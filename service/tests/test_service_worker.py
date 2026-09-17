"""Record promotion, durable reporting, worker exclusivity and pipeline result checks."""
from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from datetime import timedelta
from pathlib import Path
from unittest.mock import Mock, patch

import httpx
from sqlalchemy import create_engine, select
from sqlalchemy.orm import sessionmaker
from sqlalchemy.pool import StaticPool

from app import main, records, worker
from app.config import settings
from app.db import Base, GithubReport, Submission, User, local_lock, schedule_report, utcnow


class ServiceWorkerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.data = Path(self.temp.name)
        (self.data / 'work').mkdir()
        (self.data / 'logs').mkdir()
        self.engine = create_engine('sqlite://', connect_args={'check_same_thread': False}, poolclass=StaticPool)
        Base.metadata.create_all(self.engine)
        self.sessions = sessionmaker(self.engine, expire_on_commit=False)
        self.patches = [patch.object(settings, 'data_dir', self.data),
                        patch.object(settings, 'work_dir', self.data / 'work'),
                        patch.object(settings, 'contract_repo', 'owner/repo'),
                        patch.object(settings, 'github_token', ''),
                        patch('app.worker.SessionLocal', self.sessions), patch('app.main.SessionLocal', self.sessions)]
        for p in self.patches:
            p.start()
        with self.sessions() as session:
            user = User(login='proof-author')
            session.add(user)
            session.commit()
            self.user_id = user.id

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.engine.dispose()
        self.temp.cleanup()

    def submission(self, *, claim=19, status='verified', baseline=False, record=False, pr=7):
        with self.sessions() as session:
            sub = Submission(user_id=self.user_id, track='lower', claim=claim, status=status,
                             commit='a' * 40, source_repo='https://github.com/author/repo.git',
                             pr_number=pr, baseline=baseline, is_record=record,
                             record_at=utcnow() if record else None)
            session.add(sub)
            session.commit()
            return sub

    def merged_pr(self, *, sha='a' * 40, merged=True):
        return {'state': 'closed', 'merged': merged, 'merged_at': '2026-09-17T12:00:00Z',
                'head': {'sha': sha, 'repo': {'clone_url': 'https://github.com/author/repo.git'}}}

    def merge(self, sub):
        with patch('app.main.github.get_pr', return_value=self.merged_pr()):
            return main.handle_merged_pull_request('owner/repo', sub.pr_number, sub.commit)

    def test_verification_does_not_promote_until_exact_head_is_merged(self):
        sub = self.submission()
        with self.sessions() as session:
            worker.promote(session, session.get(Submission, sub.id))
            session.commit()
            self.assertIsNone(records.current_record(session, 'lower'))
        self.assertTrue(self.merge(sub)['promoted'])
        with self.sessions() as session:
            self.assertEqual(records.current_record(session, 'lower').id, sub.id)
            self.assertIsNotNone(session.get(GithubReport, sub.id))

    def test_unmerged_better_claim_does_not_suppress_merged_record(self):
        self.submission(claim=500, pr=8)
        sub = self.submission(claim=19)
        self.merge(sub)
        with self.sessions() as session:
            self.assertEqual(records.current_record(session, 'lower').claim, 19)

    def test_wrong_head_or_unmerged_close_never_promotes(self):
        sub = self.submission()
        for pr in [self.merged_pr(merged=False), self.merged_pr(sha='b' * 40)]:
            with patch('app.main.github.get_pr', return_value=pr):
                self.assertFalse(main.handle_merged_pull_request('owner/repo', 7, sub.commit)['promoted'])
        with self.sessions() as session:
            self.assertFalse(session.get(Submission, sub.id).is_record)
            self.assertNotIn('merge', session.get(Submission, sub.id).detail_dict)

    def test_merge_before_verification_is_retained_and_promoted_after_success(self):
        sub = self.submission(claim=None, status='pending')
        self.assertFalse(self.merge(sub)['promoted'])
        result = {'status': 'verified', 'claim': 19, 'commit': sub.commit, 'comparator_exit': 0}
        with patch('app.worker.run_pipeline', return_value=(result, None)):
            worker.process(sub.id)
        with self.sessions() as session:
            checked = session.get(Submission, sub.id)
            self.assertTrue(checked.is_record)
            self.assertEqual(checked.detail_dict['merge']['head'], sub.commit)
            self.assertIsNotNone(session.get(GithubReport, sub.id))

    def test_failed_merged_proof_cannot_become_record(self):
        sub = self.submission(claim=None, status='pending')
        self.merge(sub)
        with patch('app.worker.run_pipeline', return_value=({'status': 'rejected', 'tail': 'bad proof'}, None)):
            worker.process(sub.id)
        with self.sessions() as session:
            self.assertFalse(session.get(Submission, sub.id).is_record)
            self.assertIsNone(records.current_record(session, 'lower'))

    def test_explicit_local_certificate_can_initialize_record(self):
        sub = self.submission(claim=18, baseline=True, pr=None)
        with self.sessions() as session:
            checked = session.get(Submission, sub.id)
            worker.promote(session, checked)
            session.commit()
            self.assertTrue(checked.is_record)
        bad = self.submission(claim=None, record=True)
        with self.sessions() as session:
            self.assertEqual(records.current_record(session, 'lower').id, sub.id)
            self.assertNotIn(bad.id, [s.id for s in records.frontier(session, 'lower')])

    def test_local_certificate_cannot_lower_the_contract_record(self):
        sub = self.submission(claim=0, baseline=True, pr=None)
        with self.sessions() as session:
            checked = session.get(Submission, sub.id)
            worker.promote(session, checked)
            session.commit()
            self.assertFalse(checked.is_record)
            self.assertIsNone(records.current_record(session, 'lower'))

    def test_result_reports_are_durable_and_retried_without_reverification(self):
        sub = self.submission()
        with self.sessions() as session:
            schedule_report(session, session.get(Submission, sub.id))
            session.commit()
        with patch.object(settings, 'github_token', 'test'), patch('app.worker.report', side_effect=RuntimeError('offline')):
            worker.deliver_report(sub.id)
        with self.sessions() as session:
            pending = session.get(GithubReport, sub.id)
            self.assertEqual(pending.attempts, 1)
            self.assertGreater(pending.next_attempt, utcnow())
            pending.next_attempt = utcnow() - timedelta(seconds=1)
            session.commit()
        with patch.object(settings, 'github_token', 'test'), patch('app.worker.report', return_value=123) as report:
            worker.retry_reports()
            report.assert_called_once()
        with self.sessions() as session:
            self.assertIsNone(session.get(GithubReport, sub.id))
            self.assertEqual(session.get(Submission, sub.id).detail_dict['github_comment_id'], 123)

    def test_merge_during_report_preserves_newer_pending_outbox_version(self):
        sub = self.submission()
        with self.sessions() as session:
            schedule_report(session, session.get(Submission, sub.id))
            session.commit()
        def report(_sub):
            self.merge(sub)
            return 123
        with patch.object(settings, 'github_token', 'test'), patch('app.worker.report', side_effect=report):
            worker.deliver_report(sub.id)
        with self.sessions() as session:
            self.assertIsNotNone(session.get(GithubReport, sub.id))
            checked = session.get(Submission, sub.id)
            self.assertTrue(checked.is_record)
            self.assertEqual(checked.detail_dict['github_comment_id'], 123)

    def test_existing_result_comment_is_updated_instead_of_duplicated(self):
        sub = self.submission()
        sub.detail = json.dumps({'github_comment_id': 123})
        with patch('app.worker.github.post_status') as status, patch('app.worker.github.update_comment') as update, \
             patch('app.worker.github.post_comment') as post:
            self.assertEqual(worker.report(sub), 123)
            status.assert_called_once()
            update.assert_called_once()
            post.assert_not_called()

    def test_deleted_result_comment_is_recreated(self):
        sub = self.submission()
        sub.detail = json.dumps({'github_comment_id': 123})
        response = httpx.Response(404, request=httpx.Request('PATCH', 'https://api.github.com/comment'))
        error = httpx.HTTPStatusError('deleted', request=response.request, response=response)
        with patch('app.worker.github.post_status'), patch('app.worker.github.update_comment', side_effect=error), \
             patch('app.worker.github.post_comment', return_value=456) as post:
            self.assertEqual(worker.report(sub), 456)
            post.assert_called_once()

    def test_production_worker_refuses_web_role_even_if_settings_loaded(self):
        with patch.object(settings, 'environment', 'production'), patch.object(settings, 'role', 'web'), \
             patch('app.worker.init_db') as initialize:
            with self.assertRaises(SystemExit):
                worker.main()
            initialize.assert_not_called()

    def test_worker_lock_excludes_another_worker_and_is_released(self):
        with local_lock('worker', blocking=False):
            with self.assertRaises(BlockingIOError):
                with local_lock('worker', blocking=False):
                    self.fail('second worker acquired the active lock')
        with local_lock('worker', blocking=False):
            pass

    def pipeline(self, sub, result, *, returncode=0):
        proc = Mock(returncode=returncode)
        proc.communicate.return_value = (json.dumps(result), '')
        with patch('app.worker.subprocess.Popen', return_value=proc) as launch:
            result, log_path = worker.run_pipeline(sub)
            self.assertTrue(launch.call_args.kwargs['start_new_session'])
            self.assertTrue(Path(log_path).is_file())
            return result

    def test_pipeline_rejects_forged_or_inconsistent_success_metadata(self):
        sub = self.submission()
        valid = {'status': 'verified', 'track': 'lower', 'claim': 19, 'commit': sub.commit}
        self.assertEqual(self.pipeline(sub, valid)['status'], 'verified')
        for changes in ({'track': 'upper'}, {'claim': True}, {'claim': -1}, {'claim': 1000001},
                        {'commit': 'b' * 40}, {'claim': None}):
            self.assertEqual(self.pipeline(sub, valid | changes)['status'], 'failed')
        self.assertEqual(self.pipeline(sub, valid, returncode=1)['status'], 'failed')
        self.assertEqual(self.pipeline(sub, [])['status'], 'failed')

    def test_pipeline_outer_timeout_stops_group_and_preserves_log(self):
        sub = self.submission()
        proc = Mock(pid=12345, returncode=-15)
        proc.communicate.side_effect = [subprocess.TimeoutExpired('verify', 1), ('partial output', '')]
        with patch('app.worker.subprocess.Popen', return_value=proc), patch('app.worker.os.killpg') as kill:
            result, log_path = worker.run_pipeline(sub)
        kill.assert_called_once_with(12345, worker.signal.SIGTERM)
        self.assertEqual(result['status'], 'timeout')
        self.assertIn('partial output', Path(log_path).read_text())
        self.assertIn('outer time limit', Path(log_path).read_text())

    def test_pipeline_termination_escalates_if_graceful_shutdown_stalls(self):
        proc = Mock(pid=12345)
        proc.communicate.side_effect = [subprocess.TimeoutExpired('verify', 40), ('stopped', '')]
        with patch('app.worker.os.killpg') as kill:
            self.assertEqual(worker._stop_pipeline(proc), ('stopped', ''))
        self.assertEqual([call.args for call in kill.call_args_list],
                         [(12345, worker.signal.SIGTERM), (12345, worker.signal.SIGKILL)])

    def test_github_http_failure_is_not_silently_treated_as_reported(self):
        response = httpx.Response(503, request=httpx.Request('POST', 'https://api.github.com/test'), text='unavailable')
        with self.assertRaises(httpx.HTTPStatusError):
            worker.github._check(response, 'test status')


if __name__ == '__main__':
    unittest.main()
