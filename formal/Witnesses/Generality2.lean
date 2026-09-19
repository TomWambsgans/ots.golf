import Witnesses.Generality2.Main

/-! Internal check, not part of the contract: the Generality 2/3 lower bound quantifies over a
non-empty class. The 106-compression forest is a secure DAG scheme. -/

namespace OptimalOTS.Witnesses

theorem generality2 : ∃ S : Scheme paperParams, S.Secure ∧ ∀ i, S.verifyCost i ≤ 106 :=
  ⟨Forest.forestScheme, Forest.forestScheme_secure, fun i => (Forest.forestScheme_verifyCost i).le⟩

end OptimalOTS.Witnesses

/--
info: 'OptimalOTS.Witnesses.generality2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Witnesses.generality2
