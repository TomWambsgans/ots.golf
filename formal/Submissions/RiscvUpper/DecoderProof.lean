import Submissions.RiscvUpper.DecoderArithmetic
import Submissions.RiscvUpper.FixedChoice
import Submissions.RiscvUpper.StructuredPure

/-! Loop invariants for the bounded-composition decoder. -/

namespace OptimalOTS.RiscvUpperProgram

open Forest
open RiscvZkvm.Rv64

/-- The selected digit, if any, and the unconsumed rank. -/
abbrev SearchState := Option ℕ × ℕ

/-- Test a block unless a preceding digit has already been selected. -/
def testBlock (digit count : ℕ) (state : SearchState) : SearchState :=
  match state.1 with
  | some _ => state
  | none => if state.2 < count then (some digit, state.2) else (none, state.2 - count)

/-- The unrolled loop's state transition, in increasing digit order. -/
def scanBlocks : List ℕ → ℕ → SearchState → SearchState
  | [], _, state => state
  | count :: counts, digit, state =>
      scanBlocks counts (digit + 1) (testBlock digit count state)

theorem scanBlocks_foldl (counts : List ℕ) (digit : ℕ) (state : SearchState) :
    scanBlocks counts digit state =
      (counts.zipIdx digit).foldl (fun state entry => testBlock entry.2 entry.1 state) state := by
  induction counts generalizing digit state with
  | nil => rfl
  | cons count counts ih =>
    simpa only [scanBlocks, List.zipIdx_cons, List.foldl_cons] using
      ih (digit + 1) (testBlock digit count state)

@[simp] theorem testBlock_selected (digit count selected rank : ℕ) :
    testBlock digit count (some selected, rank) = (some selected, rank) := rfl

@[simp] theorem testBlock_zero (digit rank : ℕ) :
    testBlock digit 0 (none, rank) = (none, rank) := by simp [testBlock]

@[simp] theorem scanBlocks_selected (counts : List ℕ) (digit selected rank : ℕ) :
    scanBlocks counts digit (some selected, rank) = (some selected, rank) := by
  induction counts generalizing digit with
  | nil => rfl
  | cons count counts ih => simpa only [scanBlocks, testBlock_selected] using ih (digit + 1)

/-- The guarded scan has the same result as the specification's consecutive-block search. -/
theorem scanBlocks_locate (counts : List ℕ) (digit rank : ℕ) (hr : rank < counts.sum) :
    scanBlocks counts digit (none, rank) =
      (some (digit + (locate counts rank).1), (locate counts rank).2) := by
  induction counts generalizing digit rank with
  | nil => simp at hr
  | cons count counts ih =>
    by_cases h : rank < count
    · simp [scanBlocks, testBlock, h, locate]
    · have hrest : rank - count < counts.sum := by
        simp only [List.sum_cons] at hr
        omega
      simpa [scanBlocks, testBlock, h, locate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (digit + 1) (rank - count) hrest

/-- Skipping a candidate larger than the remaining sum agrees with its zero-size block. -/
theorem testBlock_composition (n sum digit rank : ℕ) :
    testBlock digit (if digit ≤ sum then comp n (sum - digit) else 0) (none, rank) =
      (if digit ≤ sum then
        if rank < comp n (sum - digit) then (some digit, rank)
        else (none, rank - comp n (sum - digit))
      else (none, rank)) := by
  split_ifs <;> simp_all [testBlock]

/-- At each slot the selected digit and residual rank satisfy the next recursive call's
precondition, while the selected flag makes every later candidate inert. -/
theorem scan_composition (n sum rank : ℕ) (hr : rank < comp (n + 1) sum) :
    let result := scanBlocks (compositionBlocks n sum) 0 (none, rank)
    ∃ digit, result.1 = some digit ∧ digit < 15 ∧ digit ≤ sum ∧
      result.2 < comp n (sum - digit) ∧
      unrankComposition (n + 1) sum rank =
        digit :: unrankComposition n (sum - digit) result.2 := by
  dsimp only
  rw [scanBlocks_locate _ _ _ (by rwa [compositionBlocks_sum])]
  simp only [Nat.zero_add]
  let chosen := locate (compositionBlocks n sum) rank
  obtain ⟨hi, hv, _⟩ := locate_spec (compositionBlocks n sum) rank
    (by rwa [compositionBlocks_sum])
  have hd : chosen.1 < 15 := by simpa [chosen, compositionBlocks] using hi
  rw [compositionBlocks_get n sum _ hd] at hv
  have hs : chosen.1 ≤ sum := by
    by_contra h
    simp only [if_neg h] at hv
    omega
  rw [if_pos hs] at hv
  exact ⟨chosen.1, rfl, hd, hs, hv, rfl⟩

/-- The fixed table used in memory agrees with the variable-width mathematical table. -/
theorem table_lookup (n sum digit : ℕ) (hs : sum ≤ 121) (hd : digit ≤ sum) :
    (compositionTable 121 n).getD (sum - digit) 0 = comp n (sum - digit) :=
  compositionTable_get _ _ _ (by omega)

set_option maxRecDepth 100000 in
theorem table_counts_fit_checked :
    ((List.range 36).flatMap (compositionTable 121)).all (fun n => n < 2 ^ 128) = true := by
  decide +kernel

theorem compositionTable_length (S n : ℕ) : (compositionTable S n).length = S + 1 := by
  cases n <;> simp [compositionTable]

/-- Every stored count is represented exactly in 128 bits. -/
theorem table_count_fits (n sum : ℕ) (hn : n < 36) (hs : sum ≤ 121) :
    comp n sum < 2 ^ 128 := by
  have hmem : comp n sum ∈ (List.range 36).flatMap (compositionTable 121) := by
    apply List.mem_flatMap.mpr
    refine ⟨n, List.mem_range.mpr hn, ?_⟩
    rw [← compositionTable_get 121 n sum hs]
    have hi : sum < (compositionTable 121 n).length := by
      rw [compositionTable_length]
      omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] using List.getElem_mem hi
  exact of_decide_eq_true (List.all_eq_true.mp table_counts_fit_checked _ hmem)

theorem table_count_encode (n sum : ℕ) (hn : n < 36) (hs : sum ≤ 121) :
    (BitVec.ofNat 128 (comp n sum)).toNat = comp n sum := by
  exact Nat.mod_eq_of_lt (table_count_fits n sum hn hs)

/-- Counts read by one slot of the concrete decoder, from the fixed-width table. -/
def machineBlocks (n sum : ℕ) : List ℕ :=
  (List.range 15).map fun digit =>
    if digit ≤ sum then (compositionTable 121 n).getD (sum - digit) 0 else 0

theorem machineBlocks_eq (n sum : ℕ) (hs : sum ≤ 121) :
    machineBlocks n sum = compositionBlocks n sum := by
  rw [compositionBlocks_eq]
  apply List.map_congr_left
  intro digit _
  split_ifs with hd
  · exact table_lookup n sum digit hs hd
  · rfl

/-- The state-level decoder implemented by the unrolled digit tests. Failure records an
unselected slot; the proof excludes it for every admitted hash index. -/
def decodeTable : ℕ → ℕ → ℕ → Option (List ℕ)
  | 0, _, _ => some []
  | n + 1, sum, rank =>
      let selected := scanBlocks (machineBlocks n sum) 0 (none, rank)
      match selected.1 with
      | none => none
      | some digit => (digit :: ·) <$> decodeTable n (sum - digit) selected.2

set_option maxHeartbeats 2000000 in
/-- Every in-range rank is decoded without failure to the specification's exact tuple. -/
theorem decodeTable_eq (n sum rank : ℕ) (hs : sum ≤ 121) (hr : rank < comp n sum) :
    decodeTable n sum rank = some (unrankComposition n sum rank) := by
  induction n generalizing sum rank with
  | zero => rfl
  | succ n ih =>
    obtain ⟨digit, hd, _, hsum, hnext, heq⟩ := scan_composition n sum rank hr
    change (match (scanBlocks (machineBlocks n sum) 0 (none, rank)).1 with
      | none => none
      | some digit => (digit :: ·) <$> decodeTable n (sum - digit)
          (scanBlocks (machineBlocks n sum) 0 (none, rank)).2) = _
    rw [machineBlocks_eq n sum hs, hd]
    dsimp only
    rw [ih (sum - digit) _ (by omega) hnext]
    exact congrArg some heq.symm

/-- The written positions are the complement of the decoded remaining chain lengths. -/
def decodedPositions (rank : ℕ) : Option (List ℕ) :=
  (List.map (14 - ·)) <$> decodeTable 36 121 rank

theorem decodedPositions_eq (rank : ℕ) (hr : rank < comp 36 121) :
    decodedPositions rank = some ((unrankComposition 36 121 rank).map (14 - ·)) := by
  unfold decodedPositions
  rw [decodeTable_eq 36 121 rank le_rfl hr]
  rfl

attribute [local irreducible] fixedDigits unrankComposition comp

/-- For an admitted hash index, the decoder writes the OTS specification's 36 active
chain positions, in chain-index order. -/
theorem decodedPositions_fixed (index : Fin (2 ^ 115)) :
    decodedPositions index = some (List.ofFn fun k : Fin 36 =>
      (fixedPositions index ⟨k.val, by omega⟩).val) := by
  rw [decodedPositions_eq index (index.isLt.trans_le fixed_count),
    ← fixedDigits_values]
  congr 1
  simp [fixedPositions, Fin.val_rev]

/-- Structured form of the two branches after the unsigned comparison. -/
def selectDigitBlock (slot digit : ℕ) : PureBlock :=
  .seq (.guard true .x26 (.linear subtractWords))
    (.guard false .x26 (.linear (chooseWords slot digit)))

/-- Structured form of one candidate test, retaining the exact RV64 instruction expansion. -/
def readDigitBlock (remaining slot digit : ℕ) : PureBlock :=
  .seq (.linear (readCount remaining digit ++ compareWords)) (selectDigitBlock slot digit)

def guardDigitBlock (remaining slot digit : ℕ) : PureBlock :=
  .seq (.linear (testDigitPrefix digit)) (.guard true .x26 (readDigitBlock remaining slot digit))

def tryDigitBlock (remaining slot digit : ℕ) : PureBlock :=
  .guard true .x23 (guardDigitBlock remaining slot digit)

theorem tryDigitBlock_code (remaining slot digit : ℕ) :
    (tryDigitBlock remaining slot digit).code = tryDigit remaining slot digit := by
  simp [tryDigitBlock, guardDigitBlock, readDigitBlock, selectDigitBlock, PureBlock.code, tryDigit,
    testDigitPrefix, readCount, compareWords, subtractWords, chooseWords, List.append_assoc]

/-- Data semantics of a structured pure block; branch instructions leave registers and
memory unchanged. The following theorem connects this evaluator to actual machine steps. -/
def decoderEval : PureBlock → MachineState → MachineState
  | .linear code, s => code.foldl execInstrBr s
  | .seq first last, s => decoderEval last (decoderEval first s)
  | .guard zero r body, s =>
      if PureBlock.passes zero r s then decoderEval body s else s

theorem decoderEval_data (block : PureBlock) {s t : MachineState}
    (same : PureBlock.DataEq s t) (ready : block.Ready s) :
    PureBlock.DataEq (block.eval s) (decoderEval block t) := by
  induction block generalizing s t with
  | linear code => exact same.fold code ready
  | seq first last ihFirst ihLast => exact ihLast (ihFirst same ready.1) ready.2
  | guard zero r body ih =>
    have hp : PureBlock.passes zero r s ↔ PureBlock.passes zero r t := by
      simp only [PureBlock.passes, same.reg r]
    change PureBlock.DataEq
      (if PureBlock.passes zero r s then body.eval (PureBlock.branchState zero r body.code.length s)
        else PureBlock.branchState zero r body.code.length s)
      (if PureBlock.passes zero r t then decoderEval body t else t)
    by_cases passed : PureBlock.passes zero r s
    · rw [if_pos passed, if_pos (hp.mp passed)]
      exact ih same (ready.2 passed)
    · rw [if_neg passed, if_neg (mt hp.mpr passed)]
      exact same

theorem decoderEval_applyDigit (s : MachineState) (slot digit : ℕ) :
    decoderEval (selectDigitBlock slot digit) (compareWords.foldl execInstrBr s) =
      applyDigit s slot digit := by
  simp only [selectDigitBlock, decoderEval, PureBlock.passes, decide_eq_true_eq,
    decide_eq_false_iff_not, ite_not, applyDigit, compareAndSubtract]
  rfl

def tryDigitState (s : MachineState) (remaining slot digit : ℕ) : MachineState :=
  if s.getReg .x23 = 0 then
    let tested := (testDigitPrefix digit).foldl execInstrBr s
    if tested.getReg .x26 = 0 then
      applyDigit ((readCount remaining digit).foldl execInstrBr tested) slot digit
    else tested
  else s

theorem decoderEval_tryDigit (s : MachineState) (remaining slot digit : ℕ) :
    decoderEval (tryDigitBlock remaining slot digit) s = tryDigitState s remaining slot digit := by
  simp only [tryDigitBlock, guardDigitBlock, readDigitBlock, decoderEval,
    PureBlock.passes, decide_eq_true_eq,
    tryDigitState, testDigitPrefix, List.foldl_append]
  split_ifs <;> try rfl
  exact decoderEval_applyDigit _ slot digit

def rankOf (s : MachineState) : ℕ := (joinWords (s.getReg .x20) (s.getReg .x21)).toNat

theorem rankOf_eq (s : MachineState) :
    rankOf s = (joinWords (s.getReg .x20) (s.getReg .x21)).toNat := rfl

attribute [local irreducible] readCount testDigitPrefix compareWords subtractWords chooseWords

theorem tryDigitState_selected (s : MachineState) (remaining slot digit : ℕ)
    (selected : s.getReg .x23 ≠ 0) : tryDigitState s remaining slot digit = s := by
  simp only [tryDigitState, if_neg selected]

theorem tryDigitState_inactive (s : MachineState) (remaining slot digit sum : ℕ)
    (hd : digit < 15) (hs : sum ≤ 121) (disallowed : sum < digit)
    (selected : s.getReg .x23 = 0) (remainingSum : s.getReg .x22 = BitVec.ofNat 64 sum) :
    tryDigitState s remaining slot digit = (testDigitPrefix digit).foldl execInstrBr s := by
  dsimp only [tryDigitState]
  rw [if_pos selected, testDigitPrefix_flag s sum digit hs hd remainingSum, if_pos disallowed]
  rw [if_neg (by decide : (1 : Word) ≠ 0)]

theorem tryDigitState_base (s : MachineState) (remaining slot digit : ℕ) :
    (tryDigitState s remaining slot digit).getReg .x8 = s.getReg .x8 := by
  dsimp only [tryDigitState]
  split_ifs <;> simp only [applyDigit_preserves _ _ _ .x8
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    readCount_preserves _ _ _ .x8 (by decide) (by decide) (by decide) (by decide),
    testDigitPrefix_preserves _ _ .x8 (by decide)]

theorem tryDigitState_active (s : MachineState) (remaining slot digit sum : ℕ)
    (hr : remaining < 36) (hslot : slot < 36) (hd : digit < 15)
    (hs : sum ≤ 121) (allowed : digit ≤ sum)
    (selected : s.getReg .x23 = 0) (remainingSum : s.getReg .x22 = BitVec.ofNat 64 sum)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) (table : TableLoaded s) :
    let result := tryDigitState s remaining slot digit
    let count := comp remaining (sum - digit)
    result.getReg .x23 = (if rankOf s < count then 1 else 0) ∧
    rankOf result = (if rankOf s < count then rankOf s else rankOf s - count) ∧
    result.getReg .x22 = (if rankOf s < count then
      BitVec.ofNat 64 sum - BitVec.ofNat 64 digit else BitVec.ofNat 64 sum) ∧
    result.mem = (if rankOf s < count then
      (s.setMem (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot))
        (BitVec.ofNat 64 (14 - digit))).mem else s.mem) := by
  let tested := (testDigitPrefix digit).foldl execInstrBr s
  let loaded := (readCount remaining digit).foldl execInstrBr tested
  have testedReg (r : Reg) (h : r ≠ .x26) : tested.getReg r = s.getReg r :=
    testDigitPrefix_preserves s digit r h
  have loadedReg (r : Reg) (h6 : r ≠ .x6) (h7 : r ≠ .x7)
      (h24 : r ≠ .x24) (h25 : r ≠ .x25) : loaded.getReg r = tested.getReg r :=
    readCount_preserves tested remaining digit r h6 h7 h24 h25
  have testedSum : tested.getReg .x22 = BitVec.ofNat 64 sum := by
    rw [testedReg .x22 (by decide), remainingSum]
  have loadedRank : rankOf loaded = rankOf s := by
    simp only [rankOf, loadedReg .x20 (by decide) (by decide) (by decide) (by decide),
      loadedReg .x21 (by decide) (by decide) (by decide) (by decide),
      testedReg .x20 (by decide), testedReg .x21 (by decide)]
  have testedTable : TableLoaded tested := table.of_mem_eq (testDigitPrefix_mem s digit)
  have loadedCount : (joinWords (loaded.getReg .x24) (loaded.getReg .x25)).toNat =
      comp remaining (sum - digit) := by
    rw [readCount_value tested remaining digit sum hr hs hd allowed testedSum testedTable,
      table_count_encode remaining (sum - digit) hr (by omega)]
  have loadedSum : loaded.getReg .x22 = BitVec.ofNat 64 sum := by
    rw [loadedReg .x22 (by decide) (by decide) (by decide) (by decide), testedSum]
  have loadedSelected : loaded.getReg .x23 = 0 := by
    rw [loadedReg .x23 (by decide) (by decide) (by decide) (by decide),
      testedReg .x23 (by decide), selected]
  have loadedBase : loaded.getReg .x8 = BitVec.ofNat 64 positionsBase := by
    rw [loadedReg .x8 (by decide) (by decide) (by decide) (by decide),
      testedReg .x8 (by decide), base]
  have loadedMem : loaded.mem = s.mem :=
    (readCount_mem tested remaining digit).trans (testDigitPrefix_mem s digit)
  have transition : tryDigitState s remaining slot digit = applyDigit loaded slot digit := by
    dsimp only [tryDigitState]
    rw [if_pos selected, testDigitPrefix_flag s sum digit hs hd remainingSum,
      if_neg (by omega : ¬ sum < digit)]
    rfl
  dsimp only
  rw [transition]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [← rankOf_eq, loadedRank, loadedCount, loadedSelected] using applyDigit_flag loaded slot digit
  · simpa only [← rankOf_eq, loadedRank, loadedCount] using applyDigit_rank loaded slot digit
  · simpa only [← rankOf_eq, loadedRank, loadedCount, loadedSum] using applyDigit_sum loaded slot digit hd
  · simpa only [← rankOf_eq, loadedRank, loadedCount, loadedBase, MachineState.setMem, loadedMem]
      using applyDigit_mem loaded slot digit hslot

theorem selectDigitBlock_ready (s : MachineState) (slot digit : ℕ) (hslot : slot < 36)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    (selectDigitBlock slot digit).Ready s := by
  have small : 14 - digit < 2048 := by omega
  have firstBase : ((PureBlock.guard true .x26 (.linear subtractWords)).eval s).getReg .x8 =
      s.getReg .x8 := by
    dsimp only [PureBlock.eval]
    split_ifs <;> simp only [subtractWords_preserves _ .x8 (by decide) (by decide) (by decide),
      PureBlock.branchState, MachineState.getReg_setPC]
  refine ⟨⟨by simp [PureBlock.code, subtractWords], fun _ => subtractWords_ready _⟩, ?_⟩
  refine ⟨?_, fun _ => chooseWords_ready _ slot digit hslot ?_⟩
  · simp [PureBlock.code, chooseWords, constant, small]
  · simpa only [PureBlock.branchState, MachineState.getReg_setPC] using firstBase.trans base

theorem readDigitBlock_ready (s : MachineState) (remaining slot digit sum : ℕ)
    (hr : remaining < 36) (hslot : slot < 36) (hd : digit < 15)
    (hs : sum ≤ 121) (allowed : digit ≤ sum)
    (remainingSum : s.getReg .x22 = BitVec.ofNat 64 sum)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    (readDigitBlock remaining slot digit).Ready s := by
  refine ⟨Riscv.LinearReady.append
    (readCount_ready s remaining digit sum hr hs hd allowed remainingSum) (compareWords_ready _),
    selectDigitBlock_ready _ slot digit hslot ?_⟩
  simp only [PureBlock.eval, List.foldl_append,
    compareWords_preserves _ .x8 (by decide) (by decide) (by decide),
    readCount_preserves _ _ _ .x8 (by decide) (by decide) (by decide) (by decide), base]

theorem digitBlock_lengths (remaining slot digit : ℕ) :
    (readDigitBlock remaining slot digit).code.length < 1023 ∧
      (guardDigitBlock remaining slot digit).code.length < 1023 := by
  simp [readDigitBlock, guardDigitBlock, selectDigitBlock, PureBlock.code,
    readCount, compareWords, subtractWords, chooseWords, testDigitPrefix,
    constant, whenZero, whenNonzero]
  split_ifs <;> norm_num

theorem guardDigitBlock_ready (s : MachineState) (remaining slot digit sum : ℕ)
    (hr : remaining < 36) (hslot : slot < 36) (hd : digit < 15)
    (hs : sum ≤ 121) (remainingSum : s.getReg .x22 = BitVec.ofNat 64 sum)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    (guardDigitBlock remaining slot digit).Ready s := by
  refine ⟨testDigitPrefix_ready s digit, (digitBlock_lengths remaining slot digit).1, ?_⟩
  intro passed
  have zero : ((testDigitPrefix digit).foldl execInstrBr s).getReg .x26 = 0 := by
    exact of_decide_eq_true passed
  rw [testDigitPrefix_flag s sum digit hs hd remainingSum] at zero
  have allowed : digit ≤ sum := by
    by_contra h
    rw [if_pos (by omega : sum < digit)] at zero
    exact absurd zero (by decide)
  apply readDigitBlock_ready _ remaining slot digit sum hr hslot hd hs allowed
  · simpa only [PureBlock.branchState, MachineState.getReg_setPC, PureBlock.eval,
      testDigitPrefix_preserves _ _ .x22 (by decide)] using remainingSum
  · simpa only [PureBlock.branchState, MachineState.getReg_setPC, PureBlock.eval,
      testDigitPrefix_preserves _ _ .x8 (by decide)] using base

theorem tryDigitBlock_ready (s : MachineState) (remaining slot digit sum : ℕ)
    (hr : remaining < 36) (hslot : slot < 36) (hd : digit < 15)
    (hs : sum ≤ 121) (remainingSum : s.getReg .x22 = BitVec.ofNat 64 sum)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    (tryDigitBlock remaining slot digit).Ready s := by
  refine ⟨(digitBlock_lengths remaining slot digit).2, fun _ => ?_⟩
  exact guardDigitBlock_ready _ remaining slot digit sum hr hslot hd hs remainingSum base

/-- A slot's live rank, selection flag, remaining sum and sole permitted memory write. -/
def SlotRep (initial : MachineState) (slot sum : ℕ) (s : MachineState) (search : SearchState) : Prop :=
  s.getReg .x8 = BitVec.ofNat 64 positionsBase ∧ rankOf s = search.2 ∧
    match search.1 with
    | none => s.getReg .x23 = 0 ∧ s.getReg .x22 = BitVec.ofNat 64 sum ∧ s.mem = initial.mem
    | some digit => digit < 15 ∧ digit ≤ sum ∧ s.getReg .x23 = 1 ∧
        s.getReg .x22 = BitVec.ofNat 64 (sum - digit) ∧
        s.mem = (initial.setMem
          (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot))
          (BitVec.ofNat 64 (14 - digit))).mem

theorem SlotRep.table {initial s : MachineState} {slot sum : ℕ} {search : SearchState}
    (rep : SlotRep initial slot sum s search) (hs : slot < 36) (table : TableLoaded initial) :
    TableLoaded s := by
  obtain ⟨_, _, rest⟩ := rep
  cases h : search.1 with
  | none => simp only [h] at rest; exact table.of_mem_eq rest.2.2
  | some digit =>
    simp only [h] at rest
    exact (table.setPosition slot (BitVec.ofNat 64 (14 - digit)) hs).of_mem_eq rest.2.2.2.2

theorem SlotRep.step {initial s : MachineState} {slot sum : ℕ} {search : SearchState}
    (rep : SlotRep initial slot sum s search) (remaining digit : ℕ)
    (hr : remaining < 36) (hslot : slot < 36) (hd : digit < 15) (hs : sum ≤ 121)
    (table : TableLoaded initial) :
    SlotRep initial slot sum (tryDigitState s remaining slot digit)
      (testBlock digit (if digit ≤ sum then comp remaining (sum - digit) else 0) search) := by
  obtain ⟨chosen, rank⟩ := search
  have loaded := rep.table hslot table
  obtain ⟨base, rankEq, state⟩ := rep
  cases chosen with
  | some chosen =>
    have selected : s.getReg .x23 ≠ 0 := by rw [state.2.2.1]; decide
    rw [tryDigitState_selected s remaining slot digit selected]
    exact ⟨base, rankEq, state⟩
  | none =>
    obtain ⟨flag, sumEq, memEq⟩ := state
    by_cases allowed : digit ≤ sum
    · have effect := tryDigitState_active s remaining slot digit sum hr hslot hd hs
        allowed flag sumEq base loaded
      dsimp only at effect
      rw [rankEq] at effect
      by_cases selected : rank < comp remaining (sum - digit)
      · simp only [if_pos selected] at effect
        simp only [testBlock, if_pos allowed, if_pos selected]
        refine ⟨(tryDigitState_base s remaining slot digit).trans base,
          effect.2.1, hd, allowed, effect.1, ?_, ?_⟩
        · rw [effect.2.2.1, BitVec.ofNat_sub_ofNat_of_le sum digit (by omega) allowed]
        · rw [effect.2.2.2]
          simp only [MachineState.setMem, memEq]
      · simp only [if_neg selected] at effect
        simp only [testBlock, if_pos allowed, if_neg selected]
        exact ⟨(tryDigitState_base s remaining slot digit).trans base,
          effect.2.1, effect.1, effect.2.2.1, effect.2.2.2.trans memEq⟩
    · rw [tryDigitState_inactive s remaining slot digit sum hd hs (by omega) flag sumEq]
      simp only [if_neg allowed, testBlock_zero]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (testDigitPrefix_preserves s digit .x8 (by decide)).trans base
      · simpa only [rankOf, testDigitPrefix_preserves s digit .x20 (by decide),
          testDigitPrefix_preserves s digit .x21 (by decide)] using rankEq
      · exact (testDigitPrefix_preserves s digit .x23 (by decide)).trans flag
      · exact (testDigitPrefix_preserves s digit .x22 (by decide)).trans sumEq
      · exact (testDigitPrefix_mem s digit).trans memEq

theorem scanBlocks_range (f : ℕ → ℕ) (start length : ℕ) (search : SearchState) :
    scanBlocks ((List.range' start length).map f) start search =
      (List.range' start length).foldl (fun state digit => testBlock digit (f digit) state) search := by
  induction length generalizing start search with
  | zero => rfl
  | succ length ih =>
    simpa only [List.range'_succ, List.map_cons, scanBlocks, List.foldl_cons,
      Nat.mul_one, Nat.add_comm] using ih (start + 1) (testBlock start (f start) search)

theorem composition_scan_fold (remaining sum : ℕ) (search : SearchState) :
    (List.range 15).foldl (fun state digit =>
      testBlock digit (if digit ≤ sum then comp remaining (sum - digit) else 0) state) search =
      scanBlocks (compositionBlocks remaining sum) 0 search := by
  rw [compositionBlocks_eq, List.range_eq_range', scanBlocks_range]

theorem SlotRep.congr {initial s t : MachineState} {slot sum : ℕ} {search : SearchState}
    (rep : SlotRep initial slot sum s search) (same : PureBlock.DataEq t s) :
    SlotRep initial slot sum t search := by
  simp only [SlotRep, rankOf, same.reg, same.2] at rep ⊢
  exact rep

theorem SlotRep.remaining {initial s : MachineState} {slot sum : ℕ} {search : SearchState}
    (rep : SlotRep initial slot sum s search) (hs : sum ≤ 121) :
    ∃ current ≤ 121, s.getReg .x22 = BitVec.ofNat 64 current := by
  cases h : search.1 with
  | none =>
    obtain ⟨_, _, rest⟩ := rep
    simp only [h] at rest
    exact ⟨sum, hs, rest.2.1⟩
  | some digit =>
    obtain ⟨_, _, rest⟩ := rep
    simp only [h] at rest
    exact ⟨sum - digit, by omega, rest.2.2.2.1⟩

def candidateBlocks (remaining slot : ℕ) : List ℕ → PureBlock
  | [] => .linear []
  | digit :: digits => .seq (tryDigitBlock remaining slot digit) (candidateBlocks remaining slot digits)

theorem candidateBlocks_code (remaining slot : ℕ) (digits : List ℕ) :
    (candidateBlocks remaining slot digits).code = digits.flatMap (tryDigit remaining slot) := by
  induction digits with
  | nil => rfl
  | cons digit digits ih => simp only [candidateBlocks, PureBlock.code, List.flatMap_cons,
      tryDigitBlock_code, ih]

theorem candidateBlocks_rep (initial s : MachineState) (remaining slot sum : ℕ)
    (digits : List ℕ) (search : SearchState) (rep : SlotRep initial slot sum s search)
    (hr : remaining < 36) (hslot : slot < 36) (hs : sum ≤ 121)
    (digitsBound : ∀ digit ∈ digits, digit < 15) (table : TableLoaded initial) :
    (candidateBlocks remaining slot digits).Ready s ∧
      SlotRep initial slot sum ((candidateBlocks remaining slot digits).eval s)
        (digits.foldl (fun state digit =>
          testBlock digit (if digit ≤ sum then comp remaining (sum - digit) else 0) state) search) := by
  induction digits generalizing s search with
  | nil => exact ⟨True.intro, rep⟩
  | cons digit digits ih =>
    obtain ⟨current, currentBound, currentEq⟩ := rep.remaining hs
    have hd := digitsBound digit (by simp)
    have ready := tryDigitBlock_ready s remaining slot digit current hr hslot hd
      currentBound currentEq rep.1
    have nextRep := (rep.step remaining digit hr hslot hd hs table).congr
      (by simpa only [decoderEval_tryDigit] using
        decoderEval_data (tryDigitBlock remaining slot digit) ⟨rfl, rfl⟩ ready)
    have rest := ih _ _ nextRep (fun d h => digitsBound d (by simp [h]))
    exact ⟨⟨ready, rest.1⟩, rest.2⟩

theorem candidateBlocks_locate (s : MachineState) (remaining slot sum : ℕ)
    (hr : remaining < 36) (hslot : slot < 36) (hs : sum ≤ 121)
    (flag : s.getReg .x23 = 0) (sumEq : s.getReg .x22 = BitVec.ofNat 64 sum)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) (table : TableLoaded s)
    (rankBound : rankOf s < comp (remaining + 1) sum) :
    let chosen := locate (compositionBlocks remaining sum) (rankOf s)
    (candidateBlocks remaining slot (List.range 15)).Ready s ∧
      SlotRep s slot sum ((candidateBlocks remaining slot (List.range 15)).eval s)
        (some chosen.1, chosen.2) := by
  have result := candidateBlocks_rep s s remaining slot sum (List.range 15) (none, rankOf s)
    ⟨base, rfl, flag, sumEq, rfl⟩ hr hslot hs
    (fun digit h => List.mem_range.mp h) table
  rw [composition_scan_fold, scanBlocks_locate _ _ _ (by rwa [compositionBlocks_sum])] at result
  simpa only [Nat.zero_add] using result

def slotBlock (remaining slot : ℕ) : PureBlock :=
  .seq (.linear [.ADDI .x23 .x0 0]) (candidateBlocks remaining slot (List.range 15))

theorem slotBlock_code (remaining slot : ℕ) :
    (slotBlock remaining slot).code = [.ADDI .x23 .x0 0] ++
      (List.range 15).flatMap (tryDigit remaining slot) := by
  simp only [slotBlock, PureBlock.code, candidateBlocks_code]

theorem slotBlock_locate (s : MachineState) (remaining slot sum : ℕ)
    (hr : remaining < 36) (hslot : slot < 36) (hs : sum ≤ 121)
    (sumEq : s.getReg .x22 = BitVec.ofNat 64 sum)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) (table : TableLoaded s)
    (rankBound : rankOf s < comp (remaining + 1) sum) :
    let chosen := locate (compositionBlocks remaining sum) (rankOf s)
    (slotBlock remaining slot).Ready s ∧
      SlotRep s slot sum ((slotBlock remaining slot).eval s) (some chosen.1, chosen.2) := by
  let start := execInstrBr s (.ADDI .x23 .x0 0)
  have tableStart : TableLoaded start := table.of_mem_eq rfl
  have result := candidateBlocks_locate start remaining slot sum hr hslot hs rfl
    sumEq base tableStart rankBound
  exact ⟨⟨by simp [PureBlock.Ready, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady], result.1⟩, result.2⟩

def decodeBlock : ℕ → ℕ → PureBlock
  | 0, _ => .linear []
  | remaining + 1, slot => .seq (slotBlock remaining slot) (decodeBlock remaining (slot + 1))

def writePositions (s : MachineState) (slot : ℕ) : List ℕ → MachineState
  | [] => s
  | position :: positions =>
      writePositions (s.setMem (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot))
        (BitVec.ofNat 64 position)) (slot + 1) positions

theorem writePositions_mem_congr (s t : MachineState) (slot : ℕ) (positions : List ℕ)
    (same : s.mem = t.mem) : (writePositions s slot positions).mem = (writePositions t slot positions).mem := by
  induction positions generalizing s t slot with
  | nil => exact same
  | cons position positions ih =>
    exact ih _ _ _ (by simp only [MachineState.setMem, same])

attribute [local irreducible] slotBlock candidateBlocks tryDigitBlock guardDigitBlock readDigitBlock

theorem decodeBlock_correct (s : MachineState) (length slot sum : ℕ)
    (slots : slot + length ≤ 36) (hs : sum ≤ 121)
    (sumEq : s.getReg .x22 = BitVec.ofNat 64 sum)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) (table : TableLoaded s)
    (rankBound : rankOf s < comp length sum) :
    let block := decodeBlock length slot
    block.Ready s ∧ (block.eval s).getReg .x8 = BitVec.ofNat 64 positionsBase ∧
      TableLoaded (block.eval s) ∧ (block.eval s).getReg .x22 = 0 ∧ rankOf (block.eval s) = 0 ∧
      (block.eval s).mem = (writePositions s slot ((unrankComposition length sum (rankOf s)).map (14 - ·))).mem := by
  induction length generalizing s slot sum with
  | zero =>
    have sumZero : sum = 0 := by by_contra h; simp only [comp, if_neg h] at rankBound; omega
    subst sum
    have rankZero : rankOf s = 0 := by simpa [comp] using rankBound
    refine ⟨True.intro, base, table, sumEq, rankZero, ?_⟩
    simp [unrankComposition, writePositions, decodeBlock, PureBlock.eval]
  | succ remaining ih =>
    let chosen := locate (compositionBlocks remaining sum) (rankOf s)
    let next := (slotBlock remaining slot).eval s
    have one := slotBlock_locate s remaining slot sum (by omega) (by omega) hs sumEq base table rankBound
    have rep : SlotRep s slot sum next (some chosen.1, chosen.2) := one.2
    have nextBase := rep.1
    have nextRank := rep.2.1
    have nextSum := rep.2.2.2.2.2.1
    have nextMem := rep.2.2.2.2.2.2
    have nextTable := rep.table (by omega) table
    obtain ⟨digitBound, residualBound, _⟩ := locate_spec (compositionBlocks remaining sum) (rankOf s)
      (by rwa [compositionBlocks_sum])
    have digitSmall : chosen.1 < 15 := by simpa [chosen, compositionBlocks] using digitBound
    rw [compositionBlocks_get remaining sum chosen.1 digitSmall] at residualBound
    have allowed : chosen.1 ≤ sum := rep.2.2.2.1
    rw [if_pos allowed] at residualBound
    have rest := ih next (slot + 1) (sum - chosen.1) (by omega) (by omega) nextSum nextBase
      nextTable (by simpa only [nextRank] using residualBound)
    refine ⟨⟨one.1, rest.1⟩, rest.2.1, rest.2.2.1, rest.2.2.2.1, rest.2.2.2.2.1, ?_⟩
    change ((decodeBlock remaining (slot + 1)).eval next).mem = _
    rw [rest.2.2.2.2.2, nextRank]
    rw [unrankComposition, List.map_cons, writePositions]
    exact writePositions_mem_congr _ _ _ _ nextMem

def decoderBlock : PureBlock :=
  .seq (.linear (constant .x8 positionsBase ++ constant .x22 121)) (decodeBlock 36 0)

set_option maxRecDepth 100000 in
theorem decoderBlock_code : decoderBlock.code = decodePositions := by decide +kernel

/-- The complete decoder terminates and writes the exact chain positions selected by the
OTS specification, for every 115-bit hash index and every initial data state. -/
theorem decoderBlock_correct (s : MachineState) (index : Fin (2 ^ 115))
    (rankEq : rankOf s = index.val) (table : TableLoaded s) :
    decoderBlock.Ready s ∧
      (decoderBlock.eval s).mem =
        (writePositions s 0 ((unrankComposition 36 121 index.val).map (14 - ·))).mem := by
  let initCode := constant .x8 positionsBase ++ constant .x22 121
  let start := initCode.foldl execInstrBr s
  have initReady : Riscv.LinearReady s initCode :=
    Riscv.LinearReady.append (constant_ready s .x8 positionsBase) (constant_ready _ .x22 121)
  have baseLiteral : literalValue positionsBase = BitVec.ofNat 64 positionsBase := by decide +kernel
  have startReg (r : Reg) (h8 : r ≠ .x8) (h22 : r ≠ .x22) :
      start.getReg r = s.getReg r := by
    simp [start, initCode, List.foldl_append, constant_preserves, Ne.symm h8, Ne.symm h22]
  have startSum : start.getReg .x22 = BitVec.ofNat 64 121 := by
    simp [start, initCode, List.foldl_append, constant_value, literalValue_small _ (by decide : 121 < 2048)]
  have startBase : start.getReg .x8 = BitVec.ofNat 64 positionsBase := by
    simp [start, initCode, List.foldl_append, constant_value, constant_preserves, baseLiteral]
  have startMem : start.mem = s.mem := by
    simp only [start, initCode, List.foldl_append, constant_mem]
  have startRank : rankOf start = index.val := by
    simpa only [rankOf, startReg .x20 (by decide) (by decide),
      startReg .x21 (by decide) (by decide)] using rankEq
  have result := decodeBlock_correct start 36 0 121 (by decide) le_rfl startSum startBase
    (table.of_mem_eq startMem) (by rw [startRank]; exact index.isLt.trans_le fixed_count)
  refine ⟨⟨initReady, result.1⟩, ?_⟩
  change ((decodeBlock 36 0).eval start).mem = _
  rw [result.2.2.2.2.2, startRank]
  exact writePositions_mem_congr _ _ _ _ startMem

theorem decoderBlock_steps (s : MachineState) (index : Fin (2 ^ 115))
    (rankEq : rankOf s = index.val) (table : TableLoaded s)
    (located : Riscv.CodeAt s s.pc decodePositions) :
    ∃ count, count ≤ decodePositions.length ∧
      Riscv.PureSteps count s (decoderBlock.eval s) := by
  have checked := decoderBlock.steps s (decoderBlock_correct s index rankEq table).1
    (by simpa only [decoderBlock_code] using located)
  simpa only [decoderBlock_code] using checked

theorem positionAddress_ne (i j : ℕ) (hi : i < 36) (hj : j < 36) (different : i ≠ j) :
    BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * i) ≠
      BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * j) := by
  intro h
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add] at h
  have value := congrArg BitVec.toNat h
  change (6291456 + 8 * i) % 2 ^ 64 = (6291456 + 8 * j) % 2 ^ 64 at value
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at value
  omega

theorem writePositions_outside (s : MachineState) (slot : ℕ) (positions : List ℕ) (address : Word)
    (outside : ∀ k < positions.length,
      address ≠ BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * (slot + k))) :
    (writePositions s slot positions).getMem address = s.getMem address := by
  induction positions generalizing s slot with
  | nil => rfl
  | cons position positions ih =>
    rw [writePositions, ih]
    · exact MachineState.getMem_setMem_ne (by simpa only [Nat.add_zero] using outside 0 (by simp))
    · intro k hk
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using outside (k + 1) (by simp; omega)

theorem writePositions_get (s : MachineState) (slot : ℕ) (positions : List ℕ)
    (bound : slot + positions.length ≤ 36) (k : ℕ) (hk : k < positions.length) :
    (writePositions s slot positions).getMem
      (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * (slot + k))) =
        BitVec.ofNat 64 positions[k] := by
  induction positions generalizing s slot k with
  | nil => simp at hk
  | cons position positions ih =>
    cases k with
    | zero =>
      rw [writePositions, writePositions_outside]
      · simp only [Nat.add_zero, List.getElem_cons_zero, MachineState.getMem_setMem_eq]
      · intro j hj
        exact positionAddress_ne _ _ (by simp only [List.length_cons] at bound; omega)
          (by simp only [List.length_cons] at bound; omega) (by omega)
    | succ k =>
      simp only [writePositions, List.getElem_cons_succ]
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (s.setMem (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot))
          (BitVec.ofNat 64 position)) (slot + 1)
          (by simp only [List.length_cons] at bound; omega) k (by simpa using hk)

theorem decoderBlock_positions (s : MachineState) (index : Fin (2 ^ 115))
    (rankEq : rankOf s = index.val) (table : TableLoaded s) (k : Fin 36) :
    (decoderBlock.eval s).getMem (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * k.val)) =
      BitVec.ofNat 64 (fixedPositions index ⟨k.val, by omega⟩).val := by
  have written := (decoderBlock_correct s index rankEq table).2
  have length := (unrankComposition_spec 36 121 index (index.isLt.trans_le fixed_count)).1
  change (decoderBlock.eval s).mem _ = _
  rw [written]
  have entry := writePositions_get s 0 ((unrankComposition 36 121 index).map (14 - ·))
    (by simp [length]) k.val (by simp [length])
  have digit : (unrankComposition 36 121 index.val)[k.val]'(by omega) =
      (fixedDigits index k).val := by
    simp only [← fixedDigits_values index, List.getElem_ofFn]
  simp only [Nat.zero_add, List.getElem_map, digit] at entry
  have value : (fixedPositions index ⟨k.val, by omega⟩).val = 14 - (fixedDigits index k).val := by
    simp only [fixedPositions, dif_pos k.isLt, Fin.val_rev]
    change 15 - ((fixedDigits index k).val + 1) = 14 - (fixedDigits index k).val
    omega
  rw [value]
  exact entry

end OptimalOTS.RiscvUpperProgram
