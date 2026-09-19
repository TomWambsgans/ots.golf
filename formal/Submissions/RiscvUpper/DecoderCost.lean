import Submissions.RiscvUpper.DecoderProof

/-! The decoder executes exactly 4033 instructions on every index: each slot scans its candidate
digits, paying 23 instructions per active candidate and one per skipped candidate, and the
selected digits of a composition sum to 121. -/

namespace OptimalOTS.RiscvUpperProgram

open Forest RiscvZkvm.Rv64

/-- The instruction count of a structured block, on the data semantics `decoderEval`. -/
def decoderCost : PureBlock → MachineState → ℕ
  | .linear code, _ => code.length
  | .seq first last, s => decoderCost first s + decoderCost last (decoderEval first s)
  | .guard zero r body, s => 1 + if PureBlock.passes zero r s then decoderCost body s else 0

/-- The exact machine cost agrees with the data-semantics cost. -/
theorem cost_eq_decoderCost (block : PureBlock) {s t : MachineState}
    (same : PureBlock.DataEq s t) (ready : block.Ready s) :
    block.cost s = decoderCost block t := by
  induction block generalizing s t with
  | linear code => rfl
  | seq first last ihFirst ihLast =>
    simp only [PureBlock.cost, decoderCost]
    rw [ihFirst same ready.1, ihLast (decoderEval_data first same ready.1) ready.2]
  | guard zero r body ih =>
    have hp : PureBlock.passes zero r s ↔ PureBlock.passes zero r t := by
      simp only [PureBlock.passes, same.reg r]
    simp only [PureBlock.cost, decoderCost]
    by_cases passed : PureBlock.passes zero r s
    · rw [if_pos passed, if_pos (hp.mp passed),
        ih (⟨same.1, same.2⟩ : PureBlock.DataEq (PureBlock.branchState zero r body.code.length s) t)
          (ready.2 passed)]
    · rw [if_neg passed, if_neg (mt hp.mpr passed)]

theorem testDigitPrefix_length (digit : ℕ) (hd : digit < 15) : (testDigitPrefix digit).length = 2 := by
  simp [testDigitPrefix, constant, show digit < 2048 by omega]

theorem readCount_length (remaining digit : ℕ) : (readCount remaining digit).length = 7 := by
  simp only [readCount, constant, List.length_append, List.length_cons, List.length_nil]
  rw [if_neg (by simp [Riscv.dataBase]; omega)]
  rfl

theorem chooseWords_length (slot digit : ℕ) : (chooseWords slot digit).length = 4 := by
  simp [chooseWords, constant, show 14 - digit < 2048 by omega]

/-- One candidate costs 23 instructions while the digit is still being searched and allowed,
4 when the digit exceeds the remaining sum, and 1 once a digit has been selected. -/
theorem tryDigit_cost (s : MachineState) (remaining slot digit : ℕ) (hd : digit < 15) :
    decoderCost (tryDigitBlock remaining slot digit) s =
      if s.getReg .x23 = 0 then
        (if ((testDigitPrefix digit).foldl execInstrBr s).getReg .x26 = 0 then 23 else 4)
      else 1 := by
  have lengths : (testDigitPrefix digit).length = 2 ∧ (readCount remaining digit).length = 7 ∧
      compareWords.length = 6 ∧ subtractWords.length = 4 ∧ (chooseWords slot digit).length = 4 :=
    ⟨testDigitPrefix_length digit hd, readCount_length remaining digit, rfl, rfl,
      chooseWords_length slot digit⟩
  obtain ⟨l1, l2, l3, l4, l5⟩ := lengths
  by_cases flag : s.getReg .x23 = 0
  · have p1 : PureBlock.passes true .x23 s := by simpa [PureBlock.passes] using flag
    rw [if_pos flag]
    by_cases allowed : ((testDigitPrefix digit).foldl execInstrBr s).getReg .x26 = 0
    · have p2 : PureBlock.passes true .x26 ((testDigitPrefix digit).foldl execInstrBr s) := by
        simpa [PureBlock.passes] using allowed
      rw [if_pos allowed]
      set compared := compareWords.foldl execInstrBr
        ((readCount remaining digit).foldl execInstrBr ((testDigitPrefix digit).foldl execInstrBr s))
        with hc
      have keep : (subtractWords.foldl execInstrBr compared).getReg .x26 = compared.getReg .x26 :=
        subtractWords_preserves compared .x26 (by decide) (by decide) (by decide)
      by_cases less : compared.getReg .x26 = 0
      · have p3 : PureBlock.passes true .x26 compared := by simpa [PureBlock.passes] using less
        have p4 : ¬ PureBlock.passes false .x26 (subtractWords.foldl execInstrBr compared) := by
          simpa [PureBlock.passes, keep] using less
        simp [tryDigitBlock, guardDigitBlock, readDigitBlock, selectDigitBlock, decoderCost,
          decoderEval, List.foldl_append, p1, p2, p3, p4, ← hc, l1, l2, l3, l4]
      · have p3 : ¬ PureBlock.passes true .x26 compared := by simpa [PureBlock.passes] using less
        have p4 : PureBlock.passes false .x26 compared := by simpa [PureBlock.passes] using less
        simp [tryDigitBlock, guardDigitBlock, readDigitBlock, selectDigitBlock, decoderCost,
          decoderEval, List.foldl_append, p1, p2, p3, p4, ← hc, l1, l2, l3, l5]
    · have p2 : ¬ PureBlock.passes true .x26 ((testDigitPrefix digit).foldl execInstrBr s) := by
        simpa [PureBlock.passes] using allowed
      rw [if_neg allowed]
      simp [tryDigitBlock, guardDigitBlock, readDigitBlock, selectDigitBlock, decoderCost,
        decoderEval, p1, p2, l1]
  · have p1 : ¬ PureBlock.passes true .x23 s := by simpa [PureBlock.passes] using flag
    rw [if_neg flag]
    simp [tryDigitBlock, decoderCost, p1]

/-- The instruction count of scanning `digits` from search state `search`: a candidate costs
23 while the digit is still being searched and allowed, 4 when it exceeds the remaining sum,
and 1 once a digit has been selected. -/
def scanCost (remaining sum : ℕ) : List ℕ → SearchState → ℕ
  | [], _ => 0
  | digit :: digits, search =>
      (match search.1 with
        | some _ => 1
        | none => if digit ≤ sum then 23 else 4) +
      scanCost remaining sum digits
        (testBlock digit (if digit ≤ sum then comp remaining (sum - digit) else 0) search)

theorem scanCost_selected (remaining sum : ℕ) (digits : List ℕ) (selected rank : ℕ) :
    scanCost remaining sum digits (some selected, rank) = digits.length := by
  induction digits with
  | nil => rfl
  | cons digit digits ih =>
    simp only [scanCost, testBlock_selected, ih, List.length_cons]
    omega

/-- The candidate counts of a digit range. -/
def rangeCounts (remaining sum start len : ℕ) : List ℕ :=
  (List.range' start len).map (fun v => if v ≤ sum then comp remaining (sum - v) else 0)

theorem rangeCounts_succ (remaining sum start len : ℕ) :
    rangeCounts remaining sum start (len + 1) =
      (if start ≤ sum then comp remaining (sum - start) else 0) ::
        rangeCounts remaining sum (start + 1) len := by
  simp only [rangeCounts, List.range'_succ, List.map_cons]

/-- Digits above the remaining sum have empty candidate blocks. -/
theorem rangeCounts_above (remaining sum start len : ℕ) (h : sum < start) :
    (rangeCounts remaining sum start len).sum = 0 := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
    rw [rangeCounts_succ, List.sum_cons, if_neg (by omega), ih (start + 1) (by omega)]

/-- Scanning a digit range whose blocks cover the rank costs 23 per candidate up to and
including the selected one and 1 per candidate after it. -/
theorem scanCost_range (remaining sum len start rank : ℕ)
    (hr : rank < (rangeCounts remaining sum start len).sum) :
    scanCost remaining sum (List.range' start len) (none, rank) =
      23 * ((locate (rangeCounts remaining sum start len) rank).1 + 1) +
        (len - 1 - (locate (rangeCounts remaining sum start len) rank).1) := by
  induction len generalizing start rank with
  | zero => simp [rangeCounts] at hr
  | succ len ih =>
    rw [rangeCounts_succ] at hr ⊢
    rw [List.range'_succ]
    by_cases allowed : start ≤ sum
    · simp only [if_pos allowed] at hr ⊢
      simp only [scanCost, if_pos allowed, testBlock, locate]
      by_cases selected : rank < comp remaining (sum - start)
      · simp only [if_pos selected, scanCost_selected, List.length_range']
        omega
      · simp only [if_neg selected]
        rw [ih (start + 1) (rank - comp remaining (sum - start))
          (by simp only [List.sum_cons] at hr; omega)]
        omega
    · exfalso
      rw [if_neg allowed, List.sum_cons, rangeCounts_above remaining sum (start + 1) len (by omega)] at hr
      omega

/-- The machine cost of a candidate list is the abstract scan cost. -/
theorem candidateBlocks_cost (initial s : MachineState) (remaining slot sum : ℕ)
    (digits : List ℕ) (search : SearchState) (rep : SlotRep initial slot sum s search)
    (hr : remaining < 36) (hslot : slot < 36) (hs : sum ≤ 121)
    (digitsBound : ∀ digit ∈ digits, digit < 15) (table : TableLoaded initial) :
    decoderCost (candidateBlocks remaining slot digits) s = scanCost remaining sum digits search := by
  induction digits generalizing s search with
  | nil => rfl
  | cons digit digits ih =>
    have hd := digitsBound digit (by simp)
    have nextRep := rep.step remaining digit hr hslot hd hs table
    rw [← decoderEval_tryDigit] at nextRep
    have rest := ih _ _ nextRep (fun d h => digitsBound d (by simp [h]))
    simp only [candidateBlocks, decoderCost, rest, scanCost, tryDigit_cost s remaining slot digit hd]
    congr 1
    obtain ⟨chosen, rank⟩ := search
    obtain ⟨base, rankEq, state⟩ := rep
    cases chosen with
    | some chosen =>
      simp only at state
      rw [if_neg (by rw [state.2.2.1]; decide)]
    | none =>
      simp only at state
      rw [if_pos state.1, testDigitPrefix_flag s sum digit hs hd state.2.1]
      show (if (if sum < digit then (1 : Word) else 0) = 0 then 23 else 4) =
        if digit ≤ sum then 23 else 4
      by_cases allowed : digit ≤ sum
      · rw [if_pos allowed, if_neg (not_lt.mpr allowed), if_pos rfl]
      · rw [if_neg allowed, if_pos (not_le.mp allowed), if_neg (by decide : (1 : Word) ≠ 0)]

/-- One slot costs 38 instructions plus 22 per unit of the selected digit. -/
theorem slotBlock_cost (s : MachineState) (remaining slot sum : ℕ)
    (hr : remaining < 36) (hslot : slot < 36) (hs : sum ≤ 121)
    (sumEq : s.getReg .x22 = BitVec.ofNat 64 sum)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) (table : TableLoaded s)
    (rankBound : rankOf s < comp (remaining + 1) sum) :
    decoderCost (slotBlock remaining slot) s =
      38 + 22 * (locate (compositionBlocks remaining sum) (rankOf s)).1 := by
  let start := execInstrBr s (.ADDI .x23 .x0 0)
  have tableStart : TableLoaded start := table.of_mem_eq rfl
  have scan := candidateBlocks_cost start start remaining slot sum (List.range 15) (none, rankOf start)
    ⟨base, rfl, rfl, sumEq, rfl⟩ hr hslot hs (fun digit h => List.mem_range.mp h) tableStart
  have rankStart : rankOf start = rankOf s := rfl
  have counts : compositionBlocks remaining sum = rangeCounts remaining sum 0 15 := by
    rw [compositionBlocks_eq, rangeCounts, List.range_eq_range']
  have hr' : rankOf s < (rangeCounts remaining sum 0 15).sum := by
    rwa [← counts, compositionBlocks_sum]
  have chosenBound : (locate (rangeCounts remaining sum 0 15) (rankOf s)).1 < 15 := by
    have := (locate_spec _ _ hr').1
    simpa [rangeCounts] using this
  show 1 + decoderCost (candidateBlocks remaining slot (List.range 15)) start = _
  rw [scan, rankStart, List.range_eq_range', scanCost_range remaining sum 15 0 (rankOf s) hr', counts]
  omega

/-- The slot sweep costs 38 instructions per slot plus 22 per unit of the remaining sum. -/
theorem decodeBlock_cost (s : MachineState) (length slot sum : ℕ)
    (slots : slot + length ≤ 36) (hs : sum ≤ 121)
    (sumEq : s.getReg .x22 = BitVec.ofNat 64 sum)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) (table : TableLoaded s)
    (rankBound : rankOf s < comp length sum) :
    decoderCost (decodeBlock length slot) s = 38 * length + 22 * sum := by
  induction length generalizing s slot sum with
  | zero =>
    have sumZero : sum = 0 := by by_contra h; simp only [comp, if_neg h] at rankBound; omega
    subst sumZero
    rfl
  | succ remaining ih =>
    let chosen := locate (compositionBlocks remaining sum) (rankOf s)
    let next := decoderEval (slotBlock remaining slot) s
    have one := slotBlock_locate s remaining slot sum (by omega) (by omega) hs sumEq base table rankBound
    have same := decoderEval_data (slotBlock remaining slot) ⟨rfl, rfl⟩ one.1
    have rep : SlotRep s slot sum next (some chosen.1, chosen.2) :=
      one.2.congr ⟨same.1.symm, same.2.symm⟩
    obtain ⟨digitBound, residualBound, _⟩ := locate_spec (compositionBlocks remaining sum) (rankOf s)
      (by rwa [compositionBlocks_sum])
    have digitSmall : chosen.1 < 15 := by simpa [chosen, compositionBlocks] using digitBound
    rw [compositionBlocks_get remaining sum chosen.1 digitSmall] at residualBound
    have allowed : chosen.1 ≤ sum := rep.2.2.2.1
    rw [if_pos allowed] at residualBound
    have nextRank : rankOf next = chosen.2 := rep.2.1
    have rest := ih next (slot + 1) (sum - chosen.1) (by omega) (by omega) rep.2.2.2.2.2.1 rep.1
      (rep.table (by omega) table) (by rw [nextRank]; exact residualBound)
    have first := slotBlock_cost s remaining slot sum (by omega) (by omega) hs sumEq base table rankBound
    show decoderCost (slotBlock remaining slot) s + decoderCost (decodeBlock remaining (slot + 1)) next = _
    rw [first, rest]
    have chosenEq : chosen.1 = (locate (compositionBlocks remaining sum) (rankOf s)).1 := rfl
    omega

/-- The complete decoder executes exactly 4033 instructions on every 115-bit hash index. -/
theorem decoderBlock_cost (s : MachineState) (index : Fin (2 ^ 115))
    (rankEq : rankOf s = index.val) (table : TableLoaded s) :
    decoderBlock.cost s = 4033 := by
  rw [cost_eq_decoderCost decoderBlock (s := s) (t := s) ⟨rfl, rfl⟩
    (decoderBlock_correct s index rankEq table).1]
  let initCode := constant .x8 positionsBase ++ constant .x22 121
  let start := initCode.foldl execInstrBr s
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
  have rest := decodeBlock_cost start 36 0 121 (by decide) le_rfl startSum startBase
    (table.of_mem_eq startMem) (by rw [startRank]; exact index.isLt.trans_le fixed_count)
  have initLength : initCode.length = 3 := by decide
  show initCode.length + decoderCost (decodeBlock 36 0) start = 4033
  rw [rest, initLength]

end OptimalOTS.RiscvUpperProgram
