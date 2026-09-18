import Submissions.RiscvUpper.Count

/-!
# Executable bounded-composition decoding

Decode an integer rank into base-15 digits with a prescribed sum. This provides the
computable chain-position selector needed to implement the forest on a finite machine.
The inverse theorem proves that different ranks give different tuples.
-/

namespace OptimalOTS.Forest

/-- Build each dynamic-programming row once, before constructing the next row. -/
def compositionTable (S : ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate S 0
  | n + 1 =>
      let previous := compositionTable S n
      (List.range (S + 1)).map fun s =>
        ((List.range 15).map fun v => if v ≤ s then previous.getD (s - v) 0 else 0).sum

theorem compositionTable_eq (S n : ℕ) : compositionTable S n = compTable S n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [compositionTable, compTable, ih]

theorem compositionTable_get (S n s : ℕ) (hs : s ≤ S) :
    (compositionTable S n).getD s 0 = comp n s := by
  rw [compositionTable_eq, compTable_getD S n s hs]

/-- Locate an index in consecutive blocks of the given lengths. -/
def locate : List ℕ → ℕ → ℕ × ℕ
  | [], r => (0, r)
  | c :: cs, r => if r < c then (0, r) else
      let next := locate cs (r - c)
      (next.1 + 1, next.2)

theorem locate_spec (cs : List ℕ) (r : ℕ) (hr : r < cs.sum) :
    (locate cs r).1 < cs.length ∧
    (locate cs r).2 < cs.getD (locate cs r).1 0 ∧
    r = (cs.take (locate cs r).1).sum + (locate cs r).2 := by
  induction cs generalizing r with
  | nil => simp at hr
  | cons c cs ih =>
    by_cases h : r < c
    · simp [locate, h]
    · have rest : r - c < cs.sum := by simp only [List.sum_cons] at hr; omega
      obtain ⟨hi, hv, he⟩ := ih (r - c) rest
      simp only [locate, if_neg h]
      refine ⟨by simpa using Nat.succ_lt_succ hi, ?_, ?_⟩
      · simpa using hv
      · simp only [List.take_succ_cons, List.sum_cons]
        omega

/-- Block lengths for choosing the next digit. -/
def compositionBlocks (n s : ℕ) : List ℕ :=
  let row := compositionTable s n
  (List.range 15).map fun v => if v ≤ s then row.getD (s - v) 0 else 0

theorem compositionBlocks_eq (n s : ℕ) : compositionBlocks n s =
    (List.range 15).map (fun v => if v ≤ s then comp n (s - v) else 0) := by
  simp only [compositionBlocks, compositionTable_get s n _ (Nat.sub_le _ _)]

theorem compositionBlocks_sum (n s : ℕ) : (compositionBlocks n s).sum = comp (n + 1) s := by
  rw [compositionBlocks_eq, sum_map_range, comp]

theorem compositionBlocks_get (n s v : ℕ) (hv : v < 15) :
    (compositionBlocks n s).getD v 0 = if v ≤ s then comp n (s - v) else 0 := by
  simp [compositionBlocks_eq, List.getD_eq_getElem?_getD, List.getElem?_range hv]

/-- Lexicographic unranking of `n` digits in `0,…,14` with sum `s`. -/
def unrankComposition : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | n + 1, s, r =>
      let selected := locate (compositionBlocks n s) r
      selected.1 :: unrankComposition n (s - selected.1) selected.2

/-- The rank recovered from a tuple. -/
def rankComposition : ℕ → List ℕ → ℕ
  | _, [] => 0
  | s, v :: vs =>
      ((compositionBlocks vs.length s).take v).sum + rankComposition (s - v) vs

theorem unrankComposition_spec (n s r : ℕ) (hr : r < comp n s) :
    (unrankComposition n s r).length = n ∧
    (∀ v ∈ unrankComposition n s r, v < 15) ∧
    (unrankComposition n s r).sum = s ∧
    rankComposition s (unrankComposition n s r) = r := by
  induction n generalizing s r with
  | zero =>
    have hs : s = 0 := by
      by_contra h
      simp [comp, h] at hr
    subst s
    have hzero : r = 0 := by simpa [comp] using hr
    subst r
    simp [unrankComposition, rankComposition]
  | succ n ih =>
    let selected := locate (compositionBlocks n s) r
    obtain ⟨hi, hv, he⟩ := locate_spec (compositionBlocks n s) r
      (by rwa [compositionBlocks_sum])
    have hi' : selected.1 < 15 := by simpa [selected, compositionBlocks] using hi
    rw [compositionBlocks_get n s _ hi'] at hv
    have hs : selected.1 ≤ s := by
      by_contra h
      simp only [if_neg h] at hv
      omega
    rw [if_pos hs] at hv
    obtain ⟨hl, hd, hsum, hrank⟩ := ih (s - selected.1) selected.2 hv
    let rest := unrankComposition n (s - selected.1) selected.2
    change (selected.1 :: rest).length = n + 1 ∧
      (∀ v ∈ selected.1 :: rest, v < 15) ∧
      (selected.1 :: rest).sum = s ∧ rankComposition s (selected.1 :: rest) = r
    refine ⟨by simp [rest, hl], ?_, ?_, ?_⟩
    · intro v hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hi'
      · exact hd v hmem
    · simp only [rest, List.sum_cons, hsum]
      omega
    · simp only [rest, rankComposition, hl, hrank]
      exact he.symm

/-- The decoder selects distinct tuples for distinct in-range ranks. -/
theorem unrankComposition_injective (n s : ℕ) :
    Function.Injective (fun r : Fin (comp n s) => unrankComposition n s r) := by
  intro r t h
  have eq := congrArg (rankComposition s) h
  rw [(unrankComposition_spec n s r r.isLt).2.2.2,
    (unrankComposition_spec n s t t.isLt).2.2.2] at eq
  exact Fin.ext eq

end OptimalOTS.Forest
