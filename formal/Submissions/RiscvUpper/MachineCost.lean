import OptimalOTS.RiscvMachine

/-! A reusable cost rule for fuel-bounded machine executions. -/

namespace OptimalOTS.Riscv

open RiscvZkvm.Rv64 OracleComp

/-- An invariant preserved by every transition, with a bound on each hash call. -/
structure CostInvariant (I : MachineState → Prop) (limit : ℕ) : Prop where
  hashCost : ∀ s, I s → blockCost paperParams (s.getReg .x11).toNat ≤ limit
  hashStep : ∀ s, I s → ∀ answer, I (writeHash s answer)
  randomStep : ∀ s, I s → ∀ word, I ((s.setReg .x10 word).setPC (s.pc + 4))
  ordinaryStep : ∀ s, I s → ∀ next, step s = some next → I next

theorem execute_regular (fuel : ℕ) (s : MachineState) (i : Instr)
    (fetch : s.code s.pc = some i) (admitted : admittedInstruction i = true)
    (ordinary : i ≠ .ECALL) :
    execute (fuel + 1) s = match step s with
      | none => pure none
      | some next => addCycles 1 <$> execute fuel next := by
  rw [execute, fetch]
  simp only [admitted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases i <;> rfl

theorem addCycles_bound (computation : OracleComp (Spec paperParams) Outcome) (a b : ℕ)
    (bound : ∀ decision cycles, some (decision, cycles) ∈ support computation → cycles ≤ b)
    (decision : Bool) (cycles : ℕ)
    (h : some (decision, cycles) ∈ support (addCycles a <$> computation)) : cycles ≤ a + b := by
  rw [support_map] at h
  obtain ⟨result, hr, equal⟩ := h
  cases result with
  | none => cases equal
  | some result =>
    rcases result with ⟨decision', cycles'⟩
    have hc : a + cycles' = cycles := congrArg (fun v : Outcome => (v.getD (false, 0)).2) equal
    have hb := bound decision' cycles' hr
    omega

/-- At most `fuel * limit` cycles, whenever each possible step costs at most `limit`. -/
theorem execute_cost_of_invariant {I : MachineState → Prop} {limit : ℕ}
    (invariant : CostInvariant I limit) (positive : 1 ≤ limit) (fuel : ℕ)
    (s : MachineState) (hs : I s) (decision : Bool) (cycles : ℕ)
    (accepted : some (decision, cycles) ∈ support (execute fuel s)) : cycles ≤ fuel * limit := by
  induction fuel generalizing s decision cycles with
  | zero => simp [execute] at accepted
  | succ fuel ih =>
    have advance (a : ℕ) (next : MachineState) (ha : a ≤ limit) (hn : I next)
        (h : some (decision, cycles) ∈ support (addCycles a <$> execute fuel next)) :
        cycles ≤ (fuel + 1) * limit := by
      have bound := addCycles_bound (execute fuel next) a (fuel * limit)
        (fun b c hc => ih next hn b c hc) decision cycles h
      nlinarith
    cases fetch : s.code s.pc with
    | none => simp [execute, fetch] at accepted
    | some i =>
      by_cases admitted : admittedInstruction i = true
      · by_cases system : i = .ECALL
        · subst i
          rw [execute, fetch] at accepted
          simp only [admittedInstruction, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at accepted
          by_cases halt : s.getReg .x5 = 0
          · simp only [if_pos halt] at accepted
            split_ifs at accepted <;> simp only [support_pure, Set.mem_singleton_iff] at accepted
            · cases accepted
              nlinarith
            · cases accepted
              nlinarith
            · cases accepted
          · simp only [if_neg halt] at accepted
            by_cases hashCall : s.getReg .x5 = Riscv.hashCall
            · simp only [if_pos hashCall] at accepted
              split_ifs at accepted with valid
              · rw [support_bind] at accepted
                simp only [Set.mem_iUnion] at accepted
                obtain ⟨answer, _, accepted⟩ := accepted
                exact advance _ _ (invariant.hashCost s hs) (invariant.hashStep s hs answer) accepted
              · simp at accepted
            · simp only [if_neg hashCall] at accepted
              split_ifs at accepted with random
              · rw [support_bind] at accepted
                simp only [Set.mem_iUnion] at accepted
                obtain ⟨word, _, accepted⟩ := accepted
                exact advance 1 _ positive (invariant.randomStep s hs word) accepted
              · simp at accepted
        · rw [execute_regular fuel s i fetch admitted system] at accepted
          cases next : step s with
          | none => simp [next] at accepted
          | some state =>
            rw [next] at accepted
            exact advance 1 state positive (invariant.ordinaryStep s hs state next) accepted
      · simp [execute, fetch, admitted] at accepted

end OptimalOTS.Riscv
