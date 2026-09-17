import Submissions.Lower.AnalysisDefs

/-!
# Splitting a uniform table

A uniform table on cells restricts to independent uniform graph tables and nonce tables for two
distinct messages.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Analysis

variable {P : Params} (S : Scheme P)

/-- The embedding of the nonce cells of two messages into the encoding inputs. -/
def nonceEmb (P : Params) : Nonce P ⊕ Nonce P → EncIn P :=
  Sum.elim (fun η => Attack.msg₁ P ++ η) (fun η => Attack.msg₂ P ++ η)

theorem nonceEmb_injective (h12 : Attack.msg₁ P ≠ Attack.msg₂ P) :
    Function.Injective (nonceEmb P) := by
  have hl : ∀ (m m' : Message P) (η η' : Nonce P), m ++ η = m' ++ η' → m = m' := by
    intro m m' η η' h
    have := congrArg (fun z : EncIn P => z.extractLsb' P.nonceBits P.msgBits) h
    simpa only [BitVec.extractLsb'_append_eq_left] using this
  have hr : ∀ (m m' : Message P) (η η' : Nonce P), m ++ η = m' ++ η' → η = η' := by
    intro m m' η η' h
    have := congrArg (fun z : EncIn P => z.extractLsb' 0 P.nonceBits) h
    simpa only [BitVec.extractLsb'_append_eq_right] using this
  rintro (η | η) (η' | η') h <;> simp only [nonceEmb, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (hr _ _ _ _ h)
  · exact absurd (hl _ _ _ _ h) h12
  · exact absurd (hl _ _ _ _ h).symm h12
  · exact congrArg Sum.inr (hr _ _ _ _ h)

/-- The remaining encoding inputs. -/
abbrev RestIn (P : Params) := {e : EncIn P // e ∉ Set.range (nonceEmb P)}

/-- Decomposition of the cells. -/
def cellEquiv (h12 : Attack.msg₁ P ≠ Attack.msg₂ P) :
    (Σ v : Fin S.graph.size, BitVec (S.graph.kind v).inLen) ⊕ ((Nonce P ⊕ Nonce P) ⊕ RestIn P)
      ≃ Cell S :=
  Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.ofInjective _ (nonceEmb_injective h12)) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun e => e ∈ Set.range (nonceEmb P))))

/-- Decomposition of the tables. -/
def tableEquiv (h12 : Attack.msg₁ P ≠ Attack.msg₂ P) :
    (Cell S → BitVec P.hashBits) ≃
      S.graph.Tab × (((Nonce P → BitVec P.hashBits) × (Nonce P → BitVec P.hashBits)) ×
        (RestIn P → BitVec P.hashBits)) :=
  ((cellEquiv S h12).arrowCongr (Equiv.refl _)).symm.trans <|
    (Equiv.sumArrowEquivProdArrow _ _ _).trans <|
      Equiv.prodCongr (Equiv.piCurry (fun v (_ : BitVec (S.graph.kind v).inLen) => BitVec P.hashBits)) <|
        (Equiv.sumArrowEquivProdArrow _ _ _).trans <|
          Equiv.prodCongr (Equiv.sumArrowEquivProdArrow _ _ _) (Equiv.refl _)

theorem tableEquiv_apply (h12 : Attack.msg₁ P ≠ Attack.msg₂ P) (g : Cell S → BitVec P.hashBits) :
    tableEquiv S h12 g =
      (graphTab S g, (nonceTab S g (Attack.msg₁ P), nonceTab S g (Attack.msg₂ P)),
        fun c => g (.inr c.1)) := rfl

theorem sum_table_eq (h12 : Attack.msg₁ P ≠ Attack.msg₂ P)
    (F : S.graph.Tab → (Nonce P → BitVec P.hashBits) → (Nonce P → BitVec P.hashBits) → ℝ≥0∞) :
    (∑ g : Cell S → BitVec P.hashBits,
        F (graphTab S g) (nonceTab S g (Attack.msg₁ P)) (nonceTab S g (Attack.msg₂ P))) /
        (Fintype.card (Cell S → BitVec P.hashBits) : ℝ≥0∞) =
      (∑ t, ∑ u, ∑ w, F t u w) /
        ((Fintype.card S.graph.Tab : ℝ≥0∞) * Fintype.card (Nonce P → BitVec P.hashBits) *
          Fintype.card (Nonce P → BitVec P.hashBits)) := by
  have hsum : (∑ g : Cell S → BitVec P.hashBits,
        F (graphTab S g) (nonceTab S g (Attack.msg₁ P)) (nonceTab S g (Attack.msg₂ P))) =
      (Fintype.card (RestIn P → BitVec P.hashBits) : ℝ≥0∞) * ∑ t, ∑ u, ∑ w, F t u w := by
    rw [Fintype.sum_equiv (tableEquiv S h12) _
      (fun p => F p.1 p.2.1.1 p.2.1.2) (fun g => by rw [tableEquiv_apply])]
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [Finset.mul_sum]
  have hcard : (Fintype.card (Cell S → BitVec P.hashBits) : ℝ≥0∞) =
      (Fintype.card (RestIn P → BitVec P.hashBits) : ℝ≥0∞) *
        ((Fintype.card S.graph.Tab : ℝ≥0∞) * Fintype.card (Nonce P → BitVec P.hashBits) * Fintype.card (Nonce P → BitVec P.hashBits)) := by
    rw [Fintype.card_congr (tableEquiv S h12)]
    simp only [Fintype.card_prod, Nat.cast_mul]
    ring
  rw [hsum, hcard, ENNReal.mul_div_mul_left]
  · exact_mod_cast Fintype.card_ne_zero
  · exact ENNReal.natCast_ne_top _

end Analysis

end OptimalOTS
