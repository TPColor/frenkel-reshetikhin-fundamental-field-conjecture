import D4CounterexampleProof.ScreeningPoleNecessity
import D4CounterexampleProof.CoefficientAggregation

/-! Repeated elementary labels are grouped using their full original
symbols and positive specialized coefficients before applying cancellation. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance groupedPoleNecessityField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem positive_expansion_pole_partner {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (c : ι → Coefficient) (n : ι → ℕ)
    (hpositive : ∀ j ∈ s, 0 < n j)
    (hspecialize : ∀ j ∈ s, specializesToNat (c j) (n j))
    (hW : (∑ j ∈ s, RatFunc.C (c j) •
      evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) (factors j))) ∈ deformedW D₄)
    (sign : ScreeningSign) (i : Fin 4) (source : ι) (hsource : source ∈ s)
    (a : Spectral)
    (hpole : screeningDivisor sign (rootExponents (monomialOfFactors (factors source)) i) a = -1) :
    ∃ j ∈ s, monomialOfFactors (factors j) ≠ monomialOfFactors (factors source) ∧
      ∃ b : Spectral, screeningDivisor sign (rootExponents (monomialOfFactors (factors j)) i) b < 0 ∧
      match sign with
      | .minus => tDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A i a.1 a.2 - A i b.1 b.2
      | .plus => qDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A i b.1 b.2 - A i a.1 a.2 := by
  classical
  let mono (j : ι) := monomialOfFactors (factors j)
  let labels := s.image mono
  let rep (m : Monomial) := if hm : m ∈ labels then
    Classical.choose (Finset.mem_image.mp hm) else source
  have hrep (m : Monomial) (hm : m ∈ labels) : rep m ∈ s ∧ mono (rep m) = m := by
    dsimp only [rep]
    rw [dif_pos hm]
    exact Classical.choose_spec (Finset.mem_image.mp hm)
  let C (m : Monomial) := ∑ j ∈ s.filter (fun j => mono j = m), c j
  have hinj : Set.InjOn (fun m => monomialOfFactors (factors (rep m))) labels := by
    intro m hm l hl he
    change mono (rep m) = mono (rep l) at he
    rw [(hrep m hm).2, (hrep l hl).2] at he
    exact he
  have hgroup : (∑ m ∈ labels, RatFunc.C (C m) •
      evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) (factors (rep m)))) =
      ∑ j ∈ s, RatFunc.C (c j) •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) (factors j)) := by
    calc
      _ = ∑ m ∈ labels, ∑ j ∈ s.filter (fun j => mono j = m), RatFunc.C (c j) •
          evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) (factors j)) := by
        apply Finset.sum_congr rfl
        intro m hm
        dsimp only [C]
        rw [map_sum]
        rw [Finset.sum_smul (s := s.filter (fun j => mono j = m)) (f := fun j => RatFunc.C (c j))
          (x := evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) (factors (rep m))))]
        apply Finset.sum_congr rfl
        intro j hj
        have hmono : monomialOfFactors (factors (rep m)) = monomialOfFactors (factors j) :=
          (hrep m hm).2.trans (Finset.mem_filter.mp hj).2.symm
        rw [elementaryField_eq_of_monomial_eq _ _ hmono]
      _ = _ := Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image.mpr ⟨j, hj, rfl⟩) _
  have hlabel : mono source ∈ labels := Finset.mem_image.mpr ⟨source, hsource, rfl⟩
  have hC : C (mono source) ≠ 0 := by
    dsimp only [C]
    apply coefficient_sum_ne_zero_of_positive_specialization
      (s.filter (fun j => mono j = mono source)) c n
      (fun j hj => hspecialize j (Finset.mem_filter.mp hj).1) source
      (Finset.mem_filter.mpr ⟨hsource, rfl⟩) (hpositive source hsource)
  have hpole' : screeningDivisor sign
      (rootExponents (monomialOfFactors (factors (rep (mono source)))) i) a = -1 := by
    change screeningDivisor sign (rootExponents (mono (rep (mono source))) i) a = -1
    rw [(hrep _ hlabel).2]
    exact hpole
  obtain ⟨m, hm, hne, b, hb, hs⟩ := finite_expansion_pole_partner labels
    (fun m => factors (rep m)) C hinj (by rw [hgroup]; exact hW)
      sign i (mono source) hlabel hC a hpole'
  have hsourceEq : monomialOfFactors (factors (rep (mono source))) =
      monomialOfFactors (factors source) := (hrep _ hlabel).2
  refine ⟨rep m, (hrep m hm).1, ?_, b, hb, ?_⟩
  · simpa only [hsourceEq] using hne
  · cases sign <;> simpa only [hsourceEq] using hs

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
