import D4CounterexampleProof.CompletedCreationAction
import D4CounterexampleProof.ScreeningContractions

/-! Explicit all-mode contractions for the original elementary ansatz,
including every inverse-root factor. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance allModeContractionsField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem elementaryPositiveContraction_nil (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    elementaryPositiveContraction [] i n hn =
      RatFunc.C ((if i = (1 : Fin 4) then 1 else 0) *
        ((n : Coefficient)⁻¹ * (q ^ n - q ^ (-n)) * (t ^ n - t ^ (-n)))) := by
  classical
  calc
    _ = RatFunc.C (∑ j : RootIndex D₄, (deformedCartan D₄ (-n))⁻¹ j (1 : Fin 4) *
        oscillatorCommutator D₄ Coefficient q t i j n (-n)) := by
      simp only [elementaryPositiveContraction, elementaryModeExponent, List.map_nil,
        List.sum_nil, add_zero, map_sum, map_mul, oscillatorCommutator_scalar_extension]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [d4_oscillator_weight_pairing n (ne_of_gt hn) i (1 : Fin 4)]
      split_ifs <;> rfl

theorem elementaryPositiveContraction_cons (f : InverseRootFactor D₄)
    (factors : List (InverseRootFactor D₄)) (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    elementaryPositiveContraction (f :: factors) i n hn =
      elementaryPositiveContraction factors i n hn -
        oscillatorCommutator D₄ Scalars Q T i f.root n (-n) *
          RatFunc.C ((q ^ f.qShift * t ^ f.tShift) ^ n) := by
  classical
  calc
    _ = elementaryPositiveContraction factors i n hn -
        ∑ j : RootIndex D₄, oscillatorCommutator D₄ Scalars Q T i j n (-n) *
          (if j = f.root then RatFunc.C ((q ^ f.qShift * t ^ f.tShift) ^ n) else 0) := by
      unfold elementaryPositiveContraction
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [elementaryModeExponent, List.map_cons, List.sum_cons, neg_neg]
      by_cases h : j = f.root <;> simp only [h, if_true, if_false] <;> ring
    _ = _ := by simp

/-- The scalar multiplying an elementary creation series under a
positive oscillator is the highest-Y contraction minus the contractions
of its inverse-root factors, all in the original coefficient field. -/
theorem elementaryPositiveContraction_formula (factors : List (InverseRootFactor D₄))
    (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    elementaryPositiveContraction factors i n hn =
      RatFunc.C ((if i = (1 : Fin 4) then 1 else 0) *
        ((n : Coefficient)⁻¹ * (q ^ n - q ^ (-n)) * (t ^ n - t ^ (-n)))) -
      (factors.map fun f => oscillatorCommutator D₄ Scalars Q T i f.root n (-n) *
        RatFunc.C ((q ^ f.qShift * t ^ f.tShift) ^ n)).sum := by
  induction factors with
  | nil => simpa using elementaryPositiveContraction_nil i n hn
  | cons f fs ih =>
    rw [elementaryPositiveContraction_cons, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- Multiplying the actual all-mode contractions by the original
screening exponent coefficients gives the logarithmic scalar contraction
for the complete elementary ansatz. -/
theorem screening_elementary_contraction_formula (sign : ScreeningSign)
    (factors : List (InverseRootFactor D₄)) (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    RatFunc.C (screeningModes (g := D₄) sign i n i) *
        elementaryPositiveContraction factors i n hn =
      RatFunc.C ((if i = (1 : Fin 4) then 1 else 0) *
        (match sign with
        | .minus => -(q ^ n - q ^ (-n)) / (n : Coefficient)
        | .plus => (t ^ n - t ^ (-n)) / (n : Coefficient))) -
      (factors.map fun f => RatFunc.C (screeningModes (g := D₄) sign i n i) *
        oscillatorCommutator D₄ Scalars Q T i f.root n (-n) *
          RatFunc.C ((q ^ f.qShift * t ^ f.tShift) ^ n)).sum := by
  classical
  induction factors with
  | nil =>
    simp only [elementaryPositiveContraction_nil, List.map_nil, List.sum_nil, sub_zero, ← map_mul]
    have he := d4_screening_weight_contraction n (ne_of_gt hn) i (1 : Fin 4) sign
    rw [d4_oscillator_weight_pairing n (ne_of_gt hn) i (1 : Fin 4)] at he
    cases sign <;> by_cases hi : i = (1 : Fin 4) <;>
      simpa only [hi, if_true, if_false] using congrArg RatFunc.C he
  | cons f fs ih =>
    rw [elementaryPositiveContraction_cons, mul_sub, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
