import D4CounterexampleProof.FourierContractions
import D4CounterexampleProof.ScreeningPolynomial

/-! Normal words acting on original elementary vacuum Fourier states.
The negative modes remain actual creation operators; the positive modes
are contracted using the proved identities in the original quotient. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance normalWordContractionsField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def negativePolynomial (d : ModeMonomial D₄) : Polynomials :=
  ((d.support.toList.filter fun mode => mode.2.val < 0).map fun mode =>
    MvPolynomial.X (absoluteVariable mode) ^ d mode).prod

theorem negative_word_polynomial (charge : RootIndex D₄ → Scalars) (d : ModeMonomial D₄) :
    representation charge
      (((d.support.toList.filter fun mode => mode.2.val < 0).map fun mode =>
        rootMode D₄ Scalars Q T mode.1 mode.2.val ^ d mode).prod) =
      Algebra.lmul Scalars Polynomials (negativePolynomial d) := by
  apply negative_word_representation
  intro mode hm
  simpa using (List.mem_filter.mp hm).2

/-- Exact normal-word action on an original elementary Fourier state,
transported through the proved polynomial equivalence. -/
theorem normalWord_elementary_fourier (factors : List (InverseRootFactor D₄))
    (charge : Charge D₄) (m : ℤ) (d : ModeMonomial D₄) :
    vacuumMap (chargeEigenvalues D₄ charge)
      (normalWord D₄ d •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) charge m
          (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge))) =
      ((annihilationList D₄ d).map (positiveModeScalar factors)).prod •
        (negativePolynomial d *
          vacuumMap (chargeEigenvalues D₄ charge)
            (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) charge
              (m - positiveDegree D₄ d)
              (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)))) := by
  rw [normalWord, ← annihilationList_word, mul_smul,
    positiveWord_elementary_fourier, annihilationList_energy, smul_comm]
  rw [(vacuumMap (chargeEigenvalues D₄ charge)).map_smul,
    vacuumMap_action, negative_word_polynomial]
  rfl

/-- The original screening residue on an elementary Fourier state is a
locally finite sum of creation polynomials with explicit scalar
contractions. No rational OPE or residue identification is assumed. -/
theorem screening_elementary_fourier_sum (sign : ScreeningSign) (i : RootIndex D₄)
    (factors : List (InverseRootFactor D₄)) (m : ℤ) :
    letI : TopologicalSpace Polynomials := ⊥
    vacuumMap (chargeEigenvalues D₄ (some (sign, i)))
      (screeningOperator D₄ sign i
        (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) none m
          (vacuum D₄ Scalars Q T 0))) =
      ∑' d : ModeMonomial D₄, if monomialDegree D₄ d = -1 then
        ((d.prod fun mode k =>
            RatFunc.C (screeningModes sign i mode.2.val mode.1) ^ k / (k.factorial : Scalars)) *
          ((annihilationList D₄ d).map (positiveModeScalar factors)).prod) •
          (negativePolynomial d *
            vacuumMap 0
              (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) none
                (m - positiveDegree D₄ d) (vacuum D₄ Scalars Q T 0))) else 0 := by
  classical
  let : TopologicalSpace Polynomials := ⊥
  rw [vacuumMap_screeningOperator]
  erw [vacuumMap_evaluateSymbol (screeningSymbol D₄ sign i) none (-1) _]
  apply tsum_congr
  intro d
  simp only [screeningSymbol, sub_zero]
  by_cases hd : monomialDegree D₄ d = -1
  · rw [if_pos hd, if_pos hd]
    have hc : exponentialSymbol D₄
        (fun mode => RatFunc.C (screeningModes sign i mode.2.val mode.1)) d =
        d.prod (fun mode k =>
          RatFunc.C (screeningModes sign i mode.2.val mode.1) ^ k / (k.factorial : Scalars)) :=
      exponentialSymbol_coeff_product D₄ _ d
    rw [hc]
    have h := normalWord_elementary_fourier factors none m d
    rw [vacuumMap_action] at h
    exact (congrArg (fun p : Polynomials =>
      (d.prod fun mode k => RatFunc.C (screeningModes sign i mode.2.val mode.1) ^ k /
        (k.factorial : Scalars)) • p) h).trans (smul_smul _ _ _)
  · rw [if_neg hd, if_neg hd]

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
