import D4CounterexampleProof.CreationPBW
import D4CounterexampleProof.LocalFiniteness
import D4CounterexampleProof.VacuumCoefficients
import D4CounterexampleProof.ExponentialCoefficients

/-! The original screening charge shifts preserve the proved creation
coordinates. In particular they are injective on the presented Fock
modules, so passing to a charged target cannot create cancellations. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screeningPolynomialField : _root_.Field Coefficient := inferInstance

theorem chargeTranslation_creationPolynomial (δ : RootIndex D₄ → Scalars) (p : Polynomials) :
    chargeTranslation D₄ Scalars Q T δ (creationPolynomial p) = creationPolynomial p := by
  have h : (chargeTranslation D₄ Scalars Q T δ).comp creationPolynomial = creationPolynomial := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, creationPolynomial_X, negativeGenerator, chargeTranslation_rootMode]
    have hn : -v.2.val ≠ 0 := by have hv := v.2.property; omega
    rw [if_neg hn, map_zero, add_zero]
  exact DFunLike.congr_fun h p

theorem fockChargeShift_creationState (charge δ : RootIndex D₄ → Scalars) (p : Polynomials) :
    fockChargeShift D₄ Scalars Q T charge δ (creationState charge p) =
      creationState (charge + δ) p := by
  change Submodule.Quotient.mk (chargeTranslation D₄ Scalars Q T (-δ) (creationPolynomial p * 1)) =
    Submodule.Quotient.mk (creationPolynomial p * 1)
  rw [mul_one, chargeTranslation_creationPolynomial]

theorem vacuumMap_fockChargeShift (charge δ : RootIndex D₄ → Scalars)
    (v : FockModule D₄ Scalars Q T charge) :
    vacuumMap (charge + δ) (fockChargeShift D₄ Scalars Q T charge δ v) = vacuumMap charge v := by
  conv_lhs => rw [← creationState_vacuumMap charge v]
  rw [fockChargeShift_creationState, vacuumMap_creationState]

theorem fockChargeShift_injective (charge δ : RootIndex D₄ → Scalars) :
    Function.Injective (fockChargeShift D₄ Scalars Q T charge δ) := by
  intro v w h
  have he := congrArg (vacuumMap (charge + δ)) h
  rw [vacuumMap_fockChargeShift, vacuumMap_fockChargeShift] at he
  have hh := congrArg (creationState charge) he
  simpa only [creationState_vacuumMap] using hh

/-- The original screening map has the same creation polynomial as its
residue before the charge shift. -/
theorem vacuumMap_screeningOperator (sign : ScreeningSign) (i : RootIndex D₄)
    (v : State D₄ none) :
    vacuumMap (chargeEigenvalues D₄ (some (sign, i))) (screeningOperator D₄ sign i v) =
      vacuumMap 0 (evaluateSymbol D₄ (screeningSymbol D₄ sign i) none (-1) v) := by
  cases sign <;> exact vacuumMap_fockChargeShift 0 _ _

theorem screeningOperator_eq_zero_iff (sign : ScreeningSign) (i : RootIndex D₄)
    (v : State D₄ none) :
    screeningOperator D₄ sign i v = 0 ↔
      evaluateSymbol D₄ (screeningSymbol D₄ sign i) none (-1) v = 0 := by
  cases sign
  all_goals
    change fockChargeShift D₄ Scalars Q T 0 _ _ = 0 ↔ _ = 0
    rw [← map_zero (fockChargeShift D₄ Scalars Q T 0 _)]
    exact (fockChargeShift_injective 0 _).eq_iff

/-- Membership in the original W-centralizer gives a zero unshifted
screening residue on every vacuum coefficient. No charge-map kernel
assumption is used. -/
theorem deformedW_unshifted_screening_vacuum (f : Field D₄) (hf : f ∈ deformedW D₄)
    (sign : ScreeningSign) (i : RootIndex D₄) (n : ℤ) :
    evaluateSymbol D₄ (screeningSymbol D₄ sign i) none (-1)
      (f none n (vacuum D₄ Scalars Q T 0)) = 0 := by
  apply (screeningOperator_eq_zero_iff sign i _).mp
  exact deformedW_screening_vacuum D₄ f hf sign i n

/-- Coefficientwise conjugation of the original normally ordered action
through the proved Fock realization. All sums remain locally finite. -/
theorem vacuumMap_evaluateSymbol (a : NormalSymbol D₄) (charge : Charge D₄)
    (n : ℤ) (v : State D₄ charge) :
    letI : TopologicalSpace Polynomials := ⊥
    vacuumMap (chargeEigenvalues D₄ charge) (evaluateSymbol D₄ a charge n v) =
      ∑' d : ModeMonomial D₄, if monomialDegree D₄ d - a.offset = n then
        a.coefficients charge d •
          representation (chargeEigenvalues D₄ charge) (normalWord D₄ d)
            (vacuumMap (chargeEigenvalues D₄ charge) v) else 0 := by
  classical
  let : TopologicalSpace (State D₄ charge) := ⊥
  let : TopologicalSpace Polynomials := ⊥
  unfold evaluateSymbol
  rw [linearMap_tsum_of_finite (vacuumMap (chargeEigenvalues D₄ charge)) _
    (evaluateSymbol_hasFiniteSupport D₄ a charge n v)]
  apply tsum_congr
  intro d
  by_cases hd : monomialDegree D₄ d - a.offset = n
  · rw [if_pos hd, if_pos hd, map_smul, vacuumMap_action]
  · rw [if_neg hd, if_neg hd, map_zero]

/-- Exact polynomial formula for the original screening operator, with
its original exponential coefficients and its actual charge shift. -/
theorem screeningOperator_creation_polynomial (sign : ScreeningSign) (i : RootIndex D₄)
    (p : Polynomials) :
    letI : TopologicalSpace Polynomials := ⊥
    vacuumMap (chargeEigenvalues D₄ (some (sign, i)))
        (screeningOperator D₄ sign i (creationState 0 p)) =
      ∑' d : ModeMonomial D₄, if monomialDegree D₄ d = -1 then
        (d.prod fun mode k =>
          RatFunc.C (screeningModes sign i mode.2.val mode.1) ^ k / (k.factorial : Scalars)) •
          representation 0 (normalWord D₄ d) p else 0 := by
  classical
  let : TopologicalSpace Polynomials := ⊥
  have hs := vacuumMap_screeningOperator sign i (creationState 0 p)
  have he := vacuumMap_evaluateSymbol (screeningSymbol D₄ sign i) none (-1) (creationState 0 p)
  refine hs.trans (he.trans ?_)
  apply tsum_congr
  intro d
  simp only [screeningSymbol, sub_zero, chargeEigenvalues]
  erw [vacuumMap_creationState 0 p]
  by_cases hd : monomialDegree D₄ d = -1
  · rw [if_pos hd, if_pos hd]
    congr 1
    exact exponentialSymbol_coeff_product D₄ _ d
  · rw [if_neg hd, if_neg hd]

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
