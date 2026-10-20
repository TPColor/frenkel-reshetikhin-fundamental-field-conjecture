import D4CounterexampleProof.HigherPoleFactors

/-! Higher pole derivatives of the actual original screening exponential
after projection to the four first creation modes. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screeningPoleDerivativesField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def firstScreeningVector (sign : ScreeningSign) (root k : Fin 4) : Scalars :=
  RatFunc.C (screeningModes (g := D₄) sign root (-1) k)

/-- A projection of the originally defined screening symbol at argument
c. Its coefficients are not redefined by an exponential normal form. -/
def firstScreeningSeries (sign : ScreeningSign) (root : Fin 4) (c : Scalars) :
    MvPowerSeries (Fin 4) Scalars :=
  MvPowerSeries.killCompl firstModeEmbedding
    (exponentialSymbol D₄ (fun mode =>
      RatFunc.C (screeningModes (g := D₄) sign root mode.2.val mode.1) * c ^ (-mode.2.val)))

@[simp] theorem firstScreeningSeries_constantCoeff
    (sign : ScreeningSign) (root : Fin 4) (c : Scalars) :
    MvPowerSeries.constantCoeff (firstScreeningSeries sign root c) = 1 := by
  rw [firstScreeningSeries, constantCoeff_killCompl, exponentialSymbol_constantCoeff]

theorem firstScreeningSeries_pderiv (sign : ScreeningSign) (root k : Fin 4) (c : Scalars) :
    MvPowerSeries.pderiv Scalars k (firstScreeningSeries sign root c) =
      MvPowerSeries.C (firstScreeningVector sign root k * c) * firstScreeningSeries sign root c := by
  rw [firstScreeningSeries, pderiv_killCompl, exponentialSymbol_pderiv, map_mul,
    MvPowerSeries.killCompl_C]
  simp only [firstModeEmbedding_apply, neg_neg, zpow_one, firstScreeningVector]

theorem firstScreeningSeries_parameterLift
    (sign : ScreeningSign) (root : Fin 4) (c : Scalars) :
    MvPowerSeries.map (Polynomial.evalRingHom c)
      (parameterLift (firstScreeningSeries sign root 1)) = firstScreeningSeries sign root c := by
  have hF (k : Fin 4) :
      MvPowerSeries.pderiv Scalars k (firstScreeningSeries sign root 1) =
        MvPowerSeries.C (firstScreeningVector sign root k) * firstScreeningSeries sign root 1 := by
    simpa only [mul_one] using firstScreeningSeries_pderiv sign root k 1
  apply eigenseries_unique _ _ (fun k => firstScreeningVector sign root k * c)
  · intro k
    rw [pderiv_map_coefficients, parameterLift_pderiv _ _ hF, map_mul, MvPowerSeries.map_C]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  · intro k
    exact firstScreeningSeries_pderiv sign root k c
  · rw [MvPowerSeries.constantCoeff_map, parameterLift_constantCoeff,
      firstScreeningSeries_constantCoeff]
    simp
  · exact firstScreeningSeries_constantCoeff sign root c

/-- After any number of pole derivatives, the creation exponent stays
the same and the additional factor is an actual polynomial of degree k. -/
theorem firstScreeningSeries_higher_pole_derivative
    (sign : ScreeningSign) (root : Fin 4) (c : Scalars) (k : ℕ) :
    MvPowerSeries.map (Polynomial.evalRingHom c)
        ((poleDerivative (K := Scalars) (σ := Fin 4))^[k]
          (parameterLift (firstScreeningSeries sign root 1))) =
      ((creationLinearForm (firstScreeningVector sign root) ^ k : MvPolynomial (Fin 4) Scalars) :
        MvPowerSeries (Fin 4) Scalars) * firstScreeningSeries sign root c := by
  have hF (j : Fin 4) :
      MvPowerSeries.pderiv Scalars j (firstScreeningSeries sign root 1) =
        MvPowerSeries.C (firstScreeningVector sign root j) * firstScreeningSeries sign root 1 := by
    simpa only [mul_one] using firstScreeningSeries_pderiv sign root j 1
  rw [evaluate_parameterLift_iterate _ _ hF c k, firstScreeningSeries_parameterLift]

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
