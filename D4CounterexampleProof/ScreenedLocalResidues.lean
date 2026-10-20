import D4CounterexampleProof.LocalResidues

/-! Local residues of the original normally ordered elementary/screening
products, projected to the four first creation modes. The global identity
expressing the original screening action as their sum is proved in
`ScreeningResidueBridge.lean`. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screenedLocalResiduesField : _root_.Field Coefficient := inferInstance

def screenedPoleTaylor (factors : List (InverseRootFactor D₄)) (charge : Charge D₄)
    (sign : ScreeningSign) (root : Fin 4) (c : Scalars) :
    PowerSeries (MvPowerSeries (Fin 4) Scalars) :=
  PowerSeries.C (MvPowerSeries.killCompl firstModeEmbedding
    ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge)) *
      parameterTaylor (parameterLift (firstScreeningSeries sign root 1)) c

theorem screened_principal_parts_residue (factors : List (InverseRootFactor D₄))
    (charge : Charge D₄) (sign : ScreeningSign) (root : Fin 4) (c : Scalars)
    (order : ℕ) (r : Fin order → Scalars) :
    (∑ j : Fin order,
      HahnSeries.single (-((j.val : ℤ) + 1)) (MvPowerSeries.C (r j)) *
        (screenedPoleTaylor factors charge sign root c :
          LaurentSeries (MvPowerSeries (Fin 4) Scalars))).coeff (-1) =
      (principalPartPolynomial (firstScreeningVector sign root) order r :
        MvPowerSeries (Fin 4) Scalars) *
        (MvPowerSeries.killCompl firstModeEmbedding
          ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) *
            firstScreeningSeries sign root c) := by
  have hF (j : Fin 4) :
      MvPowerSeries.pderiv Scalars j (firstScreeningSeries sign root 1) =
        MvPowerSeries.C (firstScreeningVector sign root j) * firstScreeningSeries sign root 1 := by
    simpa only [mul_one] using firstScreeningSeries_pderiv sign root j 1
  unfold screenedPoleTaylor
  rw [finite_principal_parts_residue_with_factor _ _ _ hF, firstScreeningSeries_parameterLift]

theorem elementary_firstMode_ne_zero (factors : List (InverseRootFactor D₄)) (charge : Charge D₄) :
    MvPowerSeries.killCompl firstModeEmbedding
      ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) ≠ 0 := by
  intro hz
  have he := congrArg MvPowerSeries.constantCoeff hz
  rw [constantCoeff_killCompl, map_zero] at he
  exact elementarySymbol_constantCoeff_ne_zero D₄ (1 : Fin 4) factors charge he

/-- A nonzero simple rational residue really gives a nonzero local
screened creation residue, retaining every original scalar prefactor. -/
theorem screened_simple_residue_ne_zero (factors : List (InverseRootFactor D₄))
    (charge : Charge D₄) (sign : ScreeningSign) (root : Fin 4) (c r : Scalars) (hr : r ≠ 0) :
    (HahnSeries.single (-1 : ℤ) (MvPowerSeries.C r) *
      (screenedPoleTaylor factors charge sign root c :
        LaurentSeries (MvPowerSeries (Fin 4) Scalars))).coeff (-1) ≠ 0 := by
  have hs : firstScreeningSeries sign root c ≠ 0 := by
    intro hz
    have he := congrArg MvPowerSeries.constantCoeff hz
    rw [firstScreeningSeries_constantCoeff, map_zero] at he
    exact one_ne_zero he
  have hC : (MvPowerSeries.C r : MvPowerSeries (Fin 4) Scalars) ≠ 0 := by
    intro hz
    have he := congrArg MvPowerSeries.constantCoeff hz
    rw [MvPowerSeries.constantCoeff_C, map_zero] at he
    exact hr he
  have he := principal_part_residue (screenedPoleTaylor factors charge sign root c)
    (MvPowerSeries.C r) 0
  simp only [Nat.cast_zero, zero_add] at he
  rw [he, screenedPoleTaylor, PowerSeries.coeff_C_mul, firstScreeningSeries_taylor_coeff]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, map_one, pow_zero,
    MvPolynomial.coe_one, one_mul]
  exact mul_ne_zero hC (mul_ne_zero (elementary_firstMode_ne_zero factors charge) hs)

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
