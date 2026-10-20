import D4CounterexampleProof.ExponentialSubstitution
import D4CounterexampleProof.ScreeningPoleDerivatives
import D4CounterexampleProof.ResidueTransform

/-! Formal substitution for the actual first-mode screening exponential.
These identities connect the scalar residue transform to the original
projected normally ordered screening series. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance firstModeSubstitutionField : _root_.Field Coefficient := inferInstance

section General

variable {K σ τ : Type*} [_root_.Field K]

theorem killCompl_powerSeries_subst (e : σ ↪ τ) (f : PowerSeries K)
    (L : MvPowerSeries τ K) (hL : MvPowerSeries.constantCoeff L = 0) :
    MvPowerSeries.killCompl e (f.subst L) = f.subst (MvPowerSeries.killCompl e L) := by
  have hLe : MvPowerSeries.constantCoeff (MvPowerSeries.killCompl e L) = 0 := by
    rw [constantCoeff_killCompl, hL]
  apply MvPowerSeries.ext
  intro d
  rw [MvPowerSeries.coeff_killCompl,
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hL),
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hLe)]
  apply finsum_congr
  intro k
  rw [← map_pow, MvPowerSeries.coeff_killCompl]

end General

theorem killCompl_linearSymbol {σ : Type*} [Fintype σ] (g : SimpleLieType)
    (e : σ ↪ ModeIndex g) (c : ModeIndex g → Scalars) :
    MvPowerSeries.killCompl e (linearSymbol g c) =
      ∑ i : σ, MvPowerSeries.C (c (e i)) * MvPowerSeries.X i := by
  classical
  apply MvPowerSeries.pderiv.ext
  · intro i
    rw [pderiv_killCompl, linearSymbol_pderiv, MvPowerSeries.killCompl_C]
    simp only [map_sum, Derivation.leibniz, MvPowerSeries.pderiv_C,
      smul_eq_mul, mul_zero, add_zero, MvPowerSeries.pderiv_X]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      rw [Pi.single_eq_of_ne hji, mul_zero]
    · simp
  · rw [constantCoeff_killCompl, linearSymbol_constantCoeff]
    simp

/-- The formal exponential expression for the first-mode projection is
derived from the original screening symbol and its original exponential
definition. The original scalar screening coefficients are retained. -/
theorem firstScreeningSeries_exp_subst (sign : ScreeningSign) (root : Fin 4) (c : Scalars) :
    firstScreeningSeries sign root c =
      (PowerSeries.exp Scalars).subst
        (∑ j : Fin 4, MvPowerSeries.C (firstScreeningVector sign root j * c) *
          MvPowerSeries.X j) := by
  rw [firstScreeningSeries, exponentialSymbol_eq_exp_subst,
    killCompl_powerSeries_subst _ _ _ (linearSymbol_constantCoeff _ _), killCompl_linearSymbol]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstModeEmbedding_apply, neg_neg, zpow_one, firstScreeningVector]

theorem firstScreeningSeries_exp_linear (sign : ScreeningSign) (root : Fin 4) (c : Scalars) :
    firstScreeningSeries sign root c =
      (PowerSeries.exp Scalars).subst
        (c • (creationLinearForm (firstScreeningVector sign root) :
          MvPowerSeries (Fin 4) Scalars)) := by
  rw [firstScreeningSeries_exp_subst]
  apply congrArg (fun L : MvPowerSeries (Fin 4) Scalars => (PowerSeries.exp Scalars).subst L)
  rw [creationLinearForm_coe, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MvPowerSeries.smul_eq_C_mul, map_mul]
  ring

/-- Substituting the original first-mode creation form into the scalar
simple-pole transform produces the actual projected screening series. -/
theorem residueTransform_simple_pole_firstMode (sign : ScreeningSign) (root : Fin 4)
    (c : Scalars) :
    (residueTransform (PowerSeries.X * (1 - PowerSeries.C c * PowerSeries.X)⁻¹)).subst
        (creationLinearForm (firstScreeningVector sign root) : MvPowerSeries (Fin 4) Scalars) =
      firstScreeningSeries sign root c := by
  let L : MvPowerSeries (Fin 4) Scalars := creationLinearForm (firstScreeningVector sign root)
  have hL0 : MvPowerSeries.constantCoeff L = 0 := by
    simp [L, creationLinearForm_coe]
  have hL := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  have hcX : PowerSeries.HasSubst (c • (PowerSeries.X : PowerSeries Scalars)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  change (residueTransform (PowerSeries.X * (1 - PowerSeries.C c * PowerSeries.X)⁻¹)).subst L = _
  rw [residueTransform_simple_pole, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply hcX hL,
    PowerSeries.subst_smul hL, PowerSeries.subst_X hL]
  exact (firstScreeningSeries_exp_linear sign root c).symm

/-- The higher-pole transform has the same original screening series,
multiplied by the exact creation polynomial L^k/k!. -/
theorem residueTransform_higher_pole_firstMode (sign : ScreeningSign) (root : Fin 4)
    (c : Scalars) (k : ℕ) :
    (residueTransform (PowerSeries.X ^ (k + 1) *
      PowerSeries.rescale c (PowerSeries.invOneSubPow Scalars (k + 1)).val)).subst
        (creationLinearForm (firstScreeningVector sign root) : MvPowerSeries (Fin 4) Scalars) =
      MvPowerSeries.C ((k.factorial : Scalars)⁻¹) *
        (((creationLinearForm (firstScreeningVector sign root) :
          MvPowerSeries (Fin 4) Scalars) ^ k) * firstScreeningSeries sign root c) := by
  let L : MvPowerSeries (Fin 4) Scalars := creationLinearForm (firstScreeningVector sign root)
  have hL0 : MvPowerSeries.constantCoeff L = 0 := by simp [L, creationLinearForm_coe]
  have hL := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  have he : (PowerSeries.rescale c (PowerSeries.exp Scalars)).subst L =
      firstScreeningSeries sign root c := by
    rw [← residueTransform_simple_pole c]
    exact residueTransform_simple_pole_firstMode sign root c
  change (residueTransform (PowerSeries.X ^ (k + 1) *
    PowerSeries.rescale c (PowerSeries.invOneSubPow Scalars (k + 1)).val)).subst L = _
  rw [residueTransform_higher_pole, PowerSeries.subst_mul hL, PowerSeries.subst_C,
    PowerSeries.subst_mul hL, PowerSeries.subst_pow hL, PowerSeries.subst_X hL, he]

/-- Finite principal parts transform into polynomial multiples of the
actual original first-mode screening series; the constant part vanishes. -/
theorem residueTransform_principal_parts_firstMode {ι : Type*} (s : Finset ι)
    (sign : ScreeningSign) (root : Fin 4) (a : Scalars) (r c : ι → Scalars) (k : ι → ℕ) :
    (residueTransform (PowerSeries.C a + ∑ i ∈ s, r i •
      (PowerSeries.X ^ (k i + 1) *
        PowerSeries.rescale (c i) (PowerSeries.invOneSubPow Scalars (k i + 1)).val))).subst
          (creationLinearForm (firstScreeningVector sign root) : MvPowerSeries (Fin 4) Scalars) =
      ∑ i ∈ s, r i • (MvPowerSeries.C (((k i).factorial : Scalars)⁻¹) *
        (((creationLinearForm (firstScreeningVector sign root) :
          MvPowerSeries (Fin 4) Scalars) ^ k i) * firstScreeningSeries sign root (c i))) := by
  let L : MvPowerSeries (Fin 4) Scalars := creationLinearForm (firstScreeningVector sign root)
  have hL0 : MvPowerSeries.constantCoeff L = 0 := by simp [L, creationLinearForm_coe]
  have hL := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  rw [← PowerSeries.coe_substAlgHom (R := Scalars) hL]
  rw [map_add, residueTransform_C, zero_add, map_sum]
  simp only [map_smul]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  rw [PowerSeries.coe_substAlgHom (R := Scalars) hL]
  exact congrArg (fun F : MvPowerSeries (Fin 4) Scalars => r i • F)
    (residueTransform_higher_pole_firstMode sign root (c i) (k i))

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
