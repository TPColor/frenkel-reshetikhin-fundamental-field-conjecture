import D4CounterexampleProof.ScreeningLogarithms
import D4CounterexampleProof.PolynomialPart
import Mathlib.RingTheory.LaurentSeries

/-! Rational identities expanded in the formal ratio variable at
infinity. The coefficient field and the independent FR q,t are unchanged. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open scoped BigOperators LaurentSeries RatFunc

variable (K : Type*) [Field K]

theorem ratFunc_inverse_X_transcendental : Transcendental K (RatFunc.X⁻¹ : RatFunc K) := by
  intro h
  exact RatFunc.transcendental_X (IsAlgebraic.inv_iff.mp h)

def invertRationalVariable : RatFunc K →+* RatFunc K :=
  RatFunc.liftRingHom (Polynomial.aeval (RatFunc.X⁻¹ : RatFunc K)).toRingHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (ratFunc_inverse_X_transcendental K)))

theorem invertRationalVariable_polynomial (P : Polynomial K) :
    invertRationalVariable K (algebraMap (Polynomial K) (RatFunc K) P) =
      Polynomial.aeval (RatFunc.X⁻¹ : RatFunc K) P := by
  exact RatFunc.liftRingHom_algebraMap _ _ P

@[simp] theorem invertRationalVariable_X : invertRationalVariable K RatFunc.X = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X, invertRationalVariable_polynomial, Polynomial.aeval_X]
  rfl

@[simp] theorem invertRationalVariable_C (c : K) :
    invertRationalVariable K (RatFunc.C c) = RatFunc.C c := by
  rw [← RatFunc.algebraMap_C, invertRationalVariable_polynomial, Polynomial.aeval_C]
  rfl

def expansionAtInfinity : RatFunc K →+* LaurentSeries K :=
  (algebraMap (RatFunc K) (LaurentSeries K)).comp (invertRationalVariable K)

@[simp] theorem expansionAtInfinity_X :
    expansionAtInfinity K RatFunc.X = (HahnSeries.single (1 : ℤ) (1 : K))⁻¹ := by
  simp [expansionAtInfinity, RatFunc.coe_X]

@[simp] theorem expansionAtInfinity_C (c : K) :
    expansionAtInfinity K (RatFunc.C c) = HahnSeries.C c := by
  change algebraMap (RatFunc K) (LaurentSeries K) (invertRationalVariable K (RatFunc.C c)) = _
  rw [invertRationalVariable_C]
  rw [← RatFunc.algebraMap_C,
    ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
  simp

theorem powerSeries_inclusion_unit_inv (u : (PowerSeries K)ˣ) :
    HahnSeries.ofPowerSeries ℤ K ((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) =
      (HahnSeries.ofPowerSeries ℤ K (u : PowerSeries K))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul]
  change HahnSeries.ofPowerSeries ℤ K (u.inv * u.val) = 1
  rw [u.inv_val, map_one]

theorem powerSeries_inclusion_unit_zpow (u : (PowerSeries K)ˣ) (n : ℤ) :
    HahnSeries.ofPowerSeries ℤ K ((u ^ n : (PowerSeries K)ˣ) : PowerSeries K) =
      (HahnSeries.ofPowerSeries ℤ K (u : PowerSeries K)) ^ n := by
  cases n with
  | ofNat n => simp
  | negSucc n =>
    rw [zpow_negSucc, powerSeries_inclusion_unit_inv]
    simp

theorem expansionAtInfinity_linear_ratio [CharZero K] (a b : K) :
    expansionAtInfinity K ((RatFunc.X - RatFunc.C b) / (RatFunc.X - RatFunc.C a)) =
      HahnSeries.ofPowerSeries ℤ K
        ((oneSubSeriesUnit b / oneSubSeriesUnit a : (PowerSeries K)ˣ) : PowerSeries K) := by
  have hx : (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ≠ 0 := by simp
  rw [map_div₀, map_sub, map_sub, expansionAtInfinity_X,
    expansionAtInfinity_C, expansionAtInfinity_C]
  change _ = HahnSeries.ofPowerSeries ℤ K
    ((oneSubSeriesUnit b : PowerSeries K) *
      (((oneSubSeriesUnit a)⁻¹ : (PowerSeries K)ˣ) : PowerSeries K))
  rw [map_mul, powerSeries_inclusion_unit_inv]
  change _ = HahnSeries.ofPowerSeries ℤ K (1 - PowerSeries.C b * PowerSeries.X) *
    (HahnSeries.ofPowerSeries ℤ K (1 - PowerSeries.C a * PowerSeries.X))⁻¹
  simp only [map_sub, map_one, map_mul, PowerSeries.coe_C, PowerSeries.coe_X]
  have hb : (HahnSeries.single (1 : ℤ) (1 : K))⁻¹ - HahnSeries.C b =
      (1 - HahnSeries.C b * HahnSeries.single 1 1) / HahnSeries.single 1 1 := by
    field_simp
  have ha : (HahnSeries.single (1 : ℤ) (1 : K))⁻¹ - HahnSeries.C a =
      (1 - HahnSeries.C a * HahnSeries.single 1 1) / HahnSeries.single 1 1 := by
    field_simp
  rw [hb, ha, div_div_div_cancel_right₀ hx]
  rfl

theorem powerSeries_inclusion_rescale_invOneSubPow (c : K) (k : ℕ) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.rescale c (PowerSeries.invOneSubPow K k).val) =
      (1 - HahnSeries.C c * HahnSeries.single (1 : ℤ) 1 : LaurentSeries K)⁻¹ ^ k := by
  have hu := (PowerSeries.invOneSubPow K k).val_inv
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at hu
  have hr := congrArg (fun F : PowerSeries K =>
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.rescale c F)) hu
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.rescale_X,
    PowerSeries.coe_C, PowerSeries.coe_X] at hr
  have hi := eq_inv_of_mul_eq_one_left hr
  simpa only [inv_pow] using hi

theorem expansionAtInfinity_principal_part (r c : K) (k : ℕ) :
    expansionAtInfinity K (RatFunc.C r / (RatFunc.X - RatFunc.C c) ^ k) =
      HahnSeries.ofPowerSeries ℤ K (r •
        (PowerSeries.X ^ k * PowerSeries.rescale c (PowerSeries.invOneSubPow K k).val)) := by
  rw [map_div₀, map_pow, map_sub, expansionAtInfinity_X, expansionAtInfinity_C,
    expansionAtInfinity_C]
  rw [PowerSeries.smul_eq_C_mul, map_mul, map_mul, map_pow,
    powerSeries_inclusion_rescale_invOneSubPow]
  simp only [PowerSeries.coe_C, PowerSeries.coe_X]
  have hx : (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ≠ 0 := by simp
  have he : (HahnSeries.single (1 : ℤ) (1 : K))⁻¹ - HahnSeries.C c =
      (1 - HahnSeries.C c * HahnSeries.single 1 1) / HahnSeries.single 1 1 := by
    field_simp
  rw [he, div_pow, div_div_eq_mul_div, div_eq_mul_inv]
  ring

theorem powerSeries_partial_fraction_expansion {ι : Type*} (F : PowerSeries K)
    (f : RatFunc K) (hF : expansionAtInfinity K f = HahnSeries.ofPowerSeries ℤ K F)
    (s : Finset ι) (a : K) (c : ι → K) (order : ι → ℕ)
    (r : (i : ι) → Fin (order i) → K)
    (hdecomp : f = RatFunc.C a + ∑ i ∈ s, ∑ j : Fin (order i),
      RatFunc.C (r i j) / (RatFunc.X - RatFunc.C (c i)) ^ (j.val + 1)) :
    F = PowerSeries.C a + ∑ i ∈ s, ∑ j : Fin (order i), r i j •
      (PowerSeries.X ^ (j.val + 1) *
        PowerSeries.rescale (c i) (PowerSeries.invOneSubPow K (j.val + 1)).val) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [← hF, hdecomp, map_add, expansionAtInfinity_C]
  simp only [map_sum, expansionAtInfinity_principal_part, map_add, PowerSeries.coe_C]

theorem map_invOneSubPow {L : Type*} [Field L] (φ : K →+* L) (k : ℕ) :
    PowerSeries.map φ (PowerSeries.invOneSubPow K (k + 1)).val =
      (PowerSeries.invOneSubPow L (k + 1)).val := by
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mk, map_natCast]

theorem map_rescale_invOneSubPow {L : Type*} [Field L] (φ : K →+* L) (c : K) (k : ℕ) :
    PowerSeries.map φ (PowerSeries.rescale c (PowerSeries.invOneSubPow K (k + 1)).val) =
      PowerSeries.rescale (φ c) (PowerSeries.invOneSubPow L (k + 1)).val := by
  rw [← PowerSeries.rescale_map, map_invOneSubPow]

open OriginalFR.Fields

local instance expansionAtInfinityCoefficientField : Field Coefficient := inferInstance

theorem screeningFactorUnit_base_ratio (sign : ScreeningSign) (a : Spectral) :
    ((match sign with
    | .minus => linearFactorUnit (a + (1, 0)) / linearFactorUnit (a + (-1, 0))
    | .plus => linearFactorUnit (a + (0, -1)) / linearFactorUnit (a + (0, 1))) :
      (RatFunc Coefficient)ˣ) =
      Units.mk0 ((RatFunc.X - RatFunc.C (screeningZeroParameter sign a)) /
        (RatFunc.X - RatFunc.C (screeningPoleParameter sign a)))
        (div_ne_zero (ratFunc_X_sub_C_ne_zero _) (ratFunc_X_sub_C_ne_zero _)) := by
  apply Units.ext
  cases sign <;>
    simp only [Units.val_div_eq_div_val, linearFactorUnit, Units.val_mk0,
      screeningZeroParameter, screeningPoleParameter, Prod.add_def,
      zpow_add₀ q_ne_zero, zpow_add₀ t_ne_zero,
      zpow_one, zpow_neg_one, zpow_zero, mul_one]
  all_goals congr 3 <;> ring

/-- The scalar series already obtained from the original oscillators is
the genuine rational screening product expanded at infinity. -/
theorem expansionAtInfinity_screeningFactor (sign : ScreeningSign) (m : Monomial) (i : Fin 4) :
    expansionAtInfinity Coefficient (screeningFactorUnit sign (rootExponents m i) : RatFunc Coefficient) =
      HahnSeries.ofPowerSeries ℤ Coefficient
        ((PowerSeries.exp Coefficient).subst (screeningScalarLog sign m i)) := by
  rw [screeningScalarLog_exp_product]
  unfold screeningFactorUnit Finsupp.prod
  change expansionAtInfinity Coefficient ((Units.coeHom (RatFunc Coefficient)) _) =
    HahnSeries.ofPowerSeries ℤ Coefficient ((Units.coeHom (PowerSeries Coefficient)) _)
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro a ha
  rw [Units.coeHom_apply, Units.coeHom_apply, Units.val_zpow_eq_zpow_val,
    map_zpow₀, powerSeries_inclusion_unit_zpow]
  congr 1
  have hh := congrArg (fun u : (RatFunc Coefficient)ˣ =>
    expansionAtInfinity Coefficient (u : RatFunc Coefficient)) (screeningFactorUnit_base_ratio sign a)
  exact hh.trans (expansionAtInfinity_linear_ratio Coefficient _ _)

theorem screening_scalar_partial_fraction_series (sign : ScreeningSign) (m : Monomial) (i : Fin 4)
    (Q : Polynomial Coefficient) (s : Finset Spectral) (order : Spectral → ℕ)
    (r : (a : Spectral) → Fin (order a) → Coefficient)
    (hdecomp : (screeningFactorUnit sign (rootExponents m i) : RatFunc Coefficient) =
      algebraMap (Polynomial Coefficient) (RatFunc Coefficient) Q +
        ∑ a ∈ s, ∑ j : Fin (order a), RatFunc.C (r a j) /
          (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1)) :
    (((PowerSeries.exp Coefficient).subst (screeningScalarLog sign m i)).map RatFunc.C :
      PowerSeries (RatFunc Coefficient)) =
      PowerSeries.C (RatFunc.C (Q.coeff 0)) + ∑ a ∈ s, ∑ j : Fin (order a), RatFunc.C (r a j) •
        (PowerSeries.X ^ (j.val + 1) * PowerSeries.rescale (RatFunc.C (q ^ a.1 * t ^ a.2))
          (PowerSeries.invOneSubPow (RatFunc Coefficient) (j.val + 1)).val) := by
  have hQ := screening_polynomial_part_constant sign m i Q s order r hdecomp
  have hrat : (screeningFactorUnit sign (rootExponents m i) : RatFunc Coefficient) =
      RatFunc.C (Q.coeff 0) + ∑ a ∈ s, ∑ j : Fin (order a), RatFunc.C (r a j) /
        (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1) := by
    conv_lhs => rw [hdecomp]
    rw [hQ, RatFunc.algebraMap_C]
    simp
  have hs := powerSeries_partial_fraction_expansion Coefficient _ _
    (expansionAtInfinity_screeningFactor sign m i) s (Q.coeff 0)
      (fun a => q ^ a.1 * t ^ a.2) order r hrat
  have hm := congrArg (PowerSeries.map (RatFunc.C : Coefficient →+* RatFunc Coefficient)) hs
  simp only [PowerSeries.smul_eq_C_mul, map_add, map_sum, map_mul, map_pow,
    PowerSeries.map_C, PowerSeries.map_X, map_rescale_invOneSubPow] at hm ⊢
  exact hm

end
end FrenkelReshetikhin.D4CounterexampleProof
