import D4CounterexampleProof.HeisenbergCoefficients
import D4CounterexampleProof.ScalarContractions
import D4CounterexampleProof.RationalResidues

/-! Scalar coefficients of the original FR Y/screening contractions.
The exponential identity is in the ratio of field arguments and uses
the original independent q and t. No h-adic specialization is made. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screeningContractionsField : _root_.Field Coefficient := inferInstance

/-- Contracting a positive Y mode with a negative screening mode,
including the sign in the original minus screening exponent. -/
theorem d4_weight_screening_contraction (n : ℤ) (hn : n ≠ 0)
    (k i : RootIndex D₄) (sign : ScreeningSign) :
    (∑ j : RootIndex D₄, (deformedCartan D₄ n)⁻¹ j i *
      screeningModes sign k (-n) k *
      oscillatorCommutator D₄ Coefficient q t j k n (-n)) =
    (if k = i then 1 else 0) *
      (match sign with
      | .minus => (q ^ n - q ^ (-n)) / (n : Coefficient)
      | .plus => -(t ^ n - t ^ (-n)) / (n : Coefficient)) := by
  classical
  have hsym (j : RootIndex D₄) :
      oscillatorCommutator D₄ Coefficient q t j k n (-n) =
        oscillatorCommutator D₄ Coefficient q t k j n (-n) := by
    rw [d4_oscillator_opposite n hn, d4_oscillator_opposite n hn,
      d4_deformedCartan_symmetric n hn j k]
  simp_rw [hsym]
  calc
    _ = (∑ j : RootIndex D₄, (deformedCartan D₄ (-n))⁻¹ j i *
        oscillatorCommutator D₄ Coefficient q t k j n (-n)) *
        screeningModes sign k (-n) k := by
      rw [d4_deformedCartan_neg_mode n hn, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [d4_oscillator_weight_pairing n hn k i]
      have hqn : q ^ (-n) - q ^ n ≠ 0 := by
        simpa only [neg_neg] using q_mode_sub_ne_zero (-n) (neg_ne_zero.mpr hn)
      have htn : t ^ (-n) - t ^ n ≠ 0 := by
        simpa only [neg_neg] using t_mode_sub_ne_zero (-n) (neg_ne_zero.mpr hn)
      have hqn' : -q ^ n + q ^ (-n) ≠ 0 := by
        simpa only [sub_eq_add_neg, add_comm] using hqn
      have htn' : -t ^ n + t ^ (-n) ≠ 0 := by
        simpa only [sub_eq_add_neg, add_comm] using htn
      simp only [screeningModes, d4_rootLength, neg_neg]
      cases sign <;> split_ifs <;>
        simp only [one_mul, zero_mul] <;>
        field_simp [q_mode_sub_ne_zero n hn, t_mode_sub_ne_zero n hn, hqn, htn] <;>
        ring_nf
      all_goals
        field_simp [hqn', htn']
        ring

/-- The two formal scalar exponential contractions displayed in the
research note, now proved over FR's original coefficient field. -/
theorem d4_minus_scalar_exponential (a : Coefficient) :
    (PowerSeries.exp Coefficient).subst
      (contractionLog (q / a) (q⁻¹ / a)) =
      (1 - PowerSeries.C (q⁻¹ / a) * PowerSeries.X) *
        (1 - PowerSeries.C (q / a) * PowerSeries.X)⁻¹ :=
  exp_contractionLog _ _

theorem d4_plus_scalar_exponential (a : Coefficient) :
    (PowerSeries.exp Coefficient).subst
      (contractionLog (t⁻¹ / a) (t / a)) =
      (1 - PowerSeries.C (t / a) * PowerSeries.X) *
        (1 - PowerSeries.C (t⁻¹ / a) * PowerSeries.X)⁻¹ :=
  exp_contractionLog _ _

/-- The reverse contraction used directly when the screening acts on a
Y-vacuum coefficient: positive screening modes meet negative Y modes. -/
theorem d4_screening_weight_contraction (n : ℤ) (hn : n ≠ 0)
    (k i : RootIndex D₄) (sign : ScreeningSign) :
    screeningModes sign k n k *
      (∑ j : RootIndex D₄, (deformedCartan D₄ (-n))⁻¹ j i *
        oscillatorCommutator D₄ Coefficient q t k j n (-n)) =
    (if k = i then 1 else 0) *
      (match sign with
      | .minus => -(q ^ n - q ^ (-n)) / (n : Coefficient)
      | .plus => (t ^ n - t ^ (-n)) / (n : Coefficient)) := by
  classical
  rw [d4_oscillator_weight_pairing n hn k i]
  have hminus : screeningModes (g := D₄) .minus k n k = -(t ^ n - t ^ (-n))⁻¹ := by
    simp [screeningModes]
  have hplus : screeningModes (g := D₄) .plus k n k = (q ^ n - q ^ (-n))⁻¹ := by
    simp [screeningModes, d4_rootLength]
  cases sign with
  | minus =>
    rw [hminus]
    by_cases hki : k = i
    · simp only [if_pos hki, one_mul]
      calc
        _ = ((t ^ n - t ^ (-n))⁻¹ * (t ^ n - t ^ (-n))) *
            (-(n : Coefficient)⁻¹ * (q ^ n - q ^ (-n))) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (t_mode_sub_ne_zero n hn)]; simp only [one_mul]; ring
    · simp only [if_neg hki, zero_mul, mul_zero]
  | plus =>
    rw [hplus]
    by_cases hki : k = i
    · simp only [if_pos hki, one_mul]
      calc
        _ = ((q ^ n - q ^ (-n))⁻¹ * (q ^ n - q ^ (-n))) *
            ((n : Coefficient)⁻¹ * (t ^ n - t ^ (-n))) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (q_mode_sub_ne_zero n hn)]; simp only [one_mul]; ring
    · simp only [if_neg hki, zero_mul, mul_zero]

/-- Expansion in z/w of the rational factors appearing when a screening
acts on a Y field on the zero-momentum vacuum. -/
theorem d4_minus_scalar_exponential_at_infinity (a : Coefficient) :
    (PowerSeries.exp Coefficient).subst (contractionLog (q⁻¹ * a) (q * a)) =
      (1 - PowerSeries.C (q * a) * PowerSeries.X) *
        (1 - PowerSeries.C (q⁻¹ * a) * PowerSeries.X)⁻¹ :=
  exp_contractionLog _ _

theorem d4_plus_scalar_exponential_at_infinity (a : Coefficient) :
    (PowerSeries.exp Coefficient).subst (contractionLog (t * a) (t⁻¹ * a)) =
      (1 - PowerSeries.C (t⁻¹ * a) * PowerSeries.X) *
        (1 - PowerSeries.C (t * a) * PowerSeries.X)⁻¹ :=
  exp_contractionLog _ _

theorem scalar_zero_mode_normalization (v a : Coefficient) (hv : v ≠ 0) (ha : a ≠ 0) :
    RatFunc.C (v ^ 2) *
      ((1 - RatFunc.C (v⁻¹ / a) * RatFunc.X) /
        (1 - RatFunc.C (v / a) * RatFunc.X)) =
      (RatFunc.X - RatFunc.C (v * a)) /
        (RatFunc.X - RatFunc.C (v⁻¹ * a)) := by
  have hden : (1 - RatFunc.C (v / a) * RatFunc.X : RatFunc Coefficient) ≠ 0 := by
    have hid : (1 - RatFunc.C (v / a) * RatFunc.X : RatFunc Coefficient) =
        -RatFunc.C (v / a) * (RatFunc.X - RatFunc.C (v⁻¹ * a)) := by
      simp only [map_mul, map_div₀, map_inv₀]
      field_simp [ha, hv]
      ring
    rw [hid]
    exact mul_ne_zero (neg_ne_zero.mpr ((map_ne_zero (RatFunc.C)).mpr (div_ne_zero hv ha)))
      (ratFunc_X_sub_C_ne_zero _)
  rw [← mul_div_assoc]
  apply (div_eq_div_iff hden (ratFunc_X_sub_C_ne_zero _)).mpr
  simp only [map_mul, map_div₀, map_inv₀, map_pow]
  field_simp [(map_ne_zero RatFunc.C).mpr hv, (map_ne_zero RatFunc.C).mpr ha]
  ring

/-- Multiplication by the original zero-mode charge factor q² changes
the scalar oscillator rational function into the minus pole factor. -/
theorem d4_minus_zero_mode_normalization (a : Coefficient) (ha : a ≠ 0) :
    RatFunc.C (q ^ (2 : ℤ)) *
      ((1 - RatFunc.C (q⁻¹ / a) * RatFunc.X) /
        (1 - RatFunc.C (q / a) * RatFunc.X)) =
      (RatFunc.X - RatFunc.C (q * a)) /
        (RatFunc.X - RatFunc.C (q⁻¹ * a)) := by
  simpa only [zpow_ofNat] using scalar_zero_mode_normalization q a q_ne_zero ha

/-- The corresponding t⁻² factor from the original plus charge shift. -/
theorem d4_plus_zero_mode_normalization (a : Coefficient) (ha : a ≠ 0) :
    RatFunc.C (t ^ (-2 : ℤ)) *
      ((1 - RatFunc.C (t / a) * RatFunc.X) /
        (1 - RatFunc.C (t⁻¹ / a) * RatFunc.X)) =
      (RatFunc.X - RatFunc.C (t⁻¹ * a)) /
        (RatFunc.X - RatFunc.C (t * a)) := by
  simpa only [inv_inv, zpow_neg, zpow_ofNat, inv_pow] using
    scalar_zero_mode_normalization t⁻¹ a (inv_ne_zero t_ne_zero) ha

end
end FrenkelReshetikhin.D4CounterexampleProof
