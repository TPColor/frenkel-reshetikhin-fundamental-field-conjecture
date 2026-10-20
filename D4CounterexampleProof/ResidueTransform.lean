import D4CounterexampleProof.ScalarContractions
import Mathlib.Data.Nat.Choose.Cast

/-! The coefficient transform occurring when a rational expansion in
z/w is contracted against a creation exponential. This is a proof-only
linear map, not a redefinition of the original screening operator. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

variable {K : Type*} [Field K]

def residueTransform : PowerSeries K →ₗ[K] PowerSeries K where
  toFun F := PowerSeries.mk (R := K) (fun n => PowerSeries.coeff (n + 1) F / (n.factorial : K))
  map_add' F G := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add, add_div]
  map_smul' a F := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_smul, smul_eq_mul, mul_div_assoc, RingHom.id_apply]

@[simp] theorem residueTransform_coeff (F : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (residueTransform F) = PowerSeries.coeff (n + 1) F / (n.factorial : K) := by
  change PowerSeries.coeff n
    (PowerSeries.mk (R := K) (fun m => PowerSeries.coeff (m + 1) F / (m.factorial : K))) = _
  exact PowerSeries.coeff_mk _ _

@[simp] theorem residueTransform_C (a : K) : residueTransform (PowerSeries.C a) = 0 := by
  ext n
  simp only [residueTransform_coeff, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n),
    zero_div, map_zero]

variable [CharZero K]

/-- The expansion X/(1-cX) of a simple principal part at infinity gives
exactly the exponential at c after the coefficient transform. -/
theorem residueTransform_simple_pole (c : K) :
    residueTransform (PowerSeries.X * (1 - PowerSeries.C c * PowerSeries.X)⁻¹) =
      PowerSeries.rescale c (PowerSeries.exp K) := by
  rw [← geometric_powerSeries_inverse c]
  ext n
  simp only [residueTransform_coeff, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

/-- The same transform for an order k+1 principal part. The standard
`invOneSubPow` series is proved in Mathlib to invert (1-X)^(k+1).
Thus all higher pole orders produce the polynomial X^k/k! times the
same exponential at the pole label. -/
theorem residueTransform_higher_pole (c : K) (k : ℕ) :
    residueTransform (PowerSeries.X ^ (k + 1) *
      PowerSeries.rescale c (PowerSeries.invOneSubPow K (k + 1)).val) =
      PowerSeries.C ((k.factorial : K)⁻¹) *
        (PowerSeries.X ^ k * PowerSeries.rescale c (PowerSeries.exp K)) := by
  ext n
  rw [residueTransform_coeff, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  by_cases hkn : k ≤ n
  · have hkn' : k + 1 ≤ n + 1 := Nat.add_le_add_right hkn 1
    rw [if_pos hkn', if_pos hkn]
    simp only [Nat.add_sub_add_right, PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
      PowerSeries.coeff_exp]
    rw [show k + (n - k) = n by omega, Nat.cast_choose K hkn]
    simp only [map_div₀, map_one, map_natCast]
    have hnf : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hkf : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hdf : ((n - k).factorial : K) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
    field_simp
  · have hkn' : ¬k + 1 ≤ n + 1 := by omega
    simp only [if_neg hkn', if_neg hkn, zero_div, mul_zero]

/-- Finite principal-part expansions transform termwise, while their
constant polynomial part contributes no residue. -/
theorem residueTransform_finite_principal_parts {ι : Type*} (s : Finset ι)
    (a : K) (r c : ι → K) (k : ι → ℕ) :
    residueTransform (PowerSeries.C a + ∑ i ∈ s, r i •
      (PowerSeries.X ^ (k i + 1) *
        PowerSeries.rescale (c i) (PowerSeries.invOneSubPow K (k i + 1)).val)) =
      ∑ i ∈ s, r i • (PowerSeries.C (((k i).factorial : K)⁻¹) *
        (PowerSeries.X ^ k i * PowerSeries.rescale (c i) (PowerSeries.exp K))) := by
  rw [map_add, residueTransform_C, zero_add, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, residueTransform_higher_pole]

end
end FrenkelReshetikhin.D4CounterexampleProof
