import D4CounterexampleProof.FormalExponentialProducts

/-! Finite rational contraction products as units of formal power
series, including arbitrary signed Laurent exponents. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem powerSeries_unit_inv (u : (PowerSeries K)ˣ) :
    ((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) = (u : PowerSeries K)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one
    ((PowerSeries.isUnit_iff_constantCoeff.mp u.isUnit).ne_zero)).mpr
  exact u.inv_val

def expSeriesUnit (F : PowerSeries K) (hF : PowerSeries.constantCoeff F = 0) :
    (PowerSeries K)ˣ where
  val := (PowerSeries.exp K).subst F
  inv := (PowerSeries.exp K).subst (-F)
  val_inv := by
    rw [← exp_subst_add F (-F) hF (by simp [hF]), add_neg_cancel, exp_subst_zero]
  inv_val := by
    rw [mul_comm, ← exp_subst_add F (-F) hF (by simp [hF]), add_neg_cancel, exp_subst_zero]

theorem exp_subst_zsmul_unit (F : PowerSeries K)
    (hF : PowerSeries.constantCoeff F = 0) (n : ℤ) :
    (PowerSeries.exp K).subst (n • F) = (expSeriesUnit F hF ^ n : (PowerSeries K)ˣ) := by
  rw [exp_subst_zsmul F hF n]
  cases n with
  | ofNat n => rfl
  | negSucc n =>
    rw [zpow_negSucc, powerSeries_unit_inv]
    rfl

def oneSubSeriesUnit (c : K) : (PowerSeries K)ˣ where
  val := 1 - PowerSeries.C c * PowerSeries.X
  inv := (1 - PowerSeries.C c * PowerSeries.X)⁻¹
  val_inv := PowerSeries.mul_inv_cancel _ (by simp)
  inv_val := PowerSeries.inv_mul_cancel _ (by simp)

theorem expSeriesUnit_contractionLog (a b : K) :
    expSeriesUnit (contractionLog a b) (contractionLog_constantCoeff a b) =
      oneSubSeriesUnit b / oneSubSeriesUnit a := by
  apply Units.ext
  exact exp_contractionLog a b

/-- Exponentiating the complete finite Laurent logarithm gives the
product of its exact rational oscillator factors with signed powers. -/
theorem exp_subst_contraction_product {ι : Type*} (f : ι →₀ ℤ) (a b : ι → K) :
    (PowerSeries.exp K).subst (f.sum fun i n => n • contractionLog (a i) (b i)) =
      (f.prod (fun i n => (oneSubSeriesUnit (b i) / oneSubSeriesUnit (a i)) ^ n) :
        (PowerSeries K)ˣ) := by
  classical
  rw [Finsupp.sum, exp_subst_sum]
  · change (∏ i ∈ f.support, (PowerSeries.exp K).subst (f i • contractionLog (a i) (b i))) =
      ((∏ i ∈ f.support, (oneSubSeriesUnit (b i) / oneSubSeriesUnit (a i)) ^ f i :
        (PowerSeries K)ˣ) : PowerSeries K)
    change _ = (Units.coeHom (PowerSeries K)) _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [exp_subst_zsmul_unit _ (contractionLog_constantCoeff _ _), expSeriesUnit_contractionLog]
    rfl
  · intro i hi
    simp [contractionLog_constantCoeff]

end
end FrenkelReshetikhin.D4CounterexampleProof
