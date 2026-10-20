import D4CounterexampleProof.ScalarContractions

/-! Formal exponential product laws for zero-constant series over the
original coefficient fields. These are used to convert logarithmic
oscillator contractions to finite rational factor products. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

theorem exp_subst_constantCoeff (F : PowerSeries K) (hF : PowerSeries.constantCoeff F = 0) :
    PowerSeries.constantCoeff ((PowerSeries.exp K).subst F) = 1 := by
  change MvPowerSeries.constantCoeff ((PowerSeries.exp K).subst F) = 1
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hF)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro n hn
    have hz : MvPowerSeries.constantCoeff F = 0 := hF
    simp only [map_pow, hz, zero_pow hn, smul_zero]

theorem exp_subst_derivative (F : PowerSeries K) (hF : PowerSeries.constantCoeff F = 0) :
    PowerSeries.derivative K ((PowerSeries.exp K).subst F) =
      PowerSeries.derivative K F * (PowerSeries.exp K).subst F := by
  rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hF),
    PowerSeries.derivative_exp, mul_comm]

theorem exp_subst_add (F G : PowerSeries K)
    (hF : PowerSeries.constantCoeff F = 0) (hG : PowerSeries.constantCoeff G = 0) :
    (PowerSeries.exp K).subst (F + G) =
      (PowerSeries.exp K).subst F * (PowerSeries.exp K).subst G := by
  have hFG : PowerSeries.constantCoeff (F + G) = 0 := by simp [hF, hG]
  apply powerSeries_linear_ode_unique _ _ (PowerSeries.derivative K (F + G))
  · exact exp_subst_derivative _ hFG
  · rw [Derivation.leibniz, exp_subst_derivative F hF, exp_subst_derivative G hG, map_add]
    simp only [smul_eq_mul]
    ring
  · exact exp_subst_constantCoeff _ hFG
  · simp only [map_mul, exp_subst_constantCoeff F hF, exp_subst_constantCoeff G hG, one_mul]

@[simp] theorem exp_subst_zero : (PowerSeries.exp K).subst (0 : PowerSeries K) = 1 := by
  rw [PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem exp_subst_neg (F : PowerSeries K) (hF : PowerSeries.constantCoeff F = 0) :
    (PowerSeries.exp K).subst (-F) = ((PowerSeries.exp K).subst F)⁻¹ := by
  have hnF : PowerSeries.constantCoeff (-F) = 0 := by simp [hF]
  have h := exp_subst_add F (-F) hF hnF
  rw [add_neg_cancel, exp_subst_zero] at h
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [exp_subst_constantCoeff F hF]; exact one_ne_zero)).mpr
  exact (mul_comm _ _).trans h.symm

theorem exp_subst_nsmul (F : PowerSeries K) (hF : PowerSeries.constantCoeff F = 0) (n : ℕ) :
    (PowerSeries.exp K).subst (n • F) = ((PowerSeries.exp K).subst F) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, exp_subst_add _ _ (by simp [hF]) hF, ih, pow_succ]

theorem exp_subst_zsmul (F : PowerSeries K) (hF : PowerSeries.constantCoeff F = 0) (n : ℤ) :
    (PowerSeries.exp K).subst (n • F) = match n with
      | .ofNat k => ((PowerSeries.exp K).subst F) ^ k
      | .negSucc k => (((PowerSeries.exp K).subst F) ^ (k + 1))⁻¹ := by
  cases n with
  | ofNat n => simpa using exp_subst_nsmul F hF n
  | negSucc n =>
    rw [negSucc_zsmul, exp_subst_neg _ (by simp [hF]), exp_subst_nsmul F hF]

theorem exp_subst_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries K)
    (hF : ∀ i ∈ s, PowerSeries.constantCoeff (F i) = 0) :
    (PowerSeries.exp K).subst (∑ i ∈ s, F i) =
      ∏ i ∈ s, (PowerSeries.exp K).subst (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi,
      exp_subst_add _ _ (hF i (by simp)) (by
        rw [map_sum]; apply Finset.sum_eq_zero; intro j hj; exact hF j (by simp [hj])),
      ih (fun j hj => hF j (by simp [hj]))]

end
end FrenkelReshetikhin.D4CounterexampleProof
