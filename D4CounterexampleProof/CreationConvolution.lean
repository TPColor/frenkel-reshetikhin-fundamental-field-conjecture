import D4CounterexampleProof.ScreeningCoefficientReduction
import D4CounterexampleProof.FirstModeSubstitution

/-! The original screened Fourier coefficients assembled as a product
of the elementary creation series and the scalar residue transform. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance creationConvolutionField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

section General

variable {K σ : Type*} [_root_.Field K] [DecidableEq σ]

theorem coeff_subst_scaled_X (F : PowerSeries K) (s : K) (i : σ) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (F.subst (s • MvPowerSeries.X i)) =
      if e = Finsupp.single i (e i) then s ^ e i * PowerSeries.coeff (e i) F else 0 := by
  have h : F.subst (s • (MvPowerSeries.X i : MvPowerSeries σ K)) =
      (PowerSeries.rescale s F).subst (MvPowerSeries.X i) := by
    rw [PowerSeries.rescale_eq_subst,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.smul_X' (R := K) s)
        (PowerSeries.HasSubst.X (S := K) i),
      PowerSeries.subst_smul (PowerSeries.HasSubst.X (S := K) i),
      PowerSeries.subst_X (PowerSeries.HasSubst.X (S := K) i)]
  rw [h, PowerSeries.coeff_subst_single, PowerSeries.coeff_rescale]

theorem coeff_mul_subst_scaled_X (E : MvPowerSeries σ K) (F : PowerSeries K)
    (s : K) (i : σ) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (E * F.subst (s • MvPowerSeries.X i)) =
      ∑ k ∈ Finset.range (e i + 1),
        MvPowerSeries.coeff (e - Finsupp.single i k) E *
          (s ^ k * PowerSeries.coeff k F) := by
  classical
  rw [MvPowerSeries.coeff_mul]
  symm
  apply Finset.sum_bij_ne_zero (fun k _ _ => (e - Finsupp.single i k, Finsupp.single i k))
  · intro k hk hne
    apply Finset.mem_antidiagonal.mpr
    apply tsub_add_cancel_of_le
    exact Finsupp.single_le_iff.mpr (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
  · intro a ha hna b hb hnb heq
    have h := congrArg (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) => p.2 i) heq
    simpa only [Finsupp.single_eq_same] using h
  · intro p hp hne
    have hadd := Finset.mem_antidiagonal.mp hp
    have hn := (mul_ne_zero_iff.mp hne).2
    rw [coeff_subst_scaled_X] at hn
    have hs : p.2 = Finsupp.single i (p.2 i) := by
      by_contra h
      exact hn (if_neg h)
    have hk : p.2 i ≤ e i := by
      have hi := congrArg (fun d : σ →₀ ℕ => d i) hadd
      simp only [Finsupp.add_apply] at hi
      omega
    have hleft : e - Finsupp.single i (p.2 i) = p.1 := by
      rw [← hs, ← hadd, add_tsub_cancel_right]
    refine ⟨p.2 i, Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · rw [hleft]
      have hn' := hne
      rw [coeff_subst_scaled_X, if_pos hs] at hn'
      exact hn'
    · exact Prod.ext hleft hs.symm
  · intro k hk hne
    rw [coeff_subst_scaled_X, Finsupp.single_eq_same, if_pos rfl]

end General

theorem firstScreening_creationLinearForm (sign : ScreeningSign) (i : Fin 4) :
    (creationLinearForm (firstScreeningVector sign i) : MvPowerSeries (Fin 4) Scalars) =
      RatFunc.C (screeningModes (g := D₄) sign i (-1) i) • MvPowerSeries.X i := by
  rw [creationLinearForm_coe, Finset.sum_eq_single i]
  · rw [firstScreeningVector, MvPowerSeries.smul_eq_C_mul]
  · intro j hj hji
    have hz : screeningModes (g := D₄) sign i (-1) j = 0 := by
      cases sign <;> unfold screeningModes <;> split_ifs with heq
      all_goals first | rfl | exact (hji (Fin.ext (congrArg Fin.val heq))).elim
    rw [firstScreeningVector, hz, map_zero, map_zero, zero_mul]
  · simp

/-- The screening/residue-transform identity for the actual original
operator, proved from its normal words and locally finite mode sums. -/
theorem screenedVacuumProjection_residueTransform (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄)) :
    screenedVacuumProjection sign i
      (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors)) =
      MvPowerSeries.killCompl firstModeEmbedding
        ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients none) *
      (residueTransform (((PowerSeries.exp Coefficient).subst
        (screeningScalarLog sign (monomialOfFactors factors) i)).map RatFunc.C)).subst
        (creationLinearForm (firstScreeningVector sign i) : MvPowerSeries (Fin 4) Scalars) := by
  apply MvPowerSeries.ext
  intro e
  rw [coeff_screenedVacuumProjection_convolution, firstScreening_creationLinearForm,
    coeff_mul_subst_scaled_X]
  apply Finset.sum_congr rfl
  intro k hk
  rw [MvPowerSeries.coeff_killCompl, residueTransform_coeff]
  simp only [PowerSeries.coeff, MvPowerSeries.coeff_map]
  simp only [MvPowerSeries.coeff_apply]
  ring

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
