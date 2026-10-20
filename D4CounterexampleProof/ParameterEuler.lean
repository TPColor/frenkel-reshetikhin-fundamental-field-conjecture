import D4CounterexampleProof.ParameterDerivatives

/-! Euler's degree identity for a parameter-scaled creation series. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open scoped BigOperators

section General

variable {R σ : Type*} [CommRing R]
attribute [local instance] Classical.propDecidable

theorem coeff_X_pderiv (F : MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (MvPowerSeries.X i * MvPowerSeries.pderiv R i F) =
      (d i : R) * MvPowerSeries.coeff d F := by
  classical
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
  by_cases hi : Finsupp.single i 1 ≤ d
  · rw [if_pos hi, one_mul, MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hi]
    have hn : (d - Finsupp.single i 1 : σ →₀ ℕ) i + 1 = d i := by
      have hdi := Finsupp.single_le_iff.mp hi
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    have hcast : (((d - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : R) + 1 = (d i : R) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : R)) hn
    rw [hcast]
    exact mul_comm _ _
  · have hdi : d i = 0 := by
      have hlt : ¬ 1 ≤ d i := fun h => hi (Finsupp.single_le_iff.mpr h)
      omega
    simp only [if_neg hi, hdi, Nat.cast_zero, zero_mul]

end General

section Parameter

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ]
attribute [local instance] Classical.propDecidable

theorem parameterLift_euler (F : MvPowerSeries σ K) :
    MvPowerSeries.C Polynomial.X * poleDerivative (parameterLift F) =
      ∑ i : σ, MvPowerSeries.X i * MvPowerSeries.pderiv (Polynomial K) i (parameterLift F) := by
  classical
  apply MvPowerSeries.ext
  intro d
  change MvPowerSeries.coeff d (MvPowerSeries.C Polynomial.X * poleDerivative (parameterLift F)) =
    MvPowerSeries.coeff d (∑ i : σ,
      MvPowerSeries.X i * MvPowerSeries.pderiv (Polynomial K) i (parameterLift F))
  rw [MvPowerSeries.coeff_C_mul, map_sum]
  simp_rw [coeff_X_pderiv]
  rw [← Finset.sum_mul]
  have hsum : (∑ i : σ, (d i : Polynomial K)) = ((d.sum (fun _ n => n) : ℕ) : Polynomial K) := by
    rw [← Nat.cast_sum]
    congr 1
    exact (d.sum_fintype (fun _ n => n) (by simp)).symm
  rw [hsum]
  change Polynomial.X * Polynomial.derivative
      (Polynomial.C (F d) * Polynomial.X ^ d.sum (fun _ n => n)) =
    ((d.sum (fun _ n => n) : ℕ) : Polynomial K) *
      (Polynomial.C (F d) * Polynomial.X ^ d.sum (fun _ n => n))
  rw [Polynomial.derivative_C_mul_X_pow]
  generalize d.sum (fun _ n => n) = N
  cases N with
  | zero => simp
  | succ n =>
    simp only [map_mul, Polynomial.C_eq_natCast, Nat.add_one_sub_one, pow_succ]
    ring

end Parameter

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
