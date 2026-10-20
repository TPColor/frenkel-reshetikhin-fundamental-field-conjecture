import D4CounterexampleProof.ParameterEuler

/-! Higher derivatives in the pole parameter of a finite-mode
exponential are polynomial multiples of that same exponential. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open scoped BigOperators

section General

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ]
attribute [local instance] Classical.propDecidable

def creationLinearForm (v : σ → K) : MvPolynomial σ K :=
  ∑ i : σ, MvPolynomial.C (v i) * MvPolynomial.X i

omit [CharZero K] in
theorem creationLinearForm_coe (v : σ → K) :
    (creationLinearForm v : MvPowerSeries σ K) =
      ∑ i : σ, MvPowerSeries.C (v i) * MvPowerSeries.X i := by
  change MvPolynomial.coeToMvPowerSeries.ringHom
    (∑ i : σ, MvPolynomial.C (v i) * MvPolynomial.X i) = _
  rw [map_sum]
  simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_mul,
    MvPolynomial.coe_C, MvPolynomial.coe_X]

omit [CharZero K] [Fintype σ] in
theorem poleDerivative_map_C (F : MvPowerSeries σ K) :
    poleDerivative (MvPowerSeries.map Polynomial.C F) = 0 := by
  apply MvPowerSeries.ext
  intro d
  change Polynomial.derivative (Polynomial.C (F d)) = 0
  exact Polynomial.derivative_C

theorem parameterLift_poleDerivative (F : MvPowerSeries σ K) (v : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (v i) * F) :
    poleDerivative (parameterLift F) =
      MvPowerSeries.map Polynomial.C (creationLinearForm v : MvPowerSeries σ K) * parameterLift F := by
  have hX : (MvPowerSeries.C (Polynomial.X : Polynomial K) :
      MvPowerSeries σ (Polynomial K)) ≠ 0 := by
    intro h
    have he := congrArg MvPowerSeries.constantCoeff h
    exact Polynomial.X_ne_zero (by
      simpa only [MvPowerSeries.constantCoeff_C, map_zero] using he)
  apply mul_left_cancel₀ hX
  rw [parameterLift_euler]
  simp_rw [parameterLift_pderiv F v hF]
  rw [creationLinearForm_coe, map_sum]
  simp only [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- An arbitrary higher pole derivative has exactly the polynomial
factor L^k. The exponent vector is unchanged. -/
theorem parameterLift_iterate_poleDerivative (F : MvPowerSeries σ K) (v : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (v i) * F) (k : ℕ) :
    (poleDerivative (K := K) (σ := σ))^[k] (parameterLift F) =
      MvPowerSeries.map Polynomial.C (creationLinearForm v : MvPowerSeries σ K) ^ k * parameterLift F := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz,
      parameterLift_poleDerivative F v hF, Derivation.leibniz_pow, poleDerivative_map_C]
    simp only [smul_eq_mul]
    rw [pow_succ]
    ring

theorem evaluate_parameterLift_iterate (F : MvPowerSeries σ K) (v : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (v i) * F)
    (c : K) (k : ℕ) :
    MvPowerSeries.map (Polynomial.evalRingHom c)
        ((poleDerivative (K := K) (σ := σ))^[k] (parameterLift F)) =
      ((creationLinearForm v ^ k : MvPolynomial σ K) : MvPowerSeries σ K) *
        MvPowerSeries.map (Polynomial.evalRingHom c) (parameterLift F) := by
  rw [parameterLift_iterate_poleDerivative F v hF, map_mul, map_pow]
  have he : MvPowerSeries.map (Polynomial.evalRingHom c)
      (MvPowerSeries.map Polynomial.C (creationLinearForm v : MvPowerSeries σ K)) =
      (creationLinearForm v : MvPowerSeries σ K) := by
    ext d
    simp only [MvPowerSeries.coeff_map, Polynomial.coe_evalRingHom, Polynomial.eval_C]
  rw [he, MvPolynomial.coe_pow]

end General

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
