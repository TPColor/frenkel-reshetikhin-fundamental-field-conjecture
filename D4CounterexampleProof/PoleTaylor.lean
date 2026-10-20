import D4CounterexampleProof.ScreeningPoleDerivatives
import Mathlib.Algebra.Polynomial.Taylor

/-! Taylor coefficients in a pole parameter, with their factorials.
These are Taylor expansions of the derived parameter family of the
original screening series, rather than new field definitions. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open scoped BigOperators

section General

variable {K σ : Type*} [Field K] [CharZero K]

theorem taylor_coeff_iterate_derivative (p : Polynomial K) (c : K) (k : ℕ) :
    (Polynomial.taylor c p).coeff k =
      (Polynomial.derivative^[k] p).eval c / (k.factorial : K) := by
  rw [Polynomial.taylor_coeff]
  have he := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) (k := k)) p
  have hev := congrArg (Polynomial.eval c) he
  change (Polynomial.evalRingHom c) (k.factorial • Polynomial.hasseDeriv k p) =
    Polynomial.eval c (Polynomial.derivative^[k] p) at hev
  rw [map_nsmul] at hev
  have hf : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  apply (eq_div_iff hf).mpr
  simpa only [Polynomial.coe_evalRingHom, nsmul_eq_mul, mul_comm] using hev

omit [CharZero K] in
theorem poleDerivative_iterate_coeff (F : MvPowerSeries σ (Polynomial K))
    (k : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d ((poleDerivative (K := K) (σ := σ))^[k] F) =
      Polynomial.derivative^[k] (MvPowerSeries.coeff d F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change Polynomial.derivative
        (MvPowerSeries.coeff d ((poleDerivative (K := K) (σ := σ))^[k] F)) = _
    rw [ih]

def parameterTaylor (F : MvPowerSeries σ (Polynomial K)) (c : K) :
    PowerSeries (MvPowerSeries σ K) :=
  PowerSeries.mk (R := MvPowerSeries σ K)
    (fun k => (show MvPowerSeries σ K from fun d => (Polynomial.taylor c (F d)).coeff k))

variable [Fintype σ]

theorem parameterTaylor_coeff (F : MvPowerSeries σ K) (v : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (v i) * F) (c : K) (k : ℕ) :
    PowerSeries.coeff k (parameterTaylor (parameterLift F) c) =
      MvPowerSeries.C ((k.factorial : K)⁻¹) *
        (((creationLinearForm v ^ k : MvPolynomial σ K) : MvPowerSeries σ K) *
          MvPowerSeries.map (Polynomial.evalRingHom c) (parameterLift F)) := by
  classical
  apply MvPowerSeries.ext
  intro d
  have he := congrArg (MvPowerSeries.coeff d) (evaluate_parameterLift_iterate F v hF c k)
  rw [MvPowerSeries.coeff_map, poleDerivative_iterate_coeff] at he
  rw [parameterTaylor, PowerSeries.coeff_mk]
  change (Polynomial.taylor c (parameterLift F d)).coeff k =
    MvPowerSeries.coeff d (MvPowerSeries.C ((k.factorial : K)⁻¹) *
      (((creationLinearForm v ^ k : MvPolynomial σ K) : MvPowerSeries σ K) *
        MvPowerSeries.map (Polynomial.evalRingHom c) (parameterLift F)))
  rw [taylor_coeff_iterate_derivative, MvPowerSeries.coeff_C_mul]
  change (Polynomial.evalRingHom c)
      (Polynomial.derivative^[k] (MvPowerSeries.coeff d (parameterLift F))) / (k.factorial : K) = _
  rw [he]
  exact div_eq_inv_mul _ _

end General

open OriginalFR OriginalFR.Fields

local instance poleTaylorCoefficientField : _root_.Field Coefficient := inferInstance

/-- The local Taylor coefficient responsible for an order k+1 pole is
the original screened creation exponential times L^k/k!. -/
theorem firstScreeningSeries_taylor_coeff
    (sign : ScreeningSign) (root : Fin 4) (c : Scalars) (k : ℕ) :
    PowerSeries.coeff k
        (parameterTaylor (parameterLift (firstScreeningSeries sign root 1)) c) =
      MvPowerSeries.C ((k.factorial : Scalars)⁻¹) *
        (((creationLinearForm (firstScreeningVector sign root) ^ k :
            MvPolynomial (Fin 4) Scalars) : MvPowerSeries (Fin 4) Scalars) *
          firstScreeningSeries sign root c) := by
  have hF (j : Fin 4) :
      MvPowerSeries.pderiv Scalars j (firstScreeningSeries sign root 1) =
        MvPowerSeries.C (firstScreeningVector sign root j) * firstScreeningSeries sign root 1 := by
    simpa only [mul_one] using firstScreeningSeries_pderiv sign root j 1
  rw [parameterTaylor_coeff _ _ hF, firstScreeningSeries_parameterLift]

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
