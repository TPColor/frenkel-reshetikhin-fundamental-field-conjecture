import D4CounterexampleProof.PoleTaylor
import Mathlib.RingTheory.LaurentSeries

/-! Local Laurent residues of finite principal parts times the original
screening creation series. The Laurent variable here is w-c. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open scoped BigOperators

section General

variable {R : Type*} [CommRing R]

theorem principal_part_residue (F : PowerSeries R) (r : R) (k : ℕ) :
    (HahnSeries.single (-((k : ℤ) + 1)) r * (F : LaurentSeries R)).coeff (-1) =
      r * PowerSeries.coeff k F := by
  rw [HahnSeries.coeff_single_mul]
  have he : (-1 : ℤ) - (-((k : ℤ) + 1)) = (k : ℤ) := by omega
  rw [he, LaurentSeries.coeff_coe_powerSeries]

end General

section PolynomialFactors

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ]

def principalPartPolynomial (v : σ → K) (order : ℕ) (r : Fin order → K) : MvPolynomial σ K :=
  ∑ j : Fin order, MvPolynomial.C (r j / (j.val.factorial : K)) * creationLinearForm v ^ j.val

omit [CharZero K] in
@[simp] theorem principalPartPolynomial_zero (v : σ → K) (r : Fin 0 → K) :
    principalPartPolynomial v 0 r = 0 := by simp [principalPartPolynomial]

omit [CharZero K] in
theorem principalPartPolynomial_one (v : σ → K) (r : Fin 1 → K) :
    principalPartPolynomial v 1 r = MvPolynomial.C (r 0) := by
  simp [principalPartPolynomial]

omit [CharZero K] in
theorem principalPartPolynomial_one_ne_zero (v : σ → K) (r : Fin 1 → K) (hr : r 0 ≠ 0) :
    principalPartPolynomial v 1 r ≠ 0 := by
  rw [principalPartPolynomial_one]
  intro hz
  have he := congrArg (MvPolynomial.constantCoeff) hz
  exact hr (by simpa using he)

omit [CharZero K] in
theorem principalPartPolynomial_simple_ne_zero (v : σ → K) (order : ℕ) (horder : order = 1)
    (r : Fin order → K) (hr : r ⟨0, by omega⟩ ≠ 0) :
    principalPartPolynomial v order r ≠ 0 := by
  subst order
  exact principalPartPolynomial_one_ne_zero v r hr

omit [CharZero K] in
theorem principalPartPolynomial_nonzero_order (v : σ → K) (order : ℕ) (r : Fin order → K)
    (h : principalPartPolynomial v order r ≠ 0) : 0 < order := by
  cases order with
  | zero => exact False.elim (h (principalPartPolynomial_zero v r))
  | succ n => exact Nat.succ_pos n

theorem finite_principal_parts_residue (F : MvPowerSeries σ K) (v : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (v i) * F)
    (c : K) (order : ℕ) (r : Fin order → K) :
    (∑ j : Fin order,
      HahnSeries.single (-((j.val : ℤ) + 1)) (MvPowerSeries.C (r j)) *
        (parameterTaylor (parameterLift F) c : LaurentSeries (MvPowerSeries σ K))).coeff (-1) =
      (principalPartPolynomial v order r : MvPowerSeries σ K) *
        MvPowerSeries.map (Polynomial.evalRingHom c) (parameterLift F) := by
  classical
  rw [HahnSeries.coeff_sum]
  simp_rw [principal_part_residue, parameterTaylor_coeff F v hF c]
  change _ = MvPolynomial.coeToMvPowerSeries.ringHom
    (∑ j : Fin order, MvPolynomial.C (r j / (j.val.factorial : K)) * creationLinearForm v ^ j.val) * _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_C, MvPolynomial.coe_pow, div_eq_mul_inv, map_mul]
  ring

theorem finite_principal_parts_residue_with_factor (G F : MvPowerSeries σ K) (v : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (v i) * F)
    (c : K) (order : ℕ) (r : Fin order → K) :
    (∑ j : Fin order,
      HahnSeries.single (-((j.val : ℤ) + 1)) (MvPowerSeries.C (r j)) *
        ((PowerSeries.C G * parameterTaylor (parameterLift F) c : PowerSeries (MvPowerSeries σ K)) :
          LaurentSeries (MvPowerSeries σ K))).coeff (-1) =
      (principalPartPolynomial v order r : MvPowerSeries σ K) *
        (G * MvPowerSeries.map (Polynomial.evalRingHom c) (parameterLift F)) := by
  classical
  rw [HahnSeries.coeff_sum]
  simp_rw [principal_part_residue, PowerSeries.coeff_C_mul, parameterTaylor_coeff F v hF c]
  change _ = MvPolynomial.coeToMvPowerSeries.ringHom
    (∑ j : Fin order, MvPolynomial.C (r j / (j.val.factorial : K)) * creationLinearForm v ^ j.val) * _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_C, MvPolynomial.coe_pow, div_eq_mul_inv, map_mul]
  ring

end PolynomialFactors

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
