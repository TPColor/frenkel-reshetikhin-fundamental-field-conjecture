import StatementDefinitions
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Ring

/-! Formal scalar contractions in the original FR setting. The power
series variable is the ratio of field arguments, not an h-adic parameter
or a specialization of q or t. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

section General

variable {K : Type*} [Field K] [CharZero K]

theorem powerSeries_linear_ode_unique (F G A : PowerSeries K)
    (hF : PowerSeries.derivative K F = A * F)
    (hG : PowerSeries.derivative K G = A * G)
    (hF0 : PowerSeries.constantCoeff F = 1) (hG0 : PowerSeries.constantCoeff G = 1) : F = G := by
  have hGnz : PowerSeries.constantCoeff G ≠ 0 := by rw [hG0]; exact one_ne_zero
  have hcancel := PowerSeries.mul_inv_cancel G hGnz
  have hicancel := PowerSeries.inv_mul_cancel G hGnz
  have hratio : F * G⁻¹ = 1 := by
    apply PowerSeries.derivative.ext
    · rw [Derivation.leibniz, PowerSeries.derivative_inv', hF, hG]
      simp only [smul_eq_mul, Derivation.map_one_eq_zero]
      calc
        _ = A * F * G⁻¹ * (1 - G * G⁻¹) := by ring
        _ = 0 := by rw [hcancel, sub_self, mul_zero]
    · simp only [map_mul, PowerSeries.constantCoeff_inv, hF0, hG0, inv_one, mul_one, map_one]
  have he := congrArg (fun p : PowerSeries K => p * G) hratio
  simpa only [mul_assoc, hicancel, mul_one, one_mul] using he

theorem geometric_powerSeries_inverse (a : K) :
    (PowerSeries.mk fun n => a ^ n) = (1 - PowerSeries.C a * PowerSeries.X)⁻¹ := by
  have hc : PowerSeries.constantCoeff (1 - PowerSeries.C a * PowerSeries.X) ≠ 0 := by simp
  apply (PowerSeries.eq_inv_iff_mul_eq_one hc).mpr
  rw [mul_sub, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [← mul_assoc, map_sub, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), pow_succ, sub_self]

def contractionLog (a b : K) : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 0 else (a ^ n - b ^ n) / (n : K)

omit [CharZero K] in
@[simp] theorem contractionLog_constantCoeff (a b : K) :
    PowerSeries.constantCoeff (contractionLog a b) = 0 := by
  simp [contractionLog, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem contractionLog_derivative (a b : K) :
    PowerSeries.derivative K (contractionLog a b) =
      PowerSeries.C a * (1 - PowerSeries.C a * PowerSeries.X)⁻¹ -
        PowerSeries.C b * (1 - PowerSeries.C b * PowerSeries.X)⁻¹ := by
  rw [← geometric_powerSeries_inverse a, ← geometric_powerSeries_inverse b]
  ext n
  rw [PowerSeries.coeff_derivative, contractionLog, PowerSeries.coeff_mk,
    if_neg (Nat.succ_ne_zero n), map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Nat.cast_add, Nat.cast_one, div_mul_cancel₀ _ hn, pow_succ, pow_succ]
  ring

theorem exp_contractionLog (a b : K) :
    (PowerSeries.exp K).subst (contractionLog a b) =
      (1 - PowerSeries.C b * PowerSeries.X) * (1 - PowerSeries.C a * PowerSeries.X)⁻¹ := by
  let F := (PowerSeries.exp K).subst (contractionLog a b)
  let U : PowerSeries K := 1 - PowerSeries.C a * PowerSeries.X
  let V : PowerSeries K := 1 - PowerSeries.C b * PowerSeries.X
  let A : PowerSeries K := PowerSeries.C a * U⁻¹ - PowerSeries.C b * V⁻¹
  have hU0 : PowerSeries.constantCoeff U = 1 := by simp [U]
  have hV0 : PowerSeries.constantCoeff V = 1 := by simp [V]
  have hU : U * U⁻¹ = 1 := PowerSeries.mul_inv_cancel U (by rw [hU0]; exact one_ne_zero)
  have hV : V * V⁻¹ = 1 := PowerSeries.mul_inv_cancel V (by rw [hV0]; exact one_ne_zero)
  have hdu : PowerSeries.derivative K U = -PowerSeries.C a := by simp [U]
  have hdv : PowerSeries.derivative K V = -PowerSeries.C b := by simp [V]
  have hF : PowerSeries.derivative K F = A * F := by
    dsimp only [F]
    rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero'
        (contractionLog_constantCoeff a b)), PowerSeries.derivative_exp, contractionLog_derivative]
    exact mul_comm _ _
  have hR : PowerSeries.derivative K (V * U⁻¹) = A * (V * U⁻¹) := by
    rw [Derivation.leibniz, PowerSeries.derivative_inv', hdu, hdv]
    simp only [smul_eq_mul]
    change V * (-U⁻¹ ^ 2 * -PowerSeries.C a) + U⁻¹ * -PowerSeries.C b =
      (PowerSeries.C a * U⁻¹ - PowerSeries.C b * V⁻¹) * (V * U⁻¹)
    calc
      _ = PowerSeries.C a * U⁻¹ ^ 2 * V - PowerSeries.C b * U⁻¹ := by ring
      _ = PowerSeries.C a * U⁻¹ ^ 2 * V - PowerSeries.C b * U⁻¹ * (V * V⁻¹) := by rw [hV, mul_one]
      _ = _ := by ring
  have hF0 : PowerSeries.constantCoeff F = 1 := by
    dsimp only [F]
    change MvPowerSeries.constantCoeff ((PowerSeries.exp K).subst (contractionLog a b)) = 1
    rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero'
      (contractionLog_constantCoeff a b))]
    rw [finsum_eq_single _ 0]
    · simp
    · intro n hn
      have hz : MvPowerSeries.constantCoeff (contractionLog a b) = 0 :=
        contractionLog_constantCoeff a b
      simp only [map_pow, hz, zero_pow hn, smul_zero]
  exact powerSeries_linear_ode_unique F (V * U⁻¹) A hF hR hF0 (by
    rw [map_mul, PowerSeries.constantCoeff_inv, hU0, hV0, inv_one, mul_one])

end General

end
end FrenkelReshetikhin.D4CounterexampleProof
