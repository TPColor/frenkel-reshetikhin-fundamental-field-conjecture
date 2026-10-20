import D4CounterexampleProof.Integrability
import Mathlib.Tactic.FieldSimp

/-! Quantum sl₂ strings derived from the original mode-zero current
relations. No character formula or finite-type replacement is assumed. -/

namespace FrenkelReshetikhin.OriginalFR.Drinfeld

noncomputable section

section Scalar

variable {K : Type*} [Field K]

theorem qInteger_string_recurrence (x : K) (hx : x ≠ 0) (n k : ℤ) :
    qInteger x (k + 1) * qInteger x (n - k) =
      qInteger x k * qInteger x (n - k + 1) + qInteger x (n - 2 * k) := by
  have hpow : x ^ (2 * k) = (x ^ k) ^ 2 := by
    rw [mul_comm (2 : ℤ), zpow_mul]
    exact zpow_ofNat _ _
  simp only [qInteger, zpow_sub₀ hx, zpow_add₀ hx, zpow_neg, zpow_one, hpow]
  field_simp
  ring

theorem qInteger_one (x : K) (hden : x - x⁻¹ ≠ 0) : qInteger x 1 = 1 := by
  simpa only [qInteger, zpow_one, zpow_neg_one] using div_self hden

end Scalar

variable (g : SimpleLieType)

theorem quantum_root_parameter_sub_inv_ne_zero (i : RootIndex g) :
    quantumQ ^ rootLength g i - (quantumQ ^ rootLength g i)⁻¹ ≠ 0 := by
  intro hz
  have he : quantumQ ^ (rootLength g i : ℤ) = quantumQ ^ (-(rootLength g i : ℤ)) := by
    simpa only [zpow_natCast, zpow_neg] using sub_eq_zero.mp hz
  have hn := D4CounterexampleProof.ratFunc_X_zpow_injective ℂ he
  have hp : (0 : ℤ) < rootLength g i := by exact_mod_cast rootLength_pos g i
  omega

theorem quantum_qInteger_ne_zero (i : RootIndex g) (n : ℤ) (hn : n ≠ 0) :
    qInteger (quantumQ ^ rootLength g i) n ≠ 0 := by
  apply div_ne_zero
  · apply sub_ne_zero.mpr
    intro he
    have he' : quantumQ ^ ((rootLength g i : ℤ) * n) =
        quantumQ ^ ((rootLength g i : ℤ) * -n) := by
      simpa only [zpow_mul, zpow_natCast] using he
    have hh := D4CounterexampleProof.ratFunc_X_zpow_injective ℂ he'
    have hr : (rootLength g i : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (rootLength_pos g i)
    have hm := mul_left_cancel₀ hr hh
    omega
  · exact quantum_root_parameter_sub_inv_ne_zero g i

/-- The standard quantum highest-weight string coefficient is derived
from the presented current commutator on the actual weight vectors. -/
theorem raising_lowering_highest_string {d : ℕ} (V : Representation g d)
    (weight : Weight g) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace g V weight) (i : RootIndex g)
    (hhigh : V (quotientMap g (x g true i 0)) v = 0) (k : ℕ) :
    V (quotientMap g (x g true i 0))
        ((V (quotientMap g (x g false i 0)) ^ (k + 1)) v) =
      (qInteger (quantumQ ^ rootLength g i) ((k : ℤ) + 1) *
        qInteger (quantumQ ^ rootLength g i) (weight i - k)) •
          ((V (quotientMap g (x g false i 0)) ^ k) v) := by
  induction k with
  | zero =>
    have h := opposite_zero_currents_on_weightVector g V weight v hv i
    rw [hhigh, map_zero, sub_zero] at h
    simpa only [Nat.cast_zero, zero_add, sub_zero, qInteger_one _
      (quantum_root_parameter_sub_inv_ne_zero g i), one_mul,
      pow_one, pow_zero, Module.End.one_apply] using h
  | succ k ih =>
    have hw := current_pow_maps_weightSpace g V weight v hv false i 0 (k + 1)
    have h := opposite_zero_currents_on_weightVector g V _ _ hw i
    have hweight : (weight + ((k + 1 : ℕ) : ℤ) • (sign false • simpleRoot g i)) i =
        weight i - 2 * ((k : ℤ) + 1) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sign, Bool.false_eq_true,
        if_false, simpleRoot, cartan_diagonal, Nat.cast_add, Nat.cast_one]
      ring
    rw [hweight, ih, map_smul] at h
    have heq := (sub_eq_iff_eq_add).mp h
    rw [pow_succ', Module.End.mul_apply]
    rw [heq]
    have hf : V (quotientMap g (x g false i 0))
        ((V (quotientMap g (x g false i 0)) ^ k) v) =
          (V (quotientMap g (x g false i 0)) ^ (k + 1)) v := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hf, ← add_smul]
    have hrec := qInteger_string_recurrence (quantumQ ^ rootLength g i)
      (pow_ne_zero _ RatFunc.X_ne_zero) (weight i) ((k : ℤ) + 1)
    rw [Nat.cast_succ]
    congr 1
    rw [hrec]
    rw [show weight i - ((k : ℤ) + 1) + 1 = weight i - k by omega]
    ring

/-- Every nonzero vector killed by a mode-zero raising current has a
nonnegative integral highest weight in that root direction. -/
theorem highest_weight_coordinate_nonnegative {d : ℕ} (V : Representation g d)
    (weight : Weight g) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace g V weight) (hne : v ≠ 0) (i : RootIndex g)
    (hhigh : V (quotientMap g (x g true i 0)) v = 0) : 0 ≤ weight i := by
  classical
  by_contra hneg
  have hneg' : weight i < 0 := by omega
  have hex := current_nilpotent_on_weightVector g V weight v hv false i 0
  have hzero := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro he
    rw [he, pow_zero, Module.End.one_apply] at hzero
    exact hne hzero
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hpos
  have hprev : (V (quotientMap g (x g false i 0)) ^ k) v ≠ 0 :=
    Nat.find_min hex (by omega)
  have he := raising_lowering_highest_string g V weight v hv i hhigh k
  rw [← hk, hzero, map_zero] at he
  have ha := quantum_qInteger_ne_zero g i ((k : ℤ) + 1) (by omega)
  have hb := quantum_qInteger_ne_zero g i (weight i - k) (by omega)
  exact smul_ne_zero (mul_ne_zero ha hb) hprev he.symm

/-- The first vanishing power of a mode-zero lowering current on a
highest vector is exactly its integral highest weight plus one. -/
theorem highest_string_first_zero {d : ℕ} (V : Representation g d)
    (weight : Weight g) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace g V weight) (hne : v ≠ 0) (i : RootIndex g)
    (hhigh : V (quotientMap g (x g true i 0)) v = 0) :
    ((V (quotientMap g (x g false i 0)) ^ (weight i).toNat) v ≠ 0) ∧
      (V (quotientMap g (x g false i 0)) ^ ((weight i).toNat + 1)) v = 0 := by
  classical
  have hex := current_nilpotent_on_weightVector g V weight v hv false i 0
  have hzero := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro he
    rw [he, pow_zero, Module.End.one_apply] at hzero
    exact hne hzero
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hpos
  have hprev : (V (quotientMap g (x g false i 0)) ^ k) v ≠ 0 :=
    Nat.find_min hex (by omega)
  have he := raising_lowering_highest_string g V weight v hv i hhigh k
  rw [← hk, hzero, map_zero] at he
  have ha := quantum_qInteger_ne_zero g i ((k : ℤ) + 1) (by omega)
  have hb : weight i - k = 0 := by
    by_contra hb
    exact smul_ne_zero (mul_ne_zero ha (quantum_qInteger_ne_zero g i _ hb)) hprev he.symm
  have hw : (weight i).toNat = k := by omega
  rw [hw]
  exact ⟨hprev, by simpa only [hk] using hzero⟩

theorem highest_weight_dominant {d : ℕ} (V : Representation g d)
    (weight : Weight g) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace g V weight) (hne : v ≠ 0)
    (hhigh : ∀ i, V (quotientMap g (x g true i 0)) v = 0) :
    ∀ i, 0 ≤ weight i :=
  fun i => highest_weight_coordinate_nonnegative g V weight v hv hne i (hhigh i)

end
end FrenkelReshetikhin.OriginalFR.Drinfeld
