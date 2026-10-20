import D4CounterexampleProof.QuantumStrings

/-! Recovering highest-vector eigenlines for the original Cartan modes
from the defining current-exponential eigenvalue equations. -/

namespace FrenkelReshetikhin.OriginalFR.Drinfeld

noncomputable section

open scoped BigOperators

section Series

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

theorem coeff_pow_mem_subalgebra_below (S : Subalgebra K A) (L : PowerSeries A) (N : ℕ)
    (hL : ∀ j < N, PowerSeries.coeff j L ∈ S) (r n : ℕ) (hn : n < N) :
    PowerSeries.coeff n (L ^ r) ∈ S := by
  induction r generalizing n with
  | zero =>
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ r ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    apply S.sum_mem
    intro p hp
    have he := Finset.mem_antidiagonal.mp hp
    apply S.mul_mem
    · exact ih p.1 (by omega)
    · exact hL p.2 (by omega)

theorem coeff_high_power_mem_subalgebra (S : Subalgebra K A) (L : PowerSeries A) (N : ℕ)
    (hL0 : PowerSeries.coeff 0 L = 0)
    (hL : ∀ j < N, PowerSeries.coeff j L ∈ S) (r : ℕ) :
    PowerSeries.coeff N (L ^ (r + 2)) ∈ S := by
  rw [show r + 2 = (r + 1) + 1 by omega, pow_succ, PowerSeries.coeff_mul]
  apply S.sum_mem
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  by_cases h0 : p.2 = 0
  · rw [h0, hL0, mul_zero]
    exact S.zero_mem
  by_cases h1 : p.1 = 0
  · rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
    have hz : PowerSeries.constantCoeff L = 0 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hL0
    rw [hz, zero_pow (by omega), zero_mul]
    exact S.zero_mem
  · exact S.mul_mem (coeff_pow_mem_subalgebra_below S L N hL (r + 1) p.1 (by omega))
      (hL p.2 (by omega))

end Series

variable (g : SimpleLieType)

def highestVectorStabilizer {d : ℕ} (V : Representation g d) (v : Fin d → QuantumCoefficient) :
    Subalgebra QuantumCoefficient (QuantumAffine g) where
  carrier := {a | ∃ lam : QuantumCoefficient, V a v = lam • v}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro a b ⟨lam, hlam⟩ ⟨mu, hmu⟩
    refine ⟨lam + mu, ?_⟩
    simp only [map_add, LinearMap.add_apply, hlam, hmu, add_smul]
  mul_mem' := by
    rintro a b ⟨lam, hlam⟩ ⟨mu, hmu⟩
    refine ⟨mu * lam, ?_⟩
    simp only [map_mul, Module.End.mul_apply, hmu, map_smul, hlam, smul_smul]
  algebraMap_mem' := by
    intro lam
    refine ⟨lam, ?_⟩
    rw [AlgHom.commutes]
    rfl

theorem quotient_cartanExponentialCoefficient (p : Bool) (i : RootIndex g) (n : ℕ) :
    quotientMap g (cartanExponentialCoefficient g p i n) =
      quotientMap g (k g i (!p)) * quotientMap g (phi g p i (sign p * (n : ℤ))) := by
  have hk := RingQuot.mkAlgHom_rel QuantumCoefficient (Relation.toral_inverse i (!p))
  change quotientMap g (k g i (!p) * k g i (!(!p))) = quotientMap g 1 at hk
  simp only [Bool.not_not, map_mul, map_one] at hk
  have hphi : phi g p i (sign p * (n : ℤ)) = k g i p * cartanExponentialCoefficient g p i n := by
    cases p <;> simp [phi, sign]
  rw [hphi, map_mul, ← mul_assoc, hk, one_mul]

theorem cartan_modes_mem_of_exponential_coefficients (S : Subalgebra QuantumCoefficient (Free g))
    (p : Bool) (i : RootIndex g) (hzero : h g i 0 ∈ S)
    (hexp : ∀ n, cartanExponentialCoefficient g p i n ∈ S) (n : ℕ) :
    h g i (sign p * (n : ℤ)) ∈ S := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simpa only [hn, Nat.cast_zero, mul_zero] using hzero
    let scalar : QuantumCoefficient := (sign p : QuantumCoefficient) * (quantumQ - quantumQ⁻¹)
    have hscalar : scalar ≠ 0 := by
      apply mul_ne_zero
      · cases p <;> norm_num [sign]
      · simpa only [D₄, rootLength, pow_one] using
          quantum_root_parameter_sub_inv_ne_zero D₄ (1 : Fin 4)
    let L : PowerSeries (Free g) := PowerSeries.mk fun m =>
      if m = 0 then 0 else scalar • h g i (sign p * (m : ℤ))
    have hL0 : PowerSeries.coeff 0 L = 0 := by simp [L]
    have hL (j : ℕ) (hj : j < n) : PowerSeries.coeff j L ∈ S := by
      dsimp only [L]
      rw [PowerSeries.coeff_mk]
      split_ifs with hj0
      · exact S.zero_mem
      · exact S.smul_mem (ih j hj) scalar
    let term (r : ℕ) := (r.factorial : QuantumCoefficient)⁻¹ • PowerSeries.coeff n (L ^ r)
    have hrest : ∑ r ∈ (Finset.range (n + 1)).erase 1, term r ∈ S := by
      apply S.sum_mem
      intro r hr
      have hr1 := (Finset.mem_erase.mp hr).1
      apply S.smul_mem
      by_cases hr0 : r = 0
      · simp only [hr0, pow_zero, PowerSeries.coeff_one, if_neg hn]
        exact S.zero_mem
      · obtain ⟨k, hk⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
        rw [hk]
        exact coeff_high_power_mem_subalgebra S L n hL0 hL k
    have hsum := Finset.sum_erase_add (Finset.range (n + 1)) term
      (show 1 ∈ Finset.range (n + 1) from Finset.mem_range.mpr (by omega))
    have hterm : term 1 = scalar • h g i (sign p * (n : ℤ)) := by
      simp only [term, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
        pow_one, L, PowerSeries.coeff_mk, if_neg hn]
    have hexp' : ∑ r ∈ Finset.range (n + 1), term r ∈ S := hexp n
    rw [← hsum, hterm] at hexp'
    have hlin := S.sub_mem hexp' hrest
    rw [add_sub_cancel_left] at hlin
    have hi := S.smul_mem hlin scalar⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ hscalar, one_smul] using hi

/-- The defining highest-current eigenvalue equations imply that every
original Cartan mode preserves the highest-vector line. -/
theorem highest_cartan_modes_preserve_line {d : ℕ} (V : Representation g d)
    (v : Fin d → QuantumCoefficient)
    (eigenvalues : Bool → RootIndex g → ℕ → QuantumCoefficient)
    (hphi : ∀ p i (n : ℕ), V (quotientMap g (phi g p i (sign p * (n : ℤ)))) v =
      eigenvalues p i n • v) (i : RootIndex g) (n : ℤ) :
    ∃ scalar : QuantumCoefficient, V (quotientMap g (h g i n)) v = scalar • v := by
  let S := (highestVectorStabilizer g V v).comap (quotientMap g)
  have hzero : h g i 0 ∈ S := by
    have hz := RingQuot.mkAlgHom_rel QuantumCoefficient (Relation.zero_h i)
    change quotientMap g (h g i 0) = quotientMap g 0 at hz
    change ∃ scalar : QuantumCoefficient, V (quotientMap g (h g i 0)) v = scalar • v
    exact ⟨0, by rw [hz, map_zero, map_zero, LinearMap.zero_apply, zero_smul]⟩
  have hk (p : Bool) : quotientMap g (k g i p) ∈ highestVectorStabilizer g V v := by
    refine ⟨eigenvalues p i 0, ?_⟩
    simpa only [Nat.cast_zero, mul_zero, phi_zero] using hphi p i 0
  have hexp (p : Bool) (m : ℕ) : cartanExponentialCoefficient g p i m ∈ S := by
    change quotientMap g (cartanExponentialCoefficient g p i m) ∈ highestVectorStabilizer g V v
    rw [quotient_cartanExponentialCoefficient]
    exact (highestVectorStabilizer g V v).mul_mem (hk (!p)) ⟨eigenvalues p i m, hphi p i m⟩
  by_cases hn : 0 ≤ n
  · have hh := cartan_modes_mem_of_exponential_coefficients g S true i hzero (hexp true) n.toNat
    change ∃ scalar : QuantumCoefficient,
      V (quotientMap g (h g i (sign true * (n.toNat : ℤ)))) v = scalar • v at hh
    simpa only [sign, if_true, one_mul, Int.toNat_of_nonneg hn] using hh
  · have hh := cartan_modes_mem_of_exponential_coefficients g S false i hzero (hexp false) n.natAbs
    have he : sign false * (n.natAbs : ℤ) = n := by
      simp only [sign, Bool.false_eq_true, if_false, neg_one_mul, Int.natCast_natAbs]
      rw [abs_of_neg (by omega), neg_neg]
    rw [he] at hh
    exact hh

end
end FrenkelReshetikhin.OriginalFR.Drinfeld
