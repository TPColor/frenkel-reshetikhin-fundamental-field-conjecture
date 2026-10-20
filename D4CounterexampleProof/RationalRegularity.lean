import D4CounterexampleProof.ScreeningDivisors

/-! Rational functions regular and nonzero at a finite point. The
fraction witnesses below are used only in proofs; pole orders are not
defined by totalized evaluation. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open scoped BigOperators

section General

variable {K ι : Type*} [Field K]

def RegularAt (c : K) (f : RatFunc K) : Prop :=
  ∃ P Q : Polynomial K, Q.eval c ≠ 0 ∧
    f = algebraMap (Polynomial K) (RatFunc K) P / algebraMap (Polynomial K) (RatFunc K) Q

theorem RegularAt.denom_ne_zero {c : K} {f : RatFunc K} (h : RegularAt c f) :
    f.denom.eval c ≠ 0 := by
  obtain ⟨P, Q, hQ, rfl⟩ := h
  intro hz
  obtain ⟨U, hU⟩ := RatFunc.denom_div_dvd P Q
  apply hQ
  rw [hU, Polynomial.eval_mul, hz, zero_mul]

theorem regularAt_polynomial (c : K) (P : Polynomial K) :
    RegularAt c (algebraMap (Polynomial K) (RatFunc K) P) :=
  ⟨P, 1, by simp, by simp⟩

theorem regularAt_zero (c : K) : RegularAt c (0 : RatFunc K) := by
  simpa using regularAt_polynomial c 0

theorem RegularAt.mul {c : K} {f g : RatFunc K}
    (hf : RegularAt c f) (hg : RegularAt c g) : RegularAt c (f * g) := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  obtain ⟨U, V, hV, rfl⟩ := hg
  exact ⟨P * U, Q * V, by simpa using mul_ne_zero hQ hV,
    by rw [map_mul, map_mul, div_mul_div_comm]⟩

theorem RegularAt.add {c : K} {f g : RatFunc K}
    (hf : RegularAt c f) (hg : RegularAt c g) : RegularAt c (f + g) := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  obtain ⟨U, V, hV, rfl⟩ := hg
  have hq : Q ≠ 0 := by intro hz; simp [hz] at hQ
  have hv : V ≠ 0 := by intro hz; simp [hz] at hV
  refine ⟨P * V + U * Q, Q * V, by simpa using mul_ne_zero hQ hV, ?_⟩
  rw [map_add, map_mul, map_mul, map_mul]
  simpa only [mul_comm] using div_add_div
    (algebraMap (Polynomial K) (RatFunc K) P) (algebraMap (Polynomial K) (RatFunc K) U)
    (RatFunc.algebraMap_ne_zero hq) (RatFunc.algebraMap_ne_zero hv)

theorem regularAt_sum (c : K) (s : Finset ι) (f : ι → RatFunc K)
    (hf : ∀ i ∈ s, RegularAt c (f i)) : RegularAt c (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using regularAt_zero c
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

def RegularNonzeroAt (c : K) (f : RatFunc K) : Prop :=
  ∃ P Q : Polynomial K, P.eval c ≠ 0 ∧ Q.eval c ≠ 0 ∧
    f = algebraMap (Polynomial K) (RatFunc K) P / algebraMap (Polynomial K) (RatFunc K) Q

theorem RegularNonzeroAt.regularAt {c : K} {f : RatFunc K} (h : RegularNonzeroAt c f) :
    RegularAt c f := by
  obtain ⟨P, Q, _, hQ, h⟩ := h
  exact ⟨P, Q, hQ, h⟩

theorem RegularNonzeroAt.eval_ne_zero {c : K} {f : RatFunc K} (h : RegularNonzeroAt c f) :
    RatFunc.eval (RingHom.id K) c f ≠ 0 := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := h
  rw [eval_polynomial_fraction P Q c hQ]
  exact div_ne_zero hP hQ

theorem RegularNonzeroAt.denom_ne_zero {c : K} {f : RatFunc K} (h : RegularNonzeroAt c f) :
    f.denom.eval c ≠ 0 := by
  simpa only [Polynomial.eval₂_id] using RatFunc.eval₂_denom_ne_zero h.eval_ne_zero

theorem regularNonzeroAt_one (c : K) : RegularNonzeroAt c 1 := by
  exact ⟨1, 1, by simp, by simp, by simp⟩

theorem RegularNonzeroAt.mul {c : K} {f g : RatFunc K}
    (hf : RegularNonzeroAt c f) (hg : RegularNonzeroAt c g) : RegularNonzeroAt c (f * g) := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hf
  obtain ⟨U, V, hU, hV, rfl⟩ := hg
  exact ⟨P * U, Q * V, by simpa using mul_ne_zero hP hU,
    by simpa using mul_ne_zero hQ hV, by rw [map_mul, map_mul, div_mul_div_comm]⟩

theorem RegularNonzeroAt.inv {c : K} {f : RatFunc K}
    (hf : RegularNonzeroAt c f) : RegularNonzeroAt c f⁻¹ := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hf
  exact ⟨Q, P, hQ, hP, inv_div _ _⟩

theorem RegularNonzeroAt.pow {c : K} {f : RatFunc K}
    (hf : RegularNonzeroAt c f) (n : ℕ) : RegularNonzeroAt c (f ^ n) := by
  induction n with
  | zero => simpa using regularNonzeroAt_one c
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem RegularNonzeroAt.zpow {c : K} {f : RatFunc K}
    (hf : RegularNonzeroAt c f) (n : ℤ) : RegularNonzeroAt c (f ^ n) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hf.pow (n + 1)).inv

theorem regularNonzeroAt_X_sub_C (c a : K) (hca : c ≠ a) :
    RegularNonzeroAt c ((RatFunc.X : RatFunc K) - RatFunc.C a) := by
  refine ⟨Polynomial.X - Polynomial.C a, 1, ?_, by simp, ?_⟩
  · simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using sub_ne_zero.mpr hca
  · simp only [map_one, div_one, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem regularNonzeroAt_prod (c : K) (s : Finset ι) (f : ι → RatFunc K)
    (hf : ∀ i ∈ s, RegularNonzeroAt c (f i)) : RegularNonzeroAt c (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using regularNonzeroAt_one c
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end General

local instance rationalRegularityCoefficientField : Field Coefficient := inferInstance

/-- Removing the candidate pole leaves a rational unit at that point.
Distinct spectral labels really are distinct values at generic q,t. -/
theorem divisorUnit_erase_regular (f : Spectral →₀ ℤ) (c : Spectral) :
    RegularNonzeroAt (q ^ c.1 * t ^ c.2) (divisorUnit (f.erase c) : RatFunc Coefficient) := by
  classical
  unfold divisorUnit Finsupp.prod
  change RegularNonzeroAt (q ^ c.1 * t ^ c.2)
    ((Units.coeHom (RatFunc Coefficient))
      (∏ a ∈ (f.erase c).support, linearFactorUnit a ^ (f.erase c) a))
  rw [map_prod]
  apply regularNonzeroAt_prod
  intro a ha
  have hac : a ≠ c := by
    intro h
    subst a
    exact (Finsupp.mem_support_iff.mp ha) Finsupp.erase_same
  simpa only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, linearFactorUnit, Units.val_mk0] using
    (regularNonzeroAt_X_sub_C (q ^ c.1 * t ^ c.2) (q ^ a.1 * t ^ a.2)
      (fun he => hac (spectralParameter_injective he).symm)).zpow ((f.erase c) a)

end
end FrenkelReshetikhin.D4CounterexampleProof
