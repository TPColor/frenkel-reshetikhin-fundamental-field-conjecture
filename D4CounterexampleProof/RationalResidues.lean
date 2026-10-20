import D4CounterexampleProof.LaurentEvaluation

/-! Actual nonzero residues of the two rational screening factors used
at the final monomial. Identification with the operator commutator is
separate; the rational functions here are exactly those in Proof.tex. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

section General

variable {K : Type*} [Field K]

theorem eval_polynomial_fraction (P Q : Polynomial K) (c : K) (hQ : Q.eval c ≠ 0) :
    RatFunc.eval (RingHom.id K) c
      (algebraMap (Polynomial K) (RatFunc K) P / algebraMap (Polynomial K) (RatFunc K) Q) =
      P.eval c / Q.eval c := by
  let f : RatFunc K := algebraMap (Polynomial K) (RatFunc K) P /
    algebraMap (Polynomial K) (RatFunc K) Q
  have hq : Q ≠ 0 := by intro h; simp [h] at hQ
  have hd : f.denom.eval c ≠ 0 := by
    intro hz
    obtain ⟨r, hr⟩ := RatFunc.denom_div_dvd P Q
    apply hQ
    rw [hr, Polynomial.eval_mul, hz, zero_mul]
  have hm := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr (rfl :
    f = algebraMap (Polynomial K) (RatFunc K) P / algebraMap (Polynomial K) (RatFunc K) Q)
  have he := congrArg (Polynomial.eval c) hm
  simp only [Polynomial.eval_mul] at he
  change RatFunc.eval (RingHom.id K) c f = _
  rw [RatFunc.eval]
  simp only [Polynomial.eval₂_id]
  exact (div_eq_div_iff hd hQ).mpr he

theorem ratFunc_X_sub_C_ne_zero (c : K) : (RatFunc.X : RatFunc K) - RatFunc.C c ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero c)

/-- Multiplication by u-c removes exactly the displayed simple pole;
the remaining rational function has the explicit nonzero value at c. -/
theorem two_factor_simple_residue (a b c d : K) (hca : c ≠ a) (hcb : c ≠ b) (hcd : c ≠ d) :
    RatFunc.eval (RingHom.id K) c
      (((RatFunc.X : RatFunc K) - RatFunc.C c) *
        ((RatFunc.X - RatFunc.C a) / (RatFunc.X - RatFunc.C c) *
          ((RatFunc.X - RatFunc.C b) / (RatFunc.X - RatFunc.C d)))) =
      (c - a) * (c - b) / (c - d) ∧
    (c - a) * (c - b) / (c - d) ≠ 0 := by
  constructor
  · have hid :
        ((RatFunc.X : RatFunc K) - RatFunc.C c) *
          ((RatFunc.X - RatFunc.C a) / (RatFunc.X - RatFunc.C c) *
            ((RatFunc.X - RatFunc.C b) / (RatFunc.X - RatFunc.C d))) =
        algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C a) *
          (Polynomial.X - Polynomial.C b)) /
          algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C d) := by
      simp only [map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
      field_simp [ratFunc_X_sub_C_ne_zero c, ratFunc_X_sub_C_ne_zero d]
    rw [hid, eval_polynomial_fraction _ _ c (by simpa using sub_ne_zero.mpr hcd)]
    simp
  · exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hca) (sub_ne_zero.mpr hcb)) (sub_ne_zero.mpr hcd)

/-- The pole is present in the reduced rational function: its canonical
denominator actually vanishes at c, rather than just a chosen presentation. -/
theorem two_factor_denominator_vanishes (a b c d : K)
    (hca : c ≠ a) (hcb : c ≠ b) (hcd : c ≠ d) :
    (((RatFunc.X : RatFunc K) - RatFunc.C a) / (RatFunc.X - RatFunc.C c) *
      ((RatFunc.X - RatFunc.C b) / (RatFunc.X - RatFunc.C d))).denom.eval c = 0 := by
  by_contra hden
  have hl : (RatFunc.X : RatFunc K) - RatFunc.C c =
      algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C c) := by
    simp
  have hld : Polynomial.eval₂ (RingHom.id K) c
      (((RatFunc.X : RatFunc K) - RatFunc.C c).denom) ≠ 0 := by
    rw [hl, RatFunc.denom_algebraMap]
    simp
  have hlc : RatFunc.eval (RingHom.id K) c
      ((RatFunc.X : RatFunc K) - RatFunc.C c) = 0 := by
    rw [hl, RatFunc.eval_algebraMap]
    simp
  have he := RatFunc.eval_mul (RingHom.id K) c hld
    (by simpa only [Polynomial.eval₂_id] using hden)
  obtain ⟨hres, hn⟩ := two_factor_simple_residue a b c d hca hcb hcd
  apply hn
  rw [← hres, he, hlc, zero_mul]

end General

local instance rationalResiduesCoefficientField : Field Coefficient := inferInstance

theorem spectralParameter_sub_ne_zero (a b : Spectral) (h : a ≠ b) :
    q ^ a.1 * t ^ a.2 - q ^ b.1 * t ^ b.2 ≠ 0 :=
  sub_ne_zero.mpr (fun he => h (spectralParameter_injective he))

theorem final_minus_rational_residue_ne_zero :
    RatFunc.eval (RingHom.id Coefficient) (q ^ (-2 : ℤ) * t)
      (((RatFunc.X : RatFunc Coefficient) - RatFunc.C (q ^ (-2 : ℤ) * t)) *
        ((RatFunc.X - RatFunc.C t) / (RatFunc.X - RatFunc.C (q ^ (-2 : ℤ) * t)) *
          ((RatFunc.X - RatFunc.C (q ^ (-2 : ℤ) * t ^ (3 : ℤ))) /
            (RatFunc.X - RatFunc.C (q ^ (-4 : ℤ) * t ^ (3 : ℤ)))))) ≠ 0 := by
  have hca := sub_ne_zero.mp (spectralParameter_sub_ne_zero (-2, 1) (0, 1) (by decide))
  have hcb := sub_ne_zero.mp (spectralParameter_sub_ne_zero (-2, 1) (-2, 3) (by decide))
  have hcd := sub_ne_zero.mp (spectralParameter_sub_ne_zero (-2, 1) (-4, 3) (by decide))
  simp only [zpow_one, zpow_zero, one_mul] at hca hcb hcd
  obtain ⟨he, hn⟩ := two_factor_simple_residue t (q ^ (-2 : ℤ) * t ^ (3 : ℤ))
    (q ^ (-2 : ℤ) * t) (q ^ (-4 : ℤ) * t ^ (3 : ℤ)) hca hcb hcd
  rw [he]
  exact hn

theorem final_plus_rational_residue_ne_zero :
    RatFunc.eval (RingHom.id Coefficient) (q ^ (-1 : ℤ) * t ^ (2 : ℤ))
      (((RatFunc.X : RatFunc Coefficient) - RatFunc.C (q ^ (-1 : ℤ) * t ^ (2 : ℤ))) *
        ((RatFunc.X - RatFunc.C (q ^ (-1 : ℤ))) /
          (RatFunc.X - RatFunc.C (q ^ (-1 : ℤ) * t ^ (2 : ℤ))) *
          ((RatFunc.X - RatFunc.C (q ^ (-3 : ℤ) * t ^ (2 : ℤ))) /
            (RatFunc.X - RatFunc.C (q ^ (-3 : ℤ) * t ^ (4 : ℤ)))))) ≠ 0 := by
  have hca := sub_ne_zero.mp (spectralParameter_sub_ne_zero (-1, 2) (-1, 0) (by decide))
  have hcb := sub_ne_zero.mp (spectralParameter_sub_ne_zero (-1, 2) (-3, 2) (by decide))
  have hcd := sub_ne_zero.mp (spectralParameter_sub_ne_zero (-1, 2) (-3, 4) (by decide))
  simp only [zpow_zero, mul_one] at hca hcb hcd
  obtain ⟨he, hn⟩ := two_factor_simple_residue (q ^ (-1 : ℤ)) (q ^ (-3 : ℤ) * t ^ (2 : ℤ))
    (q ^ (-1 : ℤ) * t ^ (2 : ℤ)) (q ^ (-3 : ℤ) * t ^ (4 : ℤ)) hca hcb hcd
  rw [he]
  exact hn

end
end FrenkelReshetikhin.D4CounterexampleProof
