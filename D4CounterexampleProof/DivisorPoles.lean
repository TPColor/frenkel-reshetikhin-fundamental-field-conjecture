import D4CounterexampleProof.RationalRegularity

/-! Genuine poles and nonzero leading coefficients of the rational
screening products. The canonical RatFunc denominator is used. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields

local instance divisorPolesField : Field Coefficient := inferInstance

theorem divisorUnit_split (f : Spectral →₀ ℤ) (c : Spectral) :
    divisorUnit f = linearFactorUnit c ^ f c * divisorUnit (f.erase c) := by
  exact (Finsupp.mul_prod_erase' f c (fun a n => linearFactorUnit a ^ n)
    (fun _ => zpow_zero _)).symm

/-- Removing exactly the negative divisor power leaves the product of
all other factors, regular and nonzero at this spectral parameter. -/
theorem divisorUnit_remove_pole (f : Spectral →₀ ℤ) (c : Spectral) (k : ℕ)
    (hk : f c = -(k : ℤ)) :
    ((RatFunc.X - RatFunc.C (q ^ c.1 * t ^ c.2)) ^ k : RatFunc Coefficient) *
        (divisorUnit f : RatFunc Coefficient) = (divisorUnit (f.erase c) : RatFunc Coefficient) := by
  have hu : linearFactorUnit c ^ k * divisorUnit f = divisorUnit (f.erase c) := by
    rw [divisorUnit_split f c, hk, zpow_neg, zpow_natCast, ← mul_assoc, mul_inv_cancel, one_mul]
  have he := congrArg (fun u : (RatFunc Coefficient)ˣ => (u : RatFunc Coefficient)) hu
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, linearFactorUnit, Units.val_mk0] using he

theorem divisorUnit_leading_coefficient_ne_zero (f : Spectral →₀ ℤ) (c : Spectral) (k : ℕ)
    (hk : f c = -(k : ℤ)) :
    RatFunc.eval (RingHom.id Coefficient) (q ^ c.1 * t ^ c.2)
      (((RatFunc.X - RatFunc.C (q ^ c.1 * t ^ c.2)) ^ k : RatFunc Coefficient) *
        (divisorUnit f : RatFunc Coefficient)) ≠ 0 := by
  rw [divisorUnit_remove_pole f c k hk]
  exact (divisorUnit_erase_regular f c).eval_ne_zero

theorem divisorUnit_denominator_vanishes (f : Spectral →₀ ℤ) (c : Spectral) (k : ℕ)
    (hkpos : 0 < k) (hk : f c = -(k : ℤ)) :
    (divisorUnit f : RatFunc Coefficient).denom.eval (q ^ c.1 * t ^ c.2) = 0 := by
  by_contra hden
  let P : Polynomial Coefficient := (Polynomial.X - Polynomial.C (q ^ c.1 * t ^ c.2)) ^ k
  have hP : (algebraMap (Polynomial Coefficient) (RatFunc Coefficient) P) =
      (RatFunc.X - RatFunc.C (q ^ c.1 * t ^ c.2)) ^ k := by
    simp only [P, map_pow, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hPd : Polynomial.eval₂ (RingHom.id Coefficient) (q ^ c.1 * t ^ c.2)
      (algebraMap (Polynomial Coefficient) (RatFunc Coefficient) P).denom ≠ 0 := by
    rw [RatFunc.denom_algebraMap]
    simp
  have hPe : RatFunc.eval (RingHom.id Coefficient) (q ^ c.1 * t ^ c.2)
      (algebraMap (Polynomial Coefficient) (RatFunc Coefficient) P) = 0 := by
    rw [RatFunc.eval_algebraMap]
    simp [P, Nat.ne_of_gt hkpos]
  have he := RatFunc.eval_mul (RingHom.id Coefficient) (q ^ c.1 * t ^ c.2) hPd
    (by simpa only [Polynomial.eval₂_id] using hden)
  have hn := divisorUnit_leading_coefficient_ne_zero f c k hk
  rw [← hP, he, hPe, zero_mul] at hn
  exact hn rfl

/-- In particular every combinatorially simple screening pole has a
nonzero actual rational residue. Its contribution to the original
screening action is identified in `ScreeningResidueBridge.lean`. -/
theorem minus_simple_pole_residue (m : Monomial) (i : Fin 4) (c : Spectral)
    (h : minusPoleOrder m i c = 1) :
    RatFunc.eval (RingHom.id Coefficient) (q ^ c.1 * t ^ c.2)
      ((RatFunc.X - RatFunc.C (q ^ c.1 * t ^ c.2)) *
        (screeningFactorUnit .minus (rootExponents m i) : RatFunc Coefficient)) ≠ 0 := by
  rw [screeningFactorUnit_eq_divisor]
  have hk : screeningDivisor .minus (rootExponents m i) c = -(1 : ℤ) := by
    rw [screeningDivisor_minus, h]
  simpa only [pow_one] using divisorUnit_leading_coefficient_ne_zero _ c 1 hk

theorem plus_simple_pole_residue (m : Monomial) (i : Fin 4) (c : Spectral)
    (h : plusPoleOrder m i c = 1) :
    RatFunc.eval (RingHom.id Coefficient) (q ^ c.1 * t ^ c.2)
      ((RatFunc.X - RatFunc.C (q ^ c.1 * t ^ c.2)) *
        (screeningFactorUnit .plus (rootExponents m i) : RatFunc Coefficient)) ≠ 0 := by
  rw [screeningFactorUnit_eq_divisor]
  have hk : screeningDivisor .plus (rootExponents m i) c = -(1 : ℤ) := by
    rw [screeningDivisor_plus, h]
  simpa only [pow_one] using divisorUnit_leading_coefficient_ne_zero _ c 1 hk

end
end FrenkelReshetikhin.D4CounterexampleProof
