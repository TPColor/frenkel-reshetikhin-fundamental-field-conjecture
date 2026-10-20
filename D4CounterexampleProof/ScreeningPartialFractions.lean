import D4CounterexampleProof.ScreeningDivisors
import D4CounterexampleProof.PartialFractions

/-! Partial-fraction decompositions of the actual rational screening
products, with all finite pole labels and multiplicities explicit. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance screeningPartialFractionsField : Field Coefficient := inferInstance

def divisorNumerator (f : Spectral →₀ ℤ) : Polynomial Coefficient :=
  f.prod fun a n => (Polynomial.X - Polynomial.C (q ^ a.1 * t ^ a.2)) ^ n.toNat

def divisorDenominator (f : Spectral →₀ ℤ) : Polynomial Coefficient :=
  f.prod fun a n => (Polynomial.X - Polynomial.C (q ^ a.1 * t ^ a.2)) ^ (-n).toNat

private theorem zpow_split_nat {K : Type*} [Field K] (x : K) (n : ℤ) :
    x ^ n = x ^ n.toNat / x ^ (-n).toNat := by
  cases n with
  | ofNat n => simp [Int.ofNat_eq_natCast]
  | negSucc n => simp [zpow_negSucc]

theorem divisorUnit_fraction (f : Spectral →₀ ℤ) :
    (divisorUnit f : RatFunc Coefficient) =
      algebraMap (Polynomial Coefficient) (RatFunc Coefficient) (divisorNumerator f) /
        algebraMap (Polynomial Coefficient) (RatFunc Coefficient) (divisorDenominator f) := by
  classical
  unfold divisorUnit divisorNumerator divisorDenominator Finsupp.prod
  change (Units.coeHom (RatFunc Coefficient))
      (∏ a ∈ f.support, linearFactorUnit a ^ f a) = _
  rw [map_prod, map_prod, map_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro a ha
  simp only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, linearFactorUnit, Units.val_mk0,
    map_pow, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  exact zpow_split_nat _ _

theorem divisorUnit_product_inverse (f : Spectral →₀ ℤ) :
    (divisorUnit f : RatFunc Coefficient) =
      algebraMap (Polynomial Coefficient) (RatFunc Coefficient) (divisorNumerator f) *
        ∏ a ∈ f.support, ((RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2))⁻¹ :
          RatFunc Coefficient) ^ (-f a).toNat := by
  rw [divisorUnit_fraction]
  simp only [divisorDenominator, Finsupp.prod, map_prod, map_pow, map_sub,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C, div_eq_mul_inv,
    Finset.prod_inv_distrib, inv_pow]

theorem divisorUnit_partial_fractions (f : Spectral →₀ ℤ) :
    ∃ (Q : Polynomial Coefficient) (r : (a : Spectral) → Fin (-f a).toNat → Coefficient),
      (divisorUnit f : RatFunc Coefficient) =
        algebraMap (Polynomial Coefficient) (RatFunc Coefficient) Q +
          ∑ a ∈ f.support, ∑ j : Fin (-f a).toNat, RatFunc.C (r a j) /
            (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1) := by
  obtain ⟨Q, r, hr⟩ := spectral_pole_partial_fractions (divisorNumerator f) f.support
    (fun a => (-f a).toNat)
  exact ⟨Q, r, (divisorUnit_product_inverse f).trans hr⟩

/-- Every rational screening product has finitely many principal parts.
Higher-order poles are retained, rather than assumed absent. -/
theorem screeningFactorUnit_partial_fractions (sign : ScreeningSign) (m : Monomial) (i : Fin 4) :
    let f := screeningDivisor sign (rootExponents m i)
    ∃ (Q : Polynomial Coefficient) (r : (a : Spectral) → Fin (-f a).toNat → Coefficient),
      (screeningFactorUnit sign (rootExponents m i) : RatFunc Coefficient) =
        algebraMap (Polynomial Coefficient) (RatFunc Coefficient) Q +
          ∑ a ∈ f.support, ∑ j : Fin (-f a).toNat, RatFunc.C (r a j) /
            (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1) := by
  dsimp only
  rw [screeningFactorUnit_eq_divisor]
  exact divisorUnit_partial_fractions _

end
end FrenkelReshetikhin.D4CounterexampleProof
