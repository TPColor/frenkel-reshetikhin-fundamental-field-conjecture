import D4CounterexampleProof.RationalResidues
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision

/-! Partial fractions at distinct spectral parameters, including
arbitrary pole orders. This is a rational-function theorem; identifying
it with the original screening action remains a separate argument. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open scoped BigOperators

section General

variable {K ι : Type*} [Field K]

theorem linear_pole_partial_fractions (P : Polynomial K) (s : Finset ι)
    (c : ι → K) (hc : Set.InjOn c s) (order : ι → ℕ) :
    ∃ (Q : Polynomial K) (r : (i : ι) → Fin (order i) → K),
      algebraMap (Polynomial K) (RatFunc K) P *
          ∏ i ∈ s, ((RatFunc.X - RatFunc.C (c i))⁻¹ : RatFunc K) ^ order i =
        algebraMap (Polynomial K) (RatFunc K) Q +
          ∑ i ∈ s, ∑ j : Fin (order i), RatFunc.C (r i j) /
            (RatFunc.X - RatFunc.C (c i)) ^ (j.val + 1) := by
  classical
  have hpair : Set.Pairwise s (fun i j =>
      IsCoprime (Polynomial.X - Polynomial.C (c i)) (Polynomial.X - Polynomial.C (c j))) := by
    intro i hi j hj hij
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    exact (sub_ne_zero.mpr (fun he => hij (hc hi hj he))).isUnit
  obtain ⟨Q, r, hr, he⟩ := Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (K := RatFunc K) P (g := fun i => Polynomial.X - Polynomial.C (c i))
    (fun i _ => Polynomial.monic_X_sub_C (c i)) hpair order
    (gi := fun i => (RatFunc.X - RatFunc.C (c i))⁻¹)
    (fun i _ => by
      simp only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
      exact inv_mul_cancel₀ (ratFunc_X_sub_C_ne_zero (c i)))
  refine ⟨Q, fun i j => (r i j).coeff 0, he.trans ?_⟩
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hdeg : (r i j).degree ≤ 0 := by
    have h := hr i hi j
    rw [Polynomial.degree_X_sub_C] at h
    by_cases hz : r i j = 0
    · simp only [hz, Polynomial.degree_zero, bot_le]
    · rw [Polynomial.degree_eq_natDegree hz] at h ⊢
      exact WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ (WithBot.coe_lt_coe.mp h))
  rw [Polynomial.eq_C_of_degree_le_zero hdeg, RatFunc.algebraMap_C, inv_pow, div_eq_mul_inv]

end General

local instance partialFractionsCoefficientField : Field Coefficient := inferInstance

/-- All pole labels in the original ansatz are distinct as elements of
the original independent-q,t field, as required by partial fractions. -/
theorem spectral_pole_partial_fractions (P : Polynomial Coefficient) (s : Finset Spectral)
    (order : Spectral → ℕ) :
    ∃ (Q : Polynomial Coefficient) (r : (a : Spectral) → Fin (order a) → Coefficient),
      algebraMap (Polynomial Coefficient) (RatFunc Coefficient) P *
          ∏ a ∈ s, ((RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2))⁻¹ : RatFunc Coefficient) ^ order a =
        algebraMap (Polynomial Coefficient) (RatFunc Coefficient) Q +
          ∑ a ∈ s, ∑ j : Fin (order a), RatFunc.C (r a j) /
            (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1) :=
  linear_pole_partial_fractions P s _ (spectralParameter_injective.injOn) order

end
end FrenkelReshetikhin.D4CounterexampleProof
