import D4CounterexampleProof.ScreeningDegree
import D4CounterexampleProof.ResidueTransform

/-! The polynomial part of a screening partial-fraction decomposition
is constant, so it contributes zero under the residue transform. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open scoped BigOperators

variable {K ι : Type*} [Field K]

theorem intDegree_add_nonpositive {f g : RatFunc K}
    (hf : f.intDegree ≤ 0) (hg : g.intDegree ≤ 0) : (f + g).intDegree ≤ 0 := by
  by_cases hfg : f + g = 0
  · simp [hfg]
  by_cases hz : g = 0
  · simpa only [hz, add_zero] using hf
  exact (RatFunc.intDegree_add_le hz hfg).trans (max_le hf hg)

theorem intDegree_sum_nonpositive (s : Finset ι) (f : ι → RatFunc K)
    (hf : ∀ i ∈ s, (f i).intDegree ≤ 0) : (∑ i ∈ s, f i).intDegree ≤ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact intDegree_add_nonpositive (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem intDegree_principal_part_nonpositive (r c : K) (k : ℕ) :
    (RatFunc.C r / ((RatFunc.X - RatFunc.C c) ^ k : RatFunc K)).intDegree ≤ 0 := by
  by_cases hr : r = 0
  · simp [hr]
  have hden : ((RatFunc.X - RatFunc.C c) ^ k : RatFunc K) ≠ 0 :=
    pow_ne_zero _ (ratFunc_X_sub_C_ne_zero c)
  have hdeg : ((RatFunc.X - RatFunc.C c) ^ k : RatFunc K).intDegree = (k : ℤ) := by
    have he : ((RatFunc.X - RatFunc.C c) ^ k : RatFunc K) =
        algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C c) ^ k) := by simp
    rw [he, RatFunc.intDegree_polynomial, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    simp
  rw [RatFunc.intDegree_div ((map_ne_zero RatFunc.C).mpr hr) hden, RatFunc.intDegree_C, hdeg]
  omega

theorem partial_fraction_polynomial_part_constant (f : RatFunc K) (hf : f.intDegree ≤ 0)
    (Q : Polynomial K) (s : Finset ι) (c : ι → K) (order : ι → ℕ)
    (r : (i : ι) → Fin (order i) → K)
    (hdecomp : f = algebraMap (Polynomial K) (RatFunc K) Q +
      ∑ i ∈ s, ∑ j : Fin (order i), RatFunc.C (r i j) /
        (RatFunc.X - RatFunc.C (c i)) ^ (j.val + 1)) :
    Q = Polynomial.C (Q.coeff 0) := by
  classical
  let R : RatFunc K := ∑ i ∈ s, ∑ j : Fin (order i), RatFunc.C (r i j) /
    (RatFunc.X - RatFunc.C (c i)) ^ (j.val + 1)
  have hR : R.intDegree ≤ 0 := by
    apply intDegree_sum_nonpositive
    intro i hi
    apply intDegree_sum_nonpositive
    intro j hj
    exact intDegree_principal_part_nonpositive _ _ _
  have he : algebraMap (Polynomial K) (RatFunc K) Q = f - R := by
    exact eq_sub_iff_add_eq.mpr hdecomp.symm
  have hQ : (algebraMap (Polynomial K) (RatFunc K) Q).intDegree ≤ 0 := by
    rw [he, sub_eq_add_neg]
    exact intDegree_add_nonpositive hf (by simpa only [RatFunc.intDegree_neg] using hR)
  rw [RatFunc.intDegree_polynomial] at hQ
  apply Polynomial.eq_C_of_degree_le_zero
  apply Polynomial.degree_le_of_natDegree_le
  omega

theorem residueTransform_polynomial_part_zero (f : RatFunc K) (hf : f.intDegree ≤ 0)
    (Q : Polynomial K) (s : Finset ι) (c : ι → K) (order : ι → ℕ)
    (r : (i : ι) → Fin (order i) → K)
    (hdecomp : f = algebraMap (Polynomial K) (RatFunc K) Q +
      ∑ i ∈ s, ∑ j : Fin (order i), RatFunc.C (r i j) /
        (RatFunc.X - RatFunc.C (c i)) ^ (j.val + 1)) :
    residueTransform (Q : PowerSeries K) = 0 := by
  rw [partial_fraction_polynomial_part_constant f hf Q s c order r hdecomp]
  simp

open OriginalFR.Fields

local instance polynomialPartCoefficientField : Field Coefficient := inferInstance

theorem screening_polynomial_part_constant (sign : ScreeningSign) (m : Monomial) (i : Fin 4)
    (Q : Polynomial Coefficient) (s : Finset Spectral) (order : Spectral → ℕ)
    (r : (a : Spectral) → Fin (order a) → Coefficient)
    (hdecomp : (screeningFactorUnit sign (rootExponents m i) : RatFunc Coefficient) =
      algebraMap (Polynomial Coefficient) (RatFunc Coefficient) Q +
        ∑ a ∈ s, ∑ j : Fin (order a), RatFunc.C (r a j) /
          (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1)) :
    Q = Polynomial.C (Q.coeff 0) :=
  partial_fraction_polynomial_part_constant _
    (le_of_eq (screeningFactorUnit_degree_zero sign (rootExponents m i))) Q s _ order r hdecomp

end
end FrenkelReshetikhin.D4CounterexampleProof
