import StatementDefinitions
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Int.Interval

/-!
Coefficientwise evaluation on the presented FR Fock modules. These lemmas
use the vacuum relations of the original quotient construction.
-/

namespace FrenkelReshetikhin.OriginalFR.Fields

noncomputable section

local instance fockEvaluationCoefficientField : _root_.Field Coefficient := inferInstance

variable (g : SimpleLieType)

theorem positiveMode_pow_vacuum (charge : Charge g) (mode : ModeIndex g)
    (hmode : 0 < mode.2.val) (k : ℕ) (hk : 0 < k) :
    rootMode g Scalars Q T mode.1 mode.2.val ^ k •
      vacuum g Scalars Q T (chargeEigenvalues g charge) = 0 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [pow_succ, mul_smul, positiveMode_vacuum g Scalars Q T _ _ _ hmode, smul_zero]

private theorem product_vacuum_zero (charge : Charge g)
    (xs : List (HeisenbergAlgebra g Scalars Q T))
    (hxs : ∀ x ∈ xs, x • vacuum g Scalars Q T (chargeEigenvalues g charge) = 0)
    (hne : xs ≠ []) : xs.prod • vacuum g Scalars Q T (chargeEigenvalues g charge) = 0 := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    by_cases ht : xs = []
    · subst xs
      simpa using hxs x (by simp)
    · rw [List.prod_cons, mul_smul, ih (fun y hy => hxs y (by simp [hy])) ht, smul_zero]

/-- A normally ordered word containing an annihilation mode kills the vacuum. -/
theorem normalWord_vacuum_zero_of_positive (charge : Charge g)
    (d : ModeMonomial g) (hpos : ∃ mode ∈ d.support, 0 < mode.2.val) :
    normalWord g d • vacuum g Scalars Q T (chargeEigenvalues g charge) = 0 := by
  classical
  let xs := (d.support.toList.filter fun mode => 0 < mode.2.val).map fun mode =>
    rootMode g Scalars Q T mode.1 mode.2.val ^ d mode
  have hall : ∀ x ∈ xs, x • vacuum g Scalars Q T (chargeEigenvalues g charge) = 0 := by
    intro x hx
    obtain ⟨mode, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hmem, hmode⟩ := List.mem_filter.mp hm
    have hs : mode ∈ d.support := by simpa using hmem
    apply positiveMode_pow_vacuum g charge mode (by simpa using hmode)
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs)
  have hne : xs ≠ [] := by
    obtain ⟨mode, hm, hmode⟩ := hpos
    have hx : rootMode g Scalars Q T mode.1 mode.2.val ^ d mode ∈ xs := by
      apply List.mem_map.mpr
      exact ⟨mode, List.mem_filter.mpr ⟨by simpa using hm, by simpa using hmode⟩, rfl⟩
    intro h
    simp [h] at hx
  unfold normalWord
  rw [mul_smul, product_vacuum_zero g charge xs hall hne, smul_zero]

theorem monomialDegree_nonneg_of_no_positive (d : ModeMonomial g)
    (hpos : ¬∃ mode ∈ d.support, 0 < mode.2.val) :
    0 ≤ monomialDegree g d := by
  apply Finset.sum_nonneg
  intro mode hm
  have hn : mode.2.val ≤ 0 := by
    by_contra h
    exact hpos ⟨mode, hm, by omega⟩
  exact mul_nonneg (neg_nonneg.mpr hn) (Nat.cast_nonneg _)

theorem finite_negative_modes_bounded (N : ℕ) :
    {mode : ModeIndex g | -(N : ℤ) ≤ mode.2.val ∧ mode.2.val ≤ -1}.Finite := by
  have hinj : Function.Injective (fun mode : ModeIndex g => (mode.1, mode.2.val)) := by
    intro x y h
    apply Prod.ext
    · exact congrArg (fun p : RootIndex g × ℤ => p.1) h
    · exact Subtype.ext (congrArg (fun p : RootIndex g × ℤ => p.2) h)
  have h := (Set.finite_univ (α := RootIndex g)).prod
    (Set.finite_Icc (-(N : ℤ)) (-1))
  convert h.preimage hinj.injOn using 1
  ext mode
  simp

/-- At bounded creation degree there are only finitely many normally ordered
creation monomials, despite the infinitely many available mode indices. -/
theorem finite_creation_monomials_bounded (N : ℕ) :
    {d : ModeMonomial g |
      (∀ mode ∈ d.support, mode.2.val < 0) ∧ monomialDegree g d ≤ (N : ℤ)}.Finite := by
  classical
  let S := (finite_negative_modes_bounded g N).toFinset
  let B : ModeMonomial g := ∑ mode ∈ S, Finsupp.single mode N
  apply (Set.finite_Icc (0 : ModeMonomial g) B).subset
  intro d hd
  refine ⟨zero_le, ?_⟩
  intro mode
  by_cases hm : mode ∈ d.support
  · have hmode := hd.1 mode hm
    have hcount : (1 : ℤ) ≤ (d mode : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hm)
    have hterm : -mode.2.val * (d mode : ℤ) ≤ monomialDegree g d := by
      apply Finset.single_le_sum _ hm
      intro j hj
      exact mul_nonneg (by have := hd.1 j hj; omega) (Nat.cast_nonneg _)
    have hfreq : -mode.2.val ≤ monomialDegree g d := by
      calc
        -mode.2.val = -mode.2.val * 1 := by ring
        _ ≤ -mode.2.val * (d mode : ℤ) :=
          mul_le_mul_of_nonneg_left hcount (by omega)
        _ ≤ _ := hterm
    have hvalue : (d mode : ℤ) ≤ monomialDegree g d := by
      calc
        (d mode : ℤ) = 1 * (d mode : ℤ) := by ring
        _ ≤ -mode.2.val * (d mode : ℤ) :=
          mul_le_mul_of_nonneg_right (by omega) (Nat.cast_nonneg _)
        _ ≤ _ := hterm
    have hS : mode ∈ S := by
      change mode ∈ (finite_negative_modes_bounded g N).toFinset
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have hN := hd.2
      constructor <;> omega
    have hB : B mode = N := by
      simp [B, Finsupp.finsetSum_apply, Finsupp.single_apply, hS]
    rw [hB]
    exact_mod_cast hvalue.trans hd.2
  · rw [Finsupp.notMem_support_iff.mp hm]
    exact Nat.zero_le _

/-- On the vacuum, each Fourier coefficient of every normal symbol is an
actual finite sum in the original quotient Fock module. -/
theorem evaluateSymbol_vacuum_hasFiniteSupport (a : NormalSymbol g)
    (charge : Charge g) (n : ℤ) :
    (Function.support (fun d : ModeMonomial g =>
      if monomialDegree g d - a.offset = n then
        a.coefficients charge d •
          (normalWord g d • vacuum g Scalars Q T (chargeEigenvalues g charge)) else 0)).Finite := by
  classical
  apply (finite_creation_monomials_bounded g (n + a.offset).toNat).subset
  intro d hd
  change (if monomialDegree g d - a.offset = n then
    a.coefficients charge d •
      (normalWord g d • vacuum g Scalars Q T (chargeEigenvalues g charge)) else 0) ≠ 0 at hd
  have hindex : monomialDegree g d - a.offset = n := by
    by_contra h
    exact hd (if_neg h)
  have hpos : ¬∃ mode ∈ d.support, 0 < mode.2.val := by
    intro h
    apply hd
    rw [if_pos hindex, normalWord_vacuum_zero_of_positive g charge d h]
    exact smul_zero (A := State g charge) (a.coefficients charge d)
  refine ⟨?_, ?_⟩
  · intro mode hm
    have hmode := mode.2.property
    by_contra h
    exact hpos ⟨mode, hm, by omega⟩
  · have hdegree := monomialDegree_nonneg_of_no_positive g d hpos
    omega

theorem evaluateSymbol_vacuum_summable (a : NormalSymbol g)
    (charge : Charge g) (n : ℤ) :
    letI : TopologicalSpace (State g charge) := ⊥
    Summable (fun d : ModeMonomial g =>
      if monomialDegree g d - a.offset = n then
        a.coefficients charge d •
          (normalWord g d • vacuum g Scalars Q T (chargeEigenvalues g charge)) else 0) := by
  let : TopologicalSpace (State g charge) := ⊥
  exact summable_of_hasFiniteSupport (evaluateSymbol_vacuum_hasFiniteSupport g a charge n)

/-- No normally ordered symbol has negative creation degree on the vacuum. -/
theorem evaluateSymbol_vacuum_lower_truncation (a : NormalSymbol g)
    (charge : Charge g) (n : ℤ) (hn : n + a.offset < 0) :
    evaluateSymbol g a charge n (vacuum g Scalars Q T (chargeEigenvalues g charge)) = 0 := by
  classical
  let : TopologicalSpace (State g charge) := ⊥
  unfold evaluateSymbol
  calc
    _ = ∑' _ : ModeMonomial g, (0 : State g charge) := by
      apply tsum_congr
      intro d
      by_cases hp : ∃ mode ∈ d.support, 0 < mode.2.val
      · rw [normalWord_vacuum_zero_of_positive g charge d hp]
        simp
        exact fun _ => smul_zero (A := State g charge) (a.coefficients charge d)
      · have hd := monomialDegree_nonneg_of_no_positive g d hp
        have hne : monomialDegree g d - a.offset ≠ n := by omega
        rw [if_neg hne]
    _ = 0 := tsum_zero

theorem evaluateSymbol_zero_state (a : NormalSymbol g) (charge : Charge g) (n : ℤ) :
    evaluateSymbol g a charge n 0 = 0 := by
  classical
  let : TopologicalSpace (State g charge) := ⊥
  unfold evaluateSymbol
  calc
    _ = ∑' _ : ModeMonomial g, (0 : State g charge) := by
      apply tsum_congr
      intro d
      simp
      exact fun _ => smul_zero (A := State g charge) (a.coefficients charge d)
    _ = 0 := tsum_zero

theorem screeningOperator_vacuum (sign : ScreeningSign) (i : RootIndex g) :
    screeningOperator g sign i (vacuum g Scalars Q T 0) = 0 := by
  cases sign <;>
    simp only [screeningOperator] <;>
    erw [evaluateSymbol_vacuum_lower_truncation g _ none (-1) (by simp [screeningSymbol]),
      map_zero] <;> rfl

/-- Every field in FR's span sends the zero state to zero, even though the
ambient field type is an unbundled family of functions. -/
theorem heisenbergFieldSpace_zero_state (f : Field g) (hf : f ∈ heisenbergFieldSpace g)
    (charge : Charge g) (n : ℤ) : f charge n 0 = 0 := by
  unfold heisenbergFieldSpace at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨factors, rfl⟩ := hf
    exact evaluateSymbol_zero_state g _ charge n
  | zero => rfl
  | add f h hf hh ihf ihh =>
    change f charge n 0 + h charge n 0 = 0
    rw [ihf, ihh, add_zero]
  | smul a f hf ih =>
    change a • f charge n 0 = 0
    rw [ih]
    exact smul_zero (A := State g charge) a

/-- The original screening-centralizer condition implies that each vacuum
coefficient of a W-field is killed by both screenings. -/
theorem deformedW_screening_vacuum (f : Field g) (hf : f ∈ deformedW g)
    (sign : ScreeningSign) (i : RootIndex g) (n : ℤ) :
    screeningOperator g sign i (f none n (vacuum g Scalars Q T 0)) = 0 := by
  have hcomm := hf.2 sign i n (vacuum g Scalars Q T 0)
  rw [screeningOperator_vacuum] at hcomm
  rw [heisenbergFieldSpace_zero_state g f hf.1] at hcomm
  exact hcomm.symm

end
end FrenkelReshetikhin.OriginalFR.Fields
