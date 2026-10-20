import D4CounterexampleProof.FockEvaluation
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.Discrete

/-!
Annihilation bounds in the original presented Fock modules. The auxiliary
positive words record finite products of annihilation modes; no alternate
definition of the Fock module or its action is introduced.
-/

namespace FrenkelReshetikhin.OriginalFR.Fields

noncomputable section

local instance localFinitenessCoefficientField : _root_.Field Coefficient := inferInstance

variable (g : SimpleLieType)

abbrev PositiveMode := RootIndex g × ℕ+

def positiveWord (xs : List (PositiveMode g)) : HeisenbergAlgebra g Scalars Q T :=
  (xs.map fun x => rootMode g Scalars Q T x.1 (x.2.val : ℤ)).prod

def positiveEnergy (xs : List (PositiveMode g)) : ℕ :=
  (xs.map fun x => x.2.val).sum

@[simp] theorem positiveWord_nil : positiveWord g [] = 1 := rfl

@[simp] theorem positiveWord_cons (x : PositiveMode g) (xs : List (PositiveMode g)) :
    positiveWord g (x :: xs) = rootMode g Scalars Q T x.1 (x.2.val : ℤ) *
      positiveWord g xs := rfl

@[simp] theorem positiveWord_append (xs ys : List (PositiveMode g)) :
    positiveWord g (xs ++ ys) = positiveWord g xs * positiveWord g ys := by
  simp [positiveWord]

@[simp] theorem positiveEnergy_nil : positiveEnergy g [] = 0 := rfl

@[simp] theorem positiveEnergy_cons (x : PositiveMode g) (xs : List (PositiveMode g)) :
    positiveEnergy g (x :: xs) = x.2.val + positiveEnergy g xs := rfl

@[simp] theorem positiveEnergy_append (xs ys : List (PositiveMode g)) :
    positiveEnergy g (xs ++ ys) = positiveEnergy g xs + positiveEnergy g ys := by
  simp [positiveEnergy]

/-- The finite commutator expansion of a positive word with one mode. -/
def wordContractions (xs : List (PositiveMode g)) (j : RootIndex g) (m : ℤ) :
    HeisenbergAlgebra g Scalars Q T :=
  match xs with
  | [] => 0
  | x :: xs =>
      algebraMap Scalars _ (oscillatorCommutator g Scalars Q T x.1 j (x.2.val : ℤ) m) *
        positiveWord g xs +
      rootMode g Scalars Q T x.1 (x.2.val : ℤ) * wordContractions xs j m

theorem positiveWord_commutator (xs : List (PositiveMode g)) (j : RootIndex g) (m : ℤ) :
    positiveWord g xs * rootMode g Scalars Q T j m =
      rootMode g Scalars Q T j m * positiveWord g xs + wordContractions g xs j m := by
  induction xs with
  | nil => simp [wordContractions]
  | cons x xs ih =>
    have hroot : rootMode g Scalars Q T x.1 (x.2.val : ℤ) * rootMode g Scalars Q T j m =
        rootMode g Scalars Q T j m * rootMode g Scalars Q T x.1 (x.2.val : ℤ) +
          algebraMap Scalars _ (oscillatorCommutator g Scalars Q T x.1 j (x.2.val : ℤ) m) := by
      have h := rootMode_commutator g Scalars Q T x.1 j (x.2.val : ℤ) m
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    simp only [positiveWord_cons, wordContractions]
    calc
      _ = rootMode g Scalars Q T x.1 (x.2.val : ℤ) *
          (positiveWord g xs * rootMode g Scalars Q T j m) := mul_assoc _ _ _
      _ = _ := by
        rw [ih, mul_add, ← mul_assoc, hroot]
        noncomm_ring

theorem contraction_energy (x : PositiveMode g) (j : RootIndex g) (m : ℤ)
    (hκ : oscillatorCommutator g Scalars Q T x.1 j (x.2.val : ℤ) m ≠ 0) :
    x.2.val = m.natAbs := by
  have hs : (x.2.val : ℤ) + m = 0 := by
    by_contra h
    simp [oscillatorCommutator, h] at hκ
  have hm : m = -(x.2.val : ℤ) := by omega
  simp [hm]

def AnnihilationBound {charge : Charge g} (v : State g charge) (N : ℕ) : Prop :=
  ∀ xs : List (PositiveMode g), N < positiveEnergy g xs → positiveWord g xs • v = 0

theorem wordContractions_bound {charge : Charge g} (v : State g charge) (N : ℕ)
    (hv : AnnihilationBound g v N) (j : RootIndex g) (m : ℤ)
    (xs pre : List (PositiveMode g))
    (henergy : N + m.natAbs < positiveEnergy g pre + positiveEnergy g xs) :
    (positiveWord g pre * wordContractions g xs j m) • v = 0 := by
  induction xs generalizing pre with
  | nil => simp [wordContractions]
  | cons x xs ih =>
    simp only [wordContractions, mul_add, add_smul]
    have hfirst :
        (positiveWord g pre *
          (algebraMap Scalars _ (oscillatorCommutator g Scalars Q T x.1 j (x.2.val : ℤ) m) *
            positiveWord g xs)) • v = 0 := by
      by_cases hκ : oscillatorCommutator g Scalars Q T x.1 j (x.2.val : ℤ) m = 0
      · simp [hκ]
      · have he := contraction_energy g x j m hκ
        have hrest : N < positiveEnergy g (pre ++ xs) := by
          simp only [positiveEnergy_append]
          simp only [positiveEnergy_cons] at henergy
          omega
        rw [← mul_assoc,
          (Algebra.commutes (oscillatorCommutator g Scalars Q T x.1 j (x.2.val : ℤ) m)
            (positiveWord g pre)).symm, mul_assoc,
          ← positiveWord_append, mul_smul, hv _ hrest, smul_zero]
    rw [hfirst, zero_add]
    have hnext : N + m.natAbs < positiveEnergy g (pre ++ [x]) + positiveEnergy g xs := by
      simp only [positiveEnergy_append, positiveEnergy_cons, positiveEnergy_nil, add_zero]
      simp only [positiveEnergy_cons] at henergy
      omega
    simpa only [positiveWord_append, positiveWord_cons, positiveWord_nil, mul_one, mul_assoc]
      using ih (pre ++ [x]) hnext

theorem annihilationBound_rootMode {charge : Charge g} (v : State g charge) (N : ℕ)
    (hv : AnnihilationBound g v N) (j : RootIndex g) (m : ℤ) :
    AnnihilationBound g (rootMode g Scalars Q T j m • v) (N + m.natAbs) := by
  intro xs hx
  rw [← mul_smul, positiveWord_commutator, add_smul, mul_smul,
    hv xs (by omega), smul_zero, zero_add]
  have h := wordContractions_bound g v N hv j m xs [] (by simpa using hx)
  simpa only [positiveWord_nil, one_mul] using h

theorem positiveEnergy_pos (xs : List (PositiveMode g)) (hne : xs ≠ []) :
    0 < positiveEnergy g xs := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    simp only [positiveEnergy_cons]
    exact Nat.add_pos_left x.2.property _

theorem annihilationBound_vacuum (charge : Charge g) :
    AnnihilationBound g (vacuum g Scalars Q T (chargeEigenvalues g charge)) 0 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro hx
    by_cases hxs : xs = []
    · subst xs
      simpa only [positiveWord_cons, positiveWord_nil, mul_one] using
        positiveMode_vacuum g Scalars Q T (chargeEigenvalues g charge)
          x.1 (x.2.val : ℤ) (by exact_mod_cast x.2.property)
    · rw [positiveWord_cons, mul_smul, ih (positiveEnergy_pos g xs hxs), smul_zero]

theorem annihilationBound_mono {charge : Charge g} {v : State g charge} {N M : ℕ}
    (hv : AnnihilationBound g v N) (hNM : N ≤ M) : AnnihilationBound g v M :=
  fun xs hx => hv xs (lt_of_le_of_lt hNM hx)

theorem annihilationBound_add {charge : Charge g} {v w : State g charge} {N M : ℕ}
    (hv : AnnihilationBound g v N) (hw : AnnihilationBound g w M) :
    AnnihilationBound g (v + w) (N + M) := by
  intro xs hx
  rw [smul_add, hv xs (by omega), hw xs (by omega), add_zero]

theorem annihilationBound_scalar {charge : Charge g} {v : State g charge} {N : ℕ}
    (hv : AnnihilationBound g v N) (c : Scalars) :
    AnnihilationBound g (algebraMap Scalars (HeisenbergAlgebra g Scalars Q T) c • v) N := by
  intro xs hx
  rw [← mul_smul, (Algebra.commutes c (positiveWord g xs)).symm,
    mul_smul, hv xs hx, smul_zero]

theorem free_action_has_annihilationBound {charge : Charge g}
    (a : FreeHeisenberg g Scalars) :
    ∀ (v : State g charge) (N : ℕ), AnnihilationBound g v N →
      ∃ M : ℕ, AnnihilationBound g (heisenbergQuotient g Scalars Q T a • v) M := by
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    intro v N hv
    refine ⟨N, ?_⟩
    rw [AlgHom.commutes]
    exact annihilationBound_scalar g hv c
  | grade1 x =>
    intro v N hv
    change ∃ M, AnnihilationBound g (rootMode g Scalars Q T x.1 x.2 • v) M
    exact ⟨N + x.2.natAbs, annihilationBound_rootMode g v N hv x.1 x.2⟩
  | mul a b ha hb =>
    intro v N hv
    rw [map_mul, mul_smul]
    obtain ⟨M, hM⟩ := hb v N hv
    exact ha _ M hM
  | add a b ha hb =>
    intro v N hv
    rw [map_add, add_smul]
    obtain ⟨M₁, hM₁⟩ := ha v N hv
    obtain ⟨M₂, hM₂⟩ := hb v N hv
    exact ⟨M₁ + M₂, annihilationBound_add g hM₁ hM₂⟩

/-- Every state of the original induced Fock module has a finite
annihilation-energy bound. The proof uses its quotient presentation and
cyclic vacuum, rather than assuming a polynomial realization. -/
theorem state_has_annihilationBound (charge : Charge g) (v : State g charge) :
    ∃ N : ℕ, AnnihilationBound g v N := by
  obtain ⟨a, rfl⟩ := vacuum_cyclic g Scalars Q T (chargeEigenvalues g charge) v
  obtain ⟨b, hb⟩ := RingQuot.mkAlgHom_surjective Scalars
    (HeisenbergRelation g Scalars Q T) a
  change heisenbergQuotient g Scalars Q T b = a at hb
  rw [← hb]
  exact free_action_has_annihilationBound g b _ 0 (annihilationBound_vacuum g charge)

def absoluteMode (mode : ModeIndex g) : PositiveMode g :=
  ⟨mode.1, ⟨mode.2.val.natAbs, Int.natAbs_pos.mpr mode.2.property⟩⟩

def annihilationList (d : ModeMonomial g) : List (PositiveMode g) :=
  (d.support.toList.filter fun mode => 0 < mode.2.val).flatMap fun mode =>
    List.replicate (d mode) (absoluteMode g mode)

def positiveDegree (d : ModeMonomial g) : ℕ :=
  d.sum fun mode n => if 0 < mode.2.val then mode.2.val.natAbs * n else 0

def absoluteDegree (d : ModeMonomial g) : ℕ :=
  d.sum fun mode n => mode.2.val.natAbs * n

@[simp] theorem absoluteMode_root (mode : ModeIndex g) : (absoluteMode g mode).1 = mode.1 := rfl

@[simp] theorem absoluteMode_value (mode : ModeIndex g) :
    (absoluteMode g mode).2.val = mode.2.val.natAbs := rfl

@[simp] theorem positiveWord_replicate (n : ℕ) (x : PositiveMode g) :
    positiveWord g (List.replicate n x) = rootMode g Scalars Q T x.1 (x.2.val : ℤ) ^ n := by
  simp [positiveWord]

@[simp] theorem positiveEnergy_replicate (n : ℕ) (x : PositiveMode g) :
    positiveEnergy g (List.replicate n x) = n * x.2.val := by
  simp [positiveEnergy]

theorem annihilationList_word (d : ModeMonomial g) :
    positiveWord g (annihilationList g d) =
      ((d.support.toList.filter fun mode => 0 < mode.2.val).map fun mode =>
        rootMode g Scalars Q T mode.1 mode.2.val ^ d mode).prod := by
  classical
  have hprod (xs : List (ModeIndex g)) :
      positiveWord g (xs.flatMap fun mode => List.replicate (d mode) (absoluteMode g mode)) =
        (xs.map fun mode => rootMode g Scalars Q T mode.1 (mode.2.val.natAbs : ℤ) ^ d mode).prod := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih]
  rw [annihilationList, hprod]
  congr 1
  apply List.map_congr_left
  intro mode hm
  have hp : 0 < mode.2.val := by simpa using (List.mem_filter.mp hm).2
  rw [Int.natCast_natAbs, abs_of_pos hp]

theorem annihilationList_energy (d : ModeMonomial g) :
    positiveEnergy g (annihilationList g d) = positiveDegree g d := by
  classical
  have hsum (xs : List (ModeIndex g)) :
      positiveEnergy g (xs.flatMap fun mode => List.replicate (d mode) (absoluteMode g mode)) =
        (xs.map fun mode => mode.2.val.natAbs * d mode).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, mul_comm]
  have hfilter (xs : List (ModeIndex g)) :
      ((xs.filter fun mode => 0 < mode.2.val).map fun mode => mode.2.val.natAbs * d mode).sum =
        (xs.map fun mode => if 0 < mode.2.val then mode.2.val.natAbs * d mode else 0).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih => by_cases hp : 0 < x.2.val <;> simp [hp, ih]
  rw [annihilationList, hsum, hfilter, Finset.sum_map_toList]
  rfl

theorem absoluteDegree_identity (d : ModeMonomial g) :
    (absoluteDegree g d : ℤ) = monomialDegree g d + 2 * (positiveDegree g d : ℤ) := by
  classical
  simp only [absoluteDegree, positiveDegree, monomialDegree, Finsupp.sum,
    Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mode hm
  by_cases hp : 0 < mode.2.val
  · simp [hp, Nat.cast_mul, abs_of_pos hp]
    ring
  · have hn : mode.2.val ≤ 0 := by omega
    simp [hp, Nat.cast_mul, abs_of_nonpos hn]

theorem normalWord_zero_of_positiveDegree {charge : Charge g} (v : State g charge)
    (N : ℕ) (hv : AnnihilationBound g v N) (d : ModeMonomial g)
    (hd : N < positiveDegree g d) : normalWord g d • v = 0 := by
  have h := hv (annihilationList g d) (by rw [annihilationList_energy]; exact hd)
  rw [annihilationList_word] at h
  unfold normalWord
  rw [mul_smul, h, smul_zero]

theorem finite_modes_bounded (N : ℕ) :
    {mode : ModeIndex g | -(N : ℤ) ≤ mode.2.val ∧ mode.2.val ≤ (N : ℤ)}.Finite := by
  have hinj : Function.Injective (fun mode : ModeIndex g => (mode.1, mode.2.val)) := by
    intro x y h
    apply Prod.ext
    · exact congrArg (fun p : RootIndex g × ℤ => p.1) h
    · exact Subtype.ext (congrArg (fun p : RootIndex g × ℤ => p.2) h)
  have h := (Set.finite_univ (α := RootIndex g)).prod
    (Set.finite_Icc (-(N : ℤ)) (N : ℤ))
  convert h.preimage hinj.injOn using 1
  ext mode
  simp

theorem finite_absolute_monomials_bounded (N : ℕ) :
    {d : ModeMonomial g | absoluteDegree g d ≤ N}.Finite := by
  classical
  let S := (finite_modes_bounded g N).toFinset
  let B : ModeMonomial g := ∑ mode ∈ S, Finsupp.single mode N
  apply (Set.finite_Icc (0 : ModeMonomial g) B).subset
  intro d hd
  refine ⟨zero_le, ?_⟩
  intro mode
  by_cases hm : mode ∈ d.support
  · have hcount : 1 ≤ d mode := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hm)
    have habs : 1 ≤ mode.2.val.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr mode.2.property)
    have hterm : mode.2.val.natAbs * d mode ≤ absoluteDegree g d := by
      change mode.2.val.natAbs * d mode ≤ ∑ j ∈ d.support, j.2.val.natAbs * d j
      exact Finset.single_le_sum (f := fun j : ModeIndex g => j.2.val.natAbs * d j)
        (fun _ _ => Nat.zero_le _) hm
    have hfreq : mode.2.val.natAbs ≤ absoluteDegree g d := by
      calc
        mode.2.val.natAbs = mode.2.val.natAbs * 1 := by simp
        _ ≤ mode.2.val.natAbs * d mode := Nat.mul_le_mul_left _ hcount
        _ ≤ _ := hterm
    have hvalue : d mode ≤ absoluteDegree g d := by
      calc
        d mode = 1 * d mode := by simp
        _ ≤ mode.2.val.natAbs * d mode := Nat.mul_le_mul_right _ habs
        _ ≤ _ := hterm
    have hS : mode ∈ S := by
      have habound : |mode.2.val| ≤ (N : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hfreq.trans hd
      change mode ∈ (finite_modes_bounded g N).toFinset
      rw [Set.Finite.mem_toFinset]
      exact abs_le.mp habound
    have hB : B mode = N := by
      simp [B, Finsupp.finsetSum_apply, Finsupp.single_apply, hS]
    rw [hB]
    exact hvalue.trans hd
  · rw [Finsupp.notMem_support_iff.mp hm]
    exact Nat.zero_le _

/-- Local finiteness of the original coefficientwise action on every state
of every presented Fock module used by the field centralizer. -/
theorem evaluateSymbol_hasFiniteSupport (a : NormalSymbol g)
    (charge : Charge g) (n : ℤ) (v : State g charge) :
    (Function.support (fun d : ModeMonomial g =>
      if monomialDegree g d - a.offset = n then
        a.coefficients charge d • (normalWord g d • v) else 0)).Finite := by
  classical
  obtain ⟨N, hN⟩ := state_has_annihilationBound g charge v
  apply (finite_absolute_monomials_bounded g (n + a.offset + 2 * (N : ℤ)).toNat).subset
  intro d hd
  change (if monomialDegree g d - a.offset = n then
    a.coefficients charge d • (normalWord g d • v) else 0) ≠ 0 at hd
  have hindex : monomialDegree g d - a.offset = n := by
    by_contra h
    exact hd (if_neg h)
  have hpositive : positiveDegree g d ≤ N := by
    by_contra h
    apply hd
    rw [if_pos hindex, normalWord_zero_of_positiveDegree g v N hN d (by omega)]
    exact smul_zero (A := State g charge) (a.coefficients charge d)
  have hid := absoluteDegree_identity g d
  change absoluteDegree g d ≤ (n + a.offset + 2 * (N : ℤ)).toNat
  omega

theorem evaluateSymbol_summable (a : NormalSymbol g)
    (charge : Charge g) (n : ℤ) (v : State g charge) :
    letI : TopologicalSpace (State g charge) := ⊥
    Summable (fun d : ModeMonomial g =>
      if monomialDegree g d - a.offset = n then
        a.coefficients charge d • (normalWord g d • v) else 0) := by
  let : TopologicalSpace (State g charge) := ⊥
  exact summable_of_hasFiniteSupport (evaluateSymbol_hasFiniteSupport g a charge n v)

theorem evaluateSymbol_add_state (a : NormalSymbol g) (charge : Charge g)
    (n : ℤ) (v w : State g charge) :
    evaluateSymbol g a charge n (v + w) =
      evaluateSymbol g a charge n v + evaluateSymbol g a charge n w := by
  classical
  let : TopologicalSpace (State g charge) := ⊥
  let : DiscreteTopology (State g charge) := discreteTopology_bot _
  unfold evaluateSymbol
  rw [← Summable.tsum_add (evaluateSymbol_summable g a charge n v)
    (evaluateSymbol_summable g a charge n w)]
  apply tsum_congr
  intro d
  by_cases hd : monomialDegree g d - a.offset = n
  · rw [if_pos hd, if_pos hd, if_pos hd, smul_add]
    exact smul_add (a.coefficients charge d) (normalWord g d • v) (normalWord g d • w)
  · simp only [if_neg hd, add_zero]

theorem evaluateSymbol_smul_state (a : NormalSymbol g) (charge : Charge g)
    (n : ℤ) (c : Scalars) (v : State g charge) :
    evaluateSymbol g a charge n (c • v) = c • evaluateSymbol g a charge n v := by
  classical
  let : TopologicalSpace (State g charge) := ⊥
  let : DiscreteTopology (State g charge) := discreteTopology_bot _
  let : ContinuousConstSMul Scalars (State g charge) :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  unfold evaluateSymbol
  rw [← Summable.tsum_const_smul c (evaluateSymbol_summable g a charge n v)]
  apply tsum_congr
  intro d
  by_cases hd : monomialDegree g d - a.offset = n
  · rw [if_pos hd, if_pos hd, smul_comm (normalWord g d) c,
      smul_comm (a.coefficients charge d) c]
  · rw [if_neg hd, if_neg hd]
    exact (smul_zero (A := State g charge) c).symm

theorem screeningOperator_add (sign : ScreeningSign) (i : RootIndex g)
    (v w : State g none) :
    screeningOperator g sign i (v + w) =
      screeningOperator g sign i v + screeningOperator g sign i w := by
  cases sign <;> simp only [screeningOperator, evaluateSymbol_add_state] <;> exact map_add _ _ _

theorem screeningOperator_smul (sign : ScreeningSign) (i : RootIndex g)
    (c : Scalars) (v : State g none) :
    screeningOperator g sign i (c • v) = c • screeningOperator g sign i v := by
  cases sign <;> simp only [screeningOperator, evaluateSymbol_smul_state] <;> exact map_smul _ _ _

end
end FrenkelReshetikhin.OriginalFR.Fields
