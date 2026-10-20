import D4CounterexampleProof.PolynomialOscillators
import D4CounterexampleProof.HeisenbergCoefficients

/-! A polynomial representation constructed from the original D₄
Heisenberg relations, for use in proving faithfulness of creation states. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance polynomialRealizationCoefficientField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

abbrev PositiveFrequency := {n : ℤ // 0 < n}
abbrev Variables := RootIndex D₄ × PositiveFrequency
abbrev Polynomials := MvPolynomial Variables Scalars
abbrev Operators := Module.End Scalars Polynomials

def positiveAction (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) : Operators :=
  ∑ j : RootIndex D₄, oscillatorCommutator D₄ Scalars Q T i j n (-n) •
    annihilation (j, (⟨n, hn⟩ : PositiveFrequency))

def modeAction (charge : RootIndex D₄ → Scalars) (i : RootIndex D₄) (n : ℤ) : Operators :=
  if hn : n < 0 then creation (i, (⟨-n, by omega⟩ : PositiveFrequency))
  else if hz : n = 0 then charge i • 1
  else positiveAction i n (by omega)

theorem modeAction_negative (charge : RootIndex D₄ → Scalars) (i : RootIndex D₄)
    (n : ℤ) (hn : n < 0) :
    modeAction charge i n = creation (i, (⟨-n, by omega⟩ : PositiveFrequency)) := by
  simp [modeAction, hn]

@[simp] theorem modeAction_zero (charge : RootIndex D₄ → Scalars) (i : RootIndex D₄) :
    modeAction charge i 0 = charge i • 1 := by simp [modeAction]

theorem modeAction_positive (charge : RootIndex D₄ → Scalars) (i : RootIndex D₄)
    (n : ℤ) (hn : 0 < n) : modeAction charge i n = positiveAction i n hn := by
  simp [modeAction, show ¬n < 0 by omega, ne_of_gt hn]

theorem positiveAction_creation (i j : RootIndex D₄) (n m : ℤ)
    (hn : 0 < n) (hm : m < 0) :
    positiveAction i n hn * creation (j, (⟨-m, by omega⟩ : PositiveFrequency)) -
      creation (j, (⟨-m, by omega⟩ : PositiveFrequency)) * positiveAction i n hn =
      oscillatorCommutator D₄ Scalars Q T i j n m • (1 : Operators) := by
  classical
  rw [positiveAction, weighted_annihilation_creation]
  congr 1
  by_cases hsum : n + m = 0
  · have he : m = -n := by omega
    subst m
    simp
  · have hne : (⟨n, hn⟩ : PositiveFrequency) ≠ ⟨-m, by omega⟩ := by
      intro h
      have he := congrArg Subtype.val h
      dsimp at he
      omega
    simp [hne, oscillatorCommutator, hsum]

theorem positiveActions_commute (i j : RootIndex D₄) (n m : ℤ)
    (hn : 0 < n) (hm : 0 < m) :
    Commute (positiveAction i n hn) (positiveAction j m hm) := by
  unfold positiveAction
  apply Commute.sum_left
  intro k hk
  apply Commute.sum_right
  intro l hl
  exact ((annihilation_commute (k, (⟨n, hn⟩ : PositiveFrequency))
    (l, (⟨m, hm⟩ : PositiveFrequency))).smul_left _).smul_right _

theorem scalar_operator_commute (a : Scalars) (f : Operators) : Commute (a • 1) f := by
  simp only [Commute, SemiconjBy, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem modeAction_commutator (charge : RootIndex D₄ → Scalars)
    (i j : RootIndex D₄) (n m : ℤ) :
    modeAction charge i n * modeAction charge j m -
      modeAction charge j m * modeAction charge i n =
      oscillatorCommutator D₄ Scalars Q T i j n m • (1 : Operators) := by
  by_cases hn : n < 0
  · rw [modeAction_negative charge i n hn]
    by_cases hm : m < 0
    · rw [modeAction_negative charge j m hm,
        sub_eq_zero.mpr (creation_commute _ _).eq]
      simp [oscillatorCommutator, show n + m ≠ 0 by omega]
    · by_cases hm0 : m = 0
      · subst m
        rw [modeAction_zero, sub_eq_zero.mpr (scalar_operator_commute _ _).symm.eq]
        simp [oscillatorCommutator, ne_of_lt hn]
      · have hmp : 0 < m := by omega
        rw [modeAction_positive charge j m hmp]
        rw [← neg_sub (positiveAction j m hmp * creation (i, (⟨-n, by omega⟩ : PositiveFrequency)))
          (creation (i, (⟨-n, by omega⟩ : PositiveFrequency)) * positiveAction j m hmp),
          positiveAction_creation j i m n hmp hn,
          d4_oscillator_antisymmetric i j n m]
        exact (neg_smul (oscillatorCommutator D₄ Scalars Q T j i m n) (1 : Operators)).symm
  · by_cases hn0 : n = 0
    · subst n
      rw [modeAction_zero, sub_eq_zero.mpr (scalar_operator_commute _ _).eq]
      simp [oscillatorCommutator]
    · have hnp : 0 < n := by omega
      rw [modeAction_positive charge i n hnp]
      by_cases hm : m < 0
      · rw [modeAction_negative charge j m hm]
        exact positiveAction_creation i j n m hnp hm
      · by_cases hm0 : m = 0
        · subst m
          rw [modeAction_zero, sub_eq_zero.mpr (scalar_operator_commute _ _).symm.eq]
          simp [oscillatorCommutator, hn0]
        · have hmp : 0 < m := by omega
          rw [modeAction_positive charge j m hmp,
            sub_eq_zero.mpr (positiveActions_commute i j n m hnp hmp).eq]
          simp [oscillatorCommutator, show n + m ≠ 0 by omega]

def freeRepresentation (charge : RootIndex D₄ → Scalars) :
    FreeHeisenberg D₄ Scalars →ₐ[Scalars] Operators :=
  FreeAlgebra.lift Scalars (fun key => modeAction charge key.1 key.2)

theorem freeRepresentation_rel (charge : RootIndex D₄ → Scalars)
    {a b : FreeHeisenberg D₄ Scalars}
    (h : HeisenbergRelation D₄ Scalars Q T a b) :
    freeRepresentation charge a = freeRepresentation charge b := by
  cases h with
  | commutator i j n m =>
    simpa only [freeRepresentation, freeMode, map_sub, map_mul,
      FreeAlgebra.lift_ι_apply, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      map_smul, map_one] using
      modeAction_commutator charge i j n m

/-- A representation of the original quotient, constructed by checking
every defining commutator on polynomial multiplication and derivatives. -/
def representation (charge : RootIndex D₄ → Scalars) :
    HeisenbergAlgebra D₄ Scalars Q T →ₐ[Scalars] Operators :=
  RingQuot.liftAlgHom Scalars ⟨freeRepresentation charge, fun {_ _} h => freeRepresentation_rel charge h⟩

@[simp] theorem representation_rootMode (charge : RootIndex D₄ → Scalars)
    (i : RootIndex D₄) (n : ℤ) :
    representation charge (rootMode D₄ Scalars Q T i n) = modeAction charge i n := by
  unfold representation rootMode heisenbergQuotient
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  simp [freeRepresentation, freeMode]

def vacuumEvaluation (charge : RootIndex D₄ → Scalars) :
    HeisenbergAlgebra D₄ Scalars Q T →ₗ[Scalars] Polynomials where
  toFun a := representation charge a 1
  map_add' a b := by simp only [map_add, LinearMap.add_apply]
  map_smul' c a := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

theorem positiveAction_one (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    positiveAction i n hn (1 : Polynomials) = 0 := by
  simp [positiveAction, LinearMap.sum_apply, annihilation]

theorem vacuumEvaluation_relations (charge : RootIndex D₄ → Scalars)
    (a : HeisenbergAlgebra D₄ Scalars Q T)
    (ha : a ∈ vacuumRelations D₄ Scalars Q T charge) : vacuumEvaluation charge a = 0 := by
  rcases ha with ⟨i, n, hn, rfl⟩ | ⟨i, rfl⟩
  · change representation charge (rootMode D₄ Scalars Q T i n) 1 = 0
    rw [representation_rootMode, modeAction_positive charge i n hn, positiveAction_one]
  · change representation charge (rootMode D₄ Scalars Q T i 0 -
      algebraMap Scalars (HeisenbergAlgebra D₄ Scalars Q T) (charge i)) 1 = 0
    simp only [map_sub, representation_rootMode, modeAction_zero,
      Algebra.algebraMap_eq_smul_one, LinearMap.sub_apply]
    simp only [map_smul, map_one, sub_self]

theorem vacuumEvaluation_ideal (charge : RootIndex D₄ → Scalars)
    (a : HeisenbergAlgebra D₄ Scalars Q T)
    (ha : a ∈ vacuumLeftIdeal D₄ Scalars Q T charge) : vacuumEvaluation charge a = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha => exact vacuumEvaluation_relations charge a ha
  | zero => exact map_zero _
  | add a b ha hb ia ib => rw [map_add, ia, ib, add_zero]
  | smul a b hb ib =>
    change representation charge (a * b) 1 = 0
    rw [map_mul, Module.End.mul_apply]
    change representation charge a (vacuumEvaluation charge b) = 0
    rw [ib, map_zero]

/-- A map out of the original presented Fock module, obtained from its
vacuum relations, rather than taking polynomials as its definition. -/
def vacuumMap (charge : RootIndex D₄ → Scalars) :
    FockModule D₄ Scalars Q T charge →ₗ[Scalars] Polynomials :=
  ((vacuumLeftIdeal D₄ Scalars Q T charge).restrictScalars Scalars).liftQ
    (vacuumEvaluation charge) (fun a ha => vacuumEvaluation_ideal charge a ha)

@[simp] theorem vacuumMap_vacuum (charge : RootIndex D₄ → Scalars) :
    vacuumMap charge (vacuum D₄ Scalars Q T charge) = 1 := by
  change representation charge 1 1 = 1
  simp only [map_one, Module.End.one_apply]

theorem original_vacuum_ne_zero (charge : RootIndex D₄ → Scalars) :
    vacuum D₄ Scalars Q T charge ≠ 0 := by
  intro h
  have he := congrArg (vacuumMap charge) h
  rw [vacuumMap_vacuum, map_zero] at he
  exact one_ne_zero he

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
