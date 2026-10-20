import D4CounterexampleProof.CreationStates

/-! The creation-polynomial embedding intertwines the original root modes
and spans the presented Fock quotient. This proves the polynomial model
is a realization of that quotient, without using it as a definition. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance creationPBWCoefficientField : _root_.Field Coefficient := inferInstance

@[simp] theorem creationState_one (charge : RootIndex D₄ → Scalars) :
    creationState charge (1 : Polynomials) = vacuum D₄ Scalars Q T charge := by
  change creationPolynomial 1 • vacuum D₄ Scalars Q T charge = _
  rw [map_one, one_smul]

theorem creationState_C (charge : RootIndex D₄ → Scalars) (c : Scalars) :
    creationState charge (MvPolynomial.C c) = c • vacuum D₄ Scalars Q T charge := by
  change creationPolynomial (algebraMap Scalars Polynomials c) • vacuum D₄ Scalars Q T charge = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_smul]

theorem creationState_X_mul (charge : RootIndex D₄ → Scalars) (v : Variables) (p : Polynomials) :
    creationState charge (MvPolynomial.X v * p) = negativeGenerator v • creationState charge p := by
  change creationPolynomial (MvPolynomial.X v * p) • vacuum D₄ Scalars Q T charge = _
  rw [map_mul, creationPolynomial_X, mul_smul]
  rfl

theorem modeAction_on_one (charge : RootIndex D₄ → Scalars) (i : RootIndex D₄) (n : ℤ) :
    rootMode D₄ Scalars Q T i n • vacuum D₄ Scalars Q T charge =
      creationState charge (modeAction charge i n (1 : Polynomials)) := by
  by_cases hn : n < 0
  · rw [modeAction_negative charge i n hn, creation_apply, mul_one]
    change rootMode D₄ Scalars Q T i n • vacuum D₄ Scalars Q T charge =
      creationPolynomial (MvPolynomial.X (i, (⟨-n, by omega⟩ : PositiveFrequency))) •
        vacuum D₄ Scalars Q T charge
    rw [creationPolynomial_X]
    simp only [negativeGenerator, neg_neg]
  · by_cases hn0 : n = 0
    · subst n
      rw [zeroMode_vacuum, IsScalarTower.algebraMap_smul, modeAction_zero,
        LinearMap.smul_apply, Module.End.one_apply, map_smul, creationState_one]
    · have hnp : 0 < n := by omega
      rw [positiveMode_vacuum D₄ Scalars Q T charge i n hnp,
        modeAction_positive charge i n hnp, positiveAction_one, map_zero]

theorem modeAction_creation (charge : RootIndex D₄ → Scalars)
    (i : RootIndex D₄) (n : ℤ) (v : Variables) (p : Polynomials) :
    modeAction charge i n (MvPolynomial.X v * p) =
      MvPolynomial.X v * modeAction charge i n p +
        oscillatorCommutator D₄ Scalars Q T i v.1 n (-v.2.val) • p := by
  have h := modeAction_commutator charge i v.1 n (-v.2.val)
  rw [modeAction_negative charge v.1 (-v.2.val) (by have hv := v.2.property; omega)] at h
  have hkey : (v.1, (⟨- -v.2.val, by have hv := v.2.property; omega⟩ : PositiveFrequency)) = v := by
    simp only [neg_neg]
  rw [hkey] at h
  have he := congrArg (fun f : Operators => f p) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, creation_apply,
    LinearMap.smul_apply, Module.End.one_apply] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem rootMode_creation_action (charge : RootIndex D₄ → Scalars)
    (i : RootIndex D₄) (n : ℤ) (v : Variables) (w : FockModule D₄ Scalars Q T charge) :
    rootMode D₄ Scalars Q T i n • (negativeGenerator v • w) =
      negativeGenerator v • (rootMode D₄ Scalars Q T i n • w) +
        oscillatorCommutator D₄ Scalars Q T i v.1 n (-v.2.val) • w := by
  have h := rootMode_commutator D₄ Scalars Q T i v.1 n (-v.2.val)
  have he := congrArg (fun a : HeisenbergAlgebra D₄ Scalars Q T => a • w) h
  simp only [sub_smul, mul_smul, IsScalarTower.algebraMap_smul] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem creationState_intertwines (charge : RootIndex D₄ → Scalars)
    (i : RootIndex D₄) (n : ℤ) (p : Polynomials) :
    rootMode D₄ Scalars Q T i n • creationState charge p =
      creationState charge (modeAction charge i n p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hC : (MvPolynomial.C c : Polynomials) = c • 1 := by simp [Algebra.smul_def]
    simp only [hC, map_smul, creationState_one]
    rw [smul_comm _ c, modeAction_on_one]
  | add p q hp hq => simp only [map_add, smul_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm p (MvPolynomial.X v), creationState_X_mul, rootMode_creation_action,
      hp, modeAction_creation, map_add, creationState_X_mul, map_smul]

theorem free_action_creationState (charge : RootIndex D₄ → Scalars)
    (a : FreeHeisenberg D₄ Scalars) : ∀ p : Polynomials,
    heisenbergQuotient D₄ Scalars Q T a • creationState charge p =
      creationState charge (representation charge (heisenbergQuotient D₄ Scalars Q T a) p) := by
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    intro p
    rw [AlgHom.commutes, IsScalarTower.algebraMap_smul, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, map_smul]
  | grade1 v =>
    intro p
    change rootMode D₄ Scalars Q T v.1 v.2 • creationState charge p =
      creationState charge (representation charge (rootMode D₄ Scalars Q T v.1 v.2) p)
    rw [representation_rootMode]
    exact creationState_intertwines charge v.1 v.2 p
  | mul a b ha hb =>
    intro p
    rw [map_mul, mul_smul, hb, ha, map_mul, Module.End.mul_apply]
  | add a b ha hb =>
    intro p
    rw [map_add, add_smul, ha, hb, map_add, LinearMap.add_apply, map_add]

/-- Every state in the original cyclic quotient is the creation state of
the polynomial recovered by the representation. This proves spanning. -/
@[simp] theorem creationState_vacuumMap (charge : RootIndex D₄ → Scalars)
    (v : FockModule D₄ Scalars Q T charge) : creationState charge (vacuumMap charge v) = v := by
  obtain ⟨a, rfl⟩ := vacuum_cyclic D₄ Scalars Q T charge v
  obtain ⟨b, hb⟩ := RingQuot.mkAlgHom_surjective Scalars (HeisenbergRelation D₄ Scalars Q T) a
  change heisenbergQuotient D₄ Scalars Q T b = a at hb
  rw [← hb, vacuumMap_smul_vacuum]
  have h := free_action_creationState charge b (1 : Polynomials)
  rw [creationState_one] at h
  exact h.symm

/-- The polynomial realization is proved equivalent to the original
presented Fock module, with the original negative modes as its variables. -/
def creationEquiv (charge : RootIndex D₄ → Scalars) :
    Polynomials ≃ₗ[Scalars] FockModule D₄ Scalars Q T charge :=
  { creationState charge with
    invFun := vacuumMap charge
    left_inv := vacuumMap_creationState charge
    right_inv := creationState_vacuumMap charge }

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
