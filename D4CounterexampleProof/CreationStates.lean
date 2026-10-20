import D4CounterexampleProof.PolynomialRealization
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! Creation polynomials embed into the original D₄ Fock quotient.
The embedding has a proved left inverse given by the polynomial
representation; no PBW assertion is made an axiom or a definition. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators IsMulCommutative

local instance creationStatesCoefficientField : _root_.Field Coefficient := inferInstance

def negativeGenerator (v : Variables) : HeisenbergAlgebra D₄ Scalars Q T :=
  rootMode D₄ Scalars Q T v.1 (-v.2.val)

theorem negativeGenerators_commute (v w : Variables) :
    Commute (negativeGenerator v) (negativeGenerator w) := by
  have h := rootMode_commutator D₄ Scalars Q T v.1 w.1 (-v.2.val) (-w.2.val)
  have hsum : -v.2.val + -w.2.val ≠ 0 := by
    have hv := v.2.property
    have hw := w.2.property
    omega
  rw [oscillatorCommutator, if_pos (Or.inr hsum), map_zero] at h
  exact sub_eq_zero.mp h

def creationAlgebra : Subalgebra Scalars (HeisenbergAlgebra D₄ Scalars Q T) :=
  Algebra.adjoin Scalars (Set.range negativeGenerator)

instance creationAlgebra_isMulCommutative : IsMulCommutative creationAlgebra :=
  Algebra.isMulCommutative_adjoin Scalars (by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    exact (negativeGenerators_commute v w).eq)

def creationPolynomial : Polynomials →ₐ[Scalars] HeisenbergAlgebra D₄ Scalars Q T :=
  creationAlgebra.val.comp (MvPolynomial.aeval (fun v : Variables =>
    (⟨negativeGenerator v, Algebra.subset_adjoin (Set.mem_range_self v)⟩ : creationAlgebra)))

@[simp] theorem creationPolynomial_X (v : Variables) :
    creationPolynomial (MvPolynomial.X v) = negativeGenerator v := by
  simp [creationPolynomial]

theorem representation_creationPolynomial (charge : RootIndex D₄ → Scalars)
    (p : Polynomials) : representation charge (creationPolynomial p) =
      Algebra.lmul Scalars Polynomials p := by
  have h : (representation charge).comp creationPolynomial = Algebra.lmul Scalars Polynomials := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, creationPolynomial_X, negativeGenerator, representation_rootMode]
    rw [modeAction_negative charge v.1 (-v.2.val) (by have hv := v.2.property; omega)]
    apply LinearMap.ext
    intro f
    change MvPolynomial.X (v.1, (⟨- -v.2.val, by have hv := v.2.property; omega⟩ : PositiveFrequency)) * f =
      MvPolynomial.X v * f
    simp only [neg_neg]
  exact DFunLike.congr_fun h p

theorem vacuumMap_smul_vacuum (charge : RootIndex D₄ → Scalars)
    (a : HeisenbergAlgebra D₄ Scalars Q T) :
    vacuumMap charge (a • vacuum D₄ Scalars Q T charge) = representation charge a 1 := by
  change vacuumEvaluation charge (a * 1) = representation charge a 1
  rw [mul_one]
  rfl

theorem vacuumMap_action (charge : RootIndex D₄ → Scalars)
    (a : HeisenbergAlgebra D₄ Scalars Q T) (v : FockModule D₄ Scalars Q T charge) :
    vacuumMap charge (a • v) = representation charge a (vacuumMap charge v) := by
  obtain ⟨b, rfl⟩ := vacuum_cyclic D₄ Scalars Q T charge v
  rw [smul_smul, vacuumMap_smul_vacuum, vacuumMap_smul_vacuum,
    map_mul, Module.End.mul_apply]

def creationState (charge : RootIndex D₄ → Scalars) :
    Polynomials →ₗ[Scalars] FockModule D₄ Scalars Q T charge where
  toFun p := creationPolynomial p • vacuum D₄ Scalars Q T charge
  map_add' p q := by rw [map_add, add_smul]
  map_smul' a p := by simp only [map_smul, RingHom.id_apply, smul_assoc]

@[simp] theorem vacuumMap_creationState (charge : RootIndex D₄ → Scalars) (p : Polynomials) :
    vacuumMap charge (creationState charge p) = p := by
  change vacuumMap charge (creationPolynomial p • vacuum D₄ Scalars Q T charge) = p
  rw [vacuumMap_smul_vacuum, representation_creationPolynomial]
  change p * 1 = p
  exact mul_one p

/-- Creation states in the original presented Fock module have no
polynomial relations: their coefficients can be recovered uniquely. -/
theorem creationState_injective (charge : RootIndex D₄ → Scalars) :
    Function.Injective (creationState charge) := by
  intro p q h
  have hh := congrArg (vacuumMap charge) h
  simpa only [vacuumMap_creationState] using hh

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
