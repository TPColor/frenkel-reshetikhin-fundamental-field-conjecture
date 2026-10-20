import D4CounterexampleProof.NegativeDescendants
import Mathlib.Algebra.DirectSum.LinearMap

/-! Projections onto selected original weight spaces and traces in a
basis adapted to the actual type-one weight decomposition. -/

namespace FrenkelReshetikhin.OriginalFR.Drinfeld

noncomputable section

open scoped BigOperators

variable (g : SimpleLieType)

def weightDecomposition {d : ℕ} (V : Representation g d) (hV : TypeOne g V) :=
  (independent_weightSpaces g V).linearEquiv hV.2

def weightProjection {d : ℕ} (V : Representation g d) (hV : TypeOne g V)
    (p : Weight g → Prop) [DecidablePred p] : Module.End QuantumCoefficient (Fin d → QuantumCoefficient) :=
  (weightDecomposition g V hV).toLinearMap.comp
    ((DFinsupp.filterLinearMap QuantumCoefficient (fun w => weightSpace g V w) p).comp
      (weightDecomposition g V hV).symm.toLinearMap)

theorem weightProjection_on_weight {d : ℕ} (V : Representation g d) (hV : TypeOne g V)
    (p : Weight g → Prop) [DecidablePred p] (weight : Weight g)
    (v : Fin d → QuantumCoefficient) (hv : v ∈ weightSpace g V weight) :
    weightProjection g V hV p v = if p weight then v else 0 := by
  let E := weightDecomposition g V hV
  change E ((E.symm v).filter p) = _
  have he : E.symm v = DFinsupp.single weight ⟨v, hv⟩ :=
    (independent_weightSpaces g V).linearEquiv_symm_apply hV.2 hv
  rw [he, DFinsupp.filter_single]
  by_cases hp : p weight
  · rw [if_pos hp, if_pos hp, ← he, E.apply_symm_apply]
  · rw [if_neg hp, if_neg hp, map_zero]

theorem internalWeightSpaces {d : ℕ} (V : Representation g d) (hV : TypeOne g V) :
    DirectSum.IsInternal (weightSpace g V) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (independent_weightSpaces g V) hV.2

abbrev WeightBasisIndex {d : ℕ} (V : Representation g d) :=
  (weight : Weight g) × Fin (weightMultiplicity g V weight)

def weightBasis {d : ℕ} (V : Representation g d) (hV : TypeOne g V) :
    Module.Basis (WeightBasisIndex g V) QuantumCoefficient (Fin d → QuantumCoefficient) :=
  (internalWeightSpaces g V hV).collectedBasis (fun w => Module.finBasis QuantumCoefficient (weightSpace g V w))

theorem weightBasis_mem {d : ℕ} (V : Representation g d) (hV : TypeOne g V)
    (j : WeightBasisIndex g V) : weightBasis g V hV j ∈ weightSpace g V j.1 :=
  (internalWeightSpaces g V hV).collectedBasis_mem _ j

abbrev weightBasisFintype {d : ℕ} (V : Representation g d) (hV : TypeOne g V) :
    Fintype (WeightBasisIndex g V) := by
  letI : Finite (WeightBasisIndex g V) := (weightBasis g V hV).linearIndependent.finite
  exact Fintype.ofFinite (WeightBasisIndex g V)

theorem weightProjection_commutes_current {d : ℕ} (V : Representation g d) (hV : TypeOne g V)
    (p : Weight g → Prop) [DecidablePred p] (positive : Bool) (i : RootIndex g) (n : ℤ)
    (hp : ∀ weight, p (weight + sign positive • simpleRoot g i) ↔ p weight) :
    Commute (weightProjection g V hV p) (V (quotientMap g (x g positive i n))) := by
  apply (weightBasis g V hV).ext
  intro j
  rw [Module.End.mul_apply, Module.End.mul_apply,
    weightProjection_on_weight g V hV p _ _
      (current_maps_weightSpace g V j.1 _ (weightBasis_mem g V hV j) positive i n),
    weightProjection_on_weight g V hV p j.1 _ (weightBasis_mem g V hV j)]
  by_cases hj : p j.1
  · rw [if_pos ((hp j.1).mpr hj), if_pos hj]
  · rw [if_neg (by simpa only [hp j.1] using hj), if_neg hj, map_zero]

theorem trace_diagonal_on_weightBasis {d : ℕ} (V : Representation g d) (hV : TypeOne g V)
    (f : Module.End QuantumCoefficient (Fin d → QuantumCoefficient))
    (a : WeightBasisIndex g V → QuantumCoefficient)
    (hf : ∀ j, f (weightBasis g V hV j) = a j • weightBasis g V hV j) :
    letI : Fintype (WeightBasisIndex g V) := weightBasisFintype g V hV
    LinearMap.trace QuantumCoefficient (Fin d → QuantumCoefficient) f = ∑ j, a j := by
  classical
  let B := weightBasis g V hV
  let : Fintype (WeightBasisIndex g V) := weightBasisFintype g V hV
  rw [LinearMap.trace_eq_matrix_trace QuantumCoefficient B]
  change (∑ j, (LinearMap.toMatrix B B f) j j) = _
  apply Finset.sum_congr rfl
  intro j hj
  rw [LinearMap.toMatrix_apply, hf j, map_smul, Module.Basis.repr_self]
  simp

end
end FrenkelReshetikhin.OriginalFR.Drinfeld
