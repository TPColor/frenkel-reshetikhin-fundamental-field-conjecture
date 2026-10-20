import D4CounterexampleProof.CreationExponents

/-! The Laurent Y monomial determines the multiset of inverse-root
factors in the original elementary ansatz. Consequently identical
monomial labels have identical original symbols, including prefactors. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance elementaryLabelsField : Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def factorLabels (factors : List (InverseRootFactor D₄)) : Monomial :=
  (factors.map fun f => Y f.root f.qShift f.tShift).sum

set_option backward.isDefEq.respectTransparency false in
theorem spectralMoment_factorLabels (factors : List (InverseRootFactor D₄)) (j : Fin 4) :
    spectralMoment (factorLabels factors) j =
      (factors.map fun f => if j = f.root then q ^ f.qShift * t ^ f.tShift else 0).sum := by
  induction factors with
  | nil => simp [factorLabels, spectralMoment_zero]
  | cons f fs ih =>
    change spectralMoment (Y f.root f.qShift f.tShift + factorLabels fs) j = _
    rw [spectralMoment_add]
    change spectralMoment (Y f.root f.qShift f.tShift) j + spectralMoment (factorLabels fs) j = _
    rw [spectralMoment_Y f.root j f.qShift f.tShift, ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem factorLabels_eq_of_monomial_eq (factors other : List (InverseRootFactor D₄))
    (h : monomialOfFactors factors = monomialOfFactors other) : factorLabels factors = factorLabels other := by
  have hC : Function.Injective
      ((deformedCartan D₄ (-1) : Matrix (Fin 4) (Fin 4) Coefficient).mulVec) :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr d4_deformedCartan_creation_det_ne_zero))
  have he : (deformedCartan D₄ (-1) : Matrix (Fin 4) (Fin 4) Coefficient).mulVec
        (fun k => (deformedCartan D₄ (-1))⁻¹ k (1 : Fin 4) - spectralMoment (factorLabels factors) k) =
      (deformedCartan D₄ (-1) : Matrix (Fin 4) (Fin 4) Coefficient).mulVec
        (fun k => (deformedCartan D₄ (-1))⁻¹ k (1 : Fin 4) - spectralMoment (factorLabels other) k) := by
    funext j
    simp only [Matrix.mulVec, dotProduct, spectralMoment_factorLabels]
    erw [elementary_creation_coordinates factors j, elementary_creation_coordinates other j, h]
  have hv := hC he
  apply spectralMoment_injective
  funext j
  exact sub_right_inj.mp (congrFun hv j)

def inverseRootFactorKey (f : InverseRootFactor D₄) : Fin 4 × Spectral :=
  (f.root, (f.qShift, f.tShift))

theorem inverseRootFactorKey_injective : Function.Injective inverseRootFactorKey := by
  intro f g h
  cases f with | mk i a b =>
    cases g with | mk j c d =>
      simp only [inverseRootFactorKey] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl

theorem factorLabels_count (factors : List (InverseRootFactor D₄)) (f : InverseRootFactor D₄) :
    factorLabels factors (inverseRootFactorKey f) = (factors.count f : ℤ) := by
  classical
  induction factors with
  | nil => simp [factorLabels]
  | cons g gs ih =>
    have hsplit : factorLabels (g :: gs) = Y g.root g.qShift g.tShift + factorLabels gs := rfl
    rw [hsplit, Finsupp.add_apply, ih]
    by_cases hgf : g = f
    · subst g
      simp [Y, inverseRootFactorKey, add_comm]
    · have hkey : inverseRootFactorKey g ≠ inverseRootFactorKey f :=
        fun he => hgf (inverseRootFactorKey_injective he)
      simp only [Y]
      change Finsupp.single (inverseRootFactorKey g) 1 (inverseRootFactorKey f) +
        (gs.count f : ℤ) = ((g :: gs).count f : ℤ)
      simp [Finsupp.single_eq_of_ne hkey.symm, hgf]

theorem factors_perm_of_monomial_eq (factors other : List (InverseRootFactor D₄))
    (h : monomialOfFactors factors = monomialOfFactors other) : factors.Perm other := by
  classical
  apply List.perm_iff_count.mpr
  intro f
  have he := congrArg (fun m : Monomial => m (inverseRootFactorKey f))
    (factorLabels_eq_of_monomial_eq factors other h)
  rw [factorLabels_count, factorLabels_count] at he
  exact_mod_cast he

/-- Grouping by Laurent monomial preserves the complete original
elementary symbol, not just its normalized first creation coefficients. -/
theorem elementarySymbol_coefficients_eq_of_monomial_eq
    (factors other : List (InverseRootFactor D₄))
    (h : monomialOfFactors factors = monomialOfFactors other) (charge : Charge D₄) :
    (elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge =
      (elementarySymbol D₄ (1 : Fin 4) other).coefficients charge := by
  have hp := factors_perm_of_monomial_eq factors other h
  change (weightVertex D₄ (1 : Fin 4) false 0 0).coefficients charge *
      (normalProducts D₄ (factors.map fun f => rootVertex D₄ f.root true f.qShift f.tShift)).coefficients charge =
    (weightVertex D₄ (1 : Fin 4) false 0 0).coefficients charge *
      (normalProducts D₄ (other.map fun f => rootVertex D₄ f.root true f.qShift f.tShift)).coefficients charge
  rw [normalProducts_coefficients, normalProducts_coefficients]
  congr 1
  exact ((hp.map (fun f => rootVertex D₄ f.root true f.qShift f.tShift)).map
    (fun a => a.coefficients charge)).prod_eq

theorem normalProducts_offset_sum (g : SimpleLieType) (xs : List (NormalSymbol g)) :
    (normalProducts g xs).offset = (xs.map NormalSymbol.offset).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change a.offset + (normalProducts g as).offset = _
    rw [ih]
    rfl

theorem elementarySymbol_offset_zero (g : SimpleLieType) (i : RootIndex g)
    (factors : List (InverseRootFactor g)) : (elementarySymbol g i factors).offset = 0 := by
  simp [elementarySymbol, normalProduct, weightVertex, rootVertex, normalProducts_offset_sum,
    Function.comp_def]

theorem elementarySymbol_eq_of_monomial_eq (factors other : List (InverseRootFactor D₄))
    (h : monomialOfFactors factors = monomialOfFactors other) :
    elementarySymbol D₄ (1 : Fin 4) factors = elementarySymbol D₄ (1 : Fin 4) other := by
  have hc := funext (elementarySymbol_coefficients_eq_of_monomial_eq factors other h)
  have ho : (elementarySymbol D₄ (1 : Fin 4) factors).offset =
      (elementarySymbol D₄ (1 : Fin 4) other).offset := by
    exact (elementarySymbol_offset_zero D₄ (1 : Fin 4) factors).trans
      (elementarySymbol_offset_zero D₄ (1 : Fin 4) other).symm
  generalize elementarySymbol D₄ (1 : Fin 4) factors = a at hc ho ⊢
  generalize elementarySymbol D₄ (1 : Fin 4) other = b at hc ho ⊢
  cases a with | mk ac ao =>
    cases b with | mk bc bo =>
      change ac = bc at hc
      change ao = bo at ho
      cases hc
      cases ho
      rfl

theorem elementaryField_eq_of_monomial_eq (factors other : List (InverseRootFactor D₄))
    (h : monomialOfFactors factors = monomialOfFactors other) :
    evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) =
      evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) other) :=
  congrArg (evaluateSymbol D₄) (elementarySymbol_eq_of_monomial_eq factors other h)

end
end FrenkelReshetikhin.D4CounterexampleProof
