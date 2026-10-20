import D4CounterexampleProof.GroupedPoleNecessity

/-! Finite indexing of the original elementary expansion, retaining the
prescribed leading term and all repeated summands. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance indexedExpansionField : _root_.Field Coefficient := inferInstance

def leadingTerm : ElementaryTerm D₄ := ⟨1, [], 1⟩

def indexedTerm (terms : List (ElementaryTerm D₄)) : Option (Fin terms.length) → ElementaryTerm D₄
  | none => leadingTerm
  | some j => terms.get j

theorem leadingTerm_valid : leadingTerm.valid := by
  constructor
  · decide
  · simp [leadingTerm, specializesToNat]

theorem indexedTerm_valid (terms : List (ElementaryTerm D₄))
    (hvalid : ∀ term ∈ terms, term.valid) (j : Option (Fin terms.length)) :
    (indexedTerm terms j).valid := by
  cases j with
  | none => exact leadingTerm_valid
  | some j => exact hvalid _ (List.get_mem terms j)

theorem elementarySymbol_nil :
    elementarySymbol D₄ (1 : Fin 4) [] = weightVertex D₄ (1 : Fin 4) false 0 0 := by
  simp [elementarySymbol, normalProducts, normalProduct, symbolOne]

theorem fundamentalExpansion_indexed (terms : List (ElementaryTerm D₄)) :
    fundamentalExpansion D₄ (1 : Fin 4) terms =
      ∑ j : Option (Fin terms.length), RatFunc.C (indexedTerm terms j).coefficient •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) (indexedTerm terms j).factors) := by
  rw [Fintype.sum_option]
  simp only [indexedTerm, leadingTerm, map_one, elementarySymbol_nil]
  rw [one_smul Scalars (evaluateSymbol D₄ (weightVertex D₄ (1 : Fin 4) false 0 0))]
  change _ + (terms.map fun term => RatFunc.C term.coefficient •
    evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) term.factors)).sum = _
  congr 1
  calc
    _ = (List.ofFn fun j : Fin terms.length => RatFunc.C (terms.get j).coefficient •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) (terms.get j).factors)).sum := by
      have hm := List.map_ofFn (f := terms.get) (g := fun term => RatFunc.C term.coefficient •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) term.factors))
      rw [List.ofFn_get] at hm
      exact congrArg List.sum hm
    _ = _ := List.sum_ofFn (M := Field D₄) (f := fun j : Fin terms.length =>
      RatFunc.C (terms.get j).coefficient •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) (terms.get j).factors))

theorem indexed_expansion_pole_partner (terms : List (ElementaryTerm D₄))
    (hvalid : ∀ term ∈ terms, term.valid)
    (hW : fundamentalExpansion D₄ (1 : Fin 4) terms ∈ deformedW D₄)
    (sign : ScreeningSign) (i : Fin 4) (source : Option (Fin terms.length)) (a : Spectral)
    (hpole : screeningDivisor sign
      (rootExponents (monomialOfFactors (indexedTerm terms source).factors) i) a = -1) :
    ∃ j : Option (Fin terms.length),
      monomialOfFactors (indexedTerm terms j).factors ≠
        monomialOfFactors (indexedTerm terms source).factors ∧
      ∃ b : Spectral, screeningDivisor sign
        (rootExponents (monomialOfFactors (indexedTerm terms j).factors) i) b < 0 ∧
      match sign with
      | .minus => tDifference (monomialOfFactors (indexedTerm terms j).factors -
            monomialOfFactors (indexedTerm terms source).factors) = A i a.1 a.2 - A i b.1 b.2
      | .plus => qDifference (monomialOfFactors (indexedTerm terms j).factors -
            monomialOfFactors (indexedTerm terms source).factors) = A i b.1 b.2 - A i a.1 a.2 := by
  classical
  have hW' := hW
  rw [fundamentalExpansion_indexed] at hW'
  obtain ⟨j, hj, hm, b, hb, hs⟩ := positive_expansion_pole_partner Finset.univ
    (fun j => (indexedTerm terms j).factors) (fun j => (indexedTerm terms j).coefficient)
    (fun j => (indexedTerm terms j).multiplicity)
    (fun j _ => (indexedTerm_valid terms hvalid j).1)
    (fun j _ => (indexedTerm_valid terms hvalid j).2)
    hW' sign i source (Finset.mem_univ _) a hpole
  cases sign <;> exact ⟨j, hm, b, hb, hs⟩

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
