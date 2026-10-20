import D4CounterexampleProof.Multiplicity
import D4CounterexampleProof.PartnerForcing

/-!
Conditional reductions from the finite D₄ obstruction to the original
`HasFundamentalField` definition. The screening premises are supplied by
`OriginalScreeningForcing.lean`, and the module facts by
`FundamentalCharacter.lean`.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

def negativeOuterWeight : Weight D₄ := -simpleRoot D₄ outer

/-- The D₄ contradiction, reduced to the module's root-weight multiplicity
and the two screening necessities. -/
theorem no_central_field_of_screening_facts
    (hmodule : ∀ (d : ℕ) (V : OriginalFR.Drinfeld.Representation D₄ d),
      OriginalFR.Drinfeld.FundamentalRepresentation D₄ central V →
      OriginalFR.Drinfeld.weightMultiplicity D₄ V negativeOuterWeight = 1)
    (hminus : ∀ (terms : List (ElementaryTerm D₄)) (d : ℕ)
      (V : OriginalFR.Drinfeld.Representation D₄ d),
      (∀ term ∈ terms, term.valid) →
      OriginalFR.Fields.fundamentalExpansion D₄ central terms ∈
        OriginalFR.Fields.deformedW D₄ →
      OriginalFR.Drinfeld.FundamentalRepresentation D₄ central V →
      (∀ weight, expansionMultiplicity central terms weight =
        OriginalFR.Drinfeld.weightMultiplicity D₄ V weight) →
      ∃ term ∈ terms,
        elementaryWeight central term.factors = negativeOuterWeight ∧
        monomialOfFactors term.factors = Nminus)
    (hplus : ∀ (terms : List (ElementaryTerm D₄)) (d : ℕ)
      (V : OriginalFR.Drinfeld.Representation D₄ d),
      (∀ term ∈ terms, term.valid) →
      OriginalFR.Fields.fundamentalExpansion D₄ central terms ∈
        OriginalFR.Fields.deformedW D₄ →
      OriginalFR.Drinfeld.FundamentalRepresentation D₄ central V →
      (∀ weight, expansionMultiplicity central terms weight =
        OriginalFR.Drinfeld.weightMultiplicity D₄ V weight) →
      ∃ term ∈ terms,
        elementaryWeight central term.factors = negativeOuterWeight ∧
        monomialOfFactors term.factors = Nplus) :
    ¬ HasFundamentalField D₄ central := by
  intro hfield
  obtain ⟨terms, d, V, hvalid, hW, hfund, hchar⟩ := hfield
  have hone : expansionMultiplicity central terms negativeOuterWeight = 1 := by
    rw [hchar]
    exact hmodule d V hfund
  exact incompatible_screening_requirements terms negativeOuterWeight
    negative_outer_ne_highest hvalid hone
    (hminus terms d V hvalid hW hfund hchar)
    (hplus terms d V hvalid hW hfund hchar)

/-- A finer reduction: the two analytic inputs need only yield distinct
signature-matched partners with actual poles. The finite D₄ certificates
force their monomials to be `Nminus` and `Nplus`. Establishing these premises
from `deformedW` must also force the four predecessors of `M`; the finite
parts of those steps are proved in `RootWeightSupport`. -/
theorem no_central_field_of_pole_facts
    (hmodule : ∀ (d : ℕ) (V : OriginalFR.Drinfeld.Representation D₄ d),
      OriginalFR.Drinfeld.FundamentalRepresentation D₄ central V →
      OriginalFR.Drinfeld.weightMultiplicity D₄ V negativeOuterWeight = 1)
    (hsupport : ∀ (d : ℕ) (V : OriginalFR.Drinfeld.Representation D₄ d),
      OriginalFR.Drinfeld.FundamentalRepresentation D₄ central V →
      ∀ weight, OriginalFR.Drinfeld.weightMultiplicity D₄ V weight ≠ 0 →
        weight ∈ roots.map coordinatesWeight ∨ weight = 0)
    (hminusPole : ∀ (terms : List (ElementaryTerm D₄)) (d : ℕ)
      (V : OriginalFR.Drinfeld.Representation D₄ d),
      (∀ term ∈ terms, term.valid) →
      OriginalFR.Fields.fundamentalExpansion D₄ central terms ∈
        OriginalFR.Fields.deformedW D₄ →
      OriginalFR.Drinfeld.FundamentalRepresentation D₄ central V →
      (∀ weight, expansionMultiplicity central terms weight =
        OriginalFR.Drinfeld.weightMultiplicity D₄ V weight) →
      ∃ term ∈ terms, ∃ da db : ℤ,
        tDifference (monomialOfFactors term.factors - M) =
          A 3 (-2) 1 - A 3 da db ∧
        monomialOfFactors term.factors ≠ M ∧
        minusPoleOrder (monomialOfFactors term.factors) 3 (da, db) ≠ 0)
    (hplusPole : ∀ (terms : List (ElementaryTerm D₄)) (d : ℕ)
      (V : OriginalFR.Drinfeld.Representation D₄ d),
      (∀ term ∈ terms, term.valid) →
      OriginalFR.Fields.fundamentalExpansion D₄ central terms ∈
        OriginalFR.Fields.deformedW D₄ →
      OriginalFR.Drinfeld.FundamentalRepresentation D₄ central V →
      (∀ weight, expansionMultiplicity central terms weight =
        OriginalFR.Drinfeld.weightMultiplicity D₄ V weight) →
      ∃ term ∈ terms, ∃ da db : ℤ,
        qDifference (monomialOfFactors term.factors - M) =
          A 3 da db - A 3 (-1) 2 ∧
        monomialOfFactors term.factors ≠ M ∧
        plusPoleOrder (monomialOfFactors term.factors) 3 (da, db) ≠ 0) :
    ¬ HasFundamentalField D₄ central := by
  intro hfield
  obtain ⟨terms, d, V, hvalid, hW, hfund, hchar⟩ := hfield
  have hone : expansionMultiplicity central terms negativeOuterWeight = 1 := by
    rw [hchar]
    exact hmodule d V hfund
  have hs : ∀ term ∈ terms,
      monomialWeight (monomialOfFactors term.factors) ∈
        roots.map coordinatesWeight ∨
      monomialWeight (monomialOfFactors term.factors) = 0 := by
    intro term ht
    rw [monomialOfFactors_weight]
    apply hsupport d V hfund
    rw [← hchar]
    exact Nat.ne_of_gt (term_weight_expansionMultiplicity_pos central terms hvalid term ht)
  have hm := minus_partner_forced terms hs
    (hminusPole terms d V hvalid hW hfund hchar)
  have hp := plus_partner_forced terms hs
    (hplusPole terms d V hvalid hW hfund hchar)
  exact incompatible_screening_requirements terms negativeOuterWeight
    negative_outer_ne_highest hvalid hone hm hp

end
end FrenkelReshetikhin.D4CounterexampleProof
