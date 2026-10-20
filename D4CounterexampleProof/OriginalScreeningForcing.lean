import D4CounterexampleProof.IndexedExpansion
import D4CounterexampleProof.Reduction
import D4CounterexampleProof.FundamentalModule

/-! The D₄ monomial chain and the two incompatible endpoints, now forced
by the original FR screening centralizer rather than analytic hypotheses. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance originalScreeningForcingField : _root_.Field Coefficient := inferInstance

theorem original_screenings_force_M (terms : List (ElementaryTerm D₄))
    (hvalid : ∀ term ∈ terms, term.valid)
    (hW : fundamentalExpansion D₄ (1 : Fin 4) terms ∈ deformedW D₄)
    (hsupport : ∀ j : Option (Fin terms.length),
      monomialWeight (monomialOfFactors (indexedTerm terms j).factors) ∈ roots.map coordinatesWeight ∨
      monomialWeight (monomialOfFactors (indexedTerm terms j).factors) = 0) :
    ∃ j : Option (Fin terms.length), monomialOfFactors (indexedTerm terms j).factors = M := by
  let m (j : Option (Fin terms.length)) := monomialOfFactors (indexedTerm terms j).factors
  have h0 : m none = M₀ := by simp [m, indexedTerm, leadingTerm, monomialOfFactors]
  have hp0 : screeningDivisor .minus (rootExponents (m none) 1) (-1, 0) = -1 := by
    rw [h0, screeningDivisor_minus, forcing_pole_0]
  obtain ⟨j1, hn1, b1, hb1, hs1⟩ := indexed_expansion_pole_partner terms hvalid hW .minus 1 none (-1, 0) hp0
  change m j1 ≠ m none at hn1
  change tDifference (m j1 - m none) = A 1 (-1) 0 - A 1 b1.1 b1.2 at hs1
  rw [h0] at hn1 hs1
  have h1 : m j1 = M₁ := first_partner_of_root_support _ _ _ hs1 (hsupport j1) hn1
  have hp1 : screeningDivisor .minus (rootExponents (m j1) 0) (-2, 1) = -1 := by
    rw [h1, screeningDivisor_minus, forcing_pole_1]
  obtain ⟨j2, hn2, b2, hb2, hs2⟩ := indexed_expansion_pole_partner terms hvalid hW .minus 0 j1 (-2, 1) hp1
  change m j2 ≠ m j1 at hn2
  change tDifference (m j2 - m j1) = A 0 (-2) 1 - A 0 b2.1 b2.2 at hs2
  rw [h1] at hn2 hs2
  have h2 : m j2 = M₂ := second_partner_of_root_support _ _ _ hs2 (hsupport j2) hn2
  have hp2 : screeningDivisor .minus (rootExponents (m j2) 2) (-2, 1) = -1 := by
    rw [h2, screeningDivisor_minus, forcing_pole_2]
  obtain ⟨j3, hn3, b3, hb3, hs3⟩ := indexed_expansion_pole_partner terms hvalid hW .minus 2 j2 (-2, 1) hp2
  change m j3 ≠ m j2 at hn3
  change tDifference (m j3 - m j2) = A 2 (-2) 1 - A 2 b3.1 b3.2 at hs3
  rw [h2] at hn3 hs3
  have h3 : m j3 = M₃ := third_partner_of_root_support _ _ _ hs3 (hsupport j3) hn3
  have hp3 : screeningDivisor .minus (rootExponents (m j3) 1) (-3, 2) = -1 := by
    rw [h3, screeningDivisor_minus, forcing_pole_3]
  obtain ⟨j4, hn4, b4, hb4, hs4⟩ := indexed_expansion_pole_partner terms hvalid hW .minus 1 j3 (-3, 2) hp3
  change m j4 ≠ m j3 at hn4
  change tDifference (m j4 - m j3) = A 1 (-3) 2 - A 1 b4.1 b4.2 at hs4
  rw [h3] at hn4 hs4
  exact ⟨j4, fourth_partner_of_root_support _ _ _ hs4 (hsupport j4) hn4⟩

theorem original_screenings_force_endpoints (terms : List (ElementaryTerm D₄))
    (hvalid : ∀ term ∈ terms, term.valid)
    (hW : fundamentalExpansion D₄ (1 : Fin 4) terms ∈ deformedW D₄)
    (hsupport : ∀ j : Option (Fin terms.length),
      monomialWeight (monomialOfFactors (indexedTerm terms j).factors) ∈ roots.map coordinatesWeight ∨
      monomialWeight (monomialOfFactors (indexedTerm terms j).factors) = 0) :
    (∃ j : Option (Fin terms.length), monomialOfFactors (indexedTerm terms j).factors = Nminus) ∧
    (∃ j : Option (Fin terms.length), monomialOfFactors (indexedTerm terms j).factors = Nplus) := by
  obtain ⟨source, hsource⟩ := original_screenings_force_M terms hvalid hW hsupport
  constructor
  · have hpole : screeningDivisor .minus
        (rootExponents (monomialOfFactors (indexedTerm terms source).factors) 3) (-2, 1) = -1 := by
      rw [hsource, screeningDivisor_minus, first_minus_pole]
    obtain ⟨j, hn, b, hb, hs⟩ := indexed_expansion_pole_partner terms hvalid hW .minus 3 source (-2, 1) hpole
    change tDifference (monomialOfFactors (indexedTerm terms j).factors -
      monomialOfFactors (indexedTerm terms source).factors) = A 3 (-2) 1 - A 3 b.1 b.2 at hs
    rw [hsource] at hn hs
    have hcases := final_minus_partner_of_root_support _ b.1 b.2 hs (hsupport j)
    rcases hcases with he | he | he
    · exact (hn he).elim
    · rw [screeningDivisor_minus, he, intermediate_has_no_minus_pole] at hb
      omega
    · exact ⟨j, he⟩
  · have hpole : screeningDivisor .plus
        (rootExponents (monomialOfFactors (indexedTerm terms source).factors) 3) (-1, 2) = -1 := by
      rw [hsource, screeningDivisor_plus, first_plus_pole]
    obtain ⟨j, hn, b, hb, hs⟩ := indexed_expansion_pole_partner terms hvalid hW .plus 3 source (-1, 2) hpole
    change qDifference (monomialOfFactors (indexedTerm terms j).factors -
      monomialOfFactors (indexedTerm terms source).factors) = A 3 b.1 b.2 - A 3 (-1) 2 at hs
    rw [hsource] at hn hs
    have hcases := final_plus_partner_of_root_support _ b.1 b.2 hs (hsupport j)
    rcases hcases with he | he | he
    · exact (hn he).elim
    · rw [screeningDivisor_plus, he, intermediate_has_no_plus_pole] at hb
      omega
    · exact ⟨j, he⟩

theorem indexed_negative_endpoint_is_term (terms : List (ElementaryTerm D₄))
    (endpoint : Monomial) (hw : monomialWeight endpoint = negativeOuterWeight)
    (hex : ∃ j : Option (Fin terms.length), monomialOfFactors (indexedTerm terms j).factors = endpoint) :
    ∃ term ∈ terms, elementaryWeight central term.factors = negativeOuterWeight ∧
      monomialOfFactors term.factors = endpoint := by
  obtain ⟨j, hj⟩ := hex
  have hweight : elementaryWeight central (indexedTerm terms j).factors = negativeOuterWeight := by
    rw [← monomialOfFactors_weight, hj, hw]
  cases j with
  | none =>
    have hlead : elementaryWeight central (indexedTerm terms none).factors =
        fundamentalWeight D₄ central := by
      funext k
      simp [indexedTerm, leadingTerm, elementaryWeight]
    exact (negative_outer_ne_highest (hweight.symm.trans hlead)).elim
  | some j => exact ⟨terms.get j, List.get_mem terms j, hweight, hj⟩

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

/-- The original screening argument is complete. Only the two stated
consequences of the original Drinfeld-polynomial module definition are
needed to conclude the D₄ counterexample. -/
theorem no_central_field_of_module_facts
    (hmodule : ∀ (d : ℕ) (V : OriginalFR.Drinfeld.Representation D₄ d),
      OriginalFR.Drinfeld.FundamentalRepresentation D₄ central V →
      OriginalFR.Drinfeld.weightMultiplicity D₄ V negativeOuterWeight = 1)
    (hsupport : ∀ (d : ℕ) (V : OriginalFR.Drinfeld.Representation D₄ d),
      OriginalFR.Drinfeld.FundamentalRepresentation D₄ central V →
      ∀ weight, OriginalFR.Drinfeld.weightMultiplicity D₄ V weight ≠ 0 →
        weight ∈ roots.map coordinatesWeight ∨ weight = 0) :
    ¬ HasFundamentalField D₄ central := by
  intro hfield
  obtain ⟨terms, d, V, hvalid, hW, hfund, hchar⟩ := hfield
  have hs (j : Option (Fin terms.length)) :
      monomialWeight (monomialOfFactors (PolynomialFock.indexedTerm terms j).factors) ∈
        roots.map coordinatesWeight ∨
      monomialWeight (monomialOfFactors (PolynomialFock.indexedTerm terms j).factors) = 0 := by
    rw [monomialOfFactors_weight]
    apply hsupport d V hfund
    cases j with
    | none =>
      have he : elementaryWeight central (PolynomialFock.indexedTerm terms none).factors =
          fundamentalWeight D₄ central := by
        funext k
        simp [PolynomialFock.indexedTerm, PolynomialFock.leadingTerm, elementaryWeight]
      rw [he]
      exact Nat.ne_of_gt (OriginalFR.Drinfeld.fundamental_highest_weightMultiplicity_pos D₄ central V hfund)
    | some j =>
      rw [← hchar]
      exact Nat.ne_of_gt (term_weight_expansionMultiplicity_pos central terms hvalid _ (List.get_mem terms j))
  obtain ⟨hm, hp⟩ := PolynomialFock.original_screenings_force_endpoints terms hvalid hW hs
  have hminus := PolynomialFock.indexed_negative_endpoint_is_term terms Nminus minus_endpoint_weight hm
  have hplus := PolynomialFock.indexed_negative_endpoint_is_term terms Nplus plus_endpoint_weight hp
  have hone : expansionMultiplicity central terms negativeOuterWeight = 1 := by
    rw [hchar]
    exact hmodule d V hfund
  exact incompatible_screening_requirements terms negativeOuterWeight
    negative_outer_ne_highest hvalid hone hminus hplus

end
end FrenkelReshetikhin.D4CounterexampleProof
