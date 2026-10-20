import D4CounterexampleProof.RootWeightSupport
import D4CounterexampleProof.PoleOrders

/-!
The finite part of screening-partner forcing. `ScreeningPoleNecessity.lean`
and `GroupedPoleNecessity.lean` supply the partner hypotheses from membership
in the original deformed-W centralizer.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

theorem minus_endpoint_weight : monomialWeight Nminus = -simpleRoot D₄ outer := by
  rw [← minus_factors_monomial, monomialOfFactors_weight, minus_factors_weight]

theorem plus_endpoint_weight : monomialWeight Nplus = -simpleRoot D₄ outer := by
  rw [← plus_factors_monomial, monomialOfFactors_weight, plus_factors_weight]

theorem minus_partner_forced (terms : List (ElementaryTerm D₄))
    (hsupport : ∀ term ∈ terms,
      monomialWeight (monomialOfFactors term.factors) ∈
        roots.map coordinatesWeight ∨
      monomialWeight (monomialOfFactors term.factors) = 0)
    (hpartner : ∃ term ∈ terms, ∃ da db : ℤ,
      tDifference (monomialOfFactors term.factors - M) =
        A 3 (-2) 1 - A 3 da db ∧
      monomialOfFactors term.factors ≠ M ∧
      minusPoleOrder (monomialOfFactors term.factors) 3 (da, db) ≠ 0) :
    ∃ term ∈ terms,
      elementaryWeight central term.factors = -simpleRoot D₄ outer ∧
      monomialOfFactors term.factors = Nminus := by
  obtain ⟨term, ht, da, db, hsig, hne, hpole⟩ := hpartner
  have hcases := final_minus_partner_of_root_support
    (monomialOfFactors term.factors) da db hsig (hsupport term ht)
  rcases hcases with hM | hZ | hN
  · exact False.elim (hne hM)
  · rw [hZ, intermediate_has_no_minus_pole] at hpole
    exact False.elim (hpole rfl)
  · refine ⟨term, ht, ?_, hN⟩
    rw [← monomialOfFactors_weight, hN, minus_endpoint_weight]

theorem plus_partner_forced (terms : List (ElementaryTerm D₄))
    (hsupport : ∀ term ∈ terms,
      monomialWeight (monomialOfFactors term.factors) ∈
        roots.map coordinatesWeight ∨
      monomialWeight (monomialOfFactors term.factors) = 0)
    (hpartner : ∃ term ∈ terms, ∃ da db : ℤ,
      qDifference (monomialOfFactors term.factors - M) =
        A 3 da db - A 3 (-1) 2 ∧
      monomialOfFactors term.factors ≠ M ∧
      plusPoleOrder (monomialOfFactors term.factors) 3 (da, db) ≠ 0) :
    ∃ term ∈ terms,
      elementaryWeight central term.factors = -simpleRoot D₄ outer ∧
      monomialOfFactors term.factors = Nplus := by
  obtain ⟨term, ht, da, db, hsig, hne, hpole⟩ := hpartner
  have hcases := final_plus_partner_of_root_support
    (monomialOfFactors term.factors) da db hsig (hsupport term ht)
  rcases hcases with hM | hZ | hN
  · exact False.elim (hne hM)
  · rw [hZ, intermediate_has_no_plus_pole] at hpole
    exact False.elim (hpole rfl)
  · refine ⟨term, ht, ?_, hN⟩
    rw [← monomialOfFactors_weight, hN, plus_endpoint_weight]

end
end FrenkelReshetikhin.D4CounterexampleProof
