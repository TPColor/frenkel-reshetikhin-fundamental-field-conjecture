import D4CounterexampleProof.ScreenedCancellation

/-! Projection of the original Fock vacuum to its four frequency-one
creation coordinates. This is a proved projection of the original
module, not a replacement definition of the Fock space. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance firstCreationModesField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def firstCreationEmbedding : Fin 4 ↪ Variables where
  toFun k := (k, ⟨1, by decide⟩)
  inj' := by intro i j h; exact congrArg Prod.fst h

def firstModeEmbedding : Fin 4 ↪ ModeIndex D₄ :=
  firstCreationEmbedding.trans creationEmbedding

@[simp] theorem firstModeEmbedding_apply (k : Fin 4) :
    firstModeEmbedding k = (k, ⟨-1, by decide⟩) := rfl

theorem killCompl_trans {K σ τ υ : Type*} [CommSemiring K]
    (e : σ ↪ τ) (f : τ ↪ υ) (p : MvPowerSeries υ K) :
    MvPowerSeries.killCompl (e.trans f) p =
      MvPowerSeries.killCompl e (MvPowerSeries.killCompl f p) := by
  ext d
  simp only [MvPowerSeries.coeff_killCompl, Finsupp.embDomain_trans_apply]

/-- All first-mode coefficients are determined by the actual original
vacuum actions. In particular, a zero field action has zero projection. -/
theorem firstModeSymbol_zero_of_vacuum_coefficients
    (a : NormalSymbol D₄) (charge : Charge D₄)
    (h : ∀ n : ℤ,
      evaluateSymbol D₄ a charge n (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) = 0) :
    MvPowerSeries.killCompl firstModeEmbedding (a.coefficients charge) = 0 := by
  rw [firstModeEmbedding, killCompl_trans,
    creationSymbol_zero_of_vacuum_coefficients a charge h, map_zero]

/-- The cancellation criterion using precisely the four creation modes
in the written proof. Polynomial factors may have arbitrary finite degree. -/
theorem firstMode_screened_cancelling_partner {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (sign : ScreeningSign) (root : Fin 4) (qa ta : ι → ℤ)
    (P : ι → MvPolynomial (Fin 4) Scalars)
    (hsum : ∑ j ∈ s, (P j : MvPowerSeries (Fin 4) Scalars) *
      MvPowerSeries.killCompl firstModeEmbedding
        ((elementarySymbol D₄ (1 : Fin 4) (factors j)).coefficients charge *
          exponentialSymbol D₄ (fun mode => RatFunc.C
            (screeningModes (g := D₄) sign root mode.2.val mode.1 *
              (q ^ qa j * t ^ ta j) ^ (-mode.2.val)))) = 0)
    (source : ι) (hsource : source ∈ s) (hPsource : P source ≠ 0) :
    ∃ j ∈ s, j ≠ source ∧ P j ≠ 0 ∧
      match sign with
      | .minus => tDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa source) (ta source) - A root (qa j) (ta j)
      | .plus => qDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa j) (ta j) - A root (qa source) (ta source) := by
  obtain ⟨j, hj, hne, hpj, hs⟩ := screened_restricted_cancelling_partner s firstModeEmbedding
    id (fun _ => rfl) factors charge sign root qa ta P hsum source hsource hPsource
  refine ⟨j, hj, hne, hpj, ?_⟩
  cases sign <;> exact hs

/-- Equal Laurent signatures at a fixed elementary monomial determine
the pole label. This excludes cancellation by a second label of that
same monomial when each monomial/pole pair is indexed once. -/
theorem pole_parameters_eq_of_same_monomial_signature
    (sign : ScreeningSign) (root : Fin 4) (m n : Monomial)
    (a b : Spectral) (hmn : m = n)
    (hs : match sign with
      | .minus => tDifference (m - n) = A root a.1 a.2 - A root b.1 b.2
      | .plus => qDifference (m - n) = A root b.1 b.2 - A root a.1 a.2) : a = b := by
  subst m
  cases sign with
  | minus =>
    change tDifference (n - n) = A root a.1 a.2 - A root b.1 b.2 at hs
    have hz : tDifference (0 : Monomial) = 0 := by simp [tDifference, shift]
    rw [sub_self, hz] at hs
    exact @root_monomial_parameters_injective root a b (sub_eq_zero.mp hs.symm)
  | plus =>
    change qDifference (n - n) = A root b.1 b.2 - A root a.1 a.2 at hs
    have hz : qDifference (0 : Monomial) = 0 := by simp [qDifference, shift]
    rw [sub_self, hz] at hs
    exact (@root_monomial_parameters_injective root b a (sub_eq_zero.mp hs.symm)).symm

theorem firstMode_screened_distinct_partner {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (sign : ScreeningSign) (root : Fin 4) (qa ta : ι → ℤ)
    (P : ι → MvPolynomial (Fin 4) Scalars)
    (hpairs : Set.InjOn (fun j => (monomialOfFactors (factors j), (qa j, ta j))) s)
    (hsum : ∑ j ∈ s, (P j : MvPowerSeries (Fin 4) Scalars) *
      MvPowerSeries.killCompl firstModeEmbedding
        ((elementarySymbol D₄ (1 : Fin 4) (factors j)).coefficients charge *
          exponentialSymbol D₄ (fun mode => RatFunc.C
            (screeningModes (g := D₄) sign root mode.2.val mode.1 *
              (q ^ qa j * t ^ ta j) ^ (-mode.2.val)))) = 0)
    (source : ι) (hsource : source ∈ s) (hPsource : P source ≠ 0) :
    ∃ j ∈ s, monomialOfFactors (factors j) ≠ monomialOfFactors (factors source) ∧ P j ≠ 0 ∧
      match sign with
      | .minus => tDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa source) (ta source) - A root (qa j) (ta j)
      | .plus => qDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa j) (ta j) - A root (qa source) (ta source) := by
  obtain ⟨j, hj, hne, hpj, hs⟩ := firstMode_screened_cancelling_partner s factors charge sign root
    qa ta P hsum source hsource hPsource
  have hm : monomialOfFactors (factors j) ≠ monomialOfFactors (factors source) := by
    intro hm
    have hs' : (qa source, ta source) = (qa j, ta j) := by
      apply pole_parameters_eq_of_same_monomial_signature sign root _ _ _ _ hm
      cases sign <;> exact hs
    exact hne (hpairs hj hsource (Prod.ext hm hs'.symm))
  refine ⟨j, hj, hm, hpj, ?_⟩
  cases sign <;> exact hs

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
