import D4CounterexampleProof.ScreenedLocalResidues
import D4CounterexampleProof.PrincipalPartCoefficients
import D4CounterexampleProof.DivisorPoles

/-! From a zero sum of genuine local Laurent residues to a distinct
screening-signature partner. `ScreeningResidueBridge.lean` and
`ScreeningPoleNecessity.lean` derive the zero sum from original W-membership. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance localResiduePartnersField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem firstScreeningSeries_spectral (sign : ScreeningSign) (root : Fin 4) (qa ta : ℤ) :
    firstScreeningSeries sign root (RatFunc.C (q ^ qa * t ^ ta)) =
      MvPowerSeries.killCompl firstModeEmbedding
        (exponentialSymbol D₄ (fun mode => RatFunc.C
          (screeningModes (g := D₄) sign root mode.2.val mode.1 *
            (q ^ qa * t ^ ta) ^ (-mode.2.val)))) := by
  unfold firstScreeningSeries
  apply congrArg (MvPowerSeries.killCompl firstModeEmbedding)
  apply congrArg (exponentialSymbol D₄)
  funext mode
  simp only [map_mul, map_zpow₀]

theorem local_residue_sum_forces_distinct_partner {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (sign : ScreeningSign) (root : Fin 4) (qa ta : ι → ℤ)
    (order : ι → ℕ) (r : (j : ι) → Fin (order j) → Scalars)
    (hpairs : Set.InjOn (fun j => (monomialOfFactors (factors j), (qa j, ta j))) s)
    (hlocal : (∑ j ∈ s,
      (∑ k : Fin (order j),
        HahnSeries.single (-((k.val : ℤ) + 1)) (MvPowerSeries.C (r j k)) *
          (screenedPoleTaylor (factors j) charge sign root (RatFunc.C (q ^ qa j * t ^ ta j)) :
            LaurentSeries (MvPowerSeries (Fin 4) Scalars))).coeff (-1) :
              MvPowerSeries (Fin 4) Scalars) = 0)
    (source : ι) (hsource : source ∈ s) (horder : order source = 1)
    (hr : r source ⟨0, by omega⟩ ≠ 0) :
    ∃ j ∈ s, monomialOfFactors (factors j) ≠ monomialOfFactors (factors source) ∧ 0 < order j ∧
      match sign with
      | .minus => tDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa source) (ta source) - A root (qa j) (ta j)
      | .plus => qDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa j) (ta j) - A root (qa source) (ta source) := by
  let P (j : ι) := principalPartPolynomial (firstScreeningVector sign root) (order j) (r j)
  have hPsource : P source ≠ 0 :=
    principalPartPolynomial_simple_ne_zero _ _ horder _ hr
  have hsum : ∑ j ∈ s, (P j : MvPowerSeries (Fin 4) Scalars) *
      MvPowerSeries.killCompl firstModeEmbedding
        ((elementarySymbol D₄ (1 : Fin 4) (factors j)).coefficients charge *
          exponentialSymbol D₄ (fun mode => RatFunc.C
            (screeningModes (g := D₄) sign root mode.2.val mode.1 *
              (q ^ qa j * t ^ ta j) ^ (-mode.2.val)))) = 0 := by
    simp_rw [screened_principal_parts_residue, firstScreeningSeries_spectral] at hlocal
    simpa only [map_mul, P] using hlocal
  obtain ⟨j, hj, hm, hpj, hs⟩ := firstMode_screened_distinct_partner s factors charge sign root
    qa ta P hpairs hsum source hsource hPsource
  refine ⟨j, hj, hm, principalPartPolynomial_nonzero_order _ _ _ hpj, ?_⟩
  cases sign <;> exact hs

/-- When each principal-part order is the actual rational screening
pole order, the partner supplied by cancellation has an actual pole.
The original-operator derivation is supplied by `ScreeningResidueBridge.lean`. -/
theorem local_residue_sum_forces_pole_partner {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (sign : ScreeningSign) (root : Fin 4) (qa ta : ι → ℤ)
    (order : ι → ℕ) (r : (j : ι) → Fin (order j) → Scalars)
    (hpairs : Set.InjOn (fun j => (monomialOfFactors (factors j), (qa j, ta j))) s)
    (horders : ∀ j ∈ s, order j =
      (match sign with
      | .minus => minusPoleOrder (monomialOfFactors (factors j)) root (qa j, ta j)
      | .plus => plusPoleOrder (monomialOfFactors (factors j)) root (qa j, ta j)).toNat)
    (hlocal : (∑ j ∈ s,
      (∑ k : Fin (order j),
        HahnSeries.single (-((k.val : ℤ) + 1)) (MvPowerSeries.C (r j k)) *
          (screenedPoleTaylor (factors j) charge sign root (RatFunc.C (q ^ qa j * t ^ ta j)) :
            LaurentSeries (MvPowerSeries (Fin 4) Scalars))).coeff (-1) :
              MvPowerSeries (Fin 4) Scalars) = 0)
    (source : ι) (hsource : source ∈ s) (horder : order source = 1)
    (hr : r source ⟨0, by omega⟩ ≠ 0) :
    ∃ j ∈ s, monomialOfFactors (factors j) ≠ monomialOfFactors (factors source) ∧
      match sign with
      | .minus =>
          tDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
            A root (qa source) (ta source) - A root (qa j) (ta j) ∧
          minusPoleOrder (monomialOfFactors (factors j)) root (qa j, ta j) ≠ 0
      | .plus =>
          qDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
            A root (qa j) (ta j) - A root (qa source) (ta source) ∧
          plusPoleOrder (monomialOfFactors (factors j)) root (qa j, ta j) ≠ 0 := by
  obtain ⟨j, hj, hm, hpos, hs⟩ := local_residue_sum_forces_distinct_partner s factors charge sign root
    qa ta order r hpairs hlocal source hsource horder hr
  have hp : (match sign with
      | .minus => minusPoleOrder (monomialOfFactors (factors j)) root (qa j, ta j)
      | .plus => plusPoleOrder (monomialOfFactors (factors j)) root (qa j, ta j)) ≠ 0 := by
    intro hz
    have he := horders j hj
    rw [hz, Int.toNat_zero] at he
    exact (Nat.ne_of_gt hpos) he
  refine ⟨j, hj, hm, ?_⟩
  cases sign <;> exact ⟨hs, hp⟩

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
