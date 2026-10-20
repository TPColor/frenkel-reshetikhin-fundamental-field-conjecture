import D4CounterexampleProof.ScreeningResidueBridge
import D4CounterexampleProof.LocalResiduePartners
import D4CounterexampleProof.NonzeroPrincipalParts

/-! Actual screening centralizer membership forces pole partners for
finite expansions with distinct elementary monomial labels. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screeningPoleNecessityField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem finite_expansion_pole_partner {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (c : ι → Coefficient)
    (hinj : Set.InjOn (fun j => monomialOfFactors (factors j)) s)
    (hW : (∑ j ∈ s, RatFunc.C (c j) •
      evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) (factors j))) ∈ deformedW D₄)
    (sign : ScreeningSign) (i : Fin 4) (source : ι) (hsource : source ∈ s)
    (hc : c source ≠ 0) (a : Spectral)
    (hpole : screeningDivisor sign (rootExponents (monomialOfFactors (factors source)) i) a = -1) :
    ∃ j ∈ s, monomialOfFactors (factors j) ≠ monomialOfFactors (factors source) ∧
      ∃ b : Spectral, screeningDivisor sign (rootExponents (monomialOfFactors (factors j)) i) b < 0 ∧
      match sign with
      | .minus => tDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A i a.1 a.2 - A i b.1 b.2
      | .plus => qDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A i b.1 b.2 - A i a.1 a.2 := by
  classical
  let div (j : ι) := screeningDivisor sign (rootExponents (monomialOfFactors (factors j)) i)
  let order (j : ι) (b : Spectral) := (-div j b).toNat
  have hex (j : ι) := screeningFactor_partial_fractions_nonzero_simple sign
    (monomialOfFactors (factors j)) i
  choose Q r hdecomp hsimple using hex
  let parts := s.sigma (fun j => (div j).support)
  let P (ja : (_ : ι) × Spectral) : MvPolynomial (Fin 4) Scalars :=
    MvPolynomial.C (RatFunc.C (c ja.1)) *
      principalPartPolynomial (firstScreeningVector sign i) (order ja.1 ja.2)
        (fun k => RatFunc.C (r ja.1 ja.2 k))
  have hparts : Set.InjOn
      (fun ja : (_ : ι) × Spectral => (monomialOfFactors (factors ja.1), (ja.2.1, ja.2.2))) parts := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_sigma.mp hx).1
    have hy' := (Finset.mem_sigma.mp hy).1
    have hfst := hinj hx' hy' (congrArg Prod.fst hxy)
    have hsnd := congrArg Prod.snd hxy
    exact Sigma.ext hfst (heq_of_eq hsnd)
  have hsum : ∑ ja ∈ parts, (P ja : MvPowerSeries (Fin 4) Scalars) *
      MvPowerSeries.killCompl firstModeEmbedding
        ((elementarySymbol D₄ (1 : Fin 4) (factors ja.1)).coefficients none *
          exponentialSymbol D₄ (fun mode => RatFunc.C
            (screeningModes (g := D₄) sign i mode.2.val mode.1 *
              (q ^ ja.2.1 * t ^ ja.2.2) ^ (-mode.2.val)))) = 0 := by
    have hz := screenedVacuumProjection_deformedW _ hW sign i
    rw [map_sum] at hz
    simp only [map_smul] at hz
    have hj (j : ι) := screenedVacuumProjection_principal_parts sign i (factors j)
      (Q j) (div j).support (order j) (r j) (hdecomp j)
    simp_rw [hj] at hz
    simp only [Finset.smul_sum] at hz
    dsimp only [parts]
    rw [Finset.sum_sigma]
    convert hz using 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [P]
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_C, map_mul,
      ← firstScreeningSeries_spectral sign i b.1 b.2, MvPowerSeries.smul_eq_C_mul]
    ring
  have hasource : (⟨source, a⟩ : (_ : ι) × Spectral) ∈ parts := by
    apply Finset.mem_sigma.mpr
    refine ⟨hsource, Finsupp.mem_support_iff.mpr ?_⟩
    change div source a ≠ 0
    change div source a = -1 at hpole
    rw [hpole]
    decide
  have horder : order source a = 1 := by
    change (-screeningDivisor sign (rootExponents (monomialOfFactors (factors source)) i) a).toNat = 1
    rw [hpole]
    decide
  have hPsource : P ⟨source, a⟩ ≠ 0 := by
    apply mul_ne_zero
    · exact MvPolynomial.C_ne_zero.mpr ((map_ne_zero RatFunc.C).mpr hc)
    · apply principalPartPolynomial_simple_ne_zero _ _ horder
      exact (map_ne_zero RatFunc.C).mpr (hsimple source a hpole)
  obtain ⟨ja, hja, hm, hpj, hs⟩ := firstMode_screened_distinct_partner parts
    (fun ja => factors ja.1) none sign i (fun ja => ja.2.1) (fun ja => ja.2.2)
      P hparts hsum ⟨source, a⟩ hasource hPsource
  refine ⟨ja.1, (Finset.mem_sigma.mp hja).1, hm, ja.2, ?_, ?_⟩
  · have hpp : principalPartPolynomial (firstScreeningVector sign i) (order ja.1 ja.2)
        (fun k => RatFunc.C (r ja.1 ja.2 k)) ≠ 0 := by
      intro hz
      exact hpj (by dsimp only [P]; rw [hz, mul_zero])
    have ho := principalPartPolynomial_nonzero_order _ _ _ hpp
    change 0 < (-screeningDivisor sign (rootExponents (monomialOfFactors (factors ja.1)) i) ja.2).toNat at ho
    omega
  · cases sign <;> exact hs

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
