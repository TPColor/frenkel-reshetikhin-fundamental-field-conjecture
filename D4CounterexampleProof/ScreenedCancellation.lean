import D4CounterexampleProof.CreationFieldIndependence
import D4CounterexampleProof.ScreeningSignatures

/-! From a vanishing sum of actual screened creation series to a distinct
signature-matched pole contribution. Polynomial factors are unrestricted.
The residue expansion that must supply this premise is a separate step. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screenedCancellationField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem root_monomial_parameters_injective (i : Fin 4) :
    Function.Injective (fun ab : Spectral => A i ab.1 ab.2) := by
  classical
  intro ab cd h
  let j : Fin 4 := if i = 1 then 0 else 1
  have hc : deformedCartan D₄ (-1) j i = -1 := by
    rw [d4_deformedCartan_creation]
    change (if j = i then q * t⁻¹ + q⁻¹ * t else
      if adjacent D₄ j.val i.val then (-1 : Coefficient) else 0) = -1
    dsimp only [j]
    fin_cases i <;> norm_num [adjacent, D₄, SimpleLieType.rank]
  have he := congrArg (fun m : Monomial => spectralMoment m j) h
  rw [spectralMoment_A, spectralMoment_A, hc] at he
  apply spectralParameter_injective
  simpa only [mul_neg_one, neg_inj] using he

/-- A zero screened creation sum forces another nonzero contribution
with the exact Laurent signature. The premise is a concrete sum of the
original Y/A and screening exponentials, rather than a signature assumption. -/
theorem screened_restricted_cancelling_partner {ι σ : Type*} (s : Finset ι)
    (e : σ ↪ ModeIndex D₄) (first : Fin 4 → σ)
    (hfirst : ∀ k, e (first k) = (k, ⟨-1, by decide⟩))
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (sign : ScreeningSign) (root : Fin 4) (qa ta : ι → ℤ) (P : ι → MvPolynomial σ Scalars)
    (hsum : ∑ j ∈ s, (P j : MvPowerSeries σ Scalars) *
      MvPowerSeries.killCompl e
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
  classical
  choose c hc using fun j : ι =>
    elementarySymbol_scaled_exponential D₄ (1 : Fin 4) (factors j) charge
  let screen (j : ι) (mode : ModeIndex D₄) : Scalars := RatFunc.C
    (screeningModes (g := D₄) sign root mode.2.val mode.1 * (q ^ qa j * t ^ ta j) ^ (-mode.2.val))
  let a (j : ι) := MvPowerSeries.constantCoeff
    ((elementarySymbol D₄ (1 : Fin 4) (factors j)).coefficients charge)
  let F (j : ι) : SymbolSeries D₄ :=
    (elementarySymbol D₄ (1 : Fin 4) (factors j)).coefficients charge * exponentialSymbol D₄ (screen j)
  have ha (j : ι) : a j ≠ 0 := elementarySymbol_constantCoeff_ne_zero D₄ (1 : Fin 4) (factors j) charge
  have hF (j : ι) : F j = MvPowerSeries.C (a j) * exponentialSymbol D₄ (c j + screen j) := by
    dsimp only [F]
    rw [hc j, ← exponentialSymbol_mul]
    ring
  have hderiv (j : ι) (v : σ) :
      MvPowerSeries.pderiv Scalars v (MvPowerSeries.killCompl e (F j)) =
        MvPowerSeries.C ((c j + screen j) (e v)) *
          MvPowerSeries.killCompl e (F j) := by
    rw [hF j]
    exact scaled_exponential_restricted_pderiv e (a j) (c j + screen j) v
  have hFnz (j : ι) : MvPowerSeries.killCompl e (F j) ≠ 0 := by
    intro hz
    have he := congrArg MvPowerSeries.constantCoeff hz
    rw [constantCoeff_killCompl, hF j, map_mul, MvPowerSeries.constantCoeff_C,
      exponentialSymbol_constantCoeff, mul_one, map_zero] at he
    exact ha j he
  obtain ⟨j, hj, hne, heq, hpj⟩ := eigenseries_cancelling_partner s
    (fun j => MvPowerSeries.killCompl e (F j))
    (fun j v => (c j + screen j) (e v)) hderiv P hsum source hsource hPsource (hFnz source)
  refine ⟨j, hj, hne, hpj, ?_⟩
  have hnorm (j : ι) (k : Fin 4) :
      MvPowerSeries.coeff (Finsupp.single (k, ⟨-1, by decide⟩) 1) (F j) /
        MvPowerSeries.constantCoeff (F j) = (c j + screen j) (k, ⟨-1, by decide⟩) := by
    rw [hF j]
    exact normalized_single_scaled_exponential D₄ (a j) (c j + screen j) _ (ha j)
  have hs := signature_of_screened_normalized_creation (factors source) (factors j)
    charge charge sign root (qa source) (ta source) (qa j) (ta j) (fun k => by
      change MvPowerSeries.coeff (Finsupp.single (k, ⟨-1, by decide⟩) 1) (F source) /
          MvPowerSeries.constantCoeff (F source) =
        MvPowerSeries.coeff (Finsupp.single (k, ⟨-1, by decide⟩) 1) (F j) /
          MvPowerSeries.constantCoeff (F j)
      rw [hnorm source k, hnorm j k]
      have he := congrFun heq (first k)
      rw [hfirst k] at he
      exact he.symm)
  cases sign <;> exact hs

theorem screened_creation_cancelling_partner {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (sign : ScreeningSign) (root : Fin 4) (qa ta : ι → ℤ) (P : ι → Polynomials)
    (hsum : ∑ j ∈ s, (P j : MvPowerSeries Variables Scalars) *
      MvPowerSeries.killCompl creationEmbedding
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
  obtain ⟨j, hj, hne, hpj, hs⟩ := screened_restricted_cancelling_partner s creationEmbedding
    (fun k => (k, ⟨1, by decide⟩)) (fun _ => rfl) factors charge sign root qa ta P hsum
    source hsource hPsource
  refine ⟨j, hj, hne, hpj, ?_⟩
  cases sign <;> exact hs

/-- The same necessity stated on the original Fock vacuum. Each distinct
monomial/pole pair is indexed once. A future OPE/residue theorem must
supply the vanishing screened-field sum from the screening commutator. -/
theorem screened_field_cancelling_partner {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (sign : ScreeningSign) (root : Fin 4) (qa ta : ι → ℤ) (P : ι → Polynomials)
    (hpairs : Function.Injective (fun j => (monomialOfFactors (factors j), (qa j, ta j))))
    (source : ι) (hsource : source ∈ s) (hPsource : P source ≠ 0) :
    let a : NormalSymbol D₄ := ⟨fun inputCharge => ∑ j ∈ s,
      MvPowerSeries.rename creationEmbedding (P j : MvPowerSeries Variables Scalars) *
        ((elementarySymbol D₄ (1 : Fin 4) (factors j)).coefficients inputCharge *
          exponentialSymbol D₄ (fun mode => RatFunc.C
            (screeningModes (g := D₄) sign root mode.2.val mode.1 *
              (q ^ qa j * t ^ ta j) ^ (-mode.2.val)))), 0⟩
    (∀ n : ℤ, evaluateSymbol D₄ a charge n
      (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) = 0) →
    ∃ j ∈ s, monomialOfFactors (factors j) ≠ monomialOfFactors (factors source) ∧ P j ≠ 0 ∧
      match sign with
      | .minus => tDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa source) (ta source) - A root (qa j) (ta j)
      | .plus => qDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa j) (ta j) - A root (qa source) (ta source) := by
  dsimp only
  intro h
  have hz := creationSymbol_zero_of_vacuum_coefficients _ charge h
  have hsum : ∑ j ∈ s, (P j : MvPowerSeries Variables Scalars) *
      MvPowerSeries.killCompl creationEmbedding
        ((elementarySymbol D₄ (1 : Fin 4) (factors j)).coefficients charge *
          exponentialSymbol D₄ (fun mode => RatFunc.C
            (screeningModes (g := D₄) sign root mode.2.val mode.1 *
              (q ^ qa j * t ^ ta j) ^ (-mode.2.val)))) = 0 := by
    simpa only [map_sum, map_mul, MvPowerSeries.killCompl_rename_app] using hz
  obtain ⟨j, hj, hne, hpj, hsig⟩ := screened_creation_cancelling_partner s factors charge sign root
    qa ta P hsum source hsource hPsource
  have hmono : monomialOfFactors (factors j) ≠ monomialOfFactors (factors source) := by
    intro hm
    have hpole : (qa j, ta j) = (qa source, ta source) := by
      cases sign with
      | minus =>
        change tDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa source) (ta source) - A root (qa j) (ta j) at hsig
        rw [hm, sub_self] at hsig
        have hzero : tDifference (0 : Monomial) = 0 := by simp [tDifference, shift]
        rw [hzero] at hsig
        have hA : A root (qa source) (ta source) = A root (qa j) (ta j) := sub_eq_zero.mp hsig.symm
        exact (@root_monomial_parameters_injective root (qa source, ta source) (qa j, ta j) hA).symm
      | plus =>
        change qDifference (monomialOfFactors (factors j) - monomialOfFactors (factors source)) =
          A root (qa j) (ta j) - A root (qa source) (ta source) at hsig
        rw [hm, sub_self] at hsig
        have hzero : qDifference (0 : Monomial) = 0 := by simp [qDifference, shift]
        rw [hzero] at hsig
        have hA : A root (qa j) (ta j) = A root (qa source) (ta source) := sub_eq_zero.mp hsig.symm
        exact @root_monomial_parameters_injective root (qa j, ta j) (qa source, ta source) hA
    have hpair : (monomialOfFactors (factors j), (qa j, ta j)) =
        (monomialOfFactors (factors source), (qa source, ta source)) := Prod.ext hm hpole
    exact hne (hpairs hpair)
  refine ⟨j, hj, hmono, hpj, ?_⟩
  cases sign <;> exact hsig

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
