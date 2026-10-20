import D4CounterexampleProof.NormalWordContractions
import D4CounterexampleProof.ScreeningScalarSeries
import D4CounterexampleProof.ElementaryLabels

/-! Finite weighted positive-mode sums expressed through the actual
annihilation words used in the original normally ordered action. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance annihilationPartitionsField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem positiveModeScalar_absolute (factors : List (InverseRootFactor D₄))
    (mode : ModeIndex D₄) (hp : 0 < mode.2.val) :
    positiveModeScalar factors (absoluteMode D₄ mode) = elementaryContractionFamily factors mode := by
  unfold positiveModeScalar elementaryContractionFamily
  rw [dif_pos hp]
  change elementaryPositiveContraction factors mode.1 (mode.2.val.natAbs : ℤ) _ =
    elementaryPositiveContraction factors mode.1 mode.2.val hp
  congr 1
  exact (Int.natCast_natAbs mode.2.val).trans (abs_of_pos hp)

/-- The scalar contractions of the actual repeated annihilation word
are exactly the modewise powers used in the weighted partition formula. -/
theorem annihilationList_scalar_positive (factors : List (InverseRootFactor D₄))
    (d : ModeMonomial D₄) (hp : ∀ mode ∈ d.support, 0 < mode.2.val) :
    ((annihilationList D₄ d).map (positiveModeScalar factors)).prod =
      d.prod (fun mode k => elementaryContractionFamily factors mode ^ k) := by
  classical
  have hprod (xs : List (ModeIndex D₄)) :
      ((xs.flatMap fun mode => List.replicate (d mode) (absoluteMode D₄ mode)).map
        (positiveModeScalar factors)).prod =
      (xs.map fun mode => positiveModeScalar factors (absoluteMode D₄ mode) ^ d mode).prod := by
    induction xs with
    | nil => simp
    | cons mode xs ih => simp [ih]
  have hfilter : (d.support.toList.filter fun mode => 0 < mode.2.val) = d.support.toList := by
    apply List.filter_eq_self.mpr
    intro mode hm
    simpa using hp mode (by simpa using hm)
  rw [annihilationList, hfilter, hprod, Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro mode hm
  rw [positiveModeScalar_absolute factors mode (hp mode hm)]

/-- The complete scalar rational contraction coefficient equals the
finite sum of original screening factorial coefficients multiplied by
the contractions of the actual annihilation words. -/
theorem screening_scalar_coefficient_annihilationWords (sign : ScreeningSign)
    (factors : List (InverseRootFactor D₄)) (i : RootIndex D₄) (n : ℕ) :
    RatFunc.C (PowerSeries.coeff n ((PowerSeries.exp Coefficient).subst
      (screeningScalarLog sign (monomialOfFactors factors) i))) =
      ∑ d ∈ (finite_positive_frequency_partitions D₄ n).toFinset,
        (d.prod fun mode k =>
          RatFunc.C (screeningModes sign i mode.2.val mode.1) ^ k / (k.factorial : Scalars)) *
          ((annihilationList D₄ d).map (positiveModeScalar factors)).prod := by
  rw [screening_scalar_coefficient_partitions]
  apply Finset.sum_congr rfl
  intro d hd
  have hp := ((finite_positive_frequency_partitions D₄ n).mem_toFinset.mp hd).1
  rw [annihilationList_scalar_positive factors d hp]

/-- The original elementary Fourier state has the explicit annihilation
energy bound supplied by its Fourier degree. -/
theorem elementary_fourier_annihilationBound (factors : List (InverseRootFactor D₄))
    (charge : Charge D₄) (m : ℤ) (N : ℕ) (hm : m ≤ (N : ℤ)) :
    AnnihilationBound D₄
      (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) charge m
        (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge))) N := by
  intro xs hxs
  rw [positiveWord_elementary_fourier]
  have henergy : (N : ℤ) < (positiveEnergy D₄ xs : ℤ) := by exact_mod_cast hxs
  have hz := evaluateSymbol_vacuum_lower_truncation D₄
    (elementarySymbol D₄ (1 : Fin 4) factors) charge (m - positiveEnergy D₄ xs)
    (by have ho := elementarySymbol_offset_zero D₄ (1 : Fin 4) factors; omega)
  rw [hz]
  exact smul_zero (A := State D₄ charge) ((xs.map (positiveModeScalar factors)).prod : Scalars)

/-- An explicit finite bound for the complete original screening sum on
an elementary Fourier state of nonnegative index m: only normal words of
absolute oscillator degree at most 2m can contribute. -/
theorem screening_elementary_fourier_bounded_sum (sign : ScreeningSign) (i : RootIndex D₄)
    (factors : List (InverseRootFactor D₄)) (m : ℕ) :
    vacuumMap (chargeEigenvalues D₄ (some (sign, i)))
      (screeningOperator D₄ sign i
        (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) none (m : ℤ)
          (vacuum D₄ Scalars Q T 0))) =
      ∑ d ∈ (finite_absolute_monomials_bounded D₄ (2 * m)).toFinset,
        if monomialDegree D₄ d = -1 then
          ((d.prod fun mode k =>
              RatFunc.C (screeningModes sign i mode.2.val mode.1) ^ k / (k.factorial : Scalars)) *
            ((annihilationList D₄ d).map (positiveModeScalar factors)).prod) •
            (negativePolynomial d *
              vacuumMap 0
                (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) none
                  ((m : ℤ) - positiveDegree D₄ d) (vacuum D₄ Scalars Q T 0))) else 0 := by
  classical
  let : TopologicalSpace Polynomials := ⊥
  rw [screening_elementary_fourier_sum]
  apply tsum_eq_sum
  intro d hd
  by_cases hdeg : monomialDegree D₄ d = -1
  · rw [if_pos hdeg]
    have hlarge : 2 * m < absoluteDegree D₄ d := by
      have hnot : ¬absoluteDegree D₄ d ≤ 2 * m := by
        intro hle
        exact hd ((finite_absolute_monomials_bounded D₄ (2 * m)).mem_toFinset.mpr hle)
      omega
    have hid := absoluteDegree_identity D₄ d
    have hlarge' : (2 * m : ℕ) < absoluteDegree D₄ d := hlarge
    have hp : (m : ℤ) - (positiveDegree D₄ d : ℤ) < 0 := by
      have hcast : ((2 * m : ℕ) : ℤ) < (absoluteDegree D₄ d : ℤ) := by exact_mod_cast hlarge'
      rw [hdeg] at hid
      omega
    have hz := evaluateSymbol_vacuum_lower_truncation D₄
      (elementarySymbol D₄ (1 : Fin 4) factors) none ((m : ℤ) - positiveDegree D₄ d)
      (by have ho := elementarySymbol_offset_zero D₄ (1 : Fin 4) factors; omega)
    change evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) none
      ((m : ℤ) - positiveDegree D₄ d) (vacuum D₄ Scalars Q T 0) = 0 at hz
    change _ • (negativePolynomial d * vacuumMap 0
      (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) none
        ((m : ℤ) - positiveDegree D₄ d) (vacuum D₄ Scalars Q T 0))) = 0
    rw [hz]
    change (_ : Scalars) • (negativePolynomial d *
      vacuumMap 0 (0 : FockModule D₄ Scalars Q T 0)) = 0
    rw [map_zero, mul_zero, smul_zero]
  · rw [if_neg hdeg]

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
