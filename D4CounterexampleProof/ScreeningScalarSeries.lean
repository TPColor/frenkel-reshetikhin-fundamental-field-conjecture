import D4CounterexampleProof.ScreeningLogarithms

/-! Equality of the scalar series obtained from the original screening
exponential and the rational-factor logarithm for the complete elementary
monomial. This addresses the scalar part of the normal-ordering bridge;
the final residue reindexing is separate. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screeningScalarSeriesField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def elementaryContractionFamily (factors : List (InverseRootFactor D₄))
    (mode : ModeIndex D₄) : Scalars :=
  if hn : 0 < mode.2.val then
    elementaryPositiveContraction factors mode.1 mode.2.val hn else 0

theorem elementaryContractionFamily_positive (factors : List (InverseRootFactor D₄))
    (n : ℕ) (hn : 0 < n) (j : RootIndex D₄) :
    elementaryContractionFamily factors (positiveFrequencyEmbedding D₄ n hn j) =
      elementaryPositiveContraction factors j (n : ℤ) (by exact_mod_cast hn) := by
  unfold elementaryContractionFamily
  rw [dif_pos (by change 0 < (n : ℤ); exact_mod_cast hn)]
  rfl

/-- Every coefficient of the substituted original screening logarithm
agrees with the logarithm of the full rational Laurent factor product. -/
theorem screening_positiveFrequencyLog (sign : ScreeningSign)
    (factors : List (InverseRootFactor D₄)) (i : RootIndex D₄) :
    positiveFrequencyLog D₄
        (fun mode => RatFunc.C (screeningModes sign i mode.2.val mode.1))
        (elementaryContractionFamily factors) =
      (screeningScalarLog sign (monomialOfFactors factors) i).map RatFunc.C := by
  apply PowerSeries.ext
  intro n
  rw [positiveFrequencyLog, PowerSeries.coeff_mk, PowerSeries.coeff_map]
  by_cases hn : 0 < n
  · rw [dif_pos hn, screeningScalarLog_coeff sign _ i n hn]
    calc
      _ = RatFunc.C (screeningModes (g := D₄) sign i (n : ℤ) i) *
          elementaryPositiveContraction factors i (n : ℤ) (by exact_mod_cast hn) := by
        rw [Finset.sum_eq_single i]
        · rw [elementaryContractionFamily_positive]
          rfl
        · intro j hj hji
          have hz : screeningModes (g := D₄) sign i (n : ℤ) j = 0 := by
            simp [screeningModes, hji]
          change RatFunc.C (screeningModes (g := D₄) sign i (n : ℤ) j) * _ = 0
          rw [hz, map_zero, zero_mul]
        · simp
      _ = _ := screening_elementary_contraction_moment sign factors i (n : ℤ)
        (by exact_mod_cast hn)
  · have hn0 : n = 0 := by omega
    subst n
    rw [dif_neg (by omega), PowerSeries.coeff_zero_eq_constantCoeff_apply,
      screeningScalarLog_constantCoeff sign (monomialOfFactors factors) i, map_zero]

/-- The original screening exponential, evaluated at its actual positive
oscillator eigenvalues with their frequencies, gives the exponential of
the rational screening logarithm. All substitutions are locally finite. -/
theorem original_screening_scalar_series (sign : ScreeningSign)
    (factors : List (InverseRootFactor D₄)) (i : RootIndex D₄) :
    (exponentialSymbol D₄
        (fun mode => RatFunc.C (screeningModes sign i mode.2.val mode.1))).subst
        (positiveFrequencyFamily D₄ (elementaryContractionFamily factors)) =
      ((PowerSeries.exp Coefficient).subst
        (screeningScalarLog sign (monomialOfFactors factors) i)).map RatFunc.C := by
  rw [exponentialSymbol_positiveFrequency, screening_positiveFrequencyLog,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero'
      (screeningScalarLog_constantCoeff sign _ i)), PowerSeries.map_exp]
  rfl

/-- Exact finite rational factor product for the scalar contraction of
the original exponential with a full elementary field. -/
theorem original_screening_scalar_product (sign : ScreeningSign)
    (factors : List (InverseRootFactor D₄)) (i : RootIndex D₄) :
    (exponentialSymbol D₄
        (fun mode => RatFunc.C (screeningModes sign i mode.2.val mode.1))).subst
        (positiveFrequencyFamily D₄ (elementaryContractionFamily factors)) =
      (((rootExponents (monomialOfFactors factors) i).prod fun a k =>
        (oneSubSeriesUnit (screeningZeroParameter sign a) /
          oneSubSeriesUnit (screeningPoleParameter sign a)) ^ k :
            (PowerSeries Coefficient)ˣ) : PowerSeries Coefficient).map RatFunc.C := by
  exact (original_screening_scalar_series sign factors i).trans
    (congrArg (fun F : PowerSeries Coefficient => F.map RatFunc.C)
      (screeningScalarLog_exp_product sign (monomialOfFactors factors) i))

/-- Each coefficient of the complete scalar contraction is a genuinely
finite sum of original screening coefficients and oscillator eigenvalues. -/
theorem screening_scalar_coefficient_partitions (sign : ScreeningSign)
    (factors : List (InverseRootFactor D₄)) (i : RootIndex D₄) (n : ℕ) :
    RatFunc.C (PowerSeries.coeff n ((PowerSeries.exp Coefficient).subst
      (screeningScalarLog sign (monomialOfFactors factors) i))) =
      ∑ d ∈ (finite_positive_frequency_partitions D₄ n).toFinset,
        (d.prod fun mode k =>
          RatFunc.C (screeningModes sign i mode.2.val mode.1) ^ k / (k.factorial : Scalars)) *
          (d.prod fun mode k => elementaryContractionFamily factors mode ^ k) := by
  calc
    _ = PowerSeries.coeff n ((exponentialSymbol D₄
        (fun mode => RatFunc.C (screeningModes sign i mode.2.val mode.1))).subst
          (positiveFrequencyFamily D₄ (elementaryContractionFamily factors))) := by
      have h := congrArg (PowerSeries.coeff n) (original_screening_scalar_series sign factors i)
      simpa only [PowerSeries.coeff, MvPowerSeries.coeff_map] using h.symm
    _ = _ := exponentialSymbol_positiveFrequency_coeff_finite D₄ _ _ n

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
