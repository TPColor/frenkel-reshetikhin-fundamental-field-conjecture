import D4CounterexampleProof.FrequencyMoments
import D4CounterexampleProof.FrequencySubstitution
import D4CounterexampleProof.ContractionProducts
import D4CounterexampleProof.ScreeningDivisors

/-! The scalar screening logarithm associated to the complete elementary
Laurent monomial. Its coefficients are proved equal to the original
oscillator contractions at every positive frequency. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screeningLogarithmsField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

@[simp] theorem rootExponents_zero (i : Fin 4) : rootExponents 0 i = 0 := by
  ext a
  rfl

theorem rootExponents_add (m l : Monomial) (i : Fin 4) :
    rootExponents (m + l) i = rootExponents m i + rootExponents l i := by
  ext a
  rfl

theorem rootExponents_single (j i : Fin 4) (a : Spectral) (k : ℤ) :
    rootExponents (Finsupp.single (j, a) k) i =
      if i = j then Finsupp.single a k else 0 := by
  by_cases hij : i = j
  · subst j
    ext b
    simp [rootExponents_apply, Finsupp.single_apply]
  · rw [if_neg hij]
    ext b
    simp [rootExponents_apply, hij]

theorem frequencyMoment_rootExponents (m : Monomial) (i : Fin 4) (n : ℤ) :
    frequencyMoment m i n =
      (rootExponents m i).sum fun a k => (k : Coefficient) * (q ^ a.1 * t ^ a.2) ^ n := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m l hm hl =>
    rw [frequencyMoment_add, rootExponents_add, hm, hl]
    symm
    apply Finsupp.sum_add_index'
    · intro a; simp
    · intro a k l; simp [add_mul]
  | single key k =>
    rcases key with ⟨j, a⟩
    rw [rootExponents_single]
    by_cases hij : i = j
    · subst j
      simp [frequencyMoment]
    · simp [frequencyMoment, hij, Ne.symm hij]

def screeningPoleParameter (sign : ScreeningSign) (a : Spectral) : Coefficient :=
  match sign with
  | .minus => q⁻¹ * (q ^ a.1 * t ^ a.2)
  | .plus => t * (q ^ a.1 * t ^ a.2)

def screeningZeroParameter (sign : ScreeningSign) (a : Spectral) : Coefficient :=
  match sign with
  | .minus => q * (q ^ a.1 * t ^ a.2)
  | .plus => t⁻¹ * (q ^ a.1 * t ^ a.2)

def screeningScalarLog (sign : ScreeningSign) (m : Monomial) (i : Fin 4) :
    PowerSeries Coefficient :=
  (rootExponents m i).sum fun a k =>
    k • contractionLog (screeningPoleParameter sign a) (screeningZeroParameter sign a)

theorem screeningScalarLog_constantCoeff (sign : ScreeningSign) (m : Monomial) (i : Fin 4) :
    PowerSeries.constantCoeff (screeningScalarLog sign m i) = 0 := by
  classical
  simp [screeningScalarLog, Finsupp.sum, map_sum, contractionLog_constantCoeff]

/-- The coefficient of the rational screening logarithm is precisely
the scalar mode factor times the all-frequency Laurent moment. -/
theorem screeningScalarLog_coeff (sign : ScreeningSign) (m : Monomial) (i : Fin 4)
    (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n (screeningScalarLog sign m i) =
      (match sign with
      | .minus => -(q ^ (n : ℤ) - q ^ (-(n : ℤ))) / (n : Coefficient)
      | .plus => (t ^ (n : ℤ) - t ^ (-(n : ℤ))) / (n : Coefficient)) *
        frequencyMoment m i (n : ℤ) := by
  rw [screeningScalarLog, frequencyMoment_rootExponents]
  simp only [Finsupp.sum, map_sum, map_zsmul, contractionLog, PowerSeries.coeff_mk,
    if_neg (ne_of_gt hn), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  cases sign <;>
    simp only [screeningPoleParameter, screeningZeroParameter, zsmul_eq_mul, mul_pow, inv_pow,
      zpow_natCast, zpow_neg, zpow_natCast] <;> ring

/-- Exponentiating the logarithm gives all rational contraction factors,
with exactly the signed exponents of the original Laurent monomial. -/
theorem screeningScalarLog_exp_product (sign : ScreeningSign) (m : Monomial) (i : Fin 4) :
    (PowerSeries.exp Coefficient).subst (screeningScalarLog sign m i) =
      ((rootExponents m i).prod fun a k =>
        (oneSubSeriesUnit (screeningZeroParameter sign a) /
          oneSubSeriesUnit (screeningPoleParameter sign a)) ^ k :
            (PowerSeries Coefficient)ˣ) :=
  exp_subst_contraction_product _ _ _

end
end FrenkelReshetikhin.D4CounterexampleProof
