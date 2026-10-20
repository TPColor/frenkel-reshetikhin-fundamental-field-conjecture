import D4CounterexampleProof.ScreeningPartialFractions
import D4CounterexampleProof.PrincipalPartCoefficients
import D4CounterexampleProof.DivisorPoles

/-! Partial-fraction data for the rational screening product, including
proved nonvanishing at every simple pole. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance nonzeroPrincipalPartsField : Field Coefficient := inferInstance

theorem divisorUnit_partial_fractions_nonzero_simple (f : Spectral →₀ ℤ) :
    ∃ (Q : Polynomial Coefficient) (r : (a : Spectral) → Fin (-f a).toNat → Coefficient),
      (divisorUnit f : RatFunc Coefficient) =
        algebraMap (Polynomial Coefficient) (RatFunc Coefficient) Q +
          ∑ a ∈ f.support, ∑ j : Fin (-f a).toNat, RatFunc.C (r a j) /
            (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1) ∧
      ∀ (c : Spectral) (hc : f c = -1), r c ⟨0, by simp [hc]⟩ ≠ 0 := by
  classical
  obtain ⟨Q, r, he⟩ := divisorUnit_partial_fractions f
  refine ⟨Q, r, he, ?_⟩
  intro c hc
  have hsource : c ∈ f.support := Finsupp.mem_support_iff.mpr (by rw [hc]; decide)
  have horder : (-f c).toNat = 1 := by simp [hc]
  have hpole := divisorUnit_denominator_vanishes f c 1 (by decide) (by simpa using hc)
  exact simple_principal_coefficient_ne_zero (divisorUnit f : RatFunc Coefficient) Q f.support
    (fun a => q ^ a.1 * t ^ a.2) spectralParameter_injective.injOn
    (fun a => (-f a).toNat) r he c hsource horder hpole

theorem screeningFactor_partial_fractions_nonzero_simple
    (sign : ScreeningSign) (m : Monomial) (i : Fin 4) :
    let f := screeningDivisor sign (rootExponents m i)
    ∃ (Q : Polynomial Coefficient) (r : (a : Spectral) → Fin (-f a).toNat → Coefficient),
      (screeningFactorUnit sign (rootExponents m i) : RatFunc Coefficient) =
        algebraMap (Polynomial Coefficient) (RatFunc Coefficient) Q +
          ∑ a ∈ f.support, ∑ j : Fin (-f a).toNat, RatFunc.C (r a j) /
            (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1) ∧
      ∀ (c : Spectral) (hc : f c = -1), r c ⟨0, by simp [hc]⟩ ≠ 0 := by
  dsimp only
  rw [screeningFactorUnit_eq_divisor]
  exact divisorUnit_partial_fractions_nonzero_simple _

end
end FrenkelReshetikhin.D4CounterexampleProof
