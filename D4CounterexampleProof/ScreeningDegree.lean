import D4CounterexampleProof.ScreeningPartialFractions
import Mathlib.FieldTheory.RatFunc.Degree

/-! The rational screening factors have degree zero at infinity. This
keeps the polynomial part of their eventual residue expansion controlled. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance screeningDegreeField : Field Coefficient := inferInstance

def rationalDegreeHom : (RatFunc Coefficient)ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (RatFunc.intDegree (u : RatFunc Coefficient))
  map_one' := by simp
  map_mul' u v := by
    change Multiplicative.ofAdd (RatFunc.intDegree ((u : RatFunc Coefficient) * (v : RatFunc Coefficient))) =
      Multiplicative.ofAdd (RatFunc.intDegree (u : RatFunc Coefficient) + RatFunc.intDegree (v : RatFunc Coefficient))
    rw [RatFunc.intDegree_mul (Units.ne_zero u) (Units.ne_zero v)]

theorem rationalDegreeHom_linearFactorUnit (a : Spectral) :
    rationalDegreeHom (linearFactorUnit a) = Multiplicative.ofAdd 1 := by
  change Multiplicative.ofAdd
    (RatFunc.intDegree (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2) : RatFunc Coefficient)) = _
  have he : (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2) : RatFunc Coefficient) =
      algebraMap (Polynomial Coefficient) (RatFunc Coefficient)
        (Polynomial.X - Polynomial.C (q ^ a.1 * t ^ a.2)) := by
    simp only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [he, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_sub_C]
  rfl

theorem screeningFactorUnit_degree_zero (sign : ScreeningSign) (f : Spectral →₀ ℤ) :
    RatFunc.intDegree (screeningFactorUnit sign f : RatFunc Coefficient) = 0 := by
  classical
  have he : rationalDegreeHom (screeningFactorUnit sign f) = 1 := by
    unfold screeningFactorUnit Finsupp.prod
    rw [map_prod]
    apply Finset.prod_eq_one
    intro a ha
    rw [map_zpow]
    cases sign <;>
      simp only [map_div, rationalDegreeHom_linearFactorUnit, div_self', one_zpow]
  exact congrArg Multiplicative.toAdd he

end
end FrenkelReshetikhin.D4CounterexampleProof
