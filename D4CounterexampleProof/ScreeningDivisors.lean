import D4CounterexampleProof.PoleOrders
import D4CounterexampleProof.RationalResidues

/-! Divisors of the rational screening factors in the original q,t
setting. Signed Laurent exponents include both zeros and poles. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance screeningDivisorsField : Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def rootExponents (m : Monomial) (i : Fin 4) : Spectral →₀ ℤ :=
  Finsupp.comapDomain (fun a => (i, a)) m (by
    intro a _ b _ h
    exact congrArg Prod.snd h)

@[simp] theorem rootExponents_apply (m : Monomial) (i : Fin 4) (a : Spectral) :
    rootExponents m i a = m (i, a) := rfl

def shiftExponents (δ : Spectral) (f : Spectral →₀ ℤ) : Spectral →₀ ℤ :=
  Finsupp.mapDomain (Equiv.addRight δ) f

@[simp] theorem shiftExponents_apply (δ : Spectral) (f : Spectral →₀ ℤ) (a : Spectral) :
    shiftExponents δ f a = f (a - δ) := by
  exact Finsupp.mapDomain_equiv_apply f a

def screeningDivisor (sign : ScreeningSign) (f : Spectral →₀ ℤ) : Spectral →₀ ℤ :=
  match sign with
  | .minus => shiftExponents (1, 0) f - shiftExponents (-1, 0) f
  | .plus => shiftExponents (0, -1) f - shiftExponents (0, 1) f

/-- The combinatorial pole orders already used by the finite proof are
exactly the negatives of the rational screening divisors. -/
theorem screeningDivisor_minus (m : Monomial) (i : Fin 4) (a : Spectral) :
    screeningDivisor .minus (rootExponents m i) a = -minusPoleOrder m i a := by
  simp only [screeningDivisor, Finsupp.sub_apply, shiftExponents_apply, rootExponents_apply,
    minusPoleOrder, Prod.sub_def]
  simp

theorem screeningDivisor_plus (m : Monomial) (i : Fin 4) (a : Spectral) :
    screeningDivisor .plus (rootExponents m i) a = -plusPoleOrder m i a := by
  simp only [screeningDivisor, Finsupp.sub_apply, shiftExponents_apply, rootExponents_apply,
    plusPoleOrder, Prod.sub_def]
  simp

def linearFactorUnit (a : Spectral) : (RatFunc Coefficient)ˣ :=
  Units.mk0 (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) (ratFunc_X_sub_C_ne_zero _)

def divisorUnit (f : Spectral →₀ ℤ) : (RatFunc Coefficient)ˣ :=
  f.prod fun a n => linearFactorUnit a ^ n

@[simp] theorem divisorUnit_zero : divisorUnit 0 = 1 := by simp [divisorUnit]

theorem divisorUnit_add (f g : Spectral →₀ ℤ) :
    divisorUnit (f + g) = divisorUnit f * divisorUnit g := by
  exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

theorem divisorUnit_sub (f g : Spectral →₀ ℤ) :
    divisorUnit (f - g) = divisorUnit f / divisorUnit g := by
  calc
    _ = (divisorUnit (f - g) * divisorUnit g) / divisorUnit g := by simp
    _ = _ := by rw [← divisorUnit_add, sub_add_cancel]

def screeningFactorUnit (sign : ScreeningSign) (f : Spectral →₀ ℤ) : (RatFunc Coefficient)ˣ :=
  f.prod fun a n => (match sign with
    | .minus => linearFactorUnit (a + (1, 0)) / linearFactorUnit (a + (-1, 0))
    | .plus => linearFactorUnit (a + (0, -1)) / linearFactorUnit (a + (0, 1))) ^ n

theorem screeningFactorUnit_add (sign : ScreeningSign) (f g : Spectral →₀ ℤ) :
    screeningFactorUnit sign (f + g) = screeningFactorUnit sign f * screeningFactorUnit sign g := by
  exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

theorem screeningDivisor_add (sign : ScreeningSign) (f g : Spectral →₀ ℤ) :
    screeningDivisor sign (f + g) = screeningDivisor sign f + screeningDivisor sign g := by
  cases sign <;> simp only [screeningDivisor, shiftExponents, Finsupp.mapDomain_add] <;> abel

/-- The full rational factor product has the displayed divisor, with
all inverse Y factors and coinciding zeros/poles included. -/
theorem screeningFactorUnit_eq_divisor (sign : ScreeningSign) (f : Spectral →₀ ℤ) :
    screeningFactorUnit sign f = divisorUnit (screeningDivisor sign f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => cases sign <;> simp [screeningFactorUnit, screeningDivisor, shiftExponents, divisorUnit]
  | add f g hf hg => rw [screeningFactorUnit_add, screeningDivisor_add, divisorUnit_add, hf, hg]
  | single a n =>
    cases sign <;>
      simp only [screeningFactorUnit, screeningDivisor, shiftExponents, Finsupp.mapDomain_single]
    all_goals
      rw [divisorUnit_sub]
      simp [divisorUnit, div_zpow]

end
end FrenkelReshetikhin.D4CounterexampleProof
