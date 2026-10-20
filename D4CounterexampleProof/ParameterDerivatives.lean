import D4CounterexampleProof.FirstCreationModes
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Derivation

/-! Coefficientwise differentiation in a formal pole parameter. This
prepares the polynomial factors produced by higher-order residues after
retaining the four first creation modes. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open scoped BigOperators

section General

variable {K R σ : Type*} [CommRing K] [CommRing R] [Algebra K R]

def coefficientLinearMap (L : R →ₗ[K] R) : MvPowerSeries σ R →ₗ[K] MvPowerSeries σ R where
  toFun F d := L (F d)
  map_add' F G := by ext d; exact L.map_add _ _
  map_smul' a F := by ext d; exact L.map_smul a (F d)

@[simp] theorem coefficientLinearMap_apply (L : R →ₗ[K] R)
    (F : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (coefficientLinearMap L F) = L (MvPowerSeries.coeff d F) := rfl

def coefficientDerivation (D : Derivation K R R) :
    Derivation K (MvPowerSeries σ R) (MvPowerSeries σ R) where
  __ := coefficientLinearMap D.toLinearMap
  map_one_eq_zero' := by
    classical
    ext d
    simp only [coefficientLinearMap_apply, MvPowerSeries.coeff_one, MvPowerSeries.coeff_zero]
    split_ifs <;> simp
  leibniz' F G := by
    classical
    change coefficientLinearMap D.toLinearMap (F * G) =
      F * coefficientLinearMap D.toLinearMap G + G * coefficientLinearMap D.toLinearMap F
    rw [mul_comm G (coefficientLinearMap D.toLinearMap F)]
    ext d
    simp only [map_add, MvPowerSeries.coeff_mul, coefficientLinearMap_apply]
    rw [map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    change D (MvPowerSeries.coeff p.1 F * MvPowerSeries.coeff p.2 G) =
      MvPowerSeries.coeff p.1 F * D (MvPowerSeries.coeff p.2 G) +
        D (MvPowerSeries.coeff p.1 F) * MvPowerSeries.coeff p.2 G
    simpa only [smul_eq_mul, mul_comm] using
      D.leibniz (MvPowerSeries.coeff p.1 F) (MvPowerSeries.coeff p.2 G)

@[simp] theorem coefficientDerivation_apply (D : Derivation K R R)
    (F : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (coefficientDerivation D F) = D (MvPowerSeries.coeff d F) := rfl

end General

section CoefficientMap

variable {R S σ : Type*} [CommRing R] [CommRing S]

theorem pderiv_map_coefficients (f : R →+* S) (F : MvPowerSeries σ R) (i : σ) :
    MvPowerSeries.pderiv S i (MvPowerSeries.map f F) =
      MvPowerSeries.map f (MvPowerSeries.pderiv R i F) := by
  apply MvPowerSeries.ext
  intro d
  simp only [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map, map_mul,
    map_add, map_natCast, map_one]

end CoefficientMap

section PoleParameter

variable {K σ : Type*} [Field K] [CharZero K]
attribute [local instance] Classical.propDecidable

theorem eigenseries_unique (F G : MvPowerSeries σ K) (v : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (v i) * F)
    (hG : ∀ i, MvPowerSeries.pderiv K i G = MvPowerSeries.C (v i) * G)
    (hF0 : MvPowerSeries.constantCoeff F = 1)
    (hG0 : MvPowerSeries.constantCoeff G = 1) : F = G := by
  have hGnz : MvPowerSeries.constantCoeff G ≠ 0 := by rw [hG0]; exact one_ne_zero
  have hcancel := MvPowerSeries.mul_inv_cancel G hGnz
  have hicancel := MvPowerSeries.inv_mul_cancel G hGnz
  have hratio : F * G⁻¹ = 1 := by
    apply MvPowerSeries.pderiv.ext
    · intro i
      rw [Derivation.leibniz, MvPowerSeries.pderiv_inv', hF, hG, MvPowerSeries.pderiv_one]
      simp only [smul_eq_mul]
      calc
        _ = MvPowerSeries.C (v i) * F * G⁻¹ * (1 - G * G⁻¹) := by ring
        _ = 0 := by rw [hcancel, sub_self, mul_zero]
    · simp [hF0, hG0, MvPowerSeries.constantCoeff_inv]
  have he := congrArg (fun p : MvPowerSeries σ K => p * G) hratio
  simpa only [mul_assoc, hicancel, mul_one, one_mul] using he

/-- Give each creation variable degree one in a separate formal
parameter. This is a proof construction applied to an existing series. -/
def parameterLift (F : MvPowerSeries σ K) : MvPowerSeries σ (Polynomial K) :=
  fun d => Polynomial.C (F d) * Polynomial.X ^ d.sum (fun _ n => n)

def poleDerivative : Derivation K (MvPowerSeries σ (Polynomial K))
    (MvPowerSeries σ (Polynomial K)) := coefficientDerivation Polynomial.derivative'

omit [CharZero K] in
@[simp] theorem parameterLift_constantCoeff (F : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (parameterLift F) = Polynomial.C (MvPowerSeries.constantCoeff F) := by
  change Polynomial.C (F 0) * Polynomial.X ^ (0 : σ →₀ ℕ).sum (fun _ n => n) = _
  simp only [Finsupp.sum_zero_index, pow_zero, mul_one]
  rfl

omit [CharZero K] in
theorem parameterLift_pderiv (F : MvPowerSeries σ K) (v : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (v i) * F) (i : σ) :
    MvPowerSeries.pderiv (Polynomial K) i (parameterLift F) =
      MvPowerSeries.C (Polynomial.C (v i) * Polynomial.X) * parameterLift F := by
  classical
  apply MvPowerSeries.ext
  intro d
  change MvPowerSeries.coeff d (MvPowerSeries.pderiv (Polynomial K) i (parameterLift F)) =
    MvPowerSeries.coeff d (MvPowerSeries.C (Polynomial.C (v i) * Polynomial.X) * parameterLift F)
  have he := congrArg (MvPowerSeries.coeff d) (hF i)
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C_mul] at he
  have htotal : (d + Finsupp.single i 1).sum (fun _ n => n) = d.sum (fun _ n => n) + 1 := by
    rw [Finsupp.sum_add_index' (by simp) (by simp)]
    simp
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C_mul]
  change (Polynomial.C (F (d + Finsupp.single i 1)) *
      Polynomial.X ^ (d + Finsupp.single i 1).sum (fun _ n => n)) * ((d i : Polynomial K) + 1) =
    (Polynomial.C (v i) * Polynomial.X) *
      (Polynomial.C (F d) * Polynomial.X ^ d.sum (fun _ n => n))
  rw [htotal, pow_succ]
  have he' := congrArg Polynomial.C he
  simp only [map_mul, map_add, map_natCast, map_one, MvPowerSeries.coeff_apply] at he'
  calc
    _ = (Polynomial.C (F (d + Finsupp.single i 1)) * ((d i : Polynomial K) + 1)) *
        (Polynomial.X ^ d.sum (fun _ n => n) * Polynomial.X) := by ring
    _ = _ := by rw [he']; ring

end PoleParameter

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
