import D4CounterexampleProof.CreationConvolution
import D4CounterexampleProof.ExpansionAtInfinity
import D4CounterexampleProof.ScreenedLocalResidues

/-! The screening action of an original elementary field is the finite
sum of its genuine local Laurent residues, including higher-order poles. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screeningResidueBridgeField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem polynomial_coe_sum {ι σ R : Type*} [CommSemiring R]
    (s : Finset ι) (f : ι → MvPolynomial σ R) :
    ((∑ x ∈ s, f x : MvPolynomial σ R) : MvPowerSeries σ R) =
      ∑ x ∈ s, (f x : MvPowerSeries σ R) :=
  map_sum MvPolynomial.coeToMvPowerSeries.ringHom f s

theorem residueTransform_grouped_principal_parts {ι : Type*} (s : Finset ι)
    (sign : ScreeningSign) (i : Fin 4) (a : Scalars) (c : ι → Scalars)
    (order : ι → ℕ) (r : (b : ι) → Fin (order b) → Scalars) :
    (residueTransform (PowerSeries.C a + ∑ b ∈ s, ∑ j : Fin (order b), r b j •
      (PowerSeries.X ^ (j.val + 1) *
        PowerSeries.rescale (c b) (PowerSeries.invOneSubPow Scalars (j.val + 1)).val))).subst
          (creationLinearForm (firstScreeningVector sign i) : MvPowerSeries (Fin 4) Scalars) =
      ∑ b ∈ s,
        (principalPartPolynomial (firstScreeningVector sign i) (order b) (r b) :
          MvPowerSeries (Fin 4) Scalars) * firstScreeningSeries sign i (c b) := by
  let L : MvPowerSeries (Fin 4) Scalars := creationLinearForm (firstScreeningVector sign i)
  have hL0 : MvPowerSeries.constantCoeff L = 0 := by simp [L, creationLinearForm_coe]
  have hL := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  rw [← PowerSeries.coe_substAlgHom (R := Scalars) hL]
  rw [map_add, residueTransform_C, zero_add]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [principalPartPolynomial, polynomial_coe_sum, MvPolynomial.coe_mul,
    MvPolynomial.coe_C, MvPolynomial.coe_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [PowerSeries.coe_substAlgHom (R := Scalars) hL]
  change r b j • ((residueTransform
    (PowerSeries.X ^ (j.val + 1) *
      PowerSeries.rescale (c b) (PowerSeries.invOneSubPow Scalars (j.val + 1)).val)).subst
        (creationLinearForm (firstScreeningVector sign i) : MvPowerSeries (Fin 4) Scalars)) = _
  rw [residueTransform_higher_pole_firstMode,
    MvPowerSeries.smul_eq_C_mul, div_eq_mul_inv, map_mul]
  ring

theorem screenedVacuumProjection_principal_parts (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄))
    (Q : Polynomial Coefficient) (s : Finset Spectral) (order : Spectral → ℕ)
    (r : (a : Spectral) → Fin (order a) → Coefficient)
    (hdecomp : (screeningFactorUnit sign (rootExponents (monomialOfFactors factors) i) :
        RatFunc Coefficient) =
      algebraMap (Polynomial Coefficient) (RatFunc Coefficient) Q +
        ∑ a ∈ s, ∑ j : Fin (order a), RatFunc.C (r a j) /
          (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1)) :
    screenedVacuumProjection sign i
      (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors)) =
      ∑ a ∈ s,
        (principalPartPolynomial (firstScreeningVector sign i) (order a)
          (fun j => RatFunc.C (r a j)) : MvPowerSeries (Fin 4) Scalars) *
        (MvPowerSeries.killCompl firstModeEmbedding
          ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients none) *
          firstScreeningSeries sign i (RatFunc.C (q ^ a.1 * t ^ a.2))) := by
  rw [screenedVacuumProjection_residueTransform,
    screening_scalar_partial_fraction_series sign (monomialOfFactors factors) i Q s order r hdecomp,
    residueTransform_grouped_principal_parts, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The finite local-residue identity follows from the original FR
operator; no local cancellation hypothesis is added. -/
theorem screenedVacuumProjection_local_residues (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄))
    (Q : Polynomial Coefficient) (s : Finset Spectral) (order : Spectral → ℕ)
    (r : (a : Spectral) → Fin (order a) → Coefficient)
    (hdecomp : (screeningFactorUnit sign (rootExponents (monomialOfFactors factors) i) :
        RatFunc Coefficient) =
      algebraMap (Polynomial Coefficient) (RatFunc Coefficient) Q +
        ∑ a ∈ s, ∑ j : Fin (order a), RatFunc.C (r a j) /
          (RatFunc.X - RatFunc.C (q ^ a.1 * t ^ a.2)) ^ (j.val + 1)) :
    screenedVacuumProjection sign i
      (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors)) =
      ∑ a ∈ s, (∑ j : Fin (order a),
        HahnSeries.single (-((j.val : ℤ) + 1)) (MvPowerSeries.C (RatFunc.C (r a j))) *
          (screenedPoleTaylor factors none sign i (RatFunc.C (q ^ a.1 * t ^ a.2)) :
            LaurentSeries (MvPowerSeries (Fin 4) Scalars))).coeff (-1) := by
  simp_rw [screened_principal_parts_residue]
  exact screenedVacuumProjection_principal_parts sign i factors Q s order r hdecomp

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
