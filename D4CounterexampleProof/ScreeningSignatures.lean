import D4CounterexampleProof.CreationExponents

/-! Recovering the finite Laurent signature equations from equality of
the first creation coefficients of the original elementary symbols. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance screeningSignaturesCoefficientField : Field Coefficient := inferInstance

set_option backward.isDefEq.respectTransparency false in
theorem rational_signature_of_creation_equality
    (factors other : List (InverseRootFactor D₄)) (charge charge' : Charge D₄)
    (i : Fin 4) (den c d : Coefficient) (hden : den ≠ 0)
    (h : ∀ j : Fin 4,
      MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
          ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) /
        MvPowerSeries.constantCoeff ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) +
        RatFunc.C (if j = i then c / den else 0) =
      MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
          ((elementarySymbol D₄ (1 : Fin 4) other).coefficients charge') /
        MvPowerSeries.constantCoeff ((elementarySymbol D₄ (1 : Fin 4) other).coefficients charge') +
        RatFunc.C (if j = i then d / den else 0)) :
    ∀ j : Fin 4,
      den * (spectralMoment (monomialOfFactors other) j -
        spectralMoment (monomialOfFactors factors) j) =
        (c - d) * deformedCartan D₄ (-1) j i := by
  classical
  have hr (k : Fin 4) : den *
      (((deformedCartan D₄ (-1))⁻¹ k (1 : Fin 4) -
        (other.map fun f => if k = f.root then q ^ f.qShift * t ^ f.tShift else 0).sum) -
       ((deformedCartan D₄ (-1))⁻¹ k (1 : Fin 4) -
        (factors.map fun f => if k = f.root then q ^ f.qShift * t ^ f.tShift else 0).sum)) =
        if k = i then c - d else 0 := by
    have hh := h k
    erw [elementarySymbol_normalized_creation_C,
      elementarySymbol_normalized_creation_C, ← map_add, ← map_add] at hh
    have he := RatFunc.C_injective hh
    by_cases hki : k = i
    · simp only [if_pos hki] at he ⊢
      field_simp at he
      linear_combination -he
    · simp only [if_neg hki, add_zero] at he ⊢
      rw [he, sub_self, mul_zero]
  intro j
  rw [← elementary_creation_coordinates other j, ← elementary_creation_coordinates factors j,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    _ = ∑ k : Fin 4, deformedCartan D₄ (-1) j k *
        (if k = i then c - d else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← hr k]
      ring
    _ = (c - d) * deformedCartan D₄ (-1) j i := by
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp [mul_comm]

theorem d4_minus_screening_mode (i j : RootIndex D₄) (c : Coefficient) :
    screeningModes (g := D₄) .minus i (-1) j * c =
      if j = i then c / (t - t⁻¹) else 0 := by
  classical
  by_cases h : j = i
  · simp only [screeningModes, if_pos h, zpow_neg_one, neg_neg, zpow_one]
    rw [← neg_sub t t⁻¹, inv_neg, neg_neg]
    simp only [div_eq_mul_inv]
    ring
  · simp [screeningModes, h]

theorem d4_plus_screening_mode (i j : RootIndex D₄) (c : Coefficient) :
    screeningModes (g := D₄) .plus i (-1) j * c =
      if j = i then -c / (q - q⁻¹) else 0 := by
  classical
  by_cases h : j = i
  · simp only [screeningModes, if_pos h, d4_rootLength, Nat.cast_one, mul_one,
      zpow_neg_one, neg_neg, zpow_one]
    rw [← neg_sub q q⁻¹, inv_neg]
    simp only [div_eq_mul_inv]
    ring
  · simp [screeningModes, h]

/-- Equality of the actual elementary first creation coefficients, with
the original screening contribution added at each pole, implies precisely
the Laurent signature relation used by the partner classification. -/
theorem signature_of_creation_equality
    (factors other : List (InverseRootFactor D₄)) (charge charge' : Charge D₄)
    (sign : ScreeningSign) (i : Fin 4) (ca cb da db : ℤ)
    (h : ∀ j : Fin 4,
      MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
          ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) /
        MvPowerSeries.constantCoeff ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) +
        RatFunc.C (screeningModes (g := D₄) sign i (-1) j * (q ^ ca * t ^ cb)) =
      MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
          ((elementarySymbol D₄ (1 : Fin 4) other).coefficients charge') /
        MvPowerSeries.constantCoeff ((elementarySymbol D₄ (1 : Fin 4) other).coefficients charge') +
        RatFunc.C (screeningModes (g := D₄) sign i (-1) j * (q ^ da * t ^ db))) :
    match sign with
    | .minus => tDifference (monomialOfFactors other - monomialOfFactors factors) =
        A i ca cb - A i da db
    | .plus => qDifference (monomialOfFactors other - monomialOfFactors factors) =
        A i da db - A i ca cb := by
  cases sign with
  | minus =>
    have hh := rational_signature_of_creation_equality factors other charge charge' i
      (t - t⁻¹) (q ^ ca * t ^ cb) (q ^ da * t ^ db) t_sub_inv_ne_zero
      (by
        intro j
        have hj := h j
        erw [d4_minus_screening_mode, d4_minus_screening_mode] at hj
        exact hj)
    apply tDifference_of_rational_signature
    intro j
    rw [hh j, spectralMoment_sub]
    simp only [Pi.sub_apply, spectralMoment_A]
    ring
  | plus =>
    have hh := rational_signature_of_creation_equality factors other charge charge' i
      (q - q⁻¹) (-(q ^ ca * t ^ cb)) (-(q ^ da * t ^ db)) q_sub_inv_ne_zero
      (by
        intro j
        have hj := h j
        erw [d4_plus_screening_mode, d4_plus_screening_mode] at hj
        exact hj)
    apply qDifference_of_rational_signature
    intro j
    rw [hh j, spectralMoment_sub]
    simp only [Pi.sub_apply, spectralMoment_A]
    ring

/-- A version with the screened normal products themselves in the premise.
The screening series is the original FR exponential with w=z q^a t^b.
This theorem only extracts the signature; it does not assert that a
screening commutator supplies such an equality or a cancelling partner. -/
theorem signature_of_screened_normalized_creation
    (factors other : List (InverseRootFactor D₄)) (charge charge' : Charge D₄)
    (sign : ScreeningSign) (i : Fin 4) (ca cb da db : ℤ) :
    let f := (elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge
    let g := (elementarySymbol D₄ (1 : Fin 4) other).coefficients charge'
    let s := exponentialSymbol D₄ (fun mode =>
      RatFunc.C (screeningModes (g := D₄) sign i mode.2.val mode.1 *
        (q ^ ca * t ^ cb) ^ (-mode.2.val)))
    let u := exponentialSymbol D₄ (fun mode =>
      RatFunc.C (screeningModes (g := D₄) sign i mode.2.val mode.1 *
        (q ^ da * t ^ db) ^ (-mode.2.val)))
    (∀ j : Fin 4,
      MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1) (f * s) /
          MvPowerSeries.constantCoeff (f * s) =
        MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1) (g * u) /
          MvPowerSeries.constantCoeff (g * u)) →
    match sign with
    | .minus => tDifference (monomialOfFactors other - monomialOfFactors factors) =
        A i ca cb - A i da db
    | .plus => qDifference (monomialOfFactors other - monomialOfFactors factors) =
        A i da db - A i ca cb := by
  dsimp only
  intro h
  have result := signature_of_creation_equality factors other charge charge' sign i ca cb da db (fun j => by
    have hf := normalized_creation_screening_product D₄
      ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge)
      (elementarySymbol_constantCoeff_ne_zero D₄ (1 : Fin 4) factors charge) sign i j ca cb
    have hg := normalized_creation_screening_product D₄
      ((elementarySymbol D₄ (1 : Fin 4) other).coefficients charge')
      (elementarySymbol_constantCoeff_ne_zero D₄ (1 : Fin 4) other charge') sign i j da db
    exact hf.symm.trans ((h j).trans hg))
  cases sign <;> exact result

end
end FrenkelReshetikhin.D4CounterexampleProof
