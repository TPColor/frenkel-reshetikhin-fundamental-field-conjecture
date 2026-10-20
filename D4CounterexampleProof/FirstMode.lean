import D4CounterexampleProof.Signatures

/-!
First creation-mode coefficients of the original FR formal symbols.
These lemmas connect the finite signature calculations to `StatementDefinitions`.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

local instance : Field Coefficient := inferInstance

theorem linearSymbol_single_coeff (g : SimpleLieType)
    (c : OriginalFR.Fields.ModeIndex g → OriginalFR.Fields.Scalars)
    (mode : OriginalFR.Fields.ModeIndex g) :
    MvPowerSeries.coeff (Finsupp.single mode 1)
      (OriginalFR.Fields.linearSymbol g c) = c mode := by
  classical
  rw [MvPowerSeries.coeff_apply]
  rw [OriginalFR.Fields.linearSymbol]
  simp

private theorem linearSymbol_constantCoeff_zero (g : SimpleLieType)
    (c : OriginalFR.Fields.ModeIndex g → OriginalFR.Fields.Scalars) :
    MvPowerSeries.constantCoeff (OriginalFR.Fields.linearSymbol g c) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply,
    OriginalFR.Fields.linearSymbol]
  simp

private theorem linearSymbol_single_pow_coeff_zero (g : SimpleLieType)
    (c : OriginalFR.Fields.ModeIndex g → OriginalFR.Fields.Scalars)
    (mode : OriginalFR.Fields.ModeIndex g) (k : ℕ) (hk : 2 ≤ k) :
    MvPowerSeries.coeff (Finsupp.single mode 1)
      ((OriginalFR.Fields.linearSymbol g c) ^ k) = 0 := by
  apply MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent
    (m := 1) (by simp [linearSymbol_constantCoeff_zero g c])
  simpa using hk

/-- The first creation-mode coefficient of FR's formal exponential is its
linear exponent coefficient. -/
theorem exponentialSymbol_single_coeff (g : SimpleLieType)
    (c : OriginalFR.Fields.ModeIndex g → OriginalFR.Fields.Scalars)
    (mode : OriginalFR.Fields.ModeIndex g) :
    MvPowerSeries.coeff (Finsupp.single mode 1)
      (OriginalFR.Fields.exponentialSymbol g c) = c mode := by
  classical
  rw [MvPowerSeries.coeff_apply, OriginalFR.Fields.exponentialSymbol]
  simp [Finset.sum_range_succ, linearSymbol_single_coeff, MvPowerSeries.coeff_one]

theorem exponentialSymbol_constantCoeff (g : SimpleLieType)
    (c : OriginalFR.Fields.ModeIndex g → OriginalFR.Fields.Scalars) :
    MvPowerSeries.constantCoeff (OriginalFR.Fields.exponentialSymbol g c) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply,
    OriginalFR.Fields.exponentialSymbol]
  simp

/-- The first mode of the original screening current, before the charge
shift, is its prescribed Heisenberg coefficient. -/
theorem screeningSymbol_single_coeff (g : SimpleLieType)
    (sign : ScreeningSign) (i j : RootIndex g)
    (charge : OriginalFR.Fields.Charge g) :
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
      ((OriginalFR.Fields.screeningSymbol g sign i).coefficients charge) =
      RatFunc.C (screeningModes sign i (-1) j) := by
  exact exponentialSymbol_single_coeff g
    (fun mode => RatFunc.C (screeningModes sign i mode.2.val mode.1))
    (j, ⟨-1, by decide⟩)

/-- The sign in FR's minus screening is retained at creation mode -1. -/
theorem minus_screening_creation_coeff (g : SimpleLieType)
    (i j : RootIndex g) (charge : OriginalFR.Fields.Charge g) :
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
      ((OriginalFR.Fields.screeningSymbol g .minus i).coefficients charge) =
      if j = i then RatFunc.C (-(t ^ (-1 : ℤ) - t)⁻¹) else 0 := by
  rw [screeningSymbol_single_coeff]
  by_cases h : j = i <;> simp [screeningModes, h]

/-- The corresponding plus-screening creation coefficient. -/
theorem plus_screening_creation_coeff (g : SimpleLieType)
    (i j : RootIndex g) (charge : OriginalFR.Fields.Charge g) :
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
      ((OriginalFR.Fields.screeningSymbol g .plus i).coefficients charge) =
      if j = i then
        RatFunc.C ((q ^ (-(rootLength g i : ℤ)) - q ^ (rootLength g i : ℤ))⁻¹)
      else 0 := by
  rw [screeningSymbol_single_coeff]
  by_cases h : j = i <;> simp [screeningModes, h]

/-- The first creation coefficient of FR's A vertex follows from its
normally ordered exponential, including the original scalar prefactor. -/
theorem rootVertex_creation_coeff (g : SimpleLieType)
    (i j : RootIndex g) (inverse : Bool) (a b : ℤ)
    (charge : OriginalFR.Fields.Charge g) :
    let sign : ℤ := if inverse then -1 else 1
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
      ((OriginalFR.Fields.rootVertex g i inverse a b).coefficients charge) =
    RatFunc.C ((t ^ (2 : ℤ) * q ^ (-(2 * rootLength g i : ℤ)) *
      OriginalFR.Fields.chargePrefactor g charge (simpleRoot g i)) ^ sign) *
      (if j = i then RatFunc.C ((sign : Coefficient) * q ^ a * t ^ b) else 0) := by
  dsimp [OriginalFR.Fields.rootVertex]
  rw [MvPowerSeries.coeff_C_mul, exponentialSymbol_single_coeff]
  by_cases h : j = i <;> simp [h, mul_assoc]

/-- The corresponding coefficient of the original Y vertex. -/
theorem weightVertex_creation_coeff (g : SimpleLieType)
    (i j : RootIndex g) (inverse : Bool) (a b : ℤ)
    (charge : OriginalFR.Fields.Charge g) :
    let sign : ℤ := if inverse then -1 else 1
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
      ((OriginalFR.Fields.weightVertex g i inverse a b).coefficients charge) =
    RatFunc.C ((t ^ OriginalFR.Fields.rhoTExponent g i *
      q ^ (-OriginalFR.Fields.rhoQExponent g i) *
      OriginalFR.Fields.chargePrefactor g charge (fundamentalWeight g i)) ^ sign) *
    RatFunc.C ((sign : Coefficient) *
      (deformedCartan g (-1))⁻¹ j i * q ^ a * t ^ b) := by
  dsimp [OriginalFR.Fields.weightVertex]
  rw [MvPowerSeries.coeff_C_mul, exponentialSymbol_single_coeff]
  simp [mul_assoc]

/-- The linear coefficient of a normally ordered product has the expected
Leibniz form; this is the algebra behind adding first-mode signatures. -/
theorem normalProduct_single_coeff (g : SimpleLieType)
    (f h : OriginalFR.Fields.SymbolSeries g)
    (mode : OriginalFR.Fields.ModeIndex g) :
    MvPowerSeries.coeff (Finsupp.single mode 1) (f * h) =
      MvPowerSeries.coeff (Finsupp.single mode 1) f *
        MvPowerSeries.constantCoeff h +
      MvPowerSeries.constantCoeff f *
        MvPowerSeries.coeff (Finsupp.single mode 1) h := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    add_comm]

/-- Normal ordering adds the first-mode exponent vectors of formal
exponentials. -/
theorem exponentials_product_single_coeff (g : SimpleLieType)
    (c d : OriginalFR.Fields.ModeIndex g → OriginalFR.Fields.Scalars)
    (mode : OriginalFR.Fields.ModeIndex g) :
    MvPowerSeries.coeff (Finsupp.single mode 1)
      (OriginalFR.Fields.exponentialSymbol g c *
        OriginalFR.Fields.exponentialSymbol g d) = c mode + d mode := by
  rw [normalProduct_single_coeff, exponentialSymbol_single_coeff,
    exponentialSymbol_single_coeff, exponentialSymbol_constantCoeff,
    exponentialSymbol_constantCoeff]
  simp

end
end FrenkelReshetikhin.D4CounterexampleProof
