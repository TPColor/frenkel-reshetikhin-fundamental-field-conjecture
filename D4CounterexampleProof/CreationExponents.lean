import D4CounterexampleProof.D4Cartan
import D4CounterexampleProof.ExponentialSymbols

/-!
Normalized first creation coefficients of the actual original FR symbols.
The scalar and zero-mode prefactors are retained and proved nonzero before
they are cancelled in a coefficient ratio.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance creationExponentsCoefficientField : Field Coefficient := inferInstance

theorem normalized_single_product (g : SimpleLieType) (f h : SymbolSeries g)
    (mode : ModeIndex g) (hf : MvPowerSeries.constantCoeff f ≠ 0)
    (hh : MvPowerSeries.constantCoeff h ≠ 0) :
    MvPowerSeries.coeff (Finsupp.single mode 1) (f * h) /
        MvPowerSeries.constantCoeff (f * h) =
      MvPowerSeries.coeff (Finsupp.single mode 1) f / MvPowerSeries.constantCoeff f +
      MvPowerSeries.coeff (Finsupp.single mode 1) h / MvPowerSeries.constantCoeff h := by
  rw [normalProduct_single_coeff, map_mul]
  field_simp

theorem constantCoeff_prod_ne_zero (g : SimpleLieType) (xs : List (SymbolSeries g))
    (hx : ∀ f ∈ xs, MvPowerSeries.constantCoeff f ≠ 0) :
    MvPowerSeries.constantCoeff xs.prod ≠ 0 := by
  induction xs with
  | nil => simp
  | cons f fs ih =>
    rw [List.prod_cons, map_mul]
    exact mul_ne_zero (hx f (by simp)) (ih (fun h hh => hx h (by simp [hh])))

theorem normalized_single_list_product (g : SimpleLieType) (xs : List (SymbolSeries g))
    (mode : ModeIndex g) (hx : ∀ f ∈ xs, MvPowerSeries.constantCoeff f ≠ 0) :
    MvPowerSeries.coeff (Finsupp.single mode 1) xs.prod / MvPowerSeries.constantCoeff xs.prod =
      (xs.map fun f => MvPowerSeries.coeff (Finsupp.single mode 1) f /
        MvPowerSeries.constantCoeff f).sum := by
  classical
  induction xs with
  | nil => simp [MvPowerSeries.coeff_one]
  | cons f fs ih =>
    have htail : ∀ h ∈ fs, MvPowerSeries.constantCoeff h ≠ 0 :=
      fun h hh => hx h (by simp [hh])
    rw [List.prod_cons, normalized_single_product g f fs.prod mode
      (hx f (by simp)) (constantCoeff_prod_ne_zero g fs htail), ih htail]
    rfl

theorem normalized_single_scaled_exponential (g : SimpleLieType) (a : Scalars)
    (c : ModeIndex g → Scalars) (mode : ModeIndex g) (ha : a ≠ 0) :
    MvPowerSeries.coeff (Finsupp.single mode 1) (MvPowerSeries.C a * exponentialSymbol g c) /
      MvPowerSeries.constantCoeff (MvPowerSeries.C a * exponentialSymbol g c) = c mode := by
  rw [MvPowerSeries.coeff_C_mul, exponentialSymbol_single_coeff, map_mul,
    MvPowerSeries.constantCoeff_C, exponentialSymbol_constantCoeff, mul_one]
  exact mul_div_cancel_left₀ _ ha

theorem chargePrefactor_ne_zero (g : SimpleLieType) (charge : Charge g) (weight : Weight g) :
    chargePrefactor g charge weight ≠ 0 := by
  cases charge with
  | none => simp [chargePrefactor]
  | some data =>
    rcases data with ⟨sign, i⟩
    cases sign
    · exact zpow_ne_zero _ t_ne_zero
    · exact zpow_ne_zero _ q_ne_zero

theorem weightVertex_constantCoeff_ne_zero (g : SimpleLieType) (i : RootIndex g)
    (inverse : Bool) (a b : ℤ) (charge : Charge g) :
    MvPowerSeries.constantCoeff ((weightVertex g i inverse a b).coefficients charge) ≠ 0 := by
  dsimp only [weightVertex]
  rw [map_mul, MvPowerSeries.constantCoeff_C, exponentialSymbol_constantCoeff, mul_one]
  intro hz
  have hbase : t ^ rhoTExponent g i * q ^ (-rhoQExponent g i) *
      chargePrefactor g charge (fundamentalWeight g i) ≠ 0 := mul_ne_zero
    (mul_ne_zero (zpow_ne_zero _ t_ne_zero) (zpow_ne_zero _ q_ne_zero))
    (chargePrefactor_ne_zero g charge (fundamentalWeight g i))
  have hpow := zpow_ne_zero (if inverse then (-1 : ℤ) else 1) hbase
  apply hpow
  exact RatFunc.C_injective (hz.trans (map_zero _).symm)

theorem rootVertex_constantCoeff_ne_zero (g : SimpleLieType) (i : RootIndex g)
    (inverse : Bool) (a b : ℤ) (charge : Charge g) :
    MvPowerSeries.constantCoeff ((rootVertex g i inverse a b).coefficients charge) ≠ 0 := by
  dsimp only [rootVertex]
  rw [map_mul, MvPowerSeries.constantCoeff_C, exponentialSymbol_constantCoeff, mul_one]
  intro hz
  have hbase : t ^ (2 : ℤ) * q ^ (-(2 * rootLength g i : ℤ)) *
      chargePrefactor g charge (simpleRoot g i) ≠ 0 := mul_ne_zero
    (mul_ne_zero (zpow_ne_zero _ t_ne_zero) (zpow_ne_zero _ q_ne_zero))
    (chargePrefactor_ne_zero g charge (simpleRoot g i))
  have hpow := zpow_ne_zero (if inverse then (-1 : ℤ) else 1) hbase
  apply hpow
  exact RatFunc.C_injective (hz.trans (map_zero _).symm)

theorem weightVertex_normalized_creation (g : SimpleLieType) (i j : RootIndex g)
    (a b : ℤ) (charge : Charge g) :
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
        ((weightVertex g i false a b).coefficients charge) /
      MvPowerSeries.constantCoeff ((weightVertex g i false a b).coefficients charge) =
        RatFunc.C ((deformedCartan g (-1))⁻¹ j i * q ^ a * t ^ b) := by
  have hc := weightVertex_constantCoeff_ne_zero g i false a b charge
  dsimp only [weightVertex] at hc ⊢
  rw [map_mul, MvPowerSeries.constantCoeff_C, exponentialSymbol_constantCoeff, mul_one] at hc
  rw [normalized_single_scaled_exponential g _ _ _ hc]
  simp [mul_assoc]

theorem rootVertex_inverse_normalized_creation (g : SimpleLieType) (i j : RootIndex g)
    (a b : ℤ) (charge : Charge g) :
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
        ((rootVertex g i true a b).coefficients charge) /
      MvPowerSeries.constantCoeff ((rootVertex g i true a b).coefficients charge) =
        if j = i then -RatFunc.C (q ^ a * t ^ b) else 0 := by
  have hc := rootVertex_constantCoeff_ne_zero g i true a b charge
  dsimp only [rootVertex] at hc ⊢
  rw [map_mul, MvPowerSeries.constantCoeff_C, exponentialSymbol_constantCoeff, mul_one] at hc
  rw [normalized_single_scaled_exponential g _ _ _ hc]
  by_cases hji : j = i <;> simp [hji]

theorem normalProducts_coefficients (g : SimpleLieType) (xs : List (NormalSymbol g))
    (charge : Charge g) :
    (normalProducts g xs).coefficients charge = (xs.map fun f => f.coefficients charge).prod := by
  induction xs with
  | nil => rfl
  | cons f fs ih =>
    change f.coefficients charge * (normalProducts g fs).coefficients charge =
      f.coefficients charge * (fs.map fun h => h.coefficients charge).prod
    rw [ih]

theorem elementarySymbol_normalized_creation (g : SimpleLieType) (i j : RootIndex g)
    (factors : List (InverseRootFactor g)) (charge : Charge g) :
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
        ((elementarySymbol g i factors).coefficients charge) /
      MvPowerSeries.constantCoeff ((elementarySymbol g i factors).coefficients charge) =
        RatFunc.C ((deformedCartan g (-1))⁻¹ j i) +
          (factors.map fun f => if j = f.root then -RatFunc.C (q ^ f.qShift * t ^ f.tShift) else 0).sum := by
  classical
  have hroots : ∀ f ∈ factors.map (fun f =>
      (rootVertex g f.root true f.qShift f.tShift).coefficients charge),
      MvPowerSeries.constantCoeff f ≠ 0 := by
    intro f hf
    obtain ⟨factor, _, rfl⟩ := List.mem_map.mp hf
    exact rootVertex_constantCoeff_ne_zero g factor.root true factor.qShift factor.tShift charge
  have hp := constantCoeff_prod_ne_zero g _ hroots
  change MvPowerSeries.coeff _
      ((weightVertex g i false 0 0).coefficients charge *
        (normalProducts g (factors.map fun f => rootVertex g f.root true f.qShift f.tShift)).coefficients charge) /
    MvPowerSeries.constantCoeff
      ((weightVertex g i false 0 0).coefficients charge *
        (normalProducts g (factors.map fun f => rootVertex g f.root true f.qShift f.tShift)).coefficients charge) = _
  rw [normalProducts_coefficients]
  simp only [List.map_map]
  dsimp only [Function.comp_def]
  erw [normalized_single_product g _ _ (j, ⟨-1, by decide⟩)
    (weightVertex_constantCoeff_ne_zero g i false 0 0 charge) hp,
    normalized_single_list_product g _ _ hroots,
    weightVertex_normalized_creation]
  simp only [zpow_zero, mul_one, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro f hf
  exact rootVertex_inverse_normalized_creation g f.root j f.qShift f.tShift charge

theorem elementarySymbol_constantCoeff_ne_zero (g : SimpleLieType) (i : RootIndex g)
    (factors : List (InverseRootFactor g)) (charge : Charge g) :
    MvPowerSeries.constantCoeff ((elementarySymbol g i factors).coefficients charge) ≠ 0 := by
  change MvPowerSeries.constantCoeff ((weightVertex g i false 0 0).coefficients charge *
    (normalProducts g (factors.map fun f => rootVertex g f.root true f.qShift f.tShift)).coefficients charge) ≠ 0
  rw [map_mul, normalProducts_coefficients]
  apply mul_ne_zero (weightVertex_constantCoeff_ne_zero g i false 0 0 charge)
  apply constantCoeff_prod_ne_zero
  intro f hf
  obtain ⟨factor, hmem, rfl⟩ := List.mem_map.mp hf
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hmem
  exact rootVertex_constantCoeff_ne_zero g r.root true r.qShift r.tShift charge

/-- The original screening exponential evaluated at w=z q^a t^b adds
its prescribed creation coefficient to that of a normal product. -/
theorem normalized_creation_screening_product (g : SimpleLieType)
    (f : SymbolSeries g) (hf : MvPowerSeries.constantCoeff f ≠ 0)
    (sign : ScreeningSign) (i j : RootIndex g) (a b : ℤ) :
    let s := exponentialSymbol g (fun mode =>
      RatFunc.C (screeningModes sign i mode.2.val mode.1 *
        (q ^ a * t ^ b) ^ (-mode.2.val)))
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1) (f * s) /
      MvPowerSeries.constantCoeff (f * s) =
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1) f /
      MvPowerSeries.constantCoeff f +
      RatFunc.C (screeningModes sign i (-1) j * (q ^ a * t ^ b)) := by
  dsimp only
  rw [normalized_single_product g _ _ _ hf
    (by rw [exponentialSymbol_constantCoeff]; exact one_ne_zero),
    exponentialSymbol_constantCoeff, div_one, exponentialSymbol_single_coeff]
  simp only [neg_neg, zpow_one]

theorem elementarySymbol_normalized_creation_C (g : SimpleLieType) (i j : RootIndex g)
    (factors : List (InverseRootFactor g)) (charge : Charge g) :
    MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
        ((elementarySymbol g i factors).coefficients charge) /
      MvPowerSeries.constantCoeff ((elementarySymbol g i factors).coefficients charge) =
        RatFunc.C ((deformedCartan g (-1))⁻¹ j i -
          (factors.map fun f => if j = f.root then q ^ f.qShift * t ^ f.tShift else 0).sum) := by
  classical
  rw [elementarySymbol_normalized_creation, map_sub, sub_eq_add_neg]
  congr 1
  induction factors with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons, map_add, neg_add_rev]
    rw [ih]
    by_cases h : j = f.root <;> simp [h, add_comm]

/-- Equal normalized creation coefficients of two actual elementary symbols
force equality of their Laurent monomials. No quotient of symbols or assumed
independence of formal labels is used. -/
theorem monomialOfFactors_eq_of_normalized_creation
    (factors other : List (InverseRootFactor D₄)) (charge charge' : Charge D₄)
    (h : ∀ j : Fin 4,
      MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
          ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) /
        MvPowerSeries.constantCoeff ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) =
      MvPowerSeries.coeff (Finsupp.single (j, ⟨-1, by decide⟩) 1)
          ((elementarySymbol D₄ (1 : Fin 4) other).coefficients charge') /
        MvPowerSeries.constantCoeff ((elementarySymbol D₄ (1 : Fin 4) other).coefficients charge')) :
    monomialOfFactors factors = monomialOfFactors other := by
  apply spectralMoment_injective
  funext j
  rw [← elementary_creation_coordinates factors j, ← elementary_creation_coordinates other j]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hh := h k
  erw [elementarySymbol_normalized_creation_C,
    elementarySymbol_normalized_creation_C] at hh
  exact RatFunc.C_injective hh

end
end FrenkelReshetikhin.D4CounterexampleProof
