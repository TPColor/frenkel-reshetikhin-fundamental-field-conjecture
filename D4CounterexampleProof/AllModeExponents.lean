import D4CounterexampleProof.ElementaryIndependence

/-! Explicit exponents of the original elementary symbols at every
nonzero mode, used in the operator contraction calculation. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields

local instance allModeExponentsField : Field Coefficient := inferInstance

theorem weightVertex_normalized_mode (g : SimpleLieType) (i : RootIndex g)
    (a b : ℤ) (charge : Charge g) (mode : ModeIndex g) :
    MvPowerSeries.coeff (Finsupp.single mode 1) ((weightVertex g i false a b).coefficients charge) /
      MvPowerSeries.constantCoeff ((weightVertex g i false a b).coefficients charge) =
        RatFunc.C ((deformedCartan g mode.2.val)⁻¹ mode.1 i * (q ^ a * t ^ b) ^ (-mode.2.val)) := by
  have hc := weightVertex_constantCoeff_ne_zero g i false a b charge
  dsimp only [weightVertex] at hc ⊢
  rw [map_mul, MvPowerSeries.constantCoeff_C, exponentialSymbol_constantCoeff, mul_one] at hc
  rw [normalized_single_scaled_exponential g _ _ _ hc]
  simp

theorem rootVertex_inverse_normalized_mode (g : SimpleLieType) (i : RootIndex g)
    (a b : ℤ) (charge : Charge g) (mode : ModeIndex g) :
    MvPowerSeries.coeff (Finsupp.single mode 1) ((rootVertex g i true a b).coefficients charge) /
      MvPowerSeries.constantCoeff ((rootVertex g i true a b).coefficients charge) =
        if mode.1 = i then -RatFunc.C ((q ^ a * t ^ b) ^ (-mode.2.val)) else 0 := by
  have hc := rootVertex_constantCoeff_ne_zero g i true a b charge
  dsimp only [rootVertex] at hc ⊢
  rw [map_mul, MvPowerSeries.constantCoeff_C, exponentialSymbol_constantCoeff, mul_one] at hc
  rw [normalized_single_scaled_exponential g _ _ _ hc]
  by_cases h : mode.1 = i <;> simp [h]

theorem elementarySymbol_normalized_mode (g : SimpleLieType) (i : RootIndex g)
    (factors : List (InverseRootFactor g)) (charge : Charge g) (mode : ModeIndex g) :
    MvPowerSeries.coeff (Finsupp.single mode 1) ((elementarySymbol g i factors).coefficients charge) /
      MvPowerSeries.constantCoeff ((elementarySymbol g i factors).coefficients charge) =
        RatFunc.C ((deformedCartan g mode.2.val)⁻¹ mode.1 i) +
          (factors.map fun f => if mode.1 = f.root then
            -RatFunc.C ((q ^ f.qShift * t ^ f.tShift) ^ (-mode.2.val)) else 0).sum := by
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
  erw [normalized_single_product g _ _ mode
    (weightVertex_constantCoeff_ne_zero g i false 0 0 charge) hp,
    normalized_single_list_product g _ _ hroots,
    weightVertex_normalized_mode g i 0 0 charge mode]
  simp only [zpow_zero, mul_one, one_zpow, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro f hf
  exact rootVertex_inverse_normalized_mode g f.root f.qShift f.tShift charge mode

def elementaryModeExponent (g : SimpleLieType) (i : RootIndex g)
    (factors : List (InverseRootFactor g)) (mode : ModeIndex g) : Scalars :=
  RatFunc.C ((deformedCartan g mode.2.val)⁻¹ mode.1 i) +
    (factors.map fun f => if mode.1 = f.root then
      -RatFunc.C ((q ^ f.qShift * t ^ f.tShift) ^ (-mode.2.val)) else 0).sum

/-- The complete all-mode exponential formula is derived from the
original definition; it is not used to redefine that definition. -/
theorem elementarySymbol_explicit_exponential (g : SimpleLieType) (i : RootIndex g)
    (factors : List (InverseRootFactor g)) (charge : Charge g) :
    (elementarySymbol g i factors).coefficients charge =
      MvPowerSeries.C (MvPowerSeries.constantCoeff ((elementarySymbol g i factors).coefficients charge)) *
        exponentialSymbol g (elementaryModeExponent g i factors) := by
  obtain ⟨c, hc⟩ := elementarySymbol_scaled_exponential g i factors charge
  have hn := elementarySymbol_constantCoeff_ne_zero g i factors charge
  have he : c = elementaryModeExponent g i factors := by
    funext mode
    have hm := elementarySymbol_normalized_mode g i factors charge mode
    rw [hc, normalized_single_scaled_exponential g _ c mode hn] at hm
    exact hm
  simpa only [he] using hc

end
end FrenkelReshetikhin.D4CounterexampleProof
