import D4CounterexampleProof.CreationExponents

/-! Independence of the actual elementary FR symbols, before their
evaluation in the presented Fock modules. All original prefactors remain. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance elementaryIndependenceCoefficientField : Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem exponentialSymbol_zero (g : SimpleLieType) : exponentialSymbol g 0 = 1 := by
  symm
  apply exponentialSymbol_unique
  · simp
  · intro mode
    simp only [MvPowerSeries.pderiv_one, Pi.zero_apply, map_zero, zero_mul]

theorem scaled_exponential_product (g : SimpleLieType) (a b : Scalars)
    (c d : ModeIndex g → Scalars) :
    (MvPowerSeries.C a * exponentialSymbol g c) *
      (MvPowerSeries.C b * exponentialSymbol g d) =
      MvPowerSeries.C (a * b) * exponentialSymbol g (c + d) := by
  rw [map_mul, ← exponentialSymbol_mul]
  ring

theorem weightVertex_scaled_exponential (g : SimpleLieType) (i : RootIndex g)
    (inverse : Bool) (a b : ℤ) (charge : Charge g) :
    ∃ c : ModeIndex g → Scalars,
      (weightVertex g i inverse a b).coefficients charge =
        MvPowerSeries.C (MvPowerSeries.constantCoeff
          ((weightVertex g i inverse a b).coefficients charge)) * exponentialSymbol g c := by
  dsimp only [weightVertex]
  refine ⟨fun mode => RatFunc.C
    (((if inverse then (-1 : ℤ) else 1) : Coefficient) *
      (deformedCartan g mode.2.val)⁻¹ mode.1 i * (q ^ a * t ^ b) ^ (-mode.2.val)), ?_⟩
  rw [map_mul, MvPowerSeries.constantCoeff_C, exponentialSymbol_constantCoeff, mul_one]
  cases inverse <;> simp

theorem rootVertex_scaled_exponential (g : SimpleLieType) (i : RootIndex g)
    (inverse : Bool) (a b : ℤ) (charge : Charge g) :
    ∃ c : ModeIndex g → Scalars,
      (rootVertex g i inverse a b).coefficients charge =
        MvPowerSeries.C (MvPowerSeries.constantCoeff
          ((rootVertex g i inverse a b).coefficients charge)) * exponentialSymbol g c := by
  dsimp only [rootVertex]
  refine ⟨fun mode => if mode.1 = i then RatFunc.C
    (((if inverse then (-1 : ℤ) else 1) : Coefficient) *
      (q ^ a * t ^ b) ^ (-mode.2.val)) else 0, ?_⟩
  rw [map_mul, MvPowerSeries.constantCoeff_C, exponentialSymbol_constantCoeff, mul_one]
  cases inverse <;> simp

theorem list_scaled_exponential (g : SimpleLieType) (xs : List (SymbolSeries g))
    (hx : ∀ f ∈ xs, ∃ c : ModeIndex g → Scalars,
      f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) * exponentialSymbol g c) :
    ∃ c : ModeIndex g → Scalars,
      xs.prod = MvPowerSeries.C (MvPowerSeries.constantCoeff xs.prod) * exponentialSymbol g c := by
  induction xs with
  | nil => exact ⟨0, by simp [exponentialSymbol_zero]⟩
  | cons f fs ih =>
    obtain ⟨c, hc⟩ := hx f (by simp)
    obtain ⟨d, hd⟩ := ih (fun h hh => hx h (by simp [hh]))
    refine ⟨c + d, ?_⟩
    rw [List.prod_cons, map_mul]
    conv_lhs => rw [hc, hd]
    exact scaled_exponential_product g _ _ c d

theorem elementarySymbol_scaled_exponential (g : SimpleLieType) (i : RootIndex g)
    (factors : List (InverseRootFactor g)) (charge : Charge g) :
    ∃ c : ModeIndex g → Scalars,
      (elementarySymbol g i factors).coefficients charge =
        MvPowerSeries.C (MvPowerSeries.constantCoeff
          ((elementarySymbol g i factors).coefficients charge)) * exponentialSymbol g c := by
  have hroots : ∀ f ∈ (factors.map fun f =>
      (rootVertex g f.root true f.qShift f.tShift).coefficients charge),
      ∃ c : ModeIndex g → Scalars,
        f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) * exponentialSymbol g c := by
    intro f hf
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hf
    exact rootVertex_scaled_exponential g r.root true r.qShift r.tShift charge
  obtain ⟨c, hc⟩ := weightVertex_scaled_exponential g i false 0 0 charge
  obtain ⟨d, hd⟩ := list_scaled_exponential g _ hroots
  refine ⟨c + d, ?_⟩
  change (weightVertex g i false 0 0).coefficients charge *
      (normalProducts g (factors.map fun f => rootVertex g f.root true f.qShift f.tShift)).coefficients charge =
    MvPowerSeries.C (MvPowerSeries.constantCoeff
      ((weightVertex g i false 0 0).coefficients charge *
        (normalProducts g (factors.map fun f => rootVertex g f.root true f.qShift f.tShift)).coefficients charge)) *
      exponentialSymbol g (c + d)
  simp only [normalProducts_coefficients, List.map_map, Function.comp_def]
  rw [map_mul]
  conv_lhs => rw [hc, hd]
  exact scaled_exponential_product g _ _ c d

/-- Distinct elementary Laurent monomials give independent original FR
symbols, even with polynomial coefficients in the mode variables. The
statement is about the defining formal series, not their Fock evaluations. -/
theorem elementarySymbol_polynomial_sum_eq_zero {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (hmono : Function.Injective (fun i => monomialOfFactors (factors i)))
    (P : ι → MvPolynomial (ModeIndex D₄) Scalars)
    (hsum : ∑ i ∈ s, (P i : SymbolSeries D₄) *
      (elementarySymbol D₄ (1 : Fin 4) (factors i)).coefficients charge = 0) :
    ∀ i ∈ s, P i = 0 := by
  classical
  choose c hc using fun i : ι =>
    elementarySymbol_scaled_exponential D₄ (1 : Fin 4) (factors i) charge
  have hn (i : ι) := elementarySymbol_constantCoeff_ne_zero D₄ (1 : Fin 4) (factors i) charge
  have hcoeff (i : ι) (mode : ModeIndex D₄) :
      MvPowerSeries.coeff (Finsupp.single mode 1)
          ((elementarySymbol D₄ (1 : Fin 4) (factors i)).coefficients charge) /
        MvPowerSeries.constantCoeff
          ((elementarySymbol D₄ (1 : Fin 4) (factors i)).coefficients charge) = c i mode := by
    rw [hc i]
    exact normalized_single_scaled_exponential D₄ _ _ mode (hn i)
  have hci : Function.Injective c := by
    intro i j hij
    apply hmono
    apply monomialOfFactors_eq_of_normalized_creation (factors i) (factors j) charge charge
    intro k
    erw [hcoeff i (k, ⟨-1, by decide⟩), hcoeff j (k, ⟨-1, by decide⟩), hij]
  let Q (i : ι) := P i * MvPolynomial.C (MvPowerSeries.constantCoeff
    ((elementarySymbol D₄ (1 : Fin 4) (factors i)).coefficients charge))
  have hsum' : ∑ i ∈ s, (Q i : SymbolSeries D₄) * exponentialSymbol D₄ (c i) = 0 := by
    calc
      _ = ∑ i ∈ s, (P i : SymbolSeries D₄) *
          (elementarySymbol D₄ (1 : Fin 4) (factors i)).coefficients charge := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc i]
        simp only [Q, MvPolynomial.coe_mul, MvPolynomial.coe_C, mul_assoc]
      _ = 0 := hsum
  have hz := exponentialSymbol_polynomial_sum_eq_zero D₄ s c hci Q hsum'
  intro i hi
  have hQ := hz i hi
  exact (mul_eq_zero.mp hQ).resolve_right (MvPolynomial.C_ne_zero.mpr (hn i))

end
end FrenkelReshetikhin.D4CounterexampleProof
