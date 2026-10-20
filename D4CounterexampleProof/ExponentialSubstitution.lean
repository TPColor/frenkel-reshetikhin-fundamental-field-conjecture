import D4CounterexampleProof.ExponentialSymbols
import D4CounterexampleProof.ScalarContractions

/-! Substitution identities derived for the original factorial-series
definition of the normally ordered exponential. The auxiliary power
series variables are field-argument ratios, not h-adic parameters. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance exponentialSubstitutionField : Field Coefficient := inferInstance

theorem linearSymbol_constantCoeff (g : SimpleLieType) (c : ModeIndex g → Scalars) :
    MvPowerSeries.constantCoeff (linearSymbol g c) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply,
    linearSymbol]
  simp

/-- The original finite-per-coefficient exponential agrees with formal
substitution into the ordinary exponential. This is a theorem about the
original definition, not a replacement for it. -/
theorem exponentialSymbol_eq_exp_subst (g : SimpleLieType) (c : ModeIndex g → Scalars) :
    exponentialSymbol g c = (PowerSeries.exp Scalars).subst (linearSymbol g c) := by
  classical
  have hL := PowerSeries.HasSubst.of_constantCoeff_zero (linearSymbol_constantCoeff g c)
  apply MvPowerSeries.ext
  intro d
  rw [PowerSeries.coeff_subst hL]
  change (∑ k ∈ Finset.range (d.sum (fun _ n => n) + 1),
      (k.factorial : Scalars)⁻¹ * MvPowerSeries.coeff d (linearSymbol g c ^ k)) = _
  symm
  rw [finsum_eq_sum_of_support_subset]
  · apply Finset.sum_congr rfl
    intro k hk
    simp [PowerSeries.coeff_exp, div_eq_mul_inv, smul_eq_mul]
  · intro k hk
    by_contra hnot
    have hk' : d.sum (fun _ n => n) + 1 ≤ k := by simpa using hnot
    have hz : MvPowerSeries.coeff d (linearSymbol g c ^ k) = 0 := by
      apply MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1)
      · simp [linearSymbol_constantCoeff]
      · change 1 + d.sum (fun _ n => n) ≤ k
        omega
    exact hk (by dsimp only; rw [hz, smul_zero])

/-- Any valid coefficientwise substitution of the original exponential
may be carried out on its linear exponent first. -/
theorem exponentialSymbol_subst {τ : Type*} (g : SimpleLieType)
    (c : ModeIndex g → Scalars) (a : ModeIndex g → MvPowerSeries τ Scalars)
    (ha : MvPowerSeries.HasSubst a) :
    (exponentialSymbol g c).subst a =
      (PowerSeries.exp Scalars).subst ((linearSymbol g c).subst a) := by
  rw [exponentialSymbol_eq_exp_subst]
  exact MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero (linearSymbol_constantCoeff g c)).const ha _

/-- Substituting the original linear symbol sums just the substituted
variables; all other monomial indices have zero coefficient. -/
theorem linearSymbol_coeff_subst {τ : Type*} (g : SimpleLieType)
    (c : ModeIndex g → Scalars) (a : ModeIndex g → MvPowerSeries τ Scalars)
    (ha : MvPowerSeries.HasSubst a) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e ((linearSymbol g c).subst a) =
      ∑ᶠ mode : ModeIndex g, c mode * MvPowerSeries.coeff e (a mode) := by
  classical
  rw [MvPowerSeries.coeff_subst ha]
  let f : ModeMonomial g → Scalars := fun d =>
    MvPowerSeries.coeff d (linearSymbol g c) •
      MvPowerSeries.coeff e (d.prod fun mode k => a mode ^ k)
  change (∑ᶠ d, f d) = _
  have hinj : Function.Injective (fun mode : ModeIndex g => Finsupp.single mode (1 : ℕ)) :=
    Finsupp.single_left_injective one_ne_zero
  calc
    (∑ᶠ d, f d) = ∑ᶠ d ∈ Set.range (fun mode : ModeIndex g => Finsupp.single mode (1 : ℕ)),
        f d := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro d
      by_cases hd : d ∈ Set.range (fun mode : ModeIndex g => Finsupp.single mode (1 : ℕ))
      · rw [Set.indicator_of_mem hd]
      · rw [Set.indicator_of_notMem hd]
        have hdeg : d.sum (fun _ k => k) ≠ 1 := by
          intro h
          obtain ⟨mode, hm⟩ := (Finsupp.sum_eq_one_iff d).mp h
          exact hd ⟨mode, hm.symm⟩
        simp [f, MvPowerSeries.coeff_apply, linearSymbol, hdeg]
    _ = ∑ᶠ mode : ModeIndex g, f (Finsupp.single mode 1) := finsum_mem_range hinj
    _ = _ := by
      apply finsum_congr
      intro mode
      simp [f, linearSymbol_single_coeff, Finsupp.prod_single_index, smul_eq_mul]

end
end FrenkelReshetikhin.D4CounterexampleProof
