import D4CounterexampleProof.ExponentialSymbols

/-! The factorial-product coefficient formula is proved for the original
FR exponential definition; it is not used as a replacement definition. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields

local instance exponentialCoefficientsField : Field Coefficient := inferInstance

private theorem factorial_factor_step (a : Scalars) (n : ℕ) :
    (a ^ (n + 1) / ((n + 1).factorial : Scalars)) * ((n : Scalars) + 1) =
      a * (a ^ n / (n.factorial : Scalars)) := by
  have hf : (n.factorial : Scalars) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn : (n : Scalars) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/-- Exact coefficients of the actual formal exponential in FR's
normally ordered symbols, including factorials for repeated modes. -/
theorem exponentialSymbol_coeff_product (g : SimpleLieType)
    (c : ModeIndex g → Scalars) (d : ModeMonomial g) :
    MvPowerSeries.coeff d (exponentialSymbol g c) =
      d.prod (fun mode k => c mode ^ k / (k.factorial : Scalars)) := by
  classical
  let f : ModeIndex g → ℕ → Scalars := fun mode k => c mode ^ k / (k.factorial : Scalars)
  let F : SymbolSeries g := fun e => e.prod f
  have hf : ∀ mode, f mode 0 = 1 := by intro mode; simp [f]
  have hconstant : MvPowerSeries.constantCoeff F = 1 := by
    change (0 : ModeMonomial g).prod f = 1
    simp
  have hderiv (mode : ModeIndex g) :
      MvPowerSeries.pderiv Scalars mode F = MvPowerSeries.C (c mode) * F := by
    ext e
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C_mul]
    change (e + Finsupp.single mode 1).prod f * ((e mode : Scalars) + 1) = c mode * e.prod f
    have herase : (e + Finsupp.single mode 1).erase mode = e.erase mode := by
      ext j
      by_cases hj : j = mode
      · subst j; simp
      · simp [hj]
    rw [← Finsupp.mul_prod_erase' (e + Finsupp.single mode 1) mode f hf,
      ← Finsupp.mul_prod_erase' e mode f hf, herase,
      Finsupp.add_apply, Finsupp.single_eq_same]
    change (c mode ^ (e mode + 1) / ((e mode + 1).factorial : Scalars) * (e.erase mode).prod f) *
      ((e mode : Scalars) + 1) = c mode *
      (c mode ^ e mode / ((e mode).factorial : Scalars) * (e.erase mode).prod f)
    calc
      _ = ((c mode ^ (e mode + 1) / ((e mode + 1).factorial : Scalars)) *
          ((e mode : Scalars) + 1)) * (e.erase mode).prod f := by ring
      _ = _ := by rw [factorial_factor_step]; ring
  have hF := exponentialSymbol_unique g c F hconstant hderiv
  exact (congrArg (MvPowerSeries.coeff d) hF).symm

end
end FrenkelReshetikhin.D4CounterexampleProof
