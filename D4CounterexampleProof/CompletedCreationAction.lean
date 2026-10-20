import D4CounterexampleProof.AllModeExponents
import D4CounterexampleProof.CreationFieldIndependence

/-! Extension of the proved positive-mode polynomial action to formal
creation series. Agreement on polynomials is proved below; this does not
replace the original Fock action by a completed action as a definition. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance completedCreationActionField : _root_.Field Coefficient := inferInstance

def completedPositiveAction (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    Module.End Scalars (MvPowerSeries Variables Scalars) :=
  ∑ j : RootIndex D₄, oscillatorCommutator D₄ Scalars Q T i j n (-n) •
    (MvPowerSeries.pderiv Scalars (j, (⟨n, hn⟩ : PositiveFrequency))).toLinearMap

theorem completedPositiveAction_polynomial (i : RootIndex D₄) (n : ℤ) (hn : 0 < n)
    (p : Polynomials) :
    completedPositiveAction i n hn (p : MvPowerSeries Variables Scalars) =
      (positiveAction i n hn p : MvPowerSeries Variables Scalars) := by
  classical
  simp only [completedPositiveAction, positiveAction, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, annihilation_apply]
  change _ = MvPolynomial.coeToMvPowerSeries.ringHom
    (∑ j : RootIndex D₄, oscillatorCommutator D₄ Scalars Q T i j n (-n) •
      MvPolynomial.pderiv (j, (⟨n, hn⟩ : PositiveFrequency)) p)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_smul,
    MvPowerSeries.pderiv_coe]

theorem completedPositiveAction_eigenseries (F : MvPowerSeries Variables Scalars)
    (c : Variables → Scalars)
    (hF : ∀ v, MvPowerSeries.pderiv Scalars v F = MvPowerSeries.C (c v) * F)
    (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    completedPositiveAction i n hn F =
      MvPowerSeries.C (∑ j : RootIndex D₄,
        oscillatorCommutator D₄ Scalars Q T i j n (-n) * c (j, ⟨n, hn⟩)) * F := by
  classical
  simp only [completedPositiveAction, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, hF]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, MvPowerSeries.smul_eq_C_mul, mul_assoc]

/-- Every actual elementary creation series is a joint eigenseries for
the extended positive modes, with its explicitly computed original
all-mode exponents. This supplies individual oscillator contractions for
the global normal-ordering identity. -/
theorem completedPositiveAction_elementary (factors : List (InverseRootFactor D₄))
    (charge : Charge D₄) (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    completedPositiveAction i n hn
      (MvPowerSeries.killCompl creationEmbedding
        ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge)) =
      MvPowerSeries.C (∑ j : RootIndex D₄,
        oscillatorCommutator D₄ Scalars Q T i j n (-n) *
          elementaryModeExponent D₄ (1 : Fin 4) factors (j, ⟨-n, by omega⟩)) *
        MvPowerSeries.killCompl creationEmbedding
          ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) := by
  apply completedPositiveAction_eigenseries _
    (fun v => elementaryModeExponent D₄ (1 : Fin 4) factors (creationEmbedding v))
  intro v
  rw [elementarySymbol_explicit_exponential D₄ (1 : Fin 4) factors charge]
  exact scaled_exponential_creation_pderiv _ _ v

theorem completedPositiveAction_original_state (charge : RootIndex D₄ → Scalars)
    (v : FockModule D₄ Scalars Q T charge) (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    completedPositiveAction i n hn (vacuumMap charge v : MvPowerSeries Variables Scalars) =
      (vacuumMap charge (rootMode D₄ Scalars Q T i n • v) : MvPowerSeries Variables Scalars) := by
  rw [vacuumMap_action, representation_rootMode, modeAction_positive charge i n hn]
  exact completedPositiveAction_polynomial i n hn _

theorem completedPositiveAction_pow_original_state (charge : RootIndex D₄ → Scalars)
    (v : FockModule D₄ Scalars Q T charge) (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) (k : ℕ) :
    (completedPositiveAction i n hn ^ k) (vacuumMap charge v : MvPowerSeries Variables Scalars) =
      (vacuumMap charge ((rootMode D₄ Scalars Q T i n ^ k) • v) : MvPowerSeries Variables Scalars) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, completedPositiveAction_original_state,
      ← mul_smul, ← pow_succ']

theorem completedPositiveActions_commute (i j : RootIndex D₄) (n m : ℤ)
    (hn : 0 < n) (hm : 0 < m) :
    Commute (completedPositiveAction i n hn) (completedPositiveAction j m hm) := by
  change Commute
    (∑ k : RootIndex D₄, oscillatorCommutator D₄ Scalars Q T i k n (-n) •
      differential (k, (⟨n, hn⟩ : PositiveFrequency)))
    (∑ k : RootIndex D₄, oscillatorCommutator D₄ Scalars Q T j k m (-m) •
      differential (k, (⟨m, hm⟩ : PositiveFrequency)))
  apply Commute.sum_left
  intro k hk
  apply Commute.sum_right
  intro l hl
  exact ((differentials_commute (k, (⟨n, hn⟩ : PositiveFrequency))
    (l, (⟨m, hm⟩ : PositiveFrequency))).smul_left _).smul_right _

def completedPositiveWord (xs : List (PositiveMode D₄)) :
    Module.End Scalars (MvPowerSeries Variables Scalars) :=
  (xs.map fun x => completedPositiveAction x.1 (x.2.val : ℤ) (by exact_mod_cast x.2.property)).prod

@[simp] theorem completedPositiveWord_nil : completedPositiveWord [] = 1 := rfl

theorem completedPositiveWord_cons (x : PositiveMode D₄) (xs : List (PositiveMode D₄)) :
    completedPositiveWord (x :: xs) =
      completedPositiveAction x.1 (x.2.val : ℤ) (by exact_mod_cast x.2.property) *
        completedPositiveWord xs := rfl

/-- Finite positive-mode products in the completion agree with the
actual original quotient action on every original Fock state. -/
theorem completedPositiveWord_original_state (charge : RootIndex D₄ → Scalars)
    (v : FockModule D₄ Scalars Q T charge) (xs : List (PositiveMode D₄)) :
    completedPositiveWord xs (vacuumMap charge v : MvPowerSeries Variables Scalars) =
      (vacuumMap charge (positiveWord D₄ xs • v) : MvPowerSeries Variables Scalars) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [completedPositiveWord_cons, Module.End.mul_apply, ih, completedPositiveAction_original_state,
      ← mul_smul, positiveWord_cons]

def elementaryPositiveContraction (factors : List (InverseRootFactor D₄))
    (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) : Scalars :=
  ∑ j : RootIndex D₄, oscillatorCommutator D₄ Scalars Q T i j n (-n) *
    elementaryModeExponent D₄ (1 : Fin 4) factors (j, ⟨-n, by omega⟩)

/-- Every finite annihilation word on an actual elementary creation
series contracts to its product of scalar pairings. Together with the
preceding intertwining theorem this uses the original quotient action. -/
theorem completedPositiveWord_elementary (factors : List (InverseRootFactor D₄))
    (charge : Charge D₄) (xs : List (PositiveMode D₄)) :
    completedPositiveWord xs
      (MvPowerSeries.killCompl creationEmbedding
        ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge)) =
      MvPowerSeries.C ((xs.map fun x =>
        elementaryPositiveContraction factors x.1 (x.2.val : ℤ) (by exact_mod_cast x.2.property)).prod) *
        MvPowerSeries.killCompl creationEmbedding
          ((elementarySymbol D₄ (1 : Fin 4) factors).coefficients charge) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [completedPositiveWord_cons, Module.End.mul_apply, ih]
    rw [← MvPowerSeries.smul_eq_C_mul, map_smul, completedPositiveAction_elementary]
    simp only [List.map_cons, List.prod_cons, map_mul, MvPowerSeries.smul_eq_C_mul,
      elementaryPositiveContraction]
    ring

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
