import D4CounterexampleProof.FourierContractions
import D4CounterexampleProof.FirstCreationModes
import D4CounterexampleProof.ScreeningExpansion

/-! First-mode Fourier coefficients of the actual original screening
action, and the zero sum furnished by the original W-centralizer. This
does not identify that action with a sum of local rational residues. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screenedVacuumCoefficientsField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

section General

variable {K σ τ : Type*} [_root_.Field K]

theorem weightedDegree_embDomain (w : τ → ℤ) (e : σ ↪ τ) (d : σ →₀ ℕ) :
    weightedDegree w (Finsupp.embDomain e d) = weightedDegree (w ∘ e) d := by
  change (Finsupp.embDomain e d).sum (fun i k => w i * (k : ℤ)) = _
  rw [Finsupp.sum_embDomain]
  rfl

theorem killCompl_fourierProjection (w : τ → ℤ) (e : σ ↪ τ) (n : ℤ)
    (F : MvPowerSeries τ K) :
    MvPowerSeries.killCompl e (fourierProjection w n F) =
      fourierProjection (w ∘ e) n (MvPowerSeries.killCompl e F) := by
  apply MvPowerSeries.ext
  intro d
  rw [MvPowerSeries.coeff_killCompl, coeff_fourierProjection, coeff_fourierProjection,
    MvPowerSeries.coeff_killCompl, weightedDegree_embDomain]

end General

theorem vacuum_firstMode_fourierProjection (a : NormalSymbol D₄) (charge : Charge D₄) (n : ℤ) :
    MvPowerSeries.killCompl firstCreationEmbedding
      (vacuumMap (chargeEigenvalues D₄ charge)
        (evaluateSymbol D₄ a charge n
          (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge))) :
            MvPowerSeries Variables Scalars) =
      fourierProjection (fun _ : Fin 4 => (1 : ℤ)) (n + a.offset)
        (MvPowerSeries.killCompl firstModeEmbedding (a.coefficients charge)) := by
  rw [vacuum_fourierProjection, killCompl_fourierProjection,
    firstModeEmbedding, killCompl_trans]
  rfl

/-- A proof-only linear extraction from the original field and original
screening action. The input Fourier index is total first-mode degree + 1,
as required for a screening residue of degree -1. -/
def screenedVacuumProjection (sign : ScreeningSign) (i : RootIndex D₄) :
    Field D₄ →ₗ[Scalars] MvPowerSeries (Fin 4) Scalars where
  toFun f := fun e =>
    stateCoefficient (some (sign, i)) (Finsupp.embDomain firstCreationEmbedding e)
      (screeningOperator D₄ sign i
        (f none (((Finsupp.degree e : ℕ) : ℤ) + 1) (vacuum D₄ Scalars Q T 0)))
  map_add' f g := by
    apply MvPowerSeries.ext
    intro e
    change stateCoefficient (some (sign, i)) _
      (screeningOperator D₄ sign i (_ + _)) = _
    rw [screeningOperator_add, map_add]
    rfl
  map_smul' c f := by
    apply MvPowerSeries.ext
    intro e
    change stateCoefficient (some (sign, i)) _
      (screeningOperator D₄ sign i (c • _)) = _
    rw [screeningOperator_smul, map_smul]
    rfl

@[simp] theorem coeff_screenedVacuumProjection (sign : ScreeningSign) (i : RootIndex D₄)
    (f : Field D₄) (e : Fin 4 →₀ ℕ) :
    MvPowerSeries.coeff e (screenedVacuumProjection sign i f) =
      stateCoefficient (some (sign, i)) (Finsupp.embDomain firstCreationEmbedding e)
        (screeningOperator D₄ sign i
          (f none (((Finsupp.degree e : ℕ) : ℤ) + 1) (vacuum D₄ Scalars Q T 0))) := rfl

/-- The zero creation-series premise is obtained directly from the
original W-centralizer, using only coefficients of actual Fock states. -/
theorem screenedVacuumProjection_deformedW (f : Field D₄) (hf : f ∈ deformedW D₄)
    (sign : ScreeningSign) (i : RootIndex D₄) : screenedVacuumProjection sign i f = 0 := by
  apply MvPowerSeries.ext
  intro e
  rw [coeff_screenedVacuumProjection,
    deformedW_screening_vacuum D₄ f hf sign i, map_zero, map_zero]

/-- The exact finite zero sum of original screened elementary fields
used by the global residue reindexing in `ScreeningCoefficientReduction.lean`. -/
theorem fundamentalExpansion_screenedVacuum_zero (terms : List (ElementaryTerm D₄))
    (hW : fundamentalExpansion D₄ (1 : Fin 4) terms ∈ deformedW D₄)
    (sign : ScreeningSign) (i : RootIndex D₄) :
    screenedVacuumProjection sign i (evaluateSymbol D₄ (weightVertex D₄ (1 : Fin 4) false 0 0)) +
      (terms.map fun term => RatFunc.C term.coefficient •
        screenedVacuumProjection sign i
          (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) term.factors))).sum = 0 := by
  have h := screenedVacuumProjection_deformedW _ hW sign i
  unfold fundamentalExpansion at h
  rw [map_add] at h
  rw [map_list_sum (screenedVacuumProjection sign i)
    (terms.map fun term => RatFunc.C term.coefficient •
      evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) term.factors))] at h
  simpa only [List.map_map, Function.comp_def, map_smul] using h

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
