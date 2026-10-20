import D4CounterexampleProof.CreationIndependence
import D4CounterexampleProof.ElementaryIndependence

/-! Independence of the original elementary fields on the original Fock
vacuum, after the creation-coefficient bridge has been proved. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance creationFieldIndependenceField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem constantCoeff_killCompl {K σ τ : Type*} [CommSemiring K]
    (e : σ ↪ τ) (f : MvPowerSeries τ K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.killCompl e f) = MvPowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_killCompl, Finsupp.embDomain_zero]
  exact MvPowerSeries.coeff_zero_eq_constantCoeff_apply _

theorem scaled_exponential_restricted_pderiv {σ : Type*} (e : σ ↪ ModeIndex D₄)
    (a : Scalars) (c : ModeIndex D₄ → Scalars) (v : σ) :
    MvPowerSeries.pderiv Scalars v
        (MvPowerSeries.killCompl e (MvPowerSeries.C a * exponentialSymbol D₄ c)) =
      MvPowerSeries.C (c (e v)) *
        MvPowerSeries.killCompl e (MvPowerSeries.C a * exponentialSymbol D₄ c) := by
  have hd : MvPowerSeries.pderiv Scalars (e v)
      (MvPowerSeries.C a * exponentialSymbol D₄ c) =
      MvPowerSeries.C (c (e v)) * (MvPowerSeries.C a * exponentialSymbol D₄ c) := by
    rw [Derivation.leibniz, MvPowerSeries.pderiv_C, exponentialSymbol_pderiv]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  rw [pderiv_killCompl, hd, map_mul, MvPowerSeries.killCompl_C]

theorem scaled_exponential_creation_pderiv (a : Scalars)
    (c : ModeIndex D₄ → Scalars) (v : Variables) :
    MvPowerSeries.pderiv Scalars v
        (MvPowerSeries.killCompl creationEmbedding (MvPowerSeries.C a * exponentialSymbol D₄ c)) =
      MvPowerSeries.C (c (creationEmbedding v)) *
        MvPowerSeries.killCompl creationEmbedding (MvPowerSeries.C a * exponentialSymbol D₄ c) :=
  scaled_exponential_restricted_pderiv creationEmbedding a c v

theorem elementary_creation_polynomial_sum_eq_zero {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (hmono : Function.Injective (fun i => monomialOfFactors (factors i)))
    (P : ι → Polynomials)
    (hsum : ∑ i ∈ s, (P i : MvPowerSeries Variables Scalars) *
      MvPowerSeries.killCompl creationEmbedding
        ((elementarySymbol D₄ (1 : Fin 4) (factors i)).coefficients charge) = 0) :
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
  have hci : Function.Injective (fun i : ι => fun v : Variables => c i (creationEmbedding v)) := by
    intro i j hij
    apply hmono
    apply monomialOfFactors_eq_of_normalized_creation (factors i) (factors j) charge charge
    intro k
    erw [hcoeff i (k, ⟨-1, by decide⟩), hcoeff j (k, ⟨-1, by decide⟩)]
    exact congrFun hij (k, ⟨1, by decide⟩)
  apply polynomial_eigenseries_sum_eq_zero s _ _ hci _ _ P hsum
  · intro j v
    rw [hc j]
    exact scaled_exponential_creation_pderiv _ (c j) v
  · intro j hzero
    have he := congrArg MvPowerSeries.constantCoeff hzero
    rw [constantCoeff_killCompl, map_zero] at he
    exact hn j he

/-- A polynomially weighted sum of distinct original elementary symbols
cannot vanish on every vacuum Fourier coefficient. The hypothesis uses
the original `evaluateSymbol` and the original quotient Fock module. -/
theorem elementary_fields_independent_on_vacuum {ι : Type*} (s : Finset ι)
    (factors : ι → List (InverseRootFactor D₄)) (charge : Charge D₄)
    (hmono : Function.Injective (fun i => monomialOfFactors (factors i)))
    (P : ι → Polynomials) :
    let a : NormalSymbol D₄ := ⟨fun inputCharge => ∑ i ∈ s,
      MvPowerSeries.rename creationEmbedding (P i : MvPowerSeries Variables Scalars) *
        (elementarySymbol D₄ (1 : Fin 4) (factors i)).coefficients inputCharge, 0⟩
    (∀ n : ℤ, evaluateSymbol D₄ a charge n
      (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) = 0) → ∀ i ∈ s, P i = 0 := by
  dsimp only
  intro h
  have hz := creationSymbol_zero_of_vacuum_coefficients _ charge h
  apply elementary_creation_polynomial_sum_eq_zero s factors charge hmono P
  simpa only [map_sum, map_mul, MvPowerSeries.killCompl_rename_app] using hz

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
