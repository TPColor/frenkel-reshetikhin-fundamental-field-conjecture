import D4CounterexampleProof.CompletedCreationAction

/-! Weighted Fourier extraction is used only as a proof device. Its
agreement with each Fourier coefficient of the original Fock action is
proved below, before applying the completed oscillator calculations. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance fourierContractionsField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

section General

variable {K σ : Type*} [_root_.Field K]

def weightedDegree (w : σ → ℤ) : (σ →₀ ℕ) →+ ℤ where
  toFun d := d.sum fun i k => w i * (k : ℤ)
  map_zero' := by simp
  map_add' d e := by
    apply Finsupp.sum_add_index'
    · intro i; simp
    · intro i a b; simp [mul_add]

@[simp] theorem weightedDegree_single (w : σ → ℤ) (i : σ) :
    weightedDegree w (Finsupp.single i 1) = w i := by
  change (Finsupp.single i 1 : σ →₀ ℕ).sum (fun j k => w j * (k : ℤ)) = w i
  rw [Finsupp.sum_single_index (by simp)]
  simp

def fourierProjection (w : σ → ℤ) (n : ℤ) :
    MvPowerSeries σ K →ₗ[K] MvPowerSeries σ K where
  toFun F := fun d => if weightedDegree w d = n then MvPowerSeries.coeff d F else 0
  map_add' F G := by
    apply MvPowerSeries.ext
    intro d
    change (if _ then MvPowerSeries.coeff d (F + G) else 0) =
      (if weightedDegree w d = n then MvPowerSeries.coeff d F else 0) +
      (if weightedDegree w d = n then MvPowerSeries.coeff d G else 0)
    by_cases h : weightedDegree w d = n <;> simp [h]
  map_smul' a F := by
    apply MvPowerSeries.ext
    intro d
    change (if _ then MvPowerSeries.coeff d (a • F) else 0) =
      a * (if weightedDegree w d = n then MvPowerSeries.coeff d F else 0)
    by_cases h : weightedDegree w d = n <;> simp [h]

@[simp] theorem coeff_fourierProjection (w : σ → ℤ) (n : ℤ)
    (F : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (fourierProjection w n F) =
      if weightedDegree w d = n then MvPowerSeries.coeff d F else 0 := rfl

theorem pderiv_fourierProjection (w : σ → ℤ) (n : ℤ)
    (F : MvPowerSeries σ K) (i : σ) :
    MvPowerSeries.pderiv K i (fourierProjection w n F) =
      fourierProjection w (n - w i) (MvPowerSeries.pderiv K i F) := by
  apply MvPowerSeries.ext
  intro d
  rw [MvPowerSeries.coeff_pderiv, coeff_fourierProjection,
    coeff_fourierProjection, MvPowerSeries.coeff_pderiv, map_add, weightedDegree_single]
  by_cases h : weightedDegree w d = n - w i
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), zero_mul]

/-- Multiplication by an actual creation monomial shifts the extracted
Fourier degree by its weighted oscillator degree. -/
theorem monomial_fourierProjection (w : σ → ℤ) (n : ℤ)
    (F : MvPowerSeries σ K) (d : σ →₀ ℕ) (a : K) :
    MvPowerSeries.monomial d a * fourierProjection w n F =
      fourierProjection w (n + weightedDegree w d) (MvPowerSeries.monomial d a * F) := by
  classical
  apply MvPowerSeries.ext
  intro e
  simp only [MvPowerSeries.coeff_monomial_mul, coeff_fourierProjection]
  by_cases hde : d ≤ e
  · simp only [if_pos hde]
    have hdegree := congrArg (weightedDegree w) (tsub_add_cancel_of_le hde)
    rw [map_add] at hdegree
    by_cases hn : weightedDegree w (e - d) = n
    · rw [if_pos hn, if_pos (by omega)]
    · rw [if_neg hn, if_neg (by omega), mul_zero]
  · simp only [if_neg hde]
    split_ifs <;> rfl

theorem fourierProjection_idempotent (w : σ → ℤ) (n : ℤ) (F : MvPowerSeries σ K) :
    fourierProjection w n (fourierProjection w n F) = fourierProjection w n F := by
  apply MvPowerSeries.ext
  intro d
  simp only [coeff_fourierProjection]
  split_ifs <;> rfl

theorem X_fourierProjection (w : σ → ℤ) (n : ℤ) (F : MvPowerSeries σ K) (i : σ) :
    MvPowerSeries.X i * fourierProjection w n F =
      fourierProjection w (n + w i) (MvPowerSeries.X i * F) := by
  simpa only [MvPowerSeries.X, weightedDegree_single] using
    monomial_fourierProjection w n F (Finsupp.single i 1) (1 : K)

end General

def creationWeight (v : Variables) : ℤ := v.2.val

theorem creationDegree_eq (e : Variables →₀ ℕ) :
    monomialDegree D₄ (Finsupp.embDomain creationEmbedding e) =
      weightedDegree creationWeight e := by
  rw [monomialDegree, Finsupp.sum_embDomain]
  change e.sum (fun a b => -(creationEmbedding a).2.val * (b : ℤ)) =
    e.sum (fun v k => creationWeight v * (k : ℤ))
  apply Finsupp.sum_congr
  intro v hv
  change -(-v.2.val) * (e v : ℤ) = v.2.val * (e v : ℤ)
  rw [neg_neg]

theorem vacuum_fourierProjection (a : NormalSymbol D₄) (charge : Charge D₄) (n : ℤ) :
    (vacuumMap (chargeEigenvalues D₄ charge)
      (evaluateSymbol D₄ a charge n
        (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge))) :
        MvPowerSeries Variables Scalars) =
      fourierProjection creationWeight (n + a.offset)
        (MvPowerSeries.killCompl creationEmbedding (a.coefficients charge)) := by
  apply MvPowerSeries.ext
  intro e
  rw [MvPolynomial.coeff_coe, coeff_fourierProjection, MvPowerSeries.coeff_killCompl]
  change stateCoefficient charge e (evaluateSymbol D₄ a charge n _) = _
  rw [stateCoefficient_evaluateSymbol, creationDegree_eq]
  by_cases h : weightedDegree creationWeight e = n + a.offset
  · rw [if_pos h, if_pos (by omega)]
    rfl
  · rw [if_neg h, if_neg (by omega)]

/-- A negative original mode on an actual vacuum Fourier state has
exactly the creation-degree shift proved for the formal projection. -/
theorem negativeMode_vacuum_fourierProjection (a : NormalSymbol D₄) (charge : Charge D₄)
    (m : ℤ) (v : Variables) :
    (vacuumMap (chargeEigenvalues D₄ charge)
      (negativeGenerator v • evaluateSymbol D₄ a charge m
        (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge))) :
          MvPowerSeries Variables Scalars) =
      fourierProjection creationWeight (m + a.offset + v.2.val)
        (MvPowerSeries.X v *
          MvPowerSeries.killCompl creationEmbedding (a.coefficients charge)) := by
  rw [← creationPolynomial_X v, vacuumMap_action, representation_creationPolynomial]
  change (((MvPolynomial.X v : Polynomials) * vacuumMap (chargeEigenvalues D₄ charge)
    (evaluateSymbol D₄ a charge m
      (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge))) : Polynomials) :
        MvPowerSeries Variables Scalars) = _
  rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, vacuum_fourierProjection, X_fourierProjection]
  rfl

theorem completedPositiveAction_fourierProjection (F : MvPowerSeries Variables Scalars)
    (m : ℤ) (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    completedPositiveAction i n hn (fourierProjection creationWeight m F) =
      fourierProjection creationWeight (m - n) (completedPositiveAction i n hn F) := by
  simp only [completedPositiveAction, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, pderiv_fourierProjection]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  rfl

/-- A positive mode on an actual original elementary Fourier coefficient
contracts by the previously computed scalar and lowers its Fourier degree
by the mode frequency. This is an identity in the original Fock quotient. -/
theorem positiveMode_elementary_fourier (factors : List (InverseRootFactor D₄))
    (charge : Charge D₄) (m : ℤ) (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    rootMode D₄ Scalars Q T i n •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) charge m
          (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) =
      elementaryPositiveContraction factors i n hn •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) charge (m - n)
          (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) := by
  apply (creationEquiv (chargeEigenvalues D₄ charge)).symm.injective
  change vacuumMap _ _ = vacuumMap _ _
  apply MvPolynomial.coe_injective Variables Scalars
  rw [(vacuumMap (chargeEigenvalues D₄ charge)).map_smul
    (elementaryPositiveContraction factors i n hn)]
  rw [MvPolynomial.coe_smul]
  change (vacuumMap _ _ : MvPowerSeries Variables Scalars) =
    elementaryPositiveContraction factors i n hn • (vacuumMap _ _ : MvPowerSeries Variables Scalars)
  rw [← completedPositiveAction_original_state (chargeEigenvalues D₄ charge) _ i n hn,
    vacuum_fourierProjection,
    completedPositiveAction_fourierProjection, completedPositiveAction_elementary,
    ← MvPowerSeries.smul_eq_C_mul, map_smul, vacuum_fourierProjection]
  rw [show m + (elementarySymbol D₄ (1 : Fin 4) factors).offset - n =
    m - n + (elementarySymbol D₄ (1 : Fin 4) factors).offset by omega]
  rfl

def positiveModeScalar (factors : List (InverseRootFactor D₄)) (x : PositiveMode D₄) : Scalars :=
  elementaryPositiveContraction factors x.1 (x.2.val : ℤ) (by exact_mod_cast x.2.property)

theorem positiveModeScalar_elementary_fourier (factors : List (InverseRootFactor D₄))
    (charge : Charge D₄) (m : ℤ) (x : PositiveMode D₄) :
    rootMode D₄ Scalars Q T x.1 (x.2.val : ℤ) •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) charge m
          (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) =
      positiveModeScalar factors x •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) charge (m - (x.2.val : ℤ))
          (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) :=
  positiveMode_elementary_fourier factors charge m x.1 _ _

set_option backward.isDefEq.respectTransparency false in
/-- The same contraction identity for every finite positive word. -/
theorem positiveWord_elementary_fourier (factors : List (InverseRootFactor D₄))
    (charge : Charge D₄) (m : ℤ) (xs : List (PositiveMode D₄)) :
    positiveWord D₄ xs •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) charge m
          (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) =
      (xs.map (positiveModeScalar factors)).prod •
        evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) charge
          (m - positiveEnergy D₄ xs)
          (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) := by
  induction xs with
  | nil =>
    simp only [positiveWord_nil, one_smul, List.map_nil, List.prod_nil,
      positiveEnergy_nil, Nat.cast_zero, sub_zero]
    exact (one_smul Scalars (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors)
      charge m (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)))).symm
  | cons x xs ih =>
    rw [positiveWord_cons, mul_smul, ih, smul_comm,
      positiveModeScalar_elementary_fourier factors charge _ x]
    have hs (a b : Scalars) (v : State D₄ charge) : a • (b • v) = (a * b) • v :=
      (mul_smul a b v).symm
    rw [hs]
    simp only [List.map_cons, List.prod_cons, positiveEnergy_cons, Nat.cast_add]
    rw [mul_comm]
    congr 1
    congr 1
    omega

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
