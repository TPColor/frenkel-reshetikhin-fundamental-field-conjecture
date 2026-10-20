import D4CounterexampleProof.CreationPBW
import D4CounterexampleProof.LocalFiniteness
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPowerSeries.Rename

/-! Fourier coefficients on the original vacuum, expressed through the
proved creation-polynomial realization. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance vacuumCoefficientsField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def absoluteVariable (mode : ModeIndex D₄) : Variables :=
  (mode.1, ⟨|mode.2.val|, abs_pos.mpr mode.2.property⟩)

def creationEmbedding : Variables ↪ ModeIndex D₄ where
  toFun v := (v.1, ⟨-v.2.val, neg_ne_zero.mpr (ne_of_gt v.2.property)⟩)
  inj' := by
    intro v w h
    apply Prod.ext
    · exact congrArg (fun mode : ModeIndex D₄ => mode.1) h
    · apply Subtype.ext
      have he := congrArg (fun mode : ModeIndex D₄ => mode.2.val) h
      dsimp at he
      omega

@[simp] theorem absoluteVariable_creationEmbedding (v : Variables) :
    absoluteVariable (creationEmbedding v) = v := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change |(-v.2.val)| = v.2.val
    rw [abs_neg, abs_of_pos v.2.property]

theorem negative_word_representation (charge : RootIndex D₄ → Scalars)
    (xs : List (ModeIndex D₄)) (d : ModeMonomial D₄)
    (hneg : ∀ mode ∈ xs, mode.2.val < 0) :
    representation charge ((xs.map fun mode => rootMode D₄ Scalars Q T mode.1 mode.2.val ^ d mode).prod) =
      Algebra.lmul Scalars Polynomials
        ((xs.map fun mode => MvPolynomial.X (absoluteVariable mode) ^ d mode).prod) := by
  induction xs with
  | nil =>
    change representation charge 1 = Algebra.lmul Scalars Polynomials 1
    rw [map_one, map_one]
  | cons mode xs ih =>
    have hn := hneg mode (by simp)
    have ht : ∀ mode ∈ xs, mode.2.val < 0 := fun mode hm => hneg mode (by simp [hm])
    simp only [List.map_cons, List.prod_cons, map_mul, map_pow, representation_rootMode]
    rw [modeAction_negative charge mode.1 mode.2.val hn, ih ht]
    have hX : creation (mode.1, (⟨-mode.2.val, by omega⟩ : PositiveFrequency)) =
        Algebra.lmul Scalars Polynomials (MvPolynomial.X (absoluteVariable mode)) := by
      apply LinearMap.ext
      intro p
      change MvPolynomial.X (mode.1, (⟨-mode.2.val, by omega⟩ : PositiveFrequency)) * p =
        MvPolynomial.X (absoluteVariable mode) * p
      simp only [absoluteVariable, abs_of_neg hn]
    rw [hX]

theorem vacuumMap_normalWord (charge : Charge D₄) (d : ModeMonomial D₄) :
    vacuumMap (chargeEigenvalues D₄ charge)
      (normalWord D₄ d • vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) =
      if ∃ mode ∈ d.support, 0 < mode.2.val then 0 else
        MvPolynomial.monomial (Finsupp.mapDomain absoluteVariable d) (1 : Scalars) := by
  classical
  by_cases hpos : ∃ mode ∈ d.support, 0 < mode.2.val
  · rw [if_pos hpos, normalWord_vacuum_zero_of_positive D₄ _ d hpos, map_zero]
  · rw [if_neg hpos, vacuumMap_smul_vacuum]
    have hneg : ∀ mode ∈ d.support.toList, mode.2.val < 0 := by
      intro mode hm
      have hs : mode ∈ d.support := by simpa using hm
      have hnonpos : ¬0 < mode.2.val := fun h => hpos ⟨mode, hs, h⟩
      have hn := mode.2.property
      omega
    have hfneg : (d.support.toList.filter fun mode => mode.2.val < 0) = d.support.toList := by
      apply List.filter_eq_self.mpr
      intro mode hm
      simpa using hneg mode hm
    have hfpos : (d.support.toList.filter fun mode => 0 < mode.2.val) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro mode hm
      have hn := hneg mode hm
      simp [show ¬0 < mode.2.val by omega]
    rw [normalWord, hfneg, hfpos, List.map_nil, List.prod_nil, mul_one,
      negative_word_representation (chargeEigenvalues D₄ charge) _ d hneg]
    change (d.support.toList.map fun mode => MvPolynomial.X (absoluteVariable mode) ^ d mode).prod * 1 = _
    rw [mul_one, Finset.prod_map_toList]
    have he := MvPolynomial.rename_monomial absoluteVariable d (1 : Scalars)
    rw [MvPolynomial.monomial_eq] at he
    simpa only [map_mul, map_one, MvPolynomial.C_1, one_mul, Finsupp.prod,
      map_prod, map_pow, MvPolynomial.rename_X] using he

theorem creationEmbedding_no_positive (d : Variables →₀ ℕ) :
    ¬∃ mode ∈ (Finsupp.embDomain creationEmbedding d).support, 0 < mode.2.val := by
  rintro ⟨mode, hm, hp⟩
  rw [Finsupp.support_embDomain] at hm
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hm
  have hn := v.2.property
  change 0 < -v.2.val at hp
  omega

theorem absoluteVariable_embDomain (d : Variables →₀ ℕ) :
    Finsupp.mapDomain absoluteVariable (Finsupp.embDomain creationEmbedding d) = d := by
  rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  have hfun : absoluteVariable ∘ creationEmbedding = id := by
    funext v
    exact absoluteVariable_creationEmbedding v
  rw [hfun, Finsupp.mapDomain_id]

theorem reconstruct_negative_monomial (d : ModeMonomial D₄)
    (hpos : ¬∃ mode ∈ d.support, 0 < mode.2.val) :
    Finsupp.embDomain creationEmbedding (Finsupp.mapDomain absoluteVariable d) = d := by
  rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  calc
    _ = Finsupp.mapDomain id d := by
      apply Finsupp.mapDomain_congr
      intro mode hm
      have hn : mode.2.val < 0 := by
        have hne := mode.2.property
        have hp : ¬0 < mode.2.val := fun h => hpos ⟨mode, hm, h⟩
        omega
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change -|mode.2.val| = mode.2.val
        rw [abs_of_neg hn, neg_neg]
    _ = d := Finsupp.mapDomain_id

def stateCoefficient (charge : Charge D₄) (e : Variables →₀ ℕ) :
    State D₄ charge →ₗ[Scalars] Scalars :=
  (MvPolynomial.lcoeff Scalars e).comp (vacuumMap (chargeEigenvalues D₄ charge))

theorem stateCoefficient_normalWord (charge : Charge D₄) (e : Variables →₀ ℕ)
    (d : ModeMonomial D₄) :
    stateCoefficient charge e (normalWord D₄ d • vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) =
      if d = Finsupp.embDomain creationEmbedding e then 1 else 0 := by
  classical
  change MvPolynomial.coeff e (vacuumMap (chargeEigenvalues D₄ charge)
    (normalWord D₄ d • vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge))) = _
  rw [vacuumMap_normalWord]
  by_cases hp : ∃ mode ∈ d.support, 0 < mode.2.val
  · have hne : d ≠ Finsupp.embDomain creationEmbedding e := by
      intro he
      rw [he] at hp
      exact creationEmbedding_no_positive e hp
    rw [if_pos hp, if_neg hne]
    exact map_zero (MvPolynomial.lcoeff Scalars e)
  · rw [if_neg hp, MvPolynomial.coeff_monomial]
    have heq : Finsupp.mapDomain absoluteVariable d = e ↔
        d = Finsupp.embDomain creationEmbedding e := by
      constructor
      · intro he
        rw [← he]
        exact (reconstruct_negative_monomial d hp).symm
      · rintro rfl
        exact absoluteVariable_embDomain e
    by_cases hd : d = Finsupp.embDomain creationEmbedding e
    · simp [hd, absoluteVariable_embDomain]
    · simp [hd, heq.not.mpr hd]

theorem linearMap_tsum_of_finite {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module Scalars M] [Module Scalars N] [TopologicalSpace M] [TopologicalSpace N]
    (L : M →ₗ[Scalars] N) (f : ι → M) (hf : Function.HasFiniteSupport f) :
    L (∑' i, f i) = ∑' i, L (f i) := by
  classical
  have hz (i : ι) (hi : i ∉ hf.toFinset) : f i = 0 := by
    by_contra h
    exact hi (hf.mem_toFinset.mpr h)
  rw [tsum_eq_sum hz, tsum_eq_sum (fun i hi => by rw [hz i hi, map_zero])]
  exact map_sum L f hf.toFinset

/-- Each vacuum Fourier coefficient recovers exactly the corresponding
creation coefficient of the original normally ordered formal symbol. -/
theorem stateCoefficient_evaluateSymbol (a : NormalSymbol D₄) (charge : Charge D₄)
    (n : ℤ) (e : Variables →₀ ℕ) :
    stateCoefficient charge e
      (evaluateSymbol D₄ a charge n (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge))) =
      if monomialDegree D₄ (Finsupp.embDomain creationEmbedding e) - a.offset = n then
        a.coefficients charge (Finsupp.embDomain creationEmbedding e) else 0 := by
  classical
  let : TopologicalSpace (State D₄ charge) := ⊥
  let : TopologicalSpace Scalars := ⊥
  unfold evaluateSymbol
  rw [linearMap_tsum_of_finite (stateCoefficient charge e) _
    (evaluateSymbol_hasFiniteSupport D₄ a charge n _)]
  rw [tsum_eq_single (Finsupp.embDomain creationEmbedding e)]
  · by_cases hd : monomialDegree D₄ (Finsupp.embDomain creationEmbedding e) - a.offset = n
    · rw [if_pos hd, if_pos hd, map_smul, stateCoefficient_normalWord, if_pos rfl]
      exact smul_eq_mul _ _ |>.trans (mul_one _)
    · rw [if_neg hd, if_neg hd, map_zero]
  · intro d hd
    by_cases hdeg : monomialDegree D₄ d - a.offset = n
    · rw [if_pos hdeg, map_smul, stateCoefficient_normalWord, if_neg hd]
      exact smul_zero _
    · rw [if_neg hdeg, map_zero]

/-- Equality of all actual vacuum coefficients implies equality of the
original symbols after setting annihilation variables to zero. -/
theorem creationSymbol_eq_of_vacuum_coefficients (a b : NormalSymbol D₄) (charge : Charge D₄)
    (hoff : a.offset = b.offset)
    (h : ∀ n : ℤ,
      evaluateSymbol D₄ a charge n (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) =
        evaluateSymbol D₄ b charge n (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge))) :
    MvPowerSeries.killCompl creationEmbedding (a.coefficients charge) =
      MvPowerSeries.killCompl creationEmbedding (b.coefficients charge) := by
  ext e
  rw [MvPowerSeries.coeff_killCompl, MvPowerSeries.coeff_killCompl]
  have he := congrArg (stateCoefficient charge e)
    (h (monomialDegree D₄ (Finsupp.embDomain creationEmbedding e) - a.offset))
  simpa only [stateCoefficient_evaluateSymbol, hoff, if_pos rfl, ite_true,
    MvPowerSeries.coeff_apply] using he

theorem creationSymbol_zero_of_vacuum_coefficients (a : NormalSymbol D₄) (charge : Charge D₄)
    (h : ∀ n : ℤ,
      evaluateSymbol D₄ a charge n (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ charge)) = 0) :
    MvPowerSeries.killCompl creationEmbedding (a.coefficients charge) = 0 := by
  ext e
  rw [MvPowerSeries.coeff_killCompl, map_zero]
  have he := congrArg (stateCoefficient charge e)
    (h (monomialDegree D₄ (Finsupp.embDomain creationEmbedding e) - a.offset))
  simpa only [stateCoefficient_evaluateSymbol, if_pos rfl, ite_true, map_zero,
    MvPowerSeries.coeff_apply] using he

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
