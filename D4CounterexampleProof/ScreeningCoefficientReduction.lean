import D4CounterexampleProof.ModeSplitting
import D4CounterexampleProof.ScreenedVacuumCoefficients

/-! Coefficients of the original screening action after the creation and
annihilation mode split. Fourier extraction is eliminated using the
proved degree identity, without assuming a rational residue formula. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance screeningCoefficientReductionField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

abbrev negativeCreationMonomial (d : ModeMonomial D₄) : Variables →₀ ℕ :=
  Finsupp.mapDomain absoluteVariable (negativePart d)

theorem firstCreation_degree (e : Fin 4 →₀ ℕ) :
    weightedDegree creationWeight (Finsupp.embDomain firstCreationEmbedding e) =
      ((Finsupp.degree e : ℕ) : ℤ) := by
  change (Finsupp.embDomain firstCreationEmbedding e).sum
    (fun v k => creationWeight v * (k : ℤ)) = _
  rw [Finsupp.sum_embDomain]
  change e.sum (fun _ k => (1 : ℤ) * (k : ℤ)) = _
  simp [Finsupp.degree_apply, Finsupp.sum, Nat.cast_sum]

/-- A screening summand of degree -1, at the Fourier index prescribed by
the target first-mode monomial, uses precisely the remaining creation
coefficient of the original elementary symbol. -/
theorem screening_normal_term_coefficient (factors : List (InverseRootFactor D₄))
    (e : Fin 4 →₀ ℕ) (d : ModeMonomial D₄) (hd : monomialDegree D₄ d = -1) :
    MvPolynomial.coeff (Finsupp.embDomain firstCreationEmbedding e)
      (negativePolynomial d * vacuumMap 0
        (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) none
          ((((Finsupp.degree e : ℕ) : ℤ) + 1) - positiveDegree D₄ d)
          (vacuum D₄ Scalars Q T 0))) =
      if negativeCreationMonomial d ≤ Finsupp.embDomain firstCreationEmbedding e then
        (elementarySymbol D₄ (1 : Fin 4) factors).coefficients none
          (Finsupp.embDomain creationEmbedding
            (Finsupp.embDomain firstCreationEmbedding e - negativeCreationMonomial d)) else 0 := by
  rw [← MvPolynomial.coeff_coe]
  rw [MvPolynomial.coe_mul, negativePolynomial_monomial, MvPolynomial.coe_monomial,
    MvPowerSeries.coeff_monomial_mul]
  by_cases hle : negativeCreationMonomial d ≤ Finsupp.embDomain firstCreationEmbedding e
  · rw [if_pos hle, if_pos hle, one_mul]
    have hdegree := congrArg (weightedDegree creationWeight) (tsub_add_cancel_of_le hle)
    rw [map_add, firstCreation_degree, negativePolynomial_degree, hd] at hdegree
    change MvPowerSeries.coeff _
      (vacuumMap (chargeEigenvalues D₄ none)
        (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) none
          ((((Finsupp.degree e : ℕ) : ℤ) + 1) - positiveDegree D₄ d)
          (vacuum D₄ Scalars Q T (chargeEigenvalues D₄ none))) :
            MvPowerSeries Variables Scalars) = _
    rw [vacuum_fourierProjection, coeff_fourierProjection]
    have ho := elementarySymbol_offset_zero D₄ (1 : Fin 4) factors
    dsimp only [negativeCreationMonomial] at hdegree
    rw [if_pos (by omega), MvPowerSeries.coeff_killCompl]
    rfl
  · rw [if_neg hle, if_neg hle]

theorem screening_negativePart_single (sign : ScreeningSign) (i : Fin 4)
    (e : Fin 4 →₀ ℕ) (d : ModeMonomial D₄)
    (hc : MvPowerSeries.coeff d (exponentialSymbol D₄
      (fun mode => RatFunc.C (screeningModes (g := D₄) sign i mode.2.val mode.1))) ≠ 0)
    (hle : negativeCreationMonomial d ≤ Finsupp.embDomain firstCreationEmbedding e) :
    ∃ k ≤ e i, negativePart d = Finsupp.single (firstModeEmbedding i) k := by
  have hs : (negativePart d).support ⊆ {firstModeEmbedding i} := by
    intro mode hm
    have hn := negativePart_support d mode hm
    have hm' : mode ∈ d.support := (Finset.mem_filter.mp hm).1
    have hr := screening_coefficient_support_root sign i d hc mode hm'
    have himage : absoluteVariable mode ∈ (negativeCreationMonomial d).support := by
      rw [negativeCreationMonomial, Finsupp.mapDomain_support_of_subsingletonAddUnits]
      exact Finset.mem_image.mpr ⟨mode, hm, rfl⟩
    have ht := Finsupp.support_mono hle himage
    rw [Finsupp.support_embDomain] at ht
    obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp ht
    have hf := congrArg (fun v : Variables => v.2.val) heq
    change 1 = |mode.2.val| at hf
    rw [abs_of_neg hn] at hf
    apply Finset.mem_singleton.mpr
    apply Prod.ext hr
    apply Subtype.ext
    change mode.2.val = -1
    omega
  refine ⟨(negativePart d) (firstModeEmbedding i), ?_, Finsupp.support_subset_singleton.mp hs⟩
  have he := Finsupp.support_subset_singleton.mp hs
  have hh := hle (firstCreationEmbedding i)
  rw [negativeCreationMonomial, he, Finsupp.mapDomain_single] at hh
  change Finsupp.single (firstCreationEmbedding i) _ (firstCreationEmbedding i) ≤ _ at hh
  simpa only [Finsupp.single_eq_same, Finsupp.embDomain_apply_self] using hh

theorem screening_positiveDegree_of_negativePart (i : Fin 4) (d : ModeMonomial D₄)
    (k : ℕ) (hd : monomialDegree D₄ d = -1)
    (hn : negativePart d = Finsupp.single (firstModeEmbedding i) k) :
    positiveDegree D₄ d = k + 1 := by
  have h := monomialDegree_negativePart d
  rw [hn, hd] at h
  have hs : monomialDegree D₄ (Finsupp.single (firstModeEmbedding i) k) = (k : ℤ) := by
    change (Finsupp.single (firstModeEmbedding i) k).sum
      (fun mode l => -mode.2.val * (l : ℤ)) = (k : ℤ)
    rw [Finsupp.sum_single_index (by simp)]
    change -(-1 : ℤ) * (k : ℤ) = (k : ℤ)
    ring
  rw [hs] at h
  omega

def screeningWord (i : Fin 4) (k : ℕ) (p : ModeMonomial D₄) : ModeMonomial D₄ :=
  Finsupp.single (firstModeEmbedding i) k + p

theorem screeningWord_parts (i : Fin 4) (k : ℕ) (p : ModeMonomial D₄)
    (hp : ∀ mode ∈ p.support, 0 < mode.2.val) :
    negativePart (screeningWord i k p) = Finsupp.single (firstModeEmbedding i) k ∧
      positivePart (screeningWord i k p) = p := by
  have hp0 (mode : ModeIndex D₄) (hn : ¬0 < mode.2.val) : p mode = 0 := by
    by_contra h
    exact hn (hp mode (Finsupp.mem_support_iff.mpr h))
  have hsingle (mode : ModeIndex D₄) (hn : 0 < mode.2.val) :
      Finsupp.single (firstModeEmbedding i) k mode = 0 := by
    apply Finsupp.single_eq_of_ne
    intro heq
    have hh := congrArg (fun x : ModeIndex D₄ => x.2.val) heq
    change mode.2.val = -1 at hh
    omega
  constructor
  · ext mode
    rw [negativePart_apply, screeningWord, Finsupp.add_apply]
    by_cases hn : mode.2.val < 0
    · rw [if_pos hn, hp0 mode (by omega), add_zero]
    · have hn' : 0 < mode.2.val := by have := mode.2.property; omega
      rw [if_neg hn, hsingle mode hn']
  · ext mode
    rw [positivePart_apply, screeningWord, Finsupp.add_apply]
    by_cases hn : 0 < mode.2.val
    · rw [if_pos hn, hsingle mode hn, zero_add]
    · rw [if_neg hn, hp0 mode hn]

theorem screeningWord_degree (i : Fin 4) (k : ℕ) (p : ModeMonomial D₄)
    (hp : ∀ mode ∈ p.support, 0 < mode.2.val) :
    monomialDegree D₄ (screeningWord i k p) = (k : ℤ) - positiveDegree D₄ p := by
  rw [screeningWord, monomialDegree_add, monomialDegree_of_positive p hp]
  have hs : monomialDegree D₄ (Finsupp.single (firstModeEmbedding i) k) = (k : ℤ) := by
    change (Finsupp.single (firstModeEmbedding i) k).sum
      (fun mode l => -mode.2.val * (l : ℤ)) = (k : ℤ)
    rw [Finsupp.sum_single_index (by simp)]
    change -(-1 : ℤ) * (k : ℤ) = (k : ℤ)
    ring
  rw [hs]
  ring

theorem screeningWord_positiveDegree (i : Fin 4) (k : ℕ) (p : ModeMonomial D₄)
    (hp : ∀ mode ∈ p.support, 0 < mode.2.val) :
    positiveDegree D₄ (screeningWord i k p) = positiveDegree D₄ p := by
  rw [← positiveDegree_positivePart, (screeningWord_parts i k p hp).2]

theorem screening_coefficient_single (sign : ScreeningSign) (i : Fin 4) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (firstModeEmbedding i) k)
      (exponentialSymbol D₄ (fun mode =>
        RatFunc.C (screeningModes (g := D₄) sign i mode.2.val mode.1))) =
      RatFunc.C (screeningModes (g := D₄) sign i (-1) i) ^ k / (k.factorial : Scalars) := by
  rw [exponentialSymbol_coeff_product, Finsupp.prod_single_index (by simp)]
  rfl

theorem screeningWord_scalar_factorization (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄)) (k : ℕ) (p : ModeMonomial D₄)
    (hp : ∀ mode ∈ p.support, 0 < mode.2.val) :
    MvPowerSeries.coeff (screeningWord i k p) (exponentialSymbol D₄ (fun mode =>
        RatFunc.C (screeningModes (g := D₄) sign i mode.2.val mode.1))) *
      ((annihilationList D₄ (screeningWord i k p)).map (positiveModeScalar factors)).prod =
    (RatFunc.C (screeningModes (g := D₄) sign i (-1) i) ^ k / (k.factorial : Scalars)) *
      (MvPowerSeries.coeff p (exponentialSymbol D₄ (fun mode =>
        RatFunc.C (screeningModes (g := D₄) sign i mode.2.val mode.1))) *
        ((annihilationList D₄ p).map (positiveModeScalar factors)).prod) := by
  rw [exponentialSymbol_coeff_mode_split, annihilationList_scalar_positivePart,
    (screeningWord_parts i k p hp).1, (screeningWord_parts i k p hp).2,
    screening_coefficient_single, annihilationList_scalar_positive factors p hp]
  ring

/-- A single coefficient of the already constructed normal-word action.
This is proof bookkeeping, with both vanishing conditions retained. -/
def screeningSummand (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄)) (e : Fin 4 →₀ ℕ) (d : ModeMonomial D₄) : Scalars :=
  if monomialDegree D₄ d = -1 then
    if negativeCreationMonomial d ≤ Finsupp.embDomain firstCreationEmbedding e then
      MvPowerSeries.coeff d (exponentialSymbol D₄ (fun mode =>
        RatFunc.C (screeningModes (g := D₄) sign i mode.2.val mode.1))) *
      ((annihilationList D₄ d).map (positiveModeScalar factors)).prod *
      (elementarySymbol D₄ (1 : Fin 4) factors).coefficients none
        (Finsupp.embDomain creationEmbedding
          (Finsupp.embDomain firstCreationEmbedding e - negativeCreationMonomial d))
    else 0
  else 0

theorem screeningSummand_nonzero (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄)) (e : Fin 4 →₀ ℕ) (d : ModeMonomial D₄)
    (h : screeningSummand sign i factors e d ≠ 0) :
    monomialDegree D₄ d = -1 ∧
      negativeCreationMonomial d ≤ Finsupp.embDomain firstCreationEmbedding e ∧
      MvPowerSeries.coeff d (exponentialSymbol D₄ (fun mode =>
        RatFunc.C (screeningModes (g := D₄) sign i mode.2.val mode.1))) ≠ 0 := by
  unfold screeningSummand at h
  split_ifs at h with hd hn
  · exact ⟨hd, hn, (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1⟩
  all_goals contradiction

theorem screeningSummand_word (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄)) (e : Fin 4 →₀ ℕ) (k : ℕ)
    (p : ModeMonomial D₄) (hk : k ≤ e i)
    (hp : ∀ mode ∈ p.support, 0 < mode.2.val) (hpk : positiveDegree D₄ p = k + 1) :
    screeningSummand sign i factors e (screeningWord i k p) =
      (RatFunc.C (screeningModes (g := D₄) sign i (-1) i) ^ k / (k.factorial : Scalars)) *
      (MvPowerSeries.coeff p (exponentialSymbol D₄ (fun mode =>
        RatFunc.C (screeningModes (g := D₄) sign i mode.2.val mode.1))) *
        ((annihilationList D₄ p).map (positiveModeScalar factors)).prod) *
      (elementarySymbol D₄ (1 : Fin 4) factors).coefficients none
        (Finsupp.embDomain firstModeEmbedding (e - Finsupp.single i k)) := by
  have hd : monomialDegree D₄ (screeningWord i k p) = -1 := by
    rw [screeningWord_degree i k p hp, hpk]
    omega
  have hn : negativeCreationMonomial (screeningWord i k p) =
      Finsupp.single (firstCreationEmbedding i) k := by
    rw [negativeCreationMonomial, (screeningWord_parts i k p hp).1,
      Finsupp.mapDomain_single]
    rfl
  have hle : negativeCreationMonomial (screeningWord i k p) ≤
      Finsupp.embDomain firstCreationEmbedding e := by
    rw [hn, Finsupp.single_le_iff, Finsupp.embDomain_apply_self]
    exact hk
  rw [screeningSummand, if_pos hd, if_pos hle, screeningWord_scalar_factorization sign i factors k p hp,
    hn, ← Finsupp.embDomain_single, ← Finsupp.embDomain_tsub]
  rw [← Finsupp.embDomain_trans_apply]
  rfl

/-- The actual bounded normal-word sum reindexed by the number of
frequency-one creators and the finite positive-frequency partitions. -/
theorem screeningSummand_reindex (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄)) (e : Fin 4 →₀ ℕ) :
    ∑ d ∈ (finite_absolute_monomials_bounded D₄ (2 * ((Finsupp.degree e : ℕ) + 1))).toFinset,
      screeningSummand sign i factors e d =
    ∑ k ∈ Finset.range (e i + 1),
      ∑ p ∈ (finite_positive_frequency_partitions D₄ (k + 1)).toFinset,
        screeningSummand sign i factors e (screeningWord i k p) := by
  classical
  symm
  rw [Finset.sum_sigma']
  apply Finset.sum_bij_ne_zero (fun kp _ _ => screeningWord i kp.1 kp.2)
  · intro kp hkp hne
    obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp hkp
    have hk' : kp.1 ≤ e i := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    obtain ⟨hpp, hpd⟩ := (finite_positive_frequency_partitions D₄ (kp.1 + 1)).mem_toFinset.mp hp
    apply (finite_absolute_monomials_bounded D₄ _).mem_toFinset.mpr
    have hdeg := screeningWord_degree i kp.1 kp.2 hpp
    have hpos := screeningWord_positiveDegree i kp.1 kp.2 hpp
    have habs := absoluteDegree_identity D₄ (screeningWord i kp.1 kp.2)
    have he := Finsupp.le_degree i e
    rw [hdeg, hpos, hpd] at habs
    change absoluteDegree D₄ (screeningWord i kp.1 kp.2) ≤ 2 * ((Finsupp.degree e : ℕ) + 1)
    omega
  · intro a ha hna b hb hnb heq
    obtain ⟨ha₁, ha₂⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hb₁, hb₂⟩ := Finset.mem_sigma.mp hb
    have hpa := ((finite_positive_frequency_partitions D₄ (a.1 + 1)).mem_toFinset.mp ha₂).1
    have hpb := ((finite_positive_frequency_partitions D₄ (b.1 + 1)).mem_toFinset.mp hb₂).1
    have hn := congrArg negativePart heq
    have hp := congrArg positivePart heq
    rw [(screeningWord_parts i a.1 a.2 hpa).1, (screeningWord_parts i b.1 b.2 hpb).1] at hn
    rw [(screeningWord_parts i a.1 a.2 hpa).2, (screeningWord_parts i b.1 b.2 hpb).2] at hp
    have hk := congrArg (fun d : ModeMonomial D₄ => d (firstModeEmbedding i)) hn
    simp only [Finsupp.single_eq_same] at hk
    exact Sigma.ext hk (heq_of_eq hp)
  · intro d hd hne
    obtain ⟨hdeg, hle, hc⟩ := screeningSummand_nonzero sign i factors e d hne
    obtain ⟨k, hk, hn⟩ := screening_negativePart_single sign i e d hc hle
    have hpk := screening_positiveDegree_of_negativePart i d k hdeg hn
    have hword : screeningWord i k (positivePart d) = d := by
      rw [screeningWord, ← hn, negativePart_add_positivePart]
    refine ⟨⟨k, positivePart d⟩, ?_, ?_, hword⟩
    · apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_range.mpr (by change k < e i + 1; omega), ?_⟩
      apply (finite_positive_frequency_partitions D₄ (k + 1)).mem_toFinset.mpr
      exact ⟨positivePart_support d, by rw [positiveDegree_positivePart, hpk]⟩
    · simpa only [hword] using hne
  · intro kp hkp hne
    rfl

theorem coeff_screenedVacuumProjection_bounded (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄)) (e : Fin 4 →₀ ℕ) :
    MvPowerSeries.coeff e (screenedVacuumProjection sign i
      (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors))) =
    ∑ d ∈ (finite_absolute_monomials_bounded D₄ (2 * ((Finsupp.degree e : ℕ) + 1))).toFinset,
      screeningSummand sign i factors e d := by
  rw [coeff_screenedVacuumProjection sign i _ e]
  change MvPolynomial.coeff (Finsupp.embDomain firstCreationEmbedding e)
    (vacuumMap (chargeEigenvalues D₄ (some (sign, i)))
      (screeningOperator D₄ sign i
        (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors) none
          (((Finsupp.degree e : ℕ) : ℤ) + 1) (vacuum D₄ Scalars Q T 0)))) = _
  have hsum := screening_elementary_fourier_bounded_sum sign i factors
    ((Finsupp.degree e : ℕ) + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hsum
  rw [hsum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdeg : monomialDegree D₄ d = -1
  · rw [if_pos hdeg, MvPolynomial.coeff_smul,
      screening_normal_term_coefficient factors e d hdeg]
    rw [screeningSummand, if_pos hdeg, exponentialSymbol_coeff_product]
    split_ifs <;> simp only [smul_eq_mul, mul_zero]
  · rw [if_neg hdeg, MvPolynomial.coeff_zero, screeningSummand, if_neg hdeg]

/-- The complete first-mode coefficient of the original screening
operator is the finite convolution of the original elementary creation
coefficients and the proved scalar screening series. -/
theorem coeff_screenedVacuumProjection_convolution (sign : ScreeningSign) (i : Fin 4)
    (factors : List (InverseRootFactor D₄)) (e : Fin 4 →₀ ℕ) :
    MvPowerSeries.coeff e (screenedVacuumProjection sign i
      (evaluateSymbol D₄ (elementarySymbol D₄ (1 : Fin 4) factors))) =
    ∑ k ∈ Finset.range (e i + 1),
      (RatFunc.C (screeningModes (g := D₄) sign i (-1) i) ^ k / (k.factorial : Scalars)) *
      RatFunc.C (PowerSeries.coeff (k + 1) ((PowerSeries.exp Coefficient).subst
        (screeningScalarLog sign (monomialOfFactors factors) i))) *
      (elementarySymbol D₄ (1 : Fin 4) factors).coefficients none
        (Finsupp.embDomain firstModeEmbedding (e - Finsupp.single i k)) := by
  rw [coeff_screenedVacuumProjection_bounded, screeningSummand_reindex]
  apply Finset.sum_congr rfl
  intro k hk
  rw [screening_scalar_coefficient_annihilationWords sign factors i (k + 1),
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpp, hpd⟩ := (finite_positive_frequency_partitions D₄ (k + 1)).mem_toFinset.mp hp
  have hk' : k ≤ e i := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [screeningSummand_word sign i factors e k p hk' hpp hpd, exponentialSymbol_coeff_product]

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

