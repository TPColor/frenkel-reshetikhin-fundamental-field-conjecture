import D4CounterexampleProof.AnnihilationPartitions

/-! Splitting an actual normally ordered mode monomial into its creation
and annihilation parts. These are finite-support projections used in the
reindexing proof; the original normal ordering and actions are unchanged. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance modeSplittingField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def negativePart (d : ModeMonomial D₄) : ModeMonomial D₄ :=
  d.filter fun mode => mode.2.val < 0

def positivePart (d : ModeMonomial D₄) : ModeMonomial D₄ :=
  d.filter fun mode => 0 < mode.2.val

@[simp] theorem negativePart_apply (d : ModeMonomial D₄) (mode : ModeIndex D₄) :
    negativePart d mode = if mode.2.val < 0 then d mode else 0 := rfl

@[simp] theorem positivePart_apply (d : ModeMonomial D₄) (mode : ModeIndex D₄) :
    positivePart d mode = if 0 < mode.2.val then d mode else 0 := rfl

theorem negativePart_add_positivePart (d : ModeMonomial D₄) :
    negativePart d + positivePart d = d := by
  ext mode
  have hn := mode.2.property
  by_cases hp : 0 < mode.2.val
  · simp [hp, show ¬mode.2.val < 0 by omega]
  · simp [hp, show mode.2.val < 0 by omega]

theorem negativePart_support (d : ModeMonomial D₄) (mode : ModeIndex D₄)
    (hm : mode ∈ (negativePart d).support) : mode.2.val < 0 := by
  exact (Finset.mem_filter.mp hm).2

theorem positivePart_support (d : ModeMonomial D₄) (mode : ModeIndex D₄)
    (hm : mode ∈ (positivePart d).support) : 0 < mode.2.val := by
  exact (Finset.mem_filter.mp hm).2

theorem mode_parts_disjoint (d : ModeMonomial D₄) :
    Disjoint (negativePart d).support (positivePart d).support := by
  apply Finset.disjoint_left.mpr
  intro mode hn hp
  have := negativePart_support d mode hn
  have := positivePart_support d mode hp
  omega

theorem exponentialSymbol_coeff_mode_split (c : ModeIndex D₄ → Scalars)
    (d : ModeMonomial D₄) :
    MvPowerSeries.coeff d (exponentialSymbol D₄ c) =
      MvPowerSeries.coeff (negativePart d) (exponentialSymbol D₄ c) *
        MvPowerSeries.coeff (positivePart d) (exponentialSymbol D₄ c) := by
  simp only [exponentialSymbol_coeff_product]
  rw [← Finsupp.prod_add_index_of_disjoint (mode_parts_disjoint d),
    negativePart_add_positivePart]

theorem annihilationList_scalar_positivePart (factors : List (InverseRootFactor D₄))
    (d : ModeMonomial D₄) :
    ((annihilationList D₄ d).map (positiveModeScalar factors)).prod =
      (positivePart d).prod (fun mode k => elementaryContractionFamily factors mode ^ k) := by
  have hprod (xs : List (ModeIndex D₄)) :
      ((xs.flatMap fun mode => List.replicate (d mode) (absoluteMode D₄ mode)).map
        (positiveModeScalar factors)).prod =
      (xs.map fun mode => positiveModeScalar factors (absoluteMode D₄ mode) ^ d mode).prod := by
    induction xs with
    | nil => simp
    | cons mode xs ih => simp [ih]
  have hf (xs : List (ModeIndex D₄)) :
      ((xs.filter fun mode => 0 < mode.2.val).map fun mode =>
        positiveModeScalar factors (absoluteMode D₄ mode) ^ d mode).prod =
      (xs.map fun mode => if 0 < mode.2.val then
        elementaryContractionFamily factors mode ^ d mode else (1 : Scalars)).prod := by
    induction xs with
    | nil => simp
    | cons mode xs ih =>
      by_cases hp : 0 < mode.2.val
      · simp [hp, ih, positiveModeScalar_absolute factors mode hp]
      · simp [hp, ih]
  rw [annihilationList, hprod, hf, Finset.prod_map_toList]
  rw [positivePart, Finsupp.prod_filter_index, Finsupp.support_filter, Finset.prod_filter]

theorem screening_coefficient_support_root (sign : ScreeningSign) (i : RootIndex D₄)
    (d : ModeMonomial D₄)
    (hc : MvPowerSeries.coeff d (exponentialSymbol D₄
      (fun mode => RatFunc.C (screeningModes sign i mode.2.val mode.1))) ≠ 0)
    (mode : ModeIndex D₄) (hm : mode ∈ d.support) : mode.1 = i := by
  rw [exponentialSymbol_coeff_product] at hc
  have ht := Finset.prod_ne_zero_iff.mp hc mode hm
  by_contra hroot
  have hz : screeningModes (g := D₄) sign i mode.2.val mode.1 = 0 := by
    cases sign <;> simp [screeningModes, hroot]
  simp [hz, Finsupp.mem_support_iff.mp hm] at ht

theorem negativePolynomial_negativePart (d : ModeMonomial D₄) :
    negativePolynomial d = (negativePart d).prod
      (fun mode k => MvPolynomial.X (absoluteVariable mode) ^ k) := by
  classical
  have hf (xs : List (ModeIndex D₄)) :
      ((xs.filter fun mode => mode.2.val < 0).map fun mode =>
        MvPolynomial.X (absoluteVariable mode) ^ d mode).prod =
      (xs.map fun mode => if mode.2.val < 0 then
        MvPolynomial.X (absoluteVariable mode) ^ d mode else (1 : Polynomials)).prod := by
    induction xs with
    | nil => simp
    | cons mode xs ih => by_cases hn : mode.2.val < 0 <;> simp [hn, ih]
  rw [negativePolynomial, hf, Finset.prod_map_toList]
  rw [negativePart, Finsupp.prod_filter_index, Finsupp.support_filter, Finset.prod_filter]

theorem negativePolynomial_monomial (d : ModeMonomial D₄) :
    negativePolynomial d =
      MvPolynomial.monomial (Finsupp.mapDomain absoluteVariable (negativePart d)) (1 : Scalars) := by
  rw [negativePolynomial_negativePart]
  have he := MvPolynomial.rename_monomial absoluteVariable (negativePart d) (1 : Scalars)
  rw [MvPolynomial.monomial_eq] at he
  simpa only [map_mul, map_one, MvPolynomial.C_1, one_mul, Finsupp.prod,
    map_prod, map_pow, MvPolynomial.rename_X] using he

theorem monomialDegree_add (d e : ModeMonomial D₄) :
    monomialDegree D₄ (d + e) = monomialDegree D₄ d + monomialDegree D₄ e := by
  apply Finsupp.sum_add_index'
  · intro mode; simp
  · intro mode a b; simp [mul_add]

theorem positiveDegree_positivePart (d : ModeMonomial D₄) :
    positiveDegree D₄ (positivePart d) = positiveDegree D₄ d := by
  rw [positiveDegree, positivePart, Finsupp.sum_filter_index,
    Finsupp.support_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mode hm
  dsimp only
  split_ifs <;> rfl

theorem monomialDegree_of_positive (d : ModeMonomial D₄)
    (hp : ∀ mode ∈ d.support, 0 < mode.2.val) :
    monomialDegree D₄ d = -(positiveDegree D₄ d : ℤ) := by
  simp only [monomialDegree, positiveDegree, Finsupp.sum, Nat.cast_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro mode hm
  rw [if_pos (hp mode hm), Nat.cast_mul, Int.natCast_natAbs, abs_of_pos (hp mode hm)]
  ring

theorem monomialDegree_negativePart (d : ModeMonomial D₄) :
    monomialDegree D₄ (negativePart d) = monomialDegree D₄ d + positiveDegree D₄ d := by
  have h := monomialDegree_add (negativePart d) (positivePart d)
  rw [negativePart_add_positivePart,
    monomialDegree_of_positive _ (positivePart_support d), positiveDegree_positivePart] at h
  omega

theorem negativePolynomial_degree (d : ModeMonomial D₄) :
    weightedDegree creationWeight (Finsupp.mapDomain absoluteVariable (negativePart d)) =
      monomialDegree D₄ d + positiveDegree D₄ d := by
  rw [← monomialDegree_negativePart]
  change (Finsupp.mapDomain absoluteVariable (negativePart d)).sum
    (fun v k => creationWeight v * (k : ℤ)) = _
  rw [Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro mode hm
    have hn := negativePart_support d mode hm
    change |mode.2.val| * ((negativePart d) mode : ℤ) = -mode.2.val * ((negativePart d) mode : ℤ)
    rw [abs_of_neg hn]
  · intro v; simp
  · intro v a b; simp [mul_add]

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
