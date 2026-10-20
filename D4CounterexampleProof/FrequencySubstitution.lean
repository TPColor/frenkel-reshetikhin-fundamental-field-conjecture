import D4CounterexampleProof.ExponentialSubstitution
import D4CounterexampleProof.ExponentialCoefficients
import D4CounterexampleProof.LocalFiniteness

/-! Legitimate coefficientwise substitution of positive oscillator
variables by powers of the field-argument ratio. Finiteness at each
frequency follows from the finite root index set. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance frequencySubstitutionField : Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def positiveFrequencyFamily (g : SimpleLieType) (a : ModeIndex g → Scalars)
    (mode : ModeIndex g) : PowerSeries Scalars :=
  if 0 < mode.2.val then PowerSeries.monomial mode.2.val.natAbs (a mode) else 0

theorem positiveFrequencyFamily_hasSubst (g : SimpleLieType) (a : ModeIndex g → Scalars) :
    MvPowerSeries.HasSubst (positiveFrequencyFamily g a) where
  const_coeff mode := by
    have hn : mode.2.val.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr mode.2.property
    change IsNilpotent (PowerSeries.constantCoeff (positiveFrequencyFamily g a mode))
    suffices PowerSeries.constantCoeff (positiveFrequencyFamily g a mode) = 0 by
      rw [this]; exact IsNilpotent.zero
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    by_cases hp : 0 < mode.2.val
    · simp [positiveFrequencyFamily, hp, PowerSeries.coeff_monomial, Ne.symm hn]
    · simp [positiveFrequencyFamily, hp]
  coeff_zero d := by
    apply (finite_modes_bounded g (d ())).subset
    intro mode hm
    by_cases hp : 0 < mode.2.val
    · change MvPowerSeries.coeff d (positiveFrequencyFamily g a mode) ≠ 0 at hm
      unfold positiveFrequencyFamily at hm
      rw [if_pos hp] at hm
      have hd : d = Finsupp.single () mode.2.val.natAbs := by
        by_contra hne
        exact hm (MvPowerSeries.coeff_monomial _ _ _ |>.trans (if_neg hne))
      have hvalue : d () = mode.2.val.natAbs := by simp [hd]
      have habs : |mode.2.val| ≤ (d () : ℤ) := by
        rw [hvalue, Int.natCast_natAbs]
      exact abs_le.mp habs
    · exact False.elim (hm (by simp [positiveFrequencyFamily, hp]))

theorem positiveFrequencyFamily_coeff (g : SimpleLieType) (a : ModeIndex g → Scalars)
    (mode : ModeIndex g) (n : ℕ) :
    PowerSeries.coeff n (positiveFrequencyFamily g a mode) =
      if mode.2.val = (n : ℤ) ∧ 0 < n then a mode else 0 := by
  by_cases hp : 0 < mode.2.val
  · rw [positiveFrequencyFamily, if_pos hp, PowerSeries.coeff_monomial]
    have he : n = mode.2.val.natAbs ↔ mode.2.val = (n : ℤ) ∧ 0 < n := by
      constructor
      · intro h
        constructor
        · rw [h, Int.natCast_natAbs, abs_of_pos hp]
        · rw [h]; exact Int.natAbs_pos.mpr mode.2.property
      · intro h
        rw [h.1, Int.natAbs_natCast]
    simp only [he]
  · rw [positiveFrequencyFamily, if_neg hp, map_zero]
    rw [if_neg (by rintro ⟨he, hn⟩; exact hp (he ▸ by exact_mod_cast hn))]

def positiveFrequencyEmbedding (g : SimpleLieType) (n : ℕ) (hn : 0 < n) :
    RootIndex g ↪ ModeIndex g where
  toFun i := (i, ⟨(n : ℤ), by exact_mod_cast (ne_of_gt hn)⟩)
  inj' := by intro i j h; exact congrArg Prod.fst h

/-- At a given positive frequency the substituted original linear
symbol has the finite sum of its rootwise contraction coefficients. -/
theorem linearSymbol_positiveFrequency_coeff (g : SimpleLieType)
    (c a : ModeIndex g → Scalars) (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n ((linearSymbol g c).subst (positiveFrequencyFamily g a)) =
      ∑ i : RootIndex g, c (positiveFrequencyEmbedding g n hn i) *
        a (positiveFrequencyEmbedding g n hn i) := by
  classical
  rw [PowerSeries.coeff, linearSymbol_coeff_subst g c _ (positiveFrequencyFamily_hasSubst g a)]
  change (∑ᶠ mode, c mode * PowerSeries.coeff n (positiveFrequencyFamily g a mode)) = _
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.map (positiveFrequencyEmbedding g n hn))]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i hi
    rw [positiveFrequencyFamily_coeff, if_pos]
    exact ⟨rfl, hn⟩
  · intro mode hm
    change c mode * PowerSeries.coeff n (positiveFrequencyFamily g a mode) ≠ 0 at hm
    rw [positiveFrequencyFamily_coeff] at hm
    have he : mode.2.val = (n : ℤ) := by
      by_contra hne
      exact hm (by simp [hne])
    apply Finset.mem_map.mpr
    refine ⟨mode.1, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · exact Subtype.ext he.symm

theorem linearSymbol_positiveFrequency_constantCoeff (g : SimpleLieType)
    (c a : ModeIndex g → Scalars) :
    PowerSeries.constantCoeff ((linearSymbol g c).subst (positiveFrequencyFamily g a)) = 0 := by
  change MvPowerSeries.constantCoeff _ = 0
  apply MvPowerSeries.constantCoeff_subst_eq_zero (positiveFrequencyFamily_hasSubst g a)
  · intro mode
    change PowerSeries.constantCoeff (positiveFrequencyFamily g a mode) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [positiveFrequencyFamily_coeff]
  · exact linearSymbol_constantCoeff g c

def positiveFrequencyLog (g : SimpleLieType) (c a : ModeIndex g → Scalars) : PowerSeries Scalars :=
  PowerSeries.mk fun n => if hn : 0 < n then
    ∑ i : RootIndex g, c (positiveFrequencyEmbedding g n hn i) *
      a (positiveFrequencyEmbedding g n hn i) else 0

theorem linearSymbol_positiveFrequency_eq (g : SimpleLieType)
    (c a : ModeIndex g → Scalars) :
    (linearSymbol g c).subst (positiveFrequencyFamily g a) = positiveFrequencyLog g c a := by
  apply PowerSeries.ext
  intro n
  rw [positiveFrequencyLog, PowerSeries.coeff_mk]
  by_cases hn : 0 < n
  · rw [dif_pos hn]
    exact linearSymbol_positiveFrequency_coeff g c a n hn
  · have hn0 : n = 0 := by omega
    subst n
    rw [dif_neg (by omega), PowerSeries.coeff_zero_eq_constantCoeff_apply,
      linearSymbol_positiveFrequency_constantCoeff]

/-- The scalar frequency generating function of the original formal
exponential is the exponential of the computed finite root sums. -/
theorem exponentialSymbol_positiveFrequency (g : SimpleLieType)
    (c a : ModeIndex g → Scalars) :
    (exponentialSymbol g c).subst (positiveFrequencyFamily g a) =
      (PowerSeries.exp Scalars).subst (positiveFrequencyLog g c a) := by
  rw [exponentialSymbol_subst g c _ (positiveFrequencyFamily_hasSubst g a),
    linearSymbol_positiveFrequency_eq]

theorem positiveFrequencyFamily_prod (g : SimpleLieType) (a : ModeIndex g → Scalars)
    (d : ModeMonomial g) (hp : ∀ mode ∈ d.support, 0 < mode.2.val) :
    d.prod (fun mode k => positiveFrequencyFamily g a mode ^ k) =
      PowerSeries.monomial (positiveDegree g d) (d.prod fun mode k => a mode ^ k) := by
  classical
  change (∏ mode ∈ d.support, positiveFrequencyFamily g a mode ^ d mode) = _
  calc
    _ = ∏ mode ∈ d.support,
        PowerSeries.monomial (d mode * mode.2.val.natAbs) (a mode ^ d mode) := by
      apply Finset.prod_congr rfl
      intro mode hm
      rw [positiveFrequencyFamily, if_pos (hp mode hm), PowerSeries.monomial_pow]
    _ = PowerSeries.monomial (∑ mode ∈ d.support, d mode * mode.2.val.natAbs)
        (d.prod fun mode k => a mode ^ k) := PowerSeries.prod_monomial _ _ _
    _ = _ := by
      have hd : (∑ mode ∈ d.support, d mode * mode.2.val.natAbs) = positiveDegree g d := by
        change (∑ mode ∈ d.support, d mode * mode.2.val.natAbs) =
          ∑ mode ∈ d.support, if 0 < mode.2.val then mode.2.val.natAbs * d mode else 0
        apply Finset.sum_congr rfl
        intro mode hm
        rw [if_pos (hp mode hm), Nat.mul_comm]
      rw [hd]

theorem positiveFrequencyFamily_prod_zero (g : SimpleLieType) (a : ModeIndex g → Scalars)
    (d : ModeMonomial g) (hp : ∃ mode ∈ d.support, ¬0 < mode.2.val) :
    d.prod (fun mode k => positiveFrequencyFamily g a mode ^ k) = 0 := by
  classical
  obtain ⟨mode, hm, hn⟩ := hp
  change (∏ j ∈ d.support, positiveFrequencyFamily g a j ^ d j) = 0
  apply Finset.prod_eq_zero hm
  change positiveFrequencyFamily g a mode ^ d mode = 0
  rw [positiveFrequencyFamily, if_neg hn, zero_pow (Finsupp.mem_support_iff.mp hm)]

theorem positiveFrequencyFamily_prod_coeff (g : SimpleLieType) (a : ModeIndex g → Scalars)
    (d : ModeMonomial g) (n : ℕ) :
    PowerSeries.coeff n (d.prod fun mode k => positiveFrequencyFamily g a mode ^ k) =
      if (∀ mode ∈ d.support, 0 < mode.2.val) ∧ positiveDegree g d = n then
        d.prod (fun mode k => a mode ^ k) else 0 := by
  classical
  by_cases hp : ∀ mode ∈ d.support, 0 < mode.2.val
  · rw [positiveFrequencyFamily_prod g a d hp, PowerSeries.coeff_monomial]
    by_cases hd : positiveDegree g d = n
    · rw [if_pos hd.symm, if_pos ⟨hp, hd⟩]
    · rw [if_neg (Ne.symm hd), if_neg (by tauto)]
  · have he : ∃ mode ∈ d.support, ¬0 < mode.2.val := by simpa using hp
    rw [positiveFrequencyFamily_prod_zero g a d he, map_zero, if_neg (by tauto)]

/-- Explicit weighted partition formula for the positive-mode scalar
contraction of the original exponential. The factorials come from the
proved coefficients of that original definition. -/
theorem exponentialSymbol_positiveFrequency_coeff (g : SimpleLieType)
    (c a : ModeIndex g → Scalars) (n : ℕ) :
    PowerSeries.coeff n ((exponentialSymbol g c).subst (positiveFrequencyFamily g a)) =
      ∑ᶠ d : ModeMonomial g,
        if (∀ mode ∈ d.support, 0 < mode.2.val) ∧ positiveDegree g d = n then
          (d.prod fun mode k => c mode ^ k / (k.factorial : Scalars)) *
            (d.prod fun mode k => a mode ^ k) else 0 := by
  classical
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst (positiveFrequencyFamily_hasSubst g a)]
  apply finsum_congr
  intro d
  change MvPowerSeries.coeff d (exponentialSymbol g c) •
    PowerSeries.coeff n (d.prod fun mode k => positiveFrequencyFamily g a mode ^ k) = _
  rw [positiveFrequencyFamily_prod_coeff, exponentialSymbol_coeff_product]
  split_ifs <;> simp only [smul_eq_mul, mul_zero]

/-- The weighted partitions at a fixed frequency are genuinely finite,
independently of any coefficients that may happen to vanish. -/
theorem finite_positive_frequency_partitions (g : SimpleLieType) (n : ℕ) :
    {d : ModeMonomial g | (∀ mode ∈ d.support, 0 < mode.2.val) ∧
      positiveDegree g d = n}.Finite := by
  apply (finite_absolute_monomials_bounded g n).subset
  rintro d ⟨hp, hd⟩
  have he : absoluteDegree g d = positiveDegree g d := by
    apply Finsupp.sum_congr
    intro mode hm
    exact (if_pos (hp mode hm)).symm
  change absoluteDegree g d ≤ n
  omega

theorem exponentialSymbol_positiveFrequency_coeff_finite (g : SimpleLieType)
    (c a : ModeIndex g → Scalars) (n : ℕ) :
    PowerSeries.coeff n ((exponentialSymbol g c).subst (positiveFrequencyFamily g a)) =
      ∑ d ∈ (finite_positive_frequency_partitions g n).toFinset,
        (d.prod fun mode k => c mode ^ k / (k.factorial : Scalars)) *
          (d.prod fun mode k => a mode ^ k) := by
  classical
  rw [exponentialSymbol_positiveFrequency_coeff]
  rw [finsum_eq_sum_of_support_subset (s := (finite_positive_frequency_partitions g n).toFinset)]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [Set.Finite.mem_toFinset] at hd
    exact if_pos hd
  · intro d hd
    change d ∈ (finite_positive_frequency_partitions g n).toFinset
    rw [Set.Finite.mem_toFinset]
    change (if (∀ mode ∈ d.support, 0 < mode.2.val) ∧ positiveDegree g d = n then
      (d.prod fun mode k => c mode ^ k / (k.factorial : Scalars)) *
        (d.prod fun mode k => a mode ^ k) else 0) ≠ 0 at hd
    change (∀ mode ∈ d.support, 0 < mode.2.val) ∧ positiveDegree g d = n
    by_contra hn
    exact hd (if_neg hn)

end
end FrenkelReshetikhin.D4CounterexampleProof
