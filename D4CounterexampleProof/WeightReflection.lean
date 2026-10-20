import D4CounterexampleProof.RootLineTrace

/-! Reflection invariance of ordinary weight multiplicities, obtained
from the original quantum commutator and Laurent coefficient independence. -/

namespace FrenkelReshetikhin.OriginalFR.Drinfeld

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable (g : SimpleLieType)

def reflectedWeight (i : RootIndex g) (weight : Weight g) : Weight g :=
  weight - weight i • simpleRoot g i

theorem sameRootLine_coordinate_injective (i : RootIndex g) (base w u : Weight g)
    (hw : sameRootLine g i base w) (hu : sameRootLine g i base u) (heq : w i = u i) : w = u := by
  obtain ⟨n, hn⟩ := hw
  obtain ⟨m, hm⟩ := hu
  have hni := congrFun hn i
  have hmi := congrFun hm i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, simpleRoot, cartan_diagonal] at hni hmi
  have hnm : n = m := by omega
  exact hn.trans ((congrArg (fun k : ℤ => base + k • simpleRoot g i) hnm).trans hm.symm)

theorem reflectedWeight_on_line (i : RootIndex g) (weight : Weight g) :
    sameRootLine g i weight (reflectedWeight g i weight) :=
  ⟨-weight i, by simp only [reflectedWeight, neg_smul, sub_eq_add_neg]⟩

theorem reflectedWeight_coordinate (i : RootIndex g) (weight : Weight g) :
    reflectedWeight g i weight i = -weight i := by
  simp only [reflectedWeight, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    simpleRoot, cartan_diagonal]
  ring

def weightBasisFiberEquiv {d : ℕ} (V : Representation g d) (weight : Weight g) :
    {j : WeightBasisIndex g V // j.1 = weight} ≃ Fin (weightMultiplicity g V weight) where
  toFun j := by rcases j with ⟨⟨w, k⟩, hw⟩; change w = weight at hw; subst w; exact k
  invFun k := ⟨⟨weight, k⟩, rfl⟩
  left_inv := by rintro ⟨⟨w, k⟩, hw⟩; change w = weight at hw; subst w; rfl
  right_inv := by intro k; rfl

theorem sum_weightBasis_fiber {d : ℕ} (V : Representation g d) (hV : TypeOne g V)
    (weight : Weight g) :
    letI : Fintype (WeightBasisIndex g V) := weightBasisFintype g V hV
    (∑ j : WeightBasisIndex g V, if j.1 = weight then (1 : ℂ) else 0) =
      (weightMultiplicity g V weight : ℂ) := by
  classical
  let : Fintype (WeightBasisIndex g V) := weightBasisFintype g V hV
  rw [Finset.sum_boole, ← Fintype.card_subtype]
  rw [Fintype.card_congr (weightBasisFiberEquiv g V weight), Fintype.card_fin]

theorem weightMultiplicity_reflection {d : ℕ} (V : Representation g d) (hV : TypeOne g V)
    (i : RootIndex g) (weight : Weight g) :
    weightMultiplicity g V weight = weightMultiplicity g V (reflectedWeight g i weight) := by
  classical
  let : Fintype (WeightBasisIndex g V) := weightBasisFintype g V hV
  let p := sameRootLine g i weight
  let exponent (j : WeightBasisIndex g V) : ℤ := (rootLength g i : ℤ) * j.1 i
  let left : ℤ →₀ ℂ := ∑ j : WeightBasisIndex g V,
    if p j.1 then Finsupp.single (exponent j) 1 else 0
  let right : ℤ →₀ ℂ := ∑ j : WeightBasisIndex g V,
    if p j.1 then Finsupp.single (-exponent j) 1 else 0
  have he : left = right := by
    apply D4CounterexampleProof.ratLaurentSum_injective ℂ
    dsimp only [left, right]
    simp only [map_sum]
    have hl (j : WeightBasisIndex g V) : D4CounterexampleProof.ratLaurentSum ℂ
        (if p j.1 then Finsupp.single (exponent j) 1 else 0) =
        if p j.1 then quantumQ ^ exponent j else 0 := by
      split_ifs <;> simp only [D4CounterexampleProof.ratLaurentSum_single, map_one, one_mul, map_zero]
      rfl
    have hr (j : WeightBasisIndex g V) : D4CounterexampleProof.ratLaurentSum ℂ
        (if p j.1 then Finsupp.single (-exponent j) 1 else 0) =
        if p j.1 then quantumQ ^ (-exponent j) else 0 := by
      split_ifs <;> simp only [D4CounterexampleProof.ratLaurentSum_single, map_one, one_mul, map_zero]
      rfl
    simp_rw [hl, hr]
    exact rootLine_trace_balance g V hV i weight
  have hcoef := congrArg (fun f : ℤ →₀ ℂ => f ((rootLength g i : ℤ) * weight i)) he
  dsimp only [left, right] at hcoef
  simp only [Finsupp.finsetSum_apply] at hcoef
  have hroot : (rootLength g i : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (rootLength_pos g i)
  have hl (j : WeightBasisIndex g V) :
      (if p j.1 then Finsupp.single (exponent j) (1 : ℂ) else 0)
        ((rootLength g i : ℤ) * weight i) = if j.1 = weight then 1 else 0 := by
    by_cases hp : p j.1
    · rw [if_pos hp, Finsupp.single_apply]
      have hi : exponent j = (rootLength g i : ℤ) * weight i ↔ j.1 = weight := by
        constructor
        · intro hh
          exact sameRootLine_coordinate_injective g i weight j.1 weight hp ⟨0, by simp⟩
            (mul_left_cancel₀ hroot hh)
        · intro hh; simp only [exponent, hh]
      simp only [hi]
    · have hj : j.1 ≠ weight := by intro hh; apply hp; rw [hh]; exact ⟨0, by simp⟩
      rw [if_neg hp, Finsupp.zero_apply, if_neg hj]
  have hr (j : WeightBasisIndex g V) :
      (if p j.1 then Finsupp.single (-exponent j) (1 : ℂ) else 0)
        ((rootLength g i : ℤ) * weight i) =
          if j.1 = reflectedWeight g i weight then 1 else 0 := by
    by_cases hp : p j.1
    · rw [if_pos hp, Finsupp.single_apply]
      have hi : -exponent j = (rootLength g i : ℤ) * weight i ↔
          j.1 = reflectedWeight g i weight := by
        constructor
        · intro hh
          apply sameRootLine_coordinate_injective g i weight j.1 _ hp (reflectedWeight_on_line g i weight)
          rw [reflectedWeight_coordinate]
          apply mul_left_cancel₀ hroot
          dsimp only [exponent] at hh
          rw [mul_neg]
          omega
        · intro hh
          simp only [exponent, hh, reflectedWeight_coordinate, mul_neg, neg_neg]
      simp only [hi]
    · have hj : j.1 ≠ reflectedWeight g i weight := by
        intro hh; apply hp; rw [hh]; exact reflectedWeight_on_line g i weight
      rw [if_neg hp, Finsupp.zero_apply, if_neg hj]
  simp_rw [hl, hr] at hcoef
  rw [sum_weightBasis_fiber, sum_weightBasis_fiber] at hcoef
  exact_mod_cast hcoef

end
end FrenkelReshetikhin.OriginalFR.Drinfeld
