import D4CounterexampleProof.AllModeContractions
import D4CounterexampleProof.HeisenbergCoefficients

/-! Spectral moments at every oscillator frequency, derived from the
finite Laurent monomials and related to the original deformed Cartan
matrix and oscillator contractions. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance frequencyMomentsField : _root_.Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

def frequencyMoment (m : Monomial) (i : Fin 4) (n : ℤ) : Coefficient :=
  m.sum fun key k => if key.1 = i then (k : Coefficient) *
    (q ^ key.2.1 * t ^ key.2.2) ^ n else 0

@[simp] theorem frequencyMoment_zero (i : Fin 4) (n : ℤ) : frequencyMoment 0 i n = 0 := by
  simp [frequencyMoment]

theorem frequencyMoment_add (m l : Monomial) (i : Fin 4) (n : ℤ) :
    frequencyMoment (m + l) i n = frequencyMoment m i n + frequencyMoment l i n := by
  unfold frequencyMoment
  apply Finsupp.sum_add_index'
  · intro key; simp
  · intro key a b
    split_ifs <;> simp [add_mul]

theorem frequencyMoment_sub (m l : Monomial) (i : Fin 4) (n : ℤ) :
    frequencyMoment (m - l) i n = frequencyMoment m i n - frequencyMoment l i n := by
  let L : Monomial →+ Coefficient :=
    { toFun := fun m => frequencyMoment m i n
      map_zero' := frequencyMoment_zero i n
      map_add' := fun m l => frequencyMoment_add m l i n }
  exact map_sub L m l

theorem frequencyMoment_Y (j i : Fin 4) (a b n : ℤ) :
    frequencyMoment (Y j a b) i n = if i = j then (q ^ a * t ^ b) ^ n else 0 := by
  simp [frequencyMoment, Y, eq_comm]

theorem spectralPower_shift (a b c d n : ℤ) :
    (q ^ (a + c) * t ^ (b + d)) ^ n =
      (q ^ c * t ^ d) ^ n * (q ^ a * t ^ b) ^ n := by
  rw [zpow_add₀ q_ne_zero, zpow_add₀ t_ne_zero]
  rw [show q ^ a * q ^ c * (t ^ b * t ^ d) =
    (q ^ c * t ^ d) * (q ^ a * t ^ b) by ring, mul_zpow]

/-- The Laurent root factor has exactly the original Cartan matrix
moment at each nonzero oscillator frequency. -/
theorem frequencyMoment_A (j i : Fin 4) (a b n : ℤ) (hn : n ≠ 0) :
    frequencyMoment (A j a b) i n =
      deformedCartan D₄ n i j * (q ^ a * t ^ b) ^ n := by
  rw [d4_deformedCartan_mode n hn]
  change frequencyMoment (A j a b) i n =
    (if i = j then q ^ n * t ^ (-n) + q ^ (-n) * t ^ n else
      if adjacent D₄ i.val j.val then (-1 : Coefficient) else 0) * (q ^ a * t ^ b) ^ n
  have hp : (q ^ (a + 1) * t ^ (b - 1)) ^ n =
      (q ^ n * t ^ (-n)) * (q ^ a * t ^ b) ^ n := by
    calc
      _ = (q ^ (1 : ℤ) * t ^ (-1 : ℤ)) ^ n * (q ^ a * t ^ b) ^ n :=
        spectralPower_shift a b 1 (-1) n
      _ = _ := by simp only [mul_zpow, zpow_one, inv_zpow, zpow_neg]
  have hm : (q ^ (a - 1) * t ^ (b + 1)) ^ n =
      (q ^ (-n) * t ^ n) * (q ^ a * t ^ b) ^ n := by
    calc
      _ = (q ^ (-1 : ℤ) * t ^ (1 : ℤ)) ^ n * (q ^ a * t ^ b) ^ n :=
        spectralPower_shift a b (-1) 1 n
      _ = _ := by simp only [mul_zpow, zpow_one, inv_zpow, zpow_neg]
  fin_cases j <;> fin_cases i <;>
    norm_num [A, frequencyMoment_sub, frequencyMoment_add, frequencyMoment_Y,
      hp, hm, adjacent, D₄, SimpleLieType.rank]
  all_goals try simp only [Fin.ext_iff]
  all_goals norm_num
  all_goals ring

theorem frequencyMoment_list_sum (ms : List Monomial) (i : Fin 4) (n : ℤ) :
    frequencyMoment ms.sum i n = (ms.map fun m => frequencyMoment m i n).sum := by
  induction ms with
  | nil => simp
  | cons m ms ih => simp only [List.sum_cons, List.map_cons, frequencyMoment_add, ih]

theorem frequencyMoment_monomialOfFactors (factors : List (InverseRootFactor D₄))
    (i : Fin 4) (n : ℤ) (hn : n ≠ 0) :
    frequencyMoment (monomialOfFactors factors) i n =
      (if i = (1 : Fin 4) then 1 else 0) -
        (factors.map fun f => deformedCartan D₄ n i f.root *
          (q ^ f.qShift * t ^ f.tShift) ^ n).sum := by
  rw [monomialOfFactors, frequencyMoment_sub, frequencyMoment_list_sum]
  simp only [M₀, frequencyMoment_Y, zpow_zero, one_mul, one_zpow, List.map_map]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro f hf
  exact frequencyMoment_A f.root i f.qShift f.tShift n hn

namespace PolynomialFock

/-- The actual oscillator eigenvalue is the scalar Heisenberg pairing
times the all-frequency Laurent moment of the elementary monomial. -/
theorem elementaryPositiveContraction_moment (factors : List (InverseRootFactor D₄))
    (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    elementaryPositiveContraction factors i n hn =
      RatFunc.C (((n : Coefficient)⁻¹ * (q ^ n - q ^ (-n)) * (t ^ n - t ^ (-n))) *
        frequencyMoment (monomialOfFactors factors) i n) := by
  induction factors with
  | nil =>
    rw [elementaryPositiveContraction_nil,
      frequencyMoment_monomialOfFactors [] i n (ne_of_gt hn)]
    simp only [List.map_nil, List.sum_nil, sub_zero]
    apply congrArg RatFunc.C
    split_ifs with h1 h2 h2
    · ring
    · exact (h2 (Fin.ext (congrArg Fin.val h1))).elim
    · exact (h1 (Fin.ext (congrArg Fin.val h2))).elim
    · ring
  | cons f fs ih =>
    have hm : frequencyMoment (monomialOfFactors (f :: fs)) i n =
        frequencyMoment (monomialOfFactors fs) i n -
          deformedCartan D₄ n i f.root * (q ^ f.qShift * t ^ f.tShift) ^ n := by
      rw [frequencyMoment_monomialOfFactors _ i n (ne_of_gt hn),
        frequencyMoment_monomialOfFactors _ i n (ne_of_gt hn)]
      simp only [List.map_cons, List.sum_cons]
      ring
    rw [elementaryPositiveContraction_cons, ih, hm,
      oscillatorCommutator_scalar_extension, d4_oscillator_opposite n (ne_of_gt hn)]
    simp only [map_mul, map_sub]
    ring

theorem screening_elementary_contraction_moment (sign : ScreeningSign)
    (factors : List (InverseRootFactor D₄)) (i : RootIndex D₄) (n : ℤ) (hn : 0 < n) :
    RatFunc.C (screeningModes (g := D₄) sign i n i) *
        elementaryPositiveContraction factors i n hn =
      RatFunc.C ((match sign with
        | .minus => -(q ^ n - q ^ (-n)) / (n : Coefficient)
        | .plus => (t ^ n - t ^ (-n)) / (n : Coefficient)) *
          frequencyMoment (monomialOfFactors factors) i n) := by
  have h := d4_screening_weight_contraction n (ne_of_gt hn) i i sign
  rw [d4_oscillator_weight_pairing n (ne_of_gt hn) i i] at h
  simp only [ite_true, one_mul] at h
  rw [elementaryPositiveContraction_moment, ← map_mul, ← mul_assoc, h]
  rfl

end PolynomialFock

end
end FrenkelReshetikhin.D4CounterexampleProof
