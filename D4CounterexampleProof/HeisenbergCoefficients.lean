import D4CounterexampleProof.OscillatorContractions

/-! Symmetry and antisymmetry of the original D₄ oscillator coefficients,
needed for a polynomial representation of the presented algebra. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance heisenbergCoefficientsField : _root_.Field Coefficient := inferInstance

theorem d4_deformedCartan_symmetric (n : ℤ) (hn : n ≠ 0) (i j : RootIndex D₄) :
    deformedCartan D₄ n i j = deformedCartan D₄ n j i := by
  rw [d4_deformedCartan_mode n hn]
  fin_cases i <;> fin_cases j <;> norm_num [adjacent, D₄, SimpleLieType.rank]
  all_goals simp only [Fin.ext_iff]
  all_goals norm_num

theorem d4_oscillator_opposite (n : ℤ) (hn : n ≠ 0) (i j : RootIndex D₄) :
    oscillatorCommutator D₄ Coefficient q t i j n (-n) =
      ((n : Coefficient)⁻¹ * (q ^ n - q ^ (-n)) * (t ^ n - t ^ (-n))) *
        deformedCartan D₄ n i j := by
  have hi : quantumInteger Coefficient (q ^ n) (rootLength D₄ i) = 1 := by
    simp only [d4_rootLength, Nat.cast_one, quantumInteger, zpow_one,
      zpow_neg_one, ← zpow_neg]
    exact div_self (q_mode_sub_ne_zero n hn)
  simp only [oscillatorCommutator, hn, false_or, add_neg_cancel, ne_eq,
    not_true_eq_false, if_false, symmetrizedCartanMatrix, hi, one_mul,
    cartanMatrix_eq_deformedCartan]

theorem d4_oscillator_antisymmetric_coefficient (i j : RootIndex D₄) (n m : ℤ) :
    oscillatorCommutator D₄ Coefficient q t i j n m =
      -oscillatorCommutator D₄ Coefficient q t j i m n := by
  by_cases hn : n = 0
  · by_cases hm : m = 0 <;> simp [oscillatorCommutator, hn, hm]
  · by_cases hsum : n + m = 0
    · have hm : m = -n := by omega
      subst m
      rw [d4_oscillator_opposite n hn,
        show oscillatorCommutator D₄ Coefficient q t j i (-n) n =
          oscillatorCommutator D₄ Coefficient q t j i (-n) (-(-n)) by simp,
        d4_oscillator_opposite (-n) (neg_ne_zero.mpr hn),
        d4_deformedCartan_neg_mode n hn, d4_deformedCartan_symmetric n hn j i]
      simp only [Int.cast_neg, inv_neg, neg_neg]
      ring
    · have hsum' : m + n ≠ 0 := by omega
      simp [oscillatorCommutator, hsum, hsum']

theorem d4_oscillator_antisymmetric (i j : RootIndex D₄) (n m : ℤ) :
    oscillatorCommutator D₄ Scalars Q T i j n m =
      -oscillatorCommutator D₄ Scalars Q T j i m n := by
  rw [oscillatorCommutator_scalar_extension, oscillatorCommutator_scalar_extension,
    d4_oscillator_antisymmetric_coefficient, map_neg]

end
end FrenkelReshetikhin.D4CounterexampleProof
