import D4CounterexampleProof.D4Modes

/-! Oscillator contractions in the actual presented Heisenberg algebra
over the original field of coefficients, including the auxiliary beta. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR OriginalFR.Fields
open scoped BigOperators

local instance oscillatorContractionsCoefficientField : Field Coefficient := inferInstance

theorem oscillatorCommutator_scalar_extension (g : SimpleLieType) (i j : RootIndex g)
    (n m : ℤ) :
    oscillatorCommutator g Scalars Q T i j n m =
      RatFunc.C (oscillatorCommutator g Coefficient q t i j n m) := by
  simp only [oscillatorCommutator, symmetrizedCartanMatrix, cartanMatrix,
    quantumInteger, Q, T]
  split_ifs <;> simp [map_mul, map_sub, map_add, map_div₀, map_inv₀, map_zpow₀]

set_option backward.isDefEq.respectTransparency false in
/-- The original FR (3.2) contraction, now as an equality in the presented
Heisenberg algebra acting on the Fock modules. The displayed linear
combination is the same inverse-Cartan combination used by the original
Y-vertex definition. -/
theorem d4_root_weight_commutator (n : ℤ) (hn : n ≠ 0) (k i : RootIndex D₄) :
    rootMode D₄ Scalars Q T k n *
        (∑ j : RootIndex D₄, RatFunc.C ((deformedCartan D₄ (-n))⁻¹ j i) •
          rootMode D₄ Scalars Q T j (-n)) -
      (∑ j : RootIndex D₄, RatFunc.C ((deformedCartan D₄ (-n))⁻¹ j i) •
          rootMode D₄ Scalars Q T j (-n)) * rootMode D₄ Scalars Q T k n =
      algebraMap Scalars (HeisenbergAlgebra D₄ Scalars Q T)
        (RatFunc.C ((if k = i then 1 else 0) *
          ((n : Coefficient)⁻¹ * (q ^ n - q ^ (-n)) * (t ^ n - t ^ (-n))))) := by
  classical
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : RootIndex D₄,
        algebraMap Scalars (HeisenbergAlgebra D₄ Scalars Q T)
          (RatFunc.C ((deformedCartan D₄ (-n))⁻¹ j i) *
            oscillatorCommutator D₄ Scalars Q T k j n (-n)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_smul_comm, smul_mul_assoc]
      calc
        _ = RatFunc.C ((deformedCartan D₄ (-n))⁻¹ j i) •
            (rootMode D₄ Scalars Q T k n * rootMode D₄ Scalars Q T j (-n) -
              rootMode D₄ Scalars Q T j (-n) * rootMode D₄ Scalars Q T k n) :=
          (smul_sub (RatFunc.C ((deformedCartan D₄ (-n))⁻¹ j i) : Scalars)
            (rootMode D₄ Scalars Q T k n * rootMode D₄ Scalars Q T j (-n))
            (rootMode D₄ Scalars Q T j (-n) * rootMode D₄ Scalars Q T k n)).symm
        _ = _ := by rw [rootMode_commutator, Algebra.smul_def, ← map_mul]
    _ = algebraMap Scalars (HeisenbergAlgebra D₄ Scalars Q T)
        (RatFunc.C (∑ j : RootIndex D₄, (deformedCartan D₄ (-n))⁻¹ j i *
          oscillatorCommutator D₄ Coefficient q t k j n (-n))) := by
      simp only [oscillatorCommutator_scalar_extension, map_sum, map_mul]
    _ = _ := by rw [d4_oscillator_weight_pairing n hn k i]

end
end FrenkelReshetikhin.D4CounterexampleProof
