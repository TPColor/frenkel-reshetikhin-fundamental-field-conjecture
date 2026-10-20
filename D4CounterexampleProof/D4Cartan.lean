import D4CounterexampleProof.LaurentEvaluation

/-! Invertibility of the actual D₄ deformed Cartan matrix at creation mode -1. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

local instance d4CartanCoefficientField : Field Coefficient := inferInstance

theorem q_ne_zero : q ≠ 0 := by
  simpa [q, quantumQ] using (RatFunc.X_ne_zero : (RatFunc.X : QuantumCoefficient) ≠ 0)

theorem t_ne_zero : t ≠ 0 := RatFunc.X_ne_zero

theorem qInteger_inv_one : qInteger (q⁻¹ : Coefficient) 1 = 1 := by
  simp only [qInteger, zpow_one, zpow_neg_one, inv_inv]
  exact div_self (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp q_sub_inv_ne_zero)))

theorem d4_rootLength (i : RootIndex D₄) : rootLength D₄ i = 1 := rfl

theorem d4_cartan (i j : RootIndex D₄) :
    cartan D₄ i j = if i = j then 2 else if adjacent D₄ i.val j.val then -1 else 0 := rfl

theorem d4_deformedCartan_creation :
    deformedCartan D₄ (-1) = fun i j =>
      if i = j then q * t⁻¹ + q⁻¹ * t else
        if adjacent D₄ i.val j.val then (-1 : Coefficient) else 0 := by
  funext i j
  simp only [deformedCartan, d4_rootLength, d4_cartan, Nat.cast_one, one_mul,
    neg_neg, zpow_one, zpow_neg_one]
  by_cases hij : i = j
  · simp [hij, qInteger]
    ring
  · by_cases hadj : adjacent D₄ i.val j.val
    · simp [hij, hadj, qInteger_inv_one]
    · simp [hij, hadj, qInteger]

theorem d4_deformedCartan_creation_det :
    (deformedCartan D₄ (-1)).det =
      (q * t⁻¹ + q⁻¹ * t) ^ 4 - 3 * (q * t⁻¹ + q⁻¹ * t) ^ 2 := by
  rw [d4_deformedCartan_creation]
  change (Matrix.det (fun i j : Fin 4 =>
    if i = j then q * t⁻¹ + q⁻¹ * t else if adjacent D₄ i.val j.val then (-1 : Coefficient) else 0)) = _
  erw [Matrix.det_succ_row_zero (n := 3)]
  simp only [Matrix.det_fin_three, Fin.sum_univ_succ]
  dsimp only [Matrix.submatrix]
  simp only [Fin.ext_iff]
  norm_num [adjacent, D₄, SimpleLieType.rank, Fin.succAbove]
  simp only [Fin.ext_iff]
  norm_num
  ring

theorem d4_deformedCartan_creation_det_laurent :
    (deformedCartan D₄ (-1)).det =
      q ^ (4 : ℤ) * t ^ (-4 : ℤ) + q ^ (2 : ℤ) * t ^ (-2 : ℤ) +
        q ^ (-2 : ℤ) * t ^ (2 : ℤ) + q ^ (-4 : ℤ) * t ^ (4 : ℤ) := by
  rw [d4_deformedCartan_creation_det]
  norm_num [zpow_neg]
  field_simp [q_ne_zero, t_ne_zero]
  ring

theorem d4_deformedCartan_creation_det_ne_zero : (deformedCartan D₄ (-1)).det ≠ 0 := by
  intro hzero
  rw [d4_deformedCartan_creation_det_laurent] at hzero
  let m : Monomial := Y 0 4 (-4) + Y 0 2 (-2) + Y 0 (-2) 2 + Y 0 (-4) 4
  have hm : spectralMoment m = 0 := by
    funext i
    fin_cases i
    · simpa [m, spectralMoment_add, spectralMoment_Y] using hzero
    all_goals simp [m, spectralMoment_add, spectralMoment_Y]
  have heq : m = 0 := spectralMoment_injective (hm.trans spectralMoment_zero.symm)
  have hc := congrArg (fun x : Monomial => x (0, (4, -4))) heq
  norm_num [m, Y, Finsupp.add_apply] at hc

theorem d4_deformedCartan_creation_mul_inv :
    deformedCartan D₄ (-1) * (deformedCartan D₄ (-1))⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr d4_deformedCartan_creation_det_ne_zero)

theorem spectralMoment_A (i j : Fin 4) (a b : ℤ) :
    spectralMoment (A i a b) j =
      (q ^ a * t ^ b) * deformedCartan D₄ (-1) j i := by
  classical
  have hs : shift a b (A i 0 0) = A i a b := by
    by_cases hi : i = 1
    · simp only [A, shift, if_pos hi, Finsupp.mapDomain_sub, Finsupp.mapDomain_add,
        Y, Finsupp.mapDomain_single]
      simp [add_comm, sub_eq_add_neg]
    · simp only [A, shift, if_neg hi, Finsupp.mapDomain_sub, Finsupp.mapDomain_add,
        Y, Finsupp.mapDomain_single]
      simp [add_comm, sub_eq_add_neg]
  rw [← hs, spectralMoment_shift]
  congr 1
  rw [d4_deformedCartan_creation]
  change spectralMoment (A i 0 0) j =
    if j = i then q * t⁻¹ + q⁻¹ * t else if adjacent D₄ j.val i.val then -1 else 0
  fin_cases i <;> fin_cases j <;>
    norm_num [A, spectralMoment_add, spectralMoment_sub, spectralMoment_Y,
      adjacent, D₄, SimpleLieType.rank]
  all_goals try simp only [Fin.ext_iff]
  all_goals norm_num [spectralMoment_add, spectralMoment_sub, spectralMoment_Y]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying the actual first creation-mode exponent in the a-basis by
the deformed Cartan matrix recovers the Laurent Y-monomial's spectral vector. -/
theorem elementary_creation_coordinates (factors : List (InverseRootFactor D₄)) (j : Fin 4) :
    (∑ k : Fin 4, deformedCartan D₄ (-1) j k *
      ((deformedCartan D₄ (-1))⁻¹ k (1 : Fin 4) -
        (factors.map fun f => if k = f.root then q ^ f.qShift * t ^ f.tShift else 0).sum)) =
      spectralMoment (monomialOfFactors factors) j := by
  classical
  induction factors with
  | nil =>
    simp only [List.map_nil, List.sum_nil, sub_zero, monomialOfFactors, M₀, spectralMoment_Y]
    have h := congrArg (fun m : Matrix (RootIndex D₄) (RootIndex D₄) Coefficient => m j (1 : Fin 4))
      d4_deformedCartan_creation_mul_inv
    erw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [zpow_zero, mul_one]
    convert h using 1
    exact Fintype.sum_equiv (Equiv.refl (Fin 4) : Fin 4 ≃ RootIndex D₄) _ _ (fun _ => rfl)
  | cons f fs ih =>
    have hsplit :
        (∑ k : Fin 4, deformedCartan D₄ (-1) j k *
          ((deformedCartan D₄ (-1))⁻¹ k (1 : Fin 4) -
            ((f :: fs).map fun h => if k = h.root then q ^ h.qShift * t ^ h.tShift else 0).sum)) =
        (∑ k : Fin 4, deformedCartan D₄ (-1) j k *
          ((deformedCartan D₄ (-1))⁻¹ k (1 : Fin 4) -
            (fs.map fun h => if k = h.root then q ^ h.qShift * t ^ h.tShift else 0).sum)) -
        ∑ k : Fin 4, deformedCartan D₄ (-1) j k *
          (if k = f.root then q ^ f.qShift * t ^ f.tShift else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [List.map_cons, List.sum_cons]
      ring
    rw [hsplit, ih]
    have hdelta : (∑ k : Fin 4, deformedCartan D₄ (-1) j k *
        (if k = f.root then q ^ f.qShift * t ^ f.tShift else 0)) =
        (q ^ f.qShift * t ^ f.tShift) * deformedCartan D₄ (-1) j f.root := by
      simp only [mul_ite, mul_zero]
      erw [Finset.sum_ite_eq']
      simp [mul_comm]
    have hm : monomialOfFactors (f :: fs) = monomialOfFactors fs - A f.root f.qShift f.tShift := by
      simp only [monomialOfFactors, List.map_cons, List.sum_cons]
      abel
    rw [hm, spectralMoment_sub]
    simp only [Pi.sub_apply]
    rw [hdelta]
    congr 1
    exact (spectralMoment_A f.root j f.qShift f.tShift).symm

end
end FrenkelReshetikhin.D4CounterexampleProof
