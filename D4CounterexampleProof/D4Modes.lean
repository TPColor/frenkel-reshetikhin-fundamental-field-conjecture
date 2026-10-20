import D4CounterexampleProof.D4Cartan

/-! Nonvanishing of the screening denominators and the deformed Cartan
matrix at every nonzero oscillator mode in the original rational setting. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

local instance d4ModesCoefficientField : Field Coefficient := inferInstance

theorem q_mode_sub_ne_zero (n : ℤ) (hn : n ≠ 0) : q ^ n - q ^ (-n) ≠ 0 := by
  intro h
  have he : q ^ n * t ^ (0 : ℤ) = q ^ (-n) * t ^ (0 : ℤ) := by
    simpa using sub_eq_zero.mp h
  have hh := congrArg Prod.fst (@spectralParameter_injective (n, 0) (-n, 0) he)
  exact hn (by dsimp at hh; omega)

theorem t_mode_sub_ne_zero (n : ℤ) (hn : n ≠ 0) : t ^ n - t ^ (-n) ≠ 0 := by
  intro h
  have he : q ^ (0 : ℤ) * t ^ n = q ^ (0 : ℤ) * t ^ (-n) := by
    simpa using sub_eq_zero.mp h
  have hh := congrArg Prod.snd (@spectralParameter_injective (0, n) (0, -n) he)
  exact hn (by dsimp at hh; omega)

theorem d4_deformedCartan_mode (n : ℤ) (hn : n ≠ 0) :
    deformedCartan D₄ n = fun i j =>
      if i = j then q ^ n * t ^ (-n) + q ^ (-n) * t ^ n else
        if adjacent D₄ i.val j.val then (-1 : Coefficient) else 0 := by
  funext i j
  have hi : qInteger (q ^ n) 1 = 1 := by
    simp only [qInteger, zpow_one, zpow_neg_one, ← zpow_neg]
    exact div_self (q_mode_sub_ne_zero n hn)
  simp only [deformedCartan, d4_rootLength, d4_cartan, Nat.cast_one, one_mul]
  by_cases hij : i = j
  · simp [hij, qInteger]
  · by_cases hadj : adjacent D₄ i.val j.val
    · simp [hij, hadj, hi]
    · simp [hij, hadj, qInteger]

theorem d4_star_det (x : Coefficient) :
    (Matrix.det (fun i j : Fin 4 =>
      if i = j then x else if adjacent D₄ i.val j.val then (-1 : Coefficient) else 0)) =
      x ^ 4 - 3 * x ^ 2 := by
  erw [Matrix.det_succ_row_zero (n := 3)]
  simp only [Matrix.det_fin_three, Fin.sum_univ_succ]
  dsimp only [Matrix.submatrix]
  simp only [Fin.ext_iff]
  norm_num [adjacent, D₄, SimpleLieType.rank, Fin.succAbove]
  simp only [Fin.ext_iff]
  norm_num
  ring

theorem d4_deformedCartan_mode_det (n : ℤ) (hn : n ≠ 0) :
    (deformedCartan D₄ n).det =
      (q ^ n * t ^ (-n) + q ^ (-n) * t ^ n) ^ 4 -
        3 * (q ^ n * t ^ (-n) + q ^ (-n) * t ^ n) ^ 2 := by
  rw [d4_deformedCartan_mode n hn]
  exact d4_star_det _

private theorem star_det_laurent (u v : Coefficient) (hu : u ≠ 0) (hv : v ≠ 0) :
    (u * v⁻¹ + u⁻¹ * v) ^ 4 - 3 * (u * v⁻¹ + u⁻¹ * v) ^ 2 =
      u ^ (4 : ℤ) * v ^ (-4 : ℤ) + u ^ (2 : ℤ) * v ^ (-2 : ℤ) +
        u ^ (-2 : ℤ) * v ^ (2 : ℤ) + u ^ (-4 : ℤ) * v ^ (4 : ℤ) := by
  norm_num [zpow_neg]
  field_simp
  ring

theorem d4_deformedCartan_mode_det_laurent (n : ℤ) (hn : n ≠ 0) :
    (deformedCartan D₄ n).det =
      q ^ (n * 4) * t ^ (n * (-4)) + q ^ (n * 2) * t ^ (n * (-2)) +
        q ^ (n * (-2)) * t ^ (n * 2) + q ^ (n * (-4)) * t ^ (n * 4) := by
  rw [d4_deformedCartan_mode_det n hn]
  simpa only [zpow_mul, zpow_natCast, zpow_neg, zpow_one] using
    star_det_laurent (q ^ n) (t ^ n) (zpow_ne_zero _ q_ne_zero) (zpow_ne_zero _ t_ne_zero)

theorem d4_deformedCartan_mode_det_ne_zero (n : ℤ) (hn : n ≠ 0) :
    (deformedCartan D₄ n).det ≠ 0 := by
  intro hzero
  rw [d4_deformedCartan_mode_det_laurent n hn] at hzero
  let m : Monomial := Y 0 (n * 4) (n * (-4)) + Y 0 (n * 2) (n * (-2)) +
    Y 0 (n * (-2)) (n * 2) + Y 0 (n * (-4)) (n * 4)
  have hm : spectralMoment m = 0 := by
    funext i
    fin_cases i
    · simpa [m, spectralMoment_add, spectralMoment_Y] using hzero
    all_goals simp [m, spectralMoment_add, spectralMoment_Y]
  have heq : m = 0 := spectralMoment_injective (hm.trans spectralMoment_zero.symm)
  have hc := congrArg (fun x : Monomial => x (0, (n * 4, n * (-4)))) heq
  have h42 : n * 4 ≠ n * 2 := by omega
  have h4m2 : n * 4 ≠ n * (-2) := by omega
  have h4m4 : n * 4 ≠ n * (-4) := by omega
  simp only [mul_neg] at h4m2 h4m4
  simp [m, Y, Finsupp.add_apply, h42, h4m2, h4m4] at hc

theorem d4_deformedCartan_mode_mul_inv (n : ℤ) (hn : n ≠ 0) :
    deformedCartan D₄ n * (deformedCartan D₄ n)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (d4_deformedCartan_mode_det_ne_zero n hn))

theorem d4_deformedCartan_neg_mode (n : ℤ) (hn : n ≠ 0) :
    deformedCartan D₄ (-n) = deformedCartan D₄ n := by
  rw [d4_deformedCartan_mode n hn, d4_deformedCartan_mode (-n) (neg_ne_zero.mpr hn)]
  funext i j
  simp only [neg_neg]
  split_ifs <;> ring

theorem cartanMatrix_eq_deformedCartan (g : SimpleLieType) (n : ℤ) :
    OriginalFR.cartanMatrix g Coefficient q t n = deformedCartan g n := rfl

/-- The scalar pairing underlying FR (3.2), derived from (3.1) and the
actual inverse Cartan matrix. This is the oscillator contraction used in
the original Y/screening OPE; it is not an added commutator axiom. -/
theorem d4_oscillator_weight_pairing (n : ℤ) (hn : n ≠ 0)
    (k i : RootIndex D₄) :
    (∑ j : RootIndex D₄, (deformedCartan D₄ (-n))⁻¹ j i *
      OriginalFR.oscillatorCommutator D₄ Coefficient q t k j n (-n)) =
    (if k = i then 1 else 0) *
      ((n : Coefficient)⁻¹ * (q ^ n - q ^ (-n)) * (t ^ n - t ^ (-n))) := by
  classical
  have hi : OriginalFR.quantumInteger Coefficient (q ^ n) (rootLength D₄ k) = 1 := by
    simp only [d4_rootLength, Nat.cast_one, OriginalFR.quantumInteger,
      zpow_one, zpow_neg_one, ← zpow_neg]
    exact div_self (q_mode_sub_ne_zero n hn)
  simp only [OriginalFR.oscillatorCommutator, hn, false_or, add_neg_cancel,
    ne_eq, not_true_eq_false, if_false, OriginalFR.symmetrizedCartanMatrix, hi,
    one_mul, cartanMatrix_eq_deformedCartan, d4_deformedCartan_neg_mode n hn]
  have hm := congrArg (fun m : Matrix (RootIndex D₄) (RootIndex D₄) Coefficient => m k i)
    (d4_deformedCartan_mode_mul_inv n hn)
  rw [Matrix.mul_apply, Matrix.one_apply] at hm
  calc
    _ = (∑ j : RootIndex D₄, deformedCartan D₄ n k j *
        (deformedCartan D₄ n)⁻¹ j i) *
        ((n : Coefficient)⁻¹ * (q ^ n - q ^ (-n)) * (t ^ n - t ^ (-n))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [hm]

end
end FrenkelReshetikhin.D4CounterexampleProof
