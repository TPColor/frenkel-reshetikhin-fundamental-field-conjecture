import D4CounterexampleProof.Signatures
import D4CounterexampleProof.Weights

/-!
The first spectral moments recover the ordinary-weight displacement from a
cross-multiplied screening-signature equation.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

def tMomentWeight (m : Monomial) : Weight D₄ :=
  fun j => m.sum fun key n => n * key.2.2 * fundamentalWeight D₄ key.1 j

theorem tMomentWeight_add (m n : Monomial) :
    tMomentWeight (m + n) = tMomentWeight m + tMomentWeight n := by
  classical
  funext j
  unfold tMomentWeight
  rw [Finsupp.sum_add_index']
  · simp
  · intro key; simp
  · intro key x y; ring

theorem tMomentWeight_neg (m : Monomial) :
    tMomentWeight (-m) = -tMomentWeight m := by
  funext j
  simp [tMomentWeight, Finsupp.sum_neg_index]

theorem tMomentWeight_sub (m n : Monomial) :
    tMomentWeight (m - n) = tMomentWeight m - tMomentWeight n := by
  rw [sub_eq_add_neg, tMomentWeight_add, tMomentWeight_neg, sub_eq_add_neg]

theorem tMomentWeight_Y (i : Fin 4) (a b : ℤ) :
    tMomentWeight (Y i a b) = b • fundamentalWeight D₄ i := by
  funext j
  simp [tMomentWeight, Y]

theorem tMomentWeight_shift (m : Monomial) (b : ℤ) :
    tMomentWeight (shift 0 b m) =
      tMomentWeight m + b • monomialWeight m := by
  classical
  funext j
  simp only [tMomentWeight, shift, Pi.add_apply]
  rw [Finsupp.sum_mapDomain_index]
  · change (m.sum fun key n => n * (key.2.2 + b) * fundamentalWeight D₄ key.1 j) =
      (m.sum fun key n => n * key.2.2 * fundamentalWeight D₄ key.1 j) +
        b * (m.sum fun key n => n * fundamentalWeight D₄ key.1 j)
    simp only [Finsupp.sum]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro key _
    ring
  · intro key; simp
  · intro key x y; ring

theorem tMomentWeight_tDifference (m : Monomial) :
    tMomentWeight (tDifference m) = 2 • monomialWeight m := by
  rw [tDifference, tMomentWeight_sub, tMomentWeight_shift,
    tMomentWeight_shift]
  funext j
  simp [Pi.add_apply, Pi.sub_apply]
  ring

theorem tMomentWeight_A (i : Fin 4) (a b : ℤ) :
    tMomentWeight (A i a b) = b • simpleRoot D₄ i := by
  calc
    tMomentWeight (A i a b) = b • monomialWeight (A i a b) := by
      fin_cases i <;>
        simp [A, tMomentWeight_sub, tMomentWeight_add, tMomentWeight_Y,
          monomialWeight_sub, monomialWeight_add, monomialWeight_Y] <;>
        (funext j; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring)
    _ = b • simpleRoot D₄ i := by rw [monomialWeight_A]

/-- The spectral moment of a minus-signature equation determines the
ordinary weight shift of any candidate partner. -/
theorem minus_signature_weight_displacement (i : Fin 4) (P N : Monomial)
    (ca cb da db k : ℤ)
    (h : tDifference (N - P) = A i ca cb - A i da db)
    (hdb : db = cb + 2 * k) :
    monomialWeight N = monomialWeight P - k • simpleRoot D₄ i := by
  have hm := congrArg tMomentWeight h
  rw [tMomentWeight_tDifference, monomialWeight_sub,
    tMomentWeight_sub, tMomentWeight_A, tMomentWeight_A, hdb] at hm
  funext j
  have hj := congrFun hm j
  simp only [Pi.sub_apply, Pi.smul_apply] at hj ⊢
  change (2 : ℤ) * (monomialWeight N j - monomialWeight P j) =
    cb * simpleRoot D₄ i j - (cb + 2 * k) * simpleRoot D₄ i j at hj
  have hcalc : (2 : ℤ) * (monomialWeight N j - monomialWeight P j) =
      (2 : ℤ) * (-k * simpleRoot D₄ i j) := by
    calc
      _ = cb * simpleRoot D₄ i j - (cb + 2 * k) * simpleRoot D₄ i j := hj
      _ = _ := by ring
  have hsmall : monomialWeight N j - monomialWeight P j =
      -k * simpleRoot D₄ i j :=
    mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hcalc
  exact_mod_cast (by nlinarith only [hsmall] :
    monomialWeight N j = monomialWeight P j - k * simpleRoot D₄ i j)

def qMomentWeight (m : Monomial) : Weight D₄ :=
  fun j => m.sum fun key n => n * key.2.1 * fundamentalWeight D₄ key.1 j

theorem qMomentWeight_add (m n : Monomial) :
    qMomentWeight (m + n) = qMomentWeight m + qMomentWeight n := by
  classical
  funext j
  unfold qMomentWeight
  rw [Finsupp.sum_add_index']
  · simp
  · intro key; simp
  · intro key x y; ring

theorem qMomentWeight_neg (m : Monomial) :
    qMomentWeight (-m) = -qMomentWeight m := by
  funext j
  simp [qMomentWeight, Finsupp.sum_neg_index]

theorem qMomentWeight_sub (m n : Monomial) :
    qMomentWeight (m - n) = qMomentWeight m - qMomentWeight n := by
  rw [sub_eq_add_neg, qMomentWeight_add, qMomentWeight_neg, sub_eq_add_neg]

theorem qMomentWeight_Y (i : Fin 4) (a b : ℤ) :
    qMomentWeight (Y i a b) = a • fundamentalWeight D₄ i := by
  funext j
  simp [qMomentWeight, Y]

theorem qMomentWeight_shift (m : Monomial) (a : ℤ) :
    qMomentWeight (shift a 0 m) =
      qMomentWeight m + a • monomialWeight m := by
  classical
  funext j
  simp only [qMomentWeight, shift, Pi.add_apply]
  rw [Finsupp.sum_mapDomain_index]
  · change (m.sum fun key n => n * (key.2.1 + a) * fundamentalWeight D₄ key.1 j) =
      (m.sum fun key n => n * key.2.1 * fundamentalWeight D₄ key.1 j) +
        a * (m.sum fun key n => n * fundamentalWeight D₄ key.1 j)
    simp only [Finsupp.sum]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro key _
    ring
  · intro key; simp
  · intro key x y; ring

theorem qMomentWeight_qDifference (m : Monomial) :
    qMomentWeight (qDifference m) = 2 • monomialWeight m := by
  rw [qDifference, qMomentWeight_sub, qMomentWeight_shift,
    qMomentWeight_shift]
  funext j
  simp [Pi.add_apply, Pi.sub_apply]
  ring

theorem qMomentWeight_A (i : Fin 4) (a b : ℤ) :
    qMomentWeight (A i a b) = a • simpleRoot D₄ i := by
  calc
    qMomentWeight (A i a b) = a • monomialWeight (A i a b) := by
      fin_cases i <;>
        simp [A, qMomentWeight_sub, qMomentWeight_add, qMomentWeight_Y,
          monomialWeight_sub, monomialWeight_add, monomialWeight_Y] <;>
        (funext j; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring)
    _ = a • simpleRoot D₄ i := by rw [monomialWeight_A]

/-- The plus-screening signature gives the analogous q spectral weight
displacement. -/
theorem plus_signature_weight_displacement (i : Fin 4) (P N : Monomial)
    (ca cb da db k : ℤ)
    (h : qDifference (N - P) = A i da db - A i ca cb)
    (hda : da = ca + 2 * k) :
    monomialWeight N = monomialWeight P + k • simpleRoot D₄ i := by
  have hm := congrArg qMomentWeight h
  rw [qMomentWeight_qDifference, monomialWeight_sub,
    qMomentWeight_sub, qMomentWeight_A, qMomentWeight_A, hda] at hm
  funext j
  have hj := congrFun hm j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at hj ⊢
  change (2 : ℤ) * (monomialWeight N j - monomialWeight P j) =
    (ca + 2 * k) * simpleRoot D₄ i j - ca * simpleRoot D₄ i j at hj
  have hcalc : (2 : ℤ) * (monomialWeight N j - monomialWeight P j) =
      (2 : ℤ) * (k * simpleRoot D₄ i j) := by
    calc
      _ = (ca + 2 * k) * simpleRoot D₄ i j - ca * simpleRoot D₄ i j := hj
      _ = _ := by ring
  have hsmall : monomialWeight N j - monomialWeight P j =
      k * simpleRoot D₄ i j :=
    mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hcalc
  exact_mod_cast (by nlinarith only [hsmall] :
    monomialWeight N j = monomialWeight P j + k * simpleRoot D₄ i j)

end
end FrenkelReshetikhin.D4CounterexampleProof
