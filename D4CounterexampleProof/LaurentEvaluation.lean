import D4CounterexampleProof.Signatures
import Mathlib.Algebra.Polynomial.Laurent

/-!
Faithful evaluation of the finite Laurent expressions in the original
rational-function coefficient fields. This supplies the link between free
spectral labels and the actual independent parameters q and t.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

variable (K : Type*) [Field K]

def laurentRatFunc : LaurentPolynomial K →+* RatFunc K :=
  LaurentPolynomial.eval₂ RatFunc.C (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

theorem laurentRatFunc_toLaurent (P : Polynomial K) :
    laurentRatFunc K (Polynomial.toLaurent P) = algebraMap (Polynomial K) (RatFunc K) P := by
  rw [laurentRatFunc, LaurentPolynomial.eval₂_toLaurent]
  have hh : Polynomial.eval₂RingHom (RatFunc.C : K →+* RatFunc K) RatFunc.X =
      algebraMap (Polynomial K) (RatFunc K) := by
    ext a <;> simp
  exact congrArg (fun f : Polynomial K →+* RatFunc K => f P) hh

theorem laurentRatFunc_T (n : ℤ) :
    laurentRatFunc K (LaurentPolynomial.T n) = (RatFunc.X : RatFunc K) ^ n := by
  simp [laurentRatFunc, LaurentPolynomial.eval₂_T]

theorem laurentRatFunc_C (c : K) :
    laurentRatFunc K (LaurentPolynomial.C c) = RatFunc.C c := by
  simp [laurentRatFunc]

theorem laurentRatFunc_eq_zero (f : LaurentPolynomial K) :
    laurentRatFunc K f = 0 → f = 0 := by
  induction f using LaurentPolynomial.induction_on_mul_T with
  | mul_T P n =>
    intro h
    rw [map_mul, laurentRatFunc_toLaurent, laurentRatFunc_T] at h
    have hx : (RatFunc.X : RatFunc K) ^ (-(n : ℤ)) ≠ 0 := zpow_ne_zero _ RatFunc.X_ne_zero
    have hP := (mul_eq_zero.mp h).resolve_right hx
    have hP0 : P = 0 := RatFunc.algebraMap_injective K (by simpa using hP)
    simp [hP0]

theorem laurentRatFunc_injective : Function.Injective (laurentRatFunc K) := by
  intro f h hfh
  apply sub_eq_zero.mp
  apply laurentRatFunc_eq_zero K
  rw [map_sub, hfh, sub_self]

def ratLaurentSum : (ℤ →₀ K) →+ RatFunc K :=
  (laurentRatFunc K).toAddMonoidHom.comp
    (AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom)

theorem ratLaurentSum_injective : Function.Injective (ratLaurentSum K) :=
  (laurentRatFunc_injective K).comp AddMonoidAlgebra.coeffAddEquiv.symm.injective

theorem ratLaurentSum_single (n : ℤ) (c : K) :
    ratLaurentSum K (Finsupp.single n c) = RatFunc.C c * (RatFunc.X : RatFunc K) ^ n := by
  change laurentRatFunc K (AddMonoidAlgebra.single n c) = _
  rw [LaurentPolynomial.single_eq_C_mul_T, map_mul, laurentRatFunc_C, laurentRatFunc_T]

theorem ratFunc_X_zpow_injective :
    Function.Injective (fun n : ℤ => (RatFunc.X : RatFunc K) ^ n) := by
  intro a b h
  have hs : ratLaurentSum K (Finsupp.single a 1) = ratLaurentSum K (Finsupp.single b 1) := by
    simpa only [ratLaurentSum_single, map_one, one_mul] using h
  exact Finsupp.single_left_injective one_ne_zero (ratLaurentSum_injective K hs)

local instance laurentEvaluationCoefficientField : Field Coefficient := inferInstance

def biLaurentEvaluation : ((ℤ × ℤ) →₀ ℂ) →+ Coefficient :=
  (ratLaurentSum QuantumCoefficient).comp
    ((Finsupp.mapRange.addMonoidHom (ratLaurentSum ℂ)).comp
      (Finsupp.curryAddEquiv.toAddMonoidHom.comp (Finsupp.mapDomain.addMonoidHom Prod.swap)))

theorem biLaurentEvaluation_injective : Function.Injective biLaurentEvaluation := by
  intro m n h
  apply Finsupp.mapDomain_injective (f := Prod.swap) (by intro x y h; simpa using congrArg Prod.swap h)
  apply Finsupp.curryEquiv.injective
  exact Finsupp.mapRange_injective _ (map_zero _) (ratLaurentSum_injective ℂ)
    (ratLaurentSum_injective QuantumCoefficient h)

theorem biLaurentEvaluation_single (a b : ℤ) (z : ℂ) :
    biLaurentEvaluation (Finsupp.single (a, b) z) =
      RatFunc.C (RatFunc.C z) * q ^ a * t ^ b := by
  change ratLaurentSum QuantumCoefficient
    ((Finsupp.curry (Finsupp.mapDomain Prod.swap (Finsupp.single (a, b) z))).mapRange
      (ratLaurentSum ℂ) (map_zero _)) = _
  simp only [Finsupp.mapDomain_single, Finsupp.curry_single, Finsupp.mapRange_single,
    ratLaurentSum_single]
  simp [q, t, quantumQ, map_zpow₀, mul_assoc]

theorem spectralParameter_injective :
    Function.Injective (fun a : ℤ × ℤ => q ^ a.1 * t ^ a.2) := by
  intro a b h
  rcases a with ⟨aq, ta⟩
  rcases b with ⟨bq, bt⟩
  have hs : biLaurentEvaluation (Finsupp.single (aq, ta) 1) =
      biLaurentEvaluation (Finsupp.single (bq, bt) 1) := by
    simpa only [biLaurentEvaluation_single, map_one, one_mul] using h
  exact Finsupp.single_left_injective one_ne_zero (biLaurentEvaluation_injective hs)

theorem q_sub_inv_ne_zero : q - q⁻¹ ≠ 0 := by
  intro h
  have he : q ^ (1 : ℤ) * t ^ (0 : ℤ) = q ^ (-1 : ℤ) * t ^ (0 : ℤ) := by
    simpa using sub_eq_zero.mp h
  have hh := congrArg Prod.fst (@spectralParameter_injective (1, 0) (-1, 0) he)
  norm_num at hh

theorem t_sub_inv_ne_zero : t - t⁻¹ ≠ 0 := by
  intro h
  have he : q ^ (0 : ℤ) * t ^ (1 : ℤ) = q ^ (0 : ℤ) * t ^ (-1 : ℤ) := by
    simpa using sub_eq_zero.mp h
  have hh := congrArg Prod.snd (@spectralParameter_injective (0, 1) (0, -1) he)
  norm_num at hh

def spectralMoment (m : Monomial) (i : Fin 4) : Coefficient :=
  biLaurentEvaluation ((Finsupp.curry m i).mapRange (Int.cast : ℤ → ℂ) (by simp))

theorem spectralMoment_injective : Function.Injective spectralMoment := by
  intro m n h
  apply Finsupp.curryEquiv.injective
  ext i a
  have hi := biLaurentEvaluation_injective (congrFun h i)
  have he := Finsupp.mapRange_injective (Int.cast : ℤ → ℂ) (by simp)
    Int.cast_injective hi
  exact congrArg (fun f : (ℤ × ℤ) →₀ ℤ => f a) he

theorem spectralMoment_add (m n : Monomial) :
    spectralMoment (m + n) = spectralMoment m + spectralMoment n := by
  funext i
  unfold spectralMoment
  simp only [Pi.add_apply]
  rw [← map_add]
  congr 1
  ext a
  simp [Finsupp.curry_apply]

theorem spectralMoment_zero : spectralMoment 0 = 0 := by
  funext i
  have h : (Finsupp.curry (0 : Monomial) i).mapRange (Int.cast : ℤ → ℂ) (by simp) = 0 := by
    ext a
    simp [Finsupp.curry_apply]
  change biLaurentEvaluation _ = 0
  rw [h, map_zero]

theorem spectralMoment_Y (i j : Fin 4) (a b : ℤ) :
    spectralMoment (Y i a b) j = if j = i then q ^ a * t ^ b else 0 := by
  classical
  by_cases hji : j = i
  · subst j
    simp [spectralMoment, Y, Finsupp.curry_single, biLaurentEvaluation_single]
  · simp [spectralMoment, Y, Finsupp.curry_single, hji]

theorem spectralMoment_single (i j : Fin 4) (a b n : ℤ) :
    spectralMoment (Finsupp.single (i, (a, b)) n) j =
      if j = i then (n : Coefficient) * q ^ a * t ^ b else 0 := by
  classical
  by_cases hji : j = i
  · subst j
    simp [spectralMoment, Finsupp.curry_single, biLaurentEvaluation_single]
  · simp [spectralMoment, Finsupp.curry_single, hji]

def spectralMomentHom : Monomial →+ (Fin 4 → Coefficient) where
  toFun := spectralMoment
  map_zero' := spectralMoment_zero
  map_add' := spectralMoment_add

theorem spectralMoment_sub (m n : Monomial) :
    spectralMoment (m - n) = spectralMoment m - spectralMoment n :=
  map_sub spectralMomentHom m n

theorem spectralMoment_shift (a b : ℤ) (m : Monomial) (i : Fin 4) :
    spectralMoment (shift a b m) i = q ^ a * t ^ b * spectralMoment m i := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp [shift, spectralMoment_zero]
  | add m n hm hn =>
    have hs : shift a b (m + n) = shift a b m + shift a b n := Finsupp.mapDomain_add
    rw [hs, spectralMoment_add, spectralMoment_add]
    change spectralMoment (shift a b m) i + spectralMoment (shift a b n) i = _
    rw [hm, hn]
    simp only [Pi.add_apply, mul_add]
  | single key n =>
    rcases key with ⟨j, u, v⟩
    simp only [shift, Finsupp.mapDomain_single, spectralMoment_single]
    by_cases hij : i = j
    · simp only [if_pos hij]
      have hq : q ≠ 0 := by
        simpa [q, quantumQ] using (RatFunc.X_ne_zero : (RatFunc.X : QuantumCoefficient) ≠ 0)
      have ht : t ≠ 0 := RatFunc.X_ne_zero
      rw [zpow_add₀ hq, zpow_add₀ ht]
      ring
    · simp [hij]

theorem spectralMoment_tDifference (m : Monomial) (i : Fin 4) :
    spectralMoment (tDifference m) i = (t - t⁻¹) * spectralMoment m i := by
  rw [tDifference, spectralMoment_sub]
  simp only [Pi.sub_apply, spectralMoment_shift, zpow_zero, one_mul,
    zpow_one, zpow_neg_one]
  ring

theorem spectralMoment_qDifference (m : Monomial) (i : Fin 4) :
    spectralMoment (qDifference m) i = (q - q⁻¹) * spectralMoment m i := by
  rw [qDifference, spectralMoment_sub]
  simp only [Pi.sub_apply, spectralMoment_shift, zpow_zero, mul_one,
    zpow_one, zpow_neg_one]
  ring

/-- A cross-multiplied signature equality in the original rational-function
field gives the exact free-Laurent equation used by the finite certificate. -/
theorem tDifference_of_rational_signature (m n r : Monomial)
    (h : ∀ i, (t - t⁻¹) * (spectralMoment n i - spectralMoment m i) =
      spectralMoment r i) : tDifference (n - m) = r := by
  apply spectralMoment_injective
  funext i
  rw [spectralMoment_tDifference, spectralMoment_sub]
  exact h i

theorem qDifference_of_rational_signature (m n r : Monomial)
    (h : ∀ i, (q - q⁻¹) * (spectralMoment n i - spectralMoment m i) =
      spectralMoment r i) : qDifference (n - m) = r := by
  apply spectralMoment_injective
  funext i
  rw [spectralMoment_qDifference, spectralMoment_sub]
  exact h i

end
end FrenkelReshetikhin.D4CounterexampleProof
