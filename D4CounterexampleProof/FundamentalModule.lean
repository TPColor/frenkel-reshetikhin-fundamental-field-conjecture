import StatementDefinitions
import D4CounterexampleProof.LaurentEvaluation
import Mathlib.Tactic.NoncommRing

/-!
Consequences of the original Drinfeld-polynomial definition of fundamental
modules. These are derived from the current eigenvalue identities, without
replacing that definition by a finite-type highest-weight condition.
-/

namespace FrenkelReshetikhin.OriginalFR.Drinfeld

noncomputable section

variable (g : SimpleLieType)

theorem cartanExponentialCoefficient_zero (p : Bool) (i : RootIndex g) :
    cartanExponentialCoefficient g p i 0 = 1 := by
  simp [cartanExponentialCoefficient]

theorem phi_zero (p : Bool) (i : RootIndex g) : phi g p i 0 = k g i p := by
  simp [phi, cartanExponentialCoefficient_zero]

theorem shiftedPolynomial_coeff_zero (P : Polynomial QuantumCoefficient)
    (a : QuantumCoefficient) : (shiftedPolynomial P a).coeff 0 = P.coeff 0 := by
  simp [shiftedPolynomial, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]

theorem drinfeld_highest_vector {d : ℕ} (V : Representation g d)
    (P : RootIndex g → Polynomial QuantumCoefficient) (hP : HasDrinfeldPolynomials g V P) :
    ∃ v : Fin d → QuantumCoefficient,
      v ≠ 0 ∧
      (∀ w, ∃ a : QuantumAffine g, V a v = w) ∧
      (∀ i n, V (quotientMap g (x g true i n)) v = 0) ∧
      ∀ i, V (quotientMap g (k g i true)) v =
        (quantumQ ^ rootLength g i) ^ (P i).natDegree • v := by
  obtain ⟨hconstant, v, eigenvalues, hv, hcyclic, hpositive, hphi, hratio⟩ := hP
  refine ⟨v, hv, hcyclic, hpositive, ?_⟩
  intro i
  have h0 := congrArg PowerSeries.constantCoeff (hratio true i)
  simp [shiftedPolynomial_coeff_zero, hconstant i] at h0
  have htoral := hphi true i 0
  simpa only [Nat.cast_zero, mul_zero, phi_zero, h0] using htoral

theorem fundamentalPolynomials_natDegree (i j : RootIndex g) (a : QuantumCoefficient)
    (ha : a ≠ 0) :
    (fundamentalPolynomials g i a j).natDegree = if j = i then 1 else 0 := by
  classical
  by_cases hji : j = i
  · simp only [fundamentalPolynomials, if_pos hji]
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
    · exact Polynomial.natDegree_C_mul_X a ha
    · simp [Polynomial.natDegree_C_mul_X a ha]
  · simp [fundamentalPolynomials, hji]

theorem fundamental_highest_vector {d : ℕ} (i : RootIndex g) (V : Representation g d)
    (hV : FundamentalRepresentation g i V) :
    ∃ v : Fin d → QuantumCoefficient,
      v ≠ 0 ∧ v ∈ weightSpace g V (fundamentalWeight g i) ∧
      (∀ w, ∃ a : QuantumAffine g, V a v = w) ∧
      ∀ j n, V (quotientMap g (x g true j n)) v = 0 := by
  obtain ⟨a, ha, hP⟩ := hV.2.2
  obtain ⟨v, hv, hcyclic, hpositive, htoral⟩ := drinfeld_highest_vector g V _ hP
  refine ⟨v, hv, ?_, hcyclic, hpositive⟩
  rw [weightSpace, Submodule.mem_iInf]
  intro j
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, htoral, fundamentalPolynomials_natDegree g i j a ha]
  by_cases hji : j = i
  · simp [hji, fundamentalWeight]
  · simp [hji, fundamentalWeight]

theorem fundamental_highest_weightMultiplicity_pos {d : ℕ} (i : RootIndex g)
    (V : Representation g d) (hV : FundamentalRepresentation g i V) :
    0 < weightMultiplicity g V (fundamentalWeight g i) := by
  obtain ⟨v, hv, hw, _, _⟩ := fundamental_highest_vector g i V hV
  rw [weightMultiplicity, Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨v, hw⟩, ?_⟩
  intro h
  exact hv (congrArg Subtype.val h)

theorem mem_weightSpace_iff {d : ℕ} (V : Representation g d) (weight : Weight g)
    (v : Fin d → QuantumCoefficient) :
    v ∈ weightSpace g V weight ↔
      ∀ i, V (quotientMap g (k g i true)) v =
        quantumQ ^ ((rootLength g i : ℤ) * weight i) • v := by
  simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem toral_current_commutation (i j : RootIndex g) (p : Bool) (n : ℤ) :
    quotientMap g (k g i true) * quotientMap g (x g p j n) =
      quantumQ ^ (sign p * B g i j) •
        (quotientMap g (x g p j n) * quotientMap g (k g i true)) := by
  have ht := RingQuot.mkAlgHom_rel QuantumCoefficient (Relation.toral_x i j p n)
  have hk := RingQuot.mkAlgHom_rel QuantumCoefficient (Relation.toral_inverse i false)
  change quotientMap g (k g i true * x g p j n * k g i false) =
    quotientMap g (quantumQ ^ (sign p * B g i j) • x g p j n) at ht
  change quotientMap g (k g i false * k g i true) = quotientMap g 1 at hk
  simp only [map_mul, map_smul] at ht
  simp only [map_mul, map_one] at hk
  calc
    _ = (quotientMap g (k g i true) * quotientMap g (x g p j n)) *
        (quotientMap g (k g i false) * quotientMap g (k g i true)) := by rw [hk, mul_one]
    _ = (quotientMap g (k g i true) * quotientMap g (x g p j n) *
        quotientMap g (k g i false)) * quotientMap g (k g i true) := by noncomm_ring
    _ = _ := by rw [ht, smul_mul_assoc]

theorem current_maps_weightSpace {d : ℕ} (V : Representation g d)
    (weight : Weight g) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace g V weight) (p : Bool) (j : RootIndex g) (n : ℤ) :
    V (quotientMap g (x g p j n)) v ∈
      weightSpace g V (weight + sign p • simpleRoot g j) := by
  rw [mem_weightSpace_iff] at hv ⊢
  intro i
  have h := congrArg (fun a : QuantumAffine g => V a v) (toral_current_commutation g i j p n)
  simp only [map_mul, map_smul, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [hv i, map_smul, smul_smul] at h
  rw [h]
  congr 1
  have hq : quantumQ ≠ 0 := RatFunc.X_ne_zero
  rw [← zpow_add₀ hq]
  congr 1
  simp only [B, Pi.add_apply, Pi.smul_apply, smul_eq_mul, simpleRoot]
  ring

theorem rootLength_pos (i : RootIndex g) : 0 < rootLength g i := by
  cases g <;> simp only [rootLength] <;> (try split_ifs) <;> norm_num

theorem weight_eigenvalues_injective :
    Function.Injective (fun weight : Weight g =>
      fun i => quantumQ ^ ((rootLength g i : ℤ) * weight i)) := by
  intro weight weight' h
  funext i
  have hi : (rootLength g i : ℤ) * weight i = (rootLength g i : ℤ) * weight' i :=
    D4CounterexampleProof.ratFunc_X_zpow_injective ℂ (congrFun h i)
  have hr : (rootLength g i : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (rootLength_pos g i)
  exact mul_left_cancel₀ hr hi

theorem weightSpaces_disjoint {d : ℕ} (V : Representation g d)
    (weight weight' : Weight g) (hne : weight ≠ weight') :
    Disjoint (weightSpace g V weight) (weightSpace g V weight') := by
  have ht : (fun i => quantumQ ^ ((rootLength g i : ℤ) * weight i)) ≠
      (fun i => quantumQ ^ ((rootLength g i : ℤ) * weight' i)) :=
    fun h => hne (weight_eigenvalues_injective g h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have h := ((mem_weightSpace_iff g V weight v).mp hv i).symm.trans
    ((mem_weightSpace_iff g V weight' v).mp hv' i)
  have hz : (quantumQ ^ ((rootLength g i : ℤ) * weight i) -
      quantumQ ^ ((rootLength g i : ℤ) * weight' i)) • v = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hi)

end
end FrenkelReshetikhin.OriginalFR.Drinfeld
