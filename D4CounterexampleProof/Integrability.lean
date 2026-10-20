import D4CounterexampleProof.FundamentalModule
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-! Local nilpotence of the original Drinfeld currents on weight vectors,
derived from their toral commutation and finite dimensionality. -/

namespace FrenkelReshetikhin.OriginalFR.Drinfeld

noncomputable section

variable (g : SimpleLieType)

/-- The finite-type quantum sl₂ commutator is a consequence of the
original opposite-current relation at mode zero. -/
theorem opposite_zero_currents (i : RootIndex g) :
    quotientMap g (x g true i 0) * quotientMap g (x g false i 0) -
      quotientMap g (x g false i 0) * quotientMap g (x g true i 0) =
      (quantumQ ^ rootLength g i - quantumQ ^ (-(rootLength g i : ℤ)))⁻¹ •
        (quotientMap g (k g i true) - quotientMap g (k g i false)) := by
  have h := RingQuot.mkAlgHom_rel QuantumCoefficient (Relation.opposite_sign i i 0 0)
  simpa only [quotientMap, sub_self, add_zero, if_pos rfl, ite_true, centralPower,
    Int.natAbs_zero, pow_zero, one_mul, phi_zero, map_smul, map_sub, map_mul] using h

theorem inverse_toral_on_weightVector {d : ℕ} (V : Representation g d)
    (weight : Weight g) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace g V weight) (i : RootIndex g) :
    V (quotientMap g (k g i false)) v =
      quantumQ ^ (-((rootLength g i : ℤ) * weight i)) • v := by
  have h := RingQuot.mkAlgHom_rel QuantumCoefficient (Relation.toral_inverse i false)
  change quotientMap g (k g i false * k g i true) = quotientMap g 1 at h
  have he := congrArg (fun a : QuantumAffine g => V a v) h
  simp only [map_mul, map_one, Module.End.mul_apply, Module.End.one_apply] at he
  rw [(mem_weightSpace_iff g V weight v).mp hv i, map_smul] at he
  have hn : quantumQ ^ ((rootLength g i : ℤ) * weight i) ≠ 0 :=
    zpow_ne_zero _ RatFunc.X_ne_zero
  have hh := congrArg (fun w : Fin d → QuantumCoefficient =>
    (quantumQ ^ ((rootLength g i : ℤ) * weight i))⁻¹ • w) he
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul, zpow_neg] using hh

/-- The standard quantum sl₂ weight coefficient follows from the
presented current commutator and the actual weight-space eigenvalues. -/
theorem opposite_zero_currents_on_weightVector {d : ℕ} (V : Representation g d)
    (weight : Weight g) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace g V weight) (i : RootIndex g) :
    V (quotientMap g (x g true i 0)) (V (quotientMap g (x g false i 0)) v) -
      V (quotientMap g (x g false i 0)) (V (quotientMap g (x g true i 0)) v) =
      qInteger (quantumQ ^ rootLength g i) (weight i) • v := by
  have he := congrArg (fun a : QuantumAffine g => V a v) (opposite_zero_currents g i)
  simp only [map_sub, map_mul, map_smul, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply] at he
  rw [(mem_weightSpace_iff g V weight v).mp hv i,
    inverse_toral_on_weightVector g V weight v hv i, ← sub_smul, smul_smul] at he
  convert he using 1
  congr 1
  simp only [qInteger, ← zpow_natCast, ← zpow_mul, ← zpow_neg, mul_neg, div_eq_mul_inv]
  ring

theorem current_pow_maps_weightSpace {d : ℕ} (V : Representation g d)
    (weight : Weight g) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace g V weight) (p : Bool) (j : RootIndex g) (n : ℤ) (k : ℕ) :
    (V (quotientMap g (x g p j n)) ^ k) v ∈
      weightSpace g V (weight + (k : ℤ) • (sign p • simpleRoot g j)) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have h := current_maps_weightSpace g V _ _ ih p j n
    rw [pow_succ', Module.End.mul_apply]
    convert h using 1
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem cartan_diagonal (j : RootIndex g) : cartan g j j = 2 := by
  cases g <;> simp [cartan]

theorem current_nilpotent_on_weightVector {d : ℕ} (V : Representation g d)
    (weight : Weight g) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace g V weight) (p : Bool) (j : RootIndex g) (n : ℤ) :
    ∃ k : ℕ, (V (quotientMap g (x g p j n)) ^ k) v = 0 := by
  classical
  by_contra h
  push Not at h
  let f := V (quotientMap g (k g j true))
  let eigenvalue (r : ℕ) : QuantumCoefficient :=
    quantumQ ^ ((rootLength g j : ℤ) * (weight j + (r : ℤ) * (sign p * 2)))
  have he (r : ℕ) : f.HasEigenvalue (eigenvalue r) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    apply Module.End.hasEigenvector_iff.mpr
    refine ⟨?_, h r⟩
    rw [Module.End.mem_eigenspace_iff]
    have hw := (mem_weightSpace_iff g V _ _).mp
      (current_pow_maps_weightSpace g V weight v hv p j n r) j
    simpa only [f, eigenvalue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      simpleRoot, cartan_diagonal] using hw
  have hinj : Function.Injective eigenvalue := by
    intro a b hab
    have hab' := D4CounterexampleProof.ratFunc_X_zpow_injective ℂ hab
    have hr : (rootLength g j : ℤ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (rootLength_pos g j)
    have heq := mul_left_cancel₀ hr hab'
    cases p <;> simp only [sign, Bool.false_eq_true, if_false, if_true] at heq <;> omega
  have hf : Set.Finite (Set.range eigenvalue) :=
    f.finite_hasEigenvalue.subset (by rintro _ ⟨r, rfl⟩; exact he r)
  exact (Set.infinite_range_of_injective hinj) hf

/-- In a finite-dimensional type-one module, each original Drinfeld
raising or lowering current is a nilpotent endomorphism. -/
theorem current_isNilpotent {d : ℕ} (V : Representation g d) (hV : TypeOne g V)
    (p : Bool) (j : RootIndex g) (n : ℤ) :
    IsNilpotent (V (quotientMap g (x g p j n))) := by
  let f := V (quotientMap g (x g p j n))
  have htop : f.maxGenEigenspace 0 = ⊤ := by
    apply top_unique
    rw [← hV.2]
    apply iSup_le
    intro weight v hv
    rw [Module.End.mem_maxGenEigenspace]
    simpa only [zero_smul, sub_zero] using
      current_nilpotent_on_weightVector g V weight v hv p j n
  refine ⟨f.maxGenEigenspaceIndex 0, ?_⟩
  apply LinearMap.ext
  intro v
  have hv : v ∈ f.maxGenEigenspace 0 := by rw [htop]; trivial
  rw [Module.End.maxGenEigenspace_eq, Module.End.mem_genEigenspace_nat] at hv
  simpa only [zero_smul, sub_zero, LinearMap.zero_apply, LinearMap.mem_ker] using hv

/-- The actual weight-space definition has finite support in every
finite-dimensional representation; no character formula is assumed. -/
theorem finite_weight_support {d : ℕ} (V : Representation g d) :
    Set.Finite {weight : Weight g | weightMultiplicity g V weight ≠ 0} := by
  classical
  let ev (w : {weight : Weight g // weightMultiplicity g V weight ≠ 0}) :
      ∀ i : RootIndex g, (V (quotientMap g (k g i true))).Eigenvalues := fun i =>
    ⟨quantumQ ^ ((rootLength g i : ℤ) * w.val i), by
      have hpos : 0 < Module.finrank QuantumCoefficient (weightSpace g V w.val) :=
        Nat.pos_of_ne_zero w.property
      obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
      apply Module.End.hasEigenvalue_of_hasEigenvector
      apply Module.End.hasEigenvector_iff.mpr
      refine ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        exact (mem_weightSpace_iff g V w.val v.val).mp v.property i
      · intro hz
        exact hv (Subtype.ext hz)⟩
  have hinj : Function.Injective ev := by
    intro a b hab
    apply Subtype.ext
    apply weight_eigenvalues_injective g
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  exact @Set.toFinite (Weight g) {weight | weightMultiplicity g V weight ≠ 0}
    (Finite.of_injective ev hinj)

theorem toral_endomorphisms_commute {d : ℕ} (V : Representation g d)
    (i j : RootIndex g) :
    Commute (V (quotientMap g (k g i true))) (V (quotientMap g (k g j true))) := by
  have h := RingQuot.mkAlgHom_rel QuantumCoefficient (Relation.toral_commute i j true true)
  change quotientMap g (k g i true * k g j true) =
    quotientMap g (k g j true * k g i true) at h
  have he := congrArg V h
  simpa only [map_mul, Commute, SemiconjBy] using he

/-- Actual weight spaces are jointly independent, not merely pairwise
disjoint. Together with TypeOne this gives the direct weight decomposition. -/
theorem independent_weightSpaces {d : ℕ} (V : Representation g d) :
    iSupIndep (fun weight : Weight g => weightSpace g V weight) := by
  let f (i : RootIndex g) := V (quotientMap g (k g i true))
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j a => Module.End.mapsTo_maxGenEigenspace_of_comm
      (toral_endomorphisms_commute g V j i) a)
  have h' := h.comp (weight_eigenvalues_injective g)
  apply h'.mono
  intro weight v hv
  apply (Submodule.mem_iInf _).mpr
  intro i
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  exact (mem_weightSpace_iff g V weight v).mp hv i

end
end FrenkelReshetikhin.OriginalFR.Drinfeld
