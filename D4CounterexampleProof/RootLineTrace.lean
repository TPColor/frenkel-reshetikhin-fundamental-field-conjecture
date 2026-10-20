import D4CounterexampleProof.WeightProjection

/-! Rank-one weight symmetry reduced to Laurent coefficients of a trace
identity on the actual type-one weight decomposition. -/

namespace FrenkelReshetikhin.OriginalFR.Drinfeld

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable (g : SimpleLieType)

def sameRootLine (i : RootIndex g) (base weight : Weight g) : Prop :=
  ∃ n : ℤ, weight = base + n • simpleRoot g i

theorem sameRootLine_shift (i : RootIndex g) (base weight : Weight g) (k : ℤ) :
    sameRootLine g i base (weight + k • simpleRoot g i) ↔ sameRootLine g i base weight := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n - k, ?_⟩
    rw [sub_smul]
    have he := congrArg (fun w : Weight g => w - k • simpleRoot g i) hn
    simpa only [add_sub_cancel_right, add_sub_assoc] using he
  · rintro ⟨n, rfl⟩
    exact ⟨n + k, by rw [add_smul]; abel⟩

theorem rootLine_trace_balance {d : ℕ} (V : Representation g d) (hV : TypeOne g V)
    (i : RootIndex g) (base : Weight g) :
    letI : Fintype (WeightBasisIndex g V) := weightBasisFintype g V hV
    (∑ j : WeightBasisIndex g V, if sameRootLine g i base j.1 then
      quantumQ ^ ((rootLength g i : ℤ) * j.1 i) else 0) =
    ∑ j : WeightBasisIndex g V, if sameRootLine g i base j.1 then
      quantumQ ^ (-((rootLength g i : ℤ) * j.1 i)) else 0 := by
  classical
  let : Fintype (WeightBasisIndex g V) := weightBasisFintype g V hV
  let p := sameRootLine g i base
  let P := weightProjection g V hV p
  let E := V (quotientMap g (x g true i 0))
  let F := V (quotientMap g (x g false i 0))
  let Kp := V (quotientMap g (k g i true))
  let Km := V (quotientMap g (k g i false))
  have hPF : Commute P F := weightProjection_commutes_current g V hV p false i 0
    (fun w => sameRootLine_shift g i base w (sign false))
  have hz := LinearMap.trace_lie_mul_eq E F P
  simp only [Ring.lie_def] at hz
  rw [hPF.eq, sub_self, mul_zero, map_zero] at hz
  have hrel := congrArg V (opposite_zero_currents g i)
  simp only [map_sub, map_mul, map_smul] at hrel
  change E * F - F * E =
    (quantumQ ^ rootLength g i - quantumQ ^ (-(rootLength g i : ℤ)))⁻¹ • (Kp - Km) at hrel
  change LinearMap.trace QuantumCoefficient (Fin d → QuantumCoefficient) ((E * F - F * E) * P) = 0 at hz
  rw [hrel, smul_mul_assoc, map_smul] at hz
  have hscalar : (quantumQ ^ rootLength g i - quantumQ ^ (-(rootLength g i : ℤ)))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    simpa only [zpow_neg, zpow_natCast] using quantum_root_parameter_sub_inv_ne_zero g i
  have htrace : LinearMap.trace QuantumCoefficient (Fin d → QuantumCoefficient) ((Kp - Km) * P) = 0 :=
    (smul_eq_zero.mp hz).resolve_left hscalar
  rw [sub_mul, map_sub, sub_eq_zero] at htrace
  have ht (positive : Bool) :
      LinearMap.trace QuantumCoefficient (Fin d → QuantumCoefficient)
        (V (quotientMap g (k g i positive)) * P) =
      ∑ j : WeightBasisIndex g V, if p j.1 then
        quantumQ ^ ((if positive then (1 : ℤ) else -1) * (rootLength g i : ℤ) * j.1 i) else 0 := by
    apply trace_diagonal_on_weightBasis g V hV
    intro j
    rw [Module.End.mul_apply, weightProjection_on_weight g V hV p j.1 _ (weightBasis_mem g V hV j)]
    by_cases hj : p j.1
    · rw [if_pos hj, if_pos hj]
      cases positive with
      | true => simpa only [if_true, one_mul] using
          (mem_weightSpace_iff g V j.1 _).mp (weightBasis_mem g V hV j) i
      | false => simpa only [Bool.false_eq_true, if_false, neg_one_mul, neg_mul, one_mul] using
          inverse_toral_on_weightVector g V j.1 _ (weightBasis_mem g V hV j) i
    · rw [if_neg hj, if_neg hj, map_zero, zero_smul]
  rw [ht true, ht false] at htrace
  simpa only [p, if_true, Bool.false_eq_true, if_false, one_mul, neg_one_mul, neg_mul] using htrace

end
end FrenkelReshetikhin.OriginalFR.Drinfeld
