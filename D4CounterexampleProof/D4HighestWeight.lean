import D4CounterexampleProof.NegativeDescendants
import D4CounterexampleProof.RootWeightSupport

/-! Highest ordinary weight multiplicity from the proved triangular
spanning result for the original Drinfeld-polynomial representation. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Drinfeld

def weightHeight : Weight D₄ →+ ℤ where
  toFun w := 3 * w (0 : Fin 4) + 5 * w (1 : Fin 4) + 3 * w (2 : Fin 4) + 3 * w (3 : Fin 4)
  map_zero' := by rfl
  map_add' w u := by
    change 3 * (w (0 : Fin 4) + u (0 : Fin 4)) + 5 * (w (1 : Fin 4) + u (1 : Fin 4)) +
      3 * (w (2 : Fin 4) + u (2 : Fin 4)) + 3 * (w (3 : Fin 4) + u (3 : Fin 4)) = _
    ring

theorem weightHeight_simpleRoot (i : Fin 4) : weightHeight (simpleRoot D₄ i) = 1 := by
  fin_cases i <;> decide

theorem weightHeight_sum_roots (xs : List (RootIndex D₄)) :
    weightHeight (xs.map (simpleRoot D₄)).sum = (xs.length : ℤ) := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons, map_add, weightHeight_simpleRoot i, ih,
      List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

theorem negative_word_weight_ne_highest (weight : Weight D₄)
    (xs : List (RootIndex D₄ × ℤ)) (hxs : xs ≠ []) :
    weight - (xs.map fun a => simpleRoot D₄ a.1).sum ≠ weight := by
  intro he
  have hz : (xs.map fun a => simpleRoot D₄ a.1).sum = 0 := sub_eq_self.mp he
  have hh := congrArg weightHeight hz
  have hsum : weightHeight (xs.map fun a => simpleRoot D₄ a.1).sum = (xs.length : ℤ) := by
    simpa only [List.map_map, Function.comp_def, List.length_map] using weightHeight_sum_roots (xs.map Prod.fst)
  rw [hsum, map_zero] at hh
  have hlen : xs.length = 0 := by omega
  exact hxs (List.length_eq_zero_iff.mp hlen)

theorem highest_weightSpace_eq_line {d : ℕ} (V : Representation D₄ d)
    (weight : Weight D₄) (v : Fin d → QuantumCoefficient)
    (hv : v ∈ weightSpace D₄ V weight)
    (hspan : negativeDescendants D₄ V v = ⊤) :
    weightSpace D₄ V weight = QuantumCoefficient ∙ v := by
  classical
  let other : Submodule QuantumCoefficient (Fin d → QuantumCoefficient) :=
    ⨆ w ∈ {w : Weight D₄ | w ≠ weight}, weightSpace D₄ V w
  have hd : Disjoint (weightSpace D₄ V weight) other :=
    (independent_weightSpaces D₄ V).disjoint_biSup (by simp)
  have hline : QuantumCoefficient ∙ v ≤ weightSpace D₄ V weight :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hv
  have hdesc : negativeDescendants D₄ V v ≤ (QuantumCoefficient ∙ v) ⊔ other := by
    apply Submodule.span_le.mpr
    rintro w ⟨xs, rfl⟩
    by_cases hx : xs = []
    · subst xs
      apply (show QuantumCoefficient ∙ v ≤ (QuantumCoefficient ∙ v) ⊔ other from le_sup_left)
      simpa only [negativeWord, Module.End.one_apply] using Submodule.mem_span_singleton_self v
    · apply (show other ≤ (QuantumCoefficient ∙ v) ⊔ other from le_sup_right)
      apply Submodule.mem_iSup_of_mem (weight - (xs.map fun a => simpleRoot D₄ a.1).sum)
      apply Submodule.mem_iSup_of_mem (negative_word_weight_ne_highest weight xs hx)
      exact negativeWord_weight D₄ V weight v hv xs
  apply le_antisymm _ hline
  intro w hw
  have hwall : w ∈ negativeDescendants D₄ V v := by rw [hspan]; trivial
  obtain ⟨u, hu, z, hz, heq⟩ := Submodule.mem_sup.mp (hdesc hwall)
  have hzw : z ∈ weightSpace D₄ V weight := by
    have hsub := (weightSpace D₄ V weight).sub_mem hw (hline hu)
    rw [← heq, add_sub_cancel_left] at hsub
    exact hsub
  have hz0 := Submodule.disjoint_def.mp hd z hzw hz
  rw [hz0, add_zero] at heq
  simpa only [heq] using hu

theorem fundamental_highest_weightMultiplicity_one {d : ℕ} (i : RootIndex D₄)
    (V : Representation D₄ d) (hV : FundamentalRepresentation D₄ i V) :
    weightMultiplicity D₄ V (fundamentalWeight D₄ i) = 1 := by
  obtain ⟨v, hv, hweight, hspan⟩ := fundamental_negative_spanning D₄ i V hV
  rw [weightMultiplicity, highest_weightSpace_eq_line V _ v hweight hspan]
  exact finrank_span_singleton hv

end
end FrenkelReshetikhin.D4CounterexampleProof
