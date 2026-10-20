import D4CounterexampleProof.RationalRegularity
import D4CounterexampleProof.Multiplicity

/-! Positive specialization is preserved when identical elementary
monomials are grouped. Their combined coefficient cannot vanish. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance coefficientAggregationField : Field Coefficient := inferInstance

theorem regularAt_of_specializesToNat {c : Coefficient} {n : ℕ} (h : specializesToNat c n) :
    RegularAt 1 c :=
  ⟨c.num, c.denom, h.1, (RatFunc.num_div_denom c).symm⟩

theorem specializesToNat_zero : specializesToNat (0 : Coefficient) 0 := by
  simp [specializesToNat]

theorem specializesToNat_add {a b : Coefficient} {m n : ℕ}
    (ha : specializesToNat a m) (hb : specializesToNat b n) :
    specializesToNat (a + b) (m + n) := by
  refine ⟨((regularAt_of_specializesToNat ha).add (regularAt_of_specializesToNat hb)).denom_ne_zero, ?_⟩
  rw [RatFunc.eval_add (RingHom.id QuantumCoefficient) 1
    (by simpa only [Polynomial.eval₂_id] using ha.1)
    (by simpa only [Polynomial.eval₂_id] using hb.1), ha.2, hb.2, Nat.cast_add]

theorem specializesToNat_sum {ι : Type*} (s : Finset ι) (c : ι → Coefficient) (n : ι → ℕ)
    (h : ∀ i ∈ s, specializesToNat (c i) (n i)) :
    specializesToNat (∑ i ∈ s, c i) (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using specializesToNat_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact specializesToNat_add (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Any nonempty group of positively specialized coefficients has a
nonzero combined coefficient at generic q,t. -/
theorem coefficient_sum_ne_zero_of_positive_specialization {ι : Type*}
    (s : Finset ι) (c : ι → Coefficient) (n : ι → ℕ)
    (h : ∀ i ∈ s, specializesToNat (c i) (n i))
    (source : ι) (hsource : source ∈ s) (hpos : 0 < n source) :
    ∑ i ∈ s, c i ≠ 0 := by
  have hs := specializesToNat_sum s c n h
  have hsumpos : 0 < ∑ i ∈ s, n i :=
    lt_of_lt_of_le hpos (Finset.single_le_sum (fun i hi => Nat.zero_le (n i)) hsource)
  intro hz
  have he := hs.2
  rw [hz, RatFunc.eval_zero] at he
  have hn : ((∑ i ∈ s, n i : ℕ) : QuantumCoefficient) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hsumpos
  exact hn he.symm

theorem grouped_valid_coefficients_ne_zero {g : SimpleLieType} {ι : Type*}
    (s : Finset ι) (terms : ι → ElementaryTerm g)
    (hvalid : ∀ i ∈ s, (terms i).valid) (source : ι) (hsource : source ∈ s) :
    ∑ i ∈ s, (terms i).coefficient ≠ 0 :=
  coefficient_sum_ne_zero_of_positive_specialization s (fun i => (terms i).coefficient)
    (fun i => (terms i).multiplicity) (fun i hi => (hvalid i hi).2)
    source hsource (hvalid source hsource).1

end
end FrenkelReshetikhin.D4CounterexampleProof
