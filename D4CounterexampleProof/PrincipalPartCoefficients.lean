import D4CounterexampleProof.RationalRegularity
import D4CounterexampleProof.PartialFractions

/-! A genuine simple pole has a nonzero principal-part coefficient in
any partial-fraction decomposition with distinct pole labels. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open scoped BigOperators

variable {K ι : Type*} [Field K]

theorem simple_principal_coefficient_ne_zero (f : RatFunc K) (Q : Polynomial K)
    (s : Finset ι) (c : ι → K) (hc : Set.InjOn c s) (order : ι → ℕ)
    (r : (i : ι) → Fin (order i) → K)
    (hdecomp : f = algebraMap (Polynomial K) (RatFunc K) Q +
      ∑ i ∈ s, ∑ j : Fin (order i), RatFunc.C (r i j) /
        (RatFunc.X - RatFunc.C (c i)) ^ (j.val + 1))
    (source : ι) (hsource : source ∈ s) (horder : order source = 1)
    (hpole : f.denom.eval (c source) = 0) :
    r source ⟨0, by omega⟩ ≠ 0 := by
  classical
  intro hzero
  have hregular : RegularAt (c source) f := by
    rw [hdecomp]
    apply (regularAt_polynomial (c source) Q).add
    apply regularAt_sum
    intro i hi
    apply regularAt_sum
    intro j hj
    by_cases his : i = source
    · subst i
      have hjzero : j = ⟨0, by omega⟩ := by
        apply Fin.ext
        have hjlt := j.isLt
        omega
      rw [hjzero, hzero, map_zero, zero_div]
      exact regularAt_zero _
    · have hci : c source ≠ c i := by
        intro he
        exact his (hc hi hsource he.symm)
      have hbase := regularNonzeroAt_X_sub_C (c source) (c i) hci
      have hconst : RegularAt (c source) (RatFunc.C (r i j)) := by
        simpa only [RatFunc.algebraMap_C] using
          regularAt_polynomial (c source) (Polynomial.C (r i j))
      simp only [div_eq_mul_inv]
      exact hconst.mul ((hbase.pow (j.val + 1)).inv.regularAt)
  exact hregular.denom_ne_zero hpole

end
end FrenkelReshetikhin.D4CounterexampleProof
