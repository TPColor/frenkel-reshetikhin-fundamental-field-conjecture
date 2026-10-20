import D4CounterexampleProof.MonomialCertificate

/-!
Finite root-data calculations for the central fundamental weight of D₄.
These use the `cartan` and `elementaryWeight` definitions in
`StatementDefinitions`, with zero-based central node 1 and outer node 3.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof


def central : RootIndex D₄ := ⟨1, by decide⟩
def outer : RootIndex D₄ := ⟨3, by decide⟩

def baseFactors : List (InverseRootFactor D₄) :=
  [⟨central, -1, 1⟩, ⟨⟨0, by decide⟩, -2, 2⟩,
   ⟨⟨2, by decide⟩, -2, 2⟩, ⟨central, -3, 3⟩]

def minusFactors : List (InverseRootFactor D₄) :=
  baseFactors ++ [⟨outer, -2, 2⟩, ⟨outer, -2, 4⟩]

def plusFactors : List (InverseRootFactor D₄) :=
  baseFactors ++ [⟨outer, -2, 2⟩, ⟨outer, -4, 2⟩]

/-- Ordinary weight of a Laurent monomial in the original Y variables. -/
def monomialWeight (m : Monomial) : Weight D₄ :=
  fun j => m.sum fun key n => n * fundamentalWeight D₄ key.1 j

theorem monomialWeight_Y (i : Fin 4) (a b : ℤ) :
    monomialWeight (Y i a b) = fundamentalWeight D₄ i := by
  funext j
  simp [monomialWeight, Y]

theorem monomialWeight_add (m n : Monomial) :
    monomialWeight (m + n) = monomialWeight m + monomialWeight n := by
  classical
  funext j
  unfold monomialWeight
  rw [Finsupp.sum_add_index']
  · simp
  · intro key
    simp
  · intro key x y
    ring

theorem monomialWeight_neg (m : Monomial) :
    monomialWeight (-m) = -monomialWeight m := by
  funext j
  simp [monomialWeight, Finsupp.sum_neg_index]

theorem monomialWeight_sub (m n : Monomial) :
    monomialWeight (m - n) = monomialWeight m - monomialWeight n := by
  rw [sub_eq_add_neg, monomialWeight_add, monomialWeight_neg, sub_eq_add_neg]

theorem monomialWeight_A (i : Fin 4) (a b : ℤ) :
    monomialWeight (A i a b) = simpleRoot D₄ i := by
  classical
  fin_cases i <;>
    simp [A, monomialWeight_sub, monomialWeight_add, monomialWeight_Y] <;>
    (funext j; fin_cases j <;> decide)

/-- The root-factor presentation and the Y-monomial presentation assign
the same ordinary weight to every proposed elementary term. -/
theorem monomialOfFactors_weight (factors : List (InverseRootFactor D₄)) :
    monomialWeight (monomialOfFactors factors) =
      elementaryWeight central factors := by
  induction factors with
  | nil =>
      simp only [monomialOfFactors, List.map_nil, List.sum_nil, sub_zero]
      rw [M₀]
      have hzero : elementaryWeight central [] = fundamentalWeight D₄ central := by
        funext j
        simp [elementaryWeight]
      rw [hzero]
      calc
        monomialWeight (Y (1 : Fin 4) 0 0) = fundamentalWeight D₄ (1 : Fin 4) :=
          monomialWeight_Y (1 : Fin 4) 0 0
        _ = fundamentalWeight D₄ central := by
          have hci : (1 : Fin 4) = central := by ext; rfl
          rw [hci]
  | cons f fs ih =>
      simp only [monomialOfFactors, List.map_cons, List.sum_cons]
      rw [show M₀ - (A f.root f.qShift f.tShift +
        (fs.map fun x => A x.root x.qShift x.tShift).sum) =
        (M₀ - (fs.map fun x => A x.root x.qShift x.tShift).sum) -
          A f.root f.qShift f.tShift by abel]
      rw [monomialWeight_sub]
      change monomialWeight (monomialOfFactors fs) -
        monomialWeight (A f.root f.qShift f.tShift) =
          elementaryWeight central (f :: fs)
      rw [ih]
      have hA : monomialWeight (A f.root f.qShift f.tShift) =
          simpleRoot D₄ f.root := by
        exact monomialWeight_A f.root f.qShift f.tShift
      rw [hA]
      funext j
      simp [elementaryWeight]
      ring

/-- The note's dominant-weight enumeration below the highest root θ.
Coordinates are in the simple-root basis; this arithmetic result does not
by itself identify the weight spaces of an arbitrary Drinfeld module. -/
theorem dominant_below_highest_root
    (a b c d : ℤ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 2)
    (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1)
    (hdom₁ : 0 ≤ 2 * a - b)
    (hdom₂ : 0 ≤ 2 * b - a - c - d)
    (hdom₃ : 0 ≤ 2 * c - b)
    (hdom₄ : 0 ≤ 2 * d - b) :
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨
      (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 1) := by
  omega

/-- Bourbaki's central fundamental weight is the highest root θ in D₄. -/
theorem central_fundamental_is_highest_root :
    fundamentalWeight D₄ central =
      simpleRoot D₄ ⟨0, by decide⟩ +
      2 • simpleRoot D₄ central +
      simpleRoot D₄ ⟨2, by decide⟩ + simpleRoot D₄ outer := by
  funext j
  fin_cases j <;> decide

theorem first_prefix_weight :
    elementaryWeight central (baseFactors.take 1) =
      simpleRoot D₄ ⟨0, by decide⟩ + simpleRoot D₄ central +
      simpleRoot D₄ ⟨2, by decide⟩ + simpleRoot D₄ outer := by
  funext j
  fin_cases j <;> decide

theorem second_prefix_weight :
    elementaryWeight central (baseFactors.take 2) =
      simpleRoot D₄ central + simpleRoot D₄ ⟨2, by decide⟩ +
      simpleRoot D₄ outer := by
  funext j
  fin_cases j <;> decide

theorem third_prefix_weight :
    elementaryWeight central (baseFactors.take 3) =
      simpleRoot D₄ central + simpleRoot D₄ outer := by
  funext j
  fin_cases j <;> decide

/-- The final forced monomial lies at the positive outer root. -/
theorem base_factors_weight :
    elementaryWeight central baseFactors = simpleRoot D₄ outer := by
  funext j
  fin_cases j <;>
    decide

/-- Both incompatible endpoints have the same negative-root weight. -/
theorem minus_factors_weight :
    elementaryWeight central minusFactors = -simpleRoot D₄ outer := by
  funext j
  fin_cases j <;>
    decide

theorem plus_factors_weight :
    elementaryWeight central plusFactors = -simpleRoot D₄ outer := by
  funext j
  fin_cases j <;>
    decide

theorem negative_outer_ne_highest :
    -simpleRoot D₄ outer ≠ fundamentalWeight D₄ central := by
  intro h
  have hh := congrFun h outer
  have hne : (-simpleRoot D₄ outer) outer ≠ fundamentalWeight D₄ central outer := by
    decide
  exact hne hh

theorem base_factors_monomial : monomialOfFactors baseFactors = M := by
  simp only [monomialOfFactors, baseFactors, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ext x
  simp [central, M₀, M, A, Y, D₄, SimpleLieType.rank,
    Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem first_prefix_monomial : monomialOfFactors (baseFactors.take 1) = M₁ := by
  ext x
  simp [monomialOfFactors, baseFactors, central, M₀, M₁, A, Y,
    D₄, SimpleLieType.rank, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem second_prefix_monomial : monomialOfFactors (baseFactors.take 2) = M₂ := by
  ext x
  simp [monomialOfFactors, baseFactors, central, M₀, M₂, A, Y,
    D₄, SimpleLieType.rank, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem third_prefix_monomial : monomialOfFactors (baseFactors.take 3) = M₃ := by
  ext x
  simp [monomialOfFactors, baseFactors, central, M₀, M₃, A, Y,
    D₄, SimpleLieType.rank, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem minus_factors_monomial : monomialOfFactors minusFactors = Nminus := by
  simp only [monomialOfFactors, minusFactors, List.map_append, List.sum_append,
    baseFactors, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ext x
  simp [central, outer, M₀, Nminus, A, Y, D₄, SimpleLieType.rank,
    Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem plus_factors_monomial : monomialOfFactors plusFactors = Nplus := by
  simp only [monomialOfFactors, plusFactors, List.map_append, List.sum_append,
    baseFactors, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ext x
  simp [central, outer, M₀, Nplus, A, Y, D₄, SimpleLieType.rank,
    Finsupp.add_apply, Finsupp.sub_apply]
  abel

end FrenkelReshetikhin.D4CounterexampleProof
