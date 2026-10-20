import D4CounterexampleProof.RootStrings
import D4CounterexampleProof.Weights
import D4CounterexampleProof.Moments

/-!
Transfer of the finite D₄ root list into the original fundamental-weight
coordinates used by `elementaryWeight`.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

def coordinatesWeight (r : RootCoordinates) : Weight D₄ :=
  r.1 • simpleRoot D₄ ⟨0, by decide⟩ +
    r.2.1 • simpleRoot D₄ central +
    r.2.2.1 • simpleRoot D₄ ⟨2, by decide⟩ +
    r.2.2.2 • simpleRoot D₄ outer

theorem coordinatesWeight_outerLine (k : ℤ) :
    coordinatesWeight (outerLine k) =
      simpleRoot D₄ outer - k • simpleRoot D₄ outer := by
  funext j
  simp [coordinatesWeight, outerLine]
  ring

theorem coordinatesWeight_at_zero (r : RootCoordinates) :
    coordinatesWeight r ⟨0, by decide⟩ = 2 * r.1 - r.2.1 := by
  rcases r with ⟨a, b, c, d⟩
  norm_num [coordinatesWeight, simpleRoot, cartan, adjacent,
    central, outer, D₄, SimpleLieType.rank]
  change a * 2 + b * (-1) = 2 * a - b
  ring

theorem coordinatesWeight_at_one (r : RootCoordinates) :
    coordinatesWeight r ⟨1, by decide⟩ = -r.1 + 2 * r.2.1 - r.2.2.1 - r.2.2.2 := by
  rcases r with ⟨a, b, c, d⟩
  norm_num [coordinatesWeight, simpleRoot, cartan, adjacent,
    central, outer, D₄, SimpleLieType.rank]
  change a * (-1) + b * 2 + c * (-1) + d * (-1) = -a + 2 * b - c - d
  ring

theorem coordinatesWeight_at_two (r : RootCoordinates) :
    coordinatesWeight r ⟨2, by decide⟩ = -r.2.1 + 2 * r.2.2.1 := by
  rcases r with ⟨a, b, c, d⟩
  norm_num [coordinatesWeight, simpleRoot, cartan, adjacent,
    central, outer, D₄, SimpleLieType.rank]
  change b * (-1) + c * 2 = -b + 2 * c
  ring

theorem coordinatesWeight_at_three (r : RootCoordinates) :
    coordinatesWeight r ⟨3, by decide⟩ = -r.2.1 + 2 * r.2.2.2 := by
  rcases r with ⟨a, b, c, d⟩
  norm_num [coordinatesWeight, simpleRoot, cartan, adjacent,
    central, outer, D₄, SimpleLieType.rank]
  change b * (-1) + d * 2 = -b + 2 * d
  ring

theorem coordinatesWeight_injective : Function.Injective coordinatesWeight := by
  intro x y h
  have h0 := congrFun h (⟨0, by decide⟩ : RootIndex D₄)
  have h1 := congrFun h (⟨1, by decide⟩ : RootIndex D₄)
  have h2 := congrFun h (⟨2, by decide⟩ : RootIndex D₄)
  have h3 := congrFun h (⟨3, by decide⟩ : RootIndex D₄)
  rw [coordinatesWeight_at_zero, coordinatesWeight_at_zero] at h0
  rw [coordinatesWeight_at_one, coordinatesWeight_at_one] at h1
  rw [coordinatesWeight_at_two, coordinatesWeight_at_two] at h2
  rw [coordinatesWeight_at_three, coordinatesWeight_at_three] at h3
  rcases x with ⟨a, b, c, d⟩
  rcases y with ⟨e, f, g, h'⟩
  dsimp at *
  have : a = e ∧ b = f ∧ c = g ∧ d = h' := by omega
  rcases this with ⟨rfl, rfl, rfl, rfl⟩
  rfl

private theorem coordinatesWeight_supported (r : RootCoordinates)
    (h : coordinatesWeight r ∈ roots.map coordinatesWeight ∨
      coordinatesWeight r = 0) :
    r ∈ roots ∨ r = 0 := by
  rcases h with hroot | hzero
  · obtain ⟨s, hs, heq⟩ := List.mem_map.mp hroot
    left
    have he : r = s := coordinatesWeight_injective heq.symm
    simpa [he] using hs
  · right
    have hz : coordinatesWeight (0 : RootCoordinates) = 0 := by
      simp [coordinatesWeight]
    exact coordinatesWeight_injective (hzero.trans hz.symm)

theorem outer_weight_root_string (k : ℤ)
    (h : coordinatesWeight (outerLine k) ∈ roots.map coordinatesWeight ∨
      coordinatesWeight (outerLine k) = 0) :
    k = 0 ∨ k = 1 ∨ k = 2 := by
  exact outer_root_string k (coordinatesWeight_supported _ h)

theorem first_forced_weight_string (k : ℤ)
    (h : coordinatesWeight (1, 2 - k, 1, 1) ∈ roots.map coordinatesWeight ∨
      coordinatesWeight (1, 2 - k, 1, 1) = 0) :
    k = 0 ∨ k = 1 :=
  first_forced_string k (coordinatesWeight_supported _ h)

theorem second_forced_weight_string (k : ℤ)
    (h : coordinatesWeight (1 - k, 1, 1, 1) ∈ roots.map coordinatesWeight ∨
      coordinatesWeight (1 - k, 1, 1, 1) = 0) :
    k = 0 ∨ k = 1 :=
  second_forced_string k (coordinatesWeight_supported _ h)

theorem third_forced_weight_string (k : ℤ)
    (h : coordinatesWeight (0, 1, 1 - k, 1) ∈ roots.map coordinatesWeight ∨
      coordinatesWeight (0, 1, 1 - k, 1) = 0) :
    k = 0 ∨ k = 1 :=
  third_forced_string k (coordinatesWeight_supported _ h)

theorem fourth_forced_weight_string (k : ℤ)
    (h : coordinatesWeight (0, 1 - k, 0, 1) ∈ roots.map coordinatesWeight ∨
      coordinatesWeight (0, 1 - k, 0, 1) = 0) :
    k = 0 ∨ k = 1 :=
  fourth_forced_string k (coordinatesWeight_supported _ h)

theorem final_monomial_weight : monomialWeight M = simpleRoot D₄ outer := by
  rw [← base_factors_monomial, monomialOfFactors_weight, base_factors_weight]

theorem initial_monomial_weight :
    monomialWeight M₀ = coordinatesWeight (1, 2, 1, 1) := by
  rw [M₀, monomialWeight_Y]
  have hci : (1 : Fin 4) = central := by ext; rfl
  rw [hci, central_fundamental_is_highest_root]
  simp [coordinatesWeight]

theorem first_monomial_weight :
    monomialWeight M₁ = coordinatesWeight (1, 1, 1, 1) := by
  rw [← first_prefix_monomial, monomialOfFactors_weight,
    first_prefix_weight]
  simp [coordinatesWeight]

theorem second_monomial_weight :
    monomialWeight M₂ = coordinatesWeight (0, 1, 1, 1) := by
  rw [← second_prefix_monomial, monomialOfFactors_weight,
    second_prefix_weight]
  simp [coordinatesWeight]

theorem third_monomial_weight :
    monomialWeight M₃ = coordinatesWeight (0, 1, 0, 1) := by
  rw [← third_prefix_monomial, monomialOfFactors_weight,
    third_prefix_weight]
  simp [coordinatesWeight]

theorem first_line_weight (k : ℤ) :
    coordinatesWeight (1, 2 - k, 1, 1) =
      monomialWeight M₀ - k • simpleRoot D₄ central := by
  rw [initial_monomial_weight]
  funext j
  simp [coordinatesWeight, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

/-- Finite forcing of the first prescribed monomial, assuming a distinct
screening-signature partner with root-or-zero weight. -/
theorem first_partner_of_root_support (N : Monomial) (da db : ℤ)
    (hsig : tDifference (N - M₀) = A 1 (-1) 0 - A 1 da db)
    (hsupport : monomialWeight N ∈ roots.map coordinatesWeight ∨
      monomialWeight N = 0)
    (hne : N ≠ M₀) : N = M₁ := by
  obtain ⟨k, hda, hdb⟩ := minus_pole_lattice 1 M₀ N (-1) 0 da db hsig
  have hw := minus_signature_weight_displacement 1 M₀ N (-1) 0 da db k hsig hdb
  have hci : (1 : Fin 4) = central := by ext; rfl
  rw [hci] at hw
  have hc : monomialWeight N = coordinatesWeight (1, 2 - k, 1, 1) := by
    rw [hw, first_line_weight]
  have hk := first_forced_weight_string k (by
    rcases hsupport with hs | hs
    · left; rw [← hc]; exact hs
    · right; rw [← hc]; exact hs)
  rcases hk with hk | hk
  · have hd : db = 0 := by omega
    rw [hda, hd] at hsig
    have hz : tDifference (N - M₀) = 0 := by simpa using hsig
    exact False.elim (hne (sub_eq_zero.mp (tDifference_eq_zero _ hz)))
  · have hd : db = 2 := by omega
    rw [hda, hd] at hsig
    have heq : N - M₀ = M₁ - M₀ :=
      tDifference_injective (hsig.trans forced_signature_0.symm)
    simpa using congrArg (fun x : Monomial => x + M₀) heq

private theorem forced_partner_generic (P Next : Monomial) (i : Fin 4)
    (ca cb : ℤ) (line : ℤ → RootCoordinates)
    (hline : ∀ k, coordinatesWeight (line k) =
      monomialWeight P - k • simpleRoot D₄ i)
    (hroot : ∀ k, coordinatesWeight (line k) ∈ roots.map coordinatesWeight ∨
      coordinatesWeight (line k) = 0 → k = 0 ∨ k = 1)
    (hnext : tDifference (Next - P) = A i ca cb - A i ca (cb + 2))
    (N : Monomial) (da db : ℤ)
    (hsig : tDifference (N - P) = A i ca cb - A i da db)
    (hsupport : monomialWeight N ∈ roots.map coordinatesWeight ∨
      monomialWeight N = 0)
    (hne : N ≠ P) : N = Next := by
  obtain ⟨k, hda, hdb⟩ := minus_pole_lattice i P N ca cb da db hsig
  have hw := minus_signature_weight_displacement i P N ca cb da db k hsig hdb
  have hc : monomialWeight N = coordinatesWeight (line k) := by rw [hw, hline]
  have hk := hroot k (by
    rcases hsupport with hs | hs
    · left; rw [← hc]; exact hs
    · right; rw [← hc]; exact hs)
  rcases hk with hk | hk
  · have hd : db = cb := by omega
    rw [hda, hd] at hsig
    have hz : tDifference (N - P) = 0 := by simpa using hsig
    exact False.elim (hne (sub_eq_zero.mp (tDifference_eq_zero _ hz)))
  · have hd : db = cb + 2 := by omega
    rw [hda, hd] at hsig
    have heq : N - P = Next - P :=
      tDifference_injective (hsig.trans hnext.symm)
    simpa using congrArg (fun x : Monomial => x + P) heq

theorem second_line_weight (k : ℤ) :
    coordinatesWeight (1 - k, 1, 1, 1) =
      monomialWeight M₁ - k • simpleRoot D₄ (0 : Fin 4) := by
  have hi : (0 : Fin 4) = (⟨0, by decide⟩ : RootIndex D₄) := by ext; rfl
  rw [hi]
  rw [first_monomial_weight]
  funext j
  simp [coordinatesWeight, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

theorem third_line_weight (k : ℤ) :
    coordinatesWeight (0, 1, 1 - k, 1) =
      monomialWeight M₂ - k • simpleRoot D₄ (2 : Fin 4) := by
  have hi : (2 : Fin 4) = (⟨2, by decide⟩ : RootIndex D₄) := by ext; rfl
  rw [hi]
  rw [second_monomial_weight]
  funext j
  simp [coordinatesWeight, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

theorem fourth_line_weight (k : ℤ) :
    coordinatesWeight (0, 1 - k, 0, 1) =
      monomialWeight M₃ - k • simpleRoot D₄ (1 : Fin 4) := by
  have hi : (1 : Fin 4) = central := by ext; rfl
  rw [hi]
  rw [third_monomial_weight]
  funext j
  simp [coordinatesWeight, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

theorem second_partner_of_root_support (N : Monomial) (da db : ℤ)
    (hsig : tDifference (N - M₁) = A 0 (-2) 1 - A 0 da db)
    (hsupport : monomialWeight N ∈ roots.map coordinatesWeight ∨
      monomialWeight N = 0) (hne : N ≠ M₁) : N = M₂ := by
  exact forced_partner_generic M₁ M₂ 0 (-2) 1
    (fun k => (1 - k, 1, 1, 1)) second_line_weight
    second_forced_weight_string forced_signature_1 N da db hsig hsupport hne

theorem third_partner_of_root_support (N : Monomial) (da db : ℤ)
    (hsig : tDifference (N - M₂) = A 2 (-2) 1 - A 2 da db)
    (hsupport : monomialWeight N ∈ roots.map coordinatesWeight ∨
      monomialWeight N = 0) (hne : N ≠ M₂) : N = M₃ := by
  exact forced_partner_generic M₂ M₃ 2 (-2) 1
    (fun k => (0, 1, 1 - k, 1)) third_line_weight
    third_forced_weight_string forced_signature_2 N da db hsig hsupport hne

theorem fourth_partner_of_root_support (N : Monomial) (da db : ℤ)
    (hsig : tDifference (N - M₃) = A 1 (-3) 2 - A 1 da db)
    (hsupport : monomialWeight N ∈ roots.map coordinatesWeight ∨
      monomialWeight N = 0) (hne : N ≠ M₃) : N = M := by
  exact forced_partner_generic M₃ M 1 (-3) 2
    (fun k => (0, 1 - k, 0, 1)) fourth_line_weight
    fourth_forced_weight_string forced_signature_3 N da db hsig hsupport hne

/-- The finite root support and the moment identity discharge the weight
restriction in the final minus-screening partner classification. -/
theorem final_minus_partner_of_root_support (N : Monomial) (da db : ℤ)
    (hsig : tDifference (N - M) = A 3 (-2) 1 - A 3 da db)
    (hsupport : monomialWeight N ∈ roots.map coordinatesWeight ∨
      monomialWeight N = 0) :
    N = M ∨ N = Z ∨ N = Nminus := by
  apply final_minus_partner_cases N da db hsig
  intro k ⟨_, hdb⟩
  have hw := minus_signature_weight_displacement 3 M N (-2) 1 da db k hsig hdb
  rw [final_monomial_weight] at hw
  have hi : (3 : Fin 4) = outer := by ext; rfl
  rw [hi] at hw
  have hc : monomialWeight N = coordinatesWeight (outerLine k) := by
    rw [hw, ← coordinatesWeight_outerLine]
  apply outer_weight_root_string k
  rcases hsupport with hs | hs
  · left; rw [← hc]; exact hs
  · right; rw [← hc]; exact hs

/-- The analogous conclusion for the plus-screening signature. -/
theorem final_plus_partner_of_root_support (N : Monomial) (da db : ℤ)
    (hsig : qDifference (N - M) = A 3 da db - A 3 (-1) 2)
    (hsupport : monomialWeight N ∈ roots.map coordinatesWeight ∨
      monomialWeight N = 0) :
    N = M ∨ N = Z ∨ N = Nplus := by
  apply final_plus_partner_cases N da db hsig
  intro k ⟨_, hda⟩
  have hw := plus_signature_weight_displacement 3 M N (-1) 2 da db k hsig hda
  rw [final_monomial_weight] at hw
  have hi : (3 : Fin 4) = outer := by ext; rfl
  rw [hi] at hw
  have hc : monomialWeight N = coordinatesWeight (outerLine (-k)) := by
    rw [hw, coordinatesWeight_outerLine]
    simp
  have hk := outer_weight_root_string (-k) (by
    rcases hsupport with hs | hs
    · left; rw [← hc]; exact hs
    · right; rw [← hc]; exact hs)
  omega

end FrenkelReshetikhin.D4CounterexampleProof
