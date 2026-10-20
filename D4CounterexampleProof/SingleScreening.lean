import D4CounterexampleProof.PartnerForcing
import D4CounterexampleProof.Multiplicity

/-! The finite partner classifications in the note's independent argument
using only the minus screening. Pole-partner existence is still an input. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

private theorem signature_unique_at_source (N P Q : Monomial)
    (h : tDifference (N - P) = tDifference (Q - P)) : N = Q := by
  have he : N - P = Q - P := tDifference_injective h
  have hh := congrArg (fun m : Monomial => m + P) he
  simpa only [sub_add_cancel] using hh

theorem second_minus_partner_of_root_support (N : Monomial) (da db : ℤ)
    (hsig : tDifference (N - M) = A 3 (-4) 3 - A 3 da db)
    (hsupport : monomialWeight N ∈ roots.map coordinatesWeight ∨ monomialWeight N = 0) :
    N = M ∨ N = Zprime ∨ N = Nprime := by
  obtain ⟨k, hda, hdb⟩ := minus_outer_pole_lattice M N (-4) 3 da db hsig
  have hw := minus_signature_weight_displacement 3 M N (-4) 3 da db k hsig hdb
  rw [final_monomial_weight] at hw
  have hi : (3 : Fin 4) = outer := by ext; rfl
  rw [hi] at hw
  have hc : monomialWeight N = coordinatesWeight (outerLine k) := by
    rw [hw, coordinatesWeight_outerLine]
  have hk := outer_weight_root_string k (by
    rcases hsupport with hs | hs
    · left; rw [← hc]; exact hs
    · right; rw [← hc]; exact hs)
  rcases hk with hk | hk | hk
  · have hd : db = 3 := by omega
    rw [hda, hd, sub_self] at hsig
    exact Or.inl (same_minus_pole_unique N hsig)
  · have hd : db = 5 := by omega
    rw [hda, hd] at hsig
    exact Or.inr (Or.inl (signature_unique_at_source N M Zprime
      (hsig.trans second_intermediate_signature_match.symm)))
  · have hd : db = 7 := by omega
    rw [hda, hd] at hsig
    exact Or.inr (Or.inr (signature_unique_at_source N M Nprime
      (hsig.trans second_negative_signature_match.symm)))

theorem prime_monomial_weight : monomialWeight Zprime = 0 := by
  simp [Zprime, monomialWeight_sub, monomialWeight_Y]

theorem prime_minus_partner_of_root_support (N : Monomial) (da db : ℤ)
    (hsig : tDifference (N - Zprime) = A 3 (-2) 1 - A 3 da db)
    (hsupport : monomialWeight N ∈ roots.map coordinatesWeight ∨ monomialWeight N = 0) :
    N = positivePrimePartner ∨ N = Zprime ∨ N = negativePrimePartner := by
  obtain ⟨k, hda, hdb⟩ := minus_outer_pole_lattice Zprime N (-2) 1 da db hsig
  have hw := minus_signature_weight_displacement 3 Zprime N (-2) 1 da db k hsig hdb
  rw [prime_monomial_weight, zero_sub] at hw
  have hi : (3 : Fin 4) = outer := by ext; rfl
  rw [hi] at hw
  have hc : monomialWeight N = coordinatesWeight (outerLine (k + 1)) := by
    rw [hw, coordinatesWeight_outerLine]
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  have hk := outer_weight_root_string (k + 1) (by
    rcases hsupport with hs | hs
    · left; rw [← hc]; exact hs
    · right; rw [← hc]; exact hs)
  rcases hk with hk | hk | hk
  · have hd : db = -1 := by omega
    rw [hda, hd] at hsig
    exact Or.inl (signature_unique_at_source N Zprime positivePrimePartner
      (hsig.trans prime_positive_signature_match.symm))
  · have hd : db = 1 := by omega
    rw [hda, hd, sub_self] at hsig
    right; left
    apply signature_unique_at_source N Zprime Zprime
    simpa [tDifference, shift] using hsig
  · have hd : db = 3 := by omega
    rw [hda, hd] at hsig
    exact Or.inr (Or.inr (signature_unique_at_source N Zprime negativePrimePartner
      (hsig.trans prime_negative_signature_match.symm)))

theorem second_negative_monomial_weight : monomialWeight Nprime = -simpleRoot D₄ outer := by
  rw [Nprime, monomialWeight_sub, monomialWeight_sub, monomialWeight_A, monomialWeight_A,
    final_monomial_weight]
  funext j
  simp only [Pi.sub_apply, Pi.neg_apply]
  change simpleRoot D₄ outer j - simpleRoot D₄ outer j - simpleRoot D₄ outer j =
    -simpleRoot D₄ outer j
  ring

theorem positive_prime_monomial_weight :
    monomialWeight positivePrimePartner = simpleRoot D₄ outer := by
  rw [positivePrimePartner, monomialWeight_add, prime_monomial_weight, monomialWeight_A, zero_add]
  rfl

theorem negative_prime_monomial_weight :
    monomialWeight negativePrimePartner = -simpleRoot D₄ outer := by
  rw [negativePrimePartner, monomialWeight_sub, prime_monomial_weight, monomialWeight_A, zero_sub]
  rfl

/-- The finite contradiction in the note's second argument uses only
minus-screening partners. This conditional finite lemma takes pole partners
and the two multiplicity-one consequences as explicit inputs. -/
theorem single_minus_obstruction (terms : List Monomial)
    (hsupport : ∀ N ∈ terms,
      monomialWeight N ∈ roots.map coordinatesWeight ∨ monomialWeight N = 0)
    (hpositive : ∀ N ∈ terms, monomialWeight N = simpleRoot D₄ outer → N = M)
    (hnegative : ∀ N ∈ terms, monomialWeight N = -simpleRoot D₄ outer → N = Nminus)
    (hsecond : ∃ N ∈ terms, ∃ da db : ℤ,
      tDifference (N - M) = A 3 (-4) 3 - A 3 da db ∧ N ≠ M)
    (hprime : Zprime ∈ terms → ∃ N ∈ terms, ∃ da db : ℤ,
      tDifference (N - Zprime) = A 3 (-2) 1 - A 3 da db ∧ N ≠ Zprime) : False := by
  have hz : Zprime ∈ terms := by
    obtain ⟨N, hN, da, db, hsig, hne⟩ := hsecond
    rcases second_minus_partner_of_root_support N da db hsig (hsupport N hN) with hm | hz | hn
    · exact False.elim (hne hm)
    · simpa only [hz] using hN
    · have hw : monomialWeight N = -simpleRoot D₄ outer := by
        rw [hn, second_negative_monomial_weight]
      have he := (hn.symm.trans (hnegative N hN hw))
      exact False.elim (second_pole_negative_distinct he)
  obtain ⟨N, hN, da, db, hsig, hne⟩ := hprime hz
  rcases prime_minus_partner_of_root_support N da db hsig (hsupport N hN) with hp | hz | hn
  · have hw : monomialWeight N = simpleRoot D₄ outer := by
      rw [hp, positive_prime_monomial_weight]
    exact positive_prime_partner_distinct (hp.symm.trans (hpositive N hN hw))
  · exact hne hz
  · have hw : monomialWeight N = -simpleRoot D₄ outer := by
      rw [hn, negative_prime_monomial_weight]
    exact negative_prime_partner_distinct (hn.symm.trans (hnegative N hN hw))

/-- The four predecessor steps follow from one uniform pole-partner
principle, rather than assuming the final monomial occurs in the field. -/
theorem forced_chain_of_minus_partners (terms : List Monomial)
    (hsupport : ∀ N ∈ terms,
      monomialWeight N ∈ roots.map coordinatesWeight ∨ monomialWeight N = 0)
    (hpartner : ∀ P ∈ M₀ :: terms, ∀ (i : Fin 4) (ca cb : ℤ),
      minusPoleOrder P i (ca, cb) = 1 →
      ∃ N ∈ terms, ∃ da db : ℤ,
        tDifference (N - P) = A i ca cb - A i da db ∧ N ≠ P) : M ∈ terms := by
  obtain ⟨N₁, hN₁, da₁, db₁, hs₁, hn₁⟩ :=
    hpartner M₀ (by simp) 1 (-1) 0 forcing_pole_0
  have he₁ := first_partner_of_root_support N₁ da₁ db₁ hs₁ (hsupport N₁ hN₁) hn₁
  have h₁ : M₁ ∈ terms := he₁ ▸ hN₁
  obtain ⟨N₂, hN₂, da₂, db₂, hs₂, hn₂⟩ :=
    hpartner M₁ (by simp [h₁]) 0 (-2) 1 forcing_pole_1
  have he₂ := second_partner_of_root_support N₂ da₂ db₂ hs₂ (hsupport N₂ hN₂) hn₂
  have h₂ : M₂ ∈ terms := he₂ ▸ hN₂
  obtain ⟨N₃, hN₃, da₃, db₃, hs₃, hn₃⟩ :=
    hpartner M₂ (by simp [h₂]) 2 (-2) 1 forcing_pole_2
  have he₃ := third_partner_of_root_support N₃ da₃ db₃ hs₃ (hsupport N₃ hN₃) hn₃
  have h₃ : M₃ ∈ terms := he₃ ▸ hN₃
  obtain ⟨N₄, hN₄, da₄, db₄, hs₄, hn₄⟩ :=
    hpartner M₃ (by simp [h₃]) 1 (-3) 2 forcing_pole_3
  have he₄ := fourth_partner_of_root_support N₄ da₄ db₄ hs₄ (hsupport N₄ hN₄) hn₄
  exact he₄ ▸ hN₄

/-- A uniform minus pole-partner theorem would suffice for the entire
finite contradiction, including forcing the four predecessors of M.
Its operator-theoretic proof is deliberately not assumed as an axiom. -/
theorem no_minus_closed_family (terms : List Monomial)
    (hsupport : ∀ N ∈ terms,
      monomialWeight N ∈ roots.map coordinatesWeight ∨ monomialWeight N = 0)
    (hpositive : ∀ N ∈ terms, monomialWeight N = simpleRoot D₄ outer → N = M)
    (hnegative : ∀ N ∈ terms, monomialWeight N = -simpleRoot D₄ outer → N = Nminus)
    (hpartner : ∀ P ∈ M₀ :: terms, ∀ (i : Fin 4) (ca cb : ℤ),
      minusPoleOrder P i (ca, cb) = 1 →
      ∃ N ∈ terms, ∃ da db : ℤ,
        tDifference (N - P) = A i ca cb - A i da db ∧ N ≠ P) : False := by
  have hM := forced_chain_of_minus_partners terms hsupport hpartner
  apply single_minus_obstruction terms hsupport hpositive hnegative
  · exact hpartner M (by simp [hM]) 3 (-4) 3 second_minus_pole
  · intro hz
    exact hpartner Zprime (by simp [hz]) 3 (-2) 1 second_intermediate_minus_pole

end
end FrenkelReshetikhin.D4CounterexampleProof
