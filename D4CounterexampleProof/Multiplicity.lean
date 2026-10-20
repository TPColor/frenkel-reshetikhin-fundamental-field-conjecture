import D4CounterexampleProof.Weights

/-!
The elementary positivity condition turns a weight multiplicity of one into
exactly one elementary term at that weight. The required negative-root
multiplicity for the original central fundamental module is proved in
`FundamentalCharacter.lean`.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

/-- A positive specialized coefficient is a nonzero rational function at
generic q,t, so every required screening residue keeps a nonzero scalar. -/
theorem coefficient_ne_zero_of_valid {g : SimpleLieType}
    (term : ElementaryTerm g) (hvalid : term.valid) : term.coefficient ≠ 0 := by
  intro hzero
  obtain ⟨hpos, hspecial⟩ := hvalid
  rcases hspecial with ⟨_, heval⟩
  rw [hzero] at heval
  simp at heval
  have hnat : (term.multiplicity : QuantumCoefficient) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  exact hnat heval.symm

/-- Every elementary term contributes positively to the multiplicity of its
own ordinary weight. This uses the conjecture's positive specialization, not
any representation-theoretic statement. -/
theorem term_weight_expansionMultiplicity_pos {g : SimpleLieType}
    (i : RootIndex g) (terms : List (ElementaryTerm g))
    (hvalid : ∀ term ∈ terms, term.valid)
    (term : ElementaryTerm g) (hterm : term ∈ terms) :
    0 < expansionMultiplicity i terms (elementaryWeight i term.factors) := by
  have hpos : 0 < term.multiplicity := (hvalid term hterm).1
  have hmem : term.multiplicity ∈
      terms.map (fun x => if elementaryWeight i x.factors =
        elementaryWeight i term.factors then x.multiplicity else 0) := by
    apply List.mem_map.mpr
    exact ⟨term, hterm, by simp⟩
  have hle : term.multiplicity ≤
      (terms.map (fun x => if elementaryWeight i x.factors =
        elementaryWeight i term.factors then x.multiplicity else 0)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) term.multiplicity hmem
  unfold expansionMultiplicity
  omega

private theorem count_matching_le_sum {g : SimpleLieType} (i : RootIndex g)
    (weight : Weight g) (terms : List (ElementaryTerm g))
    (hvalid : ∀ term ∈ terms, term.valid) :
    terms.countP (fun term => elementaryWeight i term.factors = weight) ≤
      (terms.map fun term =>
        if elementaryWeight i term.factors = weight then term.multiplicity else 0).sum := by
  classical
  induction terms with
  | nil => simp
  | cons term tail ih =>
    have hterm : 0 < term.multiplicity := (hvalid term (by simp)).1
    have htail : ∀ t ∈ tail, t.valid := by
      intro t ht
      exact hvalid t (by simp [ht])
    specialize ih htail
    by_cases hmatch : elementaryWeight i term.factors = weight
    · simp [hmatch]
      omega
    · simp [hmatch]
      omega

/-- A multiplicity-one weight distinct from the leading weight is occupied
by exactly one elementary term. -/
theorem unique_term_at_multiplicity_one {g : SimpleLieType} (i : RootIndex g)
    (weight : Weight g) (terms : List (ElementaryTerm g))
    (hweight : weight ≠ fundamentalWeight g i)
    (hvalid : ∀ term ∈ terms, term.valid)
    (hone : expansionMultiplicity i terms weight = 1) :
    terms.countP (fun term => elementaryWeight i term.factors = weight) = 1 := by
  classical
  have hsum :
      (terms.map fun term =>
        if elementaryWeight i term.factors = weight then term.multiplicity else 0).sum = 1 := by
    simpa only [expansionMultiplicity, if_neg hweight, zero_add] using hone
  have hle := count_matching_le_sum i weight terms hvalid
  rw [hsum] at hle
  have hpos : 0 < terms.countP (fun term => elementaryWeight i term.factors = weight) := by
    by_contra h
    have hz : terms.countP (fun term => elementaryWeight i term.factors = weight) = 0 := by omega
    have hall : ∀ term ∈ terms, elementaryWeight i term.factors ≠ weight := by
      intro term ht heq
      have hh := List.countP_eq_zero.mp hz term ht
      simp [heq] at hh
    have hzero :
        (terms.map fun term =>
          if elementaryWeight i term.factors = weight then term.multiplicity else 0).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hx
      simp [hall term hterm]
    omega
  omega

/-- The one matching term is unique as a list entry, independently of its
coefficient or its spectral labels. -/
theorem matching_terms_equal {g : SimpleLieType} (i : RootIndex g)
    (weight : Weight g) (terms : List (ElementaryTerm g))
    (hweight : weight ≠ fundamentalWeight g i)
    (hvalid : ∀ term ∈ terms, term.valid)
    (hone : expansionMultiplicity i terms weight = 1)
    (x y : ElementaryTerm g) (hx : x ∈ terms) (hy : y ∈ terms)
    (hxw : elementaryWeight i x.factors = weight)
    (hyw : elementaryWeight i y.factors = weight) : x = y := by
  classical
  have hc := unique_term_at_multiplicity_one i weight terms hweight hvalid hone
  rw [List.countP_eq_length_filter] at hc
  obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hc
  have hxf : x ∈ terms.filter (fun term => elementaryWeight i term.factors = weight) :=
    List.mem_filter.mpr ⟨hx, by simp [hxw]⟩
  have hyf : y ∈ terms.filter (fun term => elementaryWeight i term.factors = weight) :=
    List.mem_filter.mpr ⟨hy, by simp [hyw]⟩
  rw [hz] at hxf hyf
  simp only [List.mem_singleton] at hxf hyf
  exact hxf.trans hyf.symm

/-- The finite-monomial contradiction once the two screening arguments have
produced terms of weight -α₄. The missing analytic and representation theory
work is precisely what must supply `hminus`, `hplus`, and `hone`. -/
theorem incompatible_screening_requirements
    (terms : List (ElementaryTerm D₄)) (weight : Weight D₄)
    (hweight : weight ≠ fundamentalWeight D₄ ⟨1, by decide⟩)
    (hvalid : ∀ term ∈ terms, term.valid)
    (hone : expansionMultiplicity (g := D₄) ⟨1, by decide⟩ terms weight = 1)
    (hminus : ∃ term ∈ terms,
      elementaryWeight (g := D₄) ⟨1, by decide⟩ term.factors = weight ∧
      monomialOfFactors term.factors = Nminus)
    (hplus : ∃ term ∈ terms,
      elementaryWeight (g := D₄) ⟨1, by decide⟩ term.factors = weight ∧
      monomialOfFactors term.factors = Nplus) : False := by
  obtain ⟨x, hx, hxw, hxmono⟩ := hminus
  obtain ⟨y, hy, hyw, hymono⟩ := hplus
  have hxy := matching_terms_equal ⟨1, by decide⟩ weight terms hweight hvalid hone x y hx hy hxw hyw
  apply incompatible_endpoints
  calc
    Nminus = monomialOfFactors x.factors := hxmono.symm
    _ = monomialOfFactors y.factors := by rw [hxy]
    _ = Nplus := hymono

end
end FrenkelReshetikhin.D4CounterexampleProof
