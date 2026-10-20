import D4CounterexampleProof.MonomialCertificate

/-!
Cross-multiplied first-creation-mode signature equations from the note.
These are exact identities in free Laurent monomials. They establish that
the proposed partners have matching algebraic signatures; they do not prove
that a screening commutator forces either partner to occur.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

def shift (a b : ℤ) (m : Monomial) : Monomial :=
  Finsupp.mapDomain
    (fun key : Fin 4 × Spectral => (key.1, (key.2.1 + a, key.2.2 + b))) m

private theorem shift_at_translated (a b : ℤ) (m : Monomial)
    (key : Fin 4 × Spectral) :
    shift a b m (key.1, (key.2.1 + a, key.2.2 + b)) = m key := by
  unfold shift
  apply Finsupp.mapDomain_apply
  intro x y h
  rcases x with ⟨ix, qx, tx⟩
  rcases y with ⟨iy, qy, ty⟩
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hix, hq, ht⟩
  exact Prod.ext hix (Prod.ext (add_right_cancel hq) (add_right_cancel ht))

/-- A finitely supported Laurent monomial cannot be invariant under a
nonzero translation of its t-exponents. -/
private theorem no_t_period (m : Monomial) (hperiod : shift 0 2 m = m) : m = 0 := by
  classical
  by_contra hm
  let S : Finset ℤ := m.support.image (fun key => key.2.2)
  have hS : S.Nonempty := (Finsupp.support_nonempty_iff.mpr hm).image _
  let B := S.max' hS
  have hB : B ∈ S := Finset.max'_mem S hS
  obtain ⟨key, hkey, hcoord⟩ := Finset.mem_image.mp hB
  have hshift : m (key.1, (key.2.1, key.2.2 + 2)) = m key := by
    have h := congrArg (fun x : Monomial => x (key.1, (key.2.1, key.2.2 + 2))) hperiod
    have h0 : shift 0 2 m (key.1, (key.2.1, key.2.2 + 2)) = m key := by
      simpa using shift_at_translated 0 2 m key
    rw [h0] at h
    exact h.symm
  have hkey' : (key.1, (key.2.1, key.2.2 + 2)) ∈ m.support := by
    apply Finsupp.mem_support_iff.mpr
    rw [hshift]
    exact Finsupp.mem_support_iff.mp hkey
  have hle : key.2.2 + 2 ≤ B :=
    Finset.le_max' (s := S) (key.2.2 + 2)
      (Finset.mem_image.mpr ⟨(key.1, (key.2.1, key.2.2 + 2)), hkey', rfl⟩)
  omega

def tDifference (m : Monomial) : Monomial := shift 0 1 m - shift 0 (-1) m
def qDifference (m : Monomial) : Monomial := shift 1 0 m - shift (-1) 0 m

def qProjection (m : Monomial) : (Fin 4 × ℤ) →₀ ℤ :=
  Finsupp.mapDomain (fun key : Fin 4 × Spectral => (key.1, key.2.1)) m

def parityProjection (m : Monomial) : (Fin 4 × ℤ × ℤ) →₀ ℤ :=
  Finsupp.mapDomain
    (fun key : Fin 4 × Spectral => (key.1, key.2.1, key.2.2 % 2)) m

def tProjection (m : Monomial) : (Fin 4 × ℤ) →₀ ℤ :=
  Finsupp.mapDomain (fun key : Fin 4 × Spectral => (key.1, key.2.2)) m

def qParityProjection (m : Monomial) : (Fin 4 × ℤ × ℤ) →₀ ℤ :=
  Finsupp.mapDomain
    (fun key : Fin 4 × Spectral => (key.1, key.2.2, key.2.1 % 2)) m

private theorem qProjection_sub (m n : Monomial) :
    qProjection (m - n) = qProjection m - qProjection n := by
  exact Finsupp.mapDomain_sub

private theorem parityProjection_sub (m n : Monomial) :
    parityProjection (m - n) = parityProjection m - parityProjection n := by
  exact Finsupp.mapDomain_sub

private theorem tProjection_sub (m n : Monomial) :
    tProjection (m - n) = tProjection m - tProjection n := by
  exact Finsupp.mapDomain_sub

private theorem qParityProjection_sub (m n : Monomial) :
    qParityProjection (m - n) = qParityProjection m - qParityProjection n := by
  exact Finsupp.mapDomain_sub

private theorem qProjection_tShift (b : ℤ) (m : Monomial) :
    qProjection (shift 0 b m) = qProjection m := by
  unfold qProjection shift
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext key
  simp

theorem qProjection_tDifference (m : Monomial) :
    qProjection (tDifference m) = 0 := by
  change qProjection (shift 0 1 m - shift 0 (-1) m) = 0
  rw [qProjection, Finsupp.mapDomain_sub]
  change qProjection (shift 0 1 m) - qProjection (shift 0 (-1) m) = 0
  rw [qProjection_tShift, qProjection_tShift, sub_self]

private theorem parityProjection_tShift (m : Monomial) :
    parityProjection (shift 0 1 m) = parityProjection (shift 0 (-1) m) := by
  unfold parityProjection shift
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro key _
  simp only [Function.comp_apply]
  have hpar : (key.2.2 + 1) % 2 = (key.2.2 + -1) % 2 := by omega
  rw [hpar]

theorem parityProjection_tDifference (m : Monomial) :
    parityProjection (tDifference m) = 0 := by
  change parityProjection (shift 0 1 m - shift 0 (-1) m) = 0
  rw [parityProjection, Finsupp.mapDomain_sub]
  change parityProjection (shift 0 1 m) - parityProjection (shift 0 (-1) m) = 0
  rw [parityProjection_tShift, sub_self]

private theorem tProjection_qShift (a : ℤ) (m : Monomial) :
    tProjection (shift a 0 m) = tProjection m := by
  unfold tProjection shift
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext key
  simp

theorem tProjection_qDifference (m : Monomial) :
    tProjection (qDifference m) = 0 := by
  change tProjection (shift 1 0 m - shift (-1) 0 m) = 0
  rw [tProjection_sub, tProjection_qShift, tProjection_qShift, sub_self]

private theorem qParityProjection_qShift (m : Monomial) :
    qParityProjection (shift 1 0 m) = qParityProjection (shift (-1) 0 m) := by
  unfold qParityProjection shift
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro key _
  simp only [Function.comp_apply]
  have hpar : (key.2.1 + 1) % 2 = (key.2.1 + -1) % 2 := by omega
  rw [hpar]

theorem qParityProjection_qDifference (m : Monomial) :
    qParityProjection (qDifference m) = 0 := by
  change qParityProjection (shift 1 0 m - shift (-1) 0 m) = 0
  rw [qParityProjection_sub, qParityProjection_qShift, sub_self]

private theorem qProjection_outer_at_center (a b x : ℤ) :
    qProjection (A 3 a b) (1, x) = if x = a then -1 else 0 := by
  simp [qProjection, A, Y, Finsupp.mapDomain_add, Finsupp.mapDomain_sub,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply];
    split_ifs <;> omega

def neighbor (i : Fin 4) : Fin 4 := if i = 1 then 0 else 1

private theorem qProjection_at_neighbor (i : Fin 4) (a b x : ℤ) :
    qProjection (A i a b) (neighbor i, x) = if x = a then -1 else 0 := by
  fin_cases i <;>
    simp [neighbor, qProjection, A, Y, Finsupp.mapDomain_add,
      Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply] <;>
    split_ifs <;> omega

private theorem parityProjection_at_neighbor (i : Fin 4) (a b x p : ℤ) :
    parityProjection (A i a b) (neighbor i, x, p) =
      if x = a ∧ p = b % 2 then -1 else 0 := by
  fin_cases i <;>
    simp [neighbor, parityProjection, A, Y, Finsupp.mapDomain_add,
      Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply] <;>
    split_ifs <;> omega

private theorem parityProjection_outer_at_center (a b x p : ℤ) :
    parityProjection (A 3 a b) (1, x, p) =
      if x = a ∧ p = b % 2 then -1 else 0 := by
  simp [parityProjection, A, Y, Finsupp.mapDomain_add, Finsupp.mapDomain_sub,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply];
    split_ifs <;> omega

private theorem tProjection_outer_at_center (a b x : ℤ) :
    tProjection (A 3 a b) (1, x) = if x = b then -1 else 0 := by
  simp [tProjection, A, Y, Finsupp.mapDomain_add, Finsupp.mapDomain_sub,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply];
    split_ifs <;> omega

private theorem qParityProjection_outer_at_center (a b x p : ℤ) :
    qParityProjection (A 3 a b) (1, x, p) =
      if x = b ∧ p = a % 2 then -1 else 0 := by
  simp [qParityProjection, A, Y, Finsupp.mapDomain_add, Finsupp.mapDomain_sub,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply];
    split_ifs <;> omega

private theorem tProjection_at_neighbor (i : Fin 4) (a b x : ℤ) :
    tProjection (A i a b) (neighbor i, x) = if x = b then -1 else 0 := by
  fin_cases i <;>
    simp [neighbor, tProjection, A, Y, Finsupp.mapDomain_add,
      Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply] <;>
    split_ifs <;> omega

private theorem qParityProjection_at_neighbor (i : Fin 4) (a b x p : ℤ) :
    qParityProjection (A i a b) (neighbor i, x, p) =
      if x = b ∧ p = a % 2 then -1 else 0 := by
  fin_cases i <;>
    simp [neighbor, qParityProjection, A, Y, Finsupp.mapDomain_add,
      Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply] <;>
    split_ifs <;> omega

/-- Matching a minus-screening signature at outer node 4 forces the partner
pole to have the same q exponent and an even t displacement. -/
theorem minus_outer_pole_lattice (P N : Monomial)
    (ca cb da db : ℤ)
    (h : tDifference (N - P) = A 3 ca cb - A 3 da db) :
    ∃ k : ℤ, da = ca ∧ db = cb + 2 * k := by
  have hq := congrArg (fun x : (Fin 4 × ℤ) →₀ ℤ => x (1, ca))
    (congrArg qProjection h)
  have hda : da = ca := by
    simp only [qProjection_tDifference, Finsupp.zero_apply] at hq
    rw [qProjection_sub, Finsupp.sub_apply] at hq
    rw [qProjection_outer_at_center, qProjection_outer_at_center] at hq
    by_contra hne
    split_ifs at hq <;> omega
  have hp := congrArg (fun x : (Fin 4 × ℤ × ℤ) →₀ ℤ => x (1, ca, cb % 2))
    (congrArg parityProjection h)
  have hpar : db % 2 = cb % 2 := by
    simp only [parityProjection_tDifference, Finsupp.zero_apply] at hp
    rw [hda] at hp
    rw [parityProjection_sub, Finsupp.sub_apply] at hp
    rw [parityProjection_outer_at_center, parityProjection_outer_at_center] at hp
    by_contra hne
    split_ifs at hp <;> omega
  refine ⟨(db - cb) / 2, hda, ?_⟩
  omega

/-- The same pole-lattice restriction at every D₄ node. Each node has a
neighbor whose Y-coordinate isolates the root factor's spectral label. -/
theorem minus_pole_lattice (i : Fin 4) (P N : Monomial)
    (ca cb da db : ℤ)
    (h : tDifference (N - P) = A i ca cb - A i da db) :
    ∃ k : ℤ, da = ca ∧ db = cb + 2 * k := by
  have hq := congrArg (fun x : (Fin 4 × ℤ) →₀ ℤ => x (neighbor i, ca))
    (congrArg qProjection h)
  have hda : da = ca := by
    simp only [qProjection_tDifference, Finsupp.zero_apply] at hq
    rw [qProjection_sub, Finsupp.sub_apply,
      qProjection_at_neighbor, qProjection_at_neighbor] at hq
    by_contra hne
    split_ifs at hq <;> omega
  have hp := congrArg (fun x : (Fin 4 × ℤ × ℤ) →₀ ℤ =>
      x (neighbor i, ca, cb % 2)) (congrArg parityProjection h)
  have hpar : db % 2 = cb % 2 := by
    simp only [parityProjection_tDifference, Finsupp.zero_apply] at hp
    rw [hda, parityProjection_sub, Finsupp.sub_apply,
      parityProjection_at_neighbor, parityProjection_at_neighbor] at hp
    by_contra hne
    split_ifs at hp <;> omega
  refine ⟨(db - cb) / 2, hda, ?_⟩
  omega

/-- Matching a plus-screening signature forces the same t exponent and an
even q displacement. -/
theorem plus_outer_pole_lattice (P N : Monomial)
    (ca cb da db : ℤ)
    (h : qDifference (N - P) = A 3 da db - A 3 ca cb) :
    ∃ k : ℤ, db = cb ∧ da = ca + 2 * k := by
  have ht := congrArg (fun x : (Fin 4 × ℤ) →₀ ℤ => x (1, cb))
    (congrArg tProjection h)
  have hdb : db = cb := by
    simp only [tProjection_qDifference, Finsupp.zero_apply] at ht
    rw [tProjection_sub, Finsupp.sub_apply,
      tProjection_outer_at_center, tProjection_outer_at_center] at ht
    by_contra hne
    split_ifs at ht <;> omega
  have hp := congrArg (fun x : (Fin 4 × ℤ × ℤ) →₀ ℤ => x (1, cb, ca % 2))
    (congrArg qParityProjection h)
  have hpar : da % 2 = ca % 2 := by
    simp only [qParityProjection_qDifference, Finsupp.zero_apply] at hp
    rw [hdb, qParityProjection_sub, Finsupp.sub_apply,
      qParityProjection_outer_at_center, qParityProjection_outer_at_center] at hp
    by_contra hne
    split_ifs at hp <;> omega
  refine ⟨(da - ca) / 2, hdb, ?_⟩
  omega

theorem plus_pole_lattice (i : Fin 4) (P N : Monomial)
    (ca cb da db : ℤ)
    (h : qDifference (N - P) = A i da db - A i ca cb) :
    ∃ k : ℤ, db = cb ∧ da = ca + 2 * k := by
  have ht := congrArg (fun x : (Fin 4 × ℤ) →₀ ℤ => x (neighbor i, cb))
    (congrArg tProjection h)
  have hdb : db = cb := by
    simp only [tProjection_qDifference, Finsupp.zero_apply] at ht
    rw [tProjection_sub, Finsupp.sub_apply,
      tProjection_at_neighbor, tProjection_at_neighbor] at ht
    by_contra hne
    split_ifs at ht <;> omega
  have hp := congrArg (fun x : (Fin 4 × ℤ × ℤ) →₀ ℤ =>
      x (neighbor i, cb, ca % 2)) (congrArg qParityProjection h)
  have hpar : da % 2 = ca % 2 := by
    simp only [qParityProjection_qDifference, Finsupp.zero_apply] at hp
    rw [hdb, qParityProjection_sub, Finsupp.sub_apply,
      qParityProjection_at_neighbor, qParityProjection_at_neighbor] at hp
    by_contra hne
    split_ifs at hp <;> omega
  refine ⟨(da - ca) / 2, hdb, ?_⟩
  omega

/-- Multiplication by t−t⁻¹ is injective on the Laurent-monomial group. -/
theorem tDifference_eq_zero (m : Monomial) (hzero : tDifference m = 0) : m = 0 := by
  have hrec (key : Fin 4 × Spectral) :
      m (key.1, (key.2.1, key.2.2 + 2)) = m key := by
    have h := congrArg (fun x : Monomial => x (key.1, (key.2.1, key.2.2 + 1))) hzero
    have hp : shift 0 1 m (key.1, (key.2.1, key.2.2 + 1)) = m key := by
      simpa using shift_at_translated 0 1 m key
    have hm : shift 0 (-1) m (key.1, (key.2.1, key.2.2 + 1)) =
        m (key.1, (key.2.1, key.2.2 + 2)) := by
      simpa [add_assoc] using shift_at_translated 0 (-1) m
        (key.1, (key.2.1, key.2.2 + 2))
    simp only [tDifference, Finsupp.sub_apply, Finsupp.zero_apply] at h
    rw [hp, hm] at h
    omega
  apply no_t_period m
  ext key
  let prev : Fin 4 × Spectral := (key.1, (key.2.1, key.2.2 - 2))
  have hs : shift 0 2 m key = m prev := by
    simpa [prev] using shift_at_translated 0 2 m prev
  have hr := hrec prev
  simp only [prev] at hr
  rw [hs]
  convert hr.symm using 1; simp

private theorem no_q_period (m : Monomial) (hperiod : shift 2 0 m = m) : m = 0 := by
  classical
  by_contra hm
  let S : Finset ℤ := m.support.image (fun key => key.2.1)
  have hS : S.Nonempty := (Finsupp.support_nonempty_iff.mpr hm).image _
  let B := S.max' hS
  have hB : B ∈ S := Finset.max'_mem S hS
  obtain ⟨key, hkey, hcoord⟩ := Finset.mem_image.mp hB
  have hshift : m (key.1, (key.2.1 + 2, key.2.2)) = m key := by
    have h := congrArg (fun x : Monomial => x (key.1, (key.2.1 + 2, key.2.2))) hperiod
    have h0 : shift 2 0 m (key.1, (key.2.1 + 2, key.2.2)) = m key := by
      simpa using shift_at_translated 2 0 m key
    rw [h0] at h
    exact h.symm
  have hkey' : (key.1, (key.2.1 + 2, key.2.2)) ∈ m.support := by
    apply Finsupp.mem_support_iff.mpr
    rw [hshift]
    exact Finsupp.mem_support_iff.mp hkey
  have hle : key.2.1 + 2 ≤ B :=
    Finset.le_max' (s := S) (key.2.1 + 2)
      (Finset.mem_image.mpr ⟨(key.1, (key.2.1 + 2, key.2.2)), hkey', rfl⟩)
  omega

/-- Multiplication by q−q⁻¹ is injective on the Laurent-monomial group. -/
theorem qDifference_eq_zero (m : Monomial) (hzero : qDifference m = 0) : m = 0 := by
  have hrec (key : Fin 4 × Spectral) :
      m (key.1, (key.2.1 + 2, key.2.2)) = m key := by
    have h := congrArg (fun x : Monomial => x (key.1, (key.2.1 + 1, key.2.2))) hzero
    have hp : shift 1 0 m (key.1, (key.2.1 + 1, key.2.2)) = m key := by
      simpa using shift_at_translated 1 0 m key
    have hm : shift (-1) 0 m (key.1, (key.2.1 + 1, key.2.2)) =
        m (key.1, (key.2.1 + 2, key.2.2)) := by
      simpa [add_assoc] using shift_at_translated (-1) 0 m
        (key.1, (key.2.1 + 2, key.2.2))
    simp only [qDifference, Finsupp.sub_apply, Finsupp.zero_apply] at h
    rw [hp, hm] at h
    omega
  apply no_q_period m
  ext key
  let prev : Fin 4 × Spectral := (key.1, (key.2.1 - 2, key.2.2))
  have hs : shift 2 0 m key = m prev := by
    simpa [prev] using shift_at_translated 2 0 m prev
  have hr := hrec prev
  simp only [prev] at hr
  rw [hs]
  convert hr.symm using 1; simp

private theorem tDifference_sub (m n : Monomial) :
    tDifference (m - n) = tDifference m - tDifference n := by
  simp [tDifference, shift, Finsupp.mapDomain_sub]
  abel

theorem tDifference_injective : Function.Injective tDifference := by
  intro m n h
  apply sub_eq_zero.mp
  apply tDifference_eq_zero
  rw [tDifference_sub, h, sub_self]

private theorem qDifference_sub (m n : Monomial) :
    qDifference (m - n) = qDifference m - qDifference n := by
  simp [qDifference, shift, Finsupp.mapDomain_sub]
  abel

/-- The intermediate candidate has no Y₄ factor at any spectral parameter.
Thus its OPE with the fourth screening has no pole. -/
theorem zero_weight_candidate_has_no_outer_factor (a b : ℤ) :
    Z (3, (a, b)) = 0 := by
  simp [Z, Y, Finsupp.sub_apply]

/-- Minus-screening signature equation for the required endpoint. -/
theorem minus_signature_match :
    tDifference (Nminus - M) = A 3 (-2) 1 - A 3 (-2) 5 := by
  ext x
  simp [tDifference, shift, Nminus, M, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem forced_signature_0 :
    tDifference (M₁ - M₀) = A 1 (-1) 0 - A 1 (-1) 2 := by
  ext x
  simp [tDifference, shift, M₁, M₀, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem forced_signature_1 :
    tDifference (M₂ - M₁) = A 0 (-2) 1 - A 0 (-2) 3 := by
  ext x
  simp [tDifference, shift, M₂, M₁, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem forced_signature_2 :
    tDifference (M₃ - M₂) = A 2 (-2) 1 - A 2 (-2) 3 := by
  ext x
  simp [tDifference, shift, M₃, M₂, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem forced_signature_3 :
    tDifference (M - M₃) = A 1 (-3) 2 - A 1 (-3) 4 := by
  ext x
  simp [tDifference, shift, M, M₃, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

/-- Plus-screening signature equation for its distinct endpoint. -/
theorem plus_signature_match :
    qDifference (Nplus - M) = A 3 (-5) 2 - A 3 (-1) 2 := by
  ext x
  simp [qDifference, shift, Nplus, M, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem intermediate_minus_signature_match :
    tDifference (Z - M) = A 3 (-2) 1 - A 3 (-2) 3 := by
  ext x
  simp [tDifference, shift, Z, M, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem intermediate_plus_signature_match :
    qDifference (Z - M) = A 3 (-3) 2 - A 3 (-1) 2 := by
  ext x
  simp [qDifference, shift, Z, M, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem second_intermediate_signature_match :
    tDifference (Zprime - M) = A 3 (-4) 3 - A 3 (-4) 5 := by
  ext x
  simp [tDifference, shift, Zprime, M, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem second_negative_signature_match :
    tDifference (Nprime - M) = A 3 (-4) 3 - A 3 (-4) 7 := by
  ext x
  simp [tDifference, shift, Nprime, M, A, Y, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem prime_positive_signature_match :
    tDifference (positivePrimePartner - Zprime) = A 3 (-2) 1 - A 3 (-2) (-1) := by
  ext x
  simp [tDifference, shift, positivePrimePartner, Zprime, A, Y,
    Finsupp.mapDomain_add, Finsupp.mapDomain_sub,
    Finsupp.add_apply, Finsupp.sub_apply]

theorem prime_negative_signature_match :
    tDifference (negativePrimePartner - Zprime) = A 3 (-2) 1 - A 3 (-2) 3 := by
  ext x
  simp [tDifference, shift, negativePrimePartner, Zprime, A, Y,
    Finsupp.mapDomain_add, Finsupp.mapDomain_sub,
    Finsupp.add_apply, Finsupp.sub_apply]
  abel

/-- At the specified second-pole locations, the algebraic signatures select
one Laurent monomial each. Classifying all possible locations is separate. -/
theorem minus_signature_unique (N : Monomial)
    (h : tDifference (N - M) = A 3 (-2) 1 - A 3 (-2) 5) : N = Nminus := by
  have heq : tDifference (N - M) = tDifference (Nminus - M) :=
    h.trans minus_signature_match.symm
  have hz : tDifference ((N - M) - (Nminus - M)) = 0 := by
    rw [tDifference_sub, heq, sub_self]
  have hsame := tDifference_eq_zero _ hz
  have h' : N - M = Nminus - M := sub_eq_zero.mp hsame
  simpa using congrArg (fun x : Monomial => x + M) h'

theorem plus_signature_unique (N : Monomial)
    (h : qDifference (N - M) = A 3 (-5) 2 - A 3 (-1) 2) : N = Nplus := by
  have heq : qDifference (N - M) = qDifference (Nplus - M) :=
    h.trans plus_signature_match.symm
  have hz : qDifference ((N - M) - (Nplus - M)) = 0 := by
    rw [qDifference_sub, heq, sub_self]
  have hsame := qDifference_eq_zero _ hz
  have h' : N - M = Nplus - M := sub_eq_zero.mp hsame
  simpa using congrArg (fun x : Monomial => x + M) h'

theorem same_minus_pole_unique (N : Monomial)
    (h : tDifference (N - M) = 0) : N = M := by
  exact sub_eq_zero.mp (tDifference_eq_zero _ h)

theorem same_plus_pole_unique (N : Monomial)
    (h : qDifference (N - M) = 0) : N = M := by
  exact sub_eq_zero.mp (qDifference_eq_zero _ h)

theorem intermediate_minus_signature_unique (N : Monomial)
    (h : tDifference (N - M) = A 3 (-2) 1 - A 3 (-2) 3) : N = Z := by
  have heq : tDifference (N - M) = tDifference (Z - M) :=
    h.trans intermediate_minus_signature_match.symm
  have hz : tDifference ((N - M) - (Z - M)) = 0 := by
    rw [tDifference_sub, heq, sub_self]
  have hsame := tDifference_eq_zero _ hz
  have h' : N - M = Z - M := sub_eq_zero.mp hsame
  simpa using congrArg (fun x : Monomial => x + M) h'

theorem intermediate_plus_signature_unique (N : Monomial)
    (h : qDifference (N - M) = A 3 (-3) 2 - A 3 (-1) 2) : N = Z := by
  have heq : qDifference (N - M) = qDifference (Z - M) :=
    h.trans intermediate_plus_signature_match.symm
  have hz : qDifference ((N - M) - (Z - M)) = 0 := by
    rw [qDifference_sub, heq, sub_self]
  have hsame := qDifference_eq_zero _ hz
  have h' : N - M = Z - M := sub_eq_zero.mp hsame
  simpa using congrArg (fun x : Monomial => x + M) h'

/-- The final minus-screening residue has only these three algebraic partner
monomials once the root-string weight restriction is supplied. -/
theorem final_minus_partner_cases (N : Monomial) (da db : ℤ)
    (h : tDifference (N - M) = A 3 (-2) 1 - A 3 da db)
    (hroot : ∀ k : ℤ, da = -2 ∧ db = 1 + 2 * k →
      k = 0 ∨ k = 1 ∨ k = 2) :
    N = M ∨ N = Z ∨ N = Nminus := by
  obtain ⟨k, hda, hdb⟩ := minus_outer_pole_lattice M N (-2) 1 da db h
  rcases hroot k ⟨hda, hdb⟩ with hk | hk | hk
  · have hd : db = 1 := by omega
    rw [hda, hd] at h
    left
    apply same_minus_pole_unique
    simpa using h
  · have hd : db = 3 := by omega
    rw [hda, hd] at h
    exact Or.inr (Or.inl (intermediate_minus_signature_unique N h))
  · have hd : db = 5 := by omega
    rw [hda, hd] at h
    exact Or.inr (Or.inr (minus_signature_unique N h))

/-- The analogous three possibilities for the plus-screening residue. -/
theorem final_plus_partner_cases (N : Monomial) (da db : ℤ)
    (h : qDifference (N - M) = A 3 da db - A 3 (-1) 2)
    (hroot : ∀ k : ℤ, db = 2 ∧ da = -1 + 2 * k →
      k = 0 ∨ k = -1 ∨ k = -2) :
    N = M ∨ N = Z ∨ N = Nplus := by
  obtain ⟨k, hdb, hda⟩ := plus_outer_pole_lattice M N (-1) 2 da db h
  rcases hroot k ⟨hdb, hda⟩ with hk | hk | hk
  · have hd : da = -1 := by omega
    rw [hdb, hd] at h
    left
    apply same_plus_pole_unique
    simpa using h
  · have hd : da = -3 := by omega
    rw [hdb, hd] at h
    exact Or.inr (Or.inl (intermediate_plus_signature_unique N h))
  · have hd : da = -5 := by omega
    rw [hdb, hd] at h
    exact Or.inr (Or.inr (plus_signature_unique N h))

end
end FrenkelReshetikhin.D4CounterexampleProof
