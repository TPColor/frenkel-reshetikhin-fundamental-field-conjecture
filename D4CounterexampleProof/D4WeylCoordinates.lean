import D4CounterexampleProof.WeightReflection
import D4CounterexampleProof.D4HighestWeight

/-! D₄ Weyl reflections in simple-root coordinates, connected to the
proved reflection symmetry and the original fundamental highest bound. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Drinfeld

theorem coordinatesWeight_add (r s : RootCoordinates) :
    coordinatesWeight (r + s) = coordinatesWeight r + coordinatesWeight s := by
  rcases r with ⟨a, b, c, d⟩
  rcases s with ⟨e, f, h, k⟩
  funext j
  simp only [coordinatesWeight, Prod.add_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

def coordinatesWeightHom : RootCoordinates →+ Weight D₄ where
  toFun := coordinatesWeight
  map_zero' := by funext j; simp [coordinatesWeight]
  map_add' := coordinatesWeight_add

def simpleCoordinates (i : Fin 4) : RootCoordinates :=
  (if i = 0 then 1 else 0, if i = 1 then 1 else 0,
    if i = 2 then 1 else 0, if i = 3 then 1 else 0)

theorem coordinatesWeight_simpleCoordinates (i : Fin 4) :
    coordinatesWeight (simpleCoordinates i) = simpleRoot D₄ i := by
  fin_cases i <;> simp [simpleCoordinates, coordinatesWeight, central, outer] <;> rfl

def reflectCoordinates (i : Fin 4) (r : RootCoordinates) : RootCoordinates :=
  if i = 0 then (r.2.1 - r.1, r.2.1, r.2.2.1, r.2.2.2)
  else if i = 1 then (r.1, r.1 + r.2.2.1 + r.2.2.2 - r.2.1, r.2.2.1, r.2.2.2)
  else if i = 2 then (r.1, r.2.1, r.2.1 - r.2.2.1, r.2.2.2)
  else (r.1, r.2.1, r.2.2.1, r.2.1 - r.2.2.2)

theorem reflectCoordinates_formula (i : Fin 4) (r : RootCoordinates) :
    reflectCoordinates i r = r - coordinatesWeight r i • simpleCoordinates i := by
  fin_cases i
  · change reflectCoordinates (0 : Fin 4) r =
      r - coordinatesWeight r ⟨0, by decide⟩ • simpleCoordinates (0 : Fin 4)
    rw [coordinatesWeight_at_zero r]
    rcases r with ⟨a, b, c, d⟩
    simp [reflectCoordinates, simpleCoordinates, Prod.sub_def, Prod.smul_mk]
    ring
  · change reflectCoordinates (1 : Fin 4) r =
      r - coordinatesWeight r ⟨1, by decide⟩ • simpleCoordinates (1 : Fin 4)
    rw [coordinatesWeight_at_one r]
    rcases r with ⟨a, b, c, d⟩
    simp [reflectCoordinates, simpleCoordinates, Prod.sub_def, Prod.smul_mk]
    ring
  · change reflectCoordinates (2 : Fin 4) r =
      r - coordinatesWeight r ⟨2, by decide⟩ • simpleCoordinates (2 : Fin 4)
    rw [coordinatesWeight_at_two r]
    rcases r with ⟨a, b, c, d⟩
    simp [reflectCoordinates, simpleCoordinates, Prod.sub_def, Prod.smul_mk]
    ring
  · change reflectCoordinates (3 : Fin 4) r =
      r - coordinatesWeight r ⟨3, by decide⟩ • simpleCoordinates (3 : Fin 4)
    rw [coordinatesWeight_at_three r]
    rcases r with ⟨a, b, c, d⟩
    simp [reflectCoordinates, simpleCoordinates, Prod.sub_def, Prod.smul_mk]
    ring

theorem reflectedWeight_coordinates (i : Fin 4) (r : RootCoordinates) :
    reflectedWeight D₄ i (coordinatesWeight r) = coordinatesWeight (reflectCoordinates i r) := by
  rw [reflectCoordinates_formula]
  change reflectedWeight D₄ i (coordinatesWeightHom r) =
    coordinatesWeightHom (r - coordinatesWeight r i • simpleCoordinates i)
  rw [map_sub, map_zsmul]
  change coordinatesWeight r - coordinatesWeight r i • simpleRoot D₄ i =
    coordinatesWeight r - coordinatesWeight r i • coordinatesWeight (simpleCoordinates i)
  rw [coordinatesWeight_simpleCoordinates]

def reflectWord (word : List (Fin 4)) (r : RootCoordinates) : RootCoordinates :=
  word.foldl (fun s i => reflectCoordinates i s) r

theorem reflectWord_multiplicity {d : ℕ} (V : Representation D₄ d) (hV : TypeOne D₄ V)
    (word : List (Fin 4)) (r : RootCoordinates) :
    weightMultiplicity D₄ V (coordinatesWeight r) =
      weightMultiplicity D₄ V (coordinatesWeight (reflectWord word r)) := by
  induction word generalizing r with
  | nil => rfl
  | cons i word ih =>
    exact (weightMultiplicity_reflection D₄ V hV i (coordinatesWeight r)).trans
      (by rw [reflectedWeight_coordinates]; exact ih (reflectCoordinates i r))

theorem reflectWord_longest (r : RootCoordinates) :
    reflectWord [0, 2, 3, 1, 0, 2, 3, 1, 0, 2, 3, 1] r = -r := by
  rcases r with ⟨a, b, c, d⟩
  simp only [reflectWord, List.foldl_cons, List.foldl_nil]
  simp [reflectCoordinates, Prod.neg_mk]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem lower_weight_coordinates (xs : List (RootIndex D₄)) :
    ∃ r : RootCoordinates,
      fundamentalWeight D₄ central - (xs.map (simpleRoot D₄)).sum = coordinatesWeight r ∧
      r.1 ≤ 1 ∧ r.2.1 ≤ 2 ∧ r.2.2.1 ≤ 1 ∧ r.2.2.2 ≤ 1 := by
  induction xs with
  | nil =>
    refine ⟨(1, 2, 1, 1), ?_, by decide⟩
    simp only [List.map_nil, List.sum_nil, sub_zero]
    rw [central_fundamental_is_highest_root]
    simp [coordinatesWeight]
  | cons i xs ih =>
    obtain ⟨r, hr, ha, hb, hc, hd⟩ := ih
    refine ⟨r - simpleCoordinates i, ?_, ?_⟩
    · rw [List.map_cons, List.sum_cons]
      have he : fundamentalWeight D₄ central - (simpleRoot D₄ i + (xs.map (simpleRoot D₄)).sum) =
          (fundamentalWeight D₄ central - (xs.map (simpleRoot D₄)).sum) - simpleRoot D₄ i := by abel
      rw [he, hr, ← coordinatesWeight_simpleCoordinates i]
      exact (map_sub coordinatesWeightHom r (simpleCoordinates i)).symm
    · rcases r with ⟨a, b, c, d⟩
      dsimp only at ha hb hc hd
      fin_cases i <;> simp [simpleCoordinates, Prod.sub_def] <;> omega

theorem fundamental_coordinates_upper {d : ℕ} (V : Representation D₄ d)
    (hV : FundamentalRepresentation D₄ central V) (r : RootCoordinates)
    (hr : weightMultiplicity D₄ V (coordinatesWeight r) ≠ 0) :
    r.1 ≤ 1 ∧ r.2.1 ≤ 2 ∧ r.2.2.1 ≤ 1 ∧ r.2.2.2 ≤ 1 := by
  obtain ⟨xs, hxs⟩ := fundamental_weight_below_highest D₄ central V hV _ hr
  obtain ⟨s, hs, hb⟩ := lower_weight_coordinates xs
  have he : r = s := coordinatesWeight_injective (hxs.trans hs)
  simpa only [he] using hb

end
end FrenkelReshetikhin.D4CounterexampleProof
