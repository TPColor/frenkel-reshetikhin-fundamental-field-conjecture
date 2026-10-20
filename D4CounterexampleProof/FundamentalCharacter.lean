import D4CounterexampleProof.D4WeylCoordinates
import D4CounterexampleProof.Reduction

/-! The two fundamental-module facts used by the D₄ obstruction, derived
from the original Drinfeld definition, triangular spanning, and Weyl symmetry. -/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Drinfeld

def coordinateBox (r : RootCoordinates) : Prop :=
  -1 ≤ r.1 ∧ r.1 ≤ 1 ∧ -2 ≤ r.2.1 ∧ r.2.1 ≤ 2 ∧
    -1 ≤ r.2.2.1 ∧ r.2.2.1 ≤ 1 ∧ -1 ≤ r.2.2.2 ∧ r.2.2.2 ≤ 1

theorem fundamental_coordinates_box {d : ℕ} (V : Representation D₄ d)
    (hV : FundamentalRepresentation D₄ central V) (r : RootCoordinates)
    (hr : weightMultiplicity D₄ V (coordinatesWeight r) ≠ 0) : coordinateBox r := by
  have hu := fundamental_coordinates_upper V hV r hr
  have hneg : weightMultiplicity D₄ V (coordinatesWeight (-r)) ≠ 0 := by
    have hh := reflectWord_multiplicity V hV.1 [0, 2, 3, 1, 0, 2, 3, 1, 0, 2, 3, 1] r
    rw [reflectWord_longest] at hh
    rwa [← hh]
  have hl := fundamental_coordinates_upper V hV (-r) hneg
  rcases r with ⟨a, b, c, d⟩
  dsimp only [coordinateBox, Prod.neg_mk] at *
  omega

set_option maxHeartbeats 2000000 in
theorem root_or_zero_of_weyl_boxes (r : RootCoordinates)
    (h : ∀ word : List (Fin 4), coordinateBox (reflectWord word r)) :
    r ∈ roots ∨ r = 0 := by
  rcases r with ⟨a, b, c, d⟩
  have hb := h []
  change -1 ≤ a ∧ a ≤ 1 ∧ -2 ≤ b ∧ b ≤ 2 ∧ -1 ≤ c ∧ c ≤ 1 ∧ -1 ≤ d ∧ d ≤ 1 at hb
  obtain ⟨ha, ha', hb, hb', hc, hc', hd, hd'⟩ := hb
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
  all_goals solve
    | exact Or.inl (by decide)
    | exact Or.inr (by rfl)
    | (have hh := h [0]; revert hh; unfold coordinateBox; decide)
    | (have hh := h [2]; revert hh; unfold coordinateBox; decide)
    | (have hh := h [3]; revert hh; unfold coordinateBox; decide)
    | (have hh := h [1]; revert hh; unfold coordinateBox; decide)
    | (have hh := h [1, 3]; revert hh; unfold coordinateBox; decide)
    | (have hh := h [1, 2]; revert hh; unfold coordinateBox; decide)
    | (have hh := h [0, 1, 2]; revert hh; unfold coordinateBox; decide)
    | (have hh := h [0, 1, 3]; revert hh; unfold coordinateBox; decide)
    | (have hh := h [1, 0]; revert hh; unfold coordinateBox; decide)
    | (have hh := h [2, 1, 0]; revert hh; unfold coordinateBox; decide)

/-- Every nonzero ordinary weight of the original central fundamental
representation is a root or zero. -/
theorem fundamental_root_or_zero_support {d : ℕ} (V : Representation D₄ d)
    (hV : FundamentalRepresentation D₄ central V) (weight : Weight D₄)
    (hw : weightMultiplicity D₄ V weight ≠ 0) :
    weight ∈ roots.map coordinatesWeight ∨ weight = 0 := by
  obtain ⟨xs, hxs⟩ := fundamental_weight_below_highest D₄ central V hV weight hw
  obtain ⟨r, hr, hb⟩ := lower_weight_coordinates xs
  have he : weight = coordinatesWeight r := hxs.trans hr
  have hnr : weightMultiplicity D₄ V (coordinatesWeight r) ≠ 0 := by rwa [← he]
  have hboxes (word : List (Fin 4)) : coordinateBox (reflectWord word r) := by
    apply fundamental_coordinates_box V hV
    rwa [← reflectWord_multiplicity V hV.1 word r]
  rcases root_or_zero_of_weyl_boxes r hboxes with hroot | hz
  · exact Or.inl (List.mem_map.mpr ⟨r, hroot, he.symm⟩)
  · right
    rw [he, hz]
    exact coordinatesWeightHom.map_zero

theorem central_fundamental_coordinates :
    coordinatesWeight (1, 2, 1, 1) = fundamentalWeight D₄ central := by
  rw [central_fundamental_is_highest_root]
  simp [coordinatesWeight]

/-- The outer negative-root multiplicity is one, by the proved Weyl
symmetry and the one-dimensional original highest-weight space. -/
theorem fundamental_negative_outer_multiplicity {d : ℕ} (V : Representation D₄ d)
    (hV : FundamentalRepresentation D₄ central V) :
    weightMultiplicity D₄ V negativeOuterWeight = 1 := by
  have hstart : coordinatesWeight (0, 0, 0, -1) = negativeOuterWeight := by
    simp [coordinatesWeight, negativeOuterWeight]
  have hend : reflectWord [3, 1, 0, 2, 1] (0, 0, 0, -1) = (1, 2, 1, 1) := by decide
  have hh := reflectWord_multiplicity V hV.1 [3, 1, 0, 2, 1] (0, 0, 0, -1)
  rw [hstart, hend, central_fundamental_coordinates] at hh
  exact hh.trans (fundamental_highest_weightMultiplicity_one central V hV)

theorem root_reaches_highest (r : RootCoordinates) (hr : r ∈ roots) :
    ∃ word : List (Fin 4), reflectWord word r = (1, 2, 1, 1) := by
  have hlist : roots =
      [(1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1),
       (1,1,0,0), (0,1,1,0), (0,1,0,1), (1,1,1,0),
       (1,1,0,1), (0,1,1,1), (1,1,1,1), (1,2,1,1),
       (-1,0,0,0), (0,-1,0,0), (0,0,-1,0), (0,0,0,-1),
       (-1,-1,0,0), (0,-1,-1,0), (0,-1,0,-1), (-1,-1,-1,0),
       (-1,-1,0,-1), (0,-1,-1,-1), (-1,-1,-1,-1), (-1,-2,-1,-1)] := by decide
  rw [hlist] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨[1,2,3,1], by decide⟩
  · exact ⟨[0,2,3,1], by decide⟩
  · exact ⟨[1,0,3,1], by decide⟩
  · exact ⟨[1,0,2,1], by decide⟩
  · exact ⟨[2,3,1], by decide⟩
  · exact ⟨[0,3,1], by decide⟩
  · exact ⟨[0,2,1], by decide⟩
  · exact ⟨[3,1], by decide⟩
  · exact ⟨[2,1], by decide⟩
  · exact ⟨[0,1], by decide⟩
  · exact ⟨[1], by decide⟩
  · exact ⟨[], by decide⟩
  · exact ⟨[0,1,2,3,1], by decide⟩
  · exact ⟨[1,0,2,3,1], by decide⟩
  · exact ⟨[2,1,0,3,1], by decide⟩
  · exact ⟨[3,1,0,2,1], by decide⟩
  · exact ⟨[0,1,0,2,3,1], by decide⟩
  · exact ⟨[1,2,1,0,3,1], by decide⟩
  · exact ⟨[1,3,1,0,2,1], by decide⟩
  · exact ⟨[0,1,2,1,0,3,1], by decide⟩
  · exact ⟨[0,1,3,1,0,2,1], by decide⟩
  · exact ⟨[2,1,3,1,0,2,1], by decide⟩
  · exact ⟨[0,2,1,3,1,0,2,1], by decide⟩
  · exact ⟨[1,0,2,1,3,1,0,2,1], by decide⟩

/-- Every one of the 24 roots has multiplicity one in the original
central fundamental module; the zero-weight multiplicity is not needed. -/
theorem fundamental_root_multiplicity_one {d : ℕ} (V : Representation D₄ d)
    (hV : FundamentalRepresentation D₄ central V) (r : RootCoordinates) (hr : r ∈ roots) :
    weightMultiplicity D₄ V (coordinatesWeight r) = 1 := by
  obtain ⟨word, hword⟩ := root_reaches_highest r hr
  have hh := reflectWord_multiplicity V hV.1 word r
  rw [hword, central_fundamental_coordinates] at hh
  exact hh.trans (fundamental_highest_weightMultiplicity_one central V hV)

end
end FrenkelReshetikhin.D4CounterexampleProof
