import D4CounterexampleProof.LocalFiniteness

/-! The vanishing screening sum on the vacuum obtained directly from
the original fundamental expansion and W-centralizer definition. -/

namespace FrenkelReshetikhin.OriginalFR.Fields

noncomputable section

local instance screeningExpansionCoefficientField : _root_.Field Coefficient := inferInstance

variable (g : SimpleLieType)

theorem screeningOperator_list_sum (sign : ScreeningSign) (i : RootIndex g)
    (xs : List (State g none)) :
    screeningOperator g sign i xs.sum = (xs.map (screeningOperator g sign i)).sum := by
  induction xs with
  | nil =>
    simp only [List.sum_nil, List.map_nil]
    cases sign <;> simp only [screeningOperator, evaluateSymbol_zero_state] <;> exact map_zero _
  | cons v vs ih =>
    rw [List.sum_cons, screeningOperator_add, ih, List.map_cons, List.sum_cons]

theorem fundamentalExpansion_apply (i : RootIndex g) (terms : List (ElementaryTerm g))
    (charge : Charge g) (n : ℤ) (v : State g charge) :
    fundamentalExpansion g i terms charge n v =
      evaluateSymbol g (weightVertex g i false 0 0) charge n v +
        (terms.map fun term => RatFunc.C term.coefficient •
          evaluateSymbol g (elementarySymbol g i term.factors) charge n v).sum := by
  have hlist (fs : List (Field g)) :
      fs.sum charge n v = (fs.map fun f => f charge n v).sum := by
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      change f charge n v + fs.sum charge n v =
        f charge n v + (fs.map fun f => f charge n v).sum
      rw [ih]
  change evaluateSymbol g (weightVertex g i false 0 0) charge n v +
    (terms.map fun term => RatFunc.C term.coefficient •
      evaluateSymbol g (elementarySymbol g i term.factors)).sum charge n v = _
  rw [hlist]
  simp only [List.map_map, Function.comp_def, Pi.smul_apply]

/-- Every vacuum Fourier coefficient of a conjectural expansion gives
this finite zero sum in the actual charged Fock module. Further OPE and
faithfulness arguments are needed to turn it into a pole-partner theorem. -/
theorem fundamentalExpansion_screening_vacuum (i : RootIndex g)
    (terms : List (ElementaryTerm g))
    (hW : fundamentalExpansion g i terms ∈ deformedW g)
    (sign : ScreeningSign) (j : RootIndex g) (n : ℤ) :
    screeningOperator g sign j
        (evaluateSymbol g (weightVertex g i false 0 0) none n (vacuum g Scalars Q T 0)) +
      (terms.map fun term => RatFunc.C term.coefficient •
        screeningOperator g sign j
          (evaluateSymbol g (elementarySymbol g i term.factors) none n
            (vacuum g Scalars Q T 0))).sum = 0 := by
  have hz := deformedW_screening_vacuum g (fundamentalExpansion g i terms) hW sign j n
  erw [fundamentalExpansion_apply, screeningOperator_add, screeningOperator_list_sum] at hz
  simpa only [List.map_map, Function.comp_def, screeningOperator_smul] using hz

end
end FrenkelReshetikhin.OriginalFR.Fields
