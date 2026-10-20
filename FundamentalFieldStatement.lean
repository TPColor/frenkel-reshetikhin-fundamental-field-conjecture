import D4CounterexampleProof.Reduction
import D4CounterexampleProof.Signatures
import D4CounterexampleProof.RootStrings
import D4CounterexampleProof.PoleOrders
import D4CounterexampleProof.FirstMode
import D4CounterexampleProof.Moments
import D4CounterexampleProof.RootWeightSupport
import D4CounterexampleProof.PartnerForcing
import D4CounterexampleProof.ExponentialSymbols
import D4CounterexampleProof.FockEvaluation
import D4CounterexampleProof.LocalFiniteness
import D4CounterexampleProof.LaurentEvaluation
import D4CounterexampleProof.D4Cartan
import D4CounterexampleProof.FundamentalModule
import D4CounterexampleProof.CreationExponents
import D4CounterexampleProof.ScreeningSignatures
import D4CounterexampleProof.D4Modes
import D4CounterexampleProof.ElementaryIndependence
import D4CounterexampleProof.Integrability
import D4CounterexampleProof.RationalResidues
import D4CounterexampleProof.ScreeningExpansion
import D4CounterexampleProof.OscillatorContractions
import D4CounterexampleProof.SingleScreening
import D4CounterexampleProof.CreationFieldIndependence
import D4CounterexampleProof.ScreeningPolynomial
import D4CounterexampleProof.FirstCreationModes
import D4CounterexampleProof.ScreeningContractions
import D4CounterexampleProof.ScreeningPartialFractions
import D4CounterexampleProof.DivisorPoles
import D4CounterexampleProof.LocalResidues
import D4CounterexampleProof.LocalResiduePartners
import D4CounterexampleProof.CoefficientAggregation
import D4CounterexampleProof.ElementaryLabels
import D4CounterexampleProof.NonzeroPrincipalParts
import D4CounterexampleProof.ScreeningDegree
import D4CounterexampleProof.CompletedCreationAction
import D4CounterexampleProof.FourierContractions
import D4CounterexampleProof.NormalWordContractions
import D4CounterexampleProof.ExponentialSubstitution
import D4CounterexampleProof.FrequencySubstitution
import D4CounterexampleProof.FormalExponentialProducts
import D4CounterexampleProof.FrequencyMoments
import D4CounterexampleProof.ContractionProducts
import D4CounterexampleProof.ScreeningLogarithms
import D4CounterexampleProof.ScreeningScalarSeries
import D4CounterexampleProof.ScreenedVacuumCoefficients
import D4CounterexampleProof.AnnihilationPartitions
import D4CounterexampleProof.FirstModeSubstitution
import D4CounterexampleProof.AllModeContractions
import D4CounterexampleProof.ResidueTransform
import D4CounterexampleProof.PolynomialPart
import D4CounterexampleProof.CreationConvolution
import D4CounterexampleProof.ScreeningResidueBridge
import D4CounterexampleProof.OriginalScreeningForcing
import D4CounterexampleProof.QuantumStrings
import D4CounterexampleProof.CartanHighestModes
import D4CounterexampleProof.FundamentalCharacter

/-!
Frenkel–Reshetikhin, *Deformations of W-algebras associated to simple Lie
algebras*, §3.3, Conjecture 1 (https://arxiv.org/abs/q-alg/9708006).

The supporting definitions construct the Heisenberg algebra and Fock modules
by their presentations, the fields by normally ordered formal exponentials,
and W as the screening centralizer. Fundamental modules are specified by
their Drinfeld polynomials, following FR's quantum-affine conventions.

Coefficient functions are rational in independent q,t and regular at t=1.
The Fock charge labels include the r^vee correction required by (3.6).
Node indices are zero-based Bourbaki indices.
-/

namespace FrenkelReshetikhin

/-- Conjecture 1 restricted to a fixed simple Lie type. -/
def Conjecture1For (g : SimpleLieType) : Prop :=
  ∀ i : RootIndex g, HasFundamentalField g i

/-- Conjecture 1: every fundamental index of every simple Lie type admits
a field in W_{q,t}(g) with the prescribed elementary expansion, positive
integer specialization of coefficients, and fundamental-module weights.
-/
def Conjecture1 : Prop :=
  ∀ g : SimpleLieType, Conjecture1For g

/-- Counterexample statement for the specific type D₄.
-/
theorem conjecture1_false_for_D4 : ¬ Conjecture1For D₄ := by
  intro hconjecture
  refine (D4CounterexampleProof.no_central_field_of_module_facts ?_ ?_)
    (hconjecture D4CounterexampleProof.central)
  · /- The central fundamental module has multiplicity one at -α₄. -/
    intro d V hV
    exact D4CounterexampleProof.fundamental_negative_outer_multiplicity V hV
  · /- Every nonzero weight of the central fundamental module is a D₄ root or zero. -/
    intro d V hV weight hw
    exact D4CounterexampleProof.fundamental_root_or_zero_support V hV weight hw

/-- A counterexample at D₄ refutes the universal conjecture. -/
theorem not_conjecture1 : ¬ Conjecture1 := by
  intro h
  exact conjecture1_false_for_D4 (h D₄)

end FrenkelReshetikhin
