import StatementDefinitions
import Mathlib.Tactic.Abel

/-!
Exact, finite Laurent-monomial calculations used in the proposed D₄
counterexample in `Proof.tex`. An additive `Monomial` records the exponents of
the formal variables Yᵢ(qᵃtᵇ). These checks do not formalize the screening
residue argument or the fundamental-module weight multiplicities.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

abbrev Spectral := ℤ × ℤ
abbrev Monomial := (Fin 4 × Spectral) →₀ ℤ

def Y (i : Fin 4) (a b : ℤ) : Monomial :=
  Finsupp.single (i, (a, b)) 1

-- The central node is 1 in the repository's zero-based Bourbaki indexing.
def A (i : Fin 4) (a b : ℤ) : Monomial :=
  Y i (a + 1) (b - 1) + Y i (a - 1) (b + 1) -
    (if i = 1 then Y 0 a b + Y 2 a b + Y 3 a b else Y 1 a b)

def M₀ : Monomial := Y 1 0 0
def M₁ : Monomial := Y 0 (-1) 1 + Y 2 (-1) 1 + Y 3 (-1) 1 - Y 1 (-2) 2
def M₂ : Monomial := Y 2 (-1) 1 + Y 3 (-1) 1 - Y 0 (-3) 3
def M₃ : Monomial := Y 1 (-2) 2 + Y 3 (-1) 1 - Y 0 (-3) 3 - Y 2 (-3) 3
def M : Monomial := Y 3 (-1) 1 + Y 3 (-3) 3 - Y 1 (-4) 4

def Z : Monomial := Y 1 (-2) 2 - Y 1 (-4) 4
def Nminus : Monomial :=
  Y 1 (-2) 2 + Y 1 (-2) 4 - Y 1 (-4) 4 - Y 3 (-1) 3 - Y 3 (-3) 5
def Nplus : Monomial :=
  Y 1 (-2) 2 + Y 1 (-4) 2 - Y 1 (-4) 4 - Y 3 (-3) 1 - Y 3 (-5) 3

-- Monomials in the note's independent minus-screening check.
def Zprime : Monomial := Y 3 (-1) 1 - Y 3 (-5) 5
def Nprime : Monomial := M - A 3 (-4) 4 - A 3 (-4) 6
def positivePrimePartner : Monomial := Zprime + A 3 (-2) 0
def negativePrimePartner : Monomial := Zprime - A 3 (-2) 2

/-- The Laurent monomial specified by an actual list of inverse-root factors
in `StatementDefinitions`, at D₄'s central fundamental index. -/
def monomialOfFactors (factors : List (InverseRootFactor D₄)) : Monomial :=
  M₀ - (factors.map fun f => A f.root f.qShift f.tShift).sum


-- All four forced monomial transitions in the note.
example : M₁ = M₀ - A 1 (-1) 1 := by
  ext x
  simp [M₁, M₀, A, Y, Finsupp.add_apply, Finsupp.sub_apply]
  abel
example : M₂ = M₁ - A 0 (-2) 2 := by
  ext x
  simp [M₂, M₁, A, Y, Finsupp.add_apply, Finsupp.sub_apply]
  abel
example : M₃ = M₂ - A 2 (-2) 2 := by
  ext x
  simp [M₃, M₂, A, Y, Finsupp.add_apply, Finsupp.sub_apply]
  abel
example : M = M₃ - A 1 (-3) 3 := by
  ext x
  simp [M, M₃, A, Y, Finsupp.add_apply, Finsupp.sub_apply]
  abel

-- The two screening partner chains at the final weight.
example : Z = M - A 3 (-2) 2 := by
  ext x
  simp [Z, M, A, Y, Finsupp.sub_apply]
example : Nminus = Z - A 3 (-2) 4 := by
  ext x
  simp [Nminus, Z, A, Y, Finsupp.add_apply, Finsupp.sub_apply]
  abel
example : Nplus = Z - A 3 (-4) 2 := by
  ext x
  simp [Nplus, Z, A, Y, Finsupp.add_apply, Finsupp.sub_apply]
  abel
theorem incompatible_endpoints : Nminus ≠ Nplus := by
  intro h
  have h' := congrArg (fun m : Monomial => m (1, (-2, 4))) h
  simp [Nminus, Nplus, Y, Finsupp.add_apply, Finsupp.sub_apply] at h'

theorem second_pole_intermediate : Zprime = M - A 3 (-4) 4 := by
  ext x
  simp [Zprime, M, A, Y, Finsupp.add_apply, Finsupp.sub_apply]
  abel

theorem second_pole_negative_distinct : Nprime ≠ Nminus := by
  intro h
  have h' := congrArg (fun m : Monomial => m (3, (-1, 1))) h
  simp [Nprime, Nminus, M, A, Y, Finsupp.add_apply, Finsupp.sub_apply] at h'

theorem positive_prime_partner_distinct : positivePrimePartner ≠ M := by
  intro h
  have h' := congrArg (fun m : Monomial => m (3, (-1, -1))) h
  simp [positivePrimePartner, Zprime, M, A, Y,
    Finsupp.add_apply, Finsupp.sub_apply] at h'

theorem negative_prime_partner_distinct : negativePrimePartner ≠ Nminus := by
  intro h
  have h' := congrArg (fun m : Monomial => m (3, (-5, 5))) h
  simp [negativePrimePartner, Zprime, Nminus, A, Y,
    Finsupp.add_apply, Finsupp.sub_apply] at h'


end
end FrenkelReshetikhin.D4CounterexampleProof
