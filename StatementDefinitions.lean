import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.GroupTheory.Perm.Fin

/-!
Supporting definitions for FR Conjecture 1, §3.3.

The Heisenberg algebra and Fock modules are defined by their presentations.
Fields are formal normally ordered exponentials, with their full prefactors;
the field space and screening centralizer follow FR (3.13) and §3.3.
Fundamental quantum affine modules are specified by their Drinfeld polynomials.

Conventions: zero-based Bourbaki indices; generic independent q,t;
rational coefficient functions regular at t=1. Beta is an auxiliary formal
parameter for the charge labels t=q^beta, not an h-adic parameter.
The charge labels include the r^vee factor required by FR (3.6), correcting
the inconsistent label in the preceding sentence with the user's agreement.

Sources: FR, https://arxiv.org/abs/q-alg/9708006, §§2–3;
FR, https://arxiv.org/abs/math/9810055, §§2.2–2.3 (quantum affine modules).
-/

noncomputable section

open scoped BigOperators

namespace FrenkelReshetikhin

inductive SimpleLieType where
  | A (rank : ℕ) (valid : 1 ≤ rank)
  | B (rank : ℕ) (valid : 2 ≤ rank)
  | C (rank : ℕ) (valid : 2 ≤ rank)
  | D (rank : ℕ) (valid : 4 ≤ rank)
  | E6 | E7 | E8 | F4 | G2
  deriving DecidableEq

def SimpleLieType.rank : SimpleLieType → ℕ
  | .A n _ | .B n _ | .C n _ | .D n _ => n
  | .E6 => 6 | .E7 => 7 | .E8 => 8 | .F4 => 4 | .G2 => 2

def D₄ : SimpleLieType := .D 4 (by decide)
abbrev RootIndex (g : SimpleLieType) := Fin g.rank
abbrev Weight (g : SimpleLieType) := RootIndex g → ℤ

def fundamentalWeight (g : SimpleLieType) (i : RootIndex g) : Weight g :=
  fun j => if j = i then 1 else 0

/-- Undirected edges; multiplicities and orientations are in `cartan`. -/
def adjacent (g : SimpleLieType) (i j : ℕ) : Bool :=
  match g with
  | .D n _ =>
    (i + 1 == j && j < n - 1) || (j + 1 == i && i < n - 1) ||
      (i == n - 3 && j == n - 1) || (j == n - 3 && i == n - 1)
  | .E6 | .E7 | .E8 =>
    (i == 0 && j == 2) || (j == 0 && i == 2) ||
      (i == 1 && j == 3) || (j == 1 && i == 3) ||
      (2 ≤ i && i + 1 == j) || (2 ≤ j && j + 1 == i)
  | _ => i + 1 == j || j + 1 == i

/-- C_ij = <alpha_i^vee, alpha_j>; columns are simple-root coordinates. -/
def cartan (g : SimpleLieType) : Matrix (RootIndex g) (RootIndex g) ℤ :=
  fun i j => if i = j then 2 else if adjacent g i.val j.val then
    match g with
    | .B n _ => if i.val = n - 1 then -2 else -1
    | .C n _ => if j.val = n - 1 then -2 else -1
    | .F4 => if i.val = 2 ∧ j.val = 1 then -2 else -1
    | .G2 => if i.val = 0 then -3 else -1
    | _ => -1
  else 0

/-- Minimal positive symmetrizers r_i, so r_i C_ij = r_j C_ji. -/
def rootLength (g : SimpleLieType) (i : RootIndex g) : ℕ :=
  match g with
  | .B n _ => if i.val = n - 1 then 1 else 2
  | .C n _ => if i.val = n - 1 then 2 else 1
  | .F4 => if i.val < 2 then 2 else 1
  | .G2 => if i.val = 0 then 1 else 3
  | _ => 1

def lacingNumber : SimpleLieType → ℕ
  | .B _ _ | .C _ _ | .F4 => 2
  | .G2 => 3
  | _ => 1

def simpleRoot (g : SimpleLieType) (i : RootIndex g) : Weight g :=
  fun j => cartan g j i

abbrev QuantumCoefficient := RatFunc ℂ
abbrev Coefficient := RatFunc QuantumCoefficient

def quantumQ : QuantumCoefficient := RatFunc.X
def q : Coefficient := RatFunc.C quantumQ
def t : Coefficient := RatFunc.X

/-- The q-integer in FR §2, used at generic q. -/
def qInteger {K : Type*} [Field K] (x : K) (n : ℤ) : K :=
  (x ^ n - x ^ (-n)) / (x - x⁻¹)

/-- Evaluation uses the reduced denominator, so poles cannot be silently
evaluated to zero by the totalized division operation. -/
def specializesToNat (c : Coefficient) (n : ℕ) : Prop :=
  c.denom.eval 1 ≠ 0 ∧ RatFunc.eval (RingHom.id _) 1 c = (n : QuantumCoefficient)

def deformedCartan (g : SimpleLieType) (mode : ℤ) :
    Matrix (RootIndex g) (RootIndex g) Coefficient :=
  fun i j =>
    (if i = j then q ^ ((rootLength g i : ℤ) * mode) * t ^ (-mode) +
      q ^ (-((rootLength g i : ℤ) * mode)) * t ^ mode else 0) -
    qInteger (q ^ mode) ((if i = j then 2 else 0) - cartan g i j)

structure InverseRootFactor (g : SimpleLieType) where
  root : RootIndex g
  qShift : ℤ
  tShift : ℤ

def elementaryWeight {g : SimpleLieType} (i : RootIndex g)
    (factors : List (InverseRootFactor g)) : Weight g :=
  fun j => fundamentalWeight g i j -
    (factors.map fun f => simpleRoot g f.root j).sum

inductive ScreeningSign where
  | plus | minus
  deriving DecidableEq

/-- The change of q^(2y[0]) on the target Fock space of the screening. -/
def screeningZeroMode {g : SimpleLieType} (sign : ScreeningSign)
    (j : RootIndex g) (weight : Weight g) : Coefficient :=
  match sign with
  | .plus => t ^ (-2 * weight j)
  | .minus => q ^ (2 * (rootLength g j : ℤ) * weight j)

/-- Both FR screening-current exponents, including the minus sign in S⁻. -/
def screeningModes {g : SimpleLieType} (sign : ScreeningSign)
    (i : RootIndex g) (mode : ℤ) (j : RootIndex g) : Coefficient :=
  if j = i then
    match sign with
    | .plus => (q ^ (mode * rootLength g i) - q ^ (-(mode * rootLength g i)))⁻¹
    | .minus => -(t ^ mode - t ^ (-mode))⁻¹
  else 0

structure ElementaryTerm (g : SimpleLieType) where
  coefficient : Coefficient
  factors : List (InverseRootFactor g)
  multiplicity : ℕ

def ElementaryTerm.valid {g : SimpleLieType} (term : ElementaryTerm g) : Prop :=
  0 < term.multiplicity ∧ specializesToNat term.coefficient term.multiplicity

/-- q-binomial coefficients used in the quantum Serre relations. -/
def quantumFactorial (x : QuantumCoefficient) (n : ℕ) : QuantumCoefficient :=
  ∏ k ∈ Finset.range n, qInteger x (k + 1)

def quantumBinomial (x : QuantumCoefficient) (n k : ℕ) : QuantumCoefficient :=
  quantumFactorial x n / (quantumFactorial x k * quantumFactorial x (n - k))

def expansionMultiplicity {g : SimpleLieType} (i : RootIndex g)
    (terms : List (ElementaryTerm g)) (weight : Weight g) : ℕ :=
  (if weight = fundamentalWeight g i then 1 else 0) +
    (terms.map fun term =>
      if elementaryWeight i term.factors = weight then term.multiplicity else 0).sum

namespace OriginalFR

section Heisenberg

variable (g : SimpleLieType) (K : Type*) [Field K] (q₀ t₀ : K)

/-- The q-integer as written in FR §2. -/
def quantumInteger (x : K) (n : ℤ) : K :=
  (x ^ n - x ^ (-n)) / (x - x⁻¹)

/-- FR equation (2.2), evaluated at q₀^n,t₀^n. -/
def cartanMatrix (n : ℤ) : Matrix (RootIndex g) (RootIndex g) K :=
  fun i j =>
    (if i = j then q₀ ^ ((rootLength g i : ℤ) * n) * t₀ ^ (-n) +
      q₀ ^ (-((rootLength g i : ℤ) * n)) * t₀ ^ n else 0) -
    quantumInteger K (q₀ ^ n) ((if i = j then 2 else 0) - cartan g i j)

/-- FR equations (2.3)–(2.4): B(q,t) = D(q,t) C(q,t). -/
def symmetrizedCartanMatrix (n : ℤ) : Matrix (RootIndex g) (RootIndex g) K :=
  fun i j => quantumInteger K (q₀ ^ n) (rootLength g i) *
    cartanMatrix g K q₀ t₀ n i j

/-- The scalar in FR (3.1). All zero modes commute; the expression with
1/n is used only for n ≠ 0, as specified immediately after (3.1). -/
def oscillatorCommutator (i j : RootIndex g) (n m : ℤ) : K :=
  if n = 0 ∨ n + m ≠ 0 then 0 else
    (n : K)⁻¹ * (q₀ ^ n - q₀ ^ (-n)) * (t₀ ^ n - t₀ ^ (-n)) *
      symmetrizedCartanMatrix g K q₀ t₀ n i j

abbrev FreeHeisenberg := FreeAlgebra K (RootIndex g × ℤ)

/-- The generators a_i[n], before imposing the Heisenberg relations. -/
def freeMode (i : RootIndex g) (n : ℤ) : FreeHeisenberg g K :=
  FreeAlgebra.ι K (i, n)

/-- Exactly the commutator relations (3.1), including the zero modes. -/
inductive HeisenbergRelation : FreeHeisenberg g K → FreeHeisenberg g K → Prop
  | commutator (i j : RootIndex g) (n m : ℤ) :
      HeisenbergRelation
        (freeMode g K i n * freeMode g K j m -
          freeMode g K j m * freeMode g K i n)
        (algebraMap K (FreeHeisenberg g K)
          (oscillatorCommutator g K q₀ t₀ i j n m))

/-- H_{q,t}(g), defined by the presentation in FR §3.1. -/
abbrev HeisenbergAlgebra := RingQuot (HeisenbergRelation g K q₀ t₀)

def heisenbergQuotient : FreeHeisenberg g K →ₐ[K] HeisenbergAlgebra g K q₀ t₀ :=
  RingQuot.mkAlgHom K (HeisenbergRelation g K q₀ t₀)

/-- The actual generator a_i[n] in H_{q,t}(g). -/
def rootMode (i : RootIndex g) (n : ℤ) : HeisenbergAlgebra g K q₀ t₀ :=
  heisenbergQuotient g K q₀ t₀ (freeMode g K i n)

/-- The defining relation holds in the quotient; it is not an axiom. -/
theorem rootMode_commutator (i j : RootIndex g) (n m : ℤ) :
    rootMode g K q₀ t₀ i n * rootMode g K q₀ t₀ j m -
      rootMode g K q₀ t₀ j m * rootMode g K q₀ t₀ i n =
      algebraMap K (HeisenbergAlgebra g K q₀ t₀)
        (oscillatorCommutator g K q₀ t₀ i j n m) := by
  have h := RingQuot.mkAlgHom_rel K
    (HeisenbergRelation.commutator (g := g) (K := K) (q₀ := q₀) (t₀ := t₀) i j n m)
  simpa only [rootMode, heisenbergQuotient, map_sub, map_mul,
    AlgHom.commutes] using h

/-- A Fock charge is specified by its eigenvalues lambda_i = (mu,alpha_i).
The left ideal below imposes a_i[n] v_mu = 0 for n > 0 and
a_i[0] v_mu = lambda_i v_mu, precisely as in FR §3.1. -/
def vacuumRelations (eigenvalues : RootIndex g → K) :
    Set (HeisenbergAlgebra g K q₀ t₀) :=
  {x | (∃ (i : RootIndex g) (n : ℤ), 0 < n ∧ x = rootMode g K q₀ t₀ i n) ∨
    (∃ i : RootIndex g, x = rootMode g K q₀ t₀ i 0 -
      algebraMap K (HeisenbergAlgebra g K q₀ t₀) (eigenvalues i))}

def vacuumLeftIdeal (eigenvalues : RootIndex g → K) :
    Submodule (HeisenbergAlgebra g K q₀ t₀) (HeisenbergAlgebra g K q₀ t₀) :=
  Submodule.span (HeisenbergAlgebra g K q₀ t₀)
    (vacuumRelations g K q₀ t₀ eigenvalues)

/-- The cyclic Fock module pi_mu defined by its vacuum relations. -/
abbrev FockModule (eigenvalues : RootIndex g → K) :=
  HeisenbergAlgebra g K q₀ t₀ ⧸ vacuumLeftIdeal g K q₀ t₀ eigenvalues

def vacuum (eigenvalues : RootIndex g → K) : FockModule g K q₀ t₀ eigenvalues :=
  (vacuumLeftIdeal g K q₀ t₀ eigenvalues).mkQ 1

/-- Positive modes annihilate the vacuum, by the defining left ideal. -/
theorem positiveMode_vacuum (eigenvalues : RootIndex g → K)
    (i : RootIndex g) (n : ℤ) (hn : 0 < n) :
    rootMode g K q₀ t₀ i n • vacuum g K q₀ t₀ eigenvalues = 0 := by
  change Submodule.Quotient.mk (rootMode g K q₀ t₀ i n * 1) = 0
  rw [mul_one, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Or.inl ⟨i, n, hn, rfl⟩)

/-- The zero-mode eigenvalue relation on the cyclic vector. -/
theorem zeroMode_vacuum (eigenvalues : RootIndex g → K) (i : RootIndex g) :
    rootMode g K q₀ t₀ i 0 • vacuum g K q₀ t₀ eigenvalues =
      algebraMap K (HeisenbergAlgebra g K q₀ t₀) (eigenvalues i) •
        vacuum g K q₀ t₀ eigenvalues := by
  change Submodule.Quotient.mk (rootMode g K q₀ t₀ i 0 * 1) =
    Submodule.Quotient.mk
      (algebraMap K (HeisenbergAlgebra g K q₀ t₀) (eigenvalues i) * 1)
  simp only [mul_one, Submodule.Quotient.eq]
  exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)

/-- Every state is obtained by acting on the vacuum with the Heisenberg algebra. -/
theorem vacuum_cyclic (eigenvalues : RootIndex g → K)
    (v : FockModule g K q₀ t₀ eigenvalues) :
    ∃ a : HeisenbergAlgebra g K q₀ t₀,
      a • vacuum g K q₀ t₀ eigenvalues = v := by
  obtain ⟨a, rfl⟩ := (vacuumLeftIdeal g K q₀ t₀ eigenvalues).mkQ_surjective v
  exact ⟨a, by change Submodule.Quotient.mk (a * 1) = Submodule.Quotient.mk a
               rw [mul_one]⟩

/-- pi_0, the state module used in FR's definition of the field centralizer. -/
abbrev VacuumModule := FockModule g K q₀ t₀ (fun _ => 0)

/-- FR (3.7), including its separate prescription for the zero mode. -/
def plusScreeningMode (i : RootIndex g) (n : ℤ) : HeisenbergAlgebra g K q₀ t₀ :=
  if n = 0 then (rootLength g i : K)⁻¹ • rootMode g K q₀ t₀ i 0
  else (q₀ ^ (n * (rootLength g i : ℤ)) -
    q₀ ^ (-(n * (rootLength g i : ℤ))))⁻¹ • rootMode g K q₀ t₀ i n

/-- FR (3.8). The parameter beta is the beta in t = q^beta in §3.2;
no h-adic substitution is made. The minus sign in the exponential in
(3.10) belongs to the current, not to these modes. -/
def minusScreeningMode (β : K) (i : RootIndex g) (n : ℤ) :
    HeisenbergAlgebra g K q₀ t₀ :=
  if n = 0 then β⁻¹ • rootMode g K q₀ t₀ i 0
  else (t₀ ^ n - t₀ ^ (-n))⁻¹ • rootMode g K q₀ t₀ i n

section UniversalProperty

variable {M : Type*} [AddCommGroup M] [Module (HeisenbergAlgebra g K q₀ t₀) M]

/-- A vacuum vector satisfying FR's relations determines a module map out
of the presented Fock module. This is proved from the presentation. -/
def fockLift (eigenvalues : RootIndex g → K) (v : M)
    (hpos : ∀ (i : RootIndex g) (n : ℤ), 0 < n → rootMode g K q₀ t₀ i n • v = 0)
    (hzero : ∀ i : RootIndex g, rootMode g K q₀ t₀ i 0 • v =
      algebraMap K (HeisenbergAlgebra g K q₀ t₀) (eigenvalues i) • v) :
    FockModule g K q₀ t₀ eigenvalues →ₗ[HeisenbergAlgebra g K q₀ t₀] M :=
  (vacuumLeftIdeal g K q₀ t₀ eigenvalues).liftQ
    (LinearMap.toSpanSingleton (HeisenbergAlgebra g K q₀ t₀) M v) (by
      apply Submodule.span_le.mpr
      intro x hx
      change x • v = 0
      rcases hx with ⟨i, n, hn, rfl⟩ | ⟨i, rfl⟩
      · exact hpos i n hn
      · rw [sub_smul, hzero i, sub_self])

@[simp]
theorem fockLift_vacuum (eigenvalues : RootIndex g → K) (v : M)
    (hpos : ∀ (i : RootIndex g) (n : ℤ), 0 < n → rootMode g K q₀ t₀ i n • v = 0)
    (hzero : ∀ i : RootIndex g, rootMode g K q₀ t₀ i 0 • v =
      algebraMap K (HeisenbergAlgebra g K q₀ t₀) (eigenvalues i) • v) :
    fockLift g K q₀ t₀ eigenvalues v hpos hzero (vacuum g K q₀ t₀ eigenvalues) = v := by
  change (1 : HeisenbergAlgebra g K q₀ t₀) • v = v
  exact one_smul _ v

/-- Maps from the Fock module are determined by the image of the vacuum. -/
theorem fockMap_ext (eigenvalues : RootIndex g → K)
    (f h : FockModule g K q₀ t₀ eigenvalues →ₗ[HeisenbergAlgebra g K q₀ t₀] M)
    (hv : f (vacuum g K q₀ t₀ eigenvalues) = h (vacuum g K q₀ t₀ eigenvalues)) :
    f = h := by
  apply LinearMap.ext
  intro v
  obtain ⟨a, rfl⟩ := vacuum_cyclic g K q₀ t₀ eigenvalues v
  simp only [map_smul, hv]

end UniversalProperty

/-- Adding central scalars to two elements preserves their commutator. -/
private theorem central_translate_commutator
    (x y : HeisenbergAlgebra g K q₀ t₀) (c d : K) :
    (x + algebraMap K _ c) * (y + algebraMap K _ d) -
      (y + algebraMap K _ d) * (x + algebraMap K _ c) = x * y - y * x := by
  simp only [add_mul, mul_add]
  rw [(Algebra.commutes c y), (Algebra.commutes d x),
    (Algebra.commutes d (algebraMap K _ c))]
  abel

/-- Translation of the central zero modes before passing to the quotient. -/
def freeChargeTranslation (δ : RootIndex g → K) :
    FreeHeisenberg g K →ₐ[K] HeisenbergAlgebra g K q₀ t₀ :=
  FreeAlgebra.lift K fun a => rootMode g K q₀ t₀ a.1 a.2 +
    algebraMap K _ (if a.2 = 0 then δ a.1 else 0)

/-- The Heisenberg algebra homomorphism a_i[n] ↦ a_i[n] + δ_i δ_{n,0}.
Its existence follows from (3.1), since the translated modes are central. -/
def chargeTranslation (δ : RootIndex g → K) :
    HeisenbergAlgebra g K q₀ t₀ →ₐ[K] HeisenbergAlgebra g K q₀ t₀ :=
  RingQuot.liftAlgHom K ⟨freeChargeTranslation g K q₀ t₀ δ, by
    intro x y h
    cases h with
    | commutator i j n m =>
      simp only [map_sub, map_mul, AlgHom.commutes, freeChargeTranslation,
        freeMode, FreeAlgebra.lift_ι_apply]
      rw [central_translate_commutator]
      exact rootMode_commutator g K q₀ t₀ i j n m⟩

@[simp]
theorem chargeTranslation_rootMode (δ : RootIndex g → K) (i : RootIndex g) (n : ℤ) :
    chargeTranslation g K q₀ t₀ δ (rootMode g K q₀ t₀ i n) =
      rootMode g K q₀ t₀ i n + algebraMap K _ (if n = 0 then δ i else 0) := by
  unfold chargeTranslation rootMode heisenbergQuotient
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  exact FreeAlgebra.lift_ι_apply _ _

theorem chargeTranslation_vacuumLeftIdeal (charge δ : RootIndex g → K)
    {x : HeisenbergAlgebra g K q₀ t₀} (hx : x ∈ vacuumLeftIdeal g K q₀ t₀ charge) :
    chargeTranslation g K q₀ t₀ (-δ) x ∈ vacuumLeftIdeal g K q₀ t₀ (charge + δ) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, n, hn, rfl⟩ | ⟨i, rfl⟩
    · rw [chargeTranslation_rootMode, if_neg (ne_of_gt hn), map_zero, add_zero]
      exact Submodule.subset_span (Or.inl ⟨i, n, hn, rfl⟩)
    · have heq : chargeTranslation g K q₀ t₀ (-δ)
          (rootMode g K q₀ t₀ i 0 - algebraMap K _ (charge i)) =
          rootMode g K q₀ t₀ i 0 - algebraMap K _ ((charge + δ) i) := by
        rw [map_sub, AlgHom.commutes, chargeTranslation_rootMode]
        change rootMode g K q₀ t₀ i 0 + algebraMap K _ (-(δ i)) -
          algebraMap K _ (charge i) =
          rootMode g K q₀ t₀ i 0 - algebraMap K _ (charge i + δ i)
        rw [map_neg, map_add]
        abel
      rw [heq]
      exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add] using (vacuumLeftIdeal g K q₀ t₀ (charge + δ)).add_mem hx hy
  | smul a x _ hx =>
    change chargeTranslation g K q₀ t₀ (-δ) (a * x) ∈ _
    rw [map_mul]
    exact (vacuumLeftIdeal g K q₀ t₀ (charge + δ)).smul_mem _ hx

/-- The charge-shift map on the induced Fock modules. On creation words it
keeps the word and changes the vacuum charge. It is constructed by descent
from the Heisenberg algebra, not supplied as an uninterpreted operator. -/
def fockChargeShift (charge δ : RootIndex g → K) :
    FockModule g K q₀ t₀ charge →ₗ[K] FockModule g K q₀ t₀ (charge + δ) :=
  ((vacuumLeftIdeal g K q₀ t₀ charge).restrictScalars K).liftQ
    (((vacuumLeftIdeal g K q₀ t₀ (charge + δ)).mkQ.restrictScalars K).comp
      (chargeTranslation g K q₀ t₀ (-δ)).toLinearMap) (by
        intro x hx
        change Submodule.Quotient.mk (chargeTranslation g K q₀ t₀ (-δ) x) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact chargeTranslation_vacuumLeftIdeal g K q₀ t₀ charge δ hx)

@[simp]
theorem fockChargeShift_vacuum (charge δ : RootIndex g → K) :
    fockChargeShift g K q₀ t₀ charge δ (vacuum g K q₀ t₀ charge) =
      vacuum g K q₀ t₀ (charge + δ) := by
  change Submodule.Quotient.mk (chargeTranslation g K q₀ t₀ (-δ) 1) =
    Submodule.Quotient.mk 1
  rw [map_one]

/-- The charge change forced by FR (3.6). In weight notation this is
mu ↦ mu + gamma * beta * r^vee * alpha_i. The r^vee factor corrects the
charge label printed in §3.2 while preserving equation (3.6), as agreed.
Assakaf §2.2 uses this same normalization; no coefficient-ring change is made. -/
def screeningChargeChange (β γ : K) (i : RootIndex g) : RootIndex g → K :=
  fun j => γ * β * ((rootLength g j : K) * (cartan g j i : K))

/-- The plus-screening target charge, from e^(-Q_i/r_i). -/
def plusScreeningCharge (β : K) (i : RootIndex g) : RootIndex g → K :=
  screeningChargeChange g K β (-(rootLength g i : K)⁻¹) i

/-- The minus-screening target charge, from e^(Q_i/beta). -/
def minusScreeningCharge (β : K) (i : RootIndex g) : RootIndex g → K :=
  screeningChargeChange g K β β⁻¹ i

end Heisenberg

namespace Fields

local instance coefficientField : _root_.Field Coefficient := inferInstance

/-- Independent q,t parameters, with beta for the charge labels in t=q^beta.
No expansion of q or t in an h-adic parameter is made. -/
abbrev Scalars := RatFunc Coefficient
def Q : Scalars := RatFunc.C q
def T : Scalars := RatFunc.C t
def beta : Scalars := RatFunc.X

variable (g : SimpleLieType)

abbrev Charge := Option (ScreeningSign × RootIndex g)

def chargeEigenvalues : Charge g → RootIndex g → Scalars
  | none => 0
  | some (.plus, i) => 0 + plusScreeningCharge g Scalars beta i
  | some (.minus, i) => 0 + minusScreeningCharge g Scalars beta i

abbrev State (charge : Charge g) :=
  FockModule g Scalars Q T (chargeEigenvalues g charge)

/-- The ambient space of Fourier-coefficient actions on the vacuum module
and the target modules of the screening operators. The field space below
is the span of the normally ordered fields of FR (3.13). -/
abbrev Field := ∀ charge : Charge g, ℤ → State g charge → State g charge

abbrev ModeIndex := RootIndex g × {n : ℤ // n ≠ 0}
abbrev ModeMonomial := ModeIndex g →₀ ℕ
abbrev SymbolSeries := MvPowerSeries (ModeIndex g) Scalars

def monomialDegree (d : ModeMonomial g) : ℤ :=
  d.sum fun a k => -a.2.val * (k : ℤ)

/-- A linear formal series in the nonzero Heisenberg modes. -/
def linearSymbol (c : ModeIndex g → Scalars) : SymbolSeries g :=
  fun d => if d.sum (fun _ k => k) = 1 then d.sum (fun a k => (k : Scalars) * c a) else 0

/-- The formal exponential sum_k L^k/k!. Since L has zero constant term,
the coefficient of a monomial of total degree d uses only k ≤ d. -/
def exponentialSymbol (c : ModeIndex g → Scalars) : SymbolSeries g :=
  fun d => ∑ k ∈ Finset.range (d.sum (fun _ n => n) + 1),
    (Nat.factorial k : Scalars)⁻¹ * MvPowerSeries.coeff d (linearSymbol g c ^ k)

/-- A normally ordered formal expression, with an overall z^(-offset).
The commutative symbol variables record modes before normal ordering. -/
structure NormalSymbol where
  coefficients : Charge g → SymbolSeries g
  offset : ℤ

def symbolOne : NormalSymbol g := ⟨fun _ => 1, 0⟩

def normalProduct (a b : NormalSymbol g) : NormalSymbol g :=
  ⟨fun charge => a.coefficients charge * b.coefficients charge, a.offset + b.offset⟩

def normalProducts (xs : List (NormalSymbol g)) : NormalSymbol g :=
  xs.foldr (normalProduct g) (symbolOne g)

/-- Formal differentiation, applied before taking normally ordered products. -/
def symbolDerivative (a : NormalSymbol g) : NormalSymbol g :=
  ⟨fun charge d => ((monomialDegree g d - a.offset : ℤ) : Scalars) *
      a.coefficients charge d, a.offset + 1⟩

/-- Normal ordering puts every negative mode to the left of every positive
mode. Modes of the same sign commute by (3.1). -/
def normalWord (d : ModeMonomial g) : HeisenbergAlgebra g Scalars Q T :=
  let word := d.support.toList
  ((word.filter fun a => a.2.val < 0).map fun a =>
    rootMode g Scalars Q T a.1 a.2.val ^ d a).prod *
  ((word.filter fun a => 0 < a.2.val).map fun a =>
    rootMode g Scalars Q T a.1 a.2.val ^ d a).prod

/-- Coefficientwise action of a normally ordered formal series. The sum is
taken in the discrete Fock module. Local finiteness on every state is proved
by `evaluateSymbol_hasFiniteSupport` in
`D4CounterexampleProof/LocalFiniteness.lean`. -/
def evaluateSymbol (a : NormalSymbol g) : Field g := fun charge n v =>
  letI : TopologicalSpace (State g charge) := ⊥
  ∑' d : ModeMonomial g,
    if monomialDegree g d - a.offset = n then
      a.coefficients charge d • (normalWord g d • v) else 0

/-- Evaluation of the empty normally ordered product is the identity field. -/
theorem evaluateSymbol_symbolOne (charge : Charge g) (n : ℤ)
    (v : State g charge) :
    evaluateSymbol g (symbolOne g) charge n v = if n = 0 then v else 0 := by
  classical
  let : TopologicalSpace (State g charge) := ⊥
  unfold evaluateSymbol
  dsimp only [symbolOne]
  rw [tsum_eq_single 0]
  · have hc : (1 : SymbolSeries g) 0 = 1 := by
      change MvPowerSeries.coeff 0 (1 : SymbolSeries g) = 1
      simp
    by_cases hn : n = 0
    · simp [normalWord, monomialDegree, hn, hc]
      exact one_smul Scalars v
    · simp [monomialDegree, hn, eq_comm]
  · intro d hd
    have hc : (1 : SymbolSeries g) d = 0 := by
      change MvPowerSeries.coeff d (1 : SymbolSeries g) = 0
      rw [MvPowerSeries.coeff_one, if_neg hd]
    rw [hc]
    by_cases h : monomialDegree g d - 0 = n
    · erw [if_pos h]
      exact zero_smul Scalars (normalWord g d • v)
    · erw [if_neg h]

def finiteCartanInverse : Matrix (RootIndex g) (RootIndex g) ℚ :=
  (fun i j => (cartan g i j : ℚ))⁻¹

/-- The integral exponents 2(rho^vee,omega_i) and 2r^vee(rho,omega_i),
calculated in the fundamental-weight coordinates of the root data. -/
def rhoTExponent (i : RootIndex g) : ℤ :=
  (2 * ∑ j, finiteCartanInverse g j i).num

def rhoQExponent (i : RootIndex g) : ℤ :=
  (2 * ∑ j, (rootLength g j : ℚ) * finiteCartanInverse g j i).num

def chargePrefactor (charge : Charge g) (weight : Weight g) : Coefficient :=
  match charge with
  | none => 1
  | some (sign, j) => screeningZeroMode sign j weight

/-- The original Y_i, including its scalar and zero-mode prefactors.
The coefficients of y_i[n] in the a_j[n] basis are determined by (3.5).
`inverse` changes both the prefactor and the exponent. -/
def weightVertex (i : RootIndex g) (inverse : Bool) (a b : ℤ) : NormalSymbol g :=
  let sign : ℤ := if inverse then -1 else 1
  ⟨fun charge =>
    MvPowerSeries.C (RatFunc.C
      ((t ^ rhoTExponent g i * q ^ (-rhoQExponent g i) *
        chargePrefactor g charge (fundamentalWeight g i)) ^ sign)) *
    exponentialSymbol g (fun mode => RatFunc.C
      ((sign : Coefficient) * (deformedCartan g mode.2.val)⁻¹ mode.1 i *
        (q ^ a * t ^ b) ^ (-mode.2.val))), 0⟩

/-- The original A_i and its inverse, with their full prefactors. -/
def rootVertex (i : RootIndex g) (inverse : Bool) (a b : ℤ) : NormalSymbol g :=
  let sign : ℤ := if inverse then -1 else 1
  ⟨fun charge =>
    MvPowerSeries.C (RatFunc.C
      ((t ^ (2 : ℤ) * q ^ (-(2 * rootLength g i : ℤ)) *
        chargePrefactor g charge (simpleRoot g i)) ^ sign)) *
    exponentialSymbol g (fun mode => if mode.1 = i then
      RatFunc.C ((sign : Coefficient) * (q ^ a * t ^ b) ^ (-mode.2.val)) else 0), 0⟩

structure FieldFactor where
  index : RootIndex g
  inverse : Bool
  qShift : ℤ
  tShift : ℤ
  derivatives : ℕ

def fieldFactorSymbol (f : FieldFactor g) : NormalSymbol g :=
  (symbolDerivative g)^[f.derivatives]
    (weightVertex g f.index f.inverse f.qShift f.tShift)

/-- FR (3.13): the vector space spanned by normally ordered products of
shifted Y_i^±1 and their derivatives. -/
def heisenbergFieldSpace : Submodule Scalars (Field g) :=
  Submodule.span Scalars
    {f | ∃ factors : List (FieldFactor g),
      f = evaluateSymbol g (normalProducts g (factors.map (fieldFactorSymbol g)))}

def screeningSymbol (sign : ScreeningSign) (i : RootIndex g) : NormalSymbol g :=
  ⟨fun _ => exponentialSymbol g (fun mode =>
    RatFunc.C (screeningModes sign i mode.2.val mode.1)), 0⟩

/-- The screening operator is the z^(-1) coefficient of (3.9) or (3.10),
followed by the charge shift. The z-zero-mode factor is 1 on pi_0. -/
def screeningOperator (sign : ScreeningSign) (i : RootIndex g) :
    State g none → State g (some (sign, i)) :=
  match sign with
  | .plus => fun v => fockChargeShift g Scalars Q T 0
      (plusScreeningCharge g Scalars beta i)
      (evaluateSymbol g (screeningSymbol g .plus i) none (-1) v)
  | .minus => fun v => fockChargeShift g Scalars Q T 0
      (minusScreeningCharge g Scalars beta i)
      (evaluateSymbol g (screeningSymbol g .minus i) none (-1) v)

/-- FR §3.3: the subspace of fields commuting with both screening operators. -/
def deformedW : Set (Field g) :=
  {f | f ∈ heisenbergFieldSpace g ∧
    ∀ (sign : ScreeningSign) (i : RootIndex g) (n : ℤ) (v : State g none),
      f (some (sign, i)) n (screeningOperator g sign i v) =
        screeningOperator g sign i (f none n v)}

def elementarySymbol (i : RootIndex g) (factors : List (InverseRootFactor g)) :
    NormalSymbol g :=
  normalProduct g (weightVertex g i false 0 0)
    (normalProducts g (factors.map fun f => rootVertex g f.root true f.qShift f.tShift))

def fundamentalExpansion (i : RootIndex g) (terms : List (ElementaryTerm g)) : Field g :=
  evaluateSymbol g (weightVertex g i false 0 0) +
    (terms.map fun term => RatFunc.C term.coefficient •
      evaluateSymbol g (elementarySymbol g i term.factors)).sum

end Fields

/-! Fundamental modules are specified by their Drinfeld polynomials.
The current presentation and polynomial convention are those of FR,
*The q-characters of representations of quantum affine algebras and
deformations of W-algebras*, §2.2–2.3, equations (2.2)–(2.4).
This does not change the coefficient/completion setting of the W-algebra. -/
namespace Drinfeld

variable (g : SimpleLieType)

inductive Generator where
  | current : Bool → RootIndex g → ℤ → Generator
  | cartanMode : RootIndex g → ℤ → Generator
  | toral : RootIndex g → Bool → Generator
  | centralHalf : Bool → Generator

abbrev Free := FreeAlgebra QuantumCoefficient (Generator g)
def x (positive : Bool) (i : RootIndex g) (n : ℤ) : Free g :=
  FreeAlgebra.ι QuantumCoefficient (.current positive i n)
def h (i : RootIndex g) (n : ℤ) : Free g :=
  FreeAlgebra.ι QuantumCoefficient (.cartanMode i n)
def k (i : RootIndex g) (positive : Bool) : Free g :=
  FreeAlgebra.ι QuantumCoefficient (.toral i positive)
def c (positive : Bool) : Free g :=
  FreeAlgebra.ι QuantumCoefficient (.centralHalf positive)
def sign (positive : Bool) : ℤ := if positive then 1 else -1
def centralPower (n : ℤ) : Free g :=
  (c g (decide (0 ≤ n))) ^ n.natAbs
def B (i j : RootIndex g) : ℤ := (rootLength g i : ℤ) * cartan g i j

/-- Coefficients of the formal exponential in FR's current formula (2.2).
Only finitely many powers contribute to each coefficient. -/
def cartanExponentialCoefficient (positive : Bool) (i : RootIndex g) (n : ℕ) : Free g :=
  let L : PowerSeries (Free g) := PowerSeries.mk fun m =>
    if m = 0 then 0 else
      ((sign positive : QuantumCoefficient) * (quantumQ - quantumQ⁻¹)) •
        h g i (sign positive * (m : ℤ))
  ∑ r ∈ Finset.range (n + 1),
    (Nat.factorial r : QuantumCoefficient)⁻¹ • PowerSeries.coeff n (L ^ r)

def phi (positive : Bool) (i : RootIndex g) (n : ℤ) : Free g :=
  if 0 ≤ sign positive * n then
    k g i positive * cartanExponentialCoefficient g positive i n.natAbs else 0

def serre (positive : Bool) (i j : RootIndex g)
    (modes : Fin (1 - cartan g i j).toNat → ℤ) (m : ℤ) : Free g :=
  let s := (1 - cartan g i j).toNat
  ∑ permutation : Equiv.Perm (Fin s), ∑ r ∈ Finset.range (s + 1),
    let word := List.ofFn fun a : Fin s => x g positive i (modes (permutation a))
    ((-1 : QuantumCoefficient) ^ r * quantumBinomial (quantumQ ^ rootLength g i) s r) •
      ((word.take r).prod * x g positive j m * (word.drop r).prod)

/-- The full quantum affine current presentation, including the central
element. h_i[0] is an auxiliary generator explicitly set to zero. -/
inductive Relation : Free g → Free g → Prop
  | zero_h (i : RootIndex g) : Relation (h g i 0) 0
  | toral_inverse (i : RootIndex g) (p : Bool) : Relation (k g i p * k g i (!p)) 1
  | toral_commute (i j : RootIndex g) (p r : Bool) :
      Relation (k g i p * k g j r) (k g j r * k g i p)
  | central_inverse (p : Bool) : Relation (c g p * c g (!p)) 1
  | central_commute (p : Bool) (a : Generator g) :
      Relation (c g p * FreeAlgebra.ι QuantumCoefficient a)
        (FreeAlgebra.ι QuantumCoefficient a * c g p)
  | toral_h (i j : RootIndex g) (p : Bool) (n : ℤ) :
      Relation (k g i p * h g j n) (h g j n * k g i p)
  | toral_x (i j : RootIndex g) (p : Bool) (n : ℤ) :
      Relation (k g i true * x g p j n * k g i false)
        (quantumQ ^ (sign p * B g i j) • x g p j n)
  | h_x (i j : RootIndex g) (p : Bool) (n m : ℤ) (hn : n ≠ 0) :
      Relation (h g i n * x g p j m - x g p j m * h g i n)
        (((sign p : QuantumCoefficient) * qInteger quantumQ (n * B g i j) / (n : QuantumCoefficient)) •
          (centralPower g (-sign p * (n.natAbs : ℤ)) * x g p j (n + m)))
  | h_h (i j : RootIndex g) (n m : ℤ) (hn : n ≠ 0) (hm : m ≠ 0) :
      Relation (h g i n * h g j m - h g j m * h g i n)
        (if n + m = 0 then
          (qInteger quantumQ (n * B g i j) / ((n : QuantumCoefficient) * (quantumQ - quantumQ⁻¹))) •
            (centralPower g (2 * n) - centralPower g (-2 * n)) else 0)
  | same_sign (i j : RootIndex g) (p : Bool) (n m : ℤ) :
      Relation
        (x g p i (n + 1) * x g p j m -
          quantumQ ^ (sign p * B g i j) • (x g p j m * x g p i (n + 1)))
        (quantumQ ^ (sign p * B g i j) • (x g p i n * x g p j (m + 1)) -
          x g p j (m + 1) * x g p i n)
  | opposite_sign (i j : RootIndex g) (n m : ℤ) :
      Relation (x g true i n * x g false j m - x g false j m * x g true i n)
        (if i = j then
          (quantumQ ^ rootLength g i - quantumQ ^ (-(rootLength g i : ℤ)))⁻¹ •
            (centralPower g (n - m) * phi g true i (n + m) -
              centralPower g (m - n) * phi g false i (n + m)) else 0)
  | quantum_serre (i j : RootIndex g) (hne : i ≠ j) (p : Bool)
      (modes : Fin (1 - cartan g i j).toNat → ℤ) (m : ℤ) :
      Relation (serre g p i j modes m) 0

abbrev QuantumAffine := RingQuot (Relation g)
def quotientMap : Free g →ₐ[QuantumCoefficient] QuantumAffine g :=
  RingQuot.mkAlgHom QuantumCoefficient (Relation g)
abbrev Representation (d : ℕ) :=
  QuantumAffine g →ₐ[QuantumCoefficient] Module.End QuantumCoefficient (Fin d → QuantumCoefficient)

def weightSpace {d : ℕ} (V : Representation g d) (weight : Weight g) :
    Submodule QuantumCoefficient (Fin d → QuantumCoefficient) :=
  ⨅ i : RootIndex g,
    LinearMap.ker (V (quotientMap g (k g i true)) -
      quantumQ ^ ((rootLength g i : ℤ) * weight i) • LinearMap.id)

def weightMultiplicity {d : ℕ} (V : Representation g d) (weight : Weight g) : ℕ :=
  Module.finrank QuantumCoefficient (weightSpace g V weight)

def TypeOne {d : ℕ} (V : Representation g d) : Prop :=
  V (quotientMap g (c g true)) = 1 ∧ (⨆ weight : Weight g, weightSpace g V weight) = ⊤

def Irreducible {d : ℕ} (V : Representation g d) : Prop :=
  0 < d ∧ ∀ W : Submodule QuantumCoefficient (Fin d → QuantumCoefficient),
    (∀ a v, v ∈ W → V a v ∈ W) → W = ⊥ ∨ W = ⊤

def shiftedPolynomial (P : Polynomial QuantumCoefficient) (a : QuantumCoefficient) :
    Polynomial QuantumCoefficient := P.comp (Polynomial.C a * Polynomial.X)

/-- The defining highest-current eigenvalue identity
Psi_i^±(u) = q_i^(deg P_i) P_i(u q_i^(-1))/P_i(u q_i).
For the minus expansion, reversing both polynomials expresses the same
identity in u^(-1). No finite-highest-weight surrogate is used. -/
def HasDrinfeldPolynomials {d : ℕ} (V : Representation g d)
    (P : RootIndex g → Polynomial QuantumCoefficient) : Prop :=
  (∀ i, (P i).coeff 0 = 1) ∧
  ∃ (v : Fin d → QuantumCoefficient) (eigenvalues : Bool → RootIndex g → ℕ → QuantumCoefficient),
    v ≠ 0 ∧
    (∀ w, ∃ a : QuantumAffine g, V a v = w) ∧
    (∀ i n, V (quotientMap g (x g true i n)) v = 0) ∧
    (∀ (p : Bool) (i : RootIndex g) (n : ℕ),
      V (quotientMap g (phi g p i (sign p * (n : ℤ)))) v = eigenvalues p i n • v) ∧
    ∀ p i,
      let qi := quantumQ ^ rootLength g i
      let numerator := shiftedPolynomial (P i) qi⁻¹
      let denominator := shiftedPolynomial (P i) qi
      let numeratorAtEnd := if p then numerator else numerator.reverse
      let denominatorAtEnd := if p then denominator else denominator.reverse
      (denominatorAtEnd : PowerSeries QuantumCoefficient) * PowerSeries.mk (eigenvalues p i) =
        PowerSeries.C (qi ^ (P i).natDegree) * (numeratorAtEnd : PowerSeries QuantumCoefficient)

/-- FR's defining degree-one tuple P_i(u)=1-au, P_j(u)=1 for j≠i. -/
def fundamentalPolynomials (i : RootIndex g) (a : QuantumCoefficient) :
    RootIndex g → Polynomial QuantumCoefficient :=
  fun j => if j = i then 1 - Polynomial.C a * Polynomial.X else 1

def FundamentalRepresentation {d : ℕ} (i : RootIndex g) (V : Representation g d) : Prop :=
  TypeOne g V ∧ Irreducible g V ∧
    ∃ a : QuantumCoefficient, a ≠ 0 ∧ HasDrinfeldPolynomials g V (fundamentalPolynomials g i a)

end Drinfeld

end OriginalFR

/-- The requirements in FR Conjecture 1 at a specified fundamental index:
the original elementary expansion belongs to the screening centralizer,
and its specialized weight multiplicities are those of a fundamental module.
-/
def HasFundamentalField (g : SimpleLieType) (i : RootIndex g) : Prop :=
  ∃ (terms : List (ElementaryTerm g)) (dimension : ℕ)
      (V : OriginalFR.Drinfeld.Representation g dimension),
    (∀ term ∈ terms, term.valid) ∧
    OriginalFR.Fields.fundamentalExpansion g i terms ∈ OriginalFR.Fields.deformedW g ∧
    OriginalFR.Drinfeld.FundamentalRepresentation g i V ∧
    ∀ weight, expansionMultiplicity i terms weight =
      OriginalFR.Drinfeld.weightMultiplicity g V weight

end FrenkelReshetikhin
