import Mathlib.Algebra.MvPolynomial.PDeriv
import StatementDefinitions
import Mathlib.Tactic.Ring

/-! Polynomial multiplication and differentiation operators used to
construct a representation of the original presented Heisenberg algebra.
This construction does not change the definition of the Fock quotient. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

variable {K σ : Type*} [Field K]
attribute [local instance] Classical.propDecidable

def creation (i : σ) : Module.End K (MvPolynomial σ K) :=
  LinearMap.mulLeft K (MvPolynomial.X i)

def annihilation (i : σ) : Module.End K (MvPolynomial σ K) :=
  (MvPolynomial.pderiv i).toLinearMap

@[simp] theorem creation_apply (i : σ) (p : MvPolynomial σ K) :
    creation i p = MvPolynomial.X i * p := rfl

@[simp] theorem annihilation_apply (i : σ) (p : MvPolynomial σ K) :
    annihilation i p = MvPolynomial.pderiv i p := rfl

theorem creation_commute (i j : σ) :
    Commute (creation (K := K) i) (creation j) := by
  apply LinearMap.ext
  intro p
  change MvPolynomial.X i * (MvPolynomial.X j * p) =
    MvPolynomial.X j * (MvPolynomial.X i * p)
  ring

theorem pderiv_commute (i j : σ) (p : MvPolynomial σ K) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [MvPolynomial.pderiv_X,
        hki, hkj, hij, Ne.symm hij, eq_comm, hp] <;> ring

theorem annihilation_commute (i j : σ) :
    Commute (annihilation (K := K) i) (annihilation j) := by
  apply LinearMap.ext
  intro p
  exact pderiv_commute i j p

theorem annihilation_creation_commutator (i j : σ) :
    annihilation (K := K) i * creation j - creation j * annihilation i =
      (if i = j then (1 : K) else 0) • (1 : Module.End K (MvPolynomial σ K)) := by
  classical
  apply LinearMap.ext
  intro p
  change MvPolynomial.pderiv i (MvPolynomial.X j * p) -
      MvPolynomial.X j * MvPolynomial.pderiv i p =
    (if i = j then (1 : K) else 0) • p
  by_cases hij : i = j
  · subst j
    simp
  · simp [MvPolynomial.pderiv_X, hij, Ne.symm hij]

theorem weighted_annihilation_creation {ι τ : Type*} [Fintype ι]
    (b : ι → K) (i : ι) (n m : τ) :
    (∑ j : ι, b j • annihilation (j, n)) * creation (i, m) -
      creation (i, m) * (∑ j : ι, b j • annihilation (j, n)) =
      (if n = m then b i else 0) • (1 : Module.End K (MvPolynomial (ι × τ) K)) := by
  classical
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : ι, b j • (annihilation (j, n) * creation (i, m) -
        creation (i, m) * annihilation (j, n)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    _ = ∑ j : ι, b j • ((if (j, n) = (i, m) then (1 : K) else 0) •
        (1 : Module.End K (MvPolynomial (ι × τ) K))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [annihilation_creation_commutator]
      by_cases he : (j, n) = (i, m) <;> simp [he]
    _ = _ := by
      by_cases hnm : n = m
      · subst m
        simp [Prod.mk.injEq]
      · simp [Prod.mk.injEq, hnm]

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
