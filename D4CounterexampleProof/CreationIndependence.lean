import D4CounterexampleProof.ExponentialSymbols
import D4CounterexampleProof.VacuumCoefficients

/-! Polynomial independence for formal creation series satisfying the
original exponential differential equations, in arbitrary mode variables. -/

namespace FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock

noncomputable section

open scoped BigOperators

section General

variable {K σ : Type*} [Field K]
attribute [local instance] Classical.propDecidable

def differential (i : σ) : Module.End K (MvPowerSeries σ K) :=
  (MvPowerSeries.pderiv K i).toLinearMap

theorem differentials_commute (i j : σ) : Commute (differential (K := K) i) (differential j) := by
  apply LinearMap.ext
  intro f
  change MvPowerSeries.pderiv K i (MvPowerSeries.pderiv K j f) =
    MvPowerSeries.pderiv K j (MvPowerSeries.pderiv K i f)
  classical
  ext d
  simp only [MvPowerSeries.coeff_pderiv]
  rw [add_right_comm d (Finsupp.single i 1) (Finsupp.single j 1)]
  by_cases hij : i = j
  · subst j; rfl
  · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij,
      Finsupp.single_eq_of_ne (Ne.symm hij), add_zero]
    ring

theorem shifted_differential_product (F : MvPowerSeries σ K) (c : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (c i) * F)
    (i : σ) (P : MvPolynomial σ K) :
    (differential (K := K) i - c i • (1 : Module.End K (MvPowerSeries σ K)))
      ((P : MvPowerSeries σ K) * F) = (MvPolynomial.pderiv i P : MvPowerSeries σ K) * F := by
  change MvPowerSeries.pderiv K i ((P : MvPowerSeries σ K) * F) -
    c i • ((P : MvPowerSeries σ K) * F) = _
  rw [Derivation.leibniz, MvPowerSeries.pderiv_coe, hF]
  simp only [smul_eq_mul, MvPowerSeries.smul_eq_C_mul]
  ring

theorem shifted_differential_pow_product (F : MvPowerSeries σ K) (c : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (c i) * F)
    (i : σ) (P : MvPolynomial σ K) (n : ℕ) :
    ((differential (K := K) i - c i • (1 : Module.End K (MvPowerSeries σ K))) ^ n)
      ((P : MvPowerSeries σ K) * F) =
      ((MvPolynomial.pderiv i)^[n] P : MvPowerSeries σ K) * F := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, shifted_differential_product F c hF]
    rw [Function.iterate_succ_apply']

theorem iterate_pderiv_monomial_generic (i : σ) (d : σ →₀ ℕ) (a : K) (n : ℕ) :
    (MvPolynomial.pderiv i)^[n] (MvPolynomial.monomial d a) =
      MvPolynomial.monomial (d - Finsupp.single i n) (a * ((d i).descFactorial n : K)) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial]
    have hd : d - Finsupp.single i n - Finsupp.single i 1 = d - Finsupp.single i (n + 1) := by
      ext j
      by_cases hj : j = i
      · subst j; simp [Finsupp.tsub_apply, Nat.sub_sub]
      · simp [Finsupp.tsub_apply, hj]
    rw [hd, Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.descFactorial_succ, Nat.cast_mul]
    congr 1
    ring

theorem polynomial_eigenseries_mem (F : MvPowerSeries σ K) (c : σ → K)
    (hF : ∀ i, MvPowerSeries.pderiv K i F = MvPowerSeries.C (c i) * F)
    (i : σ) (P : MvPolynomial σ K) :
    (P : MvPowerSeries σ K) * F ∈ (differential (K := K) i).maxGenEigenspace (c i) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨d i + 1, ?_⟩
    rw [shifted_differential_pow_product F c hF, iterate_pderiv_monomial_generic,
      Nat.descFactorial_of_lt (Nat.lt_succ_self (d i))]
    simp
  | add P Q hP hQ =>
    simpa only [MvPolynomial.coe_add, add_mul] using
      ((differential (K := K) i).maxGenEigenspace (c i)).add_mem hP hQ

/-- Polynomially weighted formal exponentials are independent whenever
their exponent vectors differ. This formulation applies directly to
creation restrictions of the original FR series. -/
theorem polynomial_eigenseries_sum_eq_zero {ι : Type*} (s : Finset ι)
    (F : ι → MvPowerSeries σ K) (c : ι → σ → K) (hc : Function.Injective c)
    (hF : ∀ j i, MvPowerSeries.pderiv K i (F j) = MvPowerSeries.C (c j i) * F j)
    (hne : ∀ j, F j ≠ 0) (P : ι → MvPolynomial σ K)
    (hsum : ∑ j ∈ s, (P j : MvPowerSeries σ K) * F j = 0) : ∀ j ∈ s, P j = 0 := by
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (differential (K := K) (σ := σ)) (fun i j a =>
      Module.End.mapsTo_maxGenEigenspace_of_comm (differentials_commute j i) a)
  have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp (hind.comp hc) s
    (fun j => (P j : MvPowerSeries σ K) * F j)
    (fun j _ => (Submodule.mem_iInf _).mpr fun i => polynomial_eigenseries_mem (F j) (c j) (hF j) i (P j)) hsum
  intro j hj
  exact MvPolynomial.coe_eq_zero_iff.mp ((mul_eq_zero.mp (hz j hj)).resolve_right (hne j))

theorem pderiv_killCompl {τ : Type*} (e : σ ↪ τ) (f : MvPowerSeries τ K) (i : σ) :
    MvPowerSeries.pderiv K i (MvPowerSeries.killCompl e f) =
      MvPowerSeries.killCompl e (MvPowerSeries.pderiv K (e i) f) := by
  classical
  ext d
  simp only [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_killCompl,
    Finsupp.embDomain_add, Finsupp.embDomain_single]
  rw [Finsupp.embDomain_apply_self]

/-- A nonzero contribution to a zero sum has a distinct nonzero
polynomial contribution with the same creation exponent vector. Repeated
exponent vectors and arbitrary polynomial factors are allowed. -/
theorem eigenseries_cancelling_partner {ι : Type*} (s : Finset ι)
    (F : ι → MvPowerSeries σ K) (c : ι → σ → K)
    (hF : ∀ j i, MvPowerSeries.pderiv K i (F j) = MvPowerSeries.C (c j i) * F j)
    (P : ι → MvPolynomial σ K)
    (hsum : ∑ j ∈ s, (P j : MvPowerSeries σ K) * F j = 0)
    (i : ι) (hi : i ∈ s) (hPi : P i ≠ 0) (hFi : F i ≠ 0) :
    ∃ j ∈ s, j ≠ i ∧ c j = c i ∧ P j ≠ 0 := by
  classical
  let V (j : ι) := (P j : MvPowerSeries σ K) * F j
  let u (a : σ → K) := ∑ j ∈ s.filter (fun j => c j = a), V j
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (differential (K := K) (σ := σ)) (fun j k a =>
      Module.End.mapsTo_maxGenEigenspace_of_comm (differentials_commute k j) a)
  have humem (a : σ → K) : u a ∈ ⨅ mode, (differential (K := K) mode).maxGenEigenspace (a mode) := by
    apply Submodule.sum_mem
    intro j hj
    have hja := (Finset.mem_filter.mp hj).2
    apply (Submodule.mem_iInf _).mpr
    intro mode
    rw [← hja]
    exact polynomial_eigenseries_mem (F j) (c j) (hF j) mode (P j)
  have hgroup : ∑ a ∈ s.image c, u a = 0 := by
    calc
      _ = ∑ j ∈ s, V j :=
        Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem c hj) _
      _ = 0 := hsum
  have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind (s.image c) u
    (fun a _ => humem a) hgroup (c i) (Finset.mem_image_of_mem c hi)
  by_contra hnone
  have hu : u (c i) = V i := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hpj : P j = 0 := by
        by_contra hpj
        exact hnone ⟨j, (Finset.mem_filter.mp hj).1, hji,
          (Finset.mem_filter.mp hj).2, hpj⟩
      simp only [V, hpj, MvPolynomial.coe_zero, zero_mul]
    · intro hnot
      exact False.elim (hnot (Finset.mem_filter.mpr ⟨hi, rfl⟩))
  have he : V i = 0 := hu.symm.trans hz
  have hp := (mul_eq_zero.mp he).resolve_right hFi
  exact hPi (MvPolynomial.coe_eq_zero_iff.mp hp)

end General

end
end FrenkelReshetikhin.D4CounterexampleProof.PolynomialFock
