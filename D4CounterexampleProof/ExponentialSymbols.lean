import D4CounterexampleProof.FirstMode
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.DFinsupp

/-!
Differential identities for the actual normally ordered formal exponentials
used by the original FR field definitions.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

open OriginalFR.Fields
open scoped BigOperators

local instance exponentialSymbolsCoefficientField : Field Coefficient := inferInstance
attribute [local instance] Classical.propDecidable

theorem modeTotal_add_single {g : SimpleLieType} (d : ModeMonomial g)
    (mode : ModeIndex g) :
    (d + Finsupp.single mode 1).sum (fun _ n => n) = d.sum (fun _ n => n) + 1 := by
  classical
  rw [Finsupp.sum_add_index' (by simp) (by simp)]
  simp

theorem modeTotal_eq_zero {g : SimpleLieType} (d : ModeMonomial g) :
    d.sum (fun _ n => n) = 0 ↔ d = 0 := by
  classical
  constructor
  · intro h
    ext mode
    by_cases hm : mode ∈ d.support
    · exact (Finset.sum_eq_zero_iff.mp h) mode hm
    · exact Finsupp.notMem_support_iff.mp hm
  · rintro rfl
    simp

theorem linearSymbol_pderiv (g : SimpleLieType) (c : ModeIndex g → Scalars)
    (mode : ModeIndex g) :
    MvPowerSeries.pderiv Scalars mode (linearSymbol g c) = MvPowerSeries.C (c mode) := by
  classical
  ext d
  rw [MvPowerSeries.coeff_pderiv]
  by_cases hd : d = 0
  · subst d
    simp [linearSymbol_single_coeff]
  · have htotal : d.sum (fun _ n => n) ≠ 0 := (modeTotal_eq_zero d).not.mpr hd
    have hne : (d + Finsupp.single mode 1).sum (fun _ n => n) ≠ 1 := by
      rw [modeTotal_add_single]
      omega
    rw [MvPowerSeries.coeff_apply, linearSymbol, if_neg hne]
    simp [MvPowerSeries.coeff_C, hd]

/-- Differentiating the full original formal exponential multiplies it by
the corresponding linear exponent coefficient. -/
theorem exponentialSymbol_pderiv (g : SimpleLieType) (c : ModeIndex g → Scalars)
    (mode : ModeIndex g) :
    MvPowerSeries.pderiv Scalars mode (exponentialSymbol g c) =
      MvPowerSeries.C (c mode) * exponentialSymbol g c := by
  classical
  ext d
  have hdplus : d + Finsupp.single mode 1 ≠ 0 := by
    intro h
    have hh := congrArg (fun x : ModeMonomial g => x mode) h
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at hh
    omega
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C_mul]
  change (∑ k ∈ Finset.range ((d + Finsupp.single mode 1).sum (fun _ n => n) + 1),
      (k.factorial : Scalars)⁻¹ * MvPowerSeries.coeff (d + Finsupp.single mode 1)
        (linearSymbol g c ^ k)) * ((d mode : Scalars) + 1) =
    c mode * ∑ k ∈ Finset.range (d.sum (fun _ n => n) + 1),
      (k.factorial : Scalars)⁻¹ * MvPowerSeries.coeff d (linearSymbol g c ^ k)
  rw [modeTotal_add_single, Finset.sum_mul, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    MvPowerSeries.coeff_one, if_neg hdplus, mul_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hp := congrArg (MvPowerSeries.coeff d)
    (MvPowerSeries.pderiv_pow (i := mode) (linearSymbol g c) (k + 1))
  rw [MvPowerSeries.coeff_pderiv, linearSymbol_pderiv] at hp
  rw [show ((k + 1 : ℕ) : SymbolSeries g) =
    MvPowerSeries.C ((k + 1 : ℕ) : Scalars) by simp] at hp
  simp only [Nat.add_sub_cancel, mul_assoc,
    MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_mul_C] at hp
  rw [mul_assoc, hp]
  have hf : (k.factorial : Scalars) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hn : (k + 1 : Scalars) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The original exponential is characterized by its differential equations
and constant coefficient. -/
theorem exponentialSymbol_unique (g : SimpleLieType) (c : ModeIndex g → Scalars)
    (f : SymbolSeries g) (hconstant : MvPowerSeries.constantCoeff f = 1)
    (hderiv : ∀ mode, MvPowerSeries.pderiv Scalars mode f = MvPowerSeries.C (c mode) * f) :
    f = exponentialSymbol g c := by
  let e := exponentialSymbol g c
  have he : MvPowerSeries.constantCoeff e ≠ 0 := by simp [e, exponentialSymbol_constantCoeff]
  have hei : e * e⁻¹ = 1 := MvPowerSeries.mul_inv_cancel e he
  have hie : e⁻¹ * e = 1 := MvPowerSeries.inv_mul_cancel e he
  have hratio : f * e⁻¹ = 1 := by
    apply MvPowerSeries.pderiv.ext
    · intro mode
      rw [Derivation.leibniz, MvPowerSeries.pderiv_inv', hderiv,
        show MvPowerSeries.pderiv Scalars mode e = MvPowerSeries.C (c mode) * e from
          exponentialSymbol_pderiv g c mode, MvPowerSeries.pderiv_one]
      simp only [smul_eq_mul]
      calc
        _ = MvPowerSeries.C (c mode) * f * e⁻¹ * (1 - e * e⁻¹) := by ring
        _ = 0 := by rw [hei, sub_self, mul_zero]
    · simp [hconstant, MvPowerSeries.constantCoeff_inv, e, exponentialSymbol_constantCoeff]
  have h := congrArg (fun x : SymbolSeries g => x * e) hratio
  simpa only [mul_assoc, hie, mul_one, one_mul] using h

theorem exponentialSymbol_mul (g : SimpleLieType) (c d : ModeIndex g → Scalars) :
    exponentialSymbol g c * exponentialSymbol g d = exponentialSymbol g (c + d) := by
  apply exponentialSymbol_unique
  · simp [exponentialSymbol_constantCoeff]
  · intro mode
    rw [Derivation.leibniz, exponentialSymbol_pderiv, exponentialSymbol_pderiv]
    simp only [smul_eq_mul, Pi.add_apply, map_add]
    ring

def symbolDerivative (g : SimpleLieType) (mode : ModeIndex g) :
    Module.End Scalars (SymbolSeries g) :=
  (MvPowerSeries.pderiv Scalars mode).toLinearMap

theorem shifted_symbolDerivative_polynomial_exp (g : SimpleLieType)
    (c : ModeIndex g → Scalars) (mode : ModeIndex g)
    (P : MvPolynomial (ModeIndex g) Scalars) :
    (symbolDerivative g mode - c mode • (1 : Module.End Scalars (SymbolSeries g)))
      ((P : SymbolSeries g) * exponentialSymbol g c) =
        (MvPolynomial.pderiv mode P : SymbolSeries g) * exponentialSymbol g c := by
  change MvPowerSeries.pderiv Scalars mode ((P : SymbolSeries g) * exponentialSymbol g c) -
    c mode • ((P : SymbolSeries g) * exponentialSymbol g c) = _
  rw [Derivation.leibniz, MvPowerSeries.pderiv_coe, exponentialSymbol_pderiv]
  simp only [smul_eq_mul, MvPowerSeries.smul_eq_C_mul]
  ring

theorem shifted_symbolDerivative_pow_polynomial_exp (g : SimpleLieType)
    (c : ModeIndex g → Scalars) (mode : ModeIndex g)
    (P : MvPolynomial (ModeIndex g) Scalars) (n : ℕ) :
    ((symbolDerivative g mode - c mode • (1 : Module.End Scalars (SymbolSeries g))) ^ n)
      ((P : SymbolSeries g) * exponentialSymbol g c) =
        ((MvPolynomial.pderiv mode)^[n] P : SymbolSeries g) * exponentialSymbol g c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, shifted_symbolDerivative_polynomial_exp]
    rw [Function.iterate_succ_apply']

theorem iterate_pderiv_monomial (g : SimpleLieType) (mode : ModeIndex g)
    (d : ModeMonomial g) (a : Scalars) (n : ℕ) :
    (MvPolynomial.pderiv mode)^[n] (MvPolynomial.monomial d a) =
      MvPolynomial.monomial (d - Finsupp.single mode n)
        (a * ((d mode).descFactorial n : Scalars)) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial]
    have hd : d - Finsupp.single mode n - Finsupp.single mode 1 =
        d - Finsupp.single mode (n + 1) := by
      ext j
      by_cases hj : j = mode
      · subst j
        simp [Finsupp.tsub_apply, Nat.sub_sub]
      · simp [Finsupp.tsub_apply, hj]
    rw [hd, Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.descFactorial_succ,
      Nat.cast_mul]
    congr 1
    ring

theorem polynomial_exponential_mem_maxGenEigenspace (g : SimpleLieType)
    (c : ModeIndex g → Scalars) (mode : ModeIndex g)
    (P : MvPolynomial (ModeIndex g) Scalars) :
    (P : SymbolSeries g) * exponentialSymbol g c ∈
      (symbolDerivative g mode).maxGenEigenspace (c mode) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨d mode + 1, ?_⟩
    rw [shifted_symbolDerivative_pow_polynomial_exp, iterate_pderiv_monomial,
      Nat.descFactorial_of_lt (Nat.lt_succ_self (d mode))]
    simp
  | add P Q hP hQ =>
    simpa only [MvPolynomial.coe_add, add_mul] using
      ((symbolDerivative g mode).maxGenEigenspace (c mode)).add_mem hP hQ

theorem symbolDerivative_commute (g : SimpleLieType) (i j : ModeIndex g) :
    Commute (symbolDerivative g i) (symbolDerivative g j) := by
  apply LinearMap.ext
  intro f
  change MvPowerSeries.pderiv Scalars i (MvPowerSeries.pderiv Scalars j f) =
    MvPowerSeries.pderiv Scalars j (MvPowerSeries.pderiv Scalars i f)
  classical
  ext d
  simp only [MvPowerSeries.coeff_pderiv]
  rw [add_right_comm d (Finsupp.single i 1) (Finsupp.single j 1)]
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij,
      Finsupp.single_eq_of_ne (Ne.symm hij), add_zero]
    ring

/-- The actual FR formal exponentials are independent even when multiplied
by arbitrary polynomials in finitely many mode variables. -/
theorem exponentialSymbol_polynomial_sum_eq_zero (g : SimpleLieType)
    {ι : Type*} (s : Finset ι) (c : ι → ModeIndex g → Scalars)
    (hc : Function.Injective c) (P : ι → MvPolynomial (ModeIndex g) Scalars)
    (hsum : ∑ i ∈ s, (P i : SymbolSeries g) * exponentialSymbol g (c i) = 0) :
    ∀ i ∈ s, P i = 0 := by
  have hind : iSupIndep (fun c : ModeIndex g → Scalars =>
      ⨅ mode, (symbolDerivative g mode).maxGenEigenspace (c mode)) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
      (symbolDerivative g) (fun i j a =>
        Module.End.mapsTo_maxGenEigenspace_of_comm (symbolDerivative_commute g j i) a)
  have hind' := hind.comp hc
  have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind' s
    (fun i => (P i : SymbolSeries g) * exponentialSymbol g (c i))
    (fun i _ => (Submodule.mem_iInf _).mpr fun mode =>
      polynomial_exponential_mem_maxGenEigenspace g (c i) mode (P i)) hsum
  intro i hi
  have he : exponentialSymbol g (c i) ≠ 0 := by
    intro h
    have hh := congrArg MvPowerSeries.constantCoeff h
    simp [exponentialSymbol_constantCoeff] at hh
  have hp := (mul_eq_zero.mp (hz i hi)).resolve_right he
  exact MvPolynomial.coe_eq_zero_iff.mp hp

/-- After grouping repeated exponent vectors, every polynomial coefficient
of a zero exponential sum vanishes separately. -/
theorem exponentialSymbol_grouped_sum_eq_zero (g : SimpleLieType)
    {ι : Type*} (s : Finset ι) (c : ι → ModeIndex g → Scalars)
    (P : ι → MvPolynomial (ModeIndex g) Scalars)
    (hsum : ∑ i ∈ s, (P i : SymbolSeries g) * exponentialSymbol g (c i) = 0) :
    ∀ a ∈ s.image c, ∑ i ∈ s.filter (fun i => c i = a), P i = 0 := by
  classical
  have hcoe (t : Finset ι) :
      ((∑ i ∈ t, P i : MvPolynomial (ModeIndex g) Scalars) : SymbolSeries g) =
        ∑ i ∈ t, (P i : SymbolSeries g) :=
    map_sum MvPolynomial.coeToMvPowerSeries.ringHom P t
  have hgroup : ∑ a ∈ s.image c,
      ((∑ i ∈ s.filter (fun i => c i = a), P i : MvPolynomial (ModeIndex g) Scalars) :
        SymbolSeries g) * exponentialSymbol g a = 0 := by
    calc
      _ = ∑ a ∈ s.image c, ∑ i ∈ s.filter (fun i => c i = a),
          (P i : SymbolSeries g) * exponentialSymbol g (c i) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hcoe, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = ∑ i ∈ s, (P i : SymbolSeries g) * exponentialSymbol g (c i) :=
        Finset.sum_fiberwise_of_maps_to
          (fun i hi => Finset.mem_image_of_mem c hi) _
      _ = 0 := hsum
  exact exponentialSymbol_polynomial_sum_eq_zero g (s.image c) id Function.injective_id
    (fun a => ∑ i ∈ s.filter (fun i => c i = a), P i) hgroup

/-- A nonzero contribution to a vanishing sum must have another nonzero
contribution with exactly the same exponent vector. This allows repeated
vectors and polynomial factors of arbitrary degree. -/
theorem exponentialSymbol_cancelling_partner (g : SimpleLieType)
    {ι : Type*} (s : Finset ι) (c : ι → ModeIndex g → Scalars)
    (P : ι → MvPolynomial (ModeIndex g) Scalars)
    (hsum : ∑ i ∈ s, (P i : SymbolSeries g) * exponentialSymbol g (c i) = 0)
    (i : ι) (hi : i ∈ s) (hPi : P i ≠ 0) :
    ∃ j ∈ s, j ≠ i ∧ c j = c i ∧ P j ≠ 0 := by
  classical
  by_contra hnone
  have hz := exponentialSymbol_grouped_sum_eq_zero g s c P hsum (c i)
    (Finset.mem_image_of_mem c hi)
  have hsum_i : ∑ j ∈ s.filter (fun j => c j = c i), P j = P i := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      by_contra hPj
      exact hnone ⟨j, (Finset.mem_filter.mp hj).1, hji,
        (Finset.mem_filter.mp hj).2, hPj⟩
    · intro hnot
      exact False.elim (hnot (Finset.mem_filter.mpr ⟨hi, rfl⟩))
  exact hPi (hsum_i.symm.trans hz)

end
end FrenkelReshetikhin.D4CounterexampleProof
