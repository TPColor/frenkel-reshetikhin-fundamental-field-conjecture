import D4CounterexampleProof.MonomialCertificate

/-!
Combinatorial orders of finite poles in the rational screening OPE factors.
For a Laurent monomial, zeros and poles from inverse Y-factors are included
with their signed exponents. Identifying these orders with residues of the
original formal fields is proved separately in `ScreeningResidueBridge.lean`.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

noncomputable section

def minusPoleOrder (m : Monomial) (i : Fin 4) (c : Spectral) : ℤ :=
  m (i, (c.1 + 1, c.2)) - m (i, (c.1 - 1, c.2))

def plusPoleOrder (m : Monomial) (i : Fin 4) (c : Spectral) : ℤ :=
  m (i, (c.1, c.2 - 1)) - m (i, (c.1, c.2 + 1))

theorem first_minus_pole : minusPoleOrder M 3 (-2, 1) = 1 := by
  simp [minusPoleOrder, M, Y, Finsupp.add_apply, Finsupp.sub_apply]

theorem forcing_pole_0 : minusPoleOrder M₀ 1 (-1, 0) = 1 := by
  simp [minusPoleOrder, M₀, Y]

theorem forcing_pole_1 : minusPoleOrder M₁ 0 (-2, 1) = 1 := by
  simp [minusPoleOrder, M₁, Y, Finsupp.add_apply, Finsupp.sub_apply]

theorem forcing_pole_2 : minusPoleOrder M₂ 2 (-2, 1) = 1 := by
  simp [minusPoleOrder, M₂, Y, Finsupp.add_apply, Finsupp.sub_apply]

theorem forcing_pole_3 : minusPoleOrder M₃ 1 (-3, 2) = 1 := by
  simp [minusPoleOrder, M₃, Y, Finsupp.add_apply, Finsupp.sub_apply]

theorem first_plus_pole : plusPoleOrder M 3 (-1, 2) = 1 := by
  simp [plusPoleOrder, M, Y, Finsupp.add_apply, Finsupp.sub_apply]

theorem intermediate_has_no_minus_pole (c : Spectral) :
    minusPoleOrder Z 3 c = 0 := by
  simp [minusPoleOrder, Z, Y, Finsupp.sub_apply]

theorem intermediate_has_no_plus_pole (c : Spectral) :
    plusPoleOrder Z 3 c = 0 := by
  simp [plusPoleOrder, Z, Y, Finsupp.sub_apply]

theorem final_minus_pole : minusPoleOrder Nminus 3 (-2, 5) = 1 := by
  simp [minusPoleOrder, Nminus, Y, Finsupp.add_apply, Finsupp.sub_apply]

theorem final_plus_pole : plusPoleOrder Nplus 3 (-5, 2) = 1 := by
  simp [plusPoleOrder, Nplus, Y, Finsupp.add_apply, Finsupp.sub_apply]

theorem second_minus_pole : minusPoleOrder M 3 (-4, 3) = 1 := by
  simp [minusPoleOrder, M, Y, Finsupp.add_apply, Finsupp.sub_apply]

theorem second_intermediate_minus_pole : minusPoleOrder Zprime 3 (-2, 1) = 1 := by
  simp [minusPoleOrder, Zprime, Y, Finsupp.sub_apply]

end
end FrenkelReshetikhin.D4CounterexampleProof
