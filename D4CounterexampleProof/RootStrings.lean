import StatementDefinitions

/-!
Finite root-string calculations in simple-root coordinates for D₄. The
listed twelve positive roots are the roots of the classical D₄ root system;
their role as the weights of the central quantum-affine fundamental module
remains a separate representation-theoretic statement.
-/

namespace FrenkelReshetikhin.D4CounterexampleProof

abbrev RootCoordinates := ℤ × ℤ × ℤ × ℤ

def positiveRoots : List RootCoordinates :=
  [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1),
   (1, 1, 0, 0), (0, 1, 1, 0), (0, 1, 0, 1),
   (1, 1, 1, 0), (1, 1, 0, 1), (0, 1, 1, 1),
   (1, 1, 1, 1), (1, 2, 1, 1)]

def roots : List RootCoordinates := positiveRoots ++ positiveRoots.map Neg.neg

theorem roots_length : roots.length = 24 := by decide
theorem roots_nodup : roots.Nodup := by decide
theorem negative_outer_root_once : roots.count (0, 0, 0, -1) = 1 := by decide

def outerLine (k : ℤ) : RootCoordinates := (0, 0, 0, 1 - k)

/-- Along α₄−kα₄, only α₄, 0, and −α₄ can be a root or zero. -/
theorem outer_root_string (k : ℤ)
    (h : outerLine k ∈ roots ∨ outerLine k = 0) :
    k = 0 ∨ k = 1 ∨ k = 2 := by
  simp [outerLine, roots, positiveRoots] at h
  omega

/-- Each of the four forced root strings has only its start and successor
among root or zero weights. These are the directions used to force M₁–M₄. -/
theorem first_forced_string (k : ℤ)
    (h : (1, 2 - k, 1, 1) ∈ roots ∨
      (1, 2 - k, 1, 1) = (0 : RootCoordinates)) :
    k = 0 ∨ k = 1 := by
  simp [roots, positiveRoots] at h
  omega

theorem second_forced_string (k : ℤ)
    (h : (1 - k, 1, 1, 1) ∈ roots ∨
      (1 - k, 1, 1, 1) = (0 : RootCoordinates)) :
    k = 0 ∨ k = 1 := by
  simp [roots, positiveRoots] at h
  omega

theorem third_forced_string (k : ℤ)
    (h : (0, 1, 1 - k, 1) ∈ roots ∨
      (0, 1, 1 - k, 1) = (0 : RootCoordinates)) :
    k = 0 ∨ k = 1 := by
  simp [roots, positiveRoots] at h
  omega

theorem fourth_forced_string (k : ℤ)
    (h : (0, 1 - k, 0, 1) ∈ roots ∨
      (0, 1 - k, 0, 1) = (0 : RootCoordinates)) :
    k = 0 ∨ k = 1 := by
  simp [roots, positiveRoots] at h
  omega

end FrenkelReshetikhin.D4CounterexampleProof
