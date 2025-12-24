/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Growth degree decrease for kernels (descent argument core).

This file contains the key technical results for the descent argument in
Gromov's theorem. The main result is that when G has polynomial growth of
degree d and φ : G → ℤ is surjective, the kernel ker(φ) has polynomial
growth of degree at most d - 1.

## Main results

* `kernel_ball_size_bound` - |B_K(n)| ≤ C|B_G(Cn)|
* `kernel_growth_over_n` - |B_K(n)| ≤ C|B_G(Cn)|/n
* `kernel_degree_decrease_main` - Growth degree d implies kernel degree ≤ d-1

## References

* Gromov, "Groups of polynomial growth" (1981)
* Kleiner, "A new proof of Gromov's theorem" (2010)
-/

module

public import Gromov.Proofs.Growth.KernelDegree
public import Gromov.Proofs.Schreier.KernelGeneration
public import Gromov.Proofs.Growth.DoublingProperty
public import Gromov.Proofs.Growth.Fibration

namespace Gromov.Growth.KernelGrowth

public section

open Gromov Filter Set Subgroup Gromov.Schreier.KernelGeneration
open scoped Pointwise NNReal

variable {G : Type*} [Group G] [DecidableEq G]

/-! ## Level Set Analysis -/

section LevelSets

variable (S : Set G) [Fintype S] (φ : G →* ℤ) (hφ : Function.Surjective φ)

/-- Level set of φ: all elements with a given φ-value. -/
def levelSet (k : ℤ) : Set G :=
  { g : G | φ g = k }

/-- Level sets partition G. -/
theorem levelSet_partition : ∀ g : G, ∃! k : ℤ, g ∈ levelSet φ k := by
  intro g
  exact ⟨φ g, rfl, fun k hk => hk.symm⟩

/-- Level set intersection with a ball: elements in the ball with given φ-value. -/
def levelSetIntersection (k : ℤ) (n : ℕ) : Set G :=
  levelSet φ k ∩ CayleyBall S n

/-- Bound on level set intersections: each level has at most |B_K(Cn)| elements. -/
theorem levelSet_intersection_bound (t : G) (ht : φ t = 1) (k : ℤ) (n : ℕ) :
    (levelSetIntersection S φ k n).ncard ≤
      (CayleyBall (kernelGenerators φ (S : Set G) t)
        (n * (1 + 2 * generatorPhiBound S φ))).ncard := by
  sorry

/-- Kernel ball equals level 0 intersection. -/
theorem kernel_ball_eq_levelSet_zero_intersection (n : ℕ) :
    CayleyBall S n ∩ MonoidHom.ker φ = levelSetIntersection S φ 0 n := by
  sorry

end LevelSets

/-! ## Slicing Argument -/

section SlicingArgument

variable (S : Set G) [Fintype S] (φ : G →* ℤ) (hφ : Function.Surjective φ)

/-- The ball decomposes as disjoint union of level set intersections. -/
theorem slicing_sum (n : ℕ) (M : ℕ) (hM : ∀ g ∈ CayleyBall S n, (φ g).natAbs ≤ M) :
    (CayleyBall S n).ncard = ∑ k ∈ Finset.Icc (-M : ℤ) M, (levelSetIntersection S φ k n).ncard := by
  sorry

/-- Pigeonhole: the average level set intersection has size |B_G(n)|/(2M+1). -/
theorem average_slice_bound (n : ℕ) (M : ℕ) (hM : M > 0)
    (hM_bound : ∀ g ∈ CayleyBall S n, (φ g).natAbs ≤ M) :
    ∃ k : ℤ, (levelSetIntersection S φ k n).ncard * (2 * M + 1) ≥ (CayleyBall S n).ncard := by
  sorry

/-- Key bound: |B_K(n)| × (number of levels) ≤ C|B_G(Cn)|. -/
theorem kernel_times_levels_le_group (t : G) (ht : φ t = 1) (n : ℕ) (hn : n > 0) :
    let C := 1 + 2 * generatorPhiBound S φ
    (CayleyBall (kernelGenerators φ (S : Set G) t) n).ncard * n ≤
      (CayleyBall S (C * n)).ncard := by
  sorry

end SlicingArgument

/-! ## Main Growth Bounds -/

section MainBounds

variable (S : Set G) [Fintype S] (φ : G →* ℤ) (hφ : Function.Surjective φ)

/-- Kernel ball embeds into parent ball with linear scaling. -/
theorem kernel_ball_subset_parent_ball (t : G) (ht : φ t = 1) (n : ℕ) :
    let C := 1 + 2 * generatorPhiBound S φ
    CayleyBall (kernelGenerators φ (S : Set G) t) n ⊆
      CayleyBall S (C * n) ∩ MonoidHom.ker φ := by
  sorry

/-- Kernel ball size bound. -/
theorem kernel_ball_size_bound (t : G) (ht : φ t = 1) (n : ℕ) :
    let C := 1 + 2 * generatorPhiBound S φ
    (CayleyBall (kernelGenerators φ (S : Set G) t) n).ncard ≤
      (CayleyBall S (C * n)).ncard := by
  sorry

/-- The crucial asymptotic bound: |B_K(n)| ≤ C|B_G(Cn)|/n. -/
theorem kernel_growth_over_n (t : G) (ht : φ t = 1) (n : ℕ) (hn : n > 0) :
    let C := 1 + 2 * generatorPhiBound S φ
    ∃ C' : ℝ, C' > 0 ∧
      ((CayleyBall (kernelGenerators φ (S : Set G) t) n).ncard : ℝ) ≤
        C' * (CayleyBall S (C * n)).ncard / n := by
  sorry

end MainBounds

/-! ## Degree Decrease Theorem -/

section DegreeDecrease

variable (S : Set G) [Fintype S] (φ : G →* ℤ) (hφ : Function.Surjective φ)

/-- Main theorem: if G has polynomial growth of degree d, then ker(φ) has
    polynomial growth of degree at most d - 1.

    This is the heart of the descent argument. -/
theorem kernel_degree_decrease_main (d : ℕ) (hd : d > 0)
    (hd_bound : IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) d)
    (hd_sharp : ¬IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) (d - 1)) :
    let t := transversalGenerator φ hφ
    let K_gen := kernelGenerators φ (S : Set G) t
    IsPolynomiallyBounded (fun n => (CayleyBall K_gen n).ncard) (d - 1) := by
  sorry

/-- Consequence: if degree is 1 (linear growth), the kernel is finite. -/
theorem kernel_finite_of_linear_growth
    (hd_bound : IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) 1) :
    (MonoidHom.ker φ).Finite := by
  sorry

/-- After d iterations of taking kernels, we get a finite subgroup. -/
theorem iterated_kernel_finite (d : ℕ)
    (hd_bound : IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) d) :
    ∃ (H : Subgroup G), H.FiniteIndex ∧ H.carrier.Finite := by
  sorry

end DegreeDecrease

/-! ## Descent Termination -/

section DescentTermination

variable (S : Set G) [Fintype S]

/-- The descent argument terminates: we eventually reach a finite-index finite subgroup.
    This is the conclusion needed for Gromov's theorem. -/
theorem descent_terminates (hpoly : HasPolynomialGrowth G) :
    ∃ (H : Subgroup G), H.FiniteIndex ∧
      (H.carrier.Finite ∨ ∃ (K : Subgroup H), K.FiniteIndex ∧ IsNilpotent K) := by
  sorry

/-- Combined with virtual nilpotency: polynomial growth implies virtually nilpotent. -/
theorem polynomial_growth_virtually_nilpotent [Group.FG G] (hpoly : HasPolynomialGrowth G) :
    IsVirtuallyNilpotent G := by
  sorry

end DescentTermination

end

end Gromov.Growth.KernelGrowth
