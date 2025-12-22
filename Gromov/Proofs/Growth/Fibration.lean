/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Level sets and fibration structure for group homomorphisms to Z.

This file develops the fibration structure arising from a surjective homomorphism
phi : G -> Z. The key insight is that the level sets phi^{-1}({k}) partition G
into cosets of ker(phi), and elements of the Cayley ball B_S(n) can only reach
a bounded number of these level sets (proportional to n).

This structure is fundamental to the descent argument: by understanding how
the Cayley ball fibers over Z, we can bound the growth of ker(phi) in terms
of the growth of G.

## Main Definitions

* `levelSet phi k` - The preimage phi^{-1}({k}) = {g : G | phi(g) = k}
* `height phi g` - The absolute value |phi(g)|, measuring distance from ker(phi)

## Main Results

* `levelSets_partition` - Level sets are pairwise disjoint and cover G
* `levelSet_eq_coset` - Each level set is a coset of ker(phi)
* `height_bound_in_ball` - Elements in B_S(n) have bounded height
* `ball_intersects_bounded_levels` - B_S(n) intersects O(n) level sets

## References

* Milnor, J. "Growth of Finitely Generated Solvable Groups" (1968)
* Wolf, J.A. "Growth of Finitely Generated Solvable Groups and Curvature of Riemannian Manifolds" (1968)
* Tao-Shalom "A finitary version of Gromov's polynomial growth theorem" Section 5
-/

import Gromov.Definitions.Descent
import Gromov.Proofs.Cayley.Graph

namespace Gromov.Growth.Fibration

open Gromov

/-!
## Level Sets

For a group homomorphism phi : G -> Multiplicative Z, the level set at k in Z is the
preimage of {ofAdd(k)}, i.e., all elements g with phi(g) = ofAdd(k).
-/

section LevelSets

variable {G : Type*} [Group G]

/-- The level set of phi at integer k: elements g with phi(g) = ofAdd(k). -/
def levelSet (φ : G →* Multiplicative ℤ) (k : ℤ) : Set G :=
  {g : G | φ g = Multiplicative.ofAdd k}

/-- The height of an element g under phi is the absolute value of its image.
    This measures "how far" g is from the kernel ker(phi). -/
def height (φ : G →* Multiplicative ℤ) (g : G) : ℤ :=
  |Multiplicative.toAdd (φ g)|

/-!
### Basic Properties of Level Sets
-/

/-- The identity element is in level set 0. -/
theorem one_mem_levelSet_zero (φ : G →* Multiplicative ℤ) :
    (1 : G) ∈ levelSet φ 0 := by
  -- Proof: phi(1) = 1 = ofAdd(0)
  simp [levelSet, map_one]

/-- Level sets are pairwise disjoint. -/
theorem levelSet_disjoint (φ : G →* Multiplicative ℤ) {k₁ k₂ : ℤ} (hne : k₁ ≠ k₂) :
    Disjoint (levelSet φ k₁) (levelSet φ k₂) := by
  -- Proof: If g is in both level sets, then ofAdd(k1) = phi(g) = ofAdd(k2),
  -- which implies k1 = k2, contradiction.
  sorry

/-- Every element belongs to exactly one level set. -/
theorem mem_levelSet_unique (φ : G →* Multiplicative ℤ) (g : G) :
    ∃! k : ℤ, g ∈ levelSet φ k := by
  -- Proof: g belongs to levelSet phi (toAdd(phi(g))), and by disjointness this is unique.
  sorry

/-- Level sets cover G. -/
theorem levelSets_cover (φ : G →* Multiplicative ℤ) :
    ∀ g : G, ∃ k : ℤ, g ∈ levelSet φ k := by
  -- Proof: Take k = toAdd(phi(g)).
  sorry

/-- Combined: level sets partition G. -/
theorem levelSets_partition (φ : G →* Multiplicative ℤ) :
    (∀ g : G, ∃! k : ℤ, g ∈ levelSet φ k) ∧
    (∀ k₁ k₂ : ℤ, k₁ ≠ k₂ → Disjoint (levelSet φ k₁) (levelSet φ k₂)) := by
  -- Proof: Combine mem_levelSet_unique and levelSet_disjoint.
  constructor
  · exact mem_levelSet_unique φ
  · exact fun k₁ k₂ hne => levelSet_disjoint φ hne

/-!
### Level Sets as Cosets

Each level set is a coset of the kernel.
-/

/-- Level set 0 is exactly the kernel. -/
theorem levelSet_zero_eq_ker (φ : G →* Multiplicative ℤ) :
    levelSet φ 0 = φ.ker := by
  -- Proof: g in levelSet phi 0 iff phi(g) = ofAdd(0) = 1 iff g in ker(phi).
  sorry

/-- Each nonempty level set is a coset of the kernel.
    If g is in levelSet phi k, then levelSet phi k = g * ker(phi). -/
theorem levelSet_eq_coset (φ : G →* Multiplicative ℤ) (k : ℤ) (g : G)
    (hg : g ∈ levelSet φ k) :
    levelSet φ k = {h : G | ∃ x ∈ φ.ker, h = g * x} := by
  -- Proof: h in levelSet phi k iff phi(h) = ofAdd(k) = phi(g)
  -- iff phi(g^{-1} * h) = 1 iff g^{-1} * h in ker(phi)
  -- iff h = g * x for some x in ker(phi).
  sorry

/-- Alternative formulation: level set as left coset. -/
theorem levelSet_eq_leftCoset (φ : G →* Multiplicative ℤ) (k : ℤ) (g : G)
    (hg : g ∈ levelSet φ k) :
    levelSet φ k = (fun x : φ.ker => g * x.val) '' Set.univ := by
  -- Proof: Direct from levelSet_eq_coset using the left coset.
  sorry

/-- If phi is surjective, every level set is nonempty. -/
theorem levelSet_nonempty (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ) (k : ℤ) :
    (levelSet φ k).Nonempty := by
  -- Proof: By surjectivity, there exists g with phi(g) = ofAdd(k).
  sorry

end LevelSets

/-!
## Height Bounds

Elements in the Cayley ball B_S(n) have bounded height under any homomorphism phi : G -> Z.
The bound depends on the maximum absolute image of generators in S.
-/

section HeightBounds

variable {G : Type*} [Group G]

/-- For a finite generating set, there exists a uniform bound on generator heights. -/
theorem exists_maxGeneratorHeight (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite) :
    ∃ M : ℤ, ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M := by
  -- Proof: Finite set has a maximum.
  sorry

/-- Height is multiplicative: height(g1 * g2) <= height(g1) + height(g2) via triangle inequality
    for the underlying additive values. -/
theorem height_mul_le (φ : G →* Multiplicative ℤ) (g₁ g₂ : G) :
    height φ (g₁ * g₂) ≤ height φ g₁ + height φ g₂ := by
  -- Proof: |a + b| <= |a| + |b| where a = toAdd(phi(g1)), b = toAdd(phi(g2)).
  sorry

/-- Height of inverse equals height. -/
theorem height_inv (φ : G →* Multiplicative ℤ) (g : G) :
    height φ g⁻¹ = height φ g := by
  -- Proof: |-(a)| = |a| where a = toAdd(phi(g)).
  sorry

/-- Main height bound: elements in B_S(n) have height at most M * n,
    where M is the maximum generator height. -/
theorem height_bound_in_ball (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite) (n : ℕ)
    (M : ℤ) (hM : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hM' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) (g : G) (hg : g ∈ CayleyBall S n) :
    height φ g ≤ M * n := by
  /-
  PROOF SKETCH:
  g in B_S(n) means g = s_1 * s_2 * ... * s_k where k <= n and each s_i or s_i^{-1} in S.

  By the triangle inequality for height:
    height(g) = height(s_1 * ... * s_k)
              <= height(s_1) + height(s_2 * ... * s_k)
              <= height(s_1) + height(s_2) + ... + height(s_k)
              <= k * M
              <= n * M

  since height(s_i) <= M for each generator (by assumption).
  -/
  sorry

/-- Corollary: elements in B_S(n) have bounded image under phi. -/
theorem phi_bound_in_ball (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite) (n : ℕ)
    (M : ℤ) (hM : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hM' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) (g : G) (hg : g ∈ CayleyBall S n) :
    |Multiplicative.toAdd (φ g)| ≤ M * n := by
  -- Proof: This is exactly height_bound_in_ball by definition of height.
  sorry

end HeightBounds

/-!
## Ball-Level Set Intersection

The Cayley ball B_S(n) intersects a bounded number of level sets.
-/

section BallIntersection

variable {G : Type*} [Group G]

/-- The set of integers k such that levelSet phi k intersects B_S(n). -/
def intersectedLevels (φ : G →* Multiplicative ℤ) (S : Set G) (n : ℕ) : Set ℤ :=
  {k : ℤ | (levelSet φ k ∩ CayleyBall S n).Nonempty}

/-- B_S(n) intersects at most 2*M*n + 1 level sets. -/
theorem ball_intersects_bounded_levels (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite)
    (n : ℕ) (M : ℤ) (hM : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hM' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) :
    intersectedLevels φ S n ⊆ Set.Icc (-M * n) (M * n) := by
  /-
  PROOF SKETCH:
  If k in intersectedLevels phi S n, then there exists g in B_S(n) with phi(g) = ofAdd(k).
  By height_bound_in_ball, |k| = height(g) <= M * n.
  Thus k in [-M*n, M*n].
  -/
  sorry

/-- The number of level sets intersected is O(n). -/
theorem intersectedLevels_card_bound (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite)
    (n : ℕ) (M : ℕ) (hM : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hM' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) :
    (intersectedLevels φ S n).ncard ≤ 2 * M * n + 1 := by
  -- Proof: intersectedLevels phi S n is contained in Icc(-M*n, M*n),
  -- which has cardinality 2*M*n + 1.
  sorry

end BallIntersection

/-!
## Coset Intersection Bounds

Bounds on how many elements of B_S(n) lie in each level set (coset of ker(phi)).
-/

section CosetIntersection

variable {G : Type*} [Group G]

/-- The intersection of B_S(n) with a level set can be bounded in terms of a ball in the kernel.
    This is the key estimate for proving growth degree decreases. -/
theorem coset_intersection_bound (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite)
    (k : ℤ) (n : ℕ) :
    ∃ (S_K : Set φ.ker) (C : ℕ),
      S_K.Finite ∧
      (levelSet φ k ∩ CayleyBall S n).ncard ≤ (CayleyBall S_K (C * n)).ncard := by
  /-
  PROOF SKETCH:
  The idea is that levelSet phi k is a coset g * ker(phi) for some g.
  If h in levelSet phi k ∩ B_S(n), then h = g * x for some x in ker(phi).
  We need to bound how "large" x can be in terms of n.

  Key insight: if h in B_S(n), then h = s_1 * ... * s_m with m <= n.
  Writing each s_i = c_i * t^{k_i} where c_i in ker(phi) and t is a lift of
  a generator of Z, we get x = g^{-1} * h as a product of c_i's and t-powers
  that sum to zero (since x in ker(phi)).

  The c_i's are bounded, so x lies in a ball of radius O(n) in ker(phi).

  This requires the kernel generation infrastructure from KernelDegree.lean.
  -/
  sorry

/-- Average level set size: by pigeonhole, at least one level set has
    size at most |B_S(n)| / (number of levels intersected). -/
theorem exists_small_level_intersection (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite)
    (n : ℕ) (hn : n > 0) (M : ℕ) (hM : M > 0) (hMbound : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hMbound' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) :
    ∃ k : ℤ, |k| ≤ M * n ∧
      (levelSet φ k ∩ CayleyBall S n).ncard ≤ (CayleyBall S n).ncard / (2 * M * n + 1) + 1 := by
  /-
  PROOF SKETCH:
  B_S(n) is the disjoint union of (levelSet phi k ∩ B_S(n)) for k in [-M*n, M*n].
  By pigeonhole, at least one such intersection has size at most
  |B_S(n)| / (2*M*n + 1).
  -/
  sorry

end CosetIntersection

end Gromov.Growth.Fibration
