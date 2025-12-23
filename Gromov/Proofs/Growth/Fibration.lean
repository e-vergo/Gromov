module
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
import Mathlib.Data.Int.Interval

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
  rw [Set.disjoint_iff]
  intro g ⟨h1, h2⟩
  simp only [levelSet, Set.mem_setOf_eq] at h1 h2
  rw [h1] at h2
  exact hne (Multiplicative.ofAdd.injective h2)

/-- Every element belongs to exactly one level set. -/
theorem mem_levelSet_unique (φ : G →* Multiplicative ℤ) (g : G) :
    ∃! k : ℤ, g ∈ levelSet φ k := by
  use Multiplicative.toAdd (φ g)
  constructor
  · simp [levelSet]
  · intro k hk
    simp only [levelSet, Set.mem_setOf_eq] at hk
    exact Multiplicative.toAdd.injective (hk.symm)

/-- Level sets cover G. -/
theorem levelSets_cover (φ : G →* Multiplicative ℤ) :
    ∀ g : G, ∃ k : ℤ, g ∈ levelSet φ k := by
  intro g
  use Multiplicative.toAdd (φ g)
  simp [levelSet]

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
  ext g
  simp only [levelSet, Set.mem_setOf_eq]
  rfl

/-- Each nonempty level set is a coset of the kernel.
    If g is in levelSet phi k, then levelSet phi k = g * ker(phi). -/
theorem levelSet_eq_coset (φ : G →* Multiplicative ℤ) (k : ℤ) (g : G)
    (hg : g ∈ levelSet φ k) :
    levelSet φ k = {h : G | ∃ x ∈ φ.ker, h = g * x} := by
  ext h
  simp only [levelSet, Set.mem_setOf_eq, MonoidHom.mem_ker]
  constructor
  · intro hh
    use g⁻¹ * h
    constructor
    · simp only [levelSet, Set.mem_setOf_eq] at hg
      rw [map_mul, map_inv, hg, hh]
      simp
    · group
  · rintro ⟨x, hx, rfl⟩
    simp only [levelSet, Set.mem_setOf_eq] at hg
    rw [map_mul, hx, mul_one, hg]

/-- Alternative formulation: level set as left coset. -/
theorem levelSet_eq_leftCoset (φ : G →* Multiplicative ℤ) (k : ℤ) (g : G)
    (hg : g ∈ levelSet φ k) :
    levelSet φ k = (fun x : φ.ker => g * x.val) '' Set.univ := by
  rw [levelSet_eq_coset φ k g hg]
  ext h
  simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- If phi is surjective, every level set is nonempty. -/
theorem levelSet_nonempty (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ) (k : ℤ) :
    (levelSet φ k).Nonempty := by
  obtain ⟨g, hg⟩ := hφ (Multiplicative.ofAdd k)
  exact ⟨g, hg⟩

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
  by_cases hS' : S.Nonempty
  · obtain ⟨M, hM⟩ := hS.image (fun s => |Multiplicative.toAdd (φ s)|) |>.bddAbove
    exact ⟨M, fun s hs => hM ⟨s, hs, rfl⟩⟩
  · use 0
    intro s hs
    exfalso
    exact hS' ⟨s, hs⟩

/-- Height is multiplicative: height(g1 * g2) <= height(g1) + height(g2) via triangle inequality
    for the underlying additive values. -/
theorem height_mul_le (φ : G →* Multiplicative ℤ) (g₁ g₂ : G) :
    height φ (g₁ * g₂) ≤ height φ g₁ + height φ g₂ := by
  unfold height
  simp only [map_mul, toAdd_mul]
  exact abs_add_le _ _

/-- Height of inverse equals height. -/
theorem height_inv (φ : G →* Multiplicative ℤ) (g : G) :
    height φ g⁻¹ = height φ g := by
  simp only [height, map_inv, toAdd_inv]
  exact abs_neg _

/-- Main height bound: elements in B_S(n) have height at most M * n,
    where M is the maximum generator height. -/
theorem height_bound_in_ball (φ : G →* Multiplicative ℤ) (S : Set G)
    (hS : S.Finite) (n : ℕ)
    (M : ℤ) (hM_nonneg : 0 ≤ M) (hM : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hM' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) (g : G) (hg : g ∈ CayleyBall S n) :
    height φ g ≤ M * n := by
  simp only [CayleyBall, Set.mem_setOf_eq] at hg
  obtain ⟨l, hlen, hl_gen, hprod⟩ := hg
  subst hprod
  induction l generalizing n with
  | nil =>
    simp only [height, List.prod_nil, map_one, toAdd_one, abs_zero]
    -- Need 0 ≤ M * n. Since n ≥ 0, this follows if M ≥ 0.
    by_cases hS' : S.Nonempty
    · obtain ⟨s, hs⟩ := hS'
      have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hM s hs)
      exact mul_nonneg hM_nonneg (Nat.cast_nonneg _)
    · -- S is empty, but this is fine since height 0 * anything ≥ 0 when heights are involved
      -- For empty S, the bound M is arbitrary. But 0 ≤ M * n could be false if M < 0 and n > 0.
      -- However, looking at how this theorem is used, M comes from exists_maxGeneratorHeight
      -- which always gives M ≥ 0 (for nonempty S) or M = 0 (for empty S).
      -- For empty S with M < 0, the hypotheses are vacuously true but conclusion may fail.
      -- This is a limitation in the theorem statement. We'll need M ≥ 0 as an assumption.
      -- For now, assume the typical use case where M comes from exists_maxGeneratorHeight.
      simp only [Set.not_nonempty_iff_eq_empty] at hS'
      -- With S empty, any reasonable M from the problem setup would be ≥ 0.
      -- We use omega/positivity if possible, otherwise note this edge case.
      by_cases hn : n = 0
      · simp [hn]
      · -- For n > 0 and S empty, use the explicit M ≥ 0 hypothesis.
        exact mul_nonneg hM_nonneg (Nat.cast_nonneg _)
  | cons s t ih =>
    simp only [List.length_cons] at hlen
    simp only [List.mem_cons, forall_eq_or_imp] at hl_gen
    obtain ⟨hs_gen, ht_gen⟩ := hl_gen
    simp only [List.prod_cons]
    -- s is a generator (in S or its inverse is in S), so we can extract M ≥ 0
    have hM_nonneg : 0 ≤ M := by
      cases hs_gen with
      | inl hs => exact le_trans (abs_nonneg _) (hM s hs)
      | inr hs => exact le_trans (abs_nonneg _) (hM s⁻¹ hs)
    have ht_len : t.length ≤ n := Nat.le_of_succ_le hlen
    have ih_bound : height φ t.prod ≤ M * ↑t.length := ih t.length (le_refl _) ht_gen
    have hs_bound : height φ s ≤ M := by
      cases hs_gen with
      | inl hs => exact hM s hs
      | inr hs =>
        -- s⁻¹ ∈ S, and we need to show height φ s ≤ M
        -- Use hM on s⁻¹ directly (since s⁻¹ ∈ S)
        have h1 : |Multiplicative.toAdd (φ s⁻¹)| ≤ M := hM s⁻¹ hs
        simp only [map_inv, toAdd_inv, abs_neg] at h1
        exact h1
    calc height φ (s * t.prod)
        ≤ height φ s + height φ t.prod := height_mul_le φ s t.prod
      _ ≤ M + M * ↑t.length := add_le_add hs_bound ih_bound
      _ = M * (1 + ↑t.length) := by ring
      _ ≤ M * ↑n := by
          have h1 : (1 : ℤ) + ↑t.length ≤ ↑n := by omega
          exact mul_le_mul_of_nonneg_left h1 hM_nonneg

/-- Corollary: elements in B_S(n) have bounded image under phi. -/
theorem phi_bound_in_ball (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite) (n : ℕ)
    (M : ℤ) (hM_nonneg : 0 ≤ M) (hM : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hM' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) (g : G) (hg : g ∈ CayleyBall S n) :
    |Multiplicative.toAdd (φ g)| ≤ M * n := by
  -- Proof: This is exactly height_bound_in_ball by definition of height.
  exact height_bound_in_ball φ S hS n M hM_nonneg hM hM' g hg

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
    (n : ℕ) (M : ℤ) (hM_nonneg : 0 ≤ M) (hM : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hM' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) :
    intersectedLevels φ S n ⊆ Set.Icc (-M * n) (M * n) := by
  intro k hk
  simp only [intersectedLevels, Set.mem_setOf_eq, levelSet, Set.Nonempty, Set.mem_inter_iff] at hk
  obtain ⟨g, hg_level, hg_ball⟩ := hk
  simp only [Set.mem_Icc]
  have hbound := phi_bound_in_ball φ S hS n M hM_nonneg hM hM' g hg_ball
  rw [hg_level, toAdd_ofAdd] at hbound
  constructor <;> linarith [abs_le.mp hbound]

/-- The number of level sets intersected is O(n). -/
theorem intersectedLevels_card_bound (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite)
    (n : ℕ) (M : ℕ) (hM : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hM' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) :
    (intersectedLevels φ S n).ncard ≤ 2 * M * n + 1 := by
  have hM_int : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ (M : ℤ) := fun s hs => by
    exact_mod_cast hM s hs
  have hM'_int : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ (M : ℤ) := fun s hs => by
    exact_mod_cast hM' s hs
  have hM_nonneg : 0 ≤ (M : ℤ) := Nat.cast_nonneg M
  have hsub := ball_intersects_bounded_levels φ S hS n (M : ℤ) hM_nonneg hM_int hM'_int
  calc (intersectedLevels φ S n).ncard
      ≤ (Set.Icc (-(M : ℤ) * n) ((M : ℤ) * n)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (Finset.Icc (-(M : ℤ) * n) ((M : ℤ) * n)).card := by
        rw [Set.ncard_eq_toFinset_card']
        rw [Set.toFinset_Icc]
    _ = ((M : ℤ) * n + 1 - (-(M : ℤ) * n)).toNat := Int.card_Icc _ _
    _ = (2 * (M : ℤ) * n + 1).toNat := by ring_nf
    _ = 2 * M * n + 1 := by
        have h1 : 2 * (M : ℤ) * n + 1 = ↑(2 * M * n + 1) := by norm_cast
        rw [h1, Int.toNat_natCast]

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
  sorry

/-- Average level set size: by pigeonhole, at least one level set has
    size at most |B_S(n)| / (number of levels intersected). -/
theorem exists_small_level_intersection (φ : G →* Multiplicative ℤ) (S : Set G) (hS : S.Finite)
    (n : ℕ) (hn : n > 0) (M : ℕ) (hM : M > 0) (hMbound : ∀ s ∈ S, |Multiplicative.toAdd (φ s)| ≤ M)
    (hMbound' : ∀ s ∈ S, |Multiplicative.toAdd (φ s⁻¹)| ≤ M) :
    ∃ k : ℤ, |k| ≤ M * n ∧
      (levelSet φ k ∩ CayleyBall S n).ncard ≤ (CayleyBall S n).ncard / (2 * M * n + 1) + 1 := by
  sorry

end CosetIntersection

end Gromov.Growth.Fibration
