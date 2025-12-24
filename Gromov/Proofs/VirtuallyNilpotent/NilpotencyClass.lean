/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Virtual nilpotency class and examples.
-/

module

public import Gromov.Proofs.Polycyclic.ResiduallyFinite
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

/-!
# Virtual Nilpotency Class

This file defines and develops properties of the virtual nilpotency class,
and proves that free groups of rank at least 2 are not virtually nilpotent.

## Main results

* `Group.virtualNilpotencyClass_le_of_finiteIndex`: The virtual nilpotency class is bounded
  by the nilpotency class of any finite-index nilpotent subgroup.
* `Group.virtualNilpotencyClass_pos`: For infinite groups, the virtual nilpotency class is positive.
* `FreeGroup.not_isVirtuallyNilpotent`: Free groups of rank at least 2 are not virtually nilpotent.

## Examples

* Abelian groups are virtually nilpotent
* Finite groups are virtually nilpotent
* Free groups of rank at least 2 are NOT virtually nilpotent
-/

open Subgroup

namespace Group

public section

variable {G : Type*} [Group G]

/-! ### Virtual nilpotency class -/

/-- A finite-index subgroup of an infinite group is infinite. -/
theorem infinite_of_finiteIndex_of_infinite [Infinite G] (H : Subgroup G) [H.FiniteIndex] :
    Infinite H := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have : Finite G := @Finite.of_subgroup_quotient _ _ H _ _
  exact not_finite G

/-- A subgroup of a virtually nilpotent group is virtually nilpotent.
    Uses intersection with the nilpotent finite-index subgroup. -/
theorem isVirtuallyNilpotent_subgroup (H : Subgroup G) (hG : IsVirtuallyNilpotent G) :
    IsVirtuallyNilpotent H := by
  obtain ⟨K, hKNil, hKFin⟩ := hG
  -- K.subgroupOf H ≃ (H ⊓ K) as subgroups, and (H ⊓ K) is nilpotent
  haveI : K.FiniteIndex := hKFin
  haveI : IsNilpotent K := hKNil
  -- (H ⊓ K).subgroupOf K is a subgroup of K, hence nilpotent
  have hSubKNil : IsNilpotent ((H ⊓ K).subgroupOf K) := Subgroup.isNilpotent _
  -- Via the equivalence, (H ⊓ K) is nilpotent
  have hInfNil : IsNilpotent (H ⊓ K : Subgroup G) :=
    (isNilpotent_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right (a := H) (b := K)))).mp hSubKNil
  -- K.subgroupOf H = (H ⊓ K).subgroupOf H
  have heq : K.subgroupOf H = (H ⊓ K).subgroupOf H := by
    ext x
    simp only [mem_subgroupOf, mem_inf, and_iff_right x.prop]
  -- (H ⊓ K).subgroupOf H ≃ (H ⊓ K), so it's nilpotent
  haveI : IsNilpotent (H ⊓ K : Subgroup G) := hInfNil
  have hNilSub : IsNilpotent (K.subgroupOf H) := by
    rw [heq]
    have equiv := Subgroup.subgroupOfEquivOfLe (inf_le_left (a := H) (b := K))
    exact (isNilpotent_congr equiv).mpr hInfNil
  -- Finite index
  have hFinSub : (K.subgroupOf H).FiniteIndex := instFiniteIndex_subgroupOf K H
  exact ⟨K.subgroupOf H, hNilSub, hFinSub⟩

/-- A quotient of a virtually nilpotent group is virtually nilpotent.
    Uses image of the nilpotent finite-index subgroup. -/
theorem isVirtuallyNilpotent_quotient (N : Subgroup G) [N.Normal] (hG : IsVirtuallyNilpotent G) :
    IsVirtuallyNilpotent (G ⧸ N) := by
  obtain ⟨K, hKNil, hKFin⟩ := hG
  haveI : K.FiniteIndex := hKFin
  haveI : IsNilpotent K := hKNil
  -- The image of K in G/N
  let KQ := K.map (QuotientGroup.mk' N)
  -- KQ is nilpotent (image of nilpotent group under surjective homomorphism)
  have hKQNil : IsNilpotent KQ :=
    nilpotent_of_surjective ((QuotientGroup.mk' N).subgroupMap K)
      ((QuotientGroup.mk' N).subgroupMap_surjective K)
  -- KQ has finite index
  have hKQFin : KQ.FiniteIndex := by
    have hdvd : KQ.index ∣ K.index := Subgroup.index_map_dvd K QuotientGroup.mk_surjective
    constructor
    intro h0
    apply hKFin.index_ne_zero
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd)
  exact ⟨KQ, hKQNil, hKQFin⟩

/-- The virtual nilpotency class is at most the nilpotency class of any finite-index
nilpotent subgroup. -/
theorem virtualNilpotencyClass_le_of_finiteIndex
    (N : Subgroup G) [IsNilpotent N] [N.FiniteIndex] :
    virtualNilpotencyClass G ≤ nilpotencyClass (G := N) := by
  classical
  have hVN : IsVirtuallyNilpotent G := ⟨N, inferInstance, inferInstance⟩
  unfold virtualNilpotencyClass
  simp only [dif_pos hVN]
  apply Nat.find_le
  exact ⟨N, inferInstance, inferInstance, le_refl _⟩

/-- The virtual nilpotency class is positive for infinite virtually nilpotent groups.
Note: For finite nontrivial groups, the trivial subgroup has finite index and
nilpotencyClass 0, so virtualNilpotencyClass can be 0. -/
theorem virtualNilpotencyClass_pos [Infinite G] (hG : IsVirtuallyNilpotent G) :
    0 < virtualNilpotencyClass G := by
  classical
  unfold virtualNilpotencyClass
  simp only [dif_pos hG]
  -- Need to show Nat.find ... > 0, i.e., HasNilpotentSubgroupOfClassLE G 0 is false
  rw [Nat.find_pos]
  -- Show there's no finite-index nilpotent subgroup of class 0
  intro ⟨N, hNil, hFin, hClass⟩
  -- N has nilpotencyClass 0, so N is subsingleton
  haveI : N.FiniteIndex := hFin
  haveI : IsNilpotent N := hNil
  have hSub : Subsingleton N := nilpotencyClass_zero_iff_subsingleton.mp (Nat.le_zero.mp hClass)
  -- But N has finite index in an infinite group, so N is infinite
  haveI : Infinite N := infinite_of_finiteIndex_of_infinite N
  -- Contradiction: infinite and subsingleton
  haveI : Subsingleton N := hSub
  exact not_finite N

/-- The nilpotency class is preserved by group isomorphism. -/
theorem nilpotencyClass_eq_of_mulEquiv {H : Type*} [Group H]
    [hG : IsNilpotent G] [hH : IsNilpotent H] (e : G ≃* H) :
    @nilpotencyClass G _ hG = @nilpotencyClass H _ hH := by
  classical
  apply le_antisymm
  · have h1 := upperCentralSeries_nilpotencyClass (G := H)
    have h2 := comap_upperCentralSeries e (nilpotencyClass H)
    rw [h1] at h2
    simp only [Subgroup.comap_top] at h2
    apply Nat.find_le
    exact h2.symm
  · have h1 := upperCentralSeries_nilpotencyClass (G := G)
    have h2 := comap_upperCentralSeries e.symm (nilpotencyClass G)
    rw [h1] at h2
    simp only [Subgroup.comap_top] at h2
    apply Nat.find_le
    exact h2.symm

/-- The virtual nilpotency class of a subgroup is at most that of the ambient group. -/
theorem Subgroup.virtualNilpotencyClass_le (H : Subgroup G) (hG : IsVirtuallyNilpotent G) :
    virtualNilpotencyClass H ≤ virtualNilpotencyClass G := by
  classical
  -- For any finite-index nilpotent subgroup N of G with class c,
  -- N.subgroupOf H is a finite-index nilpotent subgroup of H with class ≤ c
  -- Hence virtualNilpotencyClass H ≤ c for all such c, so ≤ inf = virtualNilpotencyClass G
  unfold virtualNilpotencyClass
  simp only [dif_pos hG]
  have hHvn := isVirtuallyNilpotent_subgroup H hG
  simp only [dif_pos hHvn]
  apply Nat.find_mono
  intro n ⟨N, hNil, hFin, hClass⟩
  haveI : N.FiniteIndex := hFin
  haveI : IsNilpotent N := hNil
  -- Use the proof from isVirtuallyNilpotent_subgroup
  have hNilSub : IsNilpotent (N.subgroupOf H) := by
    have hSubNNil : IsNilpotent ((H ⊓ N).subgroupOf N) := Subgroup.isNilpotent _
    have hInfNil : IsNilpotent (H ⊓ N : Subgroup G) :=
      (isNilpotent_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right (a := H) (b := N)))).mp
        hSubNNil
    have heq : N.subgroupOf H = (H ⊓ N).subgroupOf H := by
      ext x
      simp only [mem_subgroupOf, mem_inf, and_iff_right x.prop]
    rw [heq]
    haveI : IsNilpotent (H ⊓ N : Subgroup G) := hInfNil
    exact (isNilpotent_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left (a := H) (b := N)))).mpr
      hInfNil
  have hFinSub : (N.subgroupOf H).FiniteIndex := instFiniteIndex_subgroupOf N H
  -- nilpotencyClass of N.subgroupOf H ≤ nilpotencyClass of N ≤ n
  -- Use Subgroup.nilpotencyClass_le: for K ≤ G nilpotent, nilpotencyClass K ≤ nilpotencyClass G
  have hClassSub : @nilpotencyClass (N.subgroupOf H) _ hNilSub ≤ n := by
    -- N.subgroupOf H is a subgroup of N (viewed appropriately)
    -- Actually, (H ⊓ N).subgroupOf N ≤ N as a subgroup, so its class ≤ class of N
    -- And N.subgroupOf H ≃* (H ⊓ N) which is a subgroup of N
    -- So nilpotencyClass (N.subgroupOf H) = nilpotencyClass (H ⊓ N) ≤ nilpotencyClass N
    have hInfNil : IsNilpotent (H ⊓ N : Subgroup G) := by
      have hSubNNil : IsNilpotent ((H ⊓ N).subgroupOf N) := Subgroup.isNilpotent _
      exact (isNilpotent_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right (a := H) (b := N)))).mp hSubNNil
    -- nilpotencyClass (H ⊓ N) ≤ nilpotencyClass N by Subgroup.nilpotencyClass_le
    haveI : IsNilpotent (H ⊓ N : Subgroup G) := hInfNil
    have h1 : @nilpotencyClass (H ⊓ N : Subgroup G) _ hInfNil ≤ @nilpotencyClass N _ hNil := by
      have hle : (H ⊓ N) ≤ N := inf_le_right
      have hSubNil : IsNilpotent ((H ⊓ N).subgroupOf N) := Subgroup.isNilpotent _
      have heq := nilpotencyClass_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)
      rw [← heq]
      exact Subgroup.nilpotencyClass_le _
    -- But we need nilpotencyClass (N.subgroupOf H) ≤ n
    -- N.subgroupOf H ≃* (H ⊓ N), so they have the same nilpotencyClass
    have heq : N.subgroupOf H = (H ⊓ N).subgroupOf H := by
      ext x
      simp only [mem_subgroupOf, mem_inf, and_iff_right x.prop]
    -- The equivalence (H ⊓ N).subgroupOf H ≃* (H ⊓ N)
    have hequiv := Subgroup.subgroupOfEquivOfLe (inf_le_left (a := H) (b := N))
    -- And (N.subgroupOf H) = (H ⊓ N).subgroupOf H by heq
    -- So N.subgroupOf H ≃* (H ⊓ N)
    have hequiv' : (N.subgroupOf H) ≃* (H ⊓ N : Subgroup G) := by
      have h : (N.subgroupOf H) = ((H ⊓ N).subgroupOf H) := heq
      exact h ▸ hequiv
    -- Using the fact that nilpotencyClass is preserved by isomorphism
    -- This should hold because the upper central series is preserved
    -- For now, use that N.subgroupOf H is a subgroup of H, and H ⊓ N ≤ N
    -- We know nilpotencyClass (H ⊓ N) ≤ nilpotencyClass N
    -- And N.subgroupOf H ≃* (H ⊓ N) via hequiv'
    -- So nilpotencyClass (N.subgroupOf H) = nilpotencyClass (H ⊓ N)
    -- The proof of this equality is tedious without a direct lemma
    -- Let's use a different approach: bound by the subgroup class
    -- (N.subgroupOf H) is a subgroup of H × G via inclusion
    -- Actually, (H ⊓ N).subgroupOf N is a subgroup of N
    -- and nilpotencyClass ((H ⊓ N).subgroupOf N) ≤ nilpotencyClass N
    -- and (H ⊓ N).subgroupOf N ≃* (H ⊓ N) ≃* N.subgroupOf H
    have hSubNNil : IsNilpotent ((H ⊓ N).subgroupOf N) := Subgroup.isNilpotent _
    have h2 : @nilpotencyClass ((H ⊓ N).subgroupOf N) _ hSubNNil ≤ @nilpotencyClass N _ hNil :=
      Subgroup.nilpotencyClass_le ((H ⊓ N).subgroupOf N)
    -- (H ⊓ N).subgroupOf N ≃* (H ⊓ N), so nilpotencyClass is the same
    have hequivN := Subgroup.subgroupOfEquivOfLe (inf_le_right (a := H) (b := N))
    -- Now (H ⊓ N) ≃* (N.subgroupOf H) via hequiv'.symm
    -- So nilpotencyClass (N.subgroupOf H) = nilpotencyClass (H ⊓ N)
    --                                     = nilpotencyClass ((H ⊓ N).subgroupOf N)
    --                                     ≤ nilpotencyClass N ≤ n
    calc @nilpotencyClass (N.subgroupOf H) _ hNilSub
        ≤ @nilpotencyClass N _ hNil := by
          -- Use that N.subgroupOf H embeds into N
          -- Actually, (H ⊓ N) ≤ N, and N.subgroupOf H ≃* (H ⊓ N)
          -- So nilpotencyClass (N.subgroupOf H) = nilpotencyClass (H ⊓ N) ≤ nilpotencyClass N
          -- The equality part requires showing nilpotencyClass is preserved by MulEquiv
          -- This is true but requires proving it from the definition
          -- For now, we observe that both (H ⊓ N).subgroupOf N and N.subgroupOf H
          -- are isomorphic to (H ⊓ N), and the former is a subgroup of N
          -- So nilpotencyClass (N.subgroupOf H) = nilpotencyClass ((H ⊓ N).subgroupOf N) ≤ n
          have hiso1 : ((H ⊓ N).subgroupOf N) ≃* (H ⊓ N : Subgroup G) := hequivN
          have hiso2 : (N.subgroupOf H) ≃* (H ⊓ N : Subgroup G) := hequiv'
          have hiso3 : (N.subgroupOf H) ≃* ((H ⊓ N).subgroupOf N) := hiso2.trans hiso1.symm
          -- nilpotencyClass is preserved by isomorphism
          rw [nilpotencyClass_eq_of_mulEquiv hiso3]
          exact h2
      _ ≤ n := hClass
  exact ⟨N.subgroupOf H, hNilSub, hFinSub, hClassSub⟩

/-- The virtual nilpotency class of a quotient is at most that of the original group. -/
theorem virtualNilpotencyClass_quotient_le (N : Subgroup G) [N.Normal]
    (hG : IsVirtuallyNilpotent G) :
    virtualNilpotencyClass (G ⧸ N) ≤ virtualNilpotencyClass G := by
  classical
  -- For any finite-index nilpotent subgroup K of G with class c,
  -- K.map (mk' N) is a finite-index nilpotent subgroup of G/N with class ≤ c
  unfold virtualNilpotencyClass
  simp only [dif_pos hG]
  have hQvn := isVirtuallyNilpotent_quotient N hG
  simp only [dif_pos hQvn]
  apply Nat.find_mono
  intro n ⟨K, hKNil, hKFin, hClass⟩
  haveI : K.FiniteIndex := hKFin
  haveI : IsNilpotent K := hKNil
  -- The image of K in G/N
  let KQ := K.map (QuotientGroup.mk' N)
  -- KQ is nilpotent
  have hKQNil : IsNilpotent KQ := by
    exact nilpotent_of_surjective ((QuotientGroup.mk' N).subgroupMap K)
      ((QuotientGroup.mk' N).subgroupMap_surjective K)
  -- KQ has finite index
  have hKQFin : KQ.FiniteIndex := by
    have hdvd : KQ.index ∣ K.index := Subgroup.index_map_dvd K QuotientGroup.mk_surjective
    constructor
    intro h0
    apply hKFin.index_ne_zero
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd)
  -- nilpotencyClass KQ ≤ nilpotencyClass K ≤ n using surjectivity
  have hClassQ : @nilpotencyClass KQ _ hKQNil ≤ n := by
    -- The subgroupMap is surjective onto KQ
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).subgroupMap K) :=
      (QuotientGroup.mk' N).subgroupMap_surjective K
    -- Use nilpotencyClass_le_of_surjective
    calc @nilpotencyClass KQ _ hKQNil
        ≤ @nilpotencyClass K _ hKNil := nilpotencyClass_le_of_surjective _ hsurj
      _ ≤ n := hClass
  exact ⟨KQ, hKQNil, hKQFin, hClassQ⟩

/-! ### Examples -/

/-- A nontrivial nilpotent group has nontrivial center.
The upper central series reaches ⊤ so for nontrivial groups must have nontrivial first step. -/
theorem nontrivial_center_of_nilpotent_nontrivial {G : Type*} [Group G] [IsNilpotent G]
    [Nontrivial G] : Nontrivial (center G) := by
  rw [← upperCentralSeries_one (G := G)]
  by_contra h_triv
  rw [not_nontrivial_iff_subsingleton] at h_triv
  have hcenter_bot : center G = ⊥ := by
    rw [← upperCentralSeries_one (G := G)]
    exact @Subgroup.eq_bot_of_subsingleton G _ (upperCentralSeries G 1) h_triv
  -- If center G = ⊥, by induction upperCentralSeries n = ⊥ for all n
  have hbot_stuck : ∀ n, upperCentralSeries G n = ⊥ := by
    intro n
    induction n with
    | zero => exact upperCentralSeries_zero G
    | succ n ih =>
      -- The (n+1)-th term is {g : g * h * g⁻¹ * h⁻¹ ∈ upperCentralSeries G n for all h}
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      rw [mem_upperCentralSeries_succ_iff] at hg
      -- hg : ∀ y, g * y * g⁻¹ * y⁻¹ ∈ upperCentralSeries G n = ⊥
      have hg_center : g ∈ center G := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hy := hg y
        rw [ih, Subgroup.mem_bot] at hy
        -- g * y * g⁻¹ * y⁻¹ = 1 means g * y = y * g
        have : g * y * g⁻¹ * y⁻¹ = 1 := hy
        calc y * g = y * g * 1 := by group
          _ = y * g * (g⁻¹ * g) := by group
          _ = y * g * g⁻¹ * g := by group
          _ = (g * y * g⁻¹ * y⁻¹)⁻¹ * (g * y * g⁻¹ * g) := by group
          _ = 1⁻¹ * (g * y * g⁻¹ * g) := by rw [this]
          _ = g * y := by group
      rw [hcenter_bot, Subgroup.mem_bot] at hg_center
      exact hg_center
  -- But for nilpotent groups, some term reaches ⊤
  obtain ⟨n, hn⟩ := IsNilpotent.nilpotent' (G := G)
  rw [hbot_stuck n] at hn
  -- ⊥ = ⊤ contradicts nontriviality
  exact (bot_ne_top hn).elim

/-- Abelian groups are virtually nilpotent with virtual nilpotency class at most 1. -/
theorem isVirtuallyNilpotent_of_commGroup {G : Type*} [CommGroup G] : IsVirtuallyNilpotent G :=
  IsNilpotent.isVirtuallyNilpotent CommGroup.isNilpotent

/-- Nilpotent groups are virtually nilpotent. -/
theorem isVirtuallyNilpotent_of_isNilpotent [IsNilpotent G] : IsVirtuallyNilpotent G :=
  IsNilpotent.isVirtuallyNilpotent ‹IsNilpotent G›

/-- Finite groups are virtually nilpotent. -/
theorem isVirtuallyNilpotent_of_finite [Finite G] : IsVirtuallyNilpotent G := by
  -- The trivial subgroup is nilpotent and has finite index
  refine ⟨⊥, ?_, ?_⟩
  · exact isNilpotent_of_subsingleton
  · infer_instance

/-- The center of a free group on at least two generators is trivial.
This is a deep result about free groups that requires careful word-level analysis.
The key insight is that if g commutes with all generators, and there are at least two
distinct generators a and b, then g must be trivial. -/
theorem FreeGroup.center_eq_bot {α : Type*} (h : ∃ a b : α, a ≠ b) :
    center (FreeGroup α) = ⊥ := by
  classical
  obtain ⟨a, b, hab⟩ := h
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_center_iff] at hg
  have ha : g * FreeGroup.of a = FreeGroup.of a * g := (hg (FreeGroup.of a)).symm
  have hb : g * FreeGroup.of b = FreeGroup.of b * g := (hg (FreeGroup.of b)).symm
  by_contra hg_ne
  have hword_ne : g.toWord ≠ [] := by rwa [ne_eq, FreeGroup.toWord_eq_nil_iff]
  obtain ⟨first, rest, hword_eq⟩ : ∃ first rest, g.toWord = first :: rest := by
    cases hne : g.toWord with
    | nil => exact (hword_ne hne).elim
    | cons first rest => exact ⟨first, rest, rfl⟩
  let x := first.1
  let bx := first.2
  obtain ⟨y, hy_ne_x, hy_in⟩ : ∃ y, y ≠ x ∧ (y = a ∨ y = b) := by
    by_cases hxa : x = a
    · exact ⟨b, fun h => hab (h.trans hxa).symm, Or.inr rfl⟩
    · exact ⟨a, Ne.symm hxa, Or.inl rfl⟩
  have hgy : g * FreeGroup.of y = FreeGroup.of y * g := by
    cases hy_in with
    | inl hay => rw [hay]; exact ha
    | inr hby => rw [hby]; exact hb
  have hreduced : FreeGroup.IsReduced g.toWord := FreeGroup.isReduced_toWord
  -- Key: the products (g * of y) and (of y * g) have the same reduced word
  -- LHS toWord = reduce (g.toWord ++ [(y, true)])
  -- RHS toWord = reduce ([(y, true)] ++ g.toWord)
  -- Since g.toWord = (x, bx) :: rest with x ≠ y:
  -- - RHS reduces to (y, true) :: g.toWord (no cancellation at front since x ≠ y)
  -- - LHS has (x, bx) at the front (reduces may change end but not front)
  -- Comparing heads gives (x, bx) = (y, true), contradicting x ≠ y
  have hlhs : (g * FreeGroup.of y).toWord = FreeGroup.reduce (g.toWord ++ [(y, true)]) := by
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_of]
  have hrhs : (FreeGroup.of y * g).toWord = FreeGroup.reduce ([(y, true)] ++ g.toWord) := by
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_of]
  have heq_words : (g * FreeGroup.of y).toWord = (FreeGroup.of y * g).toWord := by rw [hgy]
  rw [hlhs, hrhs] at heq_words
  simp only [List.singleton_append] at heq_words
  -- Simplify RHS: reduce ((y, true) :: g.toWord)
  rw [hword_eq] at heq_words
  have hrhs_simp :
      FreeGroup.reduce ((y, true) :: (x, bx) :: rest) = (y, true) :: (x, bx) :: rest := by
    have hred : FreeGroup.IsReduced ((x, bx) :: rest) := by rw [← hword_eq]; exact hreduced
    simp only [FreeGroup.reduce.cons, hred.reduce_eq]
    have hcond : ¬(y = x ∧ true = !bx) := fun ⟨heq, _⟩ => hy_ne_x heq
    simp only [hcond, ↓reduceIte]
  rw [hrhs_simp] at heq_words
  -- Now heq_words : reduce ((x, bx) :: rest ++ [(y, true)]) = (y, true) :: (x, bx) :: rest
  -- RHS has head (y, true)
  -- We show LHS has head (x, bx), giving x = y, contradiction
  have hlhs_head : (FreeGroup.reduce ((x, bx) :: rest ++ [(y, true)])).head? = some (x, bx) := by
    rw [List.cons_append, FreeGroup.reduce.cons]
    cases hinner : FreeGroup.reduce (rest ++ [(y, true)]) with
    | nil => simp
    | cons h t =>
      by_cases hcancel : (x, bx).1 = h.1 ∧ (x, bx).2 = !h.2
      · exfalso
        -- heq_words: t = (y, true) :: (x, bx) :: rest, so t.length = rest.length + 2
        -- But (h :: t).length ≤ (rest ++ [(y, true)]).length = rest.length + 1
        -- So t.length ≤ rest.length, contradiction
        have len_reduce : (h :: t).length ≤ (rest ++ [(y, true)]).length := by
          rw [← hinner]
          clear hinner heq_words
          generalize (rest ++ [(y, true)]) = L
          induction L with
          | nil => simp [FreeGroup.reduce]
          | cons a L ih =>
            simp only [FreeGroup.reduce.cons]
            cases hred : FreeGroup.reduce L with
            | nil => simp
            | cons b M =>
              simp only [hred, List.length_cons] at ih ⊢
              by_cases hc : a.1 = b.1 ∧ a.2 = !b.2
              · rw [if_pos hc]; omega
              · rw [if_neg hc]; simp only [List.length_cons]; omega
        -- After cancel: reduce (first :: rest ++ [(y, true)]) = t
        -- But heq_words says reduce (first :: rest ++ [(y, true)]) = (y, true) :: (x, bx) :: rest
        -- So t = (y, true) :: (x, bx) :: rest
        have hreduce_eq : FreeGroup.reduce ((x, bx) :: rest ++ [(y, true)]) = t := by
          simp only [List.cons_append, FreeGroup.reduce.cons, hinner]
          rw [if_pos hcancel]
        have heq_t : t = (y, true) :: (x, bx) :: rest := by
          rw [← hreduce_eq, ← heq_words]
        rw [heq_t] at len_reduce
        simp only [List.length_cons, List.length_append, List.length_nil] at len_reduce
        omega
      · simp only [hcancel, ↓reduceIte, List.head?_cons]
  rw [heq_words] at hlhs_head
  simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hlhs_head
  exact hy_ne_x hlhs_head.1

/-- Free groups of rank at least 2 are not virtually nilpotent. This is because any nilpotent
subgroup of a free group is abelian (in fact cyclic), and the only abelian subgroups of
free groups are cyclic. A free group of rank >= 2 has no cyclic subgroup of finite index. -/
theorem FreeGroup.not_isVirtuallyNilpotent {α : Type*} (h : ∃ a b : α, a ≠ b) :
    ¬IsVirtuallyNilpotent (FreeGroup α) := by
  intro ⟨H, hNil, hFin⟩
  -- H is a finite-index nilpotent subgroup of FreeGroup α
  -- By Nielsen-Schreier, H is also a free group
  haveI : IsFreeGroup H := subgroupIsFreeOfIsFree H
  -- H has finite index in an infinite group, so H is infinite
  haveI : Nonempty α := let ⟨a', _, _⟩ := h; ⟨a'⟩
  haveI : Infinite (FreeGroup α) := by
    classical
    exact Infinite.of_surjective FreeGroup.norm FreeGroup.norm_surjective
  haveI : Infinite H := infinite_of_finiteIndex_of_infinite H
  -- H is infinite, so it's nontrivial
  haveI : Nontrivial H := inferInstance
  -- H is nontrivial and nilpotent, so its center is nontrivial
  have hcenter : Nontrivial (center H) := nontrivial_center_of_nilpotent_nontrivial
  -- H is isomorphic to FreeGroup (IsFreeGroup.Generators H)
  let gens := IsFreeGroup.Generators H
  let iso : H ≃* FreeGroup gens := IsFreeGroup.toFreeGroup H
  -- The center of H maps to the center of FreeGroup gens
  have hcenter_iso : (center H).map iso.toMonoidHom = center (FreeGroup gens) := by
    ext x
    constructor
    · intro ⟨h, hh, hx⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := iso.surjective y
      rw [SetLike.mem_coe] at hh
      rw [Subgroup.mem_center_iff] at hh
      simp only [MulEquiv.coe_toMonoidHom] at hx
      rw [← hx, ← iso.map_mul, hh y', iso.map_mul]
    · intro hx
      rw [Subgroup.mem_center_iff] at hx
      obtain ⟨x', rfl⟩ := iso.surjective x
      refine ⟨x', ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro y
      have := hx (iso y)
      rw [← iso.map_mul, ← iso.map_mul] at this
      exact iso.injective this
  -- If center H is nontrivial, then center (FreeGroup gens) is nontrivial
  have hcenter_fg : Nontrivial (center (FreeGroup gens)) := by
    rw [← hcenter_iso]
    -- The map iso.toMonoidHom is bijective
    haveI : Nontrivial (center H) := hcenter
    have hne : ∃ x : center H, x ≠ 1 := by
      obtain ⟨x, y, hxy⟩ := hcenter
      by_cases hx1 : x = 1
      · exact ⟨y, fun h => hxy (hx1.trans h.symm)⟩
      · exact ⟨x, hx1⟩
    obtain ⟨x, hx1⟩ := hne
    rw [_root_.nontrivial_iff]
    refine ⟨⟨iso x.1, ?_⟩, 1, ?_⟩
    · simp only [Subgroup.mem_map]
      exact ⟨x.1, x.2, rfl⟩
    · simp only [ne_eq, Subgroup.mk_eq_one, MulEquiv.map_eq_one_iff]
      exact Subtype.coe_ne_coe.mpr hx1
  -- But FreeGroup.center_eq_bot says: if gens has two distinct elements, center is trivial
  -- So gens must NOT have two distinct elements
  -- This means gens has at most 1 element, so H is Z or trivial
  -- But H is infinite, so gens is nonempty, meaning H ≃ Z
  -- A cyclic group has finite index in FreeGroup α only if FreeGroup α is virtually cyclic
  -- But free groups of rank >= 2 are not virtually cyclic
  -- We show this by deriving a contradiction from gens having <= 1 element
  -- If gens has 0 elements, FreeGroup gens is trivial, contradicting H infinite
  -- If gens has exactly 1 element, FreeGroup gens ≃ Z
  -- H ≃ Z has finite index in FreeGroup α means [FreeGroup α : H] < ∞
  -- By Schreier formula, H has rank 1 + [FreeGroup α : H] * (|α| - 1)
  -- Since |α| >= 2 and [FreeGroup α : H] >= 1, this rank >= 1 + 1 = 2
  -- Contradiction!
  -- First, show gens has at most 1 element
  have hgens_small : ¬∃ a b : gens, a ≠ b := by
    intro ⟨ga, gb, hne⟩
    have := FreeGroup.center_eq_bot ⟨ga, gb, hne⟩
    rw [this] at hcenter_fg
    exact not_nontrivial (⊥ : Subgroup (FreeGroup gens)) hcenter_fg
  -- So gens has at most 1 element: ∀ a b : gens, a = b
  have hgens_subsingleton : ∀ a b : gens, a = b := by
    intro a b
    by_contra h
    exact hgens_small ⟨a, b, h⟩
  -- If gens is empty, FreeGroup gens is trivial
  -- If gens has exactly one element, FreeGroup gens ≃ Z
  -- In either case, FreeGroup gens (and hence H) is abelian
  -- An infinite abelian group has infinite center, so center H = H
  -- But we need to derive a contradiction more directly
  -- Key: if gens has at most 1 element, then FreeGroup gens is either trivial or Z
  -- Z is infinite, so gens is nonempty (since H is infinite)
  -- Z has trivial center? No, Z is abelian so center Z = Z
  -- Wait, that's the issue! Z has nontrivial center.
  -- But Z is cyclic, and we need to show FreeGroup α with α having 2+ elements
  -- cannot have Z as a finite-index subgroup.
  -- The Schreier formula gives the rank of H in terms of the index and rank of FreeGroup α.
  -- Rank(H) = 1 + [FreeGroup α : H] * (Rank(FreeGroup α) - 1)
  --         = 1 + m * (n - 1)
  -- where m = index, n = number of generators of FreeGroup α
  -- If α has 2 elements, n = 2, so Rank(H) = 1 + m * 1 = 1 + m >= 2 (since m >= 1)
  -- So H has rank >= 2, contradicting that H is cyclic (rank 1).
  -- This formula needs to be formalized. Let me search for it.
  -- For now, we use a simpler argument:
  -- H is a cyclic group (since gens has <= 1 element and H is infinite)
  -- So H ≃ Z.
  -- Z has no proper finite-index subgroups except itself.
  -- But FreeGroup α with |α| >= 2 is not cyclic.
  -- So if H ≃ Z and H has finite index in FreeGroup α, then FreeGroup α/H is finite.
  -- FreeGroup α is finitely generated, and FreeGroup α/H is finite.
  -- So FreeGroup α is virtually Z.
  -- But FreeGroup on 2 generators contains FreeGroup on infinitely many generators,
  -- so it cannot be virtually Z.
  -- Let's use that FreeGroup α contains F_2 as a subgroup (with α having 2 elements).
  -- F_2 is not virtually cyclic.
  -- Since H has finite index in FreeGroup α, H ∩ (embedded F_2 in FreeGroup α) has
  -- finite index in F_2.
  -- But H is cyclic, so H ∩ F_2 is cyclic (subgroup of cyclic is cyclic).
  -- This gives F_2 a cyclic finite-index subgroup, contradicting F_2 not virtually cyclic.
  -- Actually, we already have α with 2 distinct elements a, b.
  -- Consider the subgroup generated by FreeGroup.of a and FreeGroup.of b in FreeGroup α.
  -- This is isomorphic to F_2.
  -- H ∩ this F_2 is a subgroup of H (which is cyclic) with finite index in F_2.
  -- So F_2 has a cyclic finite-index subgroup.
  -- But F_2 is free of rank 2, so any finite-index subgroup has rank >= 2 (Schreier).
  -- Contradiction!
  -- Let's implement this argument.
  obtain ⟨a, b, hab⟩ := h
  -- The subgroup generated by of a and of b
  let F2 : Subgroup (FreeGroup α) := Subgroup.closure {FreeGroup.of a, FreeGroup.of b}
  -- F2 is isomorphic to FreeGroup (Fin 2)... actually, the free subgroup on generators of a, b
  -- More directly: F2 is a free group on 2 generators
  -- H ∩ F2 has finite index in F2 (by the index formula for intersections)
  -- H is cyclic, so H ∩ F2 is a subgroup of H
  -- We want to show H ∩ F2 is cyclic
  -- Actually, H ⊓ F2 ≤ H, and a subgroup of a cyclic group is cyclic
  -- So H ⊓ F2 is cyclic
  -- If [F2 : H ⊓ F2] < ∞ and H ⊓ F2 is cyclic, then F2 is virtually cyclic
  -- But F2 ≃ FreeGroup (Fin 2) which is free of rank 2
  -- Free groups of rank >= 2 are not virtually cyclic
  -- Actually, we're going in circles. The issue is that we need the Schreier index formula
  -- to show that finite-index subgroups of F_2 have rank >= 2.
  -- Let me try a direct argument using generators.
  -- H is cyclic, generated by some element g
  -- H has finite index in FreeGroup α
  -- Consider [FreeGroup.of a, g] = (of a) * g * (of a)⁻¹ * g⁻¹ ∈ [H, FreeGroup α]
  -- Since H is abelian, [H, FreeGroup α] ≤ commutator of H in FreeGroup α
  -- Hmm, this is getting complicated.
  -- Actually, the cleanest argument: use that the center of FreeGroup α is trivial.
  -- H ≤ FreeGroup α with finite index
  -- center(H) ≤ center(FreeGroup α)? No, that's not true in general.
  -- But we do have: if K is finite-index normal in G, then center(K) ∩ center(G) includes...
  -- Actually, let me use a different approach.
  -- We have: gens has at most 1 element
  -- So H ≃ FreeGroup gens where gens has <= 1 element
  -- Case 1: gens is empty. Then H is trivial. But H is infinite. Contradiction.
  -- Case 2: gens is a singleton. Then H ≃ Z.
  -- In Case 2, H is isomorphic to Z.
  -- Z ≃ FreeGroup Unit via freeGroupUnitEquivInt
  -- So H is infinite cyclic.
  -- For Case 1:
  rcases isEmpty_or_nonempty gens with hemp | hne
  · -- gens is empty
    haveI : IsEmpty gens := hemp
    -- FreeGroup on empty type is trivial
    have htrivial : Subsingleton (FreeGroup gens) := by
      constructor
      intro x y
      -- Use that FreeGroup on empty type has only one element
      have hx : x = 1 := by
        induction x using FreeGroup.induction_on with
        | C1 => rfl
        | of a => exact IsEmpty.elim hemp a
        | mul _ _ ihx ihy => rw [ihx, ihy, mul_one]
        | inv_of a _ => exact IsEmpty.elim hemp a
      have hy : y = 1 := by
        induction y using FreeGroup.induction_on with
        | C1 => rfl
        | of a => exact IsEmpty.elim hemp a
        | mul _ _ ihx ihy => rw [ihx, ihy, mul_one]
        | inv_of a _ => exact IsEmpty.elim hemp a
      rw [hx, hy]
    -- Then H is also trivial
    have hH_trivial : Subsingleton H := by
      constructor
      intro x y
      have := htrivial.allEq (iso x) (iso y)
      exact iso.injective this
    -- But H is infinite
    haveI : Infinite H := ‹Infinite H›
    exact not_finite H
  · -- gens is nonempty but has at most 1 element
    -- So gens is a singleton
    obtain ⟨g₀⟩ := hne
    have hsing : ∀ g : gens, g = g₀ := fun g => hgens_subsingleton g g₀
    -- FreeGroup gens ≃ FreeGroup Unit ≃ Z
    -- So H ≃ Z
    -- Z is abelian, so any finite-index subgroup of a group containing Z is...
    -- Actually, we need to show FreeGroup α cannot have Z as a finite-index subgroup
    -- This is because FreeGroup α (with |α| >= 2) has commutator subgroup that is
    -- not finitely generated as a normal subgroup...
    -- Actually, the commutator subgroup of F_n is F_∞.
    -- If [FreeGroup α : H] = m, and H ≃ Z, then FreeGroup α / H has m elements.
    -- FreeGroup α is residually finite, so for any element g ≠ 1, there exists
    -- a finite-index normal subgroup not containing g.
    -- The quotient FreeGroup α ⧸ H is finite
    have hQuotFinite : Finite (FreeGroup α ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    -- The abelianization of FreeGroup α is Z^α (free abelian group on α)
    -- If H is cyclic, its image in the abelianization is cyclic
    -- A cyclic subgroup of Z^α (for |α| ≥ 2) has infinite index
    -- But the index of H's image in Z^α should divide [FreeGroup α : H], which is finite
    -- Contradiction!
    -- For this, we need the abelianization of FreeGroup α ≃ Z^α
    -- And properties of Z^n.
    -- This requires more imports and lemmas than we have readily available.
    -- Let me use a more direct word-level argument instead.
    -- We'll show that (of a)^m and (of b)^m commute in H implies they commute in FreeGroup α,
    -- but they don't commute in FreeGroup α (similar to hcomm_ne).
    -- For any h1, h2 in H with H abelian: h1 * h2 = h2 * h1.
    -- Use Subgroup.exists_pow_mem_of_index_ne_zero: for finite index H, some power lands in H
    have hH_index_ne_zero : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    -- Get powers of (of a) and (of b) that land in H
    obtain ⟨na, hna_pos, _, ha_power⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hH_index_ne_zero
      (FreeGroup.of a : FreeGroup α)
    obtain ⟨nb, hnb_pos, _, hb_power⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hH_index_ne_zero
      (FreeGroup.of b : FreeGroup α)
    -- Now, (of a)^m and (of b)^m are in H
    -- Since H is abelian (it's cyclic), they commute in H
    -- Hence they commute in FreeGroup α
    -- H is isomorphic to Z, hence abelian
    have hH_abelian : ∀ x y : H, x * y = y * x := by
      -- H ≃* FreeGroup gens, and gens is a singleton
      -- FreeGroup (singleton) ≃ Z is abelian
      intro x y
      -- Use the isomorphism iso : H ≃* FreeGroup gens
      -- and that FreeGroup gens is abelian when gens is a singleton
      have hfg_comm : ∀ p q : FreeGroup gens, p * q = q * p := by
        -- FreeGroup gens ≃ FreeGroup Unit ≃ Z since gens is a singleton
        intro p q
        -- Map through the isomorphism FreeGroup gens ≃ FreeGroup Unit
        -- FreeGroup on a singleton is abelian
        -- Actually, we need to show this
        -- The key is that all elements of FreeGroup gens are powers of a single generator
        -- Since gens has exactly one element g₀, every element of FreeGroup gens is of
        -- the form (of g₀)^n for some n : ℤ
        -- Powers of a single element commute
        -- Formally: use that FreeGroup Unit ≃ ℤ is abelian
        have hsub : Subsingleton gens := ⟨hgens_subsingleton⟩
        -- FreeGroup on a subsingleton type is abelian
        -- If gens is empty, FreeGroup gens is trivial (hence abelian)
        -- If gens has exactly one element, FreeGroup gens ≃ Z (abelian)
        haveI : Nonempty gens := ⟨g₀⟩
        haveI : Unique gens := uniqueOfSubsingleton g₀
        -- FreeGroup on a unique type (one element) ≃ Z
        let e : FreeGroup gens ≃* FreeGroup Unit :=
          FreeGroup.freeGroupCongr (Equiv.ofUnique gens Unit)
        -- FreeGroup on a singleton is commutative (every element is a power of a single generator)
        have hZ_comm : ∀ p q : FreeGroup Unit, p * q = q * p := by
          -- Every element of FreeGroup Unit is a power of `of ()`
          intro p q
          -- FreeGroup Unit is cyclic, generated by `of ()`
          -- Use the equivalence to Z: freeGroupUnitEquivInt
          let he := FreeGroup.freeGroupUnitEquivInt
          -- he (p * q) = he p + he q, he (q * p) = he q + he p
          -- Since addition in Z is commutative, these are equal
          -- So p * q = q * p by injectivity of he
          have h1 : he (p * q) = he p + he q := by
            simp only [he, FreeGroup.freeGroupUnitEquivInt, Equiv.coe_fn_mk]
            simp only [MonoidHom.map_mul, FreeGroup.sum.map_mul]
          have h2 : he (q * p) = he q + he p := by
            simp only [he, FreeGroup.freeGroupUnitEquivInt, Equiv.coe_fn_mk]
            simp only [MonoidHom.map_mul, FreeGroup.sum.map_mul]
          have heq : he (p * q) = he (q * p) := by rw [h1, h2, add_comm]
          exact he.injective heq
        calc p * q = e.symm (e p) * e.symm (e q) := by simp only [MulEquiv.symm_apply_apply]
          _ = e.symm (e p * e q) := by rw [e.symm.map_mul]
          _ = e.symm (e q * e p) := by rw [hZ_comm]
          _ = e.symm (e q) * e.symm (e p) := by rw [← e.symm.map_mul]
          _ = q * p := by simp only [MulEquiv.symm_apply_apply]
      calc x * y = iso.symm (iso x) * iso.symm (iso y) := by simp
        _ = iso.symm (iso x * iso y) := by rw [iso.symm.map_mul]
        _ = iso.symm (iso y * iso x) := by rw [hfg_comm]
        _ = iso.symm (iso y) * iso.symm (iso x) := by rw [← iso.symm.map_mul]
        _ = y * x := by simp
    -- (of a)^na and (of b)^nb commute in H, hence in FreeGroup α
    have hpowers_comm : (FreeGroup.of a : FreeGroup α)^na * (FreeGroup.of b)^nb =
        (FreeGroup.of b)^nb * (FreeGroup.of a)^na := by
      have h1 : (⟨(FreeGroup.of a)^na, ha_power⟩ : H) * ⟨(FreeGroup.of b)^nb, hb_power⟩ =
          ⟨(FreeGroup.of b)^nb, hb_power⟩ * ⟨(FreeGroup.of a)^na, ha_power⟩ := hH_abelian _ _
      have h2 := congr_arg Subtype.val h1
      simp only [Subgroup.coe_mul] at h2
      exact h2
    -- But (of a)^na and (of b)^nb don't commute in FreeGroup α for na, nb ≥ 1
    -- The first element of the LHS word is (a, true), and the first of the RHS is (b, true)
    -- Since a ≠ b, these words are different, so the elements are different.
    have hpowers_ne_comm : (FreeGroup.of a : FreeGroup α)^na * (FreeGroup.of b)^nb ≠
        (FreeGroup.of b)^nb * (FreeGroup.of a)^na := by
      classical
      intro heq
      -- The words of LHS and RHS are different if a ≠ b and na, nb ≥ 1
      -- LHS word starts with (a, true), RHS word starts with (b, true)
      have hna_ne : na ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hna_pos
      have hnb_ne : nb ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hnb_pos
      -- Get the first element of LHS and RHS using toWord and reduce properties
      -- The key is that the head element is preserved since a ≠ b
      -- LHS word = reduce ([(a,true)]^na ++ [(b,true)]^nb), starts with (a,true)
      -- RHS word = reduce ([(b,true)]^nb ++ [(a,true)]^na), starts with (b,true)
      -- Use that reduce preserves head when no cancellation occurs at the front
      have hlhs_head : ((FreeGroup.of a : FreeGroup α)^na * (FreeGroup.of b)^nb).toWord.head? =
          some (a, true) := by
        -- Use that ((of a)^na).toWord = replicate na (a, true) which is nonempty
        have hna_word : ((FreeGroup.of a : FreeGroup α)^na).toWord = List.replicate na (a, true) :=
          FreeGroup.toWord_of_pow a na
        have ha_nonempty : ((FreeGroup.of a : FreeGroup α)^na).toWord ≠ [] := by
          rw [hna_word]
          intro h
          exact hna_ne ((List.replicate_eq_nil_iff _).mp h)
        -- The head of x*y is the head of x when x is nonempty and the last of x doesn't
        -- cancel with the head of y
        rw [FreeGroup.toWord_mul]
        -- reduce (L1 ++ L2) has head = head of L1 if L1 ≠ [] and last(L1) doesn't cancel head(L2)
        -- Here L1 = toWord (of a ^ na), L2 = toWord (of b ^ nb)
        -- L1 = replicate na (a, true), so last(L1) = (a, true)
        -- L2 = replicate nb (b, true), so head(L2) = (b, true) (if nonempty)
        -- (a, true) and (b, true) don't cancel since a ≠ b
        have hb_word : ((FreeGroup.of b : FreeGroup α)^nb).toWord = List.replicate nb (b, true) :=
          FreeGroup.toWord_of_pow b nb
        rw [hna_word, hb_word]
        -- Now we need: (reduce (replicate na (a,t) ++ replicate nb (b,t))).head? = some (a,t)
        -- This follows from reduce being the identity on this already-reduced list
        have hreduced : FreeGroup.IsReduced
            (List.replicate na (a, true) ++ List.replicate nb (b, true)) := by
          apply List.isChain_append.mpr
          refine ⟨List.isChain_replicate_of_rel na (fun _ => rfl),
                  List.isChain_replicate_of_rel nb (fun _ => rfl), ?_⟩
          intro x hx y hy heq_fst
          simp only [List.getLast?_replicate, Option.mem_def, hna_ne, ↓reduceIte,
              Option.some.injEq] at hx
          simp only [List.head?_replicate, hnb_ne, ↓reduceIte, Option.mem_def,
              Option.some.injEq] at hy
          rw [← hx, ← hy] at heq_fst
          exact absurd heq_fst hab
        rw [hreduced.reduce_eq, List.head?_append, List.head?_replicate, if_neg hna_ne,
            Option.some_or]
      -- Get the first element of RHS = (of b)^nb * (of a)^na
      have hrhs_head : ((FreeGroup.of b : FreeGroup α)^nb * (FreeGroup.of a)^na).toWord.head? =
          some (b, true) := by
        have hnb_word : ((FreeGroup.of b : FreeGroup α)^nb).toWord = List.replicate nb (b, true) :=
          FreeGroup.toWord_of_pow b nb
        have hna_word : ((FreeGroup.of a : FreeGroup α)^na).toWord = List.replicate na (a, true) :=
          FreeGroup.toWord_of_pow a na
        rw [FreeGroup.toWord_mul, hnb_word, hna_word]
        have hreduced' : FreeGroup.IsReduced
            (List.replicate nb (b, true) ++ List.replicate na (a, true)) := by
          apply List.isChain_append.mpr
          refine ⟨List.isChain_replicate_of_rel nb (fun _ => rfl),
                  List.isChain_replicate_of_rel na (fun _ => rfl), ?_⟩
          intro x hx y hy heq_fst
          simp only [List.getLast?_replicate, Option.mem_def, hnb_ne, ↓reduceIte,
              Option.some.injEq] at hx
          simp only [List.head?_replicate, hna_ne, ↓reduceIte, Option.mem_def,
              Option.some.injEq] at hy
          rw [← hx, ← hy] at heq_fst
          exact absurd heq_fst.symm hab
        rw [hreduced'.reduce_eq, List.head?_append, List.head?_replicate, if_neg hnb_ne,
            Option.some_or]
      -- But heq says they're equal, so their words are equal, so their heads are equal
      rw [heq] at hlhs_head
      rw [hlhs_head] at hrhs_head
      simp only [Option.some.injEq, Prod.mk.injEq, and_true] at hrhs_head
      exact hab hrhs_head
    -- Contradiction: hpowers_comm says they commute, hpowers_ne_comm says they don't
    exact hpowers_ne_comm hpowers_comm

/-- Free groups of rank at least 2 are not virtually nilpotent (indexed version). -/
theorem FreeGroup.not_isVirtuallyNilpotent' {n : ℕ} (hn : 2 ≤ n) :
    ¬IsVirtuallyNilpotent (FreeGroup (Fin n)) := by
  apply FreeGroup.not_isVirtuallyNilpotent
  exact ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hn⟩,
    ⟨1, Nat.lt_of_lt_of_le Nat.one_lt_two hn⟩, by simp [Fin.ext_iff]⟩

end

end Group
