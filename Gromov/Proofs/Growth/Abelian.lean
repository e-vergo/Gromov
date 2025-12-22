/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Polynomial growth for finitely generated abelian groups.
-/

module

public import Gromov.Proofs.Growth.Polynomial
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Polynomial Growth for Abelian Groups

This file proves that finitely generated abelian groups have polynomial growth.

## Main results

* `PolynomialGrowth.hasPolynomialGrowth_prod`: The product of two groups with polynomial growth
  has polynomial growth.
* `PolynomialGrowth.commGroup_hasPolynomialGrowth`: Every finitely generated abelian group has
  polynomial growth.

## Approach

The proof follows the structure theorem for finitely generated abelian groups:
1. Every f.g. abelian group is isomorphic to Z^r x T where T is a finite abelian group
2. Z^r has polynomial growth of degree r (proved in PolynomialGrowth.lean)
3. Finite groups have polynomial growth of degree 0
4. Products of groups with polynomial growth have polynomial growth

The growth degree equals the torsion-free rank r.
-/

namespace Gromov.PolynomialGrowth

public section

open Gromov Filter Set

variable {G : Type*} [Group G]

/-! ## Polynomial growth under equivalence -/

/-- Polynomial growth is preserved under multiplicative equivalence. -/
theorem hasPolynomialGrowth_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hH : HasPolynomialGrowth H) : HasPolynomialGrowth G := by
  obtain ⟨S, hS_fin, hS_gen, C, d, hC_pos, hbound⟩ := hH
  use e.symm '' S
  refine ⟨hS_fin.image _, ?_, C, d, hC_pos, ?_⟩
  · -- e⁻¹ '' S generates G
    ext g
    simp only [Subgroup.mem_top, iff_true]
    have heg : e g ∈ Subgroup.closure S := by rw [hS_gen]; trivial
    rw [Subgroup.mem_closure] at heg ⊢
    intro K hK
    have heK : ∀ s ∈ S, e.symm s ∈ K := fun s hs => hK (Set.mem_image_of_mem _ hs)
    have hmem : e g ∈ Subgroup.map e.toMonoidHom K := by
      apply heg
      intro s hs
      exact ⟨e.symm s, heK s hs, by simp⟩
    obtain ⟨k, hk, hek⟩ := hmem
    have : g = k := e.injective (hek.symm ▸ rfl)
    rwa [this]
  · -- Growth bound
    intro n hn
    have h_image : e '' CayleyBall (e.symm '' S) n ⊆ CayleyBall S n := by
      intro h hh
      obtain ⟨g, hg, rfl⟩ := hh
      simp only [CayleyBall, Set.mem_setOf_eq] at hg ⊢
      obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hg
      use l.map e
      refine ⟨by simp [hl_len], ?_, ?_⟩
      · intro s hs
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
        have hmem := hl_mem a ha
        rcases hmem with (⟨t, ht, rfl⟩ | ⟨t, ht, hinv⟩)
        · left; simp [ht]
        · right
          -- hinv : e.symm t = a⁻¹, so a = (e.symm t)⁻¹
          have ha_eq : a = (e.symm t)⁻¹ := by simp only [hinv, inv_inv]
          rw [ha_eq, map_inv, MulEquiv.apply_symm_apply, inv_inv]
          exact ht
      · rw [← hl_prod, ← map_list_prod]
    have h_fin : (CayleyBall S n).Finite := cayleyBall_finite hS_fin n
    have h_ncard : (CayleyBall (e.symm '' S) n).ncard ≤ (CayleyBall S n).ncard := by
      calc (CayleyBall (e.symm '' S) n).ncard
          = (e '' CayleyBall (e.symm '' S) n).ncard :=
            (Set.ncard_image_of_injective _ e.injective).symm
        _ ≤ (CayleyBall S n).ncard := Set.ncard_le_ncard h_image h_fin
    calc (GrowthFunction (e.symm '' S) n : ℝ)
        = (CayleyBall (e.symm '' S) n).ncard := rfl
      _ ≤ (CayleyBall S n).ncard := by exact_mod_cast h_ncard
      _ = GrowthFunction S n := rfl
      _ ≤ C * n ^ d := hbound n hn

/-- Polynomial growth transfer in the opposite direction. -/
theorem hasPolynomialGrowth_of_mulEquiv' {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hG : HasPolynomialGrowth G) : HasPolynomialGrowth H :=
  hasPolynomialGrowth_of_mulEquiv e.symm hG

/-! ## Products preserve polynomial growth -/

/-- Helper: fst of list product equals product of mapped list. -/
lemma prod_fst_eq_map_fst {G H : Type*} [Group G] [Group H] (l : List (G × H)) :
    l.prod.fst = (l.map Prod.fst).prod := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.prod_cons, Prod.fst_mul, List.map_cons]
    rw [ih]

/-- Helper: snd of list product equals product of mapped list. -/
lemma prod_snd_eq_map_snd {G H : Type*} [Group G] [Group H] (l : List (G × H)) :
    l.prod.snd = (l.map Prod.snd).prod := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.prod_cons, Prod.snd_mul, List.map_cons]
    rw [ih]

/-- The product of two groups with polynomial growth has polynomial growth. -/
theorem hasPolynomialGrowth_prod {G H : Type*} [Group G] [Group H]
    (hG : HasPolynomialGrowth G) (hH : HasPolynomialGrowth H) :
    HasPolynomialGrowth (G × H) := by
  obtain ⟨S_G, hS_G_fin, hS_G_gen, C_G, d_G, hC_G_pos, hbound_G⟩ := hG
  obtain ⟨S_H, hS_H_fin, hS_H_gen, C_H, d_H, hC_H_pos, hbound_H⟩ := hH
  -- Add 1 to both generating sets to use Subgroup.closure_prod
  let S_G' := insert 1 S_G
  let S_H' := insert 1 S_H
  use S_G' ×ˢ S_H'
  have hS_G'_fin : S_G'.Finite := hS_G_fin.insert 1
  have hS_H'_fin : S_H'.Finite := hS_H_fin.insert 1
  have h1G : (1 : G) ∈ S_G' := Set.mem_insert 1 S_G
  have h1H : (1 : H) ∈ S_H' := Set.mem_insert 1 S_H
  have hS_G'_gen : Subgroup.closure S_G' = ⊤ := by
    rw [eq_top_iff, ← hS_G_gen]
    exact Subgroup.closure_mono (Set.subset_insert 1 S_G)
  have hS_H'_gen : Subgroup.closure S_H' = ⊤ := by
    rw [eq_top_iff, ← hS_H_gen]
    exact Subgroup.closure_mono (Set.subset_insert 1 S_H)
  refine ⟨hS_G'_fin.prod hS_H'_fin, ?_, ?_⟩
  · -- S_G' ×ˢ S_H' generates G × H using Subgroup.closure_prod
    rw [Subgroup.closure_prod h1G h1H, hS_G'_gen, hS_H'_gen]
    ext ⟨g, h⟩
    simp only [Subgroup.mem_prod, Subgroup.mem_top, and_self]
  · -- Polynomial growth bound
    -- Get constants for the comparison of S_G and S_G'
    -- growth_equivalent gives: k₁ for S₁→S₂ and k₂ for S₂→S₁
    obtain ⟨_, k_G, _, hk_G_pos, _, hk_G1⟩ :=
      growth_equivalent_of_generating_sets hS_G_fin hS_G'_fin hS_G_gen hS_G'_gen
    obtain ⟨_, k_H, _, hk_H_pos, _, hk_H1⟩ :=
      growth_equivalent_of_generating_sets hS_H_fin hS_H'_fin hS_H_gen hS_H'_gen
    -- hk_G1 : ∀ n, GrowthFunction S_G' n ≤ GrowthFunction S_G (n * k_G)
    -- The ball for the product is bounded by product of balls
    have h_subset : ∀ n, CayleyBall (S_G' ×ˢ S_H') n ⊆
        (CayleyBall S_G' n) ×ˢ (CayleyBall S_H' n) := by
      intro n ⟨g, h⟩ hgh
      simp only [CayleyBall, Set.mem_setOf_eq] at hgh
      obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hgh
      constructor
      · -- g in CayleyBall S_G' n
        use l.map Prod.fst
        refine ⟨by simp only [List.length_map]; omega, ?_, ?_⟩
        · intro s hs
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hs
          have hmem := hl_mem (a, b) hab
          simp only [Set.mem_prod, Prod.inv_mk] at hmem
          rcases hmem with ⟨ha, _⟩ | ⟨ha, _⟩
          · exact Or.inl ha
          · exact Or.inr ha
        · rw [← prod_fst_eq_map_fst, hl_prod]
      · -- h in CayleyBall S_H' n
        use l.map Prod.snd
        refine ⟨by simp only [List.length_map]; omega, ?_, ?_⟩
        · intro s hs
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hs
          have hmem := hl_mem (a, b) hab
          simp only [Set.mem_prod, Prod.inv_mk] at hmem
          rcases hmem with ⟨_, hb⟩ | ⟨_, hb⟩
          · exact Or.inl hb
          · exact Or.inr hb
        · rw [← prod_snd_eq_map_snd, hl_prod]
    -- Use the constants k_G and k_H to build our bound
    use C_G * C_H * (k_G ^ d_G) * (k_H ^ d_H), d_G + d_H
    refine ⟨by positivity, fun n hn => ?_⟩
    have h_ncard : (CayleyBall (S_G' ×ˢ S_H') n).ncard ≤
        (CayleyBall S_G' n).ncard * (CayleyBall S_H' n).ncard := by
      have h_fin_G : (CayleyBall S_G' n).Finite := cayleyBall_finite hS_G'_fin n
      have h_fin_H : (CayleyBall S_H' n).Finite := cayleyBall_finite hS_H'_fin n
      have h_fin_prod : ((CayleyBall S_G' n) ×ˢ (CayleyBall S_H' n)).Finite :=
        h_fin_G.prod h_fin_H
      calc (CayleyBall (S_G' ×ˢ S_H') n).ncard
          ≤ ((CayleyBall S_G' n) ×ˢ (CayleyBall S_H' n)).ncard :=
            Set.ncard_le_ncard (h_subset n) h_fin_prod
        _ = (CayleyBall S_G' n).ncard * (CayleyBall S_H' n).ncard :=
            Set.ncard_prod
    -- Now use the bounds from equivalence of generating sets
    have hG'_bound : GrowthFunction S_G' n ≤ GrowthFunction S_G (n * k_G) := hk_G1 n
    have hH'_bound : GrowthFunction S_H' n ≤ GrowthFunction S_H (n * k_H) := hk_H1 n
    calc (GrowthFunction (S_G' ×ˢ S_H') n : ℝ)
        = (CayleyBall (S_G' ×ˢ S_H') n).ncard := rfl
      _ ≤ (CayleyBall S_G' n).ncard * (CayleyBall S_H' n).ncard := by exact_mod_cast h_ncard
      _ = GrowthFunction S_G' n * GrowthFunction S_H' n := rfl
      _ ≤ GrowthFunction S_G (n * k_G) * GrowthFunction S_H (n * k_H) := by
          apply mul_le_mul <;> [exact_mod_cast hG'_bound; exact_mod_cast hH'_bound;
            simp only [Nat.cast_nonneg]; simp only [Nat.cast_nonneg]]
      _ ≤ (C_G * (n * k_G : ℕ) ^ d_G) * (C_H * (n * k_H : ℕ) ^ d_H) := by
          apply mul_le_mul
          · exact hbound_G (n * k_G) (Nat.mul_pos hn hk_G_pos)
          · exact hbound_H (n * k_H) (Nat.mul_pos hn hk_H_pos)
          · simp only [Nat.cast_nonneg]
          · positivity
      _ = C_G * C_H * (k_G ^ d_G) * (k_H ^ d_H) * n ^ (d_G + d_H) := by
          push_cast
          ring

/-! ## Abelian groups have polynomial growth -/

/-- Every finitely generated abelian group has polynomial growth.

The proof uses the structure theorem: every f.g. abelian group is isomorphic to
Z^r x T where T is a finite abelian group. Since:
- Z^r has polynomial growth (zn_hasPolynomialGrowth)
- Finite groups have polynomial growth (finite_hasPolynomialGrowth)
- Products preserve polynomial growth (hasPolynomialGrowth_prod)

The growth degree equals the torsion-free rank r. -/
theorem commGroup_hasPolynomialGrowth {G : Type*} [CommGroup G] [Group.FG G] :
    HasPolynomialGrowth G := by
  -- Use the structure theorem for f.g. abelian groups
  -- G ≃* (j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ e i)))
  obtain ⟨ι, j, fι, fj, p, hp, e, ⟨φ⟩⟩ := CommGroup.equiv_free_prod_prod_multiplicative_zmod G
  haveI : Fintype j := fj
  haveI : Fintype ι := fι
  -- The first factor (j → Multiplicative ℤ) has polynomial growth
  have h1 : HasPolynomialGrowth (j → Multiplicative ℤ) := by
    let m := Fintype.card j
    -- Build equivalence (j → Multiplicative ℤ) ≃* Multiplicative (Fin m → ℤ)
    let f : j ≃ Fin m := Fintype.equivFin j
    let e_all : (j → Multiplicative ℤ) ≃* Multiplicative (Fin m → ℤ) :=
      { toFun := fun g => Multiplicative.ofAdd (fun i => Multiplicative.toAdd (g (f.symm i))),
        invFun := fun h => fun j' => Multiplicative.ofAdd (Multiplicative.toAdd h (f j')),
        left_inv := fun g => by ext j'; simp,
        right_inv := fun h => by ext i; simp,
        map_mul' := fun g g' => by
          apply Multiplicative.toAdd.injective
          funext i
          simp only [toAdd_mul, Pi.mul_apply, toAdd_ofAdd, Pi.add_apply] }
    have hzn : HasPolynomialGrowth (Multiplicative (Fin m → ℤ)) := zn_hasPolynomialGrowth m
    exact hasPolynomialGrowth_of_mulEquiv e_all hzn
  -- The second factor is finite, hence has polynomial growth
  have h2 : HasPolynomialGrowth ((i : ι) → Multiplicative (ZMod (p i ^ e i))) := by
    -- Each p i is prime, so p i ^ e i > 0
    haveI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
    haveI : ∀ i, NeZero (p i ^ e i) := fun i => inferInstance
    haveI : ∀ i, Fintype (ZMod (p i ^ e i)) := fun i => ZMod.fintype (p i ^ e i)
    haveI : ∀ i, Finite (Multiplicative (ZMod (p i ^ e i))) := fun i => inferInstance
    haveI : Finite ((i : ι) → Multiplicative (ZMod (p i ^ e i))) := Pi.finite
    exact finite_hasPolynomialGrowth
  -- The product has polynomial growth
  have hprod : HasPolynomialGrowth ((j → Multiplicative ℤ) ×
      ((i : ι) → Multiplicative (ZMod (p i ^ e i)))) :=
    hasPolynomialGrowth_prod h1 h2
  -- Transfer through the equivalence
  exact hasPolynomialGrowth_of_mulEquiv φ hprod

end

end Gromov.PolynomialGrowth
