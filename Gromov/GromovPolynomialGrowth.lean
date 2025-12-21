/-
Copyright 2025 The Formal Conjectures Authors.
SPDX-License-Identifier: Apache-2.0

Gromov's theorem on groups of polynomial growth.
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Archimedean

namespace GromovPolynomialGrowth

open Filter

variable {G : Type*} [Group G]

/-- The Cayley ball of radius `n` with respect to generating set `S`:
    elements expressible as products of at most `n` generators or their inverses. -/
def CayleyBall (S : Set G) (n : ℕ) : Set G :=
  {g : G | ∃ (l : List G), l.length ≤ n ∧ (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) ∧ l.prod = g}

theorem cayleyBall_zero (S : Set G) :
    CayleyBall S 0 = {1} := by simp [CayleyBall]

lemma cayleyBall_finite {S : Set G} (hS : S.Finite) (n : ℕ) : (CayleyBall S n).Finite := by
  have hu : (S ∪ (·)⁻¹ '' S).Finite := hS.union (by simpa using hS.preimage inv_injective.injOn)
  have hf (m : ℕ) : {f : Fin m → G | ∀ i, f i ∈ S ∨ (f i)⁻¹ ∈ S}.Finite := by
    simpa using Set.Finite.pi' fun _ ↦ hu
  have : {l : List G | l.length ≤ n ∧ ∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S}.Finite :=
    ((Set.finite_le_nat n).biUnion fun m _ ↦ (hf m).image List.ofFn).subset
      fun l ⟨hl, hlS⟩ ↦ Set.mem_biUnion hl ⟨fun i ↦ l[i], by aesop⟩
  exact (this.image List.prod).subset fun _ _ ↦ by aesop (add simp [CayleyBall])

/-- The growth function counts elements in the Cayley ball of radius `n`. -/
noncomputable def GrowthFunction (S : Set G) (n : ℕ) : ℕ :=
  (CayleyBall S n).ncard

theorem growthFunction_zero (S : Set G) :
    GrowthFunction S 0 = 1 := by
  simp [GrowthFunction, CayleyBall]

lemma one_mem_cayleyBall (S : Set G) (n : ℕ) :
    1 ∈ CayleyBall S n := by
  simp only [CayleyBall, Set.mem_setOf_eq]
  use ∅
  simp

lemma cayleyBall_monotone (S : Set G) {m n : ℕ} (h : m ≤ n) :
    CayleyBall S m ⊆ CayleyBall S n := by
  simp only [CayleyBall, Set.setOf_subset_setOf, forall_exists_index, and_imp]
  exact fun g l lLength LSubS lProdG ↦ ⟨l, by linarith, LSubS, lProdG⟩

lemma cayleyBall_mul (S : Set G) {g h : G} {m n : ℕ}
    (hg : g ∈ CayleyBall S m) (hh : h ∈ CayleyBall S n) :
    g * h ∈ CayleyBall S (m + n) := by
  simp only [CayleyBall, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨lg, lgLength, lgSubS, lgProd⟩ := hg
  obtain ⟨lh, lhLength, lhSubS, lhProd⟩ := hh
  refine ⟨lg ++ lh, ?_, ?_, by simp [lhProd, lgProd]⟩
  · simp only [List.length_append]
    linarith
  · intro s sIn
    simp only [List.mem_append] at sIn
    cases sIn with
    | inl h => simp [lgSubS s h]
    | inr h => simp [lhSubS s h]

lemma cayleyBall_inv (S : Set G) {g : G} {n : ℕ}
    (hg : g ∈ CayleyBall S n) :
    g⁻¹ ∈ CayleyBall S n := by
  simp only [CayleyBall, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨lg, lgLength, lgSubS, lgProd⟩ := hg
  refine ⟨lg.reverse.map (·⁻¹), by simp [lgLength], ?_,
    by simp [List.prod_inv_reverse, lgProd.symm]⟩
  intro s sIn
  simp only [List.map_reverse, List.mem_reverse, List.mem_map, inv_involutive,
    Function.Involutive.exists_mem_and_apply_eq_iff] at sIn
  have := lgSubS s⁻¹ sIn
  simp only [inv_inv] at this
  exact this.symm

lemma mem_cayleyBall_one_of_mem {S : Set G} {g : G} (hg : g ∈ S) : g ∈ CayleyBall S 1 :=
  ⟨[g], by simp_all⟩

lemma exists_cayleyBall_mem_of_closure_eq_top {S : Set G} (h : Subgroup.closure S = ⊤) (g : G) :
    ∃ n, g ∈ CayleyBall S n := by
  induction h ▸ Subgroup.mem_top g using Subgroup.closure_induction with
  | mem => exact ⟨1, mem_cayleyBall_one_of_mem ‹_›⟩
  | one => exact ⟨0, one_mem_cayleyBall ..⟩
  | mul _ _ _ _ hg₁ hg₂ =>
    obtain ⟨n₁, hn₁⟩ := hg₁
    obtain ⟨n₂, hn₂⟩ := hg₂
    exact ⟨n₁ + n₂, cayleyBall_mul S hn₁ hn₂⟩
  | inv _ _ hg =>
    obtain ⟨n, hn⟩ := hg
    exact ⟨n, cayleyBall_inv S hn⟩

theorem tendsto_atTop_growthFunction_of_infinite [Infinite G] {S : Set G} (hS : S.Finite)
    (h : Subgroup.closure S = ⊤) : atTop.Tendsto (GrowthFunction S) atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  -- For any bound b, find n such that the ball has ≥ b elements
  obtain ⟨elems, helems⟩ := Infinite.exists_subset_card_eq G b
  choose n hn using fun (x : elems) ↦ exists_cayleyBall_mem_of_closure_eq_top h x.1
  use Finset.sup (Finset.univ : Finset elems) n
  intro m hm
  have hsub : (elems : Set G) ⊆ CayleyBall S m := fun x hx ↦ by
    have := hn ⟨x, hx⟩
    exact cayleyBall_monotone S (le_trans (Finset.le_sup (Finset.mem_univ _)) hm) this
  calc b = elems.card := helems.symm
    _ = (elems : Set G).ncard := (Set.ncard_coe_finset elems).symm
    _ ≤ (CayleyBall S m).ncard := Set.ncard_le_ncard hsub (cayleyBall_finite hS m)
    _ = GrowthFunction S m := rfl

theorem growthFunction_not_polynomial_of_infinite [Infinite G] {S : Set G} (hS : S.Finite)
    (h : Subgroup.closure S = ⊤) {C : ℝ} (d : ℕ) :
    ∃ (n : ℕ), C * (n : ℝ) ^ d < (GrowthFunction S n : ℝ) := by
  by_cases hd : d = 0
  · obtain ⟨n, _, hn⟩ := exists_lt_of_tendsto_atTop (tendsto_atTop_growthFunction_of_infinite hS h)
      0 ⌈C⌉₊
    use n
    simp only [hd, pow_zero, mul_one]
    calc C ≤ ⌈C⌉₊ := Nat.le_ceil C
      _ < GrowthFunction S n := by exact_mod_cast hn
  · use 0
    simp only [CharP.cast_eq_zero, ne_eq, hd, not_false_eq_true, zero_pow, mul_zero,
      Nat.cast_pos, growthFunction_zero]
    norm_num

variable (G)

/-- A group has polynomial growth if there exists a finite generating set `S` such that
    the growth function is bounded by a polynomial. -/
def HasPolynomialGrowth : Prop :=
  ∃ (S : Set G), Set.Finite S ∧ Subgroup.closure S = ⊤ ∧
    ∃ (C : ℝ) (d : ℕ), C > 0 ∧
    ∀ n > 0, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d

end GromovPolynomialGrowth
