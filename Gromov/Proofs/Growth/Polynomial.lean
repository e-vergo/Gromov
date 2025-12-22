module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Schreier
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Set.Pi
public import Mathlib.Order.Interval.Finset.Basic
public import Gromov.Proofs.Growth.GromovMain
public import Gromov.Definitions.GrowthDegree

set_option linter.style.longLine false

namespace Gromov.PolynomialGrowth

public section

open Gromov Filter Set

variable {G : Type*} [Group G]

/-! ## Asymptotic Definitions -/

theorem isPolynomiallyBounded_of_le {f : ℕ → ℕ} {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂)
    (h : IsPolynomiallyBounded f d₁) : IsPolynomiallyBounded f d₂ := by
  obtain ⟨C, hC_pos, hC⟩ := h
  refine ⟨C, hC_pos, fun n hn => ?_⟩
  have hpow : (n : ℝ) ^ d₁ ≤ (n : ℝ) ^ d₂ := by
    have h1 : (n : ℕ) ^ d₁ ≤ n ^ d₂ := Nat.pow_le_pow_right (Nat.one_le_of_lt hn) hd
    calc (n : ℝ) ^ d₁ = ((n : ℕ) ^ d₁ : ℕ) := by norm_cast
      _ ≤ ((n : ℕ) ^ d₂ : ℕ) := by exact_mod_cast h1
      _ = (n : ℝ) ^ d₂ := by norm_cast
  calc (f n : ℝ) ≤ C * (n : ℝ) ^ d₁ := hC n hn
    _ ≤ C * (n : ℝ) ^ d₂ := by apply mul_le_mul_of_nonneg_left hpow (le_of_lt hC_pos)

theorem growthDegree_le_of_isPolynomiallyBounded {f : ℕ → ℕ} {d : ℕ}
    (h : IsPolynomiallyBounded f d) : GrowthDegree f ≤ d := by
  simp only [GrowthDegree]
  exact Nat.sInf_le h

/-! ## Independence of Generating Set -/

/-- If every element of S₁ lies in the Cayley ball of radius k with respect to S₂,
    then the Cayley ball of radius n with respect to S₁ is contained in the
    Cayley ball of radius n*k with respect to S₂. -/
lemma cayleyBall_subset_of_generators_in_ball {S₁ S₂ : Set G} {k : ℕ}
    (h : ∀ s ∈ S₁, s ∈ CayleyBall S₂ k) (n : ℕ) :
    CayleyBall S₁ n ⊆ CayleyBall S₂ (n * k) := by
  -- The key idea: each generator in S₁ can be expressed using at most k elements from S₂,
  -- so a word of length n in S₁ gives a word of length at most n*k in S₂
  intro g hg
  -- g is in CayleyBall S₁ n, so there exists a list of generators from S₁ (or inverses)
  simp only [CayleyBall, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hg
  -- We need to show g is in CayleyBall S₂ (n * k)
  -- We prove by induction on the list l
  induction l generalizing g n with
  | nil =>
    simp only [List.prod_nil] at hl_prod
    subst hl_prod
    exact ⟨[], by simp⟩
  | cons x xs ih =>
    simp only [List.prod_cons] at hl_prod
    -- x is either in S₁ or x⁻¹ is in S₁
    have hx_mem : x ∈ S₁ ∨ x⁻¹ ∈ S₁ := hl_mem x (List.mem_cons.mpr (Or.inl rfl))
    -- Get the representation of x in CayleyBall S₂ k
    have hx_ball : x ∈ CayleyBall S₂ k := by
      cases hx_mem with
      | inl hx => exact h x hx
      | inr hxinv =>
        have hinv_ball := h x⁻¹ hxinv
        have := cayleyBall_inv S₂ hinv_ball
        simp only [inv_inv] at this
        exact this
    -- xs.prod is in CayleyBall S₁ xs.length ⊆ CayleyBall S₂ (xs.length * k)
    have hxs_len : xs.length ≤ n - 1 := by
      simp only [List.length_cons] at hl_len
      omega
    have hxs_mem : ∀ s ∈ xs, s ∈ S₁ ∨ s⁻¹ ∈ S₁ := fun s hs =>
      hl_mem s (List.mem_cons.mpr (Or.inr hs))
    -- Get the representation of xs.prod in CayleyBall S₂
    have hxs_ball : xs.prod ∈ CayleyBall S₂ ((n - 1) * k) := by
      have := ih (n - 1) hxs_len hxs_mem rfl
      simp only [CayleyBall, Set.mem_setOf_eq] at this ⊢
      exact this
    -- Use cayleyBall_mul
    have hprod : x * xs.prod ∈ CayleyBall S₂ (k + (n - 1) * k) :=
      cayleyBall_mul S₂ hx_ball hxs_ball
    -- Show k + (n-1)*k ≤ n*k
    have hle : k + (n - 1) * k ≤ n * k := by
      cases n with
      | zero => simp only [List.length_cons, Nat.add_one_le_iff] at hl_len; omega
      | succ m => simp only [Nat.add_sub_cancel]; ring_nf; rfl
    rw [← hl_prod]
    exact cayleyBall_monotone S₂ hle hprod

/-- The growth function with respect to S₁ is bounded by the growth function with
    respect to S₂ (with scaled radius) if S₁ generators are in the S₂ ball. -/
theorem growthFunction_le_of_generators_in_ball {S₁ S₂ : Set G} (hS₂ : S₂.Finite) {k : ℕ}
    (h : ∀ s ∈ S₁, s ∈ CayleyBall S₂ k) (n : ℕ) :
    GrowthFunction S₁ n ≤ GrowthFunction S₂ (n * k) := by
  simp only [GrowthFunction]
  apply ncard_le_ncard
  · exact cayleyBall_subset_of_generators_in_ball h n
  · exact cayleyBall_finite hS₂ (n * k)

/-- Two finite generating sets give equivalent growth rates: the growth function
    with respect to one is polynomially equivalent to the growth function with
    respect to the other. -/
theorem growth_equivalent_of_generating_sets {S₁ S₂ : Set G}
    (hS₁ : S₁.Finite) (hS₂ : S₂.Finite)
    (hgen₁ : Subgroup.closure S₁ = ⊤) (hgen₂ : Subgroup.closure S₂ = ⊤) :
    ∃ (k₁ k₂ : ℕ), k₁ > 0 ∧ k₂ > 0 ∧
      (∀ n, GrowthFunction S₁ n ≤ GrowthFunction S₂ (n * k₁)) ∧
      (∀ n, GrowthFunction S₂ n ≤ GrowthFunction S₁ (n * k₂)) := by
  -- For each generator s in S₁, find the radius at which s is in CayleyBall S₂
  have hex₁ : ∀ s : G, ∃ r, s ∈ CayleyBall S₂ r :=
    fun s => exists_cayleyBall_mem_of_closure_eq_top hgen₂ s
  have hex₂ : ∀ s : G, ∃ r, s ∈ CayleyBall S₁ r :=
    fun s => exists_cayleyBall_mem_of_closure_eq_top hgen₁ s
  -- Choose radius functions using classical choice
  choose r₁ hr₁ using hex₁
  choose r₂ hr₂ using hex₂
  -- Define k₁ as the max of r₁ over S₁ (plus 1 to ensure positivity)
  let k₁ := hS₁.toFinset.sup r₁ + 1
  let k₂ := hS₂.toFinset.sup r₂ + 1
  use k₁, k₂
  refine ⟨Nat.succ_pos _, Nat.succ_pos _, ?_, ?_⟩
  · -- Show ∀ n, GrowthFunction S₁ n ≤ GrowthFunction S₂ (n * k₁)
    intro n
    apply growthFunction_le_of_generators_in_ball hS₂
    intro s hs
    have hs_mem : s ∈ hS₁.toFinset := hS₁.mem_toFinset.mpr hs
    have hle : r₁ s ≤ hS₁.toFinset.sup r₁ := Finset.le_sup hs_mem
    exact cayleyBall_monotone S₂ (Nat.le_add_right _ 1 |>.trans' hle) (hr₁ s)
  · -- Show ∀ n, GrowthFunction S₂ n ≤ GrowthFunction S₁ (n * k₂)
    intro n
    apply growthFunction_le_of_generators_in_ball hS₁
    intro s hs
    have hs_mem : s ∈ hS₂.toFinset := hS₂.mem_toFinset.mpr hs
    have hle : r₂ s ≤ hS₂.toFinset.sup r₂ := Finset.le_sup hs_mem
    exact cayleyBall_monotone S₁ (Nat.le_add_right _ 1 |>.trans' hle) (hr₂ s)

/-- Polynomial growth is independent of the choice of finite generating set. -/
theorem hasPolynomialGrowth_iff_of_generating_sets {S₁ S₂ : Set G}
    (hS₁ : S₁.Finite) (hS₂ : S₂.Finite)
    (hgen₁ : Subgroup.closure S₁ = ⊤) (hgen₂ : Subgroup.closure S₂ = ⊤) :
    (∃ (C : ℝ) (d : ℕ), C > 0 ∧ ∀ n > 0, (GrowthFunction S₁ n : ℝ) ≤ C * (n : ℝ) ^ d) ↔
    (∃ (C : ℝ) (d : ℕ), C > 0 ∧ ∀ n > 0, (GrowthFunction S₂ n : ℝ) ≤ C * (n : ℝ) ^ d) := by
  obtain ⟨k₁, k₂, hk₁_pos, hk₂_pos, h₁, h₂⟩ := growth_equivalent_of_generating_sets hS₁ hS₂ hgen₁ hgen₂
  constructor
  · -- S₁ polynomial bound implies S₂ polynomial bound
    intro ⟨C, d, hC_pos, hbound⟩
    use C * k₂ ^ d, d
    refine ⟨by positivity, fun n hn => ?_⟩
    have h := h₂ n
    calc (GrowthFunction S₂ n : ℝ) ≤ GrowthFunction S₁ (n * k₂) := by exact_mod_cast h
      _ ≤ C * (n * k₂ : ℕ) ^ d := by
        have hpos : n * k₂ > 0 := Nat.mul_pos hn hk₂_pos
        exact hbound (n * k₂) hpos
      _ = C * ((n : ℝ) * k₂) ^ d := by norm_cast
      _ = C * (n : ℝ) ^ d * (k₂ : ℝ) ^ d := by ring
      _ = C * k₂ ^ d * (n : ℝ) ^ d := by ring
  · -- S₂ polynomial bound implies S₁ polynomial bound
    intro ⟨C, d, hC_pos, hbound⟩
    use C * k₁ ^ d, d
    refine ⟨by positivity, fun n hn => ?_⟩
    have h := h₁ n
    calc (GrowthFunction S₁ n : ℝ) ≤ GrowthFunction S₂ (n * k₁) := by exact_mod_cast h
      _ ≤ C * (n * k₁ : ℕ) ^ d := by
        have hpos : n * k₁ > 0 := Nat.mul_pos hn hk₁_pos
        exact hbound (n * k₁) hpos
      _ = C * ((n : ℝ) * k₁) ^ d := by norm_cast
      _ = C * (n : ℝ) ^ d * (k₁ : ℝ) ^ d := by ring
      _ = C * k₁ ^ d * (n : ℝ) ^ d := by ring

/-! ## Basic Properties -/

/-- A group with polynomial growth is either finite or infinite (dichotomy).
    More precisely, if a group has polynomial growth of degree 0, it is finite. -/
theorem finite_of_polynomial_growth_degree_zero {S : Set G} (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤)
    (h : ∃ C : ℝ, C > 0 ∧ ∀ n > 0, (GrowthFunction S n : ℝ) ≤ C) :
    Finite G := by
  -- If growth is bounded by a constant C, the group has at most C elements
  obtain ⟨C, hC_pos, hC⟩ := h
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  -- The growth function tends to infinity for infinite groups
  have htend := @tendsto_atTop_growthFunction_of_infinite G _ hinf S hS hgen
  rw [tendsto_atTop_atTop] at htend
  obtain ⟨N, hN⟩ := htend (⌈C⌉₊ + 1)
  rcases Nat.eq_zero_or_pos N with hN_zero | hN_pos
  · subst hN_zero
    have hgrow := hN 1 (by omega)
    have hC1 := hC 1 Nat.one_pos
    have h1 : (⌈C⌉₊ + 1 : ℕ) ≤ GrowthFunction S 1 := hgrow
    have h2 : (⌈C⌉₊ + 1 : ℝ) ≤ GrowthFunction S 1 := by exact_mod_cast h1
    linarith [Nat.le_ceil C]
  · have hbound := hC N hN_pos
    have hgrow := hN N (le_refl N)
    have h1 : (⌈C⌉₊ + 1 : ℝ) ≤ GrowthFunction S N := by exact_mod_cast hgrow
    have h2 : (⌈C⌉₊ : ℝ) + 1 ≤ C := calc
      (⌈C⌉₊ : ℝ) + 1 ≤ GrowthFunction S N := h1
      _ ≤ C := by simpa using hbound
    linarith [Nat.le_ceil C]

/-- Polynomial growth is preserved under passing to finite-index subgroups. -/
theorem hasPolynomialGrowth_of_finiteIndex_subgroup
    (H : Subgroup G) (hH : H.FiniteIndex)
    (hG : HasPolynomialGrowth G) : HasPolynomialGrowth H := by
  -- The subgroup H inherits polynomial growth from G
  -- Key idea: H is finitely generated (Schreier) and each H-generator is
  -- in some bounded G-ball, so growth is bounded
  obtain ⟨S_G, hS_G_fin, hS_G_gen, C, d, hC_pos, hbound⟩ := hG
  -- H is finitely generated by Schreier's lemma
  haveI : Group.FG G := ⟨⟨hS_G_fin.toFinset, by simp [hS_G_gen]⟩⟩
  haveI hH_fg : Group.FG H := @Subgroup.fg_of_index_ne_zero G _ H _ hH
  obtain ⟨S_H_set, hS_H_gen, hS_H_fin⟩ := Group.fg_iff.mp hH_fg
  -- Each generator in S_H is in the G-ball of some radius k
  have h_in_ball : ∃ k > 0, ∀ s ∈ S_H_set, (s : G) ∈ CayleyBall S_G k := by
    -- Each element of the finite set S_H is in some G-ball
    have h : ∀ s : H, ∃ k, (s : G) ∈ CayleyBall S_G k := fun s =>
      exists_cayleyBall_mem_of_closure_eq_top hS_G_gen (s : G)
    choose f hf using h
    -- Take the maximum over the finite set
    by_cases hne : S_H_set.Nonempty
    · have hfin : (S_H_set.image (fun s => f s)).Finite := hS_H_fin.image _
      let k := hfin.toFinset.sup id + 1
      use k
      constructor
      · omega
      · intro s hs
        have hk : f s ≤ k - 1 := by
          have hmem : f s ∈ hfin.toFinset := by
            simp only [Set.Finite.mem_toFinset, Set.mem_image]
            exact ⟨s, hs, rfl⟩
          have hle : f s ≤ hfin.toFinset.sup id := Finset.le_sup (f := id) hmem
          omega
        exact cayleyBall_monotone S_G (by omega : f s ≤ k) (hf s)
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      use 1
      constructor
      · omega
      · intro s hs
        rw [hne] at hs
        exact hs.elim
  obtain ⟨k, hk_pos, h_gen_bound⟩ := h_in_ball
  -- Now we have that the H-ball is contained in the G-ball with stretched radius
  use S_H_set
  refine ⟨hS_H_fin, hS_H_gen, ?_⟩
  use C * k ^ d, d
  refine ⟨by positivity, ?_⟩
  intro n hn
  -- CayleyBall for H elements can be embedded into CayleyBall for G
  have h_bound : (CayleyBall S_H_set n).ncard ≤ (CayleyBall S_G (n * k)).ncard := by
    -- Define the embedding from CayleyBall S_H n to CayleyBall S_G (n * k)
    -- Strategy: show image under Subtype.val is contained in target, then use ncard bounds
    have h_image_subset : (Subtype.val : H → G) '' CayleyBall S_H_set n ⊆ CayleyBall S_G (n * k) := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := hg
      simp only [CayleyBall, Set.mem_setOf_eq] at hh ⊢
      obtain ⟨l, hl_len, hl_gen, hl_prod⟩ := hh
      -- Build the G-witness by expanding each H-generator
      -- Each element of l can be written using at most k elements of S_G
      -- So the total length is at most n * k
      induction l generalizing h n with
      | nil =>
        simp only [List.prod_nil] at hl_prod
        subst hl_prod
        exact ⟨[], by simp, by simp, by simp⟩
      | cons x xs ih =>
        simp only [List.prod_cons] at hl_prod
        simp only [List.length_cons, Nat.add_one_le_iff] at hl_len
        have hx_gen : x ∈ S_H_set ∨ x⁻¹ ∈ S_H_set := hl_gen x List.mem_cons_self
        have hxs_gen : ∀ s ∈ xs, s ∈ S_H_set ∨ s⁻¹ ∈ S_H_set := fun s hs =>
          hl_gen s (List.mem_cons_of_mem x hs)
        -- x is in k-ball of G (or its inverse is)
        have hx_in_ball : (x : G) ∈ CayleyBall S_G k := by
          cases hx_gen with
          | inl hx => exact h_gen_bound x hx
          | inr hxinv =>
            have hinv : (x⁻¹ : G) ∈ CayleyBall S_G k := h_gen_bound x⁻¹ hxinv
            have hinv' := cayleyBall_inv S_G hinv
            simp only [inv_inv] at hinv'
            exact hinv'
        -- xs.prod is in the ((n-1)*k)-ball of G by IH
        -- We need n - 1 > 0, which follows from xs.length < n
        have hn1 : n - 1 > 0 ∨ n = 1 := by omega
        rcases hn1 with hn1_pos | hn1_eq
        · -- Case n > 1, so n - 1 > 0
          have hxs_le : xs.length ≤ n - 1 := Nat.le_sub_one_of_lt hl_len
          have ih_hyp := ih (n - 1) hn1_pos (xs.prod) hxs_le hxs_gen rfl
          -- Combine: x * xs.prod is in the n*k ball
          have hmul := cayleyBall_mul S_G hx_in_ball ih_hyp
          rw [← hl_prod]
          simp only [Subgroup.coe_mul]
          apply cayleyBall_monotone S_G _ hmul
          have : n ≥ 2 := by omega
          have heq : k + (n - 1) * k = n * k := by
            have hn2 : 1 + (n - 1) = n := by omega
            calc k + (n - 1) * k = k * 1 + k * (n - 1) := by ring
              _ = k * (1 + (n - 1)) := by ring
              _ = k * n := by rw [hn2]
              _ = n * k := by ring
          linarith
        · -- Case n = 1, so xs must be empty
          subst hn1_eq
          simp only [Nat.lt_one_iff, List.length_eq_zero_iff] at hl_len
          subst hl_len
          simp only [List.prod_nil, mul_one] at hl_prod
          rw [← hl_prod]
          -- hx_in_ball : ↑x ∈ CayleyBall S_G k gives us the witness
          simp only [CayleyBall, Set.mem_setOf_eq] at hx_in_ball ⊢
          obtain ⟨lx, hlx_len, hlx_gen, hlx_prod⟩ := hx_in_ball
          exact ⟨lx, by omega, hlx_gen, hlx_prod⟩
    -- Now use the image subset and injectivity to bound ncard
    calc (CayleyBall S_H_set n).ncard
        = ((Subtype.val : H → G) '' CayleyBall S_H_set n).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (CayleyBall S_G (n * k)).ncard :=
          Set.ncard_le_ncard h_image_subset (cayleyBall_finite hS_G_fin (n * k))
  -- Now bound the growth function
  calc (GrowthFunction S_H_set n : ℝ)
      = (CayleyBall S_H_set n).ncard := rfl
    _ ≤ (CayleyBall S_G (n * k)).ncard := by exact_mod_cast h_bound
    _ = GrowthFunction S_G (n * k) := rfl
    _ ≤ C * (n * k : ℕ) ^ d := by
        have hpos : n * k > 0 := Nat.mul_pos hn hk_pos
        exact hbound (n * k) hpos
    _ = C * k ^ d * n ^ d := by rw [Nat.cast_mul, mul_pow]; ring

/-- Polynomial growth is preserved under quotients by finite normal subgroups. -/
theorem hasPolynomialGrowth_of_quotient_by_finite
    (N : Subgroup G) [N.Normal] (_ : (N : Set G).Finite)
    (hG : HasPolynomialGrowth G) : HasPolynomialGrowth (G ⧸ N) := by
  -- Get the generating set and polynomial bound from G's growth
  obtain ⟨S, hS_fin, hS_gen, C, d, hC_pos, hbound⟩ := hG
  -- Use π(S) as generating set for G/N, where π is the quotient map
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  use π '' S
  refine ⟨hS_fin.image π, ?_, C, d, hC_pos, ?_⟩
  -- Show π(S) generates G/N
  · -- Use that closure commutes with surjective maps
    have hsurj := QuotientGroup.mk'_surjective N
    rw [← Subgroup.map_top_of_surjective π hsurj]
    rw [← hS_gen]
    exact (MonoidHom.map_closure π S).symm
  -- Show growth bound
  · intro n hn
    -- The Cayley ball in G/N is the image of the Cayley ball in G
    -- First show: CayleyBall (π '' S) n ⊆ π '' CayleyBall S n
    have h_subset : CayleyBall (π '' S) n ⊆ π '' CayleyBall S n := by
      intro x hx
      simp only [CayleyBall, Set.mem_setOf_eq] at hx
      obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hx
      -- Each element of l is π(s) or (π(s))⁻¹ for some s ∈ S
      -- So we can lift l to a list in G
      -- Key lemma: if l has elements in π(S) ∪ π(S)⁻¹ and length ≤ m, then
      -- l.prod is the image of some element in CayleyBall S m
      suffices h_main : ∀ (l : List (G ⧸ N)) (m : ℕ),
          l.length ≤ m →
          (∀ y ∈ l, y ∈ π '' S ∨ y⁻¹ ∈ π '' S) →
          ∃ g : G, g ∈ CayleyBall S m ∧ π g = l.prod by
        obtain ⟨g, hg_ball, hg_eq⟩ := h_main l n hl_len hl_mem
        exact ⟨g, hg_ball, hl_prod ▸ hg_eq⟩
      intro l
      induction l with
      | nil =>
        intro m _ _
        exact ⟨1, one_mem_cayleyBall S m, map_one π⟩
      | cons y ys ih =>
        intro m hlen hmem
        -- Get preimage for y
        have hy_mem := hmem y List.mem_cons_self
        have hys_mem : ∀ z ∈ ys, z ∈ π '' S ∨ z⁻¹ ∈ π '' S :=
          fun z hz => hmem z (List.mem_cons.mpr (Or.inr hz))
        rcases hy_mem with ⟨s, hs, rfl⟩ | ⟨s, hs, hinv⟩
        · -- y = π s for some s ∈ S
          -- By IH, g with π g = ys.prod and g ∈ CayleyBall S (m-1) exists
          have hys_len : ys.length ≤ m - 1 := by
            simp only [List.length_cons] at hlen; omega
          obtain ⟨g_rest, hg_rest_ball, hg_rest_eq⟩ := ih (m - 1) hys_len hys_mem
          have hs_ball : s ∈ CayleyBall S 1 := mem_cayleyBall_one_of_mem hs
          have hprod : s * g_rest ∈ CayleyBall S (1 + (m - 1)) :=
            cayleyBall_mul S hs_ball hg_rest_ball
          have h1m : 1 + (m - 1) ≤ m := by
            cases m with
            | zero => simp only [List.length_cons] at hlen; omega
            | succ k => omega
          exact ⟨s * g_rest, cayleyBall_monotone S h1m hprod, by simp [hg_rest_eq]⟩
        · -- y⁻¹ = π s for some s ∈ S, so y = π(s⁻¹)
          have hys_len : ys.length ≤ m - 1 := by
            simp only [List.length_cons] at hlen; omega
          obtain ⟨g_rest, hg_rest_ball, hg_rest_eq⟩ := ih (m - 1) hys_len hys_mem
          have hsinv_ball : s⁻¹ ∈ CayleyBall S 1 := by
            have := mem_cayleyBall_one_of_mem hs
            exact cayleyBall_inv S this
          have hprod : s⁻¹ * g_rest ∈ CayleyBall S (1 + (m - 1)) :=
            cayleyBall_mul S hsinv_ball hg_rest_ball
          have h1m : 1 + (m - 1) ≤ m := by
            cases m with
            | zero => simp only [List.length_cons] at hlen; omega
            | succ k => omega
          refine ⟨s⁻¹ * g_rest, cayleyBall_monotone S h1m hprod, ?_⟩
          simp only [List.prod_cons, map_mul, map_inv, hg_rest_eq, hinv, inv_inv]
    -- ncard of image is at most ncard of original
    have h_ncard : (CayleyBall (π '' S) n).ncard ≤ (CayleyBall S n).ncard := by
      have hfin_ball : (CayleyBall S n).Finite := cayleyBall_finite hS_fin n
      calc (CayleyBall (π '' S) n).ncard
          ≤ (π '' CayleyBall S n).ncard := Set.ncard_le_ncard h_subset (hfin_ball.image π)
        _ ≤ (CayleyBall S n).ncard := Set.ncard_image_le hfin_ball
    calc (GrowthFunction (π '' S) n : ℝ)
        = (CayleyBall (π '' S) n).ncard := rfl
      _ ≤ (CayleyBall S n).ncard := by exact_mod_cast h_ncard
      _ = GrowthFunction S n := rfl
      _ ≤ C * n ^ d := hbound n hn

/-! ## Examples -/

/-- Finite groups have polynomial growth of degree 0. -/
theorem finite_hasPolynomialGrowth [Finite G] : HasPolynomialGrowth G := by
  -- Take S to be a finite set generating G
  haveI : Fintype G := Fintype.ofFinite G
  use Set.univ
  refine ⟨Set.finite_univ, ?_, ?_⟩
  · simp only [Subgroup.closure_univ]
  · use Fintype.card G, 0
    refine ⟨Nat.cast_pos.mpr Fintype.card_pos, fun n _ => ?_⟩
    simp only [pow_zero, mul_one]
    -- The growth function is bounded by the cardinality of the group
    have hsub : CayleyBall (Set.univ : Set G) n ⊆ Set.univ := Set.subset_univ _
    have hfin : (Set.univ : Set G).Finite := Set.finite_univ
    have h : (CayleyBall (Set.univ : Set G) n).ncard ≤ Fintype.card G := by
      have h1 : (CayleyBall Set.univ n).ncard ≤ (Set.univ : Set G).ncard :=
        Set.ncard_le_ncard hsub hfin
      simp only [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
      exact h1
    calc (GrowthFunction (Set.univ : Set G) n : ℝ) = (CayleyBall Set.univ n).ncard := rfl
      _ ≤ Fintype.card G := by exact_mod_cast h

/-- Helper lemma: products of ±1 in Multiplicative ℤ -/
private lemma list_prod_pm1 (l : List (Multiplicative ℤ))
    (hl : ∀ s ∈ l, s ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) ∨
                   s⁻¹ ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ))) :
    ∃ k : ℤ, |k| ≤ l.length ∧ l.prod = Multiplicative.ofAdd k := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    have hxs_mem : ∀ s ∈ xs, s ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) ∨
                             s⁻¹ ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) :=
      fun s hs => hl s (List.mem_cons.mpr (Or.inr hs))
    obtain ⟨k', hk'_bound, hk'_prod⟩ := ih hxs_mem
    have hx : x ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) ∨
              x⁻¹ ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) :=
      hl x (List.mem_cons.mpr (Or.inl rfl))
    cases hx with
    | inl hx =>
      simp only [Set.mem_singleton_iff] at hx
      use k' + 1
      constructor
      · simp only [List.length_cons]
        have h1 : |k' + 1| ≤ |k'| + 1 := by
          calc |k' + 1| ≤ |k'| + |1| := abs_add_le k' 1
            _ = |k'| + 1 := by simp
        omega
      · simp only [List.prod_cons, hx, hk'_prod]
        -- Need to show: ofAdd 1 * ofAdd k' = ofAdd (k' + 1)
        -- In Multiplicative, ofAdd a * ofAdd b = ofAdd (a + b)
        change Multiplicative.ofAdd (1 + k') = Multiplicative.ofAdd (k' + 1)
        congr 1
        ring
    | inr hxinv =>
      simp only [Set.mem_singleton_iff] at hxinv
      use k' - 1
      constructor
      · simp only [List.length_cons]
        have h1 : |k' - 1| ≤ |k'| + 1 := by
          have := abs_sub_le k' 0 1
          simp only [ge_iff_le]
          grind
        omega
      · simp only [List.prod_cons, hk'_prod]
        have hx_eq : x = Multiplicative.ofAdd (-1 : ℤ) := by
          have : x⁻¹ = Multiplicative.ofAdd (1 : ℤ) := hxinv
          calc x = (x⁻¹)⁻¹ := by simp
            _ = (Multiplicative.ofAdd (1 : ℤ))⁻¹ := by rw [this]
            _ = Multiplicative.ofAdd (-1 : ℤ) := rfl
        simp only [hx_eq]
        -- Need to show: ofAdd (-1) * ofAdd k' = ofAdd (k' - 1)
        change Multiplicative.ofAdd ((-1 : ℤ) + k') = Multiplicative.ofAdd (k' - 1)
        congr 1
        ring

/-- Helper: The Cayley ball of {ofAdd 1} is contained in {ofAdd k | |k| ≤ n} -/
private lemma cayleyBall_int_subset (n : ℕ) :
    CayleyBall {Multiplicative.ofAdd (1 : ℤ)} n ⊆
      {g | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k} := by
  intro g hg
  simp only [CayleyBall, Set.mem_setOf_eq] at hg
  obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hg
  obtain ⟨k, hk_bound, hk_prod⟩ := list_prod_pm1 l hl_mem
  refine ⟨k, ?_, hk_prod ▸ hl_prod.symm⟩
  calc |k| ≤ l.length := hk_bound
    _ ≤ n := by exact_mod_cast hl_len

/-- Helper: The set {ofAdd k | |k| ≤ n} has cardinality 2n+1 -/
private lemma int_interval_card (n : ℕ) :
    ({g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k}).ncard = 2 * n + 1 := by
  -- This set is the image of [-n, n] under ofAdd
  have h_eq : {g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k} =
              Multiplicative.ofAdd '' {k : ℤ | |k| ≤ n} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro ⟨k, hk, hg⟩
      exact ⟨k, hk, hg.symm⟩
    · intro ⟨k, hk, hg⟩
      exact ⟨k, hk, hg.symm⟩
  rw [h_eq]
  -- ofAdd is injective
  have h_inj : Function.Injective (Multiplicative.ofAdd : ℤ → Multiplicative ℤ) :=
    Multiplicative.ofAdd.injective
  rw [Set.ncard_image_of_injective _ h_inj]
  -- Now we need to count {k : ℤ | |k| ≤ n}
  have h_eq2 : {k : ℤ | |k| ≤ n} = Set.Icc (-n : ℤ) n := by
    ext k; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
  rw [h_eq2]
  -- Use ncard with Fintype
  rw [Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_Icc, Int.card_Icc, sub_neg_eq_add]
  -- Goal is now: ((n : ℤ) + 1 + n).toNat = 2 * n + 1
  have h : (n : ℤ) + 1 + n = (2 * n + 1 : ℕ) := by omega
  rw [h, Int.toNat_natCast]

/-- The additive group of integers Z has polynomial growth of degree 1. -/
theorem int_hasPolynomialGrowth : HasPolynomialGrowth (Multiplicative ℤ) := by
  -- Take S = {1} as the generating set (which is the multiplicative version of 1 in Z)
  use {Multiplicative.ofAdd 1}
  refine ⟨Set.finite_singleton _, ?_, ?_⟩
  · -- {ofAdd 1} generates Multiplicative Z
    ext n
    simp only [Subgroup.mem_top, iff_true]
    -- The closure of {1} is all of Multiplicative Z
    -- because every integer is a sum of 1s and (-1)s
    rw [Subgroup.mem_closure_singleton]
    refine ⟨Multiplicative.toAdd n, ?_⟩
    change Multiplicative.ofAdd (Multiplicative.toAdd n * 1) = n
    simp only [mul_one]
    exact Multiplicative.toAdd.symm_apply_apply n
  · -- Growth is bounded by C * n
    use 3, 1
    refine ⟨by norm_num, fun n hn => ?_⟩
    -- The Cayley ball of radius n contains integers from -n to n
    -- So it has at most 2n + 1 elements
    have h_bound : (CayleyBall {Multiplicative.ofAdd (1 : ℤ)} n).ncard ≤ 2 * n + 1 := by
      -- First prove finiteness of the target set
      have h_fin : ({g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k}).Finite := by
        have h_eq : {g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k} =
                    Multiplicative.ofAdd '' {k : ℤ | |k| ≤ n} := by
          ext g; simp only [Set.mem_setOf_eq, Set.mem_image]
          constructor <;> (intro ⟨k, hk, hg⟩; exact ⟨k, hk, hg.symm⟩)
        rw [h_eq]
        apply Set.Finite.image
        have h_eq2 : {k : ℤ | |k| ≤ n} = Set.Icc (-n : ℤ) n := by
          ext k; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        rw [h_eq2]
        exact Set.finite_Icc (-n : ℤ) n
      calc (CayleyBall {Multiplicative.ofAdd (1 : ℤ)} n).ncard
          ≤ ({g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k}).ncard :=
            Set.ncard_le_ncard (cayleyBall_int_subset n) h_fin
        _ = 2 * n + 1 := int_interval_card n
    simp only [pow_one]
    have hnn : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    calc (GrowthFunction {Multiplicative.ofAdd (1 : ℤ)} n : ℝ)
        = (CayleyBall {Multiplicative.ofAdd (1 : ℤ)} n).ncard := rfl
      _ ≤ 2 * n + 1 := by exact_mod_cast h_bound
      _ ≤ 3 * n := by linarith

/-- Helper: bound on coordinates after multiplying list of generators -/
private lemma list_prod_coord_bound (m : ℕ) (l : List (Multiplicative (Fin m → ℤ)))
    (hl_mem : ∀ s ∈ l, s ∈ (Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}) ∨
        s⁻¹ ∈ (Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}))
    (i : Fin m) : |Multiplicative.toAdd (l.prod) i| ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.prod_cons]
    have hxs_mem : ∀ s ∈ xs, s ∈ (Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}) ∨
        s⁻¹ ∈ (Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}) :=
      fun s hs => hl_mem s (List.mem_cons.mpr (Or.inr hs))
    have ih' : |Multiplicative.toAdd xs.prod i| ≤ xs.length := ih hxs_mem
    have hx := hl_mem x (List.mem_cons.mpr (Or.inl rfl))
    -- x is either ofAdd (Pi.single j 1) or its inverse ofAdd (Pi.single j (-1))
    simp only [Set.mem_image, Set.mem_setOf_eq] at hx
    rcases hx with (⟨_, ⟨j, rfl⟩, rfl⟩ | ⟨_, ⟨j, rfl⟩, hxinv⟩)
    · -- x = ofAdd (Pi.single j 1)
      simp only [toAdd_mul, toAdd_ofAdd]
      have habs : |(Pi.single j (1 : ℤ) : Fin m → ℤ) i| ≤ 1 := by
        simp only [Pi.single_apply]; split_ifs <;> simp
      calc |(Pi.single j (1 : ℤ) : Fin m → ℤ) i + Multiplicative.toAdd xs.prod i|
          ≤ |(Pi.single j (1 : ℤ) : Fin m → ℤ) i| + |Multiplicative.toAdd xs.prod i| := abs_add_le _ _
        _ ≤ 1 + xs.length := by linarith [ih']
        _ = (Multiplicative.ofAdd (Pi.single j (1 : ℤ)) :: xs).length := by simp [add_comm]
    · -- x⁻¹ = ofAdd (Pi.single j 1), so x = ofAdd (Pi.single j (-1))
      have hx_eq : x = Multiplicative.ofAdd (Pi.single j (-1 : ℤ) : Fin m → ℤ) := by
        have : x⁻¹ = Multiplicative.ofAdd (Pi.single j (1 : ℤ) : Fin m → ℤ) := hxinv.symm
        calc x = (x⁻¹)⁻¹ := by simp
          _ = (Multiplicative.ofAdd (Pi.single j (1 : ℤ) : Fin m → ℤ))⁻¹ := by rw [this]
          _ = Multiplicative.ofAdd (Pi.single j (-1 : ℤ) : Fin m → ℤ) := by
              rw [← ofAdd_neg]; congr 1; simp [Pi.single_neg]
      rw [hx_eq]
      simp only [toAdd_mul, toAdd_ofAdd]
      have habs : |(Pi.single j (-1 : ℤ) : Fin m → ℤ) i| ≤ 1 := by
        simp only [Pi.single_apply]; split_ifs <;> simp
      calc |(Pi.single j (-1 : ℤ) : Fin m → ℤ) i + Multiplicative.toAdd xs.prod i|
          ≤ |(Pi.single j (-1 : ℤ) : Fin m → ℤ) i| + |Multiplicative.toAdd xs.prod i| := abs_add_le _ _
        _ ≤ 1 + xs.length := by linarith [ih']
        _ = (x :: xs).length := by simp [add_comm]

/-- Helper: standard basis generates Multiplicative (Fin m → ℤ) -/
private lemma std_basis_closure_eq_top (m : ℕ) :
    Subgroup.closure (Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}) = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  -- We show every element is in the closure by expressing it as a product of basis elements
  -- g = ofAdd f for some f : Fin m → ℤ, and f = Σ_i f(i) * e_i
  -- We'll use induction on the closure to show g is in it
  let S := Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}
  -- Express g as a product of powers of basis elements
  -- g = ofAdd (f 0 * e_0 + f 1 * e_1 + ... + f (m-1) * e_(m-1))
  --   = (ofAdd e_0)^(f 0) * ... * (ofAdd e_(m-1))^(f (m-1))
  have hprod : g = ∏ i : Fin m, (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) ^ (Multiplicative.toAdd g i) := by
    simp only [← ofAdd_zsmul]
    change g = Multiplicative.ofAdd (∑ i : Fin m, (Multiplicative.toAdd g i) • Pi.single i (1 : ℤ))
    ext j
    simp only [toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp only [mul_ite, mul_one, mul_zero]
      split_ifs with h
      · exact (hkj h.symm).elim
      · rfl
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  rw [hprod]
  apply Subgroup.prod_mem
  intro i _
  apply Subgroup.zpow_mem
  apply Subgroup.subset_closure
  simp only [Set.mem_image, Set.mem_setOf_eq]
  exact ⟨Pi.single i 1, ⟨i, rfl⟩, rfl⟩

/-- Z^n (as an additive group, represented multiplicatively) has polynomial growth of degree n. -/
theorem zn_hasPolynomialGrowth (m : ℕ) : HasPolynomialGrowth (Multiplicative (Fin m → ℤ)) := by
  -- For m = 0, the group is trivial (finite)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact finite_hasPolynomialGrowth
  -- The proof uses the standard basis {e_i | i : Fin m} as generating set
  -- where e_i = Pi.single i 1
  use Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}
  refine ⟨?_, ?_, ?_⟩
  · -- The generating set is finite (it has m elements)
    apply Set.Finite.image
    have : {f : Fin m → ℤ | ∃ i, f = Pi.single i 1} = Set.range (fun i => Pi.single i (1 : ℤ)) := by
      ext f; simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]
    rw [this]
    exact Set.finite_range _
  · -- The basis generates the whole group
    exact std_basis_closure_eq_top m
  · -- Growth is bounded by C * r^m
    -- The Cayley ball of radius n has at most (2n+1)^m elements
    -- Each coordinate ranges from -n to n, giving 2n+1 choices per coordinate
    use (3 : ℝ) ^ m, m
    refine ⟨by positivity, fun n hn => ?_⟩
    -- The Cayley ball is contained in {f | ∀ i, |f i| ≤ n}
    have h_subset : CayleyBall (Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}) n ⊆
        {g : Multiplicative (Fin m → ℤ) | ∀ i, |Multiplicative.toAdd g i| ≤ n} := by
      intro g hg
      simp only [CayleyBall, Set.mem_setOf_eq] at hg ⊢
      obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hg
      intro i
      calc |Multiplicative.toAdd g i| = |Multiplicative.toAdd (l.prod) i| := by rw [← hl_prod]
        _ ≤ l.length := list_prod_coord_bound m l hl_mem i
        _ ≤ n := by exact_mod_cast hl_len
    -- The target set has at most (2n+1)^m elements
    have h_fin : ({g : Multiplicative (Fin m → ℤ) | ∀ i, |Multiplicative.toAdd g i| ≤ n}).Finite := by
      have h_bij : {g : Multiplicative (Fin m → ℤ) | ∀ i, |Multiplicative.toAdd g i| ≤ n} =
          Multiplicative.ofAdd '' {f : Fin m → ℤ | ∀ i, |f i| ≤ n} := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro hg
          exact ⟨Multiplicative.toAdd g, hg, Multiplicative.toAdd.symm_apply_apply g⟩
        · rintro ⟨f, hf, rfl⟩
          simp only [toAdd_ofAdd]
          exact hf
      rw [h_bij]
      apply Set.Finite.image
      have h_prod : {f : Fin m → ℤ | ∀ i, |f i| ≤ n} = Set.pi Set.univ (fun _ => {k : ℤ | |k| ≤ n}) := by
        ext f; simp
      rw [h_prod]
      apply Set.Finite.pi
      intro i
      have : {k : ℤ | |k| ≤ n} = Set.Icc (-n : ℤ) n := by
        ext k; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
      rw [this]
      exact Set.finite_Icc _ _
    have h_card : ({g : Multiplicative (Fin m → ℤ) | ∀ i, |Multiplicative.toAdd g i| ≤ n}).ncard ≤ (2 * n + 1) ^ m := by
      -- This set bijects with {f : Fin m → ℤ | ∀ i, |f i| ≤ n}
      -- which has cardinality (2n+1)^m
      have h_bij : {g : Multiplicative (Fin m → ℤ) | ∀ i, |Multiplicative.toAdd g i| ≤ n} =
          Multiplicative.ofAdd '' {f : Fin m → ℤ | ∀ i, |f i| ≤ n} := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro hg
          exact ⟨Multiplicative.toAdd g, hg, Multiplicative.toAdd.symm_apply_apply g⟩
        · rintro ⟨f, hf, rfl⟩
          simp only [toAdd_ofAdd]
          exact hf
      rw [h_bij, Set.ncard_image_of_injective _ Multiplicative.ofAdd.injective]
      -- Now count {f : Fin m → ℤ | ∀ i, |f i| ≤ n}
      have h_prod : {f : Fin m → ℤ | ∀ i, |f i| ≤ n} = Set.pi Set.univ (fun _ => {k : ℤ | |k| ≤ n}) := by
        ext f; simp
      rw [h_prod]
      -- The set is finite as a product of finite sets
      have h_fin_prod : (Set.pi Set.univ fun _ : Fin m => {k : ℤ | |k| ≤ n}).Finite := by
        apply Set.Finite.pi
        intro _
        have h_icc : ({k : ℤ | |k| ≤ n} : Set ℤ) = Set.Icc (-n : ℤ) n := by
          ext k; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        rw [h_icc]
        exact Set.finite_Icc _ _
      rw [Set.ncard_eq_toFinset_card (Set.pi Set.univ fun _ => {k : ℤ | |k| ≤ n}) h_fin_prod]
      -- Convert to piFinset using the Icc set
      have h_icc : ({k : ℤ | |k| ≤ n} : Set ℤ) = Set.Icc (-n : ℤ) n := by
        ext k; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
      have h_eq : h_fin_prod.toFinset =
          Fintype.piFinset fun _ : Fin m => Finset.Icc (-n : ℤ) n := by
        ext f
        simp only [Set.Finite.mem_toFinset, Set.mem_pi, Set.mem_univ, true_implies,
          Fintype.mem_piFinset, Finset.mem_Icc, h_icc, Set.mem_Icc]
      rw [h_eq, Fintype.card_piFinset]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
      have h : (n : ℤ) + 1 - (-n) = 2 * n + 1 := by omega
      simp only [h]
      have h2 : (2 * (n : ℤ) + 1).toNat = 2 * n + 1 := by
        have : (2 * (n : ℤ) + 1) = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this, Int.toNat_natCast]
      rw [h2]
    calc (GrowthFunction (Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}) n : ℝ)
        = (CayleyBall (Multiplicative.ofAdd '' {f : Fin m → ℤ | ∃ i, f = Pi.single i 1}) n).ncard := rfl
      _ ≤ ({g : Multiplicative (Fin m → ℤ) | ∀ i, |Multiplicative.toAdd g i| ≤ n}).ncard := by
          exact_mod_cast Set.ncard_le_ncard h_subset h_fin
      _ ≤ (2 * n + 1) ^ m := by exact_mod_cast h_card
      _ ≤ (3 * n) ^ m := by
          have hn1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn
          have h : (2 * n + 1 : ℕ) ≤ 3 * n := by omega
          exact_mod_cast Nat.pow_le_pow_left h m
      _ = 3 ^ m * n ^ m := by ring

end

end Gromov.PolynomialGrowth
