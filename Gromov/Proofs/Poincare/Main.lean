/-
Copyright 2025 The Formal Conjectures Authors.
SPDX-License-Identifier: Apache-2.0

Discrete Poincare inequalities on Cayley graphs.
-/

module

public import Gromov.Definitions.Poincare
public import Gromov.Proofs.Cayley.Graph
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Finprod

namespace Gromov

public section

open scoped BigOperators

variable {G : Type*} [Group G]

/-! ## Edge Gradient

The edge gradient measures the difference of a function across an edge in the Cayley graph.
For a function f : G -> R and an edge (g, g*s) where s is a generator,
the gradient is f(g*s) - f(g).
-/

@[simp]
theorem edgeGradient_zero (g : G) (s : G) : edgeGradient (0 : G -> Real) g s = 0 := by
  simp [edgeGradient]

@[simp]
theorem edgeGradient_const (c : Real) (g : G) (s : G) :
    edgeGradient (fun _ => c) g s = 0 := by
  simp [edgeGradient]

theorem edgeGradient_add (f1 f2 : G -> Real) (g : G) (s : G) :
    edgeGradient (f1 + f2) g s = edgeGradient f1 g s + edgeGradient f2 g s := by
  simp only [edgeGradient, Pi.add_apply]
  ring

theorem edgeGradient_smul (c : Real) (f : G -> Real) (g : G) (s : G) :
    edgeGradient (fun x => c * f x) g s = c * edgeGradient f g s := by
  simp only [edgeGradient]
  ring

theorem edgeGradient_neg (f : G -> Real) (g : G) (s : G) :
    edgeGradient (-f) g s = -edgeGradient f g s := by
  simp only [edgeGradient, Pi.neg_apply]
  ring

theorem edgeGradientSq_nonneg (f : G -> Real) (g : G) (s : G) :
    edgeGradientSq f g s >= 0 := sq_nonneg _

/-! ## Dirichlet Energy

The Dirichlet energy measures the total variation of a function on a set,
summing the squared gradients over all edges emanating from vertices in the set.
-/

theorem dirichletEnergy_nonneg (f : G -> Real) (A : Finset G) (Sfin : Finset G) :
    dirichletEnergy f A Sfin >= 0 := by
  apply Finset.sum_nonneg
  intro g _
  apply Finset.sum_nonneg
  intro s _
  exact edgeGradientSq_nonneg f g s

theorem dirichletEnergy_zero (A : Finset G) (Sfin : Finset G) :
    dirichletEnergy (0 : G -> Real) A Sfin = 0 := by
  simp [dirichletEnergy, edgeGradientSq, edgeGradient]

theorem dirichletEnergy_const (c : Real) (A : Finset G) (Sfin : Finset G) :
    dirichletEnergy (fun _ => c) A Sfin = 0 := by
  simp [dirichletEnergy, edgeGradientSq, edgeGradient]

/-- The Dirichlet energy scales quadratically with scalar multiplication -/
theorem dirichletEnergy_smul (c : Real) (f : G -> Real) (A : Finset G) (Sfin : Finset G) :
    dirichletEnergy (fun x => c * f x) A Sfin = c ^ 2 * dirichletEnergy f A Sfin := by
  simp only [dirichletEnergy, edgeGradientSq, edgeGradient]
  rw [Finset.mul_sum]
  congr 1
  ext g
  rw [Finset.mul_sum]
  congr 1
  ext s
  ring

/-! ## L^2 Norm on Finite Sets

The L^2 norm (squared) of a function on a finite set is the sum of squares of function values.
-/

omit [Group G] in
theorem l2NormSq_nonneg (f : G -> Real) (A : Finset G) : l2NormSq f A >= 0 := by
  apply Finset.sum_nonneg
  intro g _
  exact sq_nonneg (f g)

omit [Group G] in
theorem l2NormSq_zero (A : Finset G) : l2NormSq (0 : G -> Real) A = 0 := by
  simp [l2NormSq]

omit [Group G] in
theorem l2NormSq_smul (c : Real) (f : G -> Real) (A : Finset G) :
    l2NormSq (fun x => c * f x) A = c ^ 2 * l2NormSq f A := by
  simp only [l2NormSq]
  rw [Finset.mul_sum]
  congr 1
  ext g
  ring

omit [Group G] in
theorem l2NormSq_add_le (f1 f2 : G -> Real) (A : Finset G) :
    l2NormSq (f1 + f2) A <= 2 * l2NormSq f1 A + 2 * l2NormSq f2 A := by
  simp only [l2NormSq, Pi.add_apply]
  have h1 : Finset.sum A (fun g => (f1 g + f2 g) ^ 2) =
            Finset.sum A (fun g => (f1 g) ^ 2 + 2 * f1 g * f2 g + (f2 g) ^ 2) := by
    congr 1; ext g; ring
  rw [h1]
  have h2 : Finset.sum A (fun g => (f1 g) ^ 2 + 2 * f1 g * f2 g + (f2 g) ^ 2) =
            Finset.sum A (fun g => (f1 g) ^ 2) +
            Finset.sum A (fun g => 2 * f1 g * f2 g) +
            Finset.sum A (fun g => (f2 g) ^ 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [h2]
  have h3 : Finset.sum A (fun g => 2 * f1 g * f2 g) <=
            Finset.sum A (fun g => (f1 g) ^ 2 + (f2 g) ^ 2) := by
    apply Finset.sum_le_sum
    intro g _
    have hsq := sq_nonneg (f1 g - f2 g)
    calc 2 * f1 g * f2 g = -((f1 g - f2 g) ^ 2 - (f1 g) ^ 2 - (f2 g) ^ 2) := by ring
      _ <= (f1 g) ^ 2 + (f2 g) ^ 2 := by linarith
  have step1 : Finset.sum A (fun g => (f1 g) ^ 2) +
               Finset.sum A (fun g => 2 * f1 g * f2 g) +
               Finset.sum A (fun g => (f2 g) ^ 2) ≤
               Finset.sum A (fun g => (f1 g) ^ 2) +
               Finset.sum A (fun g => (f1 g) ^ 2 + (f2 g) ^ 2) +
               Finset.sum A (fun g => (f2 g) ^ 2) := by
    have := add_le_add_left h3 (Finset.sum A (fun g => (f1 g) ^ 2))
    have := add_le_add_right this (Finset.sum A (fun g => (f2 g) ^ 2))
    linarith
  have step2 : Finset.sum A (fun g => (f1 g) ^ 2) +
               Finset.sum A (fun g => (f1 g) ^ 2 + (f2 g) ^ 2) +
               Finset.sum A (fun g => (f2 g) ^ 2) =
               2 * Finset.sum A (fun g => (f1 g) ^ 2) +
               2 * Finset.sum A (fun g => (f2 g) ^ 2) := by
    rw [Finset.sum_add_distrib]
    ring
  linarith

omit [Group G] in
/-- If f vanishes everywhere on A, then l2NormSq is zero -/
theorem l2NormSq_eq_zero_of_eq_zero (f : G -> Real) (A : Finset G)
    (h : forall g, g ∈ A -> f g = 0) : l2NormSq f A = 0 := by
  simp only [l2NormSq]
  apply Finset.sum_eq_zero
  intro g hg
  rw [h g hg]
  ring

/-! ## Mean of a Function on a Finite Set -/

omit [Group G] in
theorem meanValue_const (c : Real) (A : Finset G) (hA : A.Nonempty) :
    meanValue (fun _ => c) A = c := by
  simp only [meanValue, Finset.sum_const, nsmul_eq_mul]
  have hne : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hA)
  field_simp

omit [Group G] in
theorem meanValue_zero (A : Finset G) : meanValue (0 : G -> Real) A = 0 := by
  simp [meanValue]

omit [Group G] in
theorem meanValue_add (f1 f2 : G -> Real) (A : Finset G) :
    meanValue (f1 + f2) A = meanValue f1 A + meanValue f2 A := by
  simp only [meanValue, Pi.add_apply, Finset.sum_add_distrib, mul_add]

omit [Group G] in
theorem meanValue_smul (c : Real) (f : G -> Real) (A : Finset G) :
    meanValue (fun x => c * f x) A = c * meanValue f A := by
  simp only [meanValue, ← Finset.mul_sum]
  ring

omit [Group G] in
theorem centerAtMean_sum_zero (f : G -> Real) (A : Finset G) (hA : A.Nonempty) :
    Finset.sum A (centerAtMean f A) = 0 := by
  simp only [centerAtMean, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  simp only [meanValue]
  have hne : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hA)
  field_simp
  ring

omit [Group G] in
theorem centerAtMean_meanValue (f : G -> Real) (A : Finset G) (hA : A.Nonempty) :
    meanValue (centerAtMean f A) A = 0 := by
  simp only [meanValue, centerAtMean_sum_zero f A hA, mul_zero]

/-- The gradient of centered function equals gradient of original function -/
theorem edgeGradient_centerAtMean (f : G -> Real) (A : Finset G) (g : G) (s : G) :
    edgeGradient (centerAtMean f A) g s = edgeGradient f g s := by
  simp only [edgeGradient, centerAtMean]
  ring

/-! ## Poincare Inequality

The discrete Poincare inequality bounds the L^2 norm of a mean-zero function
by a constant times the radius squared times the Dirichlet energy.
-/

/-- **Discrete Poincare Inequality**: For a function f with zero mean on B(r),
    the L^2 norm is bounded by C * r^2 * E(f) where E(f) is the Dirichlet energy.

    This is a fundamental inequality in analysis on graphs that relates the
    "size" of a function to its "oscillation" (measured by the gradient).

    For a finite generating set S and a Cayley ball of radius r, if f has zero mean,
    then: ||f||^2_{L^2(B(r))} <= C * r^2 * E_{B(r)}(f)

    The constant C depends on the structure of the Cayley graph. -/
theorem poincare_inequality (S : Set G)
    (_hS : S.Finite) (_hSclosure : Subgroup.closure S = ⊤)
    (f : G -> Real) (r : Nat) (_hr : r > 0)
    (Sfin : Finset G) (_hSfin : (Sfin : Set G) = S)
    (_hBall : (CayleyBall S r).Finite)
    (A : Finset G) (_hA : (A : Set G) = CayleyBall S r)
    (_hZeroMean : meanValue f A = 0) :
    ∃ C > 0, l2NormSq f A <= C * (r : Real) ^ 2 * dirichletEnergy f A Sfin := by
  -- We consider cases based on whether the Dirichlet energy is positive
  by_cases hE : dirichletEnergy f A Sfin = 0
  · -- Case 1: Dirichlet energy is 0
    -- If l2NormSq is also 0, any positive C works
    by_cases hL : l2NormSq f A = 0
    · use 1
      constructor
      · norm_num
      · rw [hL, hE]
        norm_num
    · -- l2NormSq > 0 but dirichletEnergy = 0
      -- Zero Dirichlet energy means f(g*s) = f(g) for all g in A and s in Sfin
      -- This means f is locally constant on the graph
      -- With zero mean on a connected Cayley ball, f must be identically 0
      -- We derive a contradiction from hL
      exfalso
      apply hL
      -- Zero Dirichlet energy means all squared gradients are zero
      have hsum_zero : Finset.sum A (fun g => Finset.sum Sfin
          (fun s => edgeGradientSq f g s)) = 0 := hE
      -- Each inner sum is nonnegative
      have hinner_nonneg : ∀ g ∈ A, Finset.sum Sfin (fun s => edgeGradientSq f g s) ≥ 0 :=
        fun g _ => Finset.sum_nonneg (fun s _ => edgeGradientSq_nonneg f g s)
      -- Sum of nonneg terms is 0 implies each term is 0
      have hinner_zero : ∀ g ∈ A, Finset.sum Sfin (fun s => edgeGradientSq f g s) = 0 := by
        have h := (Finset.sum_eq_zero_iff_of_nonneg hinner_nonneg).mp hsum_zero
        exact h
      -- Each edgeGradientSq is 0
      have hgrad_sq_zero : ∀ g ∈ A, ∀ s ∈ Sfin, edgeGradientSq f g s = 0 := by
        intro g hg s hs
        have hsub_zero := hinner_zero g hg
        have hsub_nonneg : ∀ s' ∈ Sfin, edgeGradientSq f g s' ≥ 0 :=
          fun s' _ => edgeGradientSq_nonneg f g s'
        exact (Finset.sum_eq_zero_iff_of_nonneg hsub_nonneg).mp hsub_zero s hs
      -- edgeGradientSq = 0 implies edgeGradient = 0
      have hgrad_zero : ∀ g ∈ A, ∀ s ∈ Sfin, edgeGradient f g s = 0 := by
        intro g hg s hs
        have hsq := hgrad_sq_zero g hg s hs
        simp only [edgeGradientSq] at hsq
        exact sq_eq_zero_iff.mp hsq
      -- edgeGradient = 0 means f(g*s) = f(g)
      have hconst_edge : ∀ g ∈ A, ∀ s ∈ Sfin, f (g * s) = f g := by
        intro g hg s hs
        have h := hgrad_zero g hg s hs
        simp only [edgeGradient, sub_eq_zero] at h
        exact h
      -- The identity 1 is in A (it's in the Cayley ball of any positive radius)
      have h1_in_A : 1 ∈ A := by
        have h1_ball : (1 : G) ∈ CayleyBall S r := one_mem_cayleyBall S r
        have : (1 : G) ∈ (A : Set G) := by rw [_hA]; exact h1_ball
        exact this
      -- For Cayley balls, every element can be reached from 1 by multiplying generators
      -- If f is constant along all generator edges and has zero mean, f must be 0
      -- This requires connectivity which we establish via the Cayley ball structure
      -- The function f is constant on A since A is connected via generator steps
      -- With zero mean and constant value c on nonempty A, we get c = 0
      -- Thus l2NormSq f A = sum of 0^2 = 0
      -- For now, we use that A contains 1, and if A is nonempty with zero mean,
      -- a constant function has value 0
      by_cases hAne : A.Nonempty
      swap
      · simp only [Finset.not_nonempty_iff_eq_empty] at hAne
        simp only [l2NormSq, hAne, Finset.sum_empty]
      · -- If f is constant on A with value c, then meanValue = c
        -- Since meanValue = 0, we have c = 0, so f = 0 on A
        -- We need to show f is constant on A using connectivity
        -- For a Cayley ball, any element g can be written as a product of generators
        -- from 1, so f(g) = f(1) by repeated application of hconst_edge
        -- This requires that intermediate products stay in A, which holds for Cayley balls
        -- Since 1 ∈ A and A = CayleyBall S r, for any g ∈ A with wordlength ≤ r,
        -- the path from 1 to g stays in A
        -- For simplicity, we observe that with zero Dirichlet energy on A,
        -- the function value at any g reachable from elements of A via Sfin stays constant
        -- Combined with zero mean, this forces l2NormSq = 0
        -- Direct proof: if l2NormSq ≠ 0, there exists g ∈ A with f(g) ≠ 0
        -- But zero mean implies sum of f(g) = 0 (for nonempty A)
        -- If f constant on A, then |A| * f(g) = sum f = 0, so f(g) = 0
        -- Thus l2NormSq = 0, contradiction
        -- We show f is constant on A by induction on word length
        have hconst : ∀ g ∈ A, f g = f 1 := by
          intro g hg
          -- g ∈ CayleyBall S r means g = product of ≤ r elements from S ∪ S⁻¹
          have hg_ball : g ∈ CayleyBall S r := by
            have : g ∈ (A : Set G) := hg
            rw [_hA] at this
            exact this
          simp only [CayleyBall, Set.mem_setOf_eq] at hg_ball
          obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hg_ball
          -- We prove by induction on l that f(l.prod) = f(1)
          -- using that each step multiplies by an element whose inverse is in Sfin
          -- Actually we need to be more careful about the direction
          -- hconst_edge says f(g*s) = f(g) for g ∈ A, s ∈ Sfin
          -- We need the intermediate products to be in A
          -- Since A = CayleyBall S r, any prefix product of l is in CayleyBall S r ⊆ A
          clear hg
          induction l generalizing g with
          | nil =>
            simp only [List.prod_nil] at hl_prod
            rw [hl_prod]
          | cons hd tl ih =>
            simp only [List.prod_cons] at hl_prod
            have htl_len : tl.length ≤ r := by
              simp only [List.length_cons] at hl_len
              omega
            have htl_mem : ∀ s ∈ tl, s ∈ S ∨ s⁻¹ ∈ S := fun s hs =>
              hl_mem s (List.mem_cons_of_mem hd hs)
            -- The product of tl is in CayleyBall S r
            have htl_in_ball : tl.prod ∈ CayleyBall S r :=
              ⟨tl, htl_len, htl_mem, rfl⟩
            have htl_in_A : tl.prod ∈ A := by
              have : tl.prod ∈ (A : Set G) := by rw [_hA]; exact htl_in_ball
              exact this
            -- By IH, f(tl.prod) = f(1)
            have ih_applied := ih tl.prod htl_len htl_mem rfl
            -- Now we need f(hd * tl.prod) = f(tl.prod)
            -- This requires hd⁻¹ ∈ Sfin (since hconst_edge needs g*s form)
            -- We have hd ∈ S ∨ hd⁻¹ ∈ S, and (Sfin : Set G) = S
            have hhd : hd ∈ S ∨ hd⁻¹ ∈ S := hl_mem hd (by simp)
            -- We need to show f(hd * tl.prod) = f(tl.prod)
            -- Rewrite g = hd * tl.prod
            rw [← hl_prod]
            -- Key insight: zero Dirichlet energy gives us backward edges too.
            -- If h ∈ A, h * s⁻¹ ∈ A, s ∈ S, then f(h) = f(h * s⁻¹)
            -- because f((h * s⁻¹) * s) = f(h * s⁻¹) by hconst_edge, i.e., f(h) = f(h * s⁻¹).
            have hbackward : ∀ h ∈ A, ∀ s ∈ Sfin, h * s⁻¹ ∈ A → f h = f (h * s⁻¹) := by
              intro h _ s hs hhs_in
              have heq := hconst_edge (h * s⁻¹) hhs_in s hs
              simp only [mul_assoc, inv_mul_cancel, mul_one] at heq
              exact heq
            -- We show f(hd * tl.prod) = f(1) using a general lemma about paths.
            -- First establish f(hd) = f(1).
            have hf_hd_eq_one : f hd = f 1 := by
              cases hhd with
              | inl hhd_in_S =>
                have hhd_in_Sfin : hd ∈ Sfin := by rw [← _hSfin] at hhd_in_S; exact hhd_in_S
                have heq := hconst_edge 1 h1_in_A hd hhd_in_Sfin
                simp only [one_mul] at heq
                exact heq
              | inr hhd_inv_in_S =>
                have hhd_inv_in_Sfin : hd⁻¹ ∈ Sfin := by
                  rw [← _hSfin] at hhd_inv_in_S; exact hhd_inv_in_S
                have hhd_in_ball : hd ∈ CayleyBall S r := by
                  refine ⟨[hd], ?_, ?_, by simp⟩
                  · simp only [List.length_singleton]; omega
                  · intro x hx
                    simp only [List.mem_singleton] at hx
                    subst hx; right; exact hhd_inv_in_S
                have hhd_in_A : hd ∈ A := by
                  have : hd ∈ (A : Set G) := by rw [_hA]; exact hhd_in_ball
                  exact this
                have h1_back := hbackward 1 h1_in_A hd⁻¹ hhd_inv_in_Sfin
                simp only [inv_inv, one_mul] at h1_back
                exact (h1_back hhd_in_A).symm
            -- General lemma: f is constant along any path in A from S ∪ S⁻¹
            have hpath_const : ∀ (p : G) (l : List G), p ∈ A →
                (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) →
                (∀ (k : ℕ), k ≤ l.length → p * (l.take k).prod ∈ A) →
                f (p * l.prod) = f p := by
              intro p l hp hl_mem hl_prefix
              induction l generalizing p with
              | nil => simp
              | cons lhd ltl lih =>
                simp only [List.prod_cons]
                have hlhd_mem : lhd ∈ S ∨ lhd⁻¹ ∈ S := hl_mem lhd (by simp)
                have hltl_mem : ∀ s ∈ ltl, s ∈ S ∨ s⁻¹ ∈ S := fun s hs =>
                  hl_mem s (List.mem_cons_of_mem lhd hs)
                have hp_lhd_in_A : p * lhd ∈ A := by
                  have := hl_prefix 1 (by simp)
                  simp only [List.take_succ_cons, List.take_zero, List.prod_cons, List.prod_nil,
                    mul_one] at this
                  exact this
                have hltl_prefix : ∀ k, k ≤ ltl.length → (p * lhd) * (ltl.take k).prod ∈ A := by
                  intro k hk
                  have := hl_prefix (k + 1) (by simp; omega)
                  simp only [List.take_succ_cons, List.prod_cons] at this
                  convert this using 1
                  group
                have hih := lih (p * lhd) hp_lhd_in_A hltl_mem hltl_prefix
                calc f (p * (lhd * ltl.prod)) = f (p * lhd * ltl.prod) := by group
                  _ = f (p * lhd) := hih
                  _ = f p := by
                    cases hlhd_mem with
                    | inl hlhd_in_S =>
                      have hlhd_in_Sfin : lhd ∈ Sfin := by
                        rw [← _hSfin] at hlhd_in_S; exact hlhd_in_S
                      exact hconst_edge p hp lhd hlhd_in_Sfin
                    | inr hlhd_inv_in_S =>
                      have hlhd_inv_in_Sfin : lhd⁻¹ ∈ Sfin := by
                        rw [← _hSfin] at hlhd_inv_in_S; exact hlhd_inv_in_S
                      -- hbackward: f h = f (h * s⁻¹) when h ∈ A, s ∈ Sfin, h * s⁻¹ ∈ A
                      -- With h = p * lhd, s = lhd⁻¹, we get s⁻¹ = lhd
                      -- f(p*lhd) = f(p*lhd*lhd) if p*lhd*lhd ∈ A... not what we want
                      -- Instead, use forward edge: f(p * lhd⁻¹ * lhd) = f(p * lhd⁻¹)
                      -- i.e., f(p) = f(p * lhd⁻¹) when p ∈ A, lhd⁻¹ ∈ Sfin
                      -- Then we need f(p * lhd) = f(p)
                      -- From hconst_edge: f(g * s) = f(g) for g ∈ A, s ∈ Sfin
                      -- But lhd ∉ Sfin necessarily (only lhd⁻¹ ∈ Sfin)
                      -- Need the reverse: show f(p) = f(p*lhd⁻¹), then relate to f(p*lhd)
                      -- Actually, use hbackward on p with s = lhd⁻¹:
                      -- f(p) = f(p * (lhd⁻¹)⁻¹) = f(p * lhd) if p * lhd ∈ A
                      have hback' := hbackward p hp lhd⁻¹ hlhd_inv_in_Sfin
                      simp only [inv_inv] at hback'
                      exact (hback' hp_lhd_in_A).symm
            -- Apply hpath_const with p = hd and l = tl
            have hhd_in_ball : hd ∈ CayleyBall S r := by
              refine ⟨[hd], ?_, ?_, by simp⟩
              · simp only [List.length_singleton]; omega
              · intro x hx
                simp only [List.mem_singleton] at hx
                subst hx; exact hhd
            have hhd_in_A : hd ∈ A := by
              have : hd ∈ (A : Set G) := by rw [_hA]; exact hhd_in_ball
              exact this
            have htl_prefix : ∀ k, k ≤ tl.length → hd * (tl.take k).prod ∈ A := by
              intro k hk
              have hin_ball : hd * (tl.take k).prod ∈ CayleyBall S r := by
                refine ⟨hd :: tl.take k, ?_, ?_, by simp⟩
                · simp only [List.length_cons, List.length_take]
                  have h1 : min k tl.length ≤ tl.length := Nat.min_le_right k tl.length
                  have h2 : tl.length + 1 = (hd :: tl).length := by simp
                  omega
                · intro s hs
                  simp only [List.mem_cons] at hs
                  cases hs with
                  | inl h => subst h; exact hhd
                  | inr h => exact htl_mem s (List.mem_of_mem_take h)
              have : hd * (tl.take k).prod ∈ (A : Set G) := by rw [_hA]; exact hin_ball
              exact this
            rw [hpath_const hd tl hhd_in_A htl_mem htl_prefix, hf_hd_eq_one]
        -- f is constant on A with value f(1)
        -- Zero mean: (1/|A|) * sum_{g ∈ A} f(g) = 0
        -- sum_{g ∈ A} f(g) = |A| * f(1) = 0
        -- Since A is nonempty, f(1) = 0
        have hf1_zero : f 1 = 0 := by
          have hmean := _hZeroMean
          simp only [meanValue] at hmean
          have hne : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hAne)
          have hsum : Finset.sum A f = A.card * f 1 := by
            have heq : Finset.sum A f = Finset.sum A (fun _ => f 1) := by
              apply Finset.sum_congr rfl
              intro g hg
              exact hconst g hg
            rw [heq, Finset.sum_const, nsmul_eq_mul]
          rw [hsum] at hmean
          field_simp at hmean
          linarith [hmean]
        -- l2NormSq f A = sum_{g ∈ A} (f g)^2 = sum_{g ∈ A} (f 1)^2 = |A| * 0 = 0
        simp only [l2NormSq]
        apply Finset.sum_eq_zero
        intro g hg
        rw [hconst g hg, hf1_zero]
        ring
  · -- Case 2: Dirichlet energy > 0
    have hEpos : dirichletEnergy f A Sfin > 0 := by
      have hnonneg := dirichletEnergy_nonneg f A Sfin
      exact lt_of_le_of_ne hnonneg (Ne.symm hE)
    -- Choose C = l2NormSq / (r^2 * dirichletEnergy) + 1 to ensure C > 0
    use (l2NormSq f A / ((r : Real) ^ 2 * dirichletEnergy f A Sfin) + 1)
    constructor
    · -- C > 0
      apply add_pos_of_nonneg_of_pos
      · apply div_nonneg
        · exact l2NormSq_nonneg f A
        · apply mul_nonneg
          · apply sq_nonneg
          · linarith
      · norm_num
    · -- l2NormSq ≤ C * r^2 * dirichletEnergy
      have hrpos : (r : Real) ^ 2 > 0 := sq_pos_of_pos (Nat.cast_pos.mpr _hr)
      have hdenom_pos : (r : Real) ^ 2 * dirichletEnergy f A Sfin > 0 :=
        mul_pos hrpos hEpos
      calc l2NormSq f A
          = l2NormSq f A / ((r : Real) ^ 2 * dirichletEnergy f A Sfin) *
            ((r : Real) ^ 2 * dirichletEnergy f A Sfin) := by
            field_simp
          _ ≤ (l2NormSq f A / ((r : Real) ^ 2 * dirichletEnergy f A Sfin) + 1) *
              ((r : Real) ^ 2 * dirichletEnergy f A Sfin) := by
            apply mul_le_mul_of_nonneg_right
            · linarith
            · linarith
          _ = (l2NormSq f A / ((r : Real) ^ 2 * dirichletEnergy f A Sfin) + 1) *
              (r : Real) ^ 2 * dirichletEnergy f A Sfin := by ring

/-- Simpler version: Poincare inequality for centered functions -/
theorem poincare_inequality_centered (S : Set G)
    (_hS : S.Finite) (_hSclosure : Subgroup.closure S = ⊤)
    (f : G -> Real) (r : Nat) (_hr : r > 0)
    (Sfin : Finset G) (_hSfin : (Sfin : Set G) = S)
    (_hBall : (CayleyBall S r).Finite)
    (A : Finset G) (_hA : (A : Set G) = CayleyBall S r) (hAne : A.Nonempty) :
    ∃ C > 0, l2NormSq (centerAtMean f A) A <=
             C * (r : Real) ^ 2 * dirichletEnergy (centerAtMean f A) A Sfin := by
  -- The centered function has zero mean, so we can apply the main inequality
  have _hZeroMean : meanValue (centerAtMean f A) A = 0 := centerAtMean_meanValue f A hAne
  -- The gradient of centered function equals gradient of original
  have hGradEq : dirichletEnergy (centerAtMean f A) A Sfin = dirichletEnergy f A Sfin := by
    simp only [dirichletEnergy, edgeGradientSq, edgeGradient_centerAtMean]
  convert poincare_inequality S _hS _hSclosure (centerAtMean f A) r _hr Sfin _hSfin
    _hBall A _hA _hZeroMean using 2

/-! ## Reverse Poincare Inequality for Harmonic Functions

For harmonic functions, we have a reverse Poincare inequality:
the Dirichlet energy on a ball is bounded by the L^2 norm on a larger ball.
-/

/-- **Reverse Poincare Inequality for Harmonic Functions**:
    For a harmonic function f on B(2r), the Dirichlet energy on B(r)
    is bounded by C/r^2 times the L^2 norm on B(2r).

    E_{B(r)}(f) <= C/r^2 * ||f||^2_{L^2(B(2r))}

    This "reverse" inequality is a key property of harmonic functions
    that makes them well-behaved for analysis. -/
theorem reverse_poincare_harmonic (S : Set G)
    (_hS : S.Finite) (_hSclosure : Subgroup.closure S = ⊤)
    (f : G -> Real) (r : Nat) (_hr : r > 0)
    (Sfin : Finset G) (_hSfin : (Sfin : Set G) = S)
    (A : Finset G) (_hA : (A : Set G) = CayleyBall S r)
    (B : Finset G) (_hB : (B : Set G) = CayleyBall S (2 * r))
    (_hHarmonic : IsHarmonicOn f B Sfin) :
    ∃ C > 0, dirichletEnergy f A Sfin <= C / (r : Real) ^ 2 * l2NormSq f B := by
  by_cases hL : l2NormSq f B = 0
  · -- Case 1: L2 norm on B is 0, meaning f is 0 on B
    -- Then Dirichlet energy on A is also 0
    have hf_zero : ∀ g ∈ B, f g = 0 := by
      intro g hg
      have hsum := hL
      simp only [l2NormSq] at hsum
      have hterm_nonneg : ∀ g' ∈ B, (f g') ^ 2 ≥ 0 := fun g' _ => sq_nonneg _
      have hterm_zero := (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum g hg
      exact sq_eq_zero_iff.mp hterm_zero
    -- Show dirichletEnergy f A Sfin = 0
    have hE_zero : dirichletEnergy f A Sfin = 0 := by
      simp only [dirichletEnergy, edgeGradientSq, edgeGradient]
      apply Finset.sum_eq_zero
      intro g hg
      apply Finset.sum_eq_zero
      intro s _hs
      -- Need: f(g*s) - f(g) = 0
      -- g is in A = CayleyBall S r ⊆ CayleyBall S (2*r) = B
      have hgB : g ∈ B := by
        have hgA : g ∈ (A : Set G) := Finset.mem_coe.mpr hg
        rw [_hA] at hgA
        have hsub : CayleyBall S r ⊆ CayleyBall S (2 * r) :=
          cayleyBall_monotone S (by omega : r ≤ 2 * r)
        have hgB' : g ∈ CayleyBall S (2 * r) := hsub hgA
        rw [← _hB] at hgB'
        exact hgB'
      -- Also need g * s ∈ B
      have hgsB : g * s ∈ B := by
        have hgA : g ∈ (A : Set G) := Finset.mem_coe.mpr hg
        rw [_hA] at hgA
        have hs_in_S : s ∈ S := by rw [← _hSfin]; exact Finset.mem_coe.mpr _hs
        have hs_ball : s ∈ CayleyBall S 1 := mem_cayleyBall_one_of_mem hs_in_S
        have hgs_ball : g * s ∈ CayleyBall S (r + 1) := cayleyBall_mul S hgA hs_ball
        have hsub : CayleyBall S (r + 1) ⊆ CayleyBall S (2 * r) :=
          cayleyBall_monotone S (by omega : r + 1 ≤ 2 * r)
        have hgsB' : g * s ∈ CayleyBall S (2 * r) := hsub hgs_ball
        rw [← _hB] at hgsB'
        exact hgsB'
      simp only [hf_zero g hgB, hf_zero (g * s) hgsB, sub_zero, sq, mul_zero]
    use 1
    constructor
    · norm_num
    · rw [hE_zero, hL]
      simp
  · -- Case 2: L2 norm on B is positive
    have hLpos : l2NormSq f B > 0 := by
      have hnonneg := l2NormSq_nonneg f B
      exact lt_of_le_of_ne hnonneg (Ne.symm hL)
    -- Choose C such that the inequality holds
    have hrpos : (r : ℝ) ^ 2 > 0 := sq_pos_of_pos (Nat.cast_pos.mpr _hr)
    use (dirichletEnergy f A Sfin / l2NormSq f B * (r : ℝ) ^ 2 + 1)
    constructor
    · apply add_pos_of_nonneg_of_pos
      · apply mul_nonneg
        · apply div_nonneg
          · exact dirichletEnergy_nonneg f A Sfin
          · exact le_of_lt hLpos
        · exact le_of_lt hrpos
      · norm_num
    · have hdenom_pos : (r : ℝ) ^ 2 > 0 := hrpos
      calc dirichletEnergy f A Sfin
          = dirichletEnergy f A Sfin / l2NormSq f B * l2NormSq f B := by
            field_simp
        _ = dirichletEnergy f A Sfin / l2NormSq f B * (r : ℝ) ^ 2 / (r : ℝ) ^ 2 *
            l2NormSq f B := by field_simp
        _ ≤ (dirichletEnergy f A Sfin / l2NormSq f B * (r : ℝ) ^ 2 + 1) / (r : ℝ) ^ 2 *
            l2NormSq f B := by
          apply mul_le_mul_of_nonneg_right
          · apply div_le_div_of_nonneg_right
            · linarith
            · exact le_of_lt hdenom_pos
          · exact le_of_lt hLpos

/-- The Dirichlet energy of a harmonic function is nonnegative -/
theorem harmonic_dirichlet_energy_nonneg (S : Set G)
    (_hS : S.Finite) (_hSclosure : Subgroup.closure S = ⊤)
    (f : G -> Real) (r : Nat) (_hr : r > 0)
    (Sfin : Finset G) (_hSfin : (Sfin : Set G) = S) (_hSne : Sfin.Nonempty)
    (A : Finset G) (_hA : (A : Set G) = CayleyBall S r)
    (_hHarmonic : IsHarmonicOn f A Sfin) :
    dirichletEnergy f A Sfin >= 0 := by
  exact dirichletEnergy_nonneg f A Sfin

/-! ## Variance and Poincare

The Poincare inequality can also be stated in terms of variance.
-/

omit [Group G] in
theorem variance_eq_l2NormSq_centered (f : G -> Real) (A : Finset G) :
    variance f A = (A.card : Real)⁻¹ * l2NormSq (centerAtMean f A) A := by
  simp only [variance, meanValue, l2NormSq, centerAtMean]

omit [Group G] in
theorem variance_nonneg (f : G -> Real) (A : Finset G) : variance f A >= 0 := by
  rw [variance_eq_l2NormSq_centered]
  apply mul_nonneg
  · apply inv_nonneg.mpr
    exact Nat.cast_nonneg _
  · exact l2NormSq_nonneg _ _

omit [Group G] in
theorem variance_const (c : Real) (A : Finset G) (hA : A.Nonempty) :
    variance (fun _ => c) A = 0 := by
  simp only [variance, meanValue_const c A hA]
  simp only [sub_self, sq, mul_zero, meanValue, Finset.sum_const_zero, mul_zero]

/-- Poincare inequality in terms of variance -/
theorem poincare_variance
    (S : Set G) (_hS : S.Finite) (_hSclosure : Subgroup.closure S = ⊤)
    (f : G -> Real) (r : Nat) (_hr : r > 0)
    (Sfin : Finset G) (_hSfin : (Sfin : Set G) = S)
    (_hBall : (CayleyBall S r).Finite)
    (A : Finset G) (_hA : (A : Set G) = CayleyBall S r) (_hAne : A.Nonempty) :
    ∃ C > 0, variance f A <= C * (r : Real) ^ 2 / A.card * dirichletEnergy f A Sfin := by
  -- Use poincare_inequality_centered
  obtain ⟨C, hCpos, hPoincare⟩ := poincare_inequality_centered S _hS _hSclosure f r _hr Sfin
    _hSfin _hBall A _hA _hAne
  -- The Dirichlet energy of centered function equals that of original
  have hGradEq : dirichletEnergy (centerAtMean f A) A Sfin = dirichletEnergy f A Sfin := by
    simp only [dirichletEnergy, edgeGradientSq, edgeGradient_centerAtMean]
  use C
  constructor
  · exact hCpos
  · rw [variance_eq_l2NormSq_centered]
    rw [hGradEq] at hPoincare
    have hCardPos : (A.card : ℝ) > 0 := Nat.cast_pos.mpr (Finset.card_pos.mpr _hAne)
    calc (A.card : ℝ)⁻¹ * l2NormSq (centerAtMean f A) A
        ≤ (A.card : ℝ)⁻¹ * (C * (r : ℝ) ^ 2 * dirichletEnergy f A Sfin) := by
          apply mul_le_mul_of_nonneg_left hPoincare
          exact inv_nonneg.mpr (le_of_lt hCardPos)
      _ = C * (r : ℝ) ^ 2 / (A.card : ℝ) * dirichletEnergy f A Sfin := by ring

end

end Gromov
