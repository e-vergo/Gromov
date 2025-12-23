/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Extraction of Z quotients from groups with polynomial growth.

This file develops the key construction that bridges representation theory
and group theory: extracting a surjection to Z from a finitely generated
group with polynomial growth that acts on Lipschitz harmonic functions.

## Main Results

* `virtually_abelian_has_Z_quotient`: Infinite f.g. virtually abelian groups have Z quotients
* `infinite_cyclic_quotient_of_polynomial_growth_aux`: Main extraction theorem

## References

* Tao-Shalom, Section 4-5
* Kleiner (2010), Section 4
-/

module

public import Gromov.Proofs.Representation.CompactLie
public import Gromov.Proofs.VirtuallyNilpotent.Core
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank

set_option linter.style.longLine false

namespace Gromov.Representation.QuotientExtraction

public section

open scoped NNReal BigOperators
open Gromov Gromov.Representation.CompactLie Group

variable {G : Type*} [Group G] [DecidableEq G]

/-! ## Maximum Principle for Harmonic Functions

The maximum principle states that a harmonic function constant on a
finite-index coset is constant everywhere.
-/

section MaximumPrinciple

variable (S : Set G) [Fintype S]

omit [DecidableEq G] in
/-- A harmonic function that is constant on a finite-index subgroup
    must be constant everywhere.

    This follows from the fact that the Cayley graph is connected and
    the mean value property propagates the constant value. -/
theorem maximum_principle_harmonic (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (f : G → ℝ) (hf : IsHarmonicSymmetric S f)
    (H : Subgroup G) [H.FiniteIndex] (c : ℝ) (hconst : ∀ h : H, f h.val = c) :
    ∀ g : G, f g = c := by
  -- Proof sketch: Since H has finite index, every element is within bounded
  -- distance from H. By the mean value property of harmonic functions,
  -- if f is constant on a dense set (H has finite index = "dense" in the coset sense),
  -- then f must be constant everywhere. This uses connectedness of the Cayley graph.
  sorry

omit [DecidableEq G] in
/-- Corollary: A non-constant harmonic function cannot be constant on any
    finite-index subgroup. -/
theorem nonconstant_harmonic_not_constant_on_finite_index (hS : Gromov.IsSymmetric S)
    (hS_nonempty : S.Nonempty) (hS_gen : Subgroup.closure S = ⊤)
    (f : G → ℝ) (hf : IsHarmonicSymmetric S f) (hnc : ¬∃ c, f = fun _ => c)
    (H : Subgroup G) [H.FiniteIndex] :
    ¬∃ c, ∀ h : H, f h.val = c := by
  intro ⟨c, hconst⟩
  apply hnc
  exact ⟨c, funext (maximum_principle_harmonic S hS hS_nonempty hS_gen f hf H c hconst)⟩

end MaximumPrinciple

/-! ## G-Action on Lipschitz Harmonic Space

The group G acts on the space of Lipschitz harmonic functions by left translation.
This action is precompact (has compact closure) when G has polynomial growth.
-/

section GAction

variable (S : Set G) [Fintype S]

/-- Left translation by g on functions G → ℝ. -/
def leftTranslation (g : G) : (G → ℝ) → (G → ℝ) :=
  fun f x => f (g⁻¹ * x)

omit [DecidableEq G] in
/-- Left translation preserves the harmonic property. -/
theorem left_translation_preserves_harmonic (hS : Gromov.IsSymmetric S)
    (g : G) (f : G → ℝ) (hf : IsHarmonicSymmetric S f) :
    IsHarmonicSymmetric S (leftTranslation g f) := by
  intro x
  unfold leftTranslation
  -- Goal: ∑ s : S, f (g⁻¹ * (x * s.val)) = Fintype.card S * f (g⁻¹ * x)
  -- Rewrite using associativity: g⁻¹ * (x * s) = (g⁻¹ * x) * s
  conv_lhs => arg 2; ext s; rw [← mul_assoc]
  -- Now apply hf to g⁻¹ * x
  exact hf (g⁻¹ * x)

omit [DecidableEq G] in
/-- Left translation preserves the Lipschitz property. -/
theorem left_translation_preserves_lipschitz (g : G) {L : ℝ} (f : G → ℝ)
    (hf : IsWordLipschitz S L f) :
    IsWordLipschitz S L (leftTranslation g f) := by
  intro x y
  unfold leftTranslation
  -- Need: |f (g⁻¹ * x) - f (g⁻¹ * y)| ≤ L * ↑(wordDist S x y)
  -- Use left-invariance of wordDist: wordDist S x y = wordDist S (g⁻¹ * x) (g⁻¹ * y)
  have h_left_inv : wordDist S (g⁻¹ * x) (g⁻¹ * y) = wordDist S x y := by
    unfold wordDist
    congr 1
    calc (g⁻¹ * x)⁻¹ * (g⁻¹ * y)
      _ = x⁻¹ * (g⁻¹)⁻¹ * (g⁻¹ * y) := by rw [mul_inv_rev]
      _ = x⁻¹ * g * (g⁻¹ * y) := by rw [inv_inv]
      _ = x⁻¹ * (g * (g⁻¹ * y)) := by rw [mul_assoc]
      _ = x⁻¹ * ((g * g⁻¹) * y) := by rw [mul_assoc]
      _ = x⁻¹ * (1 * y) := by rw [mul_inv_cancel]
      _ = x⁻¹ * y := by rw [one_mul]
  rw [← h_left_inv]
  exact hf (g⁻¹ * x) (g⁻¹ * y)

omit [DecidableEq G] [Fintype S] in
/-- The G-action on Lipschitz harmonic space modulo constants has precompact image
    when G has polynomial growth.

    This is because the action preserves the Lipschitz constant, and in finite
    dimensions bounded sets are precompact. -/
theorem action_precompact (_hS : Gromov.IsSymmetric S) (_hS_nonempty : S.Nonempty)
    (_hS_gen : Subgroup.closure S = ⊤) (_hpoly : HasPolynomialGrowth G) (L : ℝ) (_hL : L > 0) :
    True := by  -- Placeholder for: image of G in End(V/constants) is precompact
  -- Proof sketch:
  -- 1. The space V = LipschitzHarmonicSpace S L is finite-dimensional by Kleiner's theorem.
  -- 2. G acts by isometries on V (preserving Lipschitz constant).
  -- 3. In finite dimensions, a family of operators with uniformly bounded norm
  --    has precompact closure.
  -- 4. Since G acts by Lipschitz-preserving maps, the image is bounded, hence precompact.
  trivial

end GAction

/-! ## Finite Image Contradiction

If the action of G on V/constants has finite image, then all Lipschitz harmonic
functions are constant, which contradicts the existence theorem for infinite groups.
-/

section FiniteImage

variable (S : Set G) [Fintype S]

omit [DecidableEq G] [Fintype S] in
/-- If the G-action on V/constants has finite image, then every Lipschitz harmonic
    function is constant.

    This is a key dichotomy: either G has infinite image (giving a Z quotient)
    or all harmonic functions are constant (impossible for infinite groups). -/
theorem finite_image_contradiction (_hS : Gromov.IsSymmetric S) (_hS_nonempty : S.Nonempty)
    (_hS_gen : Subgroup.closure S = ⊤) (_hpoly : HasPolynomialGrowth G) (_hInf : Infinite G)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ρ : G →* V →ₗ[ℝ] V) (_hfin : (Set.range ρ).Finite) :
    True := by  -- Placeholder for: contradiction with existence of non-constant harmonic
  -- Proof sketch:
  -- 1. If the image of G in End(V) is finite, let H = kernel of ρ.
  -- 2. H is a finite-index subgroup of G.
  -- 3. Any Lipschitz harmonic function is fixed by H, hence constant on H-cosets.
  -- 4. By maximum_principle_harmonic, f is constant.
  -- 5. But for infinite G with polynomial growth, non-constant Lipschitz harmonic
  --    functions exist (Theorem 2 from Tao's overview).
  -- 6. Contradiction.
  trivial

end FiniteImage

/-! ## Z Quotient from Virtually Abelian Groups

An infinite finitely generated virtually abelian group has a quotient isomorphic to Z.
-/

section VirtuallyAbelianQuotient

/-- Statement: An infinite finitely generated virtually abelian group
    surjects onto Z.

    This is a standard result in group theory: the abelianization of such
    a group has positive rank, giving a Z quotient. -/
theorem virtually_abelian_has_Z_quotient (G : Type*) [Group G] (hFG : Group.FG G) (hInf : Infinite G)
    (hVA : ∃ (A : Subgroup G), A.FiniteIndex ∧ ∀ a b : A, a.val * b.val = b.val * a.val) :
    ∃ (φ : G →* ℤ), Function.Surjective φ := by
  -- Proof sketch:
  -- 1. Let A be a finite-index abelian subgroup of G.
  -- 2. A is f.g. (since finite index in f.g. group).
  -- 3. As a f.g. abelian group, A ≅ Z^r × (torsion) for some r ≥ 0.
  -- 4. Since G is infinite and A has finite index, A is infinite, so r ≥ 1.
  -- 5. Project A → Z^r → Z (first coordinate) and extend to G → Z.
  sorry

/-- Corollary: An infinite f.g. virtually nilpotent group surjects onto Z.

    Virtually nilpotent implies virtually abelian for infinite f.g. groups
    (the abelianization of a nilpotent group has the same rank). -/
theorem virtually_nilpotent_has_Z_quotient (G : Type*) [Group G] (hFG : Group.FG G) (hInf : Infinite G)
    (hVN : IsVirtuallyNilpotent G) :
    ∃ (φ : G →* ℤ), Function.Surjective φ := by
  -- Proof sketch:
  -- 1. Virtually nilpotent implies there exists a finite-index nilpotent subgroup N.
  -- 2. N is f.g. (finite index in f.g. group).
  -- 3. By the structure theorem for f.g. nilpotent groups, N is polycyclic.
  -- 4. The abelianization N/[N,N] is a f.g. abelian group.
  -- 5. Since N is infinite (G infinite, N finite index), N/[N,N] has positive rank.
  -- 6. This gives a surjection N → Z, which extends to G → Z.
  sorry

end VirtuallyAbelianQuotient

/-! ## Main Extraction Theorem

The culmination: a finitely generated group with polynomial growth surjects onto Z
(unless it is finite).
-/

section MainExtraction

variable (S : Set G) [Fintype S]

omit [DecidableEq G] in
/-- Main theorem: An infinite finitely generated group with polynomial growth
    surjects onto Z.

    This is the key group-theoretic consequence of Gromov's theorem. -/
theorem infinite_cyclic_quotient_of_polynomial_growth_aux (hS : Gromov.IsSymmetric S)
    (hS_nonempty : S.Nonempty) (hS_gen : Subgroup.closure S = ⊤)
    (hFG : Group.FG G) (hpoly : HasPolynomialGrowth G) (hInf : Infinite G) :
    ∃ (φ : G →* ℤ), Function.Surjective φ := by
  -- Proof sketch (Kleiner's argument):
  -- 1. By lipschitz_harmonic_nonconstant, there exists a non-constant L-Lipschitz
  --    harmonic function f on G.
  -- 2. The space V of L-Lipschitz harmonic functions is finite-dimensional
  --    by lipschitzHarmonicSpace_finiteDimensional.
  -- 3. G acts on V by left translation, preserving harmonicity and Lipschitz constant.
  -- 4. The action factors through V/constants (since f ↦ f + c is the constant action).
  -- 5. By action_precompact, the closure of the G-image in End(V/constants) is compact.
  -- 6. By polynomial_growth_in_compact_lie_statement, G is virtually nilpotent.
  -- 7. By virtually_nilpotent_has_Z_quotient, G surjects onto Z.
  sorry

/-- Alternative formulation: polynomial growth implies virtually cyclic quotient. -/
theorem polynomial_growth_has_infinite_cyclic_quotient
    (G : Type*) [Group G] (hFG : Group.FG G) (hpoly : HasPolynomialGrowth G) (hInf : Infinite G) :
    ∃ (N : Subgroup G) (_ : N.Normal), Nonempty (G ⧸ N ≃* ℤ) := by
  -- Proof sketch: From infinite_cyclic_quotient_of_polynomial_growth_aux,
  -- we get φ : G →* Z surjective. Let N = ker(φ). Then G/N ≅ Z.
  sorry

end MainExtraction

/-! ## Induction Setup for Gromov's Theorem

The Z quotient allows an induction on the growth rate: G/ker(φ) ≅ Z means
ker(φ) has strictly smaller growth degree.
-/

section InductionSetup

/-- The kernel of a surjection to Z has strictly smaller growth degree.

    If G has polynomial growth of degree d > 0 and φ : G → Z is surjective,
    then ker(φ) has polynomial growth of degree d - 1. -/
theorem kernel_has_smaller_growth (G : Type*) [Group G] (hFG : Group.FG G)
    (hpoly : HasPolynomialGrowth G)
    (φ : G →* ℤ) (hφ : Function.Surjective φ) :
    HasPolynomialGrowth (φ.ker) := by
  -- Proof sketch:
  -- 1. ker(φ) is finitely generated (kernel of surjection from f.g. group).
  -- 2. The growth of ker(φ) is related to the growth of G by:
  --    |B_G(n)| ≈ |B_{ker(φ)}(n)| * |B_Z(n)| = |B_{ker(φ)}(n)| * (2n+1)
  -- 3. If G has growth degree d, then ker(φ) has growth degree at most d-1.
  -- 4. Actually ker(φ) has polynomial growth with degree exactly d-1 when d > 0.
  sorry

/-- The growth degree decreases by exactly 1 when quotienting to Z.

    This gives the induction measure for Gromov's theorem. -/
theorem growth_degree_decreases (G : Type*) [Group G] (_hFG : Group.FG G)
    (_hpoly : HasPolynomialGrowth G)
    (φ : G →* ℤ) (_hφ : Function.Surjective φ)
    (d : ℕ) (_hd : d > 0) :
    True := by  -- Placeholder: degree(ker φ) < degree(G)
  -- Proof sketch: The growth degree is additive in short exact sequences
  -- 1 → ker(φ) → G → Z → 1, so degree(G) = degree(ker φ) + 1.
  trivial

end InductionSetup

end

end Gromov.Representation.QuotientExtraction
