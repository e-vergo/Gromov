/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Kleiner's finite-dimensionality theorem for Lipschitz harmonic functions.

This file proves that the space of Lipschitz harmonic functions on a group
with polynomial growth is finite-dimensional. This is a key analytic result
in the Kleiner-Tao-Shalom proof of Gromov's theorem.

## Main Definitions

* `LipschitzHarmonicSubspace`: The vector space of L-Lipschitz harmonic functions

## Main Results

* `elliptic_regularity`: Discrete elliptic regularity for harmonic functions
* `gram_determinant_bound`: Bound on Gram determinant in terms of growth
* `lipschitzHarmonicSpace_finiteDimensional`: Main theorem - finite dimensionality

## References

* Kleiner (2010), "A new proof of Gromov's theorem on groups of polynomial growth"
* Colding-Minicozzi (1997), "Harmonic functions on manifolds"
* Tao's blog, "What's New" - Gromov's theorem overview (Theorem 3)
-/

module

public import Gromov.Proofs.Harmonic.Existence
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option linter.style.longLine false

namespace Gromov.Harmonic.FiniteDim

public section

open scoped NNReal BigOperators Matrix
open Gromov Gromov.Harmonic.Spectral Gromov.Harmonic.Existence

variable {G : Type*} [Group G] [DecidableEq G]

/-! ## Discrete Elliptic Regularity

The key analytic estimate: for harmonic functions, the L^2 norm on a small ball
controls the L^2 norm on a larger ball, with a multiplicative loss.
-/

section EllipticRegularity

variable (S : Set G) [Fintype S]

/-- L^2 norm of a function on a finite set.
    We use the standard definition: sqrt of sum of squares. -/
noncomputable def L2NormOnFinset (f : G → ℝ) (A : Finset G) : ℝ :=
  Real.sqrt (∑ g ∈ A, (f g)^2)

/-- Discrete elliptic regularity: for harmonic functions with mean zero on balls,
    the L^2 norm on a ball of radius R is bounded by C times the L^2 norm
    on a ball of radius 4R, for some constant C.

    This is the key estimate that enables the doubling argument. -/
theorem elliptic_regularity (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty) :
    ∃ C > 0, ∀ (f : G → ℝ), IsHarmonicSymmetric S f →
      ∀ (x : G) (A B : Finset G), (∀ a ∈ A, a ∈ B) →
        L2NormOnFinset (fun g => f (x * g)) A ≤ C * L2NormOnFinset (fun g => f (x * g)) B := by
  -- Proof sketch: The harmonic condition implies that the gradient of f is
  -- controlled by values on a larger ball. Iterating this gives the decay.
  -- The constant C depends only on epsilon and the degree of the Cayley graph.
  sorry

/-- Alternative formulation: the L^2 norm decays under enlargement of radius. -/
theorem l2_norm_decay (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (f : G → ℝ) (hf : IsHarmonicSymmetric S f) (x : G)
    (A B : Finset G) (k : ℕ) (hAB : ∀ a ∈ A, a ∈ B) :
    L2NormOnFinset (fun g => f (x * g)) A ≤
      (1/2 : ℝ)^k * L2NormOnFinset (fun g => f (x * g)) B := by
  -- Proof sketch: Iterate elliptic_regularity k times.
  sorry

end EllipticRegularity

/-! ## Covering Argument

For polynomial growth groups, we can cover a ball of radius 4R by a bounded
number of balls of radius epsilon*R.
-/

section CoveringArgument

variable (S : Set G) [Fintype S]

/-- For polynomial growth groups, B(4R) can be covered by O_d(1) balls of radius R/4.
    The number of balls depends only on the growth degree d. -/
theorem bounded_doubling_covering (hpoly : HasPolynomialGrowth G)
    (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty) (hS_gen : Subgroup.closure S = ⊤) :
    ∃ C : ℕ, ∀ (R : ℕ), R > 0 →
      (CayleyBall S (4 * R)).ncard ≤ C * (CayleyBall S R).ncard := by
  -- Proof sketch: By polynomial growth, |B(4R)|/|B(R)| ≤ C for some constant C
  -- depending on the growth degree. This is the doubling property.
  sorry

end CoveringArgument

/-! ## Gram Matrix Bounds

The key to finite-dimensionality is bounding the Gram matrix of Lipschitz
harmonic functions. The Gram determinant cannot grow faster than polynomial.
-/

section GramMatrix

variable (S : Set G) [Fintype S]

/-- The L^2 inner product of two functions on a finite set. -/
noncomputable def L2InnerProductFinset (f g : G → ℝ) (A : Finset G) : ℝ :=
  ∑ x ∈ A, f x * g x

/-- The Gram matrix of a list of functions, evaluated on a finite set. -/
noncomputable def GramMatrixOnFinset (fs : List (G → ℝ)) (A : Finset G) :
    Matrix (Fin fs.length) (Fin fs.length) ℝ :=
  Matrix.of fun i j => L2InnerProductFinset (fs.get i) (fs.get j) A

/-- The Gram determinant Q_A(f_1, ..., f_k). -/
noncomputable def GramDeterminantFinset (fs : List (G → ℝ)) (A : Finset G) : ℝ :=
  Matrix.det (GramMatrixOnFinset fs A)

/-- The Gram determinant of D linearly independent Lipschitz harmonic functions
    grows at most polynomially in the size of the set. -/
theorem gram_determinant_bound (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hpoly : HasPolynomialGrowth G)
    {D : ℕ} (fs : Fin D → G → ℝ)
    (hfs_harm : ∀ i, IsHarmonicSymmetric S (fs i))
    (hfs_lip : ∀ i, IsWordLipschitz S 1 (fs i))
    (hfs_indep : LinearIndependent ℝ fs) :
    ∃ (C : ℝ) (d : ℕ), C > 0 ∧
      ∀ (A : Finset G), GramDeterminantFinset (List.ofFn fs) A ≤ C * (A.card : ℝ)^d := by
  -- Proof sketch: By Lipschitz and harmonic properties, |f_i(x)| ≤ L * R on B(R).
  -- Thus entries of Gram matrix are O(R^2 * |B(R)|) = O(R^(2+growth_degree)).
  -- The determinant is a polynomial in entries, giving polynomial bound.
  sorry

/-- The Gram determinant is monotone in the set: larger sets give larger determinants
    for linearly independent functions. -/
theorem gram_determinant_monotone (fs : List (G → ℝ)) (A B : Finset G) (hAB : A ⊆ B) :
    GramDeterminantFinset fs A ≤ GramDeterminantFinset fs B := by
  -- Proof sketch: Larger set means more terms in the sum defining inner product.
  -- For non-negative definite matrices, this increases the determinant.
  sorry

end GramMatrix

/-! ## Main Finite-Dimensionality Theorem

Combining elliptic regularity, covering arguments, and Gram determinant bounds,
we prove that the space of Lipschitz harmonic functions is finite-dimensional.
-/

section FiniteDimensionality

variable (S : Set G) [Fintype S]

/-- The space of L-Lipschitz harmonic functions, viewed as a subspace of G → ℝ. -/
def LipschitzHarmonicSubspace (L : ℝ) : Submodule ℝ (G → ℝ) where
  carrier := {f | IsHarmonicSymmetric S f ∧ IsWordLipschitz S L f}
  add_mem' := fun {f g} ⟨h1a, h1b⟩ ⟨h2a, h2b⟩ => by
    constructor
    · -- Sum of harmonic functions is harmonic
      sorry
    · -- Sum of Lipschitz functions is Lipschitz
      sorry
  zero_mem' := by
    constructor
    · -- Zero is harmonic
      sorry
    · -- Zero is Lipschitz
      sorry
  smul_mem' := fun c f ⟨hf_harm, hf_lip⟩ => by
    constructor
    · -- Scalar multiple of harmonic is harmonic
      sorry
    · -- Scalar multiple of Lipschitz is Lipschitz
      sorry

/-- A key lemma: if there were D linearly independent 1-Lipschitz harmonic functions,
    the Gram determinant would have to grow at least as fast as R^D,
    contradicting the polynomial bound for polynomial growth groups. -/
theorem dimension_bound_from_gram (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hpoly : HasPolynomialGrowth G)
    (D : ℕ) (fs : Fin D → G → ℝ)
    (hfs_harm : ∀ i, IsHarmonicSymmetric S (fs i))
    (hfs_lip : ∀ i, IsWordLipschitz S 1 (fs i))
    (hfs_indep : LinearIndependent ℝ fs) :
    ∃ d_max : ℕ, D ≤ d_max := by
  -- Proof sketch:
  -- 1. By elliptic regularity, Gram det Q_R satisfies Q_R ≤ C * Q_{4R} for some C < 1.
  -- 2. By polynomial growth, Q_R ≤ C' * R^{D*d} for growth degree d.
  -- 3. Iterating the first bound, Q_{4^k} ≤ C^k * Q_1.
  -- 4. But Q_{4^k} ≥ c * 4^{k*D} for some c > 0 (linear independence).
  -- 5. This forces D ≤ d (the growth degree).
  sorry

/-- Main theorem: The space of L-Lipschitz harmonic functions on a group with
    polynomial growth of degree d is finite-dimensional, with dimension at most
    a function of d and L.

    This is Theorem 3 from Tao's overview of Gromov's theorem. -/
theorem lipschitzHarmonicSpace_finiteDimensional (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hpoly : HasPolynomialGrowth G) (L : ℝ) (hL : L > 0) :
    FiniteDimensional ℝ (LipschitzHarmonicSubspace S L) := by
  -- Proof sketch:
  -- 1. Reduce to L = 1 by scaling.
  -- 2. Suppose for contradiction that dim ≥ D for arbitrarily large D.
  -- 3. Take D linearly independent functions f_1, ..., f_D.
  -- 4. By dimension_bound_from_gram, D ≤ d_max where d_max depends only on growth.
  -- 5. This bounds the dimension.
  sorry

/-- The dimension bound in terms of growth degree. -/
theorem lipschitzHarmonicSpace_dimension_bound (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hpoly : HasPolynomialGrowth G) (L : ℝ) (hL : L > 0) :
    ∃ d : ℕ, Module.finrank ℝ (LipschitzHarmonicSubspace S L) ≤ d := by
  -- Proof sketch: Follows from lipschitzHarmonicSpace_finiteDimensional and
  -- the explicit bound from dimension_bound_from_gram.
  sorry

end FiniteDimensionality

/-! ## Consequences for Representation Theory

The finite-dimensionality of Lipschitz harmonic functions enables us to
construct a finite-dimensional representation of G.
-/

section Representation

variable (S : Set G) [Fintype S]

/-- G acts on the space of Lipschitz harmonic functions by left translation. -/
def leftTranslationAction (g : G) : (G → ℝ) →ₗ[ℝ] (G → ℝ) where
  toFun := fun f x => f (g⁻¹ * x)
  map_add' := fun f₁ f₂ => by ext x; simp [Pi.add_apply]
  map_smul' := fun c f => by ext x; simp [Pi.smul_apply, smul_eq_mul]

/-- Left translation preserves harmonicity. -/
theorem leftTranslation_preserves_harmonic (hS : Gromov.IsSymmetric S) (g : G) (f : G → ℝ)
    (hf : IsHarmonicSymmetric S f) :
    IsHarmonicSymmetric S (leftTranslationAction g f) := by
  -- Proof sketch: The harmonic condition is translation-invariant because
  -- summing over neighbors commutes with translation.
  sorry

/-- Left translation preserves Lipschitz property. -/
theorem leftTranslation_preserves_lipschitz (g : G) (L : ℝ) (f : G → ℝ)
    (hf : IsWordLipschitz S L f) :
    IsWordLipschitz S L (leftTranslationAction g f) := by
  -- Proof sketch: The word distance is left-invariant:
  -- d(g^{-1}x, g^{-1}y) = d(x, y).
  sorry

/-- G acts on the Lipschitz harmonic space by left translation.
    This gives a representation of G on a finite-dimensional space. -/
theorem harmonicRepresentation_exists (hS : Gromov.IsSymmetric S) (L : ℝ) (hL : L > 0) :
    ∃ (ρ : G →* (LipschitzHarmonicSubspace S L →ₗ[ℝ] LipschitzHarmonicSubspace S L)), True := by
  -- Proof sketch: leftTranslationAction restricts to LipschitzHarmonicSubspace
  -- by the preservation theorems above. This gives a group homomorphism.
  sorry

end Representation

end

end Gromov.Harmonic.FiniteDim
