/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Self-adjointness and spectral properties of discrete Laplacian.

This file develops the L² theory of the discrete Laplacian on groups.
The main results establish self-adjointness and spectral bounds.

## Main results

* `discreteLaplacian_selfAdjoint_l2` - ⟨Δf, g⟩ = ⟨f, Δg⟩ for finite-support functions
* `laplacian_eigenvalue_nonneg` - All eigenvalues are ≥ 0
* `laplacian_eigenvalue_le_two` - All eigenvalues are ≤ 2
* `poincare_inequality_ball` - Variance bounded by Dirichlet form

## References

* Chung, "Spectral Graph Theory" (1997)
* Saloff-Coste, "Random walks on finite groups" (2004)
-/

module

public import Gromov.Proofs.Harmonic.Spectral
public import Gromov.Proofs.Growth.Polynomial
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection

namespace Gromov.Harmonic.SelfAdjoint

public section

open scoped NNReal BigOperators
open Gromov Gromov.Harmonic.Spectral

variable {G : Type*} [Group G] [DecidableEq G]

/-! ## L² Inner Product on Finite Support Functions -/

section L2InnerProduct

variable (S : Set G) [Fintype S]

/-- The L² inner product for functions with finite support.
    ⟨f, g⟩ = Σ_x f(x) * g(x) -/
noncomputable def l2InnerProduct (f g : G → ℝ) (support : Finset G) : ℝ :=
  ∑ x ∈ support, f x * g x

/-- The L² norm squared. -/
noncomputable def l2NormSq (f : G → ℝ) (support : Finset G) : ℝ :=
  ∑ x ∈ support, (f x) ^ 2

/-- The L² norm is non-negative. -/
theorem l2NormSq_nonneg (f : G → ℝ) (support : Finset G) :
    0 ≤ l2NormSq f support := by
  unfold l2NormSq
  apply Finset.sum_nonneg
  intro x _
  apply sq_nonneg

/-- L² inner product is symmetric. -/
theorem l2InnerProduct_comm (f g : G → ℝ) (support : Finset G) :
    l2InnerProduct f g support = l2InnerProduct g f support := by
  unfold l2InnerProduct
  apply Finset.sum_congr rfl
  intro x _
  ring

end L2InnerProduct

/-! ## Self-Adjointness of Laplacian -/

section SelfAdjoint

variable (S : Set G) [Fintype S] (hS_sym : S⁻¹ = S)

/-- The discrete Laplacian is self-adjoint with respect to the L² inner product.
    ⟨Δf, g⟩ = ⟨f, Δg⟩ for finite-support functions. -/
theorem discreteLaplacian_selfAdjoint_l2 (f g : G → ℝ) (support : Finset G)
    (hf : ∀ x ∉ support, f x = 0) (hg : ∀ x ∉ support, g x = 0)
    (hsupp : ∀ x ∈ support, ∀ s : S, x * s.val ∈ support) :
    l2InnerProduct (DiscreteLaplacian S f) g support =
    l2InnerProduct f (DiscreteLaplacian S g) support := by
  sorry

/-- The Laplacian can be written as a gradient form (Dirichlet form).
    ⟨Δf, f⟩ = (1/2|S|) Σ_{x,s} (f(x) - f(xs))² -/
theorem laplacian_as_gradient_form (f : G → ℝ) (support : Finset G)
    (hf : ∀ x ∉ support, f x = 0)
    (hsupp : ∀ x ∈ support, ∀ s : S, x * s.val ∈ support) :
    l2InnerProduct (DiscreteLaplacian S f) f support =
    (1 / (2 * Fintype.card S)) * ∑ x ∈ support, ∑ s : S, (f x - f (x * s.val)) ^ 2 := by
  unfold l2InnerProduct
  simp only [discreteLaplacian_eq]
  conv_lhs => arg 2; ext x; rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [sq]
  -- LHS is now: ∑ x, f x * f x - ∑ x, (1/|S| * ∑ s, f(x*s)) * f x
  -- Rearrange the second sum
  -- The rest of this proof involves complex rearrangement of sums
  -- Proof sketch: Expand (f(x) - f(x*s))^2 = f(x)^2 - 2*f(x)*f(x*s) + f(x*s)^2
  -- The f(x)^2 and f(x*s)^2 terms sum to 2*∑_x f(x)^2 by reindexing
  -- The cross term gives the averaging term
  sorry

/-- The Laplacian is positive semi-definite. -/
theorem laplacian_nonneg (f : G → ℝ) (support : Finset G)
    (hf : ∀ x ∉ support, f x = 0)
    (hsupp : ∀ x ∈ support, ∀ s : S, x * s.val ∈ support) :
    0 ≤ l2InnerProduct (DiscreteLaplacian S f) f support := by
  rw [laplacian_as_gradient_form S f support hf hsupp]
  apply mul_nonneg
  · apply div_nonneg
    · exact zero_le_one
    · apply mul_nonneg
      · exact two_pos.le
      · exact Nat.cast_nonneg _
  · apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro s _
    apply sq_nonneg

end SelfAdjoint

/-! ## Spectral Bounds -/

section SpectralBounds

variable (S : Set G) [Fintype S] (hS_sym : S⁻¹ = S) (hS_gen : Subgroup.closure S = ⊤)

/-- Eigenvalues of the discrete Laplacian are non-negative. -/
theorem laplacian_eigenvalue_nonneg (f : G → ℝ) (eigenvalue : ℝ)
    (support : Finset G)
    (hf : ∀ x ∉ support, f x = 0)
    (hf_eigen : DiscreteLaplacian S f = eigenvalue • f)
    (hf_nonzero : ∃ x, f x ≠ 0) :
    0 ≤ eigenvalue := by
  sorry

/-- Eigenvalues of the discrete Laplacian are at most 2. -/
theorem laplacian_eigenvalue_le_two (f : G → ℝ) (eigenvalue : ℝ)
    (support : Finset G)
    (hf : ∀ x ∉ support, f x = 0)
    (hf_eigen : DiscreteLaplacian S f = eigenvalue • f)
    (hf_nonzero : ∃ x, f x ≠ 0) :
    eigenvalue ≤ 2 := by
  sorry

/-- The eigenvalue 0 corresponds to constant functions (on finite connected components). -/
theorem laplacian_zero_eigenvalue_iff_constant (f : G → ℝ) (support : Finset G)
    (hf : ∀ x ∉ support, f x = 0)
    (hf_eigen : DiscreteLaplacian S f = 0) :
    ∀ x ∈ support, ∀ y ∈ support,
      (∃ path : List G, path.head? = some x ∧ path.getLast? = some y ∧
        ∀ i (hi : i + 1 < path.length),
          (path.get ⟨i, Nat.lt_of_succ_lt hi⟩)⁻¹ * path.get ⟨i + 1, hi⟩ ∈ S ∨
          ((path.get ⟨i, Nat.lt_of_succ_lt hi⟩)⁻¹ * path.get ⟨i + 1, hi⟩)⁻¹ ∈ S) →
        f x = f y := by
  sorry

end SpectralBounds

/-! ## Poincaré Inequality -/

section PoincareInequality

variable (S : Set G) [Fintype S] (hS_sym : S⁻¹ = S)

/-- The Dirichlet form (energy). -/
noncomputable def DirichletForm (f : G → ℝ) (support : Finset G) : ℝ :=
  (1 / (2 * Fintype.card S)) * ∑ x ∈ support, ∑ s : S, (f x - f (x * s.val)) ^ 2

/-- Variance of f on a set. -/
noncomputable def variance (f : G → ℝ) (support : Finset G) : ℝ :=
  let mean := (1 / support.card) * ∑ x ∈ support, f x
  (1 / support.card) * ∑ x ∈ support, (f x - mean) ^ 2

/-- Poincaré inequality on balls: variance ≤ C·R²·Dirichlet form.
    This is crucial for the finite-dimensionality argument. -/
theorem poincare_inequality_ball (R : ℕ) (f : G → ℝ) (support : Finset G)
    (hsupp : ↑support ⊆ CayleyBall S R) :
    variance f support ≤ R ^ 2 * DirichletForm S f support := by
  sorry

/-- Spectral gap version of Poincaré: if the first non-zero eigenvalue is spectralGap,
    then variance ≤ (1/spectralGap) · Dirichlet. -/
theorem poincare_spectral_gap (spectralGap : ℝ) (hGap : spectralGap > 0) (f : G → ℝ) (support : Finset G)
    (hGap_bound : ∀ g : G → ℝ, (∀ x ∉ support, g x = 0) →
      (∑ x ∈ support, g x = 0) →
      DirichletForm S g support ≥ spectralGap * l2NormSq g support) :
    variance f support ≤ (1 / spectralGap) * DirichletForm S f support := by
  sorry

end PoincareInequality

/-! ## Harmonic Functions and Laplacian Kernel -/

section HarmonicKernel

variable (S : Set G) [Fintype S]

/-- A function is harmonic iff it's in the kernel of the Laplacian. -/
theorem harmonic_eq_kernel_laplacian (hS_sym : S⁻¹ = S) (hS_ne : S.Nonempty) (f : G → ℝ) :
    IsHarmonic S f ↔ DiscreteLaplacian S f = 0 := by
  have hS_sym' : Gromov.IsSymmetric S := fun s hs => by
    have : s⁻¹⁻¹ ∈ S⁻¹ := by rw [hS_sym]; simp only [inv_inv]; exact hs
    simp only [inv_inv] at this
    exact this
  rw [isHarmonic_iff_isHarmonicSymmetric S hS_sym' f]
  exact harmonic_iff_kernel S hS_ne f

/-- Orthogonal decomposition: f = h + r where h is harmonic and r is orthogonal to harmonics.
    This is the projection onto the space of harmonic functions. -/
theorem orthogonal_decomposition (f : G → ℝ) (support : Finset G)
    (hf : ∀ x ∉ support, f x = 0)
    (hsupp : ∀ x ∈ support, ∀ s : S, x * s.val ∈ support) :
    ∃ (h r : G → ℝ), IsHarmonic S h ∧
      (∀ x ∉ support, h x = 0) ∧
      (∀ x ∉ support, r x = 0) ∧
      f = h + r ∧
      l2InnerProduct h r support = 0 := by
  sorry

end HarmonicKernel

/-! ## Spectral Gap and Amenability -/

section SpectralGapAmenability

variable (S : Set G) [Fintype S]

/-- Polynomial growth implies spectral gap is zero (amenability).
    This connects growth theory to spectral theory. -/
theorem spectralGap_zero_of_polynomial_growth (hpoly : HasPolynomialGrowth G) :
    ∀ ε > 0, ∃ f : G → ℝ, ∃ support : Finset G, (∀ x ∉ support, f x = 0) ∧
      (↑support ⊆ CayleyBall S 1) ∧
      l2NormSq f support = 1 ∧
      DirichletForm S f support < ε := by
  sorry

end SpectralGapAmenability

end

end Gromov.Harmonic.SelfAdjoint
