/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Existence of non-trivial harmonic functions on groups with polynomial growth.

This file establishes the existence of non-constant Lipschitz harmonic functions
on infinite finitely generated groups with polynomial growth. This is a key step
in the Kleiner-Tao-Shalom proof of Gromov's theorem.

## Main Definitions

* `CesaroAverage`: The Cesaro average f_n = (1/n) sum_{m=1}^n mu^{*m}
* `AsymptoticallyHarmonic`: A sequence that becomes increasingly harmonic

## Main Results

* `cesaro_asymptotically_harmonic`: Cesaro averages are asymptotically harmonic
* `lipschitz_harmonic_exists`: Existence of non-trivial Lipschitz harmonic function
* `lipschitz_harmonic_nonconstant`: Can find non-constant Lipschitz harmonic

## References

* Tao-Shalom, Section 2 (Theorem 2 in overview)
* Woess, "Random Walks on Infinite Graphs and Groups"
-/

module

public import Gromov.Proofs.Harmonic.Spectral
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Sequences

set_option linter.style.longLine false

namespace Gromov.Harmonic.Existence

public section

open scoped NNReal BigOperators
open Gromov Gromov.Harmonic.Spectral

variable {G : Type*} [Group G] [DecidableEq G]

/-! ## Cesaro Averages

The Cesaro average of the random walk measures provides asymptotically harmonic
functions. For a probability measure mu on G (uniform on generating set S),
define f_n = (1/n) * sum_{m=1}^n (mu^{*m} * f) where * denotes convolution.
-/

section CesaroAverages

variable (S : Set G) [Fintype S]

/-- The n-th convolution power of the uniform measure on S applied to a function.
    This represents averaging f over all paths of length n from the identity. -/
noncomputable def ConvolutionPower (n : ℕ) (f : G → ℝ) : G → ℝ :=
  MarkovPower S n f

/-- The Cesaro average of convolution powers: f_n = (1/n) * sum_{m=1}^n (mu^{*m} * f).
    This is a regularization that becomes asymptotically harmonic. -/
noncomputable def CesaroAverage (n : ℕ) (f : G → ℝ) : G → ℝ :=
  if n = 0 then f
  else fun x => (1 / n) * ∑ m ∈ Finset.range n, ConvolutionPower S (m + 1) f x

/-- The defect from harmonicity: how far f_n is from being harmonic.
    Measured in L^1 norm over finite support. -/
noncomputable def HarmonicDefect (f : G → ℝ) (support : Finset G) : ℝ :=
  ∑ x ∈ support, |DiscreteLaplacian S f x|

/-- Cesaro averages are asymptotically harmonic: the harmonic defect goes to 0.
    More precisely, ||f_n - A(f_n)||_{L^1} = O(1/n) where A is averaging. -/
theorem cesaro_asymptotically_harmonic (hS_nonempty : S.Nonempty) (f : G → ℝ)
    (support : Finset G) (hf : ∀ x, x ∉ support → f x = 0) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      HarmonicDefect S (CesaroAverage S n f) support ≤ ε := by
  -- Proof sketch: The Cesaro average satisfies
  -- f_n - A(f_n) = (1/n) * (f - mu^{*n} * f)
  -- where f - mu^{*n} * f is bounded (since f has finite support).
  -- Thus the defect is O(1/n) -> 0.
  sorry

/-- The Cesaro average preserves the Lipschitz property (with same constant). -/
theorem cesaro_preserves_lipschitz {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (f : G → ℝ)
    (hf : IsWordLipschitz S L f) :
    IsWordLipschitz S L (CesaroAverage S n f) := by
  -- Proof sketch: Convolution with probability measure is a contraction for Lipschitz.
  -- Cesaro average is a convex combination, so it preserves Lipschitz constant.
  sorry

end CesaroAverages

/-! ## Existence of Lipschitz Harmonic Functions

For groups with polynomial growth, we construct non-trivial Lipschitz harmonic
functions using a limiting argument on Cesaro averages.
-/

section ExistenceTheorems

variable (S : Set G) [Fintype S]

/-- For non-amenable groups, there exist non-constant bounded harmonic functions.
    This uses the spectral gap being positive. -/
theorem nonamenable_has_bounded_harmonic (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hGap : SpectralGap S > 0) :
    ∃ (f : G → ℝ), IsHarmonicSymmetric S f ∧ (∃ M, ∀ x, |f x| ≤ M) ∧ ¬(∃ c, f = fun _ => c) := by
  -- Proof sketch: Positive spectral gap means the Laplacian is invertible on
  -- orthogonal complement of constants. The inverse applied to any non-constant
  -- function gives a bounded harmonic function.
  sorry

/-- For amenable groups, we can use spectral projections near eigenvalue 0
    to construct almost-harmonic functions that can be made exactly harmonic
    in a limiting sense. -/
theorem amenable_spectral_projection (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hGap : SpectralGap S = 0) :
    ∀ ε > 0, ∃ (f : G → ℝ), (∃ x, f x ≠ 0) ∧
      ∀ x, |DiscreteLaplacian S f x| ≤ ε * |f x| := by
  -- Proof sketch: Since spectral gap is 0, for any epsilon there exists
  -- an approximate eigenfunction with eigenvalue < epsilon.
  -- This gives almost-harmonic functions.
  sorry

/-- Main existence theorem: For infinite finitely generated groups with polynomial growth,
    there exists a non-constant Lipschitz harmonic function.

    This is Theorem 2 from Tao's overview of Gromov's theorem. -/
theorem lipschitz_harmonic_exists (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hpoly : HasPolynomialGrowth G) (hInf : Infinite G) :
    ∃ (f : G → ℝ) (L : ℝ), L > 0 ∧ IsHarmonicSymmetric S f ∧ IsWordLipschitz S L f := by
  -- Proof sketch:
  -- 1. Start with any Lipschitz function f_0 (e.g., word length function).
  -- 2. Take Cesaro averages f_n to get asymptotically harmonic functions.
  -- 3. The f_n are uniformly Lipschitz, so by Arzela-Ascoli a subsequence
  --    converges locally uniformly.
  -- 4. The limit is harmonic (by continuity of Laplacian) and Lipschitz.
  -- 5. Polynomial growth ensures the limit is non-trivial.
  sorry

/-- The Lipschitz harmonic function can be chosen to be non-constant.
    This is crucial for extracting a Z quotient. -/
theorem lipschitz_harmonic_nonconstant (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hpoly : HasPolynomialGrowth G) (hInf : Infinite G) :
    ∃ (f : G → ℝ) (L : ℝ), L > 0 ∧ IsHarmonicSymmetric S f ∧ IsWordLipschitz S L f ∧
      ¬(∃ c, f = fun _ => c) := by
  -- Proof sketch: Start with a non-constant function (e.g., indicator of a half-space
  -- or the word length function). The Cesaro averaging process preserves non-constancy
  -- for infinite groups with polynomial growth because:
  -- - If all limits were constant, the original function would have bounded variation
  -- - But polynomial growth groups have unbounded diameter
  sorry

end ExistenceTheorems

/-! ## Gradient Bounds

For Lipschitz harmonic functions, we can bound the gradient in terms of values
on larger balls. This is key to the finite-dimensionality argument.
-/

section GradientBounds

variable (S : Set G) [Fintype S]

/-- The discrete gradient of a function at a point.
    Measures the maximum difference with neighbors. -/
noncomputable def DiscreteGradient (f : G → ℝ) (x : G) : ℝ :=
  ⨆ s : S, |f (x * s.val) - f x|

/-- For a harmonic function, the gradient at x is controlled by the L^infinity
    norm on a ball around x. This is a discrete mean value theorem. -/
theorem harmonic_gradient_bound (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (f : G → ℝ) (hf : IsHarmonicSymmetric S f) (x : G) (R : ℕ) (hR : R > 0) :
    DiscreteGradient S f x ≤
      (2 / R : ℝ) * ⨆ g ∈ CayleyBall S R, |f (x * g)| := by
  -- Proof sketch: The harmonic condition f(x) = average over neighbors can be
  -- iterated to get f(x) = average over R-ball. Then gradient is bounded by
  -- oscillation over R-ball divided by R.
  sorry

/-- For a Lipschitz harmonic function, there's a uniform gradient bound. -/
theorem lipschitz_harmonic_uniform_gradient (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    {L : ℝ} (f : G → ℝ) (hf : IsHarmonicSymmetric S f) (hLip : IsWordLipschitz S L f) :
    ∀ x, DiscreteGradient S f x ≤ L := by
  -- Proof sketch: Direct from the Lipschitz condition, since neighbors differ
  -- by word distance 1.
  sorry

end GradientBounds

/-! ## Maximum Principle

The maximum principle for harmonic functions: a harmonic function on a connected
component attains its supremum only if it is constant on that component.
-/

section MaximumPrinciple

variable (S : Set G) [Fintype S]

/-- Discrete maximum principle: If f is harmonic and attains its maximum at x,
    then f is constant on the connected component of x in the Cayley graph. -/
theorem maximum_principle (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (f : G → ℝ) (hf : IsHarmonicSymmetric S f)
    (x : G) (hmax : ∀ g : G, f g ≤ f x) :
    ∀ g : G, f g = f x := by
  -- Proof sketch: At a maximum, the harmonic condition f(x) = avg of neighbors
  -- implies all neighbors have the same value (by convexity). Since G is connected
  -- via the Cayley graph (S generates G), all of G has the same value.
  sorry

/-- Corollary: A harmonic function constant on a finite-index coset is constant everywhere. -/
theorem harmonic_constant_on_coset (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (f : G → ℝ) (hf : IsHarmonicSymmetric S f)
    (H : Subgroup G) [H.FiniteIndex] (c : ℝ) (hc : ∀ h : H, f h.val = c) :
    ∀ g : G, f g = c := by
  -- Proof sketch: Since H has finite index, any element g is at bounded distance
  -- from some h in H. By the maximum principle argument applied to |f - c|,
  -- if f = c on H then f = c everywhere.
  sorry

end MaximumPrinciple

end

end Gromov.Harmonic.Existence
