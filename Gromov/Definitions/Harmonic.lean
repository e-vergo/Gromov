/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Harmonic function definitions on Cayley graphs.
-/

module

public import Gromov.Definitions.WordMetric
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Module.Basic

namespace Gromov

@[expose] public section

open scoped NNReal

variable {G : Type*} [Group G]

/-! ## Harmonic Functions on Groups

A function f : G → ℝ is harmonic with respect to a finite symmetric generating set S if
at every point g, the value f(g) equals the average of f over the neighbors of g in the
Cayley graph. For a symmetric generating set, this means:

  sum over s in S of f(g * s) = |S| * f(g)

For a general generating set where we use both s and s^(-1) as edges:

  sum over s in S of (f(g * s) + f(g * s^(-1))) = 2 * |S| * f(g)
-/

section Harmonic

variable (S : Set G)

/-- A function f : G → ℝ is harmonic with respect to generating set S if at every point,
    the sum over all neighbors equals 2 * |S| times the value at that point.
    This captures the discrete Laplacian condition Δf = 0. -/
def IsHarmonic [Fintype S] (f : G → ℝ) : Prop :=
  ∀ g : G, ∑ s : S, (f (g * s.val) + f (g * s.val⁻¹)) = 2 * (Fintype.card S) * f g

/-- Alternative definition for symmetric generating sets: the sum over S equals |S| * f(g) -/
def IsHarmonicSymmetric [Fintype S] (f : G → ℝ) : Prop :=
  ∀ g : G, ∑ s : S, f (g * s.val) = (Fintype.card S) * f g

end Harmonic

/-! ## Lipschitz Functions with respect to Word Metric -/

section Lipschitz

variable (S : Set G)

/-- A function f : G → ℝ is L-Lipschitz with respect to the word metric if
    |f(g) - f(h)| ≤ L * wordDist S g h for all g, h. -/
def IsWordLipschitz (L : ℝ) (f : G → ℝ) : Prop :=
  ∀ g h : G, |f g - f h| ≤ L * (wordDist S g h : ℝ)

/-- Non-negative Lipschitz constant version -/
def IsWordLipschitz' (L : ℝ≥0) (f : G → ℝ) : Prop :=
  ∀ g h : G, |f g - f h| ≤ L * (wordDist S g h : ℝ)

end Lipschitz

/-! ## Space of Lipschitz Harmonic Functions -/

section LipschitzHarmonicSpace

variable (S : Set G) [Fintype S]

/-- The space H_L(G,S) of L-Lipschitz harmonic functions.
    This is a key object in the proof of Gromov's theorem: its finite-dimensionality
    is used to construct a representation of G. -/
def LipschitzHarmonicSpace (L : ℝ) : Set (G → ℝ) :=
  {f | IsHarmonic S f ∧ IsWordLipschitz S L f}

/-- The space of Lipschitz harmonic functions with non-negative constant -/
def LipschitzHarmonicSpace' (L : ℝ≥0) : Set (G → ℝ) :=
  {f | IsHarmonic S f ∧ IsWordLipschitz S L f}

end LipschitzHarmonicSpace

end

end Gromov
