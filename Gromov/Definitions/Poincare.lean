/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Discrete Poincare inequality definitions on Cayley graphs.
-/

module

public import Gromov.Definitions.PolynomialGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Finprod

namespace Gromov

@[expose] public section

open scoped BigOperators

variable {G : Type*} [Group G]

/-! ## Edge Gradient

The edge gradient measures the difference of a function across an edge in the Cayley graph.
For a function f : G -> R and an edge (g, g*s) where s is a generator,
the gradient is f(g*s) - f(g).
-/

/-- The edge gradient of f at (g, s): the difference f(g*s) - f(g).
    This measures how f changes along the edge from g to g*s in the Cayley graph. -/
def edgeGradient (f : G -> Real) (g : G) (s : G) : Real :=
  f (g * s) - f g

/-- The squared edge gradient -/
def edgeGradientSq (f : G -> Real) (g : G) (s : G) : Real :=
  (edgeGradient f g s) ^ 2

/-! ## Dirichlet Energy

The Dirichlet energy measures the total variation of a function on a set,
summing the squared gradients over all edges emanating from vertices in the set.
-/

/-- The Dirichlet energy of f on a finite set A with respect to generators Sfin.
    This is the sum over all g in A and all s in Sfin of |f(g*s) - f(g)|^2. -/
noncomputable def dirichletEnergy (f : G -> Real) (A : Finset G) (Sfin : Finset G) : Real :=
  Finset.sum A (fun g => Finset.sum Sfin (fun s => edgeGradientSq f g s))

/-! ## L^2 Norm on Finite Sets

The L^2 norm (squared) of a function on a finite set is the sum of squares of function values.
-/

/-- The L^2 norm squared of f on a finite set A: sum_{g in A} |f(g)|^2 -/
noncomputable def l2NormSq (f : G -> Real) (A : Finset G) : Real :=
  Finset.sum A (fun g => (f g) ^ 2)

/-! ## Mean of a Function on a Finite Set -/

/-- The mean of f on a nonempty finite set A: (1/|A|) * sum_{g in A} f(g) -/
noncomputable def meanValue (f : G -> Real) (A : Finset G) : Real :=
  (A.card : Real)⁻¹ * Finset.sum A f

/-- A function centered at its mean: f - mean(f) -/
noncomputable def centerAtMean (f : G -> Real) (A : Finset G) : G -> Real :=
  fun g => f g - meanValue f A

/-! ## Poincare Inequality Constants -/

/-- The Poincare constant for a ball of radius r -/
noncomputable def poincareConstant (_r : Nat) : Real := 1

/-! ## Harmonic Functions on Finite Sets -/

/-- A function is harmonic at g if its value equals the average over neighbors.
    For a Cayley graph with symmetric generating set S, this means:
    f(g) = (1/|S|) * sum_{s in S} f(g*s) -/
def IsHarmonicAt (f : G -> Real) (g : G) (Sfin : Finset G) : Prop :=
  f g * Sfin.card = Finset.sum Sfin (fun s => f (g * s))

/-- A function is harmonic on a set if it is harmonic at every point in the set -/
def IsHarmonicOn (f : G -> Real) (A : Finset G) (Sfin : Finset G) : Prop :=
  forall g, g ∈ A -> IsHarmonicAt f g Sfin

/-! ## Variance -/

/-- The variance of f on A: the mean of squared deviations from the mean -/
noncomputable def variance (f : G -> Real) (A : Finset G) : Real :=
  meanValue (fun g => (f g - meanValue f A) ^ 2) A

end

end Gromov
