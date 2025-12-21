/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Descent argument definitions for Gromov's theorem.
-/

module

public import Gromov.Definitions.PolynomialGrowth
public import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Gromov

@[expose] public section

variable {G : Type*} [Group G]

/-! ## Infinite Cyclic Quotient -/

/-- A group `G` has an infinite cyclic quotient if there exists a surjective homomorphism
    from `G` onto `Multiplicative ℤ` (the multiplicative version of the integers). -/
def HasInfiniteCyclicQuotient (G : Type*) [Group G] : Prop :=
  ∃ φ : G →* Multiplicative ℤ, Function.Surjective φ

/-! ## Polynomial Growth Degree for Groups -/

/-- The polynomial growth degree of a finitely generated group, defined as the infimum
    of exponents d such that some generating set has growth function bounded by C * n^d.

    For a group without polynomial growth, this returns 0 by convention (sInf of empty set).
    For finite groups, this is 0.
    For Z, this is 1.
    For Z^n, this is n.
-/
noncomputable def PolynomialGrowthDegree (G : Type*) [Group G] : ℕ :=
  sInf {d : ℕ | ∃ (S : Set G), S.Finite ∧ Subgroup.closure S = ⊤ ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n > 0, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d}

/-- A group has polynomial growth of degree at most d if there exists a finite generating set
    whose growth function is bounded by C * n^d. -/
def HasPolynomialGrowthDegree (G : Type*) [Group G] (d : ℕ) : Prop :=
  ∃ (S : Set G), S.Finite ∧ Subgroup.closure S = ⊤ ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n > 0, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d

end

end Gromov
