/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Definitions for polynomial growth of groups.

This file contains the core definitions needed to state Gromov's theorem.
All proofs and lemmas are in Gromov/Proofs/.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Real.Basic

namespace Gromov

@[expose] public section

/-!
# Polynomial Growth Definitions

## Main Definitions

* `CayleyBall S n`: Elements expressible as products of at most `n` generators from `S`
* `GrowthFunction S n`: The cardinality of `CayleyBall S n`
* `HasPolynomialGrowth G`: Group `G` has polynomial growth
-/

variable {G : Type*} [Group G]

/-- The Cayley ball of radius `n` with respect to generating set `S`:
    elements expressible as products of at most `n` generators or their inverses. -/
def CayleyBall (S : Set G) (n : ℕ) : Set G :=
  {g : G | ∃ (l : List G), l.length ≤ n ∧ (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) ∧ l.prod = g}

/-- The growth function counts elements in the Cayley ball of radius `n`. -/
noncomputable def GrowthFunction (S : Set G) (n : ℕ) : ℕ :=
  (CayleyBall S n).ncard

variable (G)

/-- A group has polynomial growth if there exists a finite generating set `S` such that
    the growth function is bounded by a polynomial. -/
def HasPolynomialGrowth : Prop :=
  ∃ (S : Set G), Set.Finite S ∧ Subgroup.closure S = ⊤ ∧
    ∃ (C : ℝ) (d : ℕ), C > 0 ∧
    ∀ n > 0, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d

end

end Gromov
