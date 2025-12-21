/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Word metric definitions for Cayley graphs.
-/

module

public import Gromov.Definitions.PolynomialGrowth
public import Mathlib.Data.Nat.Lattice

namespace Gromov

@[expose] public section

variable {G : Type*} [Group G]

/-! ## Word Length / Word Metric

The word length of an element g with respect to a generating set S is the minimal
length of a word in S and S⁻¹ that represents g.
-/

/-- The set of lengths of words representing g using generators from S -/
def wordLengths (S : Set G) (g : G) : Set ℕ :=
  {n : ℕ | g ∈ CayleyBall S n}

/-- The word length of `g` with respect to generating set `S`:
    the minimal length of a product of generators (or their inverses) equal to `g`.
    This is the infimum of all valid word lengths. -/
noncomputable def wordLength (S : Set G) (g : G) : ℕ :=
  sInf (wordLengths S g)

/-- The word metric distance between two elements -/
noncomputable def wordDist (S : Set G) (g h : G) : ℕ :=
  wordLength S (g⁻¹ * h)

/-! ## Symmetric Generating Sets -/

/-- A generating set is symmetric if it's closed under inverses -/
abbrev IsSymmetric (S : Set G) : Prop := ∀ s ∈ S, s⁻¹ ∈ S

end

end Gromov
