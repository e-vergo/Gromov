/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Gromov's Polynomial Growth Theorem - Statement

This file contains ONLY the statement of Gromov's theorem.
The proof is in ProofOfMainTheorem.lean (machine-verified).

HUMAN REVIEW REQUIRED: This file defines what is being proven.
-/

module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Finiteness
public import Gromov.Definitions.PolynomialGrowth

namespace Gromov

@[expose] public section

/-!
# Gromov's Polynomial Growth Theorem - Statement

A finitely generated group has polynomial growth if and only if it is virtually nilpotent.

## References

* Gromov, M. "Groups of polynomial growth and expanding maps" (1981)
* Kleiner, B. "A new proof of Gromov's theorem on groups of polynomial growth" (2010)
-/

/-- **Statement of Gromov's Polynomial Growth Theorem**:
A finitely generated group has polynomial growth if and only if it is virtually nilpotent. -/
def StatementOfTheorem : Prop :=
  ∀ (G : Type*) [Group G] [Group.FG G],
    HasPolynomialGrowth G ↔ Group.IsVirtuallyNilpotent G

end

end Gromov
