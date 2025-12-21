/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Gromov's Polynomial Growth Theorem - Main Result

This file contains the statement and proof of Gromov's celebrated theorem:
A finitely generated group has polynomial growth if and only if it is virtually nilpotent.
-/

import Gromov.NilpotentGrowth
import Gromov.Descent

/-!
# Gromov's Polynomial Growth Theorem

## Main Result

* `GromovPolynomialGrowthTheorem`: A finitely generated group has polynomial growth
  if and only if it is virtually nilpotent.

## Proof Overview

The theorem has two directions:

**Reverse direction (←)**: Virtually nilpotent implies polynomial growth.
This is Wolf's theorem (1968). The proof proceeds by induction on nilpotency class,
using that:
- Abelian groups have polynomial growth (degree = rank)
- Central extensions preserve polynomial growth with controlled degree increase
- Finite-index subgroups have comparable growth

**Forward direction (→)**: Polynomial growth implies virtually nilpotent.
This is the hard direction, proved by Gromov (1981) and simplified by Kleiner (2010).
The proof uses:
- Harmonic functions on Cayley graphs
- Colding-Minicozzi theory (polynomial growth ⟹ finite-dimensional harmonic space)
- Extraction of infinite cyclic quotients from the harmonic representation
- Inductive descent on growth degree

## References

* Gromov, M. "Groups of polynomial growth and expanding maps" (1981)
* Kleiner, B. "A new proof of Gromov's theorem on groups of polynomial growth" (2010)
* Wolf, J. "Growth of finitely generated solvable groups" (1968)
* Bass, H. "The degree of polynomial growth of finitely generated nilpotent groups" (1972)
-/

open GromovPolynomialGrowth NilpotentGrowth Descent

variable {G : Type*} [Group G]

/-- **Gromov's Polynomial Growth Theorem**: A finitely generated group has polynomial growth
if and only if it is virtually nilpotent.

This is one of the most celebrated theorems in geometric group theory. -/
theorem GromovPolynomialGrowthTheorem [Group.FG G] :
    HasPolynomialGrowth G ↔ Group.IsVirtuallyNilpotent G := by
  constructor
  · -- (→) Polynomial growth implies virtually nilpotent (Gromov/Kleiner)
    exact isVirtuallyNilpotent_of_polynomialGrowth
  · -- (←) Virtually nilpotent implies polynomial growth (Wolf)
    exact IsVirtuallyNilpotent.hasPolynomialGrowth
