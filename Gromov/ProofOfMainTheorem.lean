/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Proof of Gromov's Polynomial Growth Theorem.

MACHINE VERIFIED - No human review required for this file.
-/

module

public import Mathlib
public import Gromov.MainTheorem
public import Gromov.Definitions.PolynomialGrowth
import Gromov.Proofs.Growth.Nilpotent
import Gromov.Proofs.Descent.Main

namespace Gromov

@[expose] public section

/-- **Gromov's Polynomial Growth Theorem**: A finitely generated group has polynomial growth
if and only if it is virtually nilpotent. -/
theorem mainTheorem : StatementOfTheorem := by
  intro G _ _
  constructor
  · -- (→) Polynomial growth implies virtually nilpotent (Gromov/Kleiner)
    exact Descent.isVirtuallyNilpotent_of_polynomialGrowth
  · -- (←) Virtually nilpotent implies polynomial growth (Wolf)
    exact NilpotentGrowth.IsVirtuallyNilpotent.hasPolynomialGrowth

end

end Gromov
