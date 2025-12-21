/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Growth degree definitions for polynomial growth.
-/

module

public import Gromov.Definitions.PolynomialGrowth
public import Mathlib.Data.Real.Basic

namespace Gromov

@[expose] public section

/-! ## Asymptotic Definitions -/

/-- A function `f : ℕ → ℕ` is polynomially bounded with degree `d` if there exists
    a constant `C > 0` such that `f n ≤ C * n^d` for all `n > 0`. -/
def IsPolynomiallyBounded (f : ℕ → ℕ) (d : ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n > 0, (f n : ℝ) ≤ C * (n : ℝ) ^ d

/-- A function has some polynomial bound if it is polynomially bounded for some degree. -/
def HasSomePolynomialBound (f : ℕ → ℕ) : Prop :=
  ∃ d : ℕ, IsPolynomiallyBounded f d

/-- The set of degrees `d` for which `f` is polynomially bounded. -/
def PolynomialBoundDegrees (f : ℕ → ℕ) : Set ℕ :=
  {d : ℕ | IsPolynomiallyBounded f d}

/-- The growth degree of a function is the infimum of all valid polynomial bounds.
    Returns 0 if the function has no polynomial bound (by convention). -/
noncomputable def GrowthDegree (f : ℕ → ℕ) : ℕ :=
  sInf (PolynomialBoundDegrees f)

end

end Gromov
