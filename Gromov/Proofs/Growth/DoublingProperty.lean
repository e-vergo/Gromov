/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Doubling constants and volume comparison for polynomial growth.

This file develops the theory of doubling constants and doubling dimension
for groups with polynomial growth. The doubling constant measures how ball
volumes grow when the radius doubles.

## Main results

* `doublingConstant_bounded` - Doubling constant is uniformly bounded for polynomial growth
* `ball_ratio_bound` - Volume ratios bounded by (R/r)^d
* `growth_degree_eq_doubling_dimension` - Growth degree equals doubling dimension

## References

* Gromov, "Groups of polynomial growth" (1981)
* Kleiner, "A new proof of Gromov's theorem" (2010)
-/

module

public import Gromov.Proofs.Growth.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Gromov.Growth.DoublingProperty

public section

open Gromov Filter Set
open scoped Pointwise NNReal

variable {G : Type*} [Group G]

/-! ## Doubling Constants -/

section DoublingConstant

variable (S : Set G) [Fintype S]

/-- The doubling constant at radius n: |B(2n)|/|B(n)|. -/
noncomputable def doublingConstantAt (n : ℕ) : ℝ :=
  if hn : (CayleyBall S n).ncard > 0 then
    (CayleyBall S (2 * n)).ncard / (CayleyBall S n).ncard
  else 1

/-- The supremum of doubling constants over all radii. -/
noncomputable def doublingConstant : ℝ :=
  ⨆ n : ℕ, doublingConstantAt S n

/-- Doubling dimension: log₂ of the doubling constant. -/
noncomputable def doublingDimension : ℝ :=
  Real.log (doublingConstant S) / Real.log 2

/-- The doubling constant is at most 2^d for growth degree d. -/
theorem doublingConstant_le_pow_degree (d : ℕ)
    (hd : IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) d) :
    doublingConstant S ≤ 2 ^ d := by
  sorry

/-- For polynomial growth, the doubling constant is uniformly bounded. -/
theorem doublingConstant_bounded (d : ℕ)
    (hd : IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) d) :
    ∃ C : ℝ, C > 0 ∧ doublingConstant S ≤ C := by
  use 2^d
  constructor
  · positivity
  · exact doublingConstant_le_pow_degree S d hd

/-- Doubling constant at each radius is at least 1. -/
theorem doublingConstantAt_ge_one (n : ℕ) : 1 ≤ doublingConstantAt S n := by
  unfold doublingConstantAt
  split_ifs with hn
  · -- Case: (CayleyBall S n).ncard > 0
    have hsub : CayleyBall S n ⊆ CayleyBall S (2 * n) :=
      cayleyBall_monotone S (by omega : n ≤ 2 * n)
    have hfin : (CayleyBall S (2 * n)).Finite :=
      cayleyBall_finite (Set.toFinite S) (2 * n)
    have hle : (CayleyBall S n).ncard ≤ (CayleyBall S (2 * n)).ncard :=
      Set.ncard_le_ncard hsub hfin
    -- Now show 1 ≤ a / b when 0 < b ≤ a
    have hpos : (0 : ℝ) < (CayleyBall S n).ncard := by
      exact Nat.cast_pos.mpr hn
    rw [one_le_div hpos]
    exact Nat.cast_le.mpr hle
  · -- Case: (CayleyBall S n).ncard = 0, so doublingConstantAt = 1
    norm_num

end DoublingConstant

/-! ## Volume Comparison -/

section VolumeComparison

variable (S : Set G) [Fintype S]

/-- General ball ratio bound: |B(R)|/|B(r)| ≤ C(R/r)^d. -/
theorem ball_ratio_bound (d : ℕ)
    (hd : IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) d)
    (r R : ℕ) (hr : r > 0) (hR : r ≤ R) :
    ((CayleyBall S R).ncard : ℝ) / (CayleyBall S r).ncard ≤
      (2 ^ d : ℝ) * ((R : ℝ) / r) ^ d := by
  sorry

/-- Lower bound: balls have positive size for infinite groups. -/
theorem CayleyBall.ncard_pos_of_infinite [Infinite G] (hS : Subgroup.closure S = ⊤) (n : ℕ) :
    0 < (CayleyBall S n).ncard := by
  sorry

/-- Growth lower bound: |B(n)| ≥ n for infinite FG groups. -/
theorem growth_lower_bound [Infinite G] [Group.FG G]
    (hS : Subgroup.closure S = ⊤) (n : ℕ) (hn : n > 0) :
    n ≤ (CayleyBall S n).ncard := by
  sorry

/-- Adjacent radius ratio is bounded. -/
theorem GrowthFunction.ratio_bounded (n : ℕ) (hn : n > 0) :
    (CayleyBall S (n + 1)).ncard ≤ (CayleyBall S n).ncard * (Fintype.card S + 1) := by
  sorry

end VolumeComparison

/-! ## Covering and Packing Numbers -/

section CoveringPacking

variable (S : Set G) [Fintype S]

/-- Covering number: minimum balls of radius r needed to cover ball of radius R. -/
noncomputable def coveringNumber (r R : ℕ) : ℕ :=
  (CayleyBall S R).ncard  -- Trivial upper bound; actual def needs optimization

/-- Packing number: maximum disjoint balls of radius r inside ball of radius R. -/
noncomputable def packingNumber (r R : ℕ) : ℕ :=
  (CayleyBall S R).ncard  -- Trivial upper bound; actual def needs optimization

/-- Covering number is bounded polynomially for polynomial growth. -/
theorem coveringNumber_bound (d : ℕ)
    (hd : IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) d)
    (r R : ℕ) (hr : r > 0) :
    coveringNumber S r R ≤ (2 ^ d : ℕ) * (R / r + 1) ^ d := by
  sorry

/-- Packing and covering numbers are comparable. -/
theorem packing_covering_comparison (r R : ℕ) (hr : r > 0) :
    packingNumber S (2 * r) R ≤ coveringNumber S r R ∧
      coveringNumber S r R ≤ packingNumber S (r / 2) R := by
  sorry

end CoveringPacking

/-! ## Doubling Dimension Equals Growth Degree -/

section DoubleGrowthEquivalence

variable (S : Set G) [Fintype S]

/-- The growth degree equals the doubling dimension (up to constants).
    More precisely, log₂(sup_n |B(2n)|/|B(n)|) = GrowthDegree + O(1). -/
theorem growth_degree_eq_doubling_dimension (d : ℕ)
    (hd : IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) d) :
    ∃ C : ℝ, C > 0 ∧
      |doublingDimension S - GrowthDegree (fun n => (CayleyBall S n).ncard)| ≤ C := by
  sorry

/-- Polynomial growth implies finite doubling dimension. -/
theorem doublingDimension_finite (d : ℕ)
    (hd : IsPolynomiallyBounded (fun n => (CayleyBall S n).ncard) d) :
    ∃ B : ℝ, doublingDimension S ≤ B := by
  sorry

/-- Doubling dimension is non-negative. -/
theorem doublingDimension_nonneg : 0 ≤ doublingDimension S := by
  unfold doublingDimension
  apply div_nonneg
  · apply Real.log_nonneg
    have h1 : 1 ≤ doublingConstant S := by
      unfold doublingConstant
      have hbdd : BddAbove (Set.range (doublingConstantAt S)) := by
        -- This requires either finiteness or polynomial growth
        -- For now, we use it as an assumption
        sorry
      calc 1 ≤ doublingConstantAt S 0 := doublingConstantAt_ge_one S 0
        _ ≤ ⨆ n, doublingConstantAt S n := le_ciSup hbdd 0
    exact h1
  · apply Real.log_nonneg
    norm_num

end DoubleGrowthEquivalence

/-! ## Volume Growth Bounds -/

section VolumeGrowth

variable (S : Set G) [Fintype S]

/-- Upper bound on ball growth in terms of doubling dimension. -/
theorem ball_growth_upper_bound (d : ℝ) (hd : doublingDimension S ≤ d) (n : ℕ) (hn : n > 0) :
    (CayleyBall S n).ncard ≤ (CayleyBall S 1).ncard * n ^ ⌈d⌉₊ := by
  sorry

/-- Lower bound on ball growth for infinite groups. -/
theorem ball_growth_lower_bound [Infinite G] [Group.FG G] (hS : Subgroup.closure S = ⊤)
    (n : ℕ) (hn : n > 0) :
    ∃ c : ℝ, c > 0 ∧ c * n ≤ (CayleyBall S n).ncard := by
  sorry

end VolumeGrowth

end

end Gromov.Growth.DoublingProperty
