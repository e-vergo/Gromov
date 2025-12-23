/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Fitting subgroup theory for polycyclic groups.
-/

import Gromov.Proofs.Polycyclic.Core

/-!
# Fitting Subgroup Theory

This file develops the theory of the Fitting subgroup, which is the largest normal
nilpotent subgroup of a group. The main result is that in polycyclic groups, the
Fitting subgroup has finite index.

## Main Definitions

* `fittingSubgroup G`: The Fitting subgroup of G, defined as the join of all normal
  nilpotent subgroups. Equivalently, it is the largest normal nilpotent subgroup.

## Main Results

* `fittingSubgroup_normal`: The Fitting subgroup is normal.
* `fittingSubgroup_nilpotent`: The Fitting subgroup is nilpotent.
* `fittingSubgroup_le`: If N is normal and nilpotent, then N ≤ Fitting(G).
* `fittingSubgroup_finiteIndex_of_polycyclic`: In polycyclic groups, the Fitting
  subgroup has finite index.

## Mathematical Background

The Fitting subgroup is a fundamental object in the study of solvable and
polycyclic groups. Key facts:

1. The Fitting subgroup exists and is unique (it's the join of all normal nilpotent
   subgroups, which is itself normal nilpotent).

2. For finite groups, the Fitting subgroup equals the largest normal nilpotent
   subgroup and is the nilpotent radical.

3. For polycyclic groups, Fitting(G) has finite index. This is crucial for proving
   that polycyclic groups are virtually nilpotent.

4. The quotient G/Fitting(G) for polycyclic G is a finite group whose Fitting
   subgroup is trivial (such groups are called "Fitting-free").

## References

* Segal, D. "Polycyclic Groups" Cambridge University Press (1983), Theorem 1.3
* Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Section 5.2
* Hall, P. "On the Finiteness of Certain Soluble Groups" (1959)
-/

open Subgroup Group

namespace Group

variable {G : Type*} [Group G]

/-! ### Definition of the Fitting Subgroup -/

/-- The Fitting subgroup of a group G is the join (supremum) of all normal nilpotent
subgroups of G.

This is the largest normal nilpotent subgroup. The key non-trivial fact is that
this join is itself nilpotent (the join of two normal nilpotent subgroups is
nilpotent, so by Zorn's lemma or direct construction, the supremum is nilpotent).

Note: For infinite groups, care must be taken with the nilpotency class.
For polycyclic groups, the Fitting subgroup has bounded nilpotency class.
-/
def fittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  sSup { N : Subgroup G | N.Normal ∧ IsNilpotent N }

/-! ### Basic Properties of the Fitting Subgroup -/

/-- The Fitting subgroup is normal.

This follows from the fact that the supremum of normal subgroups is normal:
if all N_i are normal and g ∈ G, then gN_ig^{-1} = N_i for all i, so
g(sSup N_i)g^{-1} = sSup (gN_ig^{-1}) = sSup N_i.
-/
theorem fittingSubgroup_normal : (fittingSubgroup G).Normal := by
  -- Proof: sSup of normal subgroups is normal
  -- For n ∈ fittingSubgroup G = sSup { N | N.Normal ∧ IsNilpotent N },
  -- we show g * n * g⁻¹ ∈ fittingSubgroup G
  constructor
  intro n hn g
  -- The fitting subgroup equals the closure of the union of all normal nilpotent subgroups
  have h_eq : fittingSubgroup G =
      Subgroup.closure (⋃ N ∈ { M : Subgroup G | M.Normal ∧ IsNilpotent M }, (N : Set G)) := by
    unfold fittingSubgroup
    apply le_antisymm
    · apply sSup_le; intro N hN x hx; apply Subgroup.subset_closure; exact Set.mem_biUnion hN hx
    · rw [Subgroup.closure_le]; intro x hx
      rw [Set.mem_iUnion] at hx; obtain ⟨N, hx⟩ := hx
      rw [Set.mem_iUnion] at hx; obtain ⟨hN, hxN⟩ := hx
      exact le_sSup hN hxN
  rw [h_eq] at hn ⊢
  -- Use induction on the closure with predicate P(x) := g * x * g⁻¹ ∈ closure(union)
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    -- x is in the union of all normal nilpotent N
    rw [Set.mem_iUnion] at hx; obtain ⟨N, hx⟩ := hx
    rw [Set.mem_iUnion] at hx; obtain ⟨hN, hxN⟩ := hx
    have h_conj : g * x * g⁻¹ ∈ N := hN.1.conj_mem x hxN g
    apply Subgroup.subset_closure
    rw [Set.mem_iUnion]; use N
    rw [Set.mem_iUnion]; use hN
    exact h_conj
  | one =>
    apply Subgroup.subset_closure
    -- Need to show g * 1 * g⁻¹ ∈ union - it equals 1, pick the bottom subgroup
    rw [Set.mem_iUnion]; use ⊥
    rw [Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · constructor <;> infer_instance
    · simp
  | mul x y _ _ ihx_conj ihy_conj =>
    -- ihx_conj : g * x * g⁻¹ ∈ closure(...), ihy_conj : g * y * g⁻¹ ∈ closure(...)
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ihx_conj ihy_conj
  | inv x _ ihx_conj =>
    -- ihx_conj : g * x * g⁻¹ ∈ closure(...)
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ihx_conj

/-- The Fitting subgroup is nilpotent.

This is the non-trivial part of the Fitting subgroup construction. The proof uses:
1. The join of two normal nilpotent subgroups M, N is nilpotent with class ≤ c(M) + c(N)
2. By transfinite induction (or Zorn's lemma), the supremum is nilpotent

For polycyclic groups, we can give a more direct argument using the ascending
chain condition on normal subgroups.

References:
- Fitting, H. "Beitrage zur Theorie der Gruppen endlicher Ordnung" (1938)
- Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.2.8
-/
theorem fittingSubgroup_nilpotent : IsNilpotent (fittingSubgroup G) := by
  -- Proof strategy (for general groups):
  -- 1. Let F = Fitting(G) = sSup { N : N normal, N nilpotent }
  -- 2. The key lemma: if M, N are normal nilpotent with classes c, d, then
  --    MN is normal nilpotent with class ≤ c + d
  -- 3. This is because [MN, MN] ⊆ [M, M][N, N][M, N] and [M, N] ⊆ M ∩ N
  -- 4. By transfinite induction, the directed union/supremum is nilpotent
  --
  -- For polycyclic groups (our main case):
  -- 1. Polycyclic groups satisfy ACC on normal subgroups
  -- 2. So Fitting(G) = M_1 ∨ M_2 ∨ ... ∨ M_k for finitely many normal nilpotent M_i
  -- 3. Apply the lemma finitely many times

  -- Key insight: We use the fact that the Fitting subgroup is defined as a supremum
  -- of normal nilpotent subgroups. The challenge is showing this supremum is itself
  -- nilpotent, which requires the classical result that the product of two commuting
  -- normal nilpotent subgroups is nilpotent.

  -- This is a deep result from group theory (Robinson, Theorem 5.2.8) that would require
  -- substantial additional lemmas about commutators and the lower central series.
  -- For now, we assert this fundamental result.
  sorry

/-- Any normal nilpotent subgroup is contained in the Fitting subgroup.

This is the universal property of the Fitting subgroup: it is the largest
normal nilpotent subgroup.
-/
theorem fittingSubgroup_le (N : Subgroup G) [N.Normal] (hN : IsNilpotent N) :
    N ≤ fittingSubgroup G := by
  -- Proof strategy:
  -- 1. Fitting(G) = sSup { M : M normal, M nilpotent }
  -- 2. N is in this set (by hypothesis: N normal and nilpotent)
  -- 3. Therefore N ≤ sSup { M : M normal, M nilpotent } = Fitting(G)
  apply le_sSup
  exact ⟨inferInstance, hN⟩

/-- The Fitting subgroup is the largest normal nilpotent subgroup.

This combines the previous results: Fitting(G) is normal nilpotent, and
any normal nilpotent subgroup is contained in it.
-/
theorem fittingSubgroup_eq_largest :
    fittingSubgroup G = sSup { N : Subgroup G | N.Normal ∧ IsNilpotent N } :=
  rfl

/-! ### Fitting Subgroup of Polycyclic Groups -/

/-- In polycyclic groups, the Fitting subgroup has finite index.

This is a fundamental theorem in the theory of polycyclic groups. The proof uses:
1. Polycyclic groups satisfy the maximal condition on subgroups (ACC)
2. The quotient G/Fitting(G) is polycyclic and has trivial Fitting subgroup
3. A polycyclic group with trivial Fitting subgroup is finite

The last step is the deepest: it uses that such groups embed into Aut(V) for
some finite-dimensional vector space V over Q, and the image is a finite group.

References:
- Segal, D. "Polycyclic Groups" (1983), Theorem 1.3
- Hall, P. "On the Finiteness of Certain Soluble Groups" (1959)
- Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.2.17
-/
theorem fittingSubgroup_finiteIndex_of_polycyclic (hP : IsPolycyclic G) :
    (fittingSubgroup G).FiniteIndex := by
  -- Proof strategy:
  -- 1. G is polycyclic, so G has max condition on subgroups
  -- 2. Consider the series G = G_0 > G_1 > ... > G_n = 1 (polycyclic series)
  -- 3. The Fitting subgroup F contains the last non-trivial term that is nilpotent
  -- 4. More precisely: F is the product of all abelian normal subgroups in the series
  -- 5. G/F is polycyclic with trivial Fitting subgroup
  -- 6. Key lemma: A polycyclic group with trivial Fitting subgroup is finite
  --    Proof of key lemma:
  --    a. Such a group embeds into GL(n, Z) for some n (by polycyclic representation theory)
  --    b. A solvable subgroup of GL(n, Z) with trivial Fitting subgroup is finite
  --    c. This uses the Auslander-Swan theorem and related results
  -- 7. Therefore [G : F] < ∞

  -- This is the fundamental theorem relating polycyclic groups to their Fitting subgroup.
  -- The proof requires several deep results:
  --  (a) Every normal subgroup of a polycyclic group is polycyclic
  --  (b) The quotient G/F(G) has trivial Fitting subgroup
  --  (c) A polycyclic group with trivial Fitting subgroup is finite
  --      (this uses embedding into GL(n,Z) and properties of integer matrices)
  --
  -- References:
  -- - Segal, D. "Polycyclic Groups" Cambridge University Press (1983), Theorem 1.3
  -- - Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.2.17
  -- - Hall, P. "On the Finiteness of Certain Soluble Groups" (1959)
  --
  -- This requires substantial infrastructure for working with representations
  -- and matrix groups that goes beyond current Mathlib support.
  sorry

/-- Combining the above: polycyclic groups have a finite-index normal nilpotent subgroup.

This is a key step in proving that polycyclic groups are virtually nilpotent.
-/
theorem polycyclic_has_finiteIndex_nilpotent (hP : IsPolycyclic G) :
    ∃ N : Subgroup G, N.Normal ∧ IsNilpotent N ∧ N.FiniteIndex := by
  -- Proof strategy:
  -- 1. Take N = Fitting(G)
  -- 2. Fitting(G) is normal (fittingSubgroup_normal)
  -- 3. Fitting(G) is nilpotent (fittingSubgroup_nilpotent)
  -- 4. Fitting(G) has finite index (fittingSubgroup_finiteIndex_of_polycyclic)
  refine ⟨fittingSubgroup G, ?_, ?_, ?_⟩
  · -- Fitting subgroup is normal
    exact fittingSubgroup_normal
  · -- Fitting subgroup is nilpotent
    exact fittingSubgroup_nilpotent
  · -- Fitting subgroup has finite index in polycyclic groups
    exact fittingSubgroup_finiteIndex_of_polycyclic hP

end Group
