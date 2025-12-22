/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Fitting subgroup theory for polycyclic groups.
-/

import Gromov.Proofs.Polycyclic.Core

set_option linter.style.emptyLine false
set_option linter.style.longLine false

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
  -- Proof strategy:
  -- 1. The Fitting subgroup is defined as sSup of normal subgroups
  -- 2. sSup of normal subgroups is normal (each N_i is invariant under conjugation)
  -- 3. For any g ∈ G and x ∈ Fitting(G), x is in some normal N, so gxg^{-1} ∈ N ⊆ Fitting(G)
  sorry

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
  sorry

/-- The Fitting subgroup is the largest normal nilpotent subgroup.

This combines the previous results: Fitting(G) is normal nilpotent, and
any normal nilpotent subgroup is contained in it.
-/
theorem fittingSubgroup_eq_largest : fittingSubgroup G = sSup { N : Subgroup G | N.Normal ∧ IsNilpotent N } :=
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
    sorry
  · -- Fitting subgroup is nilpotent
    sorry
  · -- Fitting subgroup has finite index in polycyclic groups
    exact fittingSubgroup_finiteIndex_of_polycyclic hP

end Group
