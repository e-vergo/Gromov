/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Definitions for Schreier theory: coset representatives and Schreier generators.

This file provides the core definitions needed for Schreier's lemma and its
quantitative refinements for growth bounds.

## Main Definitions

* `IsCosetRepSet`: A set R is a set of coset representatives for H in G
* `schreierGenerators`: The Schreier generators of H w.r.t. generators S and transversal R

## References

* Mathlib.GroupTheory.Schreier
* Schreier, O. "Die Untergruppen der freien Gruppen" Abh. Math. Semin. Hamburg (1927)
-/

module

public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

namespace Gromov.Schreier

@[expose] public section

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] {H : Subgroup G}

/-- A set of coset representatives for H in G is a right transversal. This definition
wraps Mathlib's `IsComplement` to provide a more intuitive interface for our purposes.

For a subgroup H of G, a set R is a set of coset representatives if every element g
of G can be uniquely written as h * r for some h in H and r in R. -/
def IsCosetRepSet (H : Subgroup G) (R : Set G) : Prop :=
  Subgroup.IsComplement (H : Set G) R

/-- The Schreier generators of H with respect to generators S and coset representatives R.

Given a subgroup H, a generating set S of G, and a right transversal R of H with 1 in R,
the Schreier generators are elements of the form r * s * (bar(rs))^{-1} where:
- r ranges over R
- s ranges over S
- bar(g) denotes the unique representative in R of the coset Hg

These are guaranteed to lie in H and to generate H (Schreier's lemma). -/
noncomputable def schreierGenerators (H : Subgroup G) (S : Set G) (R : Set G)
    (hR : IsCosetRepSet H R) : Set H :=
  (R * S).image fun g => ⟨g * (hR.toRightFun g : G)⁻¹, hR.mul_inv_toRightFun_mem g⟩

end

end Gromov.Schreier
