/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Core module for virtually nilpotent groups.
Re-exports definitions and provides foundational lemmas.
-/

module

public import Gromov.Definitions.VirtuallyNilpotent

/-!
# Virtually Nilpotent Groups - Core

This module re-exports the core definitions for virtually nilpotent groups
and provides foundational lemmas used throughout the proof of Gromov's theorem.

## Main definitions (from Gromov.Definitions.VirtuallyNilpotent)

* `Group.IsPolycyclic` - Group has subnormal series with cyclic factors
* `Group.IsResiduallyFinite` - Intersection of finite-index normal subgroups is trivial
* `Group.virtualNilpotencyClass` - Minimum nilpotency class among finite-index nilpotent subgroups

## Re-exports

This module re-exports `Mathlib.GroupTheory.Nilpotent` which provides:
* `IsVirtuallyNilpotent` - Group has finite-index nilpotent subgroup
* `IsNilpotent` - Group is nilpotent
* `Group.nilpotencyClass` - Nilpotency class of a nilpotent group
-/
