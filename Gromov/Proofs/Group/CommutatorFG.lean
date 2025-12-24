/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Hall-Witt identities and commutator finite generation.

This file develops the theory of commutator subgroups and their relationship to
finite generation. The main result is that the commutator subgroup of a finitely
generated group is finitely normally generated.

## Main results

* `commutator_finitelyNormallyGenerated` - [G,G] is finitely normally generated when G is FG
* `lowerCentralSeries_fg` - Lower central series terms are FG
* `abelianization_fg` - G/[G,G] is FG when G is FG

## References

* Hall, P. "The Theory of Groups" Macmillan (1959)
* Robinson, D.J.S. "A Course in the Theory of Groups" Springer (1996)
-/

module

public import Gromov.Proofs.VirtuallyNilpotent.Core
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Nilpotent

namespace Gromov.Group.CommutatorFG

public section

open Subgroup

variable {G : Type*} [Group G]

/-! ## Finite Generation of Commutator Subgroup -/

section CommutatorFG

variable [Group.FG G]

/-- Commutators of generators generate the commutator subgroup (normally).
    More precisely, [G,G] is the normal closure of {[s,t] : s,t ∈ S}
    where S is any generating set. -/
theorem commutator_mem_of_generators (S : Set G) (hS : closure S = ⊤) :
    ∀ g ∈ commutator G,
      g ∈ normalClosure { ⁅s, t⁆ | (s : G) (t : G) (_ : s ∈ S ∪ S⁻¹) (_ : t ∈ S ∪ S⁻¹) } := by
  sorry

/-- The commutator subgroup of a finitely generated group is finitely normally generated.
    That is, [G,G] is the normal closure of finitely many elements. -/
theorem commutator_finitelyNormallyGenerated :
    ∃ (T : Finset G), normalClosure (T : Set G) = commutator G := by
  sorry

/-- The commutator of two FG subgroups is FG (when they normalize each other).
    This generalizes to ⁅H, K⁆ being FG when H and K are FG and normal. -/
theorem Subgroup.fg_commutator (H K : Subgroup G) (hH : H.FG) (hK : K.FG)
    (hHN : H.Normal) (hKN : K.Normal) : (⁅H, K⁆).FG := by
  sorry

/-- The abelianization G/[G,G] of a finitely generated group is finitely generated. -/
theorem abelianization_fg : Group.FG (Abelianization G) := by
  sorry

/-- If the abelianization is finite, then [G,G] has finite index. -/
theorem commutator_finiteIndex_of_abelianization_finite
    [Finite (Abelianization G)] : (commutator G).FiniteIndex := by
  sorry

/-- Characterization: [G,G] has finite index iff the abelianization is finite. -/
theorem commutator_finiteIndex_iff_abelianization_finite :
    (commutator G).FiniteIndex ↔ Finite (Abelianization G) := by
  sorry

end CommutatorFG

/-! ## Lower Central Series -/

section LowerCentralSeries

variable [Group.FG G]

/-- Terms of the lower central series are FG for FG groups.
    This follows by induction: γ_{n+1}(G) = [γ_n(G), G] and [FG, FG] is FG. -/
theorem lowerCentralSeries_fg (n : ℕ) : (lowerCentralSeries G n).FG := by
  sorry

/-- The quotient G/γ_n(G) is FG for all n.
    This is immediate from γ_n(G) being FG. -/
theorem lowerCentralSeries_quotient_fg (n : ℕ) :
    Group.FG (G ⧸ lowerCentralSeries G n) := by
  sorry

/-- Bound on lower central series of quotients.
    γ_n(G/N) = γ_n(G)N/N when N is normal. -/
theorem lowerCentralSeries_quotient (N : Subgroup G) [N.Normal] (n : ℕ) :
    lowerCentralSeries (G ⧸ N) n = (lowerCentralSeries G n).map (QuotientGroup.mk' N) := by
  sorry

end LowerCentralSeries

/-! ## Structure of Abelianization -/

section AbelianizationStructure

variable [Group.FG G]

/-- If the abelianization has infinite cyclic part, we can extract a surjection to ℤ.
    This is key for the descent argument in Gromov's theorem. -/
theorem exists_surjection_to_Z_of_abelianization_infinite [Infinite (Abelianization G)] :
    ∃ (φ : G →* ℤ), Function.Surjective φ := by
  sorry

/-- Structure theorem: the abelianization of a FG group is ℤ^r × T
    where T is a finite abelian group. -/
theorem abelianization_structure :
    ∃ (r : ℕ) (T : Type*) (_ : Fintype T) (_ : AddCommGroup T),
      Nonempty (Abelianization G ≃* Multiplicative ((Fin r → ℤ) × T)) := by
  sorry

end AbelianizationStructure

/-! ## Virtual Nilpotency and Commutators -/

section VirtualNilpotency

variable [Group.FG G]

/-- For virtually nilpotent FG groups, some term of the LCS has finite index.
    This is key to the structure theory. -/
theorem virtuallyNilpotent_lowerCentralSeries_finite (hVN : Group.IsVirtuallyNilpotent G) :
    ∃ n : ℕ, (lowerCentralSeries G n).FiniteIndex := by
  sorry

/-- The commutator of a virtually nilpotent FG group is virtually nilpotent. -/
theorem commutator_virtuallyNilpotent (hVN : Group.IsVirtuallyNilpotent G) :
    Group.IsVirtuallyNilpotent (commutator G) := by
  sorry

/-- Virtually nilpotent groups have virtually solvable abelianization.
    More specifically, for VN groups, the torsion part of the abelianization is finite. -/
theorem virtuallyNilpotent_abelianization_torsion_finite (hVN : Group.IsVirtuallyNilpotent G) :
    ∃ (T : Subgroup (Abelianization G)), T.Normal ∧ Finite T ∧
      ∀ (x : Abelianization G), (∃ n : ℕ, n > 0 ∧ x ^ n = 1) → x ∈ T := by
  sorry

end VirtualNilpotency

/-! ## Hall-Witt Identity -/

section HallWitt

/-- The Hall-Witt identity (three-subgroups lemma):
    [[x,y^{-1}],z]^y * [[y,z^{-1}],x]^z * [[z,x^{-1}],y]^x = 1
    This is fundamental for lower central series computations. -/
theorem hall_witt (x y z : G) :
    (y * ⁅⁅x, y⁻¹⁆, z⁆ * y⁻¹) * (z * ⁅⁅y, z⁻¹⁆, x⁆ * z⁻¹) * (x * ⁅⁅z, x⁻¹⁆, y⁆ * x⁻¹) = 1 := by
  sorry

/-- Consequence of Hall-Witt: [γ_m, γ_n] ⊆ γ_{m+n} -/
theorem lowerCentralSeries_commutator_le (m n : ℕ) :
    ⁅lowerCentralSeries G m, lowerCentralSeries G n⁆ ≤
      lowerCentralSeries G (m + n) := by
  sorry

end HallWitt

end

end Gromov.Group.CommutatorFG
