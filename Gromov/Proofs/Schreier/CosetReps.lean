/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Coset representatives and Schreier generators for finite-index subgroups.

This file develops the theory of coset representatives and Schreier generators,
building on Mathlib's `GroupTheory.Schreier`. The main results establish that:

1. Finite-index subgroups have finite sets of coset representatives
2. Schreier generators (of the form r * s * (rs)^{-1}) generate the subgroup
3. When the ambient group is finitely generated, Schreier generators are finite

## References

* Schreier, O. "Die Untergruppen der freien Gruppen" Abh. Math. Semin. Hamburg (1927)
* Lyndon & Schupp, "Combinatorial Group Theory" Springer (1977), Theorem 2.7
* Hall, M. "The Theory of Groups" Macmillan (1959), Chapter 7
* Mathlib.GroupTheory.Schreier
-/

module

public import Gromov.Definitions.Schreier
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Card

namespace Gromov.Schreier.CosetReps

@[expose] public section

open Subgroup Gromov.Schreier
open scoped Pointwise

variable {G : Type*} [Group G] {H : Subgroup G}

/-! ### Coset Representatives -/

/-- For a finite-index subgroup, we can always find a finite set of coset representatives.
This is the key finiteness result that allows Schreier's construction to produce
finitely many generators. -/
-- Proof: By definition of finite index, there are finitely many cosets H\G.
-- Pick one representative from each coset to form the transversal.
-- The set of quotient.out representatives works.
theorem cosetReps_exist [H.FiniteIndex] :
    ∃ (R : Finset G), (1 : G) ∈ R ∧ IsCosetRepSet H (R : Set G) := by
  obtain ⟨R₀, hR, hR1⟩ := H.exists_isComplement_right 1
  have hR_finite : R₀.Finite := hR.finite_right_iff.mpr inferInstance
  refine ⟨hR_finite.toFinset, hR_finite.mem_toFinset.mpr hR1, ?_⟩
  rw [hR_finite.coe_toFinset]
  exact hR

/-- Coset representatives cover G: every element can be factored as (coset rep) * (element in H).
More precisely, for any g in G, there exists r in R and h in H such that g = h * r. -/
-- Proof: This is the defining property of a right transversal.
-- The complement condition ensures G = H * R as a set.
theorem cosetReps_cover {R : Set G} (hR : IsCosetRepSet H R) (_hR1 : (1 : G) ∈ R) (g : G) :
    ∃ r ∈ R, ∃ h ∈ H, g = h * r := by
  have : g ∈ (H : Set G) * R := by
    rw [hR.mul_eq]
    trivial
  obtain ⟨h, hh, r, hr, heq⟩ := Set.mem_mul.mp this
  exact ⟨r, hr, h, hh, heq.symm⟩

/-- The coset representative of an element is unique modulo H.
If g = h_1 * r_1 = h_2 * r_2 with r_1, r_2 in R and h_1, h_2 in H, then r_1 = r_2. -/
-- Proof: From g = h_1 * r_1 = h_2 * r_2, we get r_2 * r_1^{-1} = h_2^{-1} * h_1 in H.
-- Since R is a transversal, distinct representatives lie in distinct cosets.
-- Thus r_1 and r_2 must be equal.
theorem cosetReps_unique {R : Set G} (hR : IsCosetRepSet H R) {_g : G}
    {r₁ r₂ : G} (_hr₁ : r₁ ∈ R) (_hr₂ : r₂ ∈ R)
    {h₁ h₂ : G} (_hh₁ : h₁ ∈ H) (_hh₂ : h₂ ∈ H)
    (_heq : h₁ * r₁ = h₂ * r₂) : r₁ = r₂ := by
  have h_prod : h₂⁻¹ * h₁ * r₁ = r₂ := by
    calc h₂⁻¹ * h₁ * r₁ = h₂⁻¹ * (h₁ * r₁) := by group
      _ = h₂⁻¹ * (h₂ * r₂) := by rw [_heq]
      _ = r₂ := by group
  have h_mem : h₂⁻¹ * h₁ ∈ H := Subgroup.mul_mem H (Subgroup.inv_mem H _hh₂) _hh₁
  have h_inj := hR.1
  have : ((⟨h₂⁻¹ * h₁, h_mem⟩ : ↑H), (⟨r₁, _hr₁⟩ : R)) =
         ((⟨1, Subgroup.one_mem H⟩ : ↑H), (⟨r₂, _hr₂⟩ : R)) := by
    apply h_inj
    simp [h_prod]
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
  exact this.2

/-! ### Schreier Generators -/

/-- Each Schreier generator lies in H.
This is immediate from the construction: r * s * (bar(rs))^{-1} in H because
rs and bar(rs) lie in the same H-coset. -/
-- Proof: By construction, schreierGenerators is a subset of H.
-- Specifically, g * (toRightFun g)^{-1} in H by the property of right transversals.
theorem schreierGenerators_mem (S : Set G) (R : Set G) (hR : IsCosetRepSet H R)
    (x : H) (_hx : x ∈ schreierGenerators H S R hR) : (x : G) ∈ H :=
  x.2

/-- Schreier generators generate H (Schreier's lemma).

This is the core of Schreier's lemma: the elements r * s * (bar(rs))^{-1} generate
the subgroup H. This allows us to construct explicit generators for any finite-index
subgroup from generators of the ambient group. -/
-- Proof: This is exactly Mathlib's `Subgroup.closure_mul_image_eq_top`.
-- The key insight is that any h in H can be written as a word in S,
-- and the Schreier rewriting process converts this to a word in Schreier generators.
theorem schreierGenerators_generate (S : Set G) (hS : closure S = ⊤)
    (R : Set G) (hR : IsCosetRepSet H R) (_hR1 : (1 : G) ∈ R) :
    closure (schreierGenerators H S R hR) = ⊤ := by
  unfold schreierGenerators
  exact Subgroup.closure_mul_image_eq_top hR _hR1 hS

/-- If S is finite and H has finite index, then the Schreier generators form a finite set.

The cardinality bound is |R| * |S| = [G:H] * |S|, though we don't prove the exact
bound here, only finiteness. -/
-- Proof: Schreier generators are indexed by R x S.
-- If R is finite (from finite index) and S is finite, then R x S is finite,
-- so the image under the Schreier map is finite.
theorem schreierGenerators_finite [H.FiniteIndex] {S : Finset G}
    {R : Finset G} (hR : IsCosetRepSet H (R : Set G)) :
    (schreierGenerators H (S : Set G) (R : Set G) hR).Finite := by
  unfold schreierGenerators
  refine Set.Finite.image _ ?_
  have hR_fin : (R : Set G).Finite := hR.finite_right_iff.mpr inferInstance
  exact hR_fin.mul S.finite_toSet

/-- The cardinality of Schreier generators is at most [G:H] * |S|.

This is the explicit bound from Schreier's lemma. Combined with finite generation,
it shows that finite-index subgroups of finitely generated groups are finitely generated. -/
-- Proof: Each Schreier generator corresponds to a pair (r, s) in R x S.
-- The map (r, s) -> r * s * (bar(rs))^{-1} may not be injective,
-- but the image size is at most |R| * |S|.
theorem schreierGenerators_card_le [H.FiniteIndex] {S : Finset G}
    {R : Finset G} (hR : IsCosetRepSet H (R : Set G)) (_hR1 : (1 : G) ∈ R) :
    (schreierGenerators H (S : Set G) (R : Set G) hR).ncard ≤ R.card * S.card := by
  classical
  unfold schreierGenerators
  have hR_fin : (R : Set G).Finite := hR.finite_right_iff.mpr inferInstance
  have hRS : ((R : Set G) * (S : Set G)).Finite := hR_fin.mul S.finite_toSet
  trans ((R : Set G) * (S : Set G)).ncard
  · exact Set.ncard_image_le
  · have : ((R : Set G) * (S : Set G)) ⊆ (R.product S).image (fun p => p.1 * p.2) := by
      intro x hx
      obtain ⟨r, hr, s, hs, rfl⟩ := Set.mem_mul.mp hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨(r, s), Finset.mem_product.mpr ⟨hr, hs⟩, rfl⟩
    calc ((R : Set G) * (S : Set G)).ncard
        ≤ ((R.product S).image (fun p => p.1 * p.2) : Set G).ncard := by
          refine Set.ncard_le_ncard this ?_
          simp only [Finset.coe_image]
          exact (R.product S).finite_toSet.image _
        _ = ((R.product S).image (fun p => p.1 * p.2)).card := by
          simp only [Set.ncard_coe_finset]
        _ ≤ (R.product S).card := Finset.card_image_le
        _ = R.card * S.card := Finset.card_product _ _

/-! ### Connection to Mathlib's Schreier Infrastructure -/

/-- When H has finite index, there exists a finite generating set for H derived from
any finite generating set for G via Schreier's construction.

This is a packaging of the above results into a single existence statement. -/
-- Proof: Take R to be the Quotient.out representatives, S any finite generating set of G.
-- Apply schreierGenerators_generate and schreierGenerators_finite.
theorem exists_finite_schreier_generators [H.FiniteIndex] [Group.FG G] :
    ∃ (T : Finset H), closure (T : Set H) = ⊤ := by
  obtain ⟨S, hS⟩ := Group.FG.out (G := G)
  obtain ⟨R, hR1, hR⟩ := cosetReps_exist (H := H)
  have hS_gen : closure (S : Set G) = ⊤ := hS
  have hfin := schreierGenerators_finite (S := S) (R := R) hR
  use hfin.toFinset
  have : schreierGenerators H (S : Set G) (R : Set G) hR = ↑hfin.toFinset := by
    exact hfin.coe_toFinset.symm
  rw [←this]
  exact schreierGenerators_generate (S : Set G) hS_gen (R : Set G) hR hR1

end

end Gromov.Schreier.CosetReps
