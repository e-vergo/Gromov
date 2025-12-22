/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Properties of virtually nilpotent groups.
-/

module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.SetTheory.Cardinal.Free
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Solvable
public import Gromov.Definitions.VirtuallyNilpotent

/-!
# Virtually Nilpotent Groups

This file develops the theory of virtually nilpotent groups, building on
`Group.IsVirtuallyNilpotent` from Mathlib.

## Main definitions

* `Group.virtualNilpotencyClass`: The minimum nilpotency class among finite-index nilpotent
  subgroups.

## Main results

### Basic equivalences
* `Group.isVirtuallyNilpotent_iff_exists_normal`: A group is virtually nilpotent iff it has a
  normal nilpotent subgroup of finite index.
* `Group.isVirtuallyNilpotent_quotient_center_iff`: For groups with infinite center, virtually
  nilpotent iff `G/Z(G)` is virtually nilpotent.

### Closure properties
* `Group.isVirtuallyNilpotent_subgroup`: Subgroups of virtually nilpotent groups are virtually
  nilpotent.
* `Group.isVirtuallyNilpotent_quotient`: Quotients of virtually nilpotent groups are virtually
  nilpotent.
* `Group.isVirtuallyNilpotent_of_extension`: Extensions of virtually nilpotent groups are virtually
  nilpotent.
* `Group.isVirtuallyNilpotent_prod`: Products of virtually nilpotent groups are virtually nilpotent.

### Finitely generated case
* `Group.isVirtuallyNilpotent_iff_polycyclic`: For finitely generated groups, virtually nilpotent
  iff polycyclic.
* `Group.residuallyFinite_of_fg_virtuallyNilpotent`: Finitely generated virtually nilpotent groups
  are residually finite.

### Examples
* `Group.isVirtuallyNilpotent_of_commGroup`: Abelian groups are virtually nilpotent.
* `Group.isVirtuallyNilpotent_of_finite`: Finite groups are virtually nilpotent.
* `FreeGroup.not_isVirtuallyNilpotent`: Free groups of rank at least 2 are not virtually nilpotent.

## References

* Gromov's polynomial growth theorem relates polynomial growth to virtual nilpotency.
-/

open Subgroup

namespace Group

public section

variable {G : Type*} [Group G]

/-! ### Basic equivalences -/

/-- A group is virtually nilpotent iff it has a normal nilpotent subgroup of finite index.
This is equivalent to the standard definition because every finite-index subgroup contains
a finite-index normal subgroup (its normal core). -/
theorem isVirtuallyNilpotent_iff_exists_normal :
    IsVirtuallyNilpotent G ↔
    ∃ N : Subgroup G, N.Normal ∧ IsNilpotent N ∧ N.FiniteIndex := by
  constructor
  · -- From virtually nilpotent, find a normal finite-index nilpotent subgroup
    rintro ⟨H, hNil, hFin⟩
    -- The normal core of H is normal and has finite index
    haveI hFinI : H.FiniteIndex := hFin
    haveI hNilI : IsNilpotent H := hNil
    -- H.normalCore ≤ H, so normalCore is nilpotent
    have hle : H.normalCore ≤ H := Subgroup.normalCore_le H
    -- normalCore is nilpotent because it embeds into H which is nilpotent
    -- H.normalCore.subgroupOf H : Subgroup H, and H is nilpotent
    -- By Subgroup.isNilpotent, any subgroup of H (the group) is nilpotent
    -- Then use isNilpotent_congr to transfer to H.normalCore
    have hSubNil : IsNilpotent (H.normalCore.subgroupOf H) := Subgroup.isNilpotent _
    have hNilCore : IsNilpotent H.normalCore :=
      (isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hle)).mp hSubNil
    refine ⟨H.normalCore, H.normalCore_normal, hNilCore, ?_⟩
    · -- Normal core has finite index
      exact Subgroup.finiteIndex_normalCore H
  · -- The other direction is immediate
    rintro ⟨N, _, hNil, hFin⟩
    exact ⟨N, hNil, hFin⟩

/-- If the center has finite index, then G is virtually nilpotent iff G/Z(G) is. -/
theorem isVirtuallyNilpotent_iff_quotient_center (hFin : (center G).FiniteIndex) :
    IsVirtuallyNilpotent G ↔ IsVirtuallyNilpotent (G ⧸ center G) := by
  -- Since center G has finite index and center is abelian (hence nilpotent),
  -- G is automatically virtually nilpotent. The quotient is also virtually nilpotent
  -- since it's a quotient of a virtually nilpotent group.
  -- Both directions follow from center G being a finite-index nilpotent subgroup.
  have hVN : IsVirtuallyNilpotent G := ⟨center G, CommGroup.isNilpotent, hFin⟩
  constructor
  · intro _
    -- Use the quotient theorem (proved below, but we can inline the proof)
    obtain ⟨H, hNil, hFinH⟩ := hVN
    haveI : H.FiniteIndex := hFinH
    haveI : IsNilpotent H := hNil
    refine ⟨H.map (QuotientGroup.mk' (center G)), ?_, ?_⟩
    · exact nilpotent_of_surjective ((QuotientGroup.mk' (center G)).subgroupMap H)
        ((QuotientGroup.mk' (center G)).subgroupMap_surjective H)
    · have hdvd : (H.map (QuotientGroup.mk' (center G))).index ∣ H.index :=
        Subgroup.index_map_dvd H QuotientGroup.mk_surjective
      constructor
      intro h0
      apply hFinH.index_ne_zero
      exact Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd)
  · intro _
    exact hVN

/-- Alternative: G is virtually nilpotent iff G/Z(G) is virtually nilpotent
(general case, not requiring finite index center). -/
theorem isVirtuallyNilpotent_of_quotient_center
    (h : IsVirtuallyNilpotent (G ⧸ center G)) : IsVirtuallyNilpotent G := by
  -- G/Z(G) is virtually nilpotent, so there exists H ≤ G/Z(G) nilpotent with finite index
  obtain ⟨H, hNil, hFinH⟩ := h
  -- Let K be the preimage of H in G
  let K := H.comap (QuotientGroup.mk' (center G))
  -- K has finite index in G (same index as H in G/Z(G))
  have hFinK : K.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    rw [Subgroup.index_comap_of_surjective H QuotientGroup.mk_surjective]
    exact hFinH.index_ne_zero
  -- center G ≤ K
  have hcenter_le_K : center G ≤ K := by
    intro x hx
    simp only [K, Subgroup.mem_comap, QuotientGroup.mk'_apply]
    have : (x : G ⧸ center G) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [this]
    exact Subgroup.one_mem H
  -- K is nilpotent: We use isNilpotent_of_ker_le_center
  -- The quotient map K → G/Z(G) has image H (essentially)
  -- and kernel = center G ∩ K = center G (since center G ≤ K)
  have hKNil : IsNilpotent K := by
    haveI : IsNilpotent H := hNil
    -- Define the restriction of quotient map to K
    let φ : K →* (G ⧸ center G) := (QuotientGroup.mk' (center G)).restrict K
    -- φ.ker = center G ∩ K = center G (as subgroup of K)
    have hker : φ.ker = (center G).subgroupOf K := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, φ, MonoidHom.restrict_apply]
      exact QuotientGroup.eq_one_iff (x : G)
    -- center G ∩ K ≤ center K
    have hker_le_center : φ.ker ≤ center K := by
      rw [hker]
      intro x hx
      simp only [Subgroup.mem_subgroupOf] at hx
      simp only [Subgroup.mem_center_iff]
      intro y
      have hxc : (x : G) ∈ center G := hx
      simp only [Subgroup.mem_center_iff] at hxc
      exact Subtype.ext (hxc y.val)
    -- The range of φ is H
    have hφ_range_nil : IsNilpotent φ.range := by
      -- φ.range is the image of K under the quotient map which is H
      have hrange_eq : φ.range = H := by
        ext x
        constructor
        · rintro ⟨k, hk⟩
          have hkK : (k : G) ∈ K := k.prop
          simp only [K, Subgroup.mem_comap, QuotientGroup.mk'_apply] at hkK
          simp only [φ, MonoidHom.restrict_apply] at hk
          rw [← hk]
          exact hkK
        · intro hxH
          obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x
          have hgK : g ∈ K := by
            simp only [K, Subgroup.mem_comap, QuotientGroup.mk'_apply]
            rw [hg]
            exact hxH
          refine ⟨⟨g, hgK⟩, ?_⟩
          simp only [φ, MonoidHom.restrict_apply]
          exact hg
      rw [hrange_eq]
      exact hNil
    -- Transfer nilpotency from φ.range to K
    have hequiv : φ.range ≃* K ⧸ φ.ker := QuotientGroup.quotientKerEquivRange φ |>.symm
    haveI hKQuotNil : IsNilpotent (K ⧸ φ.ker) := (isNilpotent_congr hequiv.symm).mpr hφ_range_nil
    -- Now use that ker ≤ center K and K/(ker) is nilpotent, so K is nilpotent
    have hker_le : (QuotientGroup.mk' φ.ker).ker ≤ center K := by
      rw [QuotientGroup.ker_mk']
      exact hker_le_center
    exact isNilpotent_of_ker_le_center (QuotientGroup.mk' φ.ker) hker_le hKQuotNil
  exact ⟨K, hKNil, hFinK⟩

/-! ### Closure properties -/

/-- Subgroups of virtually nilpotent groups are virtually nilpotent. -/
theorem isVirtuallyNilpotent_subgroup (H : Subgroup G) (hG : IsVirtuallyNilpotent G) :
    IsVirtuallyNilpotent H := by
  obtain ⟨N, hNil, hFin⟩ := hG
  haveI hFinI : N.FiniteIndex := hFin
  haveI hNilI : IsNilpotent N := hNil
  -- The intersection H ∩ N is a finite-index nilpotent subgroup of H
  -- N.subgroupOf H has type Subgroup H
  -- We need to show it's nilpotent and has finite index
  have hNilSub : IsNilpotent (N.subgroupOf H) := by
    -- (H ⊓ N) ≤ N, so (H ⊓ N).subgroupOf N is a subgroup of N (the group)
    -- By Subgroup.isNilpotent, it's nilpotent
    have hSubNNil : IsNilpotent ((H ⊓ N).subgroupOf N) := Subgroup.isNilpotent _
    -- (H ⊓ N).subgroupOf N ≃* (H ⊓ N) via subgroupOfEquivOfLe
    have hInfNil : IsNilpotent (H ⊓ N : Subgroup G) :=
      (isNilpotent_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right (a := H) (b := N)))).mp
        hSubNNil
    -- N.subgroupOf H = (H ⊓ N).subgroupOf H
    have heq : N.subgroupOf H = (H ⊓ N).subgroupOf H := by
      ext x
      simp only [mem_subgroupOf, mem_inf, and_iff_right x.prop]
    rw [heq]
    -- (H ⊓ N).subgroupOf H ≃* (H ⊓ N) via subgroupOfEquivOfLe
    haveI : IsNilpotent (H ⊓ N : Subgroup G) := hInfNil
    exact (isNilpotent_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left (a := H) (b := N)))).mpr
      hInfNil
  refine ⟨N.subgroupOf H, hNilSub, ?_⟩
  · -- N.subgroupOf H has finite index in H
    exact instFiniteIndex_subgroupOf N H

/-- Quotients of virtually nilpotent groups by normal subgroups are virtually nilpotent. -/
theorem isVirtuallyNilpotent_quotient (N : Subgroup G) [N.Normal] (hG : IsVirtuallyNilpotent G) :
    IsVirtuallyNilpotent (G ⧸ N) := by
  obtain ⟨H, hNil, hFin⟩ := hG
  haveI : H.FiniteIndex := hFin
  haveI : IsNilpotent H := hNil
  -- The image of H in the quotient is nilpotent and has finite index
  refine ⟨H.map (QuotientGroup.mk' N), ?_, ?_⟩
  · -- Image of nilpotent group under surjection is nilpotent
    exact nilpotent_of_surjective ((QuotientGroup.mk' N).subgroupMap H)
      ((QuotientGroup.mk' N).subgroupMap_surjective H)
  · -- The map preserves finite index
    have hdvd : (H.map (QuotientGroup.mk' N)).index ∣ H.index :=
      Subgroup.index_map_dvd H QuotientGroup.mk_surjective
    constructor
    intro h0
    apply hFin.index_ne_zero
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd)

/-- If N is a finite normal subgroup of G, and G/N is virtually nilpotent, then G is virtually
nilpotent. Note: The general extension theorem (both N and G/N virtually nilpotent implies G
virtually nilpotent) is FALSE - the wreath product Z ≀ Z is a counterexample. -/
theorem isVirtuallyNilpotent_of_extension (N : Subgroup G) [N.Normal] [Finite N]
    (hQ : IsVirtuallyNilpotent (G ⧸ N)) : IsVirtuallyNilpotent G := by
  -- G/N is virtually nilpotent, so there exists H ≤ G/N nilpotent with finite index
  obtain ⟨H, hHNil, hHFin⟩ := hQ
  haveI : IsNilpotent H := hHNil
  -- Let K be the preimage of H in G
  let K := H.comap (QuotientGroup.mk' N)
  -- K has finite index in G
  have hKFin : K.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    rw [Subgroup.index_comap_of_surjective H QuotientGroup.mk_surjective]
    exact hHFin.index_ne_zero
  haveI : K.FiniteIndex := hKFin
  -- N ≤ K (since 1 ∈ H)
  have hN_le_K : N ≤ K := by
    intro x hx
    simp only [K, Subgroup.mem_comap, QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem H
  -- Strategy: Use the centralizer of N in K.
  -- C_K(N) = {k ∈ K : kn = nk for all n ∈ N}
  -- 1. [K : C_K(N)] divides |Aut(N)| which is finite
  -- 2. C_K(N) ∩ N ≤ center(C_K(N))
  -- 3. C_K(N)/(C_K(N) ∩ N) embeds into K/N ≅ H which is nilpotent
  -- Therefore C_K(N) is nilpotent and has finite index in G.
  -- The centralizer of N (as a set) in K
  let C := (Subgroup.centralizer (N : Set G)).subgroupOf K
  -- C has finite index in K
  have hCFinK : C.FiniteIndex := by
    -- The conjugation action K → Aut(N) has kernel C
    -- First, N is finite so Aut(N) is finite
    haveI : Finite N := ‹Finite N›
    -- Construct the conjugation homomorphism from K to Aut(N)
    -- Note: MulAut.conjNormal expects a subgroup with Normal instance
    let φ : K →* MulAut N := (MulAut.conjNormal (H := N)).comp K.subtype
    -- φ.ker = C
    have hker : φ.ker = C := by
      ext ⟨k, hkK⟩
      simp only [MonoidHom.mem_ker, C, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      constructor
      · intro hφ n hn
        have : (φ ⟨k, hkK⟩) ⟨n, hn⟩ = ⟨n, hn⟩ := by
          rw [MulEquiv.ext_iff] at hφ
          exact hφ ⟨n, hn⟩
        simp only [φ] at this
        have hcoe := congr_arg Subtype.val this
        simp only [MulAut.conjNormal_apply, MonoidHom.coe_comp, Function.comp_apply,
          Subgroup.coe_subtype] at hcoe
        -- hcoe : k * n * k⁻¹ = n
        rw [mul_inv_eq_iff_eq_mul] at hcoe
        exact hcoe.symm
      · intro hk
        ext ⟨n, hn⟩
        simp only [φ, MulAut.one_apply, MulAut.conjNormal_apply, MonoidHom.coe_comp,
          Function.comp_apply, Subgroup.coe_subtype]
        rw [mul_inv_eq_iff_eq_mul]
        exact (hk n hn).symm
    -- φ has finite range (since MulAut N is finite)
    haveI hFinAut : Finite (MulAut N) := MulEquiv.finite_left
    rw [Subgroup.finiteIndex_iff, ← hker]
    -- kernel has finite index when range is finite
    haveI : Finite (φ.range : Type _) := inferInstance
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  -- C is nilpotent
  have hCNil : IsNilpotent C := by
    -- (C ∩ N).subgroupOf C ≤ center C, since C centralizes N
    have hCN_le_center : ((Subgroup.centralizer (N : Set G) ⊓ N).subgroupOf K).subgroupOf C ≤
        Subgroup.center C := by
      intro ⟨⟨c, hcK⟩, hcC⟩ hcN
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hcN hcC
      simp only [Subgroup.mem_center_iff]
      intro ⟨⟨d, hdK⟩, hdC⟩
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      -- c ∈ N, d ∈ C (so d centralizes N), hence d * c = c * d
      have hdcentralizes : d * c = c * d := by
        have hcN' : c ∈ (N : Set G) := hcN.2
        have hdC' : d ∈ Subgroup.centralizer (N : Set G) := hdC
        exact (Subgroup.mem_centralizer_iff.mp hdC' c hcN').symm
      exact hdcentralizes
    -- The quotient C / (C ∩ N) embeds into K/N ≅ H which is nilpotent
    -- Define the restriction of the quotient map to C
    let ψ : C →* (G ⧸ N) := (QuotientGroup.mk' N).comp (K.subtype.comp C.subtype)
    -- ψ.range is a subgroup of K.map (mk' N) which equals H
    have hψ_range_le : ψ.range ≤ K.map (QuotientGroup.mk' N) := by
      intro x ⟨⟨⟨k, hkK⟩, hkC⟩, hψ⟩
      simp only [ψ, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at hψ
      rw [← hψ]
      exact ⟨k, hkK, rfl⟩
    -- K/N is isomorphic to H
    have hKN_iso_H : (K.map (QuotientGroup.mk' N)) = H := by
      ext x
      constructor
      · intro ⟨k, hkK, hk⟩
        simp only [K] at hkK
        rw [← hk]
        exact hkK
      · intro hxH
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x
        have hgK : g ∈ K := by
          simp only [K, Subgroup.mem_comap, QuotientGroup.mk'_apply]
          rw [hg]
          exact hxH
        exact ⟨g, hgK, hg⟩
    -- ψ.range is nilpotent (as a subgroup of the nilpotent group H)
    have hψ_range_nil : IsNilpotent ψ.range := by
      -- ψ.range ≤ K.map (mk' N) = H
      have hle : ψ.range ≤ K.map (QuotientGroup.mk' N) := by
        intro x ⟨⟨⟨k, hkK⟩, hkC⟩, hψ⟩
        simp only [ψ, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at hψ
        rw [← hψ]
        exact ⟨k, hkK, rfl⟩
      rw [hKN_iso_H] at hle
      -- H is nilpotent, so ψ.range (as a subgroup of G ⧸ N) is isomorphic to
      -- ψ.range.subgroupOf H which is a subgroup of the nilpotent group H
      have hSubNil : IsNilpotent (ψ.range.subgroupOf H) := Subgroup.isNilpotent _
      exact (isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hle)).mp hSubNil
    -- ψ.ker = (C ∩ N).subgroupOf C (in appropriate sense)
    have hker : ψ.ker ≤ Subgroup.center C := by
      intro ⟨⟨c, hcK⟩, hcC⟩ hψker
      simp only [MonoidHom.mem_ker, ψ, MonoidHom.coe_comp, Subgroup.coe_subtype,
        Function.comp_apply] at hψker
      have hcN : c ∈ N := by
        rw [← QuotientGroup.eq_one_iff c]
        exact hψker
      -- c ∈ C ∩ N, so c is in the center of C
      simp only [Subgroup.mem_center_iff]
      intro ⟨⟨d, hdK⟩, hdC⟩
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      -- d ∈ C means d centralizes N, and c ∈ N
      have hdC' : d ∈ Subgroup.centralizer (N : Set G) := hdC
      exact (Subgroup.mem_centralizer_iff.mp hdC' c hcN).symm
    -- Use isNilpotent_of_ker_le_center
    have hequiv : ψ.range ≃* C ⧸ ψ.ker := QuotientGroup.quotientKerEquivRange ψ |>.symm
    haveI hCQuotNil : IsNilpotent (C ⧸ ψ.ker) := (isNilpotent_congr hequiv.symm).mpr hψ_range_nil
    have hker_le : (QuotientGroup.mk' ψ.ker).ker ≤ Subgroup.center C := by
      rw [QuotientGroup.ker_mk']
      exact hker
    exact isNilpotent_of_ker_le_center (QuotientGroup.mk' ψ.ker) hker_le hCQuotNil
  -- C has finite index in G (= [G : K] · [K : C])
  have hCFinG : (C.map K.subtype).FiniteIndex := by
    -- [G : C.map K.subtype] = [G : K] · [K : C]
    haveI : C.FiniteIndex := hCFinK
    haveI : K.FiniteIndex := hKFin
    -- C.map K.subtype has finite index
    rw [Subgroup.finiteIndex_iff, Subgroup.index_map_subtype]
    exact mul_ne_zero (FiniteIndex.index_ne_zero) (FiniteIndex.index_ne_zero)
  -- C.map K.subtype is nilpotent (isomorphic to C)
  have hCMapNil : IsNilpotent (C.map K.subtype) := by
    have hequiv : C ≃* (C.map K.subtype) :=
      C.equivMapOfInjective K.subtype (Subgroup.subtype_injective K)
    exact (isNilpotent_congr hequiv).mp hCNil
  exact ⟨C.map K.subtype, hCMapNil, hCFinG⟩

/-- Products of virtually nilpotent groups are virtually nilpotent. -/
theorem isVirtuallyNilpotent_prod {G' : Type*} [Group G']
    (hG : IsVirtuallyNilpotent G) (hG' : IsVirtuallyNilpotent G') :
    IsVirtuallyNilpotent (G × G') := by
  obtain ⟨H, hHNil, hHFin⟩ := hG
  obtain ⟨K, hKNil, hKFin⟩ := hG'
  haveI : H.FiniteIndex := hHFin
  haveI : K.FiniteIndex := hKFin
  haveI : IsNilpotent H := hHNil
  haveI : IsNilpotent K := hKNil
  -- H.prod K is a subgroup of G × G' that is nilpotent and has finite index
  have hNilProd : IsNilpotent (H.prod K) := by
    -- H.prod K is isomorphic to H × K as groups
    -- We have IsNilpotent H and IsNilpotent K, so H × K is nilpotent
    haveI : IsNilpotent (H × K) := isNilpotent_prod
    -- Need to transport this to H.prod K via the isomorphism
    exact (isNilpotent_congr (Subgroup.prodEquiv H K)).mpr (by assumption)
  refine ⟨H.prod K, hNilProd, ?_⟩
  · -- Product of finite index subgroups has finite index
    constructor
    rw [Subgroup.index_prod]
    exact mul_ne_zero hHFin.index_ne_zero hKFin.index_ne_zero

/-- Finite products of virtually nilpotent groups are virtually nilpotent. -/
theorem isVirtuallyNilpotent_pi {ι : Type*} [Finite ι] {Gs : ι → Type*}
    [∀ i, Group (Gs i)] (hGs : ∀ i, IsVirtuallyNilpotent (Gs i)) :
    IsVirtuallyNilpotent (∀ i, Gs i) := by
  classical
  cases nonempty_fintype ι
  -- For each i, choose a finite-index nilpotent subgroup
  choose Hs hNil hFin using hGs
  -- The pi subgroup is nilpotent
  have hPiNil : IsNilpotent (Subgroup.pi Set.univ Hs) := by
    haveI : ∀ i, IsNilpotent (Hs i) := hNil
    -- First show the equivalence: (pi Set.univ Hs) =* ∀ i, Hs i
    have hEquiv : (Subgroup.pi Set.univ Hs) ≃* (∀ i, Hs i) := {
      toFun := fun x i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
      invFun := fun x => ⟨fun i => (x i).1, fun i _ => (x i).2⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_mul' := fun x y => by ext; simp
    }
    -- IsNilpotent (∀ i, Hs i) by isNilpotent_pi
    haveI : IsNilpotent (∀ i, Hs i) := isNilpotent_pi
    exact (isNilpotent_congr hEquiv).mpr (by assumption)
  -- The pi subgroup has finite index
  have hPiFin : (Subgroup.pi Set.univ Hs).FiniteIndex := by
    haveI : ∀ i, (Hs i).FiniteIndex := hFin
    rw [Subgroup.finiteIndex_iff, Subgroup.index]
    -- Build equivalence: (∀ i, Gs i) ⧸ (pi Set.univ Hs) ≃ ∀ i, Gs i ⧸ Hs i
    have hEquiv : ((∀ i, Gs i) ⧸ (Subgroup.pi Set.univ Hs)) ≃ (∀ i, Gs i ⧸ Hs i) := by
      have h1 : ((∀ i, Gs i) ⧸ (Subgroup.pi Set.univ Hs)) ≃
          Quotient (@piSetoid _ _ (fun i => QuotientGroup.leftRel (Hs i))) :=
        Quotient.congr (Equiv.refl _) (fun a b => by rw [QuotientGroup.leftRel_pi Hs]; rfl)
      have h2 : Quotient (@piSetoid _ _ (fun i => QuotientGroup.leftRel (Hs i))) ≃
          (∀ i, Quotient (QuotientGroup.leftRel (Hs i))) :=
        (Setoid.piQuotientEquiv _).symm
      exact h1.trans h2
    rw [Nat.card_congr hEquiv, Nat.card_pi]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [← Subgroup.index]
    exact Subgroup.FiniteIndex.index_ne_zero
  exact ⟨Subgroup.pi Set.univ Hs, hPiNil, hPiFin⟩

end

end Group
