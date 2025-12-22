/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Polycyclic groups and their relationship to virtual nilpotency.
-/

module

public import Gromov.Proofs.VirtuallyNilpotent.Core

set_option linter.style.emptyLine false
set_option linter.style.longLine false

/-!
# Polycyclic Groups

This file develops the theory of polycyclic groups and proves the equivalence
between virtually nilpotent and polycyclic for finitely generated groups.

## Main results

* `Group.isVirtuallyNilpotent_iff_polycyclic`: For finitely generated groups, virtually nilpotent
  iff polycyclic (Mal'cev's theorem).
* `Subgroup.fg_of_polycyclic`: Subgroups of polycyclic groups are finitely generated.

## References

* Mal'cev, A. I. "On certain classes of infinite soluble groups" (1951)
* Segal, D. "Polycyclic Groups" Cambridge University Press (1983)
-/

open Subgroup

namespace Group

public section

variable {G : Type*} [Group G]

/-! ### Polycyclic Group Theorems -/

/-- Finitely generated nilpotent groups are polycyclic.

The proof uses the lower central series G = G_0 > G_1 > ... > G_n = 1 where each
quotient G_i/G_{i+1} is abelian and f.g. (by Mal'cev's theorem on nilpotent groups).
F.g. abelian groups are polycyclic by the structure theorem (Z^r x finite torsion).
Concatenating these polycyclic series gives a polycyclic series for G.

References:
- Segal, D. "Polycyclic Groups" (1983), Theorem 1.5
- Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.4.12
-/
theorem isPolycyclic_of_isNilpotent_fg (H : Type*) [Group H] [FG H] [IsNilpotent H] :
    IsPolycyclic H := by
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp (inferInstance : IsNilpotent H)
  -- We use the lower central series H = L_0 > L_1 > ... > L_n = 1
  -- Each quotient L_i/L_{i+1} is abelian and central in H/L_{i+1}
  -- For f.g. nilpotent groups, these quotients are f.g. abelian, hence polycyclic
  sorry

/-- Every polycyclic group has a finite-index normal nilpotent subgroup (Fitting subgroup).

This is the Fitting subgroup theorem: in polycyclic groups, the Fitting subgroup
(the unique maximal normal nilpotent subgroup) has finite index. The Fitting
subgroup is defined as the product of all normal nilpotent subgroups.

References:
- Segal, D. "Polycyclic Groups" (1983), Theorem 1.3
- Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.2.17
-/
theorem polycyclic_has_finiteIndex_nilpotent_normal_subgroup (H : Type*) [Group H]
    (hP : IsPolycyclic H) :
    ∃ N : Subgroup H, N.Normal ∧ IsNilpotent N ∧ N.FiniteIndex := by
  sorry

-- Polycyclic groups are virtually nilpotent (follows from the axiom above)
theorem isVirtuallyNilpotent_of_isPolycyclic (H : Type*) [Group H] (hP : IsPolycyclic H) :
    IsVirtuallyNilpotent H := by
  obtain ⟨N, _, hNilpotent, hFiniteIndex⟩ :=
    polycyclic_has_finiteIndex_nilpotent_normal_subgroup H hP
  exact ⟨N, hNilpotent, hFiniteIndex⟩

/-- Finite solvable groups are polycyclic.

Every finite solvable group has a composition series with cyclic (prime order) factors.
The proof uses induction on cardinality: take a maximal normal subgroup N, then K/N is
simple and solvable hence cyclic of prime order, and N is solvable hence polycyclic by IH.

Note: A finite group is polycyclic iff it is solvable. The alternating group A_5 is
finite but not polycyclic (it's not solvable).

References:
- Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.4.11
-/
-- Helper: Trivial group is polycyclic
private lemma isPolycyclic_of_subsingleton (K : Type*) [Group K] [Subsingleton K] :
    IsPolycyclic K := by
  refine ⟨0, fun _ => ⊤, rfl, ?_, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  ext x; simp only [Subgroup.mem_top, Subgroup.mem_bot, Subsingleton.elim x 1]

-- Helper: Cyclic groups are polycyclic
lemma isPolycyclic_of_isCyclic (K : Type*) [Group K] [IsCyclic K] :
    IsPolycyclic K := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  refine ⟨1, ![⊤, ⊥], rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    exact bot_le
  · intro i
    fin_cases i
    change (⊥ : Subgroup K).subgroupOf ⊤ |>.Normal
    infer_instance
  · intro i h1 h2
    fin_cases i
    change QuotientIsCyclic (⊥ : Subgroup K) ⊤ bot_le (by infer_instance)
    unfold QuotientIsCyclic
    -- The quotient ⊤/⊥ is essentially K, which is cyclic
    use ⟨g, trivial⟩
    rw [Subgroup.eq_top_iff']
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨n, hn⟩ := hg k.val
      rw [Subgroup.mem_zpowers_iff]
      use n
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
      -- Goal: ↑((⟨g, trivial⟩ ^ n)⁻¹ * k) = 1
      -- We have hn : g ^ n = ↑k
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow]
      -- Goal: (g ^ n)⁻¹ * ↑k = 1
      simp only [← hn, inv_mul_cancel]

-- Helper: IsPolycyclic is preserved under group isomorphism
-- Proof: Map the polycyclic series via the isomorphism
lemma isPolycyclic_of_mulEquiv {K K' : Type*} [Group K] [Group K']
    (e : K ≃* K') (h : IsPolycyclic K) : IsPolycyclic K' := by
  obtain ⟨n, H, hTop, hBot, hLe, hNormal, hCyclic⟩ := h
  -- We map each subgroup H i to e(H i)
  -- The key is that e induces an isomorphism of quotients (H i)/(H i+1) ≃ e(H i)/e(H i+1)
  refine ⟨n, fun i => (H i).map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · -- H 0 = ⊤ => image is ⊤
    simp only [hTop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  · -- H n = ⊥ => image is ⊥
    simp only [hBot, Subgroup.map_bot]
  · -- Monotonicity
    intro i
    exact Subgroup.map_mono (hLe i)
  · -- Normality of quotients
    intro i
    have hNorm_i : (H i.succ).subgroupOf (H i.castSucc) |>.Normal := hNormal i
    -- Normal subgroups map to normal subgroups under isomorphisms
    constructor
    intro x hx_mem
    simp only [Subgroup.mem_subgroupOf] at hx_mem ⊢
    -- x.val is in (H i.succ).map e and in (H i.castSucc).map e
    simp only [Subgroup.mem_map] at hx_mem ⊢
    -- Get preimage of x.val in H i.succ
    obtain ⟨x', hx'_succ, hxe⟩ := hx_mem
    intro g
    -- Get preimage of g.val in H i.castSucc
    have hg_mem : g.val ∈ (H i.castSucc).map e.toMonoidHom := g.2
    simp only [Subgroup.mem_map] at hg_mem
    obtain ⟨g', hg'_cast, hge⟩ := hg_mem
    -- We need to show g * x * g⁻¹ is in (H i.succ).map e
    refine ⟨g' * x' * g'⁻¹, ?_, ?_⟩
    · -- Show g' * x' * g'⁻¹ ∈ H i.succ
      -- Use that (H i.succ).subgroupOf (H i.castSucc) is normal
      -- x' ∈ H i.succ means ⟨x', hLe i hx'_succ⟩ is in (H i.succ).subgroupOf (H i.castSucc)
      have hx'_cast : x' ∈ H i.castSucc := hLe i hx'_succ
      have hx_sub' : ⟨x', hx'_cast⟩ ∈ (H i.succ).subgroupOf (H i.castSucc) := by
        rw [Subgroup.mem_subgroupOf]; exact hx'_succ
      have := hNorm_i.conj_mem ⟨x', hx'_cast⟩ hx_sub' ⟨g', hg'_cast⟩
      rw [Subgroup.mem_subgroupOf] at this
      convert this using 1
    · -- Show e (g' * x' * g'⁻¹) = g * x * g⁻¹
      simp only [map_mul, map_inv, hxe, hge, Subgroup.coe_mul, Subgroup.coe_inv]
  · -- Cyclic quotients
    intro i h1' h2'
    have hCyc := hCyclic i (hLe i) (hNormal i)
    unfold QuotientIsCyclic at hCyc ⊢
    obtain ⟨gen, hgen⟩ := hCyc
    -- The generator for the image quotient is e(gen)
    use ⟨e gen, Subgroup.mem_map_of_mem e.toMonoidHom gen.2⟩
    rw [Subgroup.eq_top_iff']
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      -- k is in (H i.castSucc).map e
      obtain ⟨k', hk'_mem, hk'_eq⟩ : ∃ k' ∈ H i.castSucc, e k' = k.val := by
        have hk := k.2
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom] at hk
        exact hk
      -- ⟨k', hk'_mem⟩ is in Subgroup.zpowers of the original generator (modulo H i.succ)
      have hk'_in_gen : QuotientGroup.mk (s := (H i.succ).subgroupOf (H i.castSucc))
          (⟨k', hk'_mem⟩ : ↥(H i.castSucc)) ∈
          Subgroup.zpowers (QuotientGroup.mk (s := (H i.succ).subgroupOf (H i.castSucc)) gen) := by
        rw [hgen]; exact Subgroup.mem_top _
      rw [Subgroup.mem_zpowers_iff] at hk'_in_gen ⊢
      obtain ⟨m, hm⟩ := hk'_in_gen
      use m
      -- Need: gen' ^ m ≡ k mod (H i.succ).map e
      apply QuotientGroup.eq.mpr
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      -- From hm we have gen ^ m ≡ k' mod (H i.succ), i.e., (gen ^ m)⁻¹ * k' ∈ H i.succ
      have hmem := QuotientGroup.eq.mp hm
      simp only [Subgroup.mem_subgroupOf] at hmem
      -- hmem : ↑((gen ^ m)⁻¹ * ⟨k', hk'_mem⟩) ∈ H i.succ
      -- Witness: (gen^m)⁻¹ * k' works because e maps it to (e gen)^(-m) * k
      refine ⟨((gen : K) ^ m)⁻¹ * k', hmem, ?_⟩
      simp only [map_mul, map_inv, map_zpow, hk'_eq, Subgroup.coe_mul, Subgroup.coe_inv,
        SubgroupClass.coe_zpow]

theorem isPolycyclic_of_finite (K : Type*) [Group K] [Finite K] [IsSolvable K] :
    IsPolycyclic K := by
  sorry

/-- Subgroups of polycyclic groups are polycyclic.

Given a polycyclic series G = G_0 > G_1 > ... > G_n = 1, intersect with H to get
H_i = H cap G_i. The quotient (H cap G_i)/(H cap G_{i+1}) embeds into G_i/G_{i+1}
which is cyclic. Since subgroups of cyclic groups are cyclic (Mathlib: Subgroup.isCyclic),
the restricted series has cyclic quotients.

References:
- Segal, D. "Polycyclic Groups" (1983), Theorem 1.1
-/
theorem isPolycyclic_subgroup {G : Type*} [Group G] (hG : IsPolycyclic G)
    (H : Subgroup G) : IsPolycyclic H := by
  -- Obtain the polycyclic series for G
  obtain ⟨n, G', hTop, hBot, hLe, hNormal, hCyclic⟩ := hG
  -- The series for H is: H_i = H ∩ G_i, viewed as a subgroup of H
  -- Each quotient (H ∩ G_i) / (H ∩ G_{i+1}) embeds into G_i / G_{i+1} which is cyclic
  refine ⟨n, fun i => Subgroup.comap H.subtype (H ⊓ G' i), ?_, ?_, ?_, ?_, ?_⟩
  · -- H' 0 = H ⊓ G' 0 = H ⊓ ⊤ = H, viewed in H is ⊤
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_top]
    constructor
    · intro ⟨hxH, _⟩; exact Subgroup.mem_top x
    · intro _; rw [hTop]; exact ⟨x.2, Subgroup.mem_top _⟩
  · -- H' n = H ⊓ G' n = H ⊓ ⊥ = ⊥
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_bot]
    constructor
    · intro ⟨_, hg⟩
      rw [hBot] at hg
      simp only [Subgroup.mem_bot] at hg
      exact Subtype.ext hg
    · intro hx
      rw [hx]
      exact ⟨H.one_mem, (G' ⟨n, _⟩).one_mem⟩
  · -- Monotonicity: H' i.succ ≤ H' i.castSucc
    intro i
    apply Subgroup.comap_mono
    exact inf_le_inf_left H (hLe i)
  · -- Normality
    intro i
    -- Need: (H' i.succ).subgroupOf (H' i.castSucc) is normal
    have hNorm_i := hNormal i
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [Subgroup.mem_comap] at hx ⊢
    rw [Subgroup.mem_inf] at hx ⊢
    constructor
    · -- Show: H.subtype ↑(g * x * g⁻¹) ∈ H
      rw [Subgroup.subtype_apply]
      exact ((g * x * g⁻¹) : H).2
    · -- Show: H.subtype ↑(g * x * g⁻¹) ∈ G' i.succ
      -- Use that (G' i.succ).subgroupOf (G' i.castSucc) is normal
      -- x is in H ⊓ G' i.succ, g is in H ⊓ G' i.castSucc
      -- So x.val.val ∈ G' i.succ and g.val.val ∈ G' i.castSucc
      -- By normality, g.val.val * x.val.val * g.val.val⁻¹ ∈ G' i.succ
      have hx_succ : H.subtype (x : H) ∈ G' i.succ := hx.2
      have hg_cast : H.subtype (g : H) ∈ G' i.castSucc := by
        have hg_mem := g.2
        rw [Subgroup.mem_comap, Subgroup.mem_inf] at hg_mem
        exact hg_mem.2
      have hx_cast : H.subtype (x : H) ∈ G' i.castSucc := hLe i hx_succ
      -- Build subtype elements
      let x' : ↥(G' i.castSucc) := ⟨H.subtype (x : H), hx_cast⟩
      let g' : ↥(G' i.castSucc) := ⟨H.subtype (g : H), hg_cast⟩
      have hx'_sub : x' ∈ (G' i.succ).subgroupOf (G' i.castSucc) := by
        rw [Subgroup.mem_subgroupOf]; exact hx_succ
      have hconj := hNorm_i.conj_mem x' hx'_sub g'
      rw [Subgroup.mem_subgroupOf] at hconj
      convert hconj using 1
  · -- Cyclic quotients
    intro i h1' h2'
    -- Need: QuotientIsCyclic (H' i.succ) (H' i.castSucc) h1' h2'
    -- Strategy: The quotient (H ∩ G_i) / (H ∩ G_{i+1}) embeds into G_i / G_{i+1} which is cyclic.
    -- Since subgroups of cyclic groups are cyclic, the quotient is cyclic.

    -- Get the cyclic quotient from hCyclic
    have hCyc := hCyclic i (hLe i) (hNormal i)
    unfold QuotientIsCyclic at hCyc ⊢
    obtain ⟨gen, hgen⟩ := hCyc

    -- Subgroup inclusions
    have h_sub : H ⊓ G' i.castSucc ≤ G' i.castSucc := inf_le_right

    -- Show that (G' i.succ).subgroupOf (H ⊓ G' i.castSucc) is normal
    haveI hNorm_sub : ((G' i.succ).subgroupOf (H ⊓ G' i.castSucc)).Normal := by
      constructor
      intro x hx g
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have hx_cast : (x : G) ∈ G' i.castSucc := h_sub x.2
      have hg_cast : (g : G) ∈ G' i.castSucc := h_sub g.2
      let x' : ↥(G' i.castSucc) := ⟨x.1, hx_cast⟩
      let g' : ↥(G' i.castSucc) := ⟨g.1, hg_cast⟩
      have hx'_sub : x' ∈ (G' i.succ).subgroupOf (G' i.castSucc) := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      have hconj := (hNormal i).conj_mem x' hx'_sub g'
      rw [Subgroup.mem_subgroupOf] at hconj
      convert hconj using 1

    -- Use that the quotient embeds into a cyclic group
    haveI : IsCyclic (G' i.castSucc ⧸ (G' i.succ).subgroupOf (G' i.castSucc)) := by
      rw [isCyclic_iff_exists_zpowers_eq_top]
      exact ⟨gen, hgen⟩

    -- The homomorphism from the smaller quotient to the larger
    let hom := QuotientGroup.quotientMapSubgroupOfOfLe (le_refl (G' i.succ)) h_sub

    -- The hom is injective
    have hom_inj : Function.Injective hom := by
      intro x y hxy
      induction x using QuotientGroup.induction_on with
      | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          -- hxy : hom (mk a) = hom (mk b)
          -- This unfolds to mk (inclusion a) = mk (inclusion b) in the larger quotient
          have hxy' : QuotientGroup.mk (Subgroup.inclusion h_sub a) =
                      QuotientGroup.mk (Subgroup.inclusion h_sub b) := hxy
          rw [QuotientGroup.eq] at hxy' ⊢
          rw [Subgroup.mem_subgroupOf] at hxy' ⊢
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] at hxy' ⊢
          exact hxy'

    -- The hom shows our quotient embeds into a cyclic group, hence is cyclic
    haveI inst_cyclic : IsCyclic (↥(H ⊓ G' i.castSucc) ⧸ (G' i.succ).subgroupOf (H ⊓ G' i.castSucc)) :=
      isCyclic_of_injective hom hom_inj

    -- Get a generator for the cyclic quotient
    obtain ⟨gen', hgen'⟩ := @IsCyclic.exists_generator _ _ inst_cyclic
    obtain ⟨gen'_rep, hgen'_rep⟩ := QuotientGroup.mk_surjective gen'

    have hgen'_rep_H : (gen'_rep : G) ∈ H := gen'_rep.2.1
    have hgen'_rep_G : (gen'_rep : G) ∈ G' i.castSucc := gen'_rep.2.2

    -- Construct the element in comap H.subtype (H ⊓ G' i.castSucc)
    let gen_H : ↥H := ⟨gen'_rep.val, hgen'_rep_H⟩
    have hgen_H_mem : gen_H ∈ Subgroup.comap H.subtype (H ⊓ G' i.castSucc) := by
      rw [Subgroup.mem_comap, Subgroup.mem_inf]
      exact ⟨hgen'_rep_H, hgen'_rep_G⟩

    use ⟨gen_H, hgen_H_mem⟩

    -- Show this generates the quotient
    rw [Subgroup.eq_top_iff']
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hk_mem := k.2
      rw [Subgroup.mem_comap, Subgroup.mem_inf] at hk_mem

      -- Lift k to an element of H ⊓ G' i.castSucc
      let k' : ↥(H ⊓ G' i.castSucc) := ⟨H.subtype k.1, hk_mem⟩

      -- k' is in the zpowers of gen'
      have hk'_gen : QuotientGroup.mk k' ∈ Subgroup.zpowers gen' := hgen' (QuotientGroup.mk k')

      rw [Subgroup.mem_zpowers_iff] at hk'_gen ⊢
      obtain ⟨m, hm⟩ := hk'_gen
      use m

      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf]

      -- From hm: gen'^m = mk k' in the quotient
      have hm_eq : QuotientGroup.mk (s := (G' i.succ).subgroupOf (H ⊓ G' i.castSucc)) (gen'_rep ^ m) =
                   QuotientGroup.mk (s := (G' i.succ).subgroupOf (H ⊓ G' i.castSucc)) k' := by
        -- We have hm : gen' ^ m = ↑k' and hgen'_rep : ↑gen'_rep = gen'
        -- So gen'^m = (↑gen'_rep)^m = ↑(gen'_rep^m)
        rw [QuotientGroup.mk_zpow, hgen'_rep, hm]
      have hm' := QuotientGroup.eq.mp hm_eq
      rw [Subgroup.mem_subgroupOf] at hm'

      constructor
      · -- Show membership in H
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, Subgroup.subtype_apply]
        exact H.mul_mem (H.inv_mem (H.zpow_mem hgen'_rep_H m)) hk_mem.1
      · -- Show membership in G' i.succ
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, Subgroup.subtype_apply]
        convert hm' using 1

-- Variant: If H <= K as subgroups of G and K is polycyclic, then H is polycyclic
-- Note: This requires transferring IsPolycyclic across the isomorphism H ≃* H.subgroupOf K
theorem isPolycyclic_of_le {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (hK : IsPolycyclic K) : IsPolycyclic H := by
  -- H.subgroupOf K is a subgroup of K, so it's polycyclic
  have h1 : IsPolycyclic (H.subgroupOf K) := isPolycyclic_subgroup hK _
  -- H.subgroupOf K ≃* H via subgroupOfEquivOfLe
  exact isPolycyclic_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK) h1

/-- Extensions of polycyclic groups are polycyclic.

If N is normal in G with both N and G/N polycyclic, then G is polycyclic.
The proof lifts the polycyclic series for G/N via comap (ending at N), then
concatenates with the polycyclic series for N.

References:
- Segal, D. "Polycyclic Groups" (1983), Proposition 1.2
-/
theorem isPolycyclic_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : IsPolycyclic N) (hQ : IsPolycyclic (G ⧸ N)) : IsPolycyclic G := by
  -- This is a substantial theorem requiring careful index manipulation.
  -- The proof constructs a polycyclic series for G by:
  -- 1. Lifting the series for G/N via comap
  -- 2. Concatenating with the series for N via map N.subtype
  sorry

/-- If H is a finite-index polycyclic subgroup of G, then G is polycyclic.

Proof outline: H polycyclic implies H solvable. H.normalCore is solvable (subgroup of solvable).
For finite-index solvable subgroups, G is solvable. Then G/H.normalCore is finite and solvable,
hence polycyclic. H.normalCore is polycyclic (subgroup of H). G is an extension of polycyclic
groups, hence polycyclic.

References:
- Segal, D. "Polycyclic Groups" (1983), Proposition 1.6
-/
theorem isPolycyclic_of_finiteIndex_polycyclic (H : Subgroup G) [H.FiniteIndex]
    (hH : IsPolycyclic H) : IsPolycyclic G := by
  sorry

/-- Subgroups of polycyclic groups are finitely generated (Mal'cev 1951).

This is Mal'cev's theorem (1951). The proof uses induction on the length of the
polycyclic series. If G = G_0 > G_1 > ... > G_n = 1 with cyclic quotients, then
for H <= G, the quotient H/(H cap G_1) embeds into G/G_1 which is cyclic, so
H/(H cap G_1) is f.g. (cyclic). By induction, H cap G_1 is f.g., so H is f.g.

References:
- Mal'cev, A. I. "On certain classes of infinite soluble groups" (1951)
- Segal, D. "Polycyclic Groups" (1983), Theorem 1.2
-/
theorem Subgroup.fg_of_polycyclic (hG : IsPolycyclic G) (H : Subgroup G) : FG H := by
  sorry

/-! ### Main Theorem -/

/-- **Mal'cev's Theorem**: For finitely generated groups, virtually nilpotent is equivalent
to polycyclic.

The forward direction uses: f.g. nilpotent groups are polycyclic, and finite extensions
of polycyclic groups are polycyclic.

The reverse direction uses: polycyclic groups have finite-index nilpotent subgroups
(the Fitting subgroup).
-/
theorem isVirtuallyNilpotent_iff_polycyclic [FG G] : IsVirtuallyNilpotent G ↔ IsPolycyclic G := by
  constructor
  · -- (=>) Virtually nilpotent => Polycyclic
    intro ⟨H, hNil, hFin⟩
    haveI : H.FiniteIndex := hFin
    haveI : IsNilpotent H := hNil
    -- H is f.g. (finite-index subgroup of f.g. group)
    haveI : FG H := Subgroup.fg_of_index_ne_zero H
    -- H is nilpotent and f.g., hence polycyclic
    have hHP : IsPolycyclic H := isPolycyclic_of_isNilpotent_fg H
    -- G is a finite extension of H, hence polycyclic
    exact isPolycyclic_of_finiteIndex_polycyclic H hHP
  · -- (<=) Polycyclic => Virtually nilpotent
    intro hP
    exact isVirtuallyNilpotent_of_isPolycyclic G hP

end

end Group
