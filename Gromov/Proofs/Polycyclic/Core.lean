/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Polycyclic groups and their relationship to virtual nilpotency.
-/

module

public import Gromov.Proofs.VirtuallyNilpotent.Core
public import Mathlib.GroupTheory.Schreier

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

/-! ### Helper Lemmas -/

/-- Trivial group is polycyclic -/
lemma isPolycyclic_of_subsingleton (K : Type*) [Group K] [Subsingleton K] :
    IsPolycyclic K := by
  refine ⟨0, fun _ => ⊤, rfl, ?_, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  ext x; simp only [Subgroup.mem_top, Subgroup.mem_bot, Subsingleton.elim x 1]

/-- Cyclic groups are polycyclic -/
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
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow]
      simp only [← hn, inv_mul_cancel]

/-- IsPolycyclic is preserved under group isomorphism -/
lemma isPolycyclic_of_mulEquiv {K K' : Type*} [Group K] [Group K']
    (e : K ≃* K') (h : IsPolycyclic K) : IsPolycyclic K' := by
  obtain ⟨n, H, hTop, hBot, hLe, hNormal, hCyclic⟩ := h
  -- We map each subgroup H i to e(H i)
  refine ⟨n, fun i => (H i).map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hTop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  · simp only [hBot, Subgroup.map_bot]
  · intro i
    exact Subgroup.map_mono (hLe i)
  · intro i
    have hNorm_i : (H i.succ).subgroupOf (H i.castSucc) |>.Normal := hNormal i
    constructor
    intro x hx_mem
    simp only [Subgroup.mem_subgroupOf] at hx_mem ⊢
    simp only [Subgroup.mem_map] at hx_mem ⊢
    obtain ⟨x', hx'_succ, hxe⟩ := hx_mem
    intro g
    have hg_mem : g.val ∈ (H i.castSucc).map e.toMonoidHom := g.2
    simp only [Subgroup.mem_map] at hg_mem
    obtain ⟨g', hg'_cast, hge⟩ := hg_mem
    refine ⟨g' * x' * g'⁻¹, ?_, ?_⟩
    · have hx'_cast : x' ∈ H i.castSucc := hLe i hx'_succ
      have hx_sub' : ⟨x', hx'_cast⟩ ∈ (H i.succ).subgroupOf (H i.castSucc) := by
        rw [Subgroup.mem_subgroupOf]; exact hx'_succ
      have := hNorm_i.conj_mem ⟨x', hx'_cast⟩ hx_sub' ⟨g', hg'_cast⟩
      rw [Subgroup.mem_subgroupOf] at this
      convert this using 1
    · simp only [map_mul, map_inv, hxe, hge, Subgroup.coe_mul, Subgroup.coe_inv]
  · intro i h1' h2'
    have hCyc := hCyclic i (hLe i) (hNormal i)
    unfold QuotientIsCyclic at hCyc ⊢
    obtain ⟨gen, hgen⟩ := hCyc
    use ⟨e gen, Subgroup.mem_map_of_mem e.toMonoidHom gen.2⟩
    rw [Subgroup.eq_top_iff']
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨k', hk'_mem, hk'_eq⟩ : ∃ k' ∈ H i.castSucc, e k' = k.val := by
        have hk := k.2
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom] at hk
        exact hk
      have hk'_in_gen : QuotientGroup.mk (s := (H i.succ).subgroupOf (H i.castSucc))
          (⟨k', hk'_mem⟩ : ↥(H i.castSucc)) ∈
          Subgroup.zpowers (QuotientGroup.mk (s := (H i.succ).subgroupOf (H i.castSucc)) gen) := by
        rw [hgen]; exact Subgroup.mem_top _
      rw [Subgroup.mem_zpowers_iff] at hk'_in_gen ⊢
      obtain ⟨m, hm⟩ := hk'_in_gen
      use m
      apply QuotientGroup.eq.mpr
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      have hmem := QuotientGroup.eq.mp hm
      simp only [Subgroup.mem_subgroupOf] at hmem
      refine ⟨((gen : K) ^ m)⁻¹ * k', hmem, ?_⟩
      simp only [map_mul, map_inv, map_zpow, hk'_eq, Subgroup.coe_mul, Subgroup.coe_inv,
        SubgroupClass.coe_zpow]

-- Auxiliary lemma: comap of ⊥ through quotient map is the kernel
private lemma comap_bot_eq_ker {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (⊥ : Subgroup (G ⧸ N)).comap (QuotientGroup.mk' N) = N := by
  rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']

/-- Extensions of polycyclic groups are polycyclic.

If N is normal in G with both N and G/N polycyclic, then G is polycyclic.
The proof lifts the polycyclic series for G/N via comap (ending at N), then
concatenates with the polycyclic series for N.

References:
- Segal, D. "Polycyclic Groups" (1983), Proposition 1.2
-/
theorem isPolycyclic_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : IsPolycyclic N) (hQ : IsPolycyclic (G ⧸ N)) : IsPolycyclic G := by
  -- Get polycyclic series for N and G/N
  obtain ⟨k, N_series, hN_top, hN_bot, hN_le, hN_norm, hN_cyc⟩ := hN
  obtain ⟨m, Q_series, hQ_top, hQ_bot, hQ_le, hQ_norm, hQ_cyc⟩ := hQ
  -- Handle edge cases first
  by_cases hk0 : k = 0
  · -- N is trivial (N_series 0 = ⊤ = ⊥)
    subst hk0
    have hN_trivial : N = ⊥ := by
      have h1 : (⊤ : Subgroup N) = ⊥ := by rw [← hN_top]; convert hN_bot
      ext x
      simp only [Subgroup.mem_bot]
      constructor
      · intro hx
        have : (⟨x, hx⟩ : N) ∈ (⊤ : Subgroup N) := Subgroup.mem_top _
        rw [h1] at this
        simp only [Subgroup.mem_bot, Subtype.ext_iff] at this
        exact this
      · intro hx; rw [hx]; exact N.one_mem
    -- G ≅ G/N which is polycyclic
    have hQ' : IsPolycyclic (G ⧸ N) := ⟨m, Q_series, hQ_top, hQ_bot, hQ_le, hQ_norm, hQ_cyc⟩
    subst hN_trivial
    exact isPolycyclic_of_mulEquiv (QuotientGroup.quotientBot (G := G)) hQ'
  by_cases hm0 : m = 0
  · -- G/N is trivial, so G = N
    subst hm0
    have hQ_trivial : (⊤ : Subgroup (G ⧸ N)) = ⊥ := by rw [← hQ_top]; convert hQ_bot
    have hG_eq_N : (⊤ : Subgroup G) = N := by
      ext x
      simp only [Subgroup.mem_top, true_iff]
      have h1 : (QuotientGroup.mk' N x : G ⧸ N) ∈ (⊤ : Subgroup (G ⧸ N)) := Subgroup.mem_top _
      rw [hQ_trivial, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hN' : IsPolycyclic N := ⟨k, N_series, hN_top, hN_bot, hN_le, hN_norm, hN_cyc⟩
    have hN_poly_full : IsPolycyclic (⊤ : Subgroup G) := by
      have hequiv : N ≃* (⊤ : Subgroup G) := by
        refine ⟨⟨fun x => ⟨x.val, by rw [hG_eq_N]; exact x.2⟩,
          fun x => ⟨x.val, by rw [← hG_eq_N]; exact x.2⟩, ?_, ?_⟩, ?_⟩
        · intro x; simp
        · intro x; simp
        · intro x y; simp [Subgroup.coe_mul]
      exact isPolycyclic_of_mulEquiv hequiv hN'
    exact isPolycyclic_of_mulEquiv Subgroup.topEquiv hN_poly_full
  -- Main case: both m, k > 0
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
  -- Build the combined series
  -- G_series has m + k + 1 terms: indices 0 to m + k
  -- For i ≤ m: G_series i = comap Q_i
  -- For i > m: G_series i = map N_{i - m}
  -- Note: at i = m, comap Q_m = N, and at i = m+1, map N_1 ≤ N
  let G_series : Fin (m + k + 1) → Subgroup G := fun i =>
    if hi : i.val ≤ m then
      (Q_series ⟨i.val, Nat.lt_succ_of_le hi⟩).comap (QuotientGroup.mk' N)
    else
      (N_series ⟨i.val - m, by omega⟩).map N.subtype
  refine ⟨m + k, G_series, ?_, ?_, ?_, ?_, ?_⟩
  · -- G_series 0 = comap Q_0 = comap ⊤ = ⊤
    simp only [G_series, Fin.val_zero, Nat.zero_le, dite_true]
    have h0 : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = 0 := rfl
    rw [h0, hQ_top, Subgroup.comap_top]
  · -- G_series (m + k) = map N_k = map ⊥ = ⊥
    simp only [G_series]
    have h_not_le : ¬ (m + k) ≤ m := by omega
    simp only [h_not_le, dite_false]
    have hsub : m + k - m = k := Nat.add_sub_cancel_left m k
    have hk_fin : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ := rfl
    simp only [hsub, hN_bot, Subgroup.map_bot]
  · -- Monotonicity
    intro i
    simp only [G_series]
    by_cases hi : i.castSucc.val ≤ m
    · by_cases hi' : i.succ.val ≤ m
      · -- Both in comap region
        simp only [hi, hi', dite_true]
        apply Subgroup.comap_mono
        simp only [Fin.val_castSucc] at hi
        simp only [Fin.val_succ] at hi'
        have hi_lt : i.val < m := by omega
        have hle := hQ_le ⟨i.val, hi_lt⟩
        convert hle using 2
      · -- Transition: castSucc in comap (= m), succ in map
        simp only [hi, hi', dite_true, dite_false]
        have hi_eq : i.val = m := by simp only [Fin.val_castSucc, Fin.val_succ] at hi hi'; omega
        -- comap Q_m = N, map N_{m+1-m} = map N_1 ≤ N
        rw [show (⟨i.castSucc.val, Nat.lt_succ_of_le hi⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩
            by simp [hi_eq]]
        rw [hQ_bot, comap_bot_eq_ker]
        apply Subgroup.map_subtype_le
    · -- Both in map region
      have hi_cast : ¬ i.castSucc.val ≤ m := hi
      have hi_succ : ¬ i.succ.val ≤ m := by
        simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega
      simp only [hi_cast, hi_succ, dite_false]
      apply Subgroup.map_mono
      -- Extract the numeric values for cleaner arithmetic
      have h_castSucc_val : i.castSucc.val = i.val := Fin.val_castSucc i
      have h_succ_val : i.succ.val = i.val + 1 := Fin.val_succ i
      rw [h_castSucc_val] at hi
      have hi_bound : i.val < m + k := i.isLt
      have hbound' : i.val - m < k := by omega
      have hN_le_i := hN_le ⟨i.val - m, hbound'⟩
      -- Need to show N_series(i.succ.val - m) ≤ N_series(i.castSucc.val - m)
      -- i.succ.val - m = i.val + 1 - m, i.castSucc.val - m = i.val - m
      -- hN_le_i gives: N_series(i.val - m + 1) ≤ N_series(i.val - m)
      have h1 : i.succ.val - m = i.val - m + 1 := by rw [h_succ_val]; omega
      have h2 : i.castSucc.val - m = i.val - m := by rw [h_castSucc_val]
      simp only [h1, h2]
      convert hN_le_i using 2
  · -- Normality: Use that subgroupOf inherits normality from both series
    intro i
    simp only [G_series]
    by_cases hi : i.castSucc.val ≤ m
    · by_cases hi' : i.succ.val ≤ m
      · -- Both in comap region: normality inherited from Q_series
        simp only [hi', dite_true]
        have hi_val : i.val ≤ m := by simp only [Fin.val_castSucc] at hi; exact hi
        have hi'_val : i.val + 1 ≤ m := by simp only [Fin.val_succ] at hi'; exact hi'
        have hbound : i.val < m := by omega
        -- The quotient Q_series(i+1) / Q_series(i) is normal
        have hQ_norm_i := hQ_norm ⟨i.val, hbound⟩
        -- We need to show normality of the comap'd subgroups
        constructor; intro x hx g
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hx ⊢
        have hg_mem : QuotientGroup.mk' N g.val ∈
            Q_series ⟨i.castSucc.val, Nat.lt_succ_of_le hi⟩ := by
          have := g.2; simp only [hi, dite_true, Subgroup.mem_comap] at this; exact this
        -- x maps into Q_series(i+1) ≤ Q_series(i), g maps into Q_series(i)
        have hx_q : QuotientGroup.mk' N x ∈ Q_series ⟨i.succ.val, Nat.lt_succ_of_le hi'⟩ := hx
        -- Set up the index for hQ_norm_i
        set j : Fin m := ⟨i.val, hbound⟩ with hj_def
        -- Convert membership using the fact that (j : Fin m).succ.val = i.val + 1 = i.succ.val
        have hx_in_succ : QuotientGroup.mk' N x ∈ Q_series j.succ := by
          have : Q_series j.succ = Q_series ⟨i.succ.val, Nat.lt_succ_of_le hi'⟩ := by
            apply congrArg Q_series
            simp only [Fin.ext_iff, Fin.val_succ, hj_def]
          rw [this]; exact hx_q
        have hg_in_castSucc : QuotientGroup.mk' N g.val ∈ Q_series j.castSucc := by
          have : Q_series j.castSucc = Q_series ⟨i.castSucc.val, Nat.lt_succ_of_le hi⟩ := by
            apply congrArg Q_series
            simp only [Fin.ext_iff, Fin.val_castSucc, hj_def]
          rw [this]; exact hg_mem
        have hx_in_castSucc : QuotientGroup.mk' N x ∈ Q_series j.castSucc := hQ_le j hx_in_succ
        have hconj := hQ_norm_i.conj_mem ⟨QuotientGroup.mk' N x, hx_in_castSucc⟩
          (by rw [Subgroup.mem_subgroupOf]; exact hx_in_succ)
          ⟨QuotientGroup.mk' N g.val, hg_in_castSucc⟩
        simp only [Subgroup.mem_subgroupOf] at hconj
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] at hconj ⊢
        have h_succ_eq : Q_series j.succ = Q_series ⟨i.succ.val, Nat.lt_succ_of_le hi'⟩ := by
          apply congrArg Q_series
          simp only [Fin.ext_iff, Fin.val_succ, hj_def]
        rw [← h_succ_eq]
        exact hconj
      · -- Transition: castSucc in comap (= m), succ in map region
        simp only [hi', dite_false]
        have h_cast : i.castSucc.val = i.val := Fin.val_castSucc i
        have h_succ : i.succ.val = i.val + 1 := Fin.val_succ i
        have hi_eq : i.castSucc.val = m := by
          rw [h_cast] at hi
          rw [h_succ] at hi'
          push_neg at hi'
          omega
        constructor; intro x hx g
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx ⊢
        obtain ⟨x', hx'_mem, hx'_eq⟩ := hx
        have hg_mem := g.2
        simp only [hi, dite_true, Subgroup.mem_comap] at hg_mem
        -- g is in comap Q_m = N
        have hi_val_eq : i.val = m := by rw [← h_cast]; exact hi_eq
        have hg_in_N : g.val ∈ N := by
          have hcast_eq : (⟨i.castSucc.val, Nat.lt_succ_of_le hi⟩ : Fin (m + 1)) =
              ⟨m, Nat.lt_succ_self m⟩ := by
            simp only [h_cast, hi_val_eq]
          have : QuotientGroup.mk' N g.val ∈ Q_series ⟨m, Nat.lt_succ_self m⟩ := by
            rw [← hcast_eq]; exact hg_mem
          rw [hQ_bot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
          exact this
        obtain ⟨g', hg'_eq⟩ : ∃ g' : N, N.subtype g' = g.val := ⟨⟨g.val, hg_in_N⟩, rfl⟩
        -- x' is in N_series(1), we need to show g' * x' * g'^{-1} is also in N_series(1)
        have hidx : i.succ.val - m = 1 := by simp only [h_succ, hi_val_eq]; omega
        refine ⟨g' * x' * g'⁻¹, ?_, ?_⟩
        · -- Use normality of N_series(1) in N_series(0) = ⊤
          have hN1_normal := hN_norm ⟨0, hk_pos⟩
          have hg'_in_top : g' ∈ N_series 0 := by rw [hN_top]; exact Subgroup.mem_top g'
          have hx'_in_N1 : x' ∈ N_series ⟨1, by omega⟩ := by
            convert hx'_mem using 2; simp only [Fin.ext_iff]; exact hidx.symm
          have hx'_in_top : x' ∈ N_series 0 := by
            have := hN_le ⟨0, hk_pos⟩; apply this
            convert hx'_in_N1 using 1
          have hconj := hN1_normal.conj_mem ⟨x', hx'_in_top⟩
            (by rw [Subgroup.mem_subgroupOf]; convert hx'_in_N1 using 1) ⟨g', hg'_in_top⟩
          simp only [Subgroup.mem_subgroupOf] at hconj
          have h_succ_0 : (⟨0, hk_pos⟩ : Fin k).succ.val = 1 := rfl
          convert hconj using 2; simp only [Fin.ext_iff, h_succ, hi_val_eq, h_succ_0]; omega
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype, ← hx'_eq, ← hg'_eq]
    · -- Both in map region: normality inherited from N_series
      have h_cast' : i.castSucc.val = i.val := Fin.val_castSucc i
      have h_succ' : i.succ.val = i.val + 1 := Fin.val_succ i
      have hi_gt : i.val > m := by simp only [← h_cast']; push_neg at hi; exact hi
      have hi' : ¬ i.succ.val ≤ m := by rw [h_succ']; omega
      simp only [hi', dite_false]
      -- Define the index for N_series carefully
      have hcast_idx_bound : i.val - m < k := by have := i.isLt; omega
      set cast_idx : Fin k := ⟨i.val - m, hcast_idx_bound⟩ with hcast_idx_def
      have hN_norm_cast := hN_norm cast_idx
      constructor; intro x hx g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx ⊢
      obtain ⟨x', hx'_mem, hx'_eq⟩ := hx
      have hg_mem := g.2
      simp only [hi, dite_false, Subgroup.mem_map] at hg_mem
      obtain ⟨g', hg'_mem, hg'_eq⟩ := hg_mem
      refine ⟨g' * x' * g'⁻¹, ?_, ?_⟩
      · -- Use normality of N_series
        have hcast_succ_val : cast_idx.succ.val = i.val - m + 1 := by simp [hcast_idx_def]
        have hcast_castSucc_val : cast_idx.castSucc.val = i.val - m := by simp [hcast_idx_def]
        have hx'_in_succ : x' ∈ N_series cast_idx.succ := by
          convert hx'_mem using 2
          simp only [Fin.ext_iff, h_succ', hcast_succ_val]; omega
        have hx'_in_cast : x' ∈ N_series cast_idx.castSucc := by
          have hle := hN_le cast_idx; apply hle; exact hx'_in_succ
        have hg'_in_cast : g' ∈ N_series cast_idx.castSucc := by
          convert hg'_mem using 2
        have hconj := hN_norm_cast.conj_mem ⟨x', hx'_in_cast⟩
          (by rw [Subgroup.mem_subgroupOf]; exact hx'_in_succ) ⟨g', hg'_in_cast⟩
        simp only [Subgroup.mem_subgroupOf] at hconj
        (convert hconj using 2; simp only [Fin.ext_iff, h_succ', hcast_succ_val]; omega)
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype, ← hx'_eq, ← hg'_eq]
  · -- Cyclic quotients
    intro i h1' h2'
    unfold QuotientIsCyclic
    simp only [G_series] at h1' ⊢
    have h_cast_val : i.castSucc.val = i.val := Fin.val_castSucc i
    have h_succ_val : i.succ.val = i.val + 1 := Fin.val_succ i
    by_cases hi : i.castSucc.val ≤ m
    · by_cases hi' : i.succ.val ≤ m
      · -- Comap region: both castSucc and succ are ≤ m
        simp only [hi, hi', dite_true] at h1' ⊢
        -- Define j : Fin m such that j.val = i.val
        have hj_bound : i.val < m := by rw [h_succ_val] at hi'; omega
        set j : Fin m := ⟨i.val, hj_bound⟩ with hj_def
        have hj_succ_val : j.succ.val = i.val + 1 := Fin.val_succ j
        have hj_castSucc_val : j.castSucc.val = i.val := Fin.val_castSucc j
        -- Use hQ_cyc for index j
        have hQ_cyc_j := hQ_cyc j (hQ_le j) (hQ_norm j)
        unfold QuotientIsCyclic at hQ_cyc_j
        obtain ⟨gen, hgen⟩ := hQ_cyc_j
        obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N gen.val
        have hcast_eq : Q_series j.castSucc =
            Q_series ⟨i.castSucc.val, Nat.lt_succ_of_le hi⟩ := by
          apply congrArg Q_series; simp only [Fin.ext_iff, hj_castSucc_val, h_cast_val]
        have hg_mem : g ∈
            (Q_series ⟨i.castSucc.val, Nat.lt_succ_of_le hi⟩).comap (QuotientGroup.mk' N) := by
          rw [Subgroup.mem_comap, hg, ← hcast_eq]; exact gen.2
        have hg_mem' : g ∈
            (if hx : i.castSucc.val ≤ m then
              (Q_series ⟨i.castSucc.val, Nat.lt_succ_of_le hx⟩).comap (QuotientGroup.mk' N)
            else (N_series ⟨i.castSucc.val - m, by have := i.isLt; omega⟩).map N.subtype) := by
          simp only [hi, dite_true]; exact hg_mem
        refine ⟨⟨g, hg_mem'⟩, ?_⟩
        rw [Subgroup.eq_top_iff']; intro q
        induction q using QuotientGroup.induction_on with
        | H x =>
          have hx_mem := x.2
          simp only [hi, dite_true, Subgroup.mem_comap] at hx_mem
          have hx_in_cast : QuotientGroup.mk' N x ∈ Q_series j.castSucc := by
            rw [hcast_eq]; exact hx_mem
          have hx_gen : QuotientGroup.mk
              (s := (Q_series j.succ).subgroupOf (Q_series j.castSucc))
              ⟨QuotientGroup.mk' N x, hx_in_cast⟩ ∈
              Subgroup.zpowers (QuotientGroup.mk gen) := by
            rw [hgen]; exact Subgroup.mem_top _
          rw [Subgroup.mem_zpowers_iff] at hx_gen ⊢
          obtain ⟨n, hn⟩ := hx_gen
          use n
          apply QuotientGroup.eq.mpr
          -- Goal has the dite form; simplify with hi' to get comap form
          simp only [hi', dite_true, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
          have hn' := QuotientGroup.eq.mp hn
          simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
            SubgroupClass.coe_zpow] at hn'
          have hsucc_eq : Q_series j.succ = Q_series ⟨i.succ.val, Nat.lt_succ_of_le hi'⟩ := by
            apply congrArg Q_series; simp only [Fin.ext_iff, hj_succ_val, h_succ_val]
          rw [← hsucc_eq]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, map_mul,
            map_inv, map_zpow, hg]
          exact hn'
      · -- Transition: castSucc in comap (= m), succ in map region
        simp only [hi, hi', dite_true, dite_false] at h1' ⊢
        have hi_val_eq : i.val = m := by rw [h_cast_val] at hi; rw [h_succ_val] at hi'; omega
        -- Use hN_cyc for index 0
        have hN_cyc_0 := hN_cyc ⟨0, hk_pos⟩ (hN_le ⟨0, hk_pos⟩) (hN_norm ⟨0, hk_pos⟩)
        unfold QuotientIsCyclic at hN_cyc_0
        obtain ⟨gen, hgen⟩ := hN_cyc_0
        have hcast_eq : (⟨i.castSucc.val, Nat.lt_succ_of_le hi⟩ : Fin (m + 1)) =
            ⟨m, Nat.lt_succ_self m⟩ := by
          simp only [h_cast_val, hi_val_eq]
        -- gen : ↥(N_series (⟨0, hk_pos⟩).castSucc) = ↥(N_series 0) = ↥⊤ (in N)
        -- gen.val : N, so N.subtype gen.val : G
        let g : G := N.subtype gen.val
        have hg_in_N : g ∈ N := (gen.val).2
        have hg_mem : g ∈
            (Q_series ⟨i.castSucc.val, Nat.lt_succ_of_le hi⟩).comap (QuotientGroup.mk' N) := by
          rw [hcast_eq, Subgroup.mem_comap, hQ_bot, Subgroup.mem_bot]
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hg_in_N
        have hg_mem' : g ∈
            (if hx : i.castSucc.val ≤ m then
              (Q_series ⟨i.castSucc.val, Nat.lt_succ_of_le hx⟩).comap (QuotientGroup.mk' N)
            else (N_series ⟨i.castSucc.val - m, by have := i.isLt; omega⟩).map N.subtype) := by
          simp only [hi, dite_true]; exact hg_mem
        refine ⟨⟨g, hg_mem'⟩, ?_⟩
        rw [Subgroup.eq_top_iff']; intro q
        induction q using QuotientGroup.induction_on with
        | H x =>
          have hx_mem := x.2
          simp only [hi, dite_true, Subgroup.mem_comap] at hx_mem
          rw [hcast_eq, hQ_bot, Subgroup.mem_bot, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at hx_mem
          obtain ⟨x', hx'_eq⟩ : ∃ x' : N, N.subtype x' = x := ⟨⟨x, hx_mem⟩, rfl⟩
          have hx'_in_top : x' ∈ N_series 0 := by rw [hN_top]; exact Subgroup.mem_top x'
          have hx'_gen : QuotientGroup.mk
              (s := (N_series (⟨0, hk_pos⟩ : Fin k).succ).subgroupOf
                (N_series (⟨0, hk_pos⟩ : Fin k).castSucc))
              ⟨x', hx'_in_top⟩ ∈
              Subgroup.zpowers (QuotientGroup.mk gen) := by
            rw [hgen]; exact Subgroup.mem_top _
          rw [Subgroup.mem_zpowers_iff] at hx'_gen ⊢
          obtain ⟨n, hn⟩ := hx'_gen
          use n
          apply QuotientGroup.eq.mpr
          -- The goal is an if-expression; simplify with hi' to get map form
          simp only [hi', dite_false, Subgroup.mem_subgroupOf, Subgroup.mem_map]
          have hn' := QuotientGroup.eq.mp hn
          simp only [Subgroup.mem_subgroupOf] at hn'
          have hidx : i.succ.val - m = 1 := by rw [h_succ_val]; omega
          have h0_succ_val : (⟨0, hk_pos⟩ : Fin k).succ.val = 1 := rfl
          have hsucc_eq : N_series ⟨i.succ.val - m, by have := i.isLt; omega⟩ =
              N_series (⟨0, hk_pos⟩ : Fin k).succ := by
            apply congrArg N_series; simp only [Fin.ext_iff, hidx, h0_succ_val]
          refine ⟨(gen.val ^ n)⁻¹ * x', ?_, ?_⟩
          · rw [hsucc_eq]; exact hn'
          · simp only [Subgroup.coe_subtype, map_mul, map_inv, map_zpow, hx'_eq, g]
            -- Goal: (↑↑gen ^ n)⁻¹ * ↑x = ↑((⟨↑↑gen, _⟩ ^ n)⁻¹ * x)
            -- The LHS uses gen.val : N, subtyped to G, then zpow'd
            -- The RHS uses g = N.subtype gen.val, wrapped as ⟨g, hg_mem'⟩, then zpow'd and coerced
            -- These should be definitionally equal after unfolding
            rfl
    · -- Both in map region
      have hi_gt : i.val > m := by rw [h_cast_val] at hi; omega
      have hi' : ¬ i.succ.val ≤ m := by rw [h_succ_val]; omega
      simp only [hi, hi', dite_false] at h1' ⊢
      -- Define j : Fin k such that j.val = i.val - m
      have hj_bound : i.val - m < k := by have := i.isLt; omega
      set j : Fin k := ⟨i.val - m, hj_bound⟩ with hj_def
      have hj_succ_val : j.succ.val = i.val - m + 1 := Fin.val_succ j
      have hj_castSucc_val : j.castSucc.val = i.val - m := Fin.val_castSucc j
      -- Use hN_cyc for index j
      have hN_cyc_j := hN_cyc j (hN_le j) (hN_norm j)
      unfold QuotientIsCyclic at hN_cyc_j
      obtain ⟨gen, hgen⟩ := hN_cyc_j
      have hcast_eq : N_series j.castSucc =
          N_series ⟨i.castSucc.val - m, by have := i.isLt; rw [h_cast_val]; omega⟩ := by
        apply congrArg N_series; simp only [Fin.ext_iff, hj_castSucc_val, h_cast_val]
      have hg_mem : N.subtype gen.val ∈
          (N_series ⟨i.castSucc.val - m, by have := i.isLt; rw [h_cast_val]; omega⟩).map
            N.subtype := by
        rw [← hcast_eq]; exact Subgroup.mem_map_of_mem N.subtype gen.2
      have hg_mem' : N.subtype gen.val ∈
          (if hx : i.castSucc.val ≤ m then
            (Q_series ⟨i.castSucc.val, Nat.lt_succ_of_le hx⟩).comap (QuotientGroup.mk' N)
          else (N_series ⟨i.castSucc.val - m, by have := i.isLt; omega⟩).map N.subtype) := by
        simp only [hi, dite_false]; exact hg_mem
      refine ⟨⟨N.subtype gen.val, hg_mem'⟩, ?_⟩
      rw [Subgroup.eq_top_iff']; intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        have hx_mem := x.2
        simp only [hi, dite_false, Subgroup.mem_map] at hx_mem
        obtain ⟨x', hx'_mem, hx'_eq⟩ := hx_mem
        have hx'_in_cast : x' ∈ N_series j.castSucc := by rw [hcast_eq]; exact hx'_mem
        have hx'_gen : QuotientGroup.mk (s := (N_series j.succ).subgroupOf (N_series j.castSucc))
            ⟨x', hx'_in_cast⟩ ∈ Subgroup.zpowers (QuotientGroup.mk gen) := by
          rw [hgen]; exact Subgroup.mem_top _
        rw [Subgroup.mem_zpowers_iff] at hx'_gen ⊢
        obtain ⟨n, hn⟩ := hx'_gen
        use n
        apply QuotientGroup.eq.mpr
        simp only [hi', dite_false, Subgroup.mem_subgroupOf, Subgroup.mem_map]
        have hn' := QuotientGroup.eq.mp hn
        simp only [Subgroup.mem_subgroupOf] at hn'
        have hsucc_eq : N_series j.succ =
            N_series ⟨i.succ.val - m, by have := i.isLt; rw [h_succ_val]; omega⟩ := by
          apply congrArg N_series; simp only [Fin.ext_iff, hj_succ_val, h_succ_val]; omega
        refine ⟨(gen.val ^ n)⁻¹ * x', ?_, ?_⟩
        · rw [← hsucc_eq]
          exact hn'
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
            SubgroupClass.coe_zpow]
          congr 1

/-- Finitely generated abelian groups are polycyclic -/
theorem isPolycyclic_of_fg_commGroup (H : Type*) [CommGroup H] [FG H] :
    IsPolycyclic H := by
  -- Abelian groups are nilpotent
  haveI : IsNilpotent H := CommGroup.isNilpotent
  -- Use well-founded induction on the number of generators
  -- Get a finite generating set
  obtain ⟨S, hSclosed, hSfin⟩ := Group.fg_iff.mp ‹FG H›
  -- Induction on cardinality of generating set
  induction hcard : Nat.card S using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    by_cases hempty : S.Nonempty
    swap
    · -- Empty generating set means trivial group
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty] at hSclosed
      simp only [Subgroup.closure_empty] at hSclosed
      have hsub : (⊤ : Subgroup H) = ⊥ := hSclosed.symm
      haveI : Subsingleton H := by
        constructor
        intro a b
        have ha : a ∈ (⊤ : Subgroup H) := Subgroup.mem_top a
        have hb : b ∈ (⊤ : Subgroup H) := Subgroup.mem_top b
        rw [hsub] at ha hb
        simp only [Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      exact isPolycyclic_of_subsingleton H
    · -- Nonempty case: use extension by cyclic quotient
      obtain ⟨g, hgS⟩ := hempty
      let C := Subgroup.zpowers g
      haveI : C.Normal := Subgroup.normal_of_comm C
      -- C is cyclic, hence polycyclic
      haveI : IsCyclic C := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨⟨g, Subgroup.mem_zpowers g⟩, by
        ext x; simp only [Subgroup.mem_zpowers_iff, Subgroup.mem_top, iff_true]
        obtain ⟨n, hn⟩ := x.2
        exact ⟨n, Subtype.ext hn⟩⟩
      have hC_cyclic : IsPolycyclic C := isPolycyclic_of_isCyclic C
      -- H/C is a finitely generated abelian group
      letI : CommGroup (H ⧸ C) := QuotientGroup.Quotient.commGroup C
      -- H/C is generated by the images of S \ {g}
      have hQ_fg : FG (H ⧸ C) := QuotientGroup.fg C
      -- Apply induction: H/C has generating set of size < n
      have hQ_poly : IsPolycyclic (H ⧸ C) := by
        -- The quotient H/C is generated by images of S
        -- But QuotientGroup.mk g = 1, so effectively one fewer generator needed
        -- We need to show there exists a smaller generating set
        have hgen : Subgroup.closure ((QuotientGroup.mk : H → H ⧸ C) '' S) = ⊤ := by
          have : (Subgroup.closure S).map (QuotientGroup.mk' C) =
              Subgroup.closure (QuotientGroup.mk '' S) :=
            MonoidHom.map_closure (QuotientGroup.mk' C) S
          rw [← this, hSclosed, Subgroup.map_top_of_surjective]
          exact QuotientGroup.mk'_surjective C
        -- The image of g is 1
        have hg_one : (QuotientGroup.mk g : H ⧸ C) = 1 := by
          have hmem : g ∈ C := Subgroup.mem_zpowers g
          change (g : H ⧸ C) = (1 : H ⧸ C)
          rw [QuotientGroup.eq_one_iff]
          exact hmem
        -- So the closure of S' = (S \ {g}).image generates H/C
        -- where we remove g from S since its image is 1
        -- Closure of set with 1 equals closure without 1
        have hgen' : Subgroup.closure ((QuotientGroup.mk : H → H ⧸ C) '' (S \ {g})) = ⊤ := by
          have : (QuotientGroup.mk : H → H ⧸ C) '' S = QuotientGroup.mk '' (S \ {g}) ∪ {1} := by
            ext x
            constructor
            · intro ⟨s, hsS, hsx⟩
              by_cases heq : s = g
              · right; rw [← hsx, heq, hg_one]; exact Set.mem_singleton 1
              · left; exact ⟨s, ⟨hsS, heq⟩, hsx⟩
            · intro hx
              rcases hx with ⟨s, ⟨hsS, _⟩, hsx⟩ | hx1
              · exact ⟨s, hsS, hsx⟩
              · rw [Set.mem_singleton_iff] at hx1
                rw [hx1, ← hg_one]
                exact ⟨g, hgS, rfl⟩
          rw [this, Subgroup.closure_union, Subgroup.closure_singleton_one,
              sup_bot_eq] at hgen
          exact hgen
        -- Now Nat.card (QuotientGroup.mk '' (S \ {g})) ≤ Nat.card (S \ {g}) < Nat.card S = n
        -- if n > 0 (which it is since S is nonempty)
        have hfin_diff : (S \ ({g} : Set H)).Finite := hSfin.subset Set.diff_subset
        have hcard_lt : Nat.card ↑(S \ ({g} : Set H)) < n := by
          rw [← hcard, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          have : (S \ {g}).ncard + 1 = S.ncard := Set.ncard_diff_singleton_add_one hgS hSfin
          omega
        -- Apply IH
        let S' := (QuotientGroup.mk : H → H ⧸ C) '' (S \ {g})
        have hS'fin : S'.Finite := Set.Finite.image _ hfin_diff
        have hS'card_le : Nat.card ↑S' ≤ Nat.card ↑(S \ ({g} : Set H)) :=
          Nat.card_image_le hfin_diff
        have hS'card_lt : Nat.card ↑S' < n := Nat.lt_of_le_of_lt hS'card_le hcard_lt
        exact ih (Nat.card ↑S') hS'card_lt (H ⧸ C) CommGroup.isNilpotent S' hgen' hS'fin rfl
      -- Now use extension theorem: C polycyclic, H/C polycyclic => H polycyclic
      exact isPolycyclic_of_extension C hC_cyclic hQ_poly

/-- The commutator of two f.g. subgroups is f.g.

BLOCKING LEMMA: This is a fundamental result in combinatorial group theory.
Proof strategy: If S generates H and T generates K, then ⁅H, K⁆ is generated
by {⁅s, t⁆ | s ∈ S±¹, t ∈ T±¹}. The proof requires Hall-Witt commutator identities.
This should be added to Mathlib.GroupTheory.Commutator.Finite.
-/
lemma commutator_fg {G : Type*} [Group G] (H K : Subgroup G) [FG H] [FG K] :
    FG (⁅H, K⁆ : Subgroup G) := by
  sorry

/-- The lower central series of a f.g. group has f.g. terms -/
theorem lowerCentralSeries_fg (H : Type*) [Group H] [FG H] (n : ℕ) :
    FG (lowerCentralSeries H n) := by
  -- The lower central series terms are generated by iterated commutators
  -- of the original generators. For a f.g. group, this is a finite set.
  induction n with
  | zero =>
    -- lowerCentralSeries H 0 = ⊤
    simp only [lowerCentralSeries_zero]
    -- ⊤ is f.g. as a subgroup because H is f.g. as a group
    -- ↥⊤ ≃* H, so FG ↥⊤ follows from FG H
    have : Function.Surjective (Subgroup.topEquiv (G := H)).symm.toMonoidHom :=
      fun x => ⟨Subgroup.topEquiv x, by simp [Subgroup.topEquiv]⟩
    exact Group.fg_of_surjective this
  | succ n ih =>
    -- lowerCentralSeries H (n+1) = ⁅lowerCentralSeries H n, ⊤⁆
    rw [lowerCentralSeries_succ]
    -- By IH, lowerCentralSeries H n is f.g.
    haveI : FG (lowerCentralSeries H n) := ih
    -- ⊤ is f.g. (isomorphic to H)
    haveI : FG (⊤ : Subgroup H) := by
      have : Function.Surjective (Subgroup.topEquiv (G := H)).symm.toMonoidHom :=
        fun x => ⟨Subgroup.topEquiv x, by simp [Subgroup.topEquiv]⟩
      exact Group.fg_of_surjective this
    -- Apply commutator_fg
    exact commutator_fg (lowerCentralSeries H n) ⊤

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
  -- Induction on nilpotency class
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp (inferInstance : IsNilpotent H)
  induction n generalizing H with
  | zero =>
    -- Class 0 means H = 1 (trivial group)
    have htrivial : lowerCentralSeries H 0 = ⊥ := hn
    rw [lowerCentralSeries_zero] at htrivial
    have : ∀ x : H, x = 1 := fun x => Subgroup.mem_bot.mp (htrivial ▸ Subgroup.mem_top x)
    haveI : Subsingleton H := ⟨fun x y => by rw [this x, this y]⟩
    exact isPolycyclic_of_subsingleton H
  | succ n ih =>
    -- L_n is the last nontrivial term, L_{n+1} = 1
    -- H/L_n has nilpotency class n, so polycyclic by IH
    -- L_n is f.g. abelian (central in H), hence polycyclic
    -- H is extension of polycyclic by polycyclic, hence polycyclic
    set L := lowerCentralSeries H n with hL_def
    haveI hL_normal : L.Normal := inferInstance
    -- L_{n+1} = 1
    have hLn1_bot : lowerCentralSeries H (n + 1) = ⊥ := hn
    -- L_n is central in H (since [H, L_n] = L_{n+1} = 1)
    have hL_central : L ≤ Subgroup.center H := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      -- ⁅x, g⁆ ∈ ⁅L_n, ⊤⁆ = L_{n+1} = ⊥
      have hcomm : ⁅x, g⁆ ∈ lowerCentralSeries H (n + 1) := by
        rw [lowerCentralSeries_succ]
        exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g)
      rw [hLn1_bot, Subgroup.mem_bot] at hcomm
      simp only [commutatorElement_def] at hcomm
      -- hcomm : x * g * x⁻¹ * g⁻¹ = 1
      -- This means x * g * x⁻¹ = g, i.e., x * g = g * x
      have h1 : x * g * x⁻¹ = g := by
        calc x * g * x⁻¹ = x * g * x⁻¹ * g⁻¹ * g := by group
          _ = 1 * g := by rw [hcomm]
          _ = g := by group
      calc g * x = x * g * x⁻¹ * x := by rw [h1]
        _ = x * g := by group
    -- L_n is f.g. (subgroup of f.g. group with trivial quotient by central subgroup)
    have hL_fg : FG L := by
      -- L is generated by commutators, which form a finite set when H is f.g.
      -- More precisely: L_n is f.g. because H is f.g. and nilpotent
      -- This follows from the standard fact about lower central series
      obtain ⟨S, hS⟩ := Group.fg_iff.mp ‹FG H›
      -- The lower central series terms are generated by iterated commutators
      -- of the original generators, which is a finite set
      exact lowerCentralSeries_fg H n
    -- L_n is abelian (central implies abelian)
    letI : CommGroup L := {
      L.toGroup with
      mul_comm := fun ⟨a, ha⟩ ⟨b, hb⟩ => by
        have ha' : a ∈ Subgroup.center H := hL_central ha
        rw [Subgroup.mem_center_iff] at ha'
        exact Subtype.ext (ha' b).symm
    }
    -- L_n is polycyclic (f.g. abelian)
    letI : FG L := hL_fg
    have hL_poly : IsPolycyclic L := isPolycyclic_of_fg_commGroup L
    -- H/L_n is f.g.
    haveI : FG (H ⧸ L) := QuotientGroup.fg L
    -- H/L_n is polycyclic by IH
    have hQ_poly : IsPolycyclic (H ⧸ L) := ih (H ⧸ L) (by
      -- Need to show lowerCentralSeries (H ⧸ L) n = ⊥
      -- We have L = lowerCentralSeries H n and lowerCentralSeries H (n+1) = ⊥
      --
      -- Key fact: lowerCentralSeries is antitone, so lowerCentralSeries H (n+1) = ⊥
      -- implies lowerCentralSeries H k = ⊥ for all k > n.
      --
      -- We'll show that comap (QuotientGroup.mk' L) (lowerCentralSeries (H ⧸ L) n) ≤
      -- lowerCentralSeries H (n+n) = ⊥, which gives the result.
      --
      -- This requires a lemma relating LCS of quotients to LCS of the original group.
      -- The needed lemma: for normal N ≤ lowerCentralSeries G m,
      --   comap (mk' N) (lowerCentralSeries (G/N) k) ≤ lowerCentralSeries G (m+k)
      -- This lemma doesn't exist in Mathlib and is non-trivial to prove.
      sorry)
    -- H is extension of L by H/L, both polycyclic
    exact isPolycyclic_of_extension L hL_poly hQ_poly

/-
TODO: This theorem requires fittingSubgroup infrastructure which doesn't exist in Mathlib yet.
It should be proven once we have the Fitting subgroup defined.

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
  use fittingSubgroup H
  refine ⟨fittingSubgroup_normal H, fittingSubgroup_isNilpotent H hP, ?_⟩
  -- F(H) has finite index because H/F(H) has Hirsch length 0
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  have hQ_poly : IsPolycyclic (H ⧸ fittingSubgroup H) := isPolycyclic_quotient hP _
  rw [← hirschLength_zero_iff_finite hQ_poly]
  exact quotient_fittingSubgroup_hirschLength_zero hP
-/

-- Polycyclic groups are virtually nilpotent (follows from the Fitting subgroup theorem)
-- BLOCKING: Requires Fitting subgroup infrastructure (not in Mathlib)
theorem isVirtuallyNilpotent_of_isPolycyclic (H : Type*) [Group H] (hP : IsPolycyclic H) :
    IsVirtuallyNilpotent H := by
  -- BLOCKED: The proof requires the Fitting subgroup theorem, which states that
  -- every polycyclic group has a finite-index normal nilpotent subgroup.
  -- The Fitting subgroup F(G) is the join of all normal nilpotent subgroups,
  -- and in polycyclic groups it has finite index.
  --
  -- This requires defining `fittingSubgroup`, proving it's normal and nilpotent,
  -- and showing it has finite index in polycyclic groups.
  -- See the commented-out theorem above for the intended structure.
  sorry

/-- Finite solvable groups are polycyclic.

Every finite solvable group has a composition series with cyclic (prime order) factors.

Note: A finite group is polycyclic iff it is solvable. The alternating group A_5 is
finite but not polycyclic (it's not solvable).

TODO: This proof requires either:
1. The structure theorem for finite abelian groups (available in Mathlib), OR
2. A careful double induction on cardinality with proper handling of quotients, OR
3. Using composition series machinery

The difficulty is showing K/K' is polycyclic when K/K' is a finite abelian group.
While finite abelian groups are polycyclic (via structure theorem), connecting this
with the quotient structure requires care with typeclass instances.

References:
- Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.4.11
-/
theorem isPolycyclic_of_finite (K : Type*) [Group K] [Finite K] [IsSolvable K] :
    IsPolycyclic K := by
  -- Proof strategy: Induct on the derived series K ⊇ K' ⊇ K'' ⊇ ... ⊇ {1}.
  -- At each step, K/K' is a finite abelian group, hence polycyclic by the structure theorem.
  -- Use isPolycyclic_of_extension to build up.
  --
  -- The key steps are:
  -- 1. Show finite abelian groups are polycyclic (use FiniteAbelian.Basic structure theorem)
  -- 2. Induct on derived length using solvability
  -- 3. Apply extension theorem at each step
  --
  -- This requires careful handling of typeclass instances for the quotient K/K'
  -- and connecting the structure theorem to the polycyclic definition.
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
    haveI inst_cyclic : IsCyclic (↥(H ⊓ G' i.castSucc) ⧸
        (G' i.succ).subgroupOf (H ⊓ G' i.castSucc)) :=
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
      have hm_eq : QuotientGroup.mk (s := (G' i.succ).subgroupOf (H ⊓ G' i.castSucc))
          (gen'_rep ^ m) =
                   QuotientGroup.mk (s := (G' i.succ).subgroupOf (H ⊓ G' i.castSucc)) k' := by
        -- We have hm : gen' ^ m = ↑k' and hgen'_rep : ↑gen'_rep = gen'
        -- So gen'^m = (↑gen'_rep)^m = ↑(gen'_rep^m)
        rw [QuotientGroup.mk_zpow, hgen'_rep, hm]
      have hm' := QuotientGroup.eq.mp hm_eq
      rw [Subgroup.mem_subgroupOf] at hm'
      constructor
      · -- Show membership in H
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow,
          Subgroup.subtype_apply]
        exact H.mul_mem (H.inv_mem (H.zpow_mem hgen'_rep_H m)) hk_mem.1
      · -- Show membership in G' i.succ
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow,
          Subgroup.subtype_apply]
        convert hm' using 1

-- Variant: If H <= K as subgroups of G and K is polycyclic, then H is polycyclic
-- Note: This requires transferring IsPolycyclic across the isomorphism H ≃* H.subgroupOf K
theorem isPolycyclic_of_le {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (hK : IsPolycyclic K) : IsPolycyclic H := by
  -- H.subgroupOf K is a subgroup of K, so it's polycyclic
  have h1 : IsPolycyclic (H.subgroupOf K) := isPolycyclic_subgroup hK _
  -- H.subgroupOf K ≃* H via subgroupOfEquivOfLe
  exact isPolycyclic_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK) h1




/-- Quotients of polycyclic groups by normal subgroups are polycyclic.

If G has a polycyclic series G = G_0 > G_1 > ... > G_n = 1 and N is normal in G,
then G/N has the polycyclic series (G_i N)/N which form a polycyclic series for G/N.
-/
lemma isPolycyclic_quotient {G : Type*} [Group G] (hG : IsPolycyclic G)
    (N : Subgroup G) [N.Normal] : IsPolycyclic (G ⧸ N) := by
  -- Get the polycyclic series for G
  obtain ⟨n, G_series, hTop, hBot, hLe, hNorm, hCyc⟩ := hG
  -- The series for G/N is (G_i · N)/N, which equals (map mk' G_i) where mk' : G → G/N
  -- But we need to be more careful: the series should be (G_i ⊔ N)/N
  -- Actually, by the correspondence theorem, subgroups of G/N containing N/N
  -- correspond to subgroups of G containing N.
  -- So we use: (G_series i ⊔ N) / N as our series for G/N
  --
  -- This requires showing the quotient map of the join equals the expected quotient.
  -- The key lemma is the correspondence theorem for quotient groups.
  sorry

theorem isPolycyclic_of_finiteIndex_polycyclic (H : Subgroup G) [H.FiniteIndex]
    (hH : IsPolycyclic H) : IsPolycyclic G := by
  -- H.normalCore is normal in G with finite index
  let N := H.normalCore
  have hN_normal : N.Normal := Subgroup.normalCore_normal H
  have hN_le_H : N ≤ H := Subgroup.normalCore_le H
  have hN_finiteIndex : N.FiniteIndex := inferInstance  -- finiteIndex_normalCore is an instance
  -- N is polycyclic (subgroup of polycyclic H)
  have hN_poly : IsPolycyclic N := isPolycyclic_of_le hN_le_H hH
  -- G/N is finite
  haveI : Finite (G ⧸ N) := inferInstance  -- finite_quotient_of_finiteIndex is an instance
  -- But wait - we can't use isPolycyclic_quotient on H because we need G to be polycyclic!
  -- Different approach: H/N has finite index in G/N (since [G:H] = [G/N : H/N])
  -- and H/N is polycyclic (as quotient of polycyclic H).
  -- So if we had a lemma that finite extensions of polycyclic groups are polycyclic...
  -- but that's what we're trying to prove!
  --
  -- CIRCULAR DEPENDENCY: Need either isPolycyclic_quotient for general groups OR
  -- some other approach.  Actually, the cleanest approach is:
  -- Since H is polycyclic and solvable, and [G:H] finite, we can show G is solvable.
  -- Then since G/N is finite and solvable, it's polycyclic by isPolycyclic_of_finite.
  sorry  -- Blocked on: polycyclic => solvable, and isPolycyclic_of_finite


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
  -- Induction on the length of the polycyclic series
  obtain ⟨n, G_series, hG_top, hG_bot, hG_le, hG_norm, hG_cyc⟩ := hG
  induction n generalizing G H with
  | zero =>
    -- G has series of length 0: G_0 = ⊤, G_0 = ⊥, so G is trivial
    have htriv : (⊤ : Subgroup G) = ⊥ := by
      have : G_series 0 = G_series ⟨0, Nat.lt_succ_self 0⟩ := by simp
      rw [← hG_top, ← hG_bot, this]
    haveI : Subsingleton (Subgroup G) := subsingleton_of_bot_eq_top htriv.symm
    haveI : Subsingleton G := Subgroup.subsingleton_iff.mp inferInstance
    haveI : Subsingleton H := inferInstance
    exact ⟨∅, by simp [ Subgroup.eq_bot_of_subsingleton]⟩
  | succ n ih =>
    -- Inductive step: G has a polycyclic series of length n+1
    -- Strategy: Show H/(H ∩ G_1) is f.g., and H ∩ G_1 is f.g. by IH
    --
    -- Let G_1 = G_series 1 (the second term in the series)
    -- Then G/G_1 is cyclic (since G_0/G_1 is cyclic and G_0 = ⊤)
    --
    -- H/(H ∩ G_1) embeds into G/G_1 via the natural map
    -- Since G/G_1 is cyclic, H/(H ∩ G_1) is cyclic (subgroup of cyclic is cyclic)
    -- So H/(H ∩ G_1) is f.g.
    --
    -- G_1 has a polycyclic series of length n (the restriction of G_series from index 1 onward)
    -- By IH, H ∩ G_1 is f.g.
    --
    -- By the extension lemma (if N ⊴ H, N f.g., and H/N f.g., then H f.g.),
    -- H is f.g.
    --
    -- The difficulty is that H ∩ G_1 might not be normal in H, so we can't directly
    -- apply an extension lemma. Instead, we need to use that if a group has f.g. quotient
    -- by a f.g. subgroup, it's f.g.
    --
    -- This requires Schreier's lemma or a careful direct construction.
    sorry  -- Need: extension-by-fg lemma or Schreier-type argument

/-! ### Main Theorem -/

/-- **Mal'cev's Theorem** (forward direction): For finitely generated groups,
virtually nilpotent implies polycyclic.

This uses: f.g. nilpotent groups are polycyclic, and finite extensions
of polycyclic groups are polycyclic.

Note: The reverse direction (polycyclic => virtually nilpotent) requires the Fitting
subgroup theorem, which needs additional infrastructure not yet in Mathlib.
-/
theorem polycyclic_of_isVirtuallyNilpotent [FG G] (hVN : IsVirtuallyNilpotent G) :
    IsPolycyclic G := by
  obtain ⟨H, hNil, hFin⟩ := hVN
  haveI : H.FiniteIndex := hFin
  haveI : IsNilpotent H := hNil
  -- H is f.g. (finite-index subgroup of f.g. group)
  haveI : FG H := Subgroup.fg_of_index_ne_zero H
  -- H is nilpotent and f.g., hence polycyclic
  have hHP : IsPolycyclic H := isPolycyclic_of_isNilpotent_fg H
  -- G is a finite extension of H, hence polycyclic
  exact isPolycyclic_of_finiteIndex_polycyclic H hHP


theorem isVirtuallyNilpotent_iff_polycyclic [FG G] : IsVirtuallyNilpotent G ↔ IsPolycyclic G := by
  constructor
  · exact polycyclic_of_isVirtuallyNilpotent
  · exact isVirtuallyNilpotent_of_isPolycyclic G


end

end Group
