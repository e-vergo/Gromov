-- Helper: Subgroups of polycyclic groups are polycyclic.
-- The subnormal series for G restricts to a subnormal series for H.
private theorem isPolycyclic_subgroup {G : Type*} [Group G] (hG : IsPolycyclic G)
    (H : Subgroup G) : IsPolycyclic H := by
  -- Proof strategy: Take the polycyclic series for G and intersect each term with H.
  -- This gives a series for H with cyclic quotients.

  -- Step 1: Unpack the polycyclic series for G
  obtain ⟨n, Gs, hG0, hGn, hChain, hNormal, hCyclic⟩ := hG

  -- Step 2: Define the series for H by intersection
  let Hs : Fin (n + 1) → Subgroup H := fun i =>
    (H ⊓ Gs i).subgroupOf H

  -- Step 3: Show H₀ = ⊤
  have hH0 : Hs 0 = ⊤ := by
    ext x
    simp only [Hs, Subgroup.mem_top, iff_true]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · exact x.prop
    · rw [hG0]
      exact Subgroup.mem_top x.val

  -- Step 4: Show Hₙ = ⊥
  have hHn : Hs ⟨n, Nat.lt_succ_self n⟩ = ⊥ := by
    ext x
    simp only [Subgroup.mem_bot]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro ⟨_, h2⟩
      rw [hGn] at h2
      simp only [Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    · intro hx
      rw [hx]
      constructor
      · exact Subgroup.one_mem H
      · rw [hGn]
        exact Subgroup.one_mem ⊥

  -- Step 5: Show the chain property
  have hHChain : ∀ i : Fin n, Hs i.succ ≤ Hs i.castSucc := by
    intro i
    intro x hx
    simp only [Hs, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx ⊢
    exact ⟨hx.1, hChain i hx.2⟩

  -- Step 6: Show normality
  have hHNormal : ∀ i : Fin n, ((Hs i.succ).subgroupOf (Hs i.castSucc)).Normal := by
    intro i
    -- This requires showing that conjugation preserves the subgroup
    -- The key insight: if x ∈ Hᵢ and y ∈ Hᵢ₊₁, then xyx⁻¹ ∈ Hᵢ₊₁
    -- This follows from the normality in G
    sorry

  -- Step 7: Show quotients are cyclic
  have hHCyclic : ∀ i : Fin n, (h1 : Hs i.succ ≤ Hs i.castSucc) →
      (h2 : ((Hs i.succ).subgroupOf (Hs i.castSucc)).Normal) →
      QuotientIsCyclic (Hs i.succ) (Hs i.castSucc) h1 h2 := by
    intro i h1 h2
    -- The quotient Hᵢ/Hᵢ₊₁ = (H ∩ Gᵢ)/(H ∩ Gᵢ₊₁) embeds into Gᵢ/Gᵢ₊₁
    -- Since subgroups of cyclic groups are cyclic, the quotient is cyclic
    --
    -- Missing infrastructure:
    -- 1. A map (H ∩ Gᵢ)/(H ∩ Gᵢ₊₁) → Gᵢ/Gᵢ₊₁ induced by the inclusion
    -- 2. Proof that this map is injective
    -- 3. Use Subgroup.isCyclic to conclude the domain is cyclic
    --
    -- This is the Second Isomorphism Theorem applied to the lattice of subgroups.
    sorry

  -- Combine all parts
  exact ⟨n, Hs, hH0, hHn, hHChain, hHNormal, hHCyclic⟩
