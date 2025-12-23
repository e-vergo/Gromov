module

public import Gromov.Proofs.Growth.Polynomial
public import Gromov.Proofs.Growth.Abelian
public import Gromov.Proofs.VirtuallyNilpotent.Core
public import Gromov.Proofs.VirtuallyNilpotent.NilpotencyClass
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Schreier
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
namespace Gromov.NilpotentGrowth

public section

open Gromov Gromov.PolynomialGrowth Group Subgroup

variable {G : Type*} [Group G]

/-! ### Auxiliary lemmas -/

/-- A finitely generated abelian group has polynomial growth. -/
theorem commGroup_hasPolynomialGrowth' {G : Type*} [CommGroup G] [Group.FG G] :
    HasPolynomialGrowth G :=
  PolynomialGrowth.commGroup_hasPolynomialGrowth

/-- For a nontrivial nilpotent group, the center is nontrivial. -/
theorem nontrivial_center_of_isNilpotent [IsNilpotent G] [Nontrivial G] :
    Nontrivial (center G) :=
  Group.nontrivial_center_of_nilpotent_nontrivial

/-- Subgroups of finitely generated abelian groups are finitely generated.
This uses that ℤ is a Noetherian ring. -/
lemma Subgroup.fg_of_fg_comm {A : Type*} [CommGroup A] [Group.FG A] (B : Subgroup A) :
    Subgroup.FG B := by
  rw [Subgroup.fg_iff_add_fg]
  haveI : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr
    (AddGroup.fg_iff_addMonoid_fg.mpr (Monoid.fg_iff_add_fg.mp inferInstance))
  haveI : IsNoetherianRing ℤ := inferInstance
  haveI : IsNoetherian ℤ (Additive A) := inferInstance
  let B' : Submodule ℤ (Additive A) := (Subgroup.toAddSubgroup B).toIntSubmodule
  have hB'fg : B'.FG := IsNoetherian.noetherian B'
  rwa [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup] at hB'fg

/-- For nilpotent groups of class n, the (n-1)th term of the lower central series
is contained in the center. -/
lemma lowerCentralSeries_le_center [IsNilpotent G] :
    lowerCentralSeries G (nilpotencyClass G - 1) ≤ center G := by
  by_cases h : nilpotencyClass G = 0
  · have : Subsingleton G := nilpotencyClass_zero_iff_subsingleton.mp h
    intro x hx
    rw [mem_center_iff]
    intro g
    have : g = 1 := Subsingleton.eq_one g
    have : x = 1 := Subsingleton.eq_one x
    simp [*]
  · have hn : nilpotencyClass G - 1 + 1 = nilpotencyClass G := by omega
    intro x hx
    rw [mem_center_iff]
    intro g
    have hcomm : ⁅x, g⁆ ∈ lowerCentralSeries G (nilpotencyClass G) := by
      rw [← hn, lowerCentralSeries_succ]
      apply subset_closure
      exact ⟨x, hx, g, mem_top g, rfl⟩
    have hbot : lowerCentralSeries G (nilpotencyClass G) = ⊥ :=
      lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr le_rfl
    rw [hbot, mem_bot, commutatorElement_def] at hcomm
    have h1 : x * g * x⁻¹ = g := by
      calc x * g * x⁻¹ = x * g * x⁻¹ * g⁻¹ * g := by group
        _ = 1 * g := by rw [hcomm]
        _ = g := by rw [one_mul]
    calc g * x = x * (x⁻¹ * g * x) := by group
      _ = x * (x⁻¹ * (x * g * x⁻¹) * x) := by rw [h1]
      _ = x * g := by group

/-- For abelian groups, center = top, so center is f.g. if G is f.g. -/
lemma center_fg_of_fg_abelian [Group.FG G] [IsNilpotent G] (h : nilpotencyClass G ≤ 1) :
    Group.FG (center G) := by
  have hcenter_top : center G = ⊤ := by
    rw [← upperCentralSeries_one]
    exact upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr h
  have equiv : (center G) ≃* G := MulEquiv.ofBijective (center G).subtype
    ⟨Subtype.val_injective, fun g => ⟨⟨g, by rw [hcenter_top]; trivial⟩, rfl⟩⟩
  rw [Group.fg_iff_monoid_fg]
  exact Monoid.fg_of_surjective equiv.symm.toMonoidHom equiv.symm.surjective


private theorem malcev_subgroup_fg_of_fg_nilpotent (H : Subgroup G) [Group.FG G] [IsNilpotent G] :
    Group.FG H := by
  -- The proof uses that f.g. nilpotent groups are polycyclic,
  -- and subgroups of polycyclic groups are f.g.
  -- Since we have isPolycyclic_of_isNilpotent_fg in Polycyclic.lean,
  -- we apply that and then use the subgroup property.
  --
  -- Step 1: G is polycyclic (f.g. nilpotent implies polycyclic)
  have hPoly : IsPolycyclic G := isPolycyclic_of_isNilpotent_fg G
  -- Step 2: Subgroups of polycyclic groups are f.g.
  exact Subgroup.fg_of_polycyclic hPoly H

/-- The center of a finitely generated nilpotent group is finitely generated.
This is a special case of Mal'cev's theorem above, since center G is a subgroup of G.
-/
theorem center_fg_of_fg_nilpotent [Group.FG G] [IsNilpotent G] : Group.FG (center G) := by
  obtain ⟨n, hn⟩ : ∃ n, nilpotencyClass G = n := ⟨_, rfl⟩
  induction n generalizing G with
  | zero =>
    haveI : Subsingleton G := nilpotencyClass_zero_iff_subsingleton.mp hn
    haveI : Finite (center G) := Finite.of_subsingleton
    rw [Group.fg_iff_monoid_fg]; exact Monoid.fg_of_finite
  | succ n ih =>
    by_cases hclass1 : n = 0
    · subst hclass1
      exact center_fg_of_fg_abelian (by omega)
    by_cases hsub : Subsingleton G
    · haveI := hsub
      haveI : Finite (center G) := Finite.of_subsingleton
      rw [Group.fg_iff_monoid_fg]; exact Monoid.fg_of_finite
    rw [not_subsingleton_iff_nontrivial] at hsub
    haveI : Nontrivial G := hsub
    have hQ_class : nilpotencyClass (G ⧸ center G) = n := by
      rw [nilpotencyClass_quotient_center, hn]; omega
    haveI : Group.FG (G ⧸ center G) := QuotientGroup.fg (center G)
    have hcenterQ_fg : Group.FG (center (G ⧸ center G)) := ih hQ_class
    exact malcev_subgroup_fg_of_fg_nilpotent (center G)

/-- For an element of the subgroup closure, there exists a list of elements (each in s or with
inverse in s) whose product equals the element. This is the group version of
`Submonoid.exists_list_of_mem_closure`. -/
theorem Subgroup.exists_list_of_mem_closure' {G : Type*} [Group G] {s : Set G} {x : G}
    (hx : x ∈ Subgroup.closure s) :
    ∃ l : List G, (∀ y ∈ l, y ∈ s ∨ y⁻¹ ∈ s) ∧ l.prod = x := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨[], by simp, by simp⟩
  | mul_left x hx y _ ih =>
    obtain ⟨l, hl_mem, hl_prod⟩ := ih
    refine ⟨x :: l, ?_, by simp [hl_prod]⟩
    intro z hz
    simp only [List.mem_cons] at hz
    cases hz with
    | inl h => left; rw [h]; exact hx
    | inr h => exact hl_mem z h
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨l, hl_mem, hl_prod⟩ := ih
    refine ⟨x⁻¹ :: l, ?_, by simp [hl_prod]⟩
    intro z hz
    simp only [List.mem_cons] at hz
    cases hz with
    | inl h => right; simp [h, hx]
    | inr h => exact hl_mem z h

private lemma cayleyBall_subtype_val_ncard {G : Type*} [Group G] (H : Subgroup G)
    (S : Set H) (n : ℕ) :
    (CayleyBall (Subtype.val '' S) n).ncard = (CayleyBall S n).ncard := by
  -- The embedding val : H → G is an injective group homomorphism
  -- It maps CayleyBall S n bijectively onto CayleyBall (val '' S) n
  have hinj : Function.Injective (Subtype.val : H → G) := Subtype.val_injective
  -- Define the map from CayleyBall S n to CayleyBall (val '' S) n
  have hmap : ∀ h ∈ CayleyBall S n, (h : G) ∈ CayleyBall (Subtype.val '' S) n := by
    intro h ⟨l, hl_len, hl_mem, hl_prod⟩
    use l.map Subtype.val
    refine ⟨by simp [hl_len], ?_, ?_⟩
    · intro s hs
      simp only [List.mem_map] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      cases hl_mem t ht with
      | inl htS => left; exact ⟨t, htS, rfl⟩
      | inr htinvS => right; simp only [← Subgroup.coe_inv]; exact ⟨t⁻¹, htinvS, rfl⟩
    · rw [← Subgroup.val_list_prod, hl_prod]
  -- Define the inverse map
  have hmap_inv : ∀ g ∈ CayleyBall (Subtype.val '' S) n, ∃ h : H,
  (h : G) = g ∧ h ∈ CayleyBall S n := by
    intro g ⟨l, hl_len, hl_mem, hl_prod⟩
    -- Each element of l is in val '' S or has inverse in val '' S
    -- Since val is injective, we can lift each element back to H
    have hl_in_H : ∀ s ∈ l, s ∈ H := by
      intro s hs
      cases hl_mem s hs with
      | inl hsS =>
        obtain ⟨t, _, rfl⟩ := hsS
        exact t.2
      | inr hsinvS =>
        obtain ⟨t, _, ht_eq⟩ := hsinvS
        -- ht_eq : ↑t = s⁻¹, so s = (↑t)⁻¹
        have : s = (t : G)⁻¹ := by rw [← inv_eq_iff_eq_inv]; exact ht_eq.symm
        rw [this]
        exact Subgroup.inv_mem H t.2
    -- Lift the list to H
    let l' : List H := l.pmap (fun s hs => ⟨s, hl_in_H s hs⟩) (fun s hs => hs)
    have hl'_val : l'.map Subtype.val = l := by
      simp only [l', List.map_pmap, List.pmap_eq_map]
      simp only [List.map_id']
    use l'.prod
    constructor
    · rw [Subgroup.val_list_prod, hl'_val, hl_prod]
    · refine ⟨l', ?_, ?_, rfl⟩
      · simp only [l']
        rw [List.length_pmap]
        exact hl_len
      · intro t ht
        simp only [l', List.mem_pmap] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        cases hl_mem s hs with
        | inl hsS =>
          left
          obtain ⟨t', ht'S, ht'_eq⟩ := hsS
          have : (⟨s, hl_in_H s hs⟩ : H) = t' := Subtype.ext ht'_eq.symm
          rw [this]
          exact ht'S
        | inr hsinvS =>
          right
          obtain ⟨t', ht'S, ht'_eq⟩ := hsinvS
          -- ht'_eq : ↑t' = s⁻¹, so s = (↑t')⁻¹
          have hs_eq : s = (t' : G)⁻¹ := by rw [← inv_eq_iff_eq_inv]; exact ht'_eq.symm
          have h_elem_eq : (⟨s, hl_in_H s hs⟩ : H) = t'⁻¹ := by
            apply Subtype.ext
            simp only [Subgroup.coe_inv, hs_eq]
          rw [h_elem_eq, inv_inv]
          exact ht'S
  -- Now show the bijection preserves ncard using Set.ncard_congr
  symm
  apply Set.ncard_congr (fun (h : H) (_ : h ∈ CayleyBall S n) => (h : G))
  · intro h hh; exact hmap h hh
  · intro h1 h2 _ _ heq; exact Subtype.ext heq
  · intro g hg
    obtain ⟨h, hval, hball⟩ := hmap_inv g hg
    exact ⟨h, hball, hval⟩

private theorem cayleyBall_lift_bound_for_center_quotient {G : Type*} [Group G]
    (S_Q : Set (G ⧸ center G)) (S_Z : Set (center G)) (m : ℕ) :
    let lift := fun (q : G ⧸ center G) => Quotient.out q
    let S_Q_lifts : Set G := lift '' S_Q
    let S_Z_embed : Set G := Subtype.val '' S_Z
    (CayleyBall S_Q m).ncard * (CayleyBall S_Z m).ncard ≤
      (CayleyBall S_Q_lifts m).ncard * (CayleyBall S_Z_embed m).ncard := by
  intro lift S_Q_lifts S_Z_embed
  -- The center embedding preserves CayleyBall cardinality (bijection via val)
  have hZ_eq : (CayleyBall S_Z_embed m).ncard = (CayleyBall S_Z m).ncard :=
    cayleyBall_subtype_val_ncard (center G) S_Z m
  rw [hZ_eq]
  gcongr
  -- Need: |CayleyBall S_Q m| ≤ |CayleyBall S_Q_lifts m|
  -- The quotient map mk : G → G/Z(G) gives a surjection on CayleyBalls.
  -- We use that mk '' (CayleyBall S_Q_lifts m) = CayleyBall S_Q m and that
  -- ncard of the image is ≤ ncard of the source.
  -- First show the image equality
  have hmk_image : QuotientGroup.mk '' CayleyBall S_Q_lifts m = CayleyBall S_Q m := by
    -- Show mk '' CayleyBall S_Q_lifts m = CayleyBall S_Q m
    ext q
    constructor
    · rintro ⟨g, hg, rfl⟩
      -- g ∈ CayleyBall S_Q_lifts m, need to show mk g ∈ CayleyBall S_Q m
      obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hg
      refine ⟨l.map QuotientGroup.mk, ?_, ?_, ?_⟩
      · simp [hl_len]
      · intro s hs
        simp only [List.mem_map] at hs
        obtain ⟨g', hg', rfl⟩ := hs
        have := hl_mem g' hg'
        rcases this with hS | hSinv
        · left
          -- hS : g' ∈ S_Q_lifts = lift '' S_Q
          -- goal : ↑g' ∈ S_Q where ↑ : G → G ⧸ center G
          obtain ⟨qg, hqg, hqg_eq⟩ := hS
          -- hqg_eq : lift qg = g', so mk g' = mk (lift qg) = qg
          rw [← hqg_eq]
          -- Now need: ↑(lift qg) ∈ S_Q, i.e., QuotientGroup.mk (Quotient.out qg) ∈ S_Q
          -- Since QuotientGroup.mk (Quotient.out qg) = qg
          have h_eq : (QuotientGroup.mk (qg.out) : G ⧸ center G) = qg := QuotientGroup.out_eq' qg
          rw [h_eq]
          exact hqg
        · right
          -- hSinv : g'⁻¹ ∈ S_Q_lifts = lift '' S_Q
          -- goal : (↑g')⁻¹ ∈ S_Q
          obtain ⟨qg, hqg, hqg_eq⟩ := hSinv
          -- hqg_eq : lift qg = g'⁻¹, so (↑g')⁻¹ = ↑(g'⁻¹) = ↑(lift qg) = qg
          have h_goal : (QuotientGroup.mk g' : G ⧸ center G)⁻¹ = qg := by
            have h1 : (QuotientGroup.mk g' : G ⧸ center G)⁻¹ =
                QuotientGroup.mk (g'⁻¹) := (QuotientGroup.mk_inv (center G) g').symm
            rw [h1]
            -- Now need: ↑(g'⁻¹) = qg. We have g'⁻¹ = lift qg = qg.out
            have h2 : g'⁻¹ = qg.out := hqg_eq.symm
            rw [h2]
            exact QuotientGroup.out_eq' qg
          rw [h_goal]
          exact hqg
      · -- Use that (map QuotientGroup.mk l).prod = QuotientGroup.mk l.prod
        -- First convert QuotientGroup.mk to QuotientGroup.mk' which is the same
        have hmap_eq : l.map QuotientGroup.mk = l.map (QuotientGroup.mk' (center G)) := by
          congr 1
        rw [hmap_eq, List.prod_hom l (QuotientGroup.mk' (center G)), hl_prod]
        exact QuotientGroup.mk'_apply (center G) g
    · intro hq
      -- q ∈ CayleyBall S_Q m, need g such that mk g = q and g ∈ CayleyBall S_Q_lifts m
      obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hq
      -- l is a list in G⧸Z with l.prod = q
      -- We need a smart lift that handles both cases:
      -- - When q' ∈ S_Q: use lift q' = Quotient.out q'
      -- - When q'⁻¹ ∈ S_Q: use (lift (q'⁻¹))⁻¹ = (Quotient.out (q'⁻¹))⁻¹
      -- The key is that mk of either choice equals q'.
      open Classical in
      let smartLift : G ⧸ center G → G := fun q' =>
        if q' ∈ S_Q then lift q' else (lift (q'⁻¹))⁻¹
      have hsmartLift_mk : ∀ q' : G ⧸ center G, QuotientGroup.mk (smartLift q') = q' := by
        intro q'
        simp only [smartLift]
        split_ifs with h
        · exact Quotient.out_eq' q'
        · simp only [lift]
          rw [QuotientGroup.mk_inv, QuotientGroup.out_eq', inv_inv]
      use (l.map smartLift).prod
      constructor
      · refine ⟨l.map smartLift, ?_, ?_, rfl⟩
        · simp [hl_len]
        · intro s hs
          simp only [List.mem_map] at hs
          obtain ⟨q', hq', rfl⟩ := hs
          have := hl_mem q' hq'
          -- smartLift q' = if q' ∈ S_Q then lift q' else (lift (q'⁻¹))⁻¹
          rcases this with hS | hSinv
          · -- q' ∈ S_Q, so smartLift q' = lift q'
            left
            have heq : smartLift q' = lift q' := if_pos hS
            rw [heq]
            exact ⟨q', hS, rfl⟩
          · -- q'⁻¹ ∈ S_Q, need smartLift q' ∈ S_Q_lifts ∨ (smartLift q')⁻¹ ∈ S_Q_lifts
            by_cases hq'S : q' ∈ S_Q
            · -- q' ∈ S_Q, so smartLift q' = lift q'
              left
              have heq : smartLift q' = lift q' := if_pos hq'S
              rw [heq]
              exact ⟨q', hq'S, rfl⟩
            · -- q' ∉ S_Q, so smartLift q' = (lift (q'⁻¹))⁻¹
              right
              have heq : smartLift q' = (lift (q'⁻¹))⁻¹ := if_neg hq'S
              rw [heq, inv_inv]
              exact ⟨q'⁻¹, hSinv, rfl⟩
      · -- mk (l.map smartLift).prod = q
        rw [← hl_prod]
        have hprod_hom := (List.prod_hom (l.map smartLift) (QuotientGroup.mk' (center G))).symm
        simp only [QuotientGroup.mk'_apply] at hprod_hom
        rw [hprod_hom, List.map_map]
        -- QuotientGroup.mk' N = QuotientGroup.mk for the same quotient
        have hfun_eq : (QuotientGroup.mk' (center G)) ∘ smartLift = id := by
          ext q'
          simp only [Function.comp_apply, QuotientGroup.mk'_apply, id_eq]
          exact hsmartLift_mk q'
        rw [hfun_eq, List.map_id]
  have hinj : Set.InjOn (QuotientGroup.mk (s := center G)) (CayleyBall S_Q_lifts m) := by

    sorry
  rw [← hmk_image, Set.ncard_image_of_injOn hinj]

/-! ### Central extension growth bound -/

/-- If elements satisfying ¬P are central, then list products can be reordered as
    (filter P).prod * (filter ¬P).prod. -/
lemma List.prod_filter_central {G : Type*} [Group G] (P : G → Bool) (l : List G)
    (hcentral : ∀ x ∈ l, P x = false → ∀ y : G, x * y = y * x) :
    l.prod = (l.filter P).prod * (l.filter (!P ·)).prod := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ih' := ih (fun x hx => hcentral x (List.mem_cons_of_mem a hx))
    simp only [List.filter_cons, List.prod_cons]
    cases hPa : P a
    case false =>
      -- a doesn't satisfy P, so a is central (P a = false)
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, List.prod_cons]
      have ha_central : ∀ y : G, a * y = y * a :=
        hcentral a (List.mem_cons_self) hPa
      have ha_comm : a * (as.filter P).prod = (as.filter P).prod * a :=
        ha_central (as.filter P).prod
      calc a * as.prod = a * ((as.filter P).prod * (as.filter (!P ·)).prod) := by rw [ih']
        _ = (a * (as.filter P).prod) * (as.filter (!P ·)).prod := by group
        _ = ((as.filter P).prod * a) * (as.filter (!P ·)).prod := by rw [ha_comm]
        _ = (as.filter P).prod * (a * (as.filter (!P ·)).prod) := by group
    case true =>
      -- a satisfies P (P a = true)
      simp only [ite_true, Bool.not_true, List.prod_cons, Bool.false_eq_true, ite_false]
      rw [ih', mul_assoc]

/-- Key lemma: for a central extension, growth of G is bounded by product of growths.
If N <= Z(G), then Ball_G(n) embeds into Ball_{lifts}(n) x Ball_{N}(n). -/
lemma cayleyBall_central_extension_bound {N : Subgroup G} [N.Normal] (hN_central : N ≤ center G)
    (S_Q : Set (G ⧸ N)) (S_N : Set N) (n : ℕ) :
    let lift : G ⧸ N → G := Quotient.out
    let S_Q_lifts : Set G := lift '' S_Q
    let S_N_embed : Set G := Subtype.val '' S_N
    let S_G : Set G := S_Q_lifts ∪ S_N_embed
    CayleyBall S_G n ⊆
      (fun p : G × G => p.1 * p.2) '' (CayleyBall S_Q_lifts n ×ˢ CayleyBall S_N_embed n) := by
  intro lift S_Q_lifts S_N_embed S_G g hg
  simp only [CayleyBall, Set.mem_setOf_eq] at hg
  obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hg
  -- Partition l into Q-lifts and N-elements
  -- Since N is central, we can reorder: g = (Q-part) * (N-part)
  classical
  -- Define the partition predicate: element comes from Q_lifts (or its inverse does)
  let isQ : G → Bool := fun x => decide (x ∈ S_Q_lifts ∨ x⁻¹ ∈ S_Q_lifts)
  let l_Q := l.filter isQ
  let l_N := l.filter (!isQ ·)
  -- Key: elements from S_N_embed are in N, hence central
  have hN_central' : ∀ x ∈ S_N_embed, ∀ y : G, x * y = y * x := by
    intro x hx y
    obtain ⟨m, _, rfl⟩ := hx
    have hm_center := hN_central m.2
    exact (Subgroup.mem_center_iff.mp hm_center y).symm
  -- Helper: if x⁻¹ commutes with everything, so does x
  have inv_comm_of_comm : ∀ x : G, (∀ y : G, x⁻¹ * y = y * x⁻¹) → ∀ y : G, x * y = y * x := by
    intro x hx y
    have := hx y⁻¹
    calc x * y = (x⁻¹)⁻¹ * y := by simp
      _ = (y⁻¹ * x⁻¹)⁻¹ := by group
      _ = (x⁻¹ * y⁻¹)⁻¹ := by rw [this]
      _ = y * (x⁻¹)⁻¹ := by group
      _ = y * x := by simp
  -- Elements with isQ = false (i.e., not in Q_lifts) are central when they come from S_G
  have hcentral : ∀ x ∈ l, isQ x = false → ∀ y : G, x * y = y * x := by
    intro x hx hnotQ y
    have hx_mem := hl_mem x hx
    have hnotQ' : ¬(x ∈ S_Q_lifts ∨ x⁻¹ ∈ S_Q_lifts) := by
      simp only [isQ, decide_eq_false_iff_not] at hnotQ
      exact hnotQ
    -- x ∈ S_G and not in Q_lifts, so x ∈ S_N_embed or x⁻¹ ∈ S_N_embed
    rcases hx_mem with (hxS | hxinvS)
    · -- x ∈ S_G = S_Q_lifts ∪ S_N_embed
      rcases hxS with (hxQ | hxN)
      · exact absurd (Or.inl hxQ) hnotQ'
      · exact hN_central' x hxN y
    · -- x⁻¹ ∈ S_G
      rcases hxinvS with (hxinvQ | hxinvN)
      · exact absurd (Or.inr hxinvQ) hnotQ'
      · -- x⁻¹ ∈ S_N_embed, so x⁻¹ is central, hence x is too
        exact inv_comm_of_comm x (hN_central' x⁻¹ hxinvN) y
  -- By centrality, l.prod = l_Q.prod * l_N.prod
  have hprod_eq : l.prod = l_Q.prod * l_N.prod :=
    List.prod_filter_central isQ l hcentral
  -- Now show l_Q.prod ∈ CayleyBall S_Q_lifts n and l_N.prod ∈ CayleyBall S_N_embed n
  have hl_Q_cayley : l_Q.prod ∈ CayleyBall S_Q_lifts n := by
    refine ⟨l_Q, ?_, ?_, rfl⟩
    · calc l_Q.length ≤ l.length := List.length_filter_le _ _
        _ ≤ n := hl_len
    · intro s hs
      rw [List.mem_filter] at hs
      simp only [isQ, decide_eq_true_eq] at hs
      rcases hs.2 with (hsQ | hsinvQ)
      · left; exact hsQ
      · right; exact hsinvQ
  have hl_N_cayley : l_N.prod ∈ CayleyBall S_N_embed n := by
    refine ⟨l_N, ?_, ?_, rfl⟩
    · calc l_N.length ≤ l.length := List.length_filter_le _ _
        _ ≤ n := hl_len
    · intro s hs
      rw [List.mem_filter] at hs
      obtain ⟨hs_l, hs_notQ⟩ := hs
      -- hs_notQ : (!isQ s) = true means isQ s = false, i.e., ¬(s ∈ S_Q_lifts ∨ s⁻¹ ∈ S_Q_lifts)
      have hs_notQ' : ¬(s ∈ S_Q_lifts ∨ s⁻¹ ∈ S_Q_lifts) := by
        simp only [isQ, Bool.not_eq_true', decide_eq_false_iff_not] at hs_notQ
        exact hs_notQ
      have hsMem := hl_mem s hs_l
      -- s ∈ S_G and not Q, so s or s⁻¹ ∈ S_N_embed
      push_neg at hs_notQ'
      rcases hsMem with (hsS | hsinvS)
      · rcases hsS with (hsQ | hsN)
        · exact absurd hsQ hs_notQ'.1
        · left; exact hsN
      · rcases hsinvS with (hsinvQ | hsinvN)
        · exact absurd hsinvQ hs_notQ'.2
        · right; exact hsinvN
  -- Conclude
  rw [← hl_prod, hprod_eq]
  exact ⟨(l_Q.prod, l_N.prod), ⟨hl_Q_cayley, hl_N_cayley⟩, rfl⟩

/-- ncard of a product set. -/
lemma Set.ncard_prod_le {α β : Type*} (s : Set α) (t : Set β) :
    (s ×ˢ t).ncard ≤ s.ncard * t.ncard := by
  by_cases hs : s.Finite
  · by_cases ht : t.Finite
    · rw [Set.ncard_prod]
    · simp only [Set.Infinite.ncard (Set.not_finite.mp ht), mul_zero]
      by_cases hs_empty : s = ∅
      · simp [hs_empty]
      · have hinf : (s ×ˢ t).Infinite := by
          intro hfin
          have : t.Finite := by
            have ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hs_empty
            have : t ⊆ (Prod.snd '' (s ×ˢ t)) := fun b hb => ⟨(a, b), ⟨ha, hb⟩, rfl⟩
            exact Set.Finite.subset (hfin.image _) this
          exact Set.not_finite.mp ht this
        simp [Set.Infinite.ncard hinf]
  · simp only [Set.Infinite.ncard (Set.not_finite.mp hs), zero_mul]
    by_cases ht_empty : t = ∅
    · simp [ht_empty]
    · have hinf : (s ×ˢ t).Infinite := by
        intro hfin
        have : s.Finite := by
          have ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.mpr ht_empty
          have : s ⊆ (Prod.fst '' (s ×ˢ t)) := fun a ha => ⟨(a, b), ⟨ha, hb⟩, rfl⟩
          exact Set.Finite.subset (hfin.image _) this
        exact Set.not_finite.mp hs this
      simp [Set.Infinite.ncard hinf]

/-- ncard of image of product under multiplication. -/
lemma ncard_image_mul_le {G : Type*} [Group G] (s t : Set G) :
    ((fun p : G × G => p.1 * p.2) '' (s ×ˢ t)).ncard ≤ s.ncard * t.ncard := by
  by_cases hs : s.Finite
  · by_cases ht : t.Finite
    · have hfin : (s ×ˢ t).Finite := by
        have h : s ×ˢ t ⊆ ↑(hs.toFinset ×ˢ ht.toFinset) := by
          intro ⟨a, b⟩ ⟨ha, hb⟩
          simp only [Finset.coe_product, Set.mem_prod]
          exact ⟨hs.mem_toFinset.mpr ha, ht.mem_toFinset.mpr hb⟩
        exact Set.Finite.subset (Finset.finite_toSet _) h
      calc ((fun p : G × G => p.1 * p.2) '' (s ×ˢ t)).ncard
          ≤ (s ×ˢ t).ncard := Set.ncard_image_le hfin
        _ = s.ncard * t.ncard := Set.ncard_prod
    · -- t is infinite
      by_cases hs_empty : s = ∅
      · simp [hs_empty]
      · -- s nonempty, t infinite => image is infinite
        have ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hs_empty
        have hinj : Set.InjOn (fun b => a * b) t := fun x _ y _ hxy => by simpa using hxy
        have hprod_sub : (fun b => a * b) '' t ⊆ (fun p : G × G => p.1 * p.2) '' (s ×ˢ t) := by
          intro x ⟨b, hb, heq⟩
          exact ⟨(a, b), ⟨ha, hb⟩, heq⟩
        have himg_inf : ((fun p : G × G => p.1 * p.2) '' (s ×ˢ t)).Infinite :=
          Set.Infinite.mono hprod_sub (Set.Infinite.image hinj (Set.not_finite.mp ht))
        rw [Set.Infinite.ncard himg_inf, Set.Infinite.ncard (Set.not_finite.mp ht), mul_zero]
  · -- s is infinite
    by_cases ht_empty : t = ∅
    · simp [ht_empty]
    · have ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.mpr ht_empty
      have hinj : Set.InjOn (fun a => a * b) s := fun x _ y _ hxy => by simpa using hxy
      have hprod_sub : (fun a => a * b) '' s ⊆ (fun p : G × G => p.1 * p.2) '' (s ×ˢ t) := by
        intro x ⟨a, ha, heq⟩
        exact ⟨(a, b), ⟨ha, hb⟩, heq⟩
      have himg_inf : ((fun p : G × G => p.1 * p.2) '' (s ×ˢ t)).Infinite :=
        Set.Infinite.mono hprod_sub (Set.Infinite.image hinj (Set.not_finite.mp hs))
      rw [Set.Infinite.ncard himg_inf, Set.Infinite.ncard (Set.not_finite.mp hs), zero_mul]

/-! ### Main induction -/

/-- Nilpotent groups of class at most n have polynomial growth. -/
theorem hasPolynomialGrowth_of_nilpotencyClass_le :
    ∀ (n : ℕ) (G : Type*) [Group G] [IsNilpotent G] [Group.FG G],
    nilpotencyClass G ≤ n → HasPolynomialGrowth G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hclass
    have hsub : Subsingleton G := nilpotencyClass_zero_iff_subsingleton.mp (Nat.le_zero.mp hclass)
    haveI : Finite G := @Finite.of_subsingleton G hsub
    exact finite_hasPolynomialGrowth
  | succ n ih =>
    intro G _ hnil hfg hclass
    by_cases hsub : Subsingleton G
    · haveI : Finite G := Finite.of_subsingleton
      exact finite_hasPolynomialGrowth
    · rw [not_subsingleton_iff_nontrivial] at hsub
      haveI : Nontrivial G := hsub
      haveI hZ_nontriv : Nontrivial (center G) := nontrivial_center_of_isNilpotent
      -- center G is f.g.
      haveI : Group.FG (center G) := center_fg_of_fg_nilpotent
      -- center G is abelian, has polynomial growth
      have hZ_growth : HasPolynomialGrowth (center G) := commGroup_hasPolynomialGrowth'
      -- G/center G has class <= n
      haveI : Group.FG (G ⧸ center G) := QuotientGroup.fg (center G)
      have hQ_class : nilpotencyClass (G ⧸ center G) ≤ n := by
        have h1 : nilpotencyClass (G ⧸ center G) = nilpotencyClass G - 1 :=
          nilpotencyClass_quotient_center
        have h2 : nilpotencyClass G ≥ 1 := by
          by_contra hlt; push_neg at hlt
          have hsing : Subsingleton G :=
            nilpotencyClass_zero_iff_subsingleton.mp (Nat.lt_one_iff.mp hlt)
          exact not_nontrivial_iff_subsingleton.mpr hsing ‹Nontrivial G›
        omega
      have hQ_growth : HasPolynomialGrowth (G ⧸ center G) := ih (G ⧸ center G) hQ_class
      -- Get generating sets and bounds
      obtain ⟨S_Z, hS_Z_fin, hS_Z_gen, C_Z, d_Z, hC_Z_pos, hbound_Z⟩ := hZ_growth
      obtain ⟨S_Q, hS_Q_fin, hS_Q_gen, C_Q, d_Q, hC_Q_pos, hbound_Q⟩ := hQ_growth
      -- Construct generating set for G
      let lift : G ⧸ center G → G := Quotient.out
      let S_Q_lifts : Set G := lift '' S_Q
      let S_Z_embed : Set G := Subtype.val '' S_Z
      let S_G : Set G := S_Q_lifts ∪ S_Z_embed
      have hS_Q_lifts_fin : S_Q_lifts.Finite := hS_Q_fin.image lift
      have hS_Z_embed_fin : S_Z_embed.Finite := hS_Z_fin.image Subtype.val
      have hS_G_fin : S_G.Finite := hS_Q_lifts_fin.union hS_Z_embed_fin
      -- S_G generates G: Any g ∈ G can be written as g = (lift q) * z where q = mk g
      -- and z ∈ center G. The lift q is in closure of S_Q_lifts (by lifting the
      -- closure property from quotient), and z is in closure of S_Z_embed.
      have hS_G_gen : Subgroup.closure S_G = ⊤ := by
        rw [eq_top_iff]
        intro g _
        -- Decompose g = (lift q) * z where q = mk g and z ∈ center G
        let q : G ⧸ center G := QuotientGroup.mk g
        let r := Quotient.out q
        have hr_eq : QuotientGroup.mk r = q := Quotient.out_eq q
        -- Then r⁻¹ * g is in the center
        have hz_mem : r⁻¹ * g ∈ center G := by
          rw [← QuotientGroup.eq]
          simp only [hr_eq]
          -- Goal: q = ↑g, but q is defined as ↑g
          rfl
        let z : center G := ⟨r⁻¹ * g, hz_mem⟩
        have hg_eq : g = r * z := by simp [z]
        rw [hg_eq]
        -- Show r ∈ closure S_G and z ∈ closure S_G
        apply Subgroup.mul_mem
        · -- r ∈ closure S_Q_lifts ⊆ closure S_G
          -- Since q ∈ closure S_Q and q = mk r, we can lift this
          have hq_gen : q ∈ Subgroup.closure S_Q := by rw [hS_Q_gen]; trivial
          -- Use that closure S_Q maps to closure (mk '' S_Q_lifts) under mk
          have hmap : Subgroup.closure S_Q ≤
              (Subgroup.closure S_Q_lifts).map (QuotientGroup.mk' (center G)) := by
            rw [MonoidHom.map_closure]
            have heq : QuotientGroup.mk' (center G) '' S_Q_lifts = S_Q := by
              ext x
              simp only [Set.mem_image, QuotientGroup.mk'_apply]
              constructor
              · intro ⟨y, hy, hyx⟩
                obtain ⟨q', hq', rfl⟩ := hy
                rw [← hyx]
                convert hq'
                -- lift q' = Quotient.out q', and ⟦Quotient.out q'⟧ = q'
                change ↑(Quotient.out q') = q'
                exact Quotient.out_eq q'
              · intro hx
                use Quotient.out x, ⟨x, hx, rfl⟩
                exact Quotient.out_eq x
            rw [heq]
          -- Since q ∈ closure S_Q and closure S_Q ≤ map mk' (closure S_Q_lifts),
          -- we have q ∈ map mk' (closure S_Q_lifts)
          have hq_in_map : q ∈ (Subgroup.closure S_Q_lifts).map (QuotientGroup.mk' (center G)) :=
            hmap hq_gen
          -- So there exists r' ∈ closure S_Q_lifts with mk' r' = q
          obtain ⟨r', hr'_mem, hr'_eq⟩ := hq_in_map
          -- But mk' r = q as well (by hr_eq)
          have hr_mk : QuotientGroup.mk' (center G) r = q := hr_eq
          -- So mk' r = mk' r', which means r⁻¹ * r' ∈ center G
          have hdiff : r⁻¹ * r' ∈ center G := by
            have heq : QuotientGroup.mk' (center G) r = QuotientGroup.mk' (center G) r' := by
              rw [hr_mk, hr'_eq]
            simp only [QuotientGroup.mk'_apply] at heq
            rwa [QuotientGroup.eq] at heq
          -- Therefore r = r' * (r⁻¹ * r')⁻¹ where r' ∈ closure S_Q_lifts
          -- and (r⁻¹ * r')⁻¹ ∈ center G
          have hr_eq' : r = r' * (r⁻¹ * r')⁻¹ := by group
          rw [hr_eq']
          apply Subgroup.mul_mem
          · exact Subgroup.closure_mono Set.subset_union_left hr'_mem
          · have hinv_center : (r⁻¹ * r')⁻¹ ∈ center G := Subgroup.inv_mem (center G) hdiff
            let z_inv : center G := ⟨(r⁻¹ * r')⁻¹, hinv_center⟩
            have hz_in_closure : z_inv ∈ Subgroup.closure S_Z := by
              rw [hS_Z_gen]; trivial
            have hmap_z : (Subgroup.closure S_Z).map (center G).subtype =
                Subgroup.closure S_Z_embed := MonoidHom.map_closure (center G).subtype S_Z
            have hz_inv_in_embed : ↑z_inv ∈ Subgroup.closure S_Z_embed := by
              rw [← hmap_z]; exact ⟨z_inv, hz_in_closure, rfl⟩
            exact Subgroup.closure_mono Set.subset_union_right hz_inv_in_embed
        · -- z ∈ closure S_Z_embed ⊆ closure S_G
          have hz_gen : z ∈ Subgroup.closure S_Z := by rw [hS_Z_gen]; trivial
          have hmap : (Subgroup.closure S_Z).map (center G).subtype = Subgroup.closure S_Z_embed :=
            MonoidHom.map_closure (center G).subtype S_Z
          have : (z : G) ∈ Subgroup.closure S_Z_embed := by
            rw [← hmap]; exact ⟨z, hz_gen, rfl⟩
          exact Subgroup.closure_mono Set.subset_union_right this
      -- Combine the growth bounds using the central extension bound
      use S_G, hS_G_fin, hS_G_gen
      use C_Z * C_Q * 2 ^ (d_Z + d_Q + 1), d_Z + d_Q
      constructor
      · positivity
      · intro m hm_pos
        -- Apply the central extension bound
        have hbound : CayleyBall S_G m ⊆
            (fun p : G × G => p.1 * p.2) '' (CayleyBall S_Q_lifts m ×ˢ CayleyBall S_Z_embed m) :=
          cayleyBall_central_extension_bound (le_refl (center G)) S_Q S_Z m
        -- Bound the size
        have h_prod_finite :
            ((fun p : G × G => p.1 * p.2) '' (CayleyBall S_Q_lifts m ×ˢ
            CayleyBall S_Z_embed m)).Finite := by
          apply Set.Finite.image
          apply Set.Finite.prod
          · exact cayleyBall_finite hS_Q_lifts_fin m
          · exact cayleyBall_finite hS_Z_embed_fin m
        have h_ncard_bound : (CayleyBall S_G m).ncard ≤
            ((fun p : G × G => p.1 * p.2) ''
            (CayleyBall S_Q_lifts m ×ˢ CayleyBall S_Z_embed m)).ncard :=
          Set.ncard_le_ncard hbound h_prod_finite
        have h_prod_bound :
            ((fun p : G × G => p.1 * p.2) ''
            (CayleyBall S_Q_lifts m ×ˢ CayleyBall S_Z_embed m)).ncard ≤
            (CayleyBall S_Q_lifts m).ncard * (CayleyBall S_Z_embed m).ncard :=
          ncard_image_mul_le _ _
        calc (GrowthFunction S_G m : ℝ)
            = (CayleyBall S_G m).ncard := rfl
          _ ≤ ((fun p : G × G => p.1 * p.2) ''
              (CayleyBall S_Q_lifts m ×ˢ CayleyBall S_Z_embed m)).ncard := by
              exact Nat.cast_le.mpr h_ncard_bound
          _ ≤ (CayleyBall S_Q_lifts m).ncard * (CayleyBall S_Z_embed m).ncard := by
              have h :
                  (((CayleyBall S_Q_lifts m).ncard * (CayleyBall S_Z_embed m).ncard :
                  ℕ) : ℝ) =
                  (CayleyBall S_Q_lifts m).ncard * (CayleyBall S_Z_embed m).ncard :=
                Nat.cast_mul _ _
              rw [← h]
              exact Nat.cast_le.mpr h_prod_bound
          _ ≤ (GrowthFunction S_Q m) * (GrowthFunction S_Z m) := by
              -- Use the Cayley ball lifting lemma for central quotients
              have h_lift_bound := @cayleyBall_lift_bound_for_center_quotient G _ S_Q S_Z m
              simp only [GrowthFunction]
              sorry
          _ ≤ (C_Q * ↑m ^ d_Q) * (C_Z * ↑m ^ d_Z) := by
              apply mul_le_mul
              · exact hbound_Q m hm_pos
              · exact hbound_Z m hm_pos
              · exact Nat.cast_nonneg _
              · positivity
          _ = C_Q * C_Z * (↑m ^ d_Q * ↑m ^ d_Z) := by ring
          _ = C_Q * C_Z * ↑m ^ (d_Q + d_Z) := by rw [← pow_add]
          _ ≤ C_Z * C_Q * 2 ^ (d_Z + d_Q + 1) * ↑m ^ (d_Z + d_Q) := by
              have hcomm : d_Q + d_Z = d_Z + d_Q := Nat.add_comm d_Q d_Z
              rw [hcomm]
              have h_const : C_Q * C_Z ≤ C_Z * C_Q * 2 ^ (d_Z + d_Q + 1) := by
                have : C_Q * C_Z = C_Z * C_Q := mul_comm C_Q C_Z
                rw [this]
                calc C_Z * C_Q = C_Z * C_Q * 1 := by ring
                  _ ≤ C_Z * C_Q * 2 ^ (d_Z + d_Q + 1) := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    have : (1 : ℝ) ≤ 2 ^ (d_Z + d_Q + 1) := by
                      have h : (2 : ℝ) ^ 0 ≤ 2 ^ (d_Z + d_Q + 1) := by
                        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
                        omega
                      simpa using h
                    exact this
              exact mul_le_mul_of_nonneg_right h_const (by positivity)

/-! ### Main theorems -/

/-- **Wolf's Theorem**: Every finitely generated nilpotent group has polynomial growth. -/
theorem IsNilpotent.hasPolynomialGrowth [IsNilpotent G] [Group.FG G] :
    HasPolynomialGrowth G :=
  hasPolynomialGrowth_of_nilpotencyClass_le (nilpotencyClass G) G le_rfl

private theorem schreier_rewrite_bound {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    (S_H : Set H) (hS_H_gen : Subgroup.closure S_H = ⊤)
    (reps : Finset G) (hreps : ∀ q : G ⧸ H, Quotient.out q ∈ reps)
    (S_G : Set G) (hS_G : S_G = Subtype.val '' S_H ∪ ↑reps)
    (k : ℕ) (h : H) (hh_ball : (h : G) ∈ CayleyBall S_G k) :
    h ∈ CayleyBall S_H ((H.index + 1) * k) := by
  -- Extract the word representation from the Cayley ball membership
  obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hh_ball
  -- This is the quantitative Schreier rewriting bound
  -- Proof strategy:
  -- 1. Process word l letter by letter, tracking which coset H*r we're in
  -- 2. At each step i, if we multiply by s ∈ S_G:
  --    - If s ∈ val(S_H), we get a Schreier generator contribution
  --    - If s ∈ reps, we cross to a different coset
  -- 3. Each crossing and return adds O(index) generators from S_H
  -- 4. Total: k steps × (index+1) generators
  -- This requires implementing the Schreier rewriting algorithm
  -- See Mathlib's Subgroup.closure_mul_image_eq for the qualitative version
  sorry

/-- **Schreier bound**: For a finite-index subgroup H ≤ G with index m, if an element h ∈ H
can be written as a word of length k using generators S_G = val(S_H) ∪ reps (where S_H
generates H and reps are coset representatives), then h can be written as a word of
length ≤ (m+1)*k using generators S_H.

This follows immediately from the Schreier rewrite bound. -/
theorem schreier_word_length_bound {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    (S_H : Set H) (hS_H_gen : Subgroup.closure S_H = ⊤)
    (reps : Finset G) (hreps : ∀ q : G ⧸ H, Quotient.out q ∈ reps)
    (S_G : Set G) (hS_G : S_G = Subtype.val '' S_H ∪ ↑reps)
    (k : ℕ) (h : G) (hh_mem : h ∈ H) (hh_ball : h ∈ CayleyBall S_G k) :
    ⟨h, hh_mem⟩ ∈ CayleyBall S_H ((H.index + 1) * k) := by
  -- Apply the Schreier rewrite bound axiom
  exact schreier_rewrite_bound S_H hS_H_gen reps hreps S_G hS_G k ⟨h, hh_mem⟩ hh_ball

/-- Every finitely generated virtually nilpotent group has polynomial growth. -/
theorem IsVirtuallyNilpotent.hasPolynomialGrowth [Group.FG G]
    (hG : Group.IsVirtuallyNilpotent G) : HasPolynomialGrowth G := by
  obtain ⟨H, hH_nil, hH_fin⟩ := hG
  haveI : H.FiniteIndex := hH_fin
  haveI : IsNilpotent H := hH_nil
  haveI : Group.FG H := Subgroup.fg_of_index_ne_zero H
  have hH_growth : HasPolynomialGrowth H := IsNilpotent.hasPolynomialGrowth
  obtain ⟨S_H, hS_H_fin, hS_H_gen, C_H, d_H, hC_H_pos, hbound_H⟩ := hH_growth
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  let m := H.index
  have hm_pos : 0 < m := Nat.pos_of_ne_zero H.index_ne_zero_of_finite
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  haveI : DecidableEq G := Classical.decEq G
  let reps : Finset G := Finset.univ.image (fun q : G ⧸ H => Quotient.out q)
  let S_G : Set G := (Subtype.val '' S_H) ∪ (reps : Set G)
  have hS_G_fin : S_G.Finite := (hS_H_fin.image _).union (Finset.finite_toSet reps)
  have hS_G_gen : Subgroup.closure S_G = ⊤ := by
    rw [eq_top_iff]; intro g _
    let q : G ⧸ H := QuotientGroup.mk g
    have hr_rep : Quotient.out q ∈ reps := Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
    have hrg : (Quotient.out q)⁻¹ * g ∈ H := by rw [← QuotientGroup.eq]; exact Quotient.out_eq q
    let h : H := ⟨(Quotient.out q)⁻¹ * g, hrg⟩
    have hg_eq : g = (Quotient.out q) * h := by simp [h]
    rw [hg_eq]
    apply Subgroup.mul_mem
    · apply Subgroup.subset_closure; right; exact hr_rep
    · have hh_mem : h ∈ Subgroup.closure S_H := by rw [hS_H_gen]; trivial
      have hmap : (Subgroup.closure S_H).map H.subtype = Subgroup.closure (Subtype.val '' S_H) :=
        MonoidHom.map_closure H.subtype S_H
      have h_embed : ∀ s : H, s ∈ Subgroup.closure S_H → (s : G) ∈ Subgroup.closure S_G := by
        intro s hs
        have hs' : (s : G) ∈ (Subgroup.closure S_H).map H.subtype := ⟨s, hs, rfl⟩
        rw [hmap] at hs'
        exact Subgroup.closure_mono Set.subset_union_left hs'
      exact h_embed h hh_mem
  use S_G, hS_G_fin, hS_G_gen
  have hball_sub : ∀ k, (Subtype.val '' CayleyBall S_H k) ⊆ CayleyBall S_G k := by
    intro k h ⟨x, hx, hxeq⟩
    simp only [CayleyBall, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hx
    use l.map Subtype.val
    refine ⟨by simp [hl_len], ?_, by simp [← hxeq, ← hl_prod]⟩
    intro s hs
    simp only [List.mem_map] at hs
    obtain ⟨t, ht, hteq⟩ := hs
    have := hl_mem t ht
    cases this with
    | inl ht_mem => left; left; exact ⟨t, ht_mem, hteq⟩
    | inr htinv_mem => right; left; exact ⟨t⁻¹, htinv_mem, by simp [← hteq]⟩
  use (m : ℝ) * C_H * (2 * (m + 1)) ^ d_H, d_H
  refine ⟨by positivity, ?_⟩
  intro n hn
  -- First, bound reps: each coset rep has word length at most 1 in S_G (since reps ⊆ S_G)
  have hreps_in_ball : ∀ r ∈ reps, r ∈ CayleyBall S_G 1 := by
    intro r hr
    exact ⟨[r], by simp, fun s hs => by
      simp only [List.mem_singleton] at hs; left; right; rw [hs]; exact hr, by simp⟩
  -- Main bound: use coset decomposition and subgroup embedding
  calc (GrowthFunction S_G n : ℝ)
      ≤ (m : ℝ) * (GrowthFunction S_H ((m + 1) * (n + 1)) : ℝ) := by
        have h1 : (CayleyBall S_G n).ncard ≤ m * (CayleyBall S_H ((m + 1) * (n + 1))).ncard := by
          -- Step 1: Coset decomposition
          have hdecomp : ∀ g : G, ∃ r ∈ reps, ∃ h : H, g = r * h := by
            intro g
            let q := QuotientGroup.mk (s := H) g
            use Quotient.out q
            constructor
            · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
            · have hh : (Quotient.out q)⁻¹ * g ∈ H := by
                rw [← QuotientGroup.eq]; exact Quotient.out_eq q
              exact ⟨⟨_, hh⟩, by simp⟩
          -- Step 2: For g ∈ B_G(n), the h part satisfies h ∈ H ∩ r⁻¹ * B_G(n) ⊆ H ∩ B_G(n+1)
          have hball_decomp : ∀ g ∈ CayleyBall S_G n,
              ∃ r ∈ reps, ∃ h : H, g = r * h ∧ (h : G) ∈ CayleyBall S_G (n + 1) := by
            intro g hg
            obtain ⟨r, hr_reps, h, hg_eq⟩ := hdecomp g
            use r, hr_reps, h, hg_eq
            have hr_ball := hreps_in_ball r hr_reps
            have hr_inv := cayleyBall_inv S_G hr_ball
            have hh_in_ball_1n : r⁻¹ * g ∈ CayleyBall S_G (1 + n) := cayleyBall_mul S_G hr_inv hg
            have hh_eq : (h : G) = r⁻¹ * g := by simp [hg_eq]
            rw [hh_eq]
            exact cayleyBall_monotone S_G (by omega) hh_in_ball_1n
          have h_word_bound : ∀ k, (H : Set G) ∩ CayleyBall S_G k ⊆
              Subtype.val '' CayleyBall S_H ((m + 1) * k) := by
            intro k h ⟨hh_mem, hh_ball⟩
            let x : H := ⟨h, hh_mem⟩
            refine ⟨x, ?_, rfl⟩
            -- Need: x ∈ CayleyBall S_H ((m+1)*k)
            -- This follows from the Schreier bound applied to the S_G-word from hh_ball
            have hreps : ∀ q : G ⧸ H, Quotient.out q ∈ reps :=
              fun q => Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
            exact schreier_word_length_bound S_H hS_H_gen reps hreps S_G rfl k h hh_mem hh_ball
          have hφ : CayleyBall S_G n ⊆
              (fun (p : G × G) => p.1 * p.2) ''
                (reps ×ˢ (Subtype.val '' CayleyBall S_H ((m + 1) * (n + 1)))) := by
            intro g hg
            obtain ⟨r, hr, h, hg_eq, hh_ball⟩ := hball_decomp g hg
            have hh_in_H : (h : G) ∈ (H : Set G) := h.2
            have hh_img : (h : G) ∈ Subtype.val '' CayleyBall S_H ((m + 1) * (n + 1)) :=
              h_word_bound (n + 1) ⟨hh_in_H, hh_ball⟩
            refine ⟨(r, (h : G)), ⟨hr, hh_img⟩, ?_⟩
            simp [hg_eq]
          -- Now bound the cardinality
          calc (CayleyBall S_G n).ncard
              ≤ ((fun (p : G × G) => p.1 * p.2) ''
                  (reps ×ˢ (Subtype.val '' CayleyBall S_H ((m + 1) * (n + 1))))).ncard :=
                Set.ncard_le_ncard hφ (by
                  apply Set.Finite.image
                  apply Set.Finite.prod
                  · exact Finset.finite_toSet reps
                  · exact (cayleyBall_finite hS_H_fin _).image _)
            _ ≤ (reps ×ˢ (Subtype.val '' CayleyBall S_H ((m + 1) * (n + 1)))).ncard :=
                Set.ncard_image_le (by
                  apply Set.Finite.prod
                  · exact Finset.finite_toSet reps
                  · exact (cayleyBall_finite hS_H_fin _).image _)
            _ = reps.card * (Subtype.val '' CayleyBall S_H ((m + 1) * (n + 1))).ncard := by
                have hr_fin : (reps : Set G).Finite := Finset.finite_toSet reps
                have hH_fin : (Subtype.val '' CayleyBall S_H ((m + 1) * (n + 1))).Finite :=
                  (cayleyBall_finite hS_H_fin _).image _
                rw [Set.ncard_prod, Set.ncard_coe_finset]
            _ ≤ m * (CayleyBall S_H ((m + 1) * (n + 1))).ncard := by
                have hcard : reps.card = m := by
                  have h1 : reps.card = Fintype.card (G ⧸ H) := by
                    simp only [reps]
                    have hinj : Function.Injective
                        (Quotient.out (s := QuotientGroup.leftRel H)) := by
                      intro x y hxy
                      exact Quotient.out_injective hxy
                    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
                    rfl
                  have h2 : Fintype.card (G ⧸ H) = H.index := by
                    have := Subgroup.index_eq_card H
                    simp only [this]
                    exact (Nat.card_eq_fintype_card (α := G ⧸ H)).symm
                  rw [h1, h2]
                rw [hcard]
                apply Nat.mul_le_mul_left
                exact Set.ncard_image_le (cayleyBall_finite hS_H_fin _)
        simp only [GrowthFunction] at h1 ⊢
        exact_mod_cast h1
    _ ≤ (m : ℝ) * (C_H * (↑((m + 1) * (n + 1))) ^ d_H) := by
        have hpos : 0 < (m + 1) * (n + 1) := Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos n)
        have hb := hbound_H ((m + 1) * (n + 1)) hpos
        exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg m)
    _ ≤ (m : ℝ) * (C_H * ((2 : ℝ) * (m + 1) * n) ^ d_H) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_H_pos)
        have hbound : (↑((m + 1) * (n + 1)) : ℝ) ≤ 2 * (m + 1) * n := by
          have hn_ge_1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
          calc ((m : ℝ) + 1) * (↑n + 1) = (m + 1) * n + (m + 1) := by ring
            _ ≤ (m + 1) * n + (m + 1) * n := by
              have : (m : ℝ) + 1 ≤ n * ((m : ℝ) + 1) := by nlinarith
              linarith
            _ = 2 * (m + 1) * n := by ring
        apply pow_le_pow_left₀ (by positivity) hbound
    _ = (m : ℝ) * C_H * (2 * (m + 1)) ^ d_H * (n : ℝ) ^ d_H := by
        rw [mul_pow]; ring
end

end Gromov.NilpotentGrowth
