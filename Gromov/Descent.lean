/-
Copyright 2025 The Formal Conjectures Authors.
SPDX-License-Identifier: Apache-2.0

Wave 4: Inductive descent argument for Kleiner's proof of Gromov's theorem.

The main structure of Kleiner's proof proceeds by induction on the polynomial growth degree:
1. If G is finite, then G is trivially virtually nilpotent.
2. If G is infinite with polynomial growth, then G admits an infinite cyclic quotient
   (via harmonic functions / Colding-Minicozzi theory).
3. The kernel K of the quotient map G → Z has polynomial growth of degree at most d-1.
4. By induction on d, K is virtually nilpotent.
5. Extensions of virtually nilpotent groups by Z are virtually nilpotent.

This file sets up the key definitions and theorem statements for this descent argument.
-/

import Gromov.PolynomialGrowth
import Gromov.VirtuallyNilpotent

set_option linter.style.longLine false

namespace Descent

open GromovPolynomialGrowth PolynomialGrowth Group

variable {G : Type*} [Group G]

/-! ## Infinite Cyclic Quotient -/

/-- A group `G` has an infinite cyclic quotient if there exists a surjective homomorphism
    from `G` onto `Multiplicative ℤ` (the multiplicative version of the integers). -/
def HasInfiniteCyclicQuotient (G : Type*) [Group G] : Prop :=
  ∃ φ : G →* Multiplicative ℤ, Function.Surjective φ

/-- Having an infinite cyclic quotient is equivalent to having a normal subgroup
    with quotient isomorphic to Z. -/
theorem hasInfiniteCyclicQuotient_iff_exists_normal :
    HasInfiniteCyclicQuotient G ↔
    ∃ (N : Subgroup G) (_ : N.Normal), Nonempty (G ⧸ N ≃* Multiplicative ℤ) := by
  constructor
  · intro ⟨φ, hφ⟩
    refine ⟨φ.ker, MonoidHom.normal_ker φ, ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφ⟩⟩
  · intro ⟨N, hN, ⟨e⟩⟩
    haveI : N.Normal := hN
    use e.toMonoidHom.comp (QuotientGroup.mk' N)
    intro z
    obtain ⟨q, hq⟩ := e.surjective z
    refine ⟨Quotient.out q, ?_⟩
    simp only [MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
      QuotientGroup.out_eq']
    exact hq

/-- The kernel of a surjection to Multiplicative Z is a normal subgroup. -/
theorem kernel_normal_of_surj_to_Z (φ : G →* Multiplicative ℤ) :
    φ.ker.Normal :=
  MonoidHom.normal_ker φ

/-! ## Polynomial Growth Degree for Groups -/

/-- The polynomial growth degree of a finitely generated group, defined as the infimum
    of exponents d such that some generating set has growth function bounded by C * n^d.

    For a group without polynomial growth, this returns 0 by convention (sInf of empty set).
    For finite groups, this is 0.
    For Z, this is 1.
    For Z^n, this is n.
-/
noncomputable def PolynomialGrowthDegree (G : Type*) [Group G] : ℕ :=
  sInf {d : ℕ | ∃ (S : Set G), S.Finite ∧ Subgroup.closure S = ⊤ ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n > 0, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d}

/-- A group has polynomial growth of degree at most d if there exists a finite generating set
    whose growth function is bounded by C * n^d. -/
def HasPolynomialGrowthDegree (G : Type*) [Group G] (d : ℕ) : Prop :=
  ∃ (S : Set G), S.Finite ∧ Subgroup.closure S = ⊤ ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n > 0, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d

/-- If a group has polynomial growth of degree d, then it has polynomial growth of degree d' for any d' ≥ d. -/
theorem hasPolynomialGrowthDegree_mono {d d' : ℕ} (hdd' : d ≤ d')
    (h : HasPolynomialGrowthDegree G d) : HasPolynomialGrowthDegree G d' := by
  obtain ⟨S, hS_fin, hS_gen, C, hC_pos, hC⟩ := h
  use S, hS_fin, hS_gen, C, hC_pos
  intro n hn
  have hpow : (n : ℝ) ^ d ≤ (n : ℝ) ^ d' := by
    have h1 : (n : ℕ) ^ d ≤ n ^ d' := Nat.pow_le_pow_right (Nat.one_le_of_lt hn) hdd'
    exact_mod_cast h1
  calc (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d := hC n hn
    _ ≤ C * (n : ℝ) ^ d' := by apply mul_le_mul_of_nonneg_left hpow (le_of_lt hC_pos)

/-- Polynomial growth implies having some polynomial growth degree. -/
theorem hasPolynomialGrowthDegree_of_hasPolynomialGrowth (h : HasPolynomialGrowth G) :
    ∃ d, HasPolynomialGrowthDegree G d := by
  obtain ⟨S, hS_fin, hS_gen, C, d, hC_pos, hC⟩ := h
  exact ⟨d, S, hS_fin, hS_gen, C, hC_pos, hC⟩

/-- Having polynomial growth degree implies polynomial growth. -/
theorem hasPolynomialGrowth_of_hasPolynomialGrowthDegree {d : ℕ}
    (h : HasPolynomialGrowthDegree G d) : HasPolynomialGrowth G := by
  obtain ⟨S, hS_fin, hS_gen, C, hC_pos, hC⟩ := h
  exact ⟨S, hS_fin, hS_gen, C, d, hC_pos, hC⟩

/-- Finite groups have polynomial growth degree 0. -/
theorem polynomialGrowthDegree_finite [Finite G] : HasPolynomialGrowthDegree G 0 := by
  haveI : Fintype G := Fintype.ofFinite G
  use Set.univ, Set.finite_univ, Subgroup.closure_univ
  use Fintype.card G
  refine ⟨Nat.cast_pos.mpr Fintype.card_pos, fun n _ => ?_⟩
  simp only [pow_zero, mul_one]
  have hsub : CayleyBall (Set.univ : Set G) n ⊆ Set.univ := Set.subset_univ _
  have hfin : (Set.univ : Set G).Finite := Set.finite_univ
  have h : (CayleyBall (Set.univ : Set G) n).ncard ≤ Fintype.card G := by
    have h1 : (CayleyBall Set.univ n).ncard ≤ (Set.univ : Set G).ncard :=
      Set.ncard_le_ncard hsub hfin
    simp only [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
    exact h1
  calc (GrowthFunction (Set.univ : Set G) n : ℝ) = (CayleyBall Set.univ n).ncard := rfl
    _ ≤ Fintype.card G := by exact_mod_cast h

/-! ## Key Lemmas for the Descent Argument -/

/-- If G is an infinite group with polynomial growth, then G has an infinite cyclic quotient.

This is a deep theorem that follows from the Colding-Minicozzi theory of harmonic functions
on groups with polynomial growth. The proof shows that an infinite group with polynomial growth
admits a nontrivial harmonic function of polynomial growth, whose level sets give rise to
a homomorphism onto Z.

The full proof requires:
1. Construction of a harmonic function with polynomial growth (Colding-Minicozzi)
2. Analysis of the level sets to produce a homomorphism
3. Verification that the homomorphism is surjective onto Z
-/
theorem infinite_cyclic_quotient_of_polynomial_growth [Infinite G] [FG G]
    (h : HasPolynomialGrowth G) : HasInfiniteCyclicQuotient G := by
  sorry

/-- If G → Z is surjective with kernel K, and G has polynomial growth degree d > 0,
    then K has polynomial growth degree at most d - 1.

This is a key step in the descent argument. The intuition is:
- K is a "codimension 1" subgroup of G
- The growth of K is one degree lower than G
- This follows from analyzing how the Cayley graph of G fibers over Z
-/
theorem kernel_growth_degree_lt (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    {d : ℕ} (hd : d > 0) (hG : HasPolynomialGrowthDegree G d) :
    HasPolynomialGrowthDegree φ.ker (d - 1) := by
  sorry

/-- The kernel of a surjection from a finitely generated group to Z is finitely generated.

This follows from the fact that G splits as a semidirect product of ker(φ) and Z.
If S generates G and t is a preimage of 1 ∈ Z, then {s * t^(-φ(s)) : s ∈ S} generates ker(φ).
-/
theorem kernel_fg_of_surj_to_Z [FG G] (φ : G →* Multiplicative ℤ)
    (hφ : Function.Surjective φ) : FG φ.ker := by
  classical
  -- Get generators for G
  obtain ⟨S, hS⟩ := Group.fg_def.mp ‹FG G›
  -- Get a preimage of 1 ∈ ℤ (generator of Multiplicative ℤ)
  obtain ⟨t, ht⟩ := hφ (Multiplicative.ofAdd 1)
  -- Helper lemma: (ofAdd 1)^n = ofAdd n for Multiplicative ℤ
  have zpow_ofAdd_one : ∀ n : ℤ, (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    intro n
    rw [← ofAdd_zsmul]
    congr 1
    ring
  -- Define kernel generators: for each s ∈ S, form s * t^(-φ(s).toAdd) which is in ker
  have helem : ∀ s ∈ S, s * t ^ (-(Multiplicative.toAdd (φ s))) ∈ φ.ker := by
    intro s _
    rw [MonoidHom.mem_ker, map_mul, map_zpow, ht, zpow_ofAdd_one]
    simp only [ofAdd_toAdd, mul_inv_cancel]
  -- Create generators for ker: {s * t^(-n_s) : s ∈ S} ∪ {[s, t] : s ∈ S}
  -- where n_s = toAdd(φ(s)) and [s,t] = s * t * s⁻¹ * t⁻¹
  -- The commutators are in ker since φ([s,t]) = φ(s) * φ(t) * φ(s)⁻¹ * φ(t)⁻¹ = 1 (Z is abelian)
  have hcomm : ∀ s ∈ S, ⁅s, t⁆ ∈ φ.ker := by
    intro s _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    ring
  -- The set T of modified generators
  let T₁ : Finset φ.ker := S.attach.image (fun ⟨s, hs⟩ => ⟨s * t ^ (-(Multiplicative.toAdd (φ s))), helem s hs⟩)
  let T₂ : Finset φ.ker := S.attach.image (fun ⟨s, hs⟩ => ⟨⁅s, t⁆, hcomm s hs⟩)
  let T := T₁ ∪ T₂
  -- Show this generates the kernel
  rw [Group.fg_def]
  use T
  -- Show closure of T is the whole kernel
  ext ⟨g, hg⟩
  simp only [Subgroup.mem_top, iff_true]
  -- g ∈ G, and g ∈ ker(φ), means φ(g) = 1
  -- g is in closure S
  have hg_clos : g ∈ Subgroup.closure (S : Set G) := by rw [hS]; exact Subgroup.mem_top g
  haveI hker_normal : φ.ker.Normal := MonoidHom.normal_ker φ
  -- Key lemma: any element of ker can be expressed using T₁ elements and conjugates by t
  -- Since conjugation by t differs from identity by a commutator [k, t], and [s, t] ∈ T₂,
  -- the closure of T contains all conjugates we need
  -- We prove by strong induction on word length
  -- Alternative approach: show ker.subgroupOf (closure (S ∪ {t})) = closure(T)
  -- For any s ∈ S: s = (s * t^(-n_s)) * t^(n_s) where s * t^(-n_s) ∈ T₁ ⊆ ker
  -- For g = s₁ε₁ * s₂ε₂ * ... * sₘεₘ (where εᵢ ∈ {1, -1}), we can rewrite:
  -- g = (T₁ * t^n₁)^ε₁ * (T₂ * t^n₂)^ε₂ * ...
  -- Moving all t-powers to the right using conjugation and commutators
  -- Final: (product of conjugates) * t^(∑εᵢnᵢ)
  -- If g ∈ ker, then ∑εᵢnᵢ = 0
  -- The conjugates differ by elements of T₂ (commutators)
  -- This is a detailed word manipulation - let's use a helper
  -- Actually, let's prove directly by showing T generates ker as a subgroup of G
  -- restricted to ker
  -- The key is: closure(T) contains all conjugates t^k * T₁_elem * t^(-k) for k ∈ ℤ
  -- because t^k * x * t^(-k) = x * [x⁻¹, t^k] and [x⁻¹, t^k] ∈ closure(T₂)
  -- This follows from [x, t^k] being a product of k copies of [x, t] (up to conjugation)
  -- For a complete proof, we need careful word manipulation
  -- Let's use a cleaner approach via the semidirect product structure
  sorry

/-- If K is virtually nilpotent and G/K ≅ Z, then G is virtually nilpotent.

This is a fundamental result about extensions. The key insight is that Z is abelian
(hence nilpotent), and extensions of nilpotent groups by nilpotent groups are
"virtually nilpotent" under the right conditions. Since Z is infinite cyclic,
the extension structure is particularly well-behaved.
-/
theorem isVirtuallyNilpotent_of_extension_by_Z (K : Subgroup G) [K.Normal]
    (hQ : Nonempty (G ⧸ K ≃* Multiplicative ℤ))
    (hK : IsVirtuallyNilpotent K) : IsVirtuallyNilpotent G := by
  sorry

/-- Alternative formulation using a surjective homomorphism directly. -/
theorem isVirtuallyNilpotent_of_surj_to_Z (φ : G →* Multiplicative ℤ)
    (hφ : Function.Surjective φ)
    (hK : IsVirtuallyNilpotent φ.ker) : IsVirtuallyNilpotent G := by
  apply isVirtuallyNilpotent_of_extension_by_Z φ.ker
  · exact ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφ⟩
  · exact hK

/-! ## The Descent Theorem -/

/-- Main descent theorem: Polynomial growth implies virtually nilpotent.

This is the forward direction of Gromov's theorem. The proof proceeds by strong
induction on the polynomial growth degree d:

Base case (d = 0 or finite group):
- Finite groups are trivially virtually nilpotent.

Inductive case (d ≥ 1, G infinite):
- By `infinite_cyclic_quotient_of_polynomial_growth`, G has a surjection φ : G → Z.
- The kernel K = ker(φ) has polynomial growth degree ≤ d - 1.
- By the inductive hypothesis, K is virtually nilpotent.
- By `isVirtuallyNilpotent_of_extension_by_Z`, G is virtually nilpotent.
-/
theorem isVirtuallyNilpotent_of_polynomialGrowth [FG G] (h : HasPolynomialGrowth G) :
    IsVirtuallyNilpotent G := by
  -- We proceed by case analysis on whether G is finite or infinite
  by_cases hFin : Finite G
  · -- Finite case: trivial
    exact isVirtuallyNilpotent_of_finite
  · -- Infinite case: use the descent argument
    haveI : Infinite G := not_finite_iff_infinite.1 hFin
    -- Get an infinite cyclic quotient
    obtain ⟨φ, hφ⟩ := infinite_cyclic_quotient_of_polynomial_growth h
    -- The kernel is virtually nilpotent (by induction - this is the sorry)
    have hK : IsVirtuallyNilpotent φ.ker := by
      sorry
    -- Extension by Z preserves virtual nilpotency
    exact isVirtuallyNilpotent_of_surj_to_Z φ hφ hK

/-! ## Auxiliary Results -/

/-- Helper lemma: products of ±1 in Multiplicative Z give bounded integers. -/
private lemma list_prod_pm1_aux (l : List (Multiplicative ℤ))
    (hl : ∀ s ∈ l, s ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) ∨
                   s⁻¹ ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ))) :
    ∃ k : ℤ, |k| ≤ l.length ∧ l.prod = Multiplicative.ofAdd k := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    have hxs_mem : ∀ s ∈ xs, s ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) ∨
                             s⁻¹ ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) :=
      fun s hs => hl s (List.mem_cons.mpr (Or.inr hs))
    obtain ⟨k', hk'_bound, hk'_prod⟩ := ih hxs_mem
    have hx : x ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) ∨
              x⁻¹ ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) :=
      hl x (List.mem_cons.mpr (Or.inl rfl))
    cases hx with
    | inl hx =>
      simp only [Set.mem_singleton_iff] at hx
      use k' + 1
      constructor
      · simp only [List.length_cons]
        have h1 : |k' + 1| ≤ |k'| + 1 := by
          calc |k' + 1| ≤ |k'| + |1| := abs_add_le k' 1
            _ = |k'| + 1 := by simp
        omega
      · simp only [List.prod_cons, hx, hk'_prod]
        change Multiplicative.ofAdd (1 + k') = Multiplicative.ofAdd (k' + 1)
        congr 1; ring
    | inr hxinv =>
      simp only [Set.mem_singleton_iff] at hxinv
      use k' - 1
      constructor
      · simp only [List.length_cons]
        have h1 : |k' - 1| ≤ |k'| + |1| := abs_sub k' 1
        simp only [abs_one] at h1
        omega
      · simp only [List.prod_cons, hk'_prod]
        have hx_eq : x = Multiplicative.ofAdd (-1 : ℤ) := by
          have : x⁻¹ = Multiplicative.ofAdd (1 : ℤ) := hxinv
          calc x = (x⁻¹)⁻¹ := by simp
            _ = (Multiplicative.ofAdd (1 : ℤ))⁻¹ := by rw [this]
            _ = Multiplicative.ofAdd (-1 : ℤ) := rfl
        simp only [hx_eq]
        change Multiplicative.ofAdd ((-1 : ℤ) + k') = Multiplicative.ofAdd (k' - 1)
        congr 1; ring

/-- Z has polynomial growth degree exactly 1. -/
theorem polynomialGrowthDegree_int : HasPolynomialGrowthDegree (Multiplicative ℤ) 1 := by
  use {Multiplicative.ofAdd 1}
  refine ⟨Set.finite_singleton _, ?_, ?_⟩
  · -- {ofAdd 1} generates Multiplicative Z
    ext n
    simp only [Subgroup.mem_top, iff_true]
    rw [Subgroup.mem_closure_singleton]
    refine ⟨Multiplicative.toAdd n, ?_⟩
    change Multiplicative.ofAdd (Multiplicative.toAdd n * 1) = n
    simp only [mul_one]
    exact Multiplicative.toAdd.symm_apply_apply n
  · -- Growth is bounded by C * n^1
    use 3
    refine ⟨by norm_num, fun n hn => ?_⟩
    -- The Cayley ball of radius n contains integers from -n to n
    -- So it has at most 2n + 1 ≤ 3n elements
    have h_bound : (CayleyBall {Multiplicative.ofAdd (1 : ℤ)} n).ncard ≤ 2 * n + 1 := by
      -- The Cayley ball is contained in {ofAdd k | |k| ≤ n}
      have h_subset : CayleyBall {Multiplicative.ofAdd (1 : ℤ)} n ⊆
          {g | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k} := by
        intro g hg
        simp only [CayleyBall, Set.mem_setOf_eq] at hg
        obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hg
        obtain ⟨k, hk_bound, hk_prod⟩ := list_prod_pm1_aux l hl_mem
        refine ⟨k, ?_, hk_prod ▸ hl_prod.symm⟩
        calc |k| ≤ l.length := hk_bound
          _ ≤ n := by exact_mod_cast hl_len
      -- The set {ofAdd k | |k| ≤ n} has cardinality 2n + 1
      have h_card : ({g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k}).ncard = 2 * n + 1 := by
        have h_eq : {g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k} =
                    Multiplicative.ofAdd '' {k : ℤ | |k| ≤ n} := by
          ext g; simp only [Set.mem_setOf_eq, Set.mem_image]
          constructor <;> (intro ⟨k, hk, hg⟩; exact ⟨k, hk, hg.symm⟩)
        rw [h_eq]
        have h_inj : Function.Injective (Multiplicative.ofAdd : ℤ → Multiplicative ℤ) :=
          Multiplicative.ofAdd.injective
        rw [Set.ncard_image_of_injective _ h_inj]
        have h_eq2 : {k : ℤ | |k| ≤ n} = Set.Icc (-n : ℤ) n := by
          ext k; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        rw [h_eq2, Set.ncard_eq_toFinset_card']
        simp only [Set.toFinset_Icc, Int.card_Icc, sub_neg_eq_add]
        have h : (n : ℤ) + 1 + n = (2 * n + 1 : ℕ) := by omega
        rw [h, Int.toNat_natCast]
      have h_fin : ({g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k}).Finite := by
        have h_eq : {g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k} =
                    Multiplicative.ofAdd '' {k : ℤ | |k| ≤ n} := by
          ext g; simp only [Set.mem_setOf_eq, Set.mem_image]
          constructor <;> (intro ⟨k, hk, hg⟩; exact ⟨k, hk, hg.symm⟩)
        rw [h_eq]
        apply Set.Finite.image
        have h_eq2 : {k : ℤ | |k| ≤ n} = Set.Icc (-n : ℤ) n := by
          ext k; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        rw [h_eq2]
        exact Set.finite_Icc (-n : ℤ) n
      calc (CayleyBall {Multiplicative.ofAdd (1 : ℤ)} n).ncard
          ≤ ({g : Multiplicative ℤ | ∃ k : ℤ, |k| ≤ n ∧ g = Multiplicative.ofAdd k}).ncard :=
            Set.ncard_le_ncard h_subset h_fin
        _ = 2 * n + 1 := h_card
    calc (GrowthFunction {Multiplicative.ofAdd (1 : ℤ)} n : ℝ)
        = (CayleyBall {Multiplicative.ofAdd (1 : ℤ)} n).ncard := rfl
      _ ≤ 2 * n + 1 := by exact_mod_cast h_bound
      _ ≤ 3 * n := by
        have : 2 * n + 1 ≤ 3 * n := by omega
        exact_mod_cast this
      _ = 3 * (n : ℝ) ^ 1 := by ring

/-- Z does not have polynomial growth degree 0 (it is infinite). -/
theorem not_polynomialGrowthDegree_zero_int : ¬HasPolynomialGrowthDegree (Multiplicative ℤ) 0 := by
  intro ⟨S, hS_fin, hS_gen, C, hC_pos, hC⟩
  -- Degree 0 polynomial bound means bounded growth, but Z is infinite
  -- Use the fact that bounded growth implies finite group
  have h_finite : Finite (Multiplicative ℤ) := by
    apply finite_of_polynomial_growth_degree_zero hS_fin hS_gen
    exact ⟨C, hC_pos, fun n hn => by simp only [pow_zero, mul_one] at hC; exact hC n hn⟩
  -- But Z is infinite - construct an injection from ℕ
  have h_inj : Function.Injective (fun n : ℕ => Multiplicative.ofAdd (n : ℤ)) := by
    intro n m h
    simp only [EmbeddingLike.apply_eq_iff_eq, Int.natCast_inj] at h
    exact h
  haveI : Infinite (Multiplicative ℤ) := Infinite.of_injective _ h_inj
  exact @not_finite (Multiplicative ℤ) _ h_finite

end Descent
