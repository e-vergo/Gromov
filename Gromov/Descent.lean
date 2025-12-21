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

/-- Having polynomial growth degree implies finitely generated. -/
theorem fg_of_hasPolynomialGrowthDegree {d : ℕ}
    (h : HasPolynomialGrowthDegree G d) : FG G := by
  obtain ⟨S, hS_fin, hS_gen, _, _, _⟩ := h
  exact ⟨⟨hS_fin.toFinset, by simp [hS_gen]⟩⟩

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
  /-
  Proof Strategy (to be completed):

  1. Let S be a generating set for G with |B_S(n)| ≤ C * n^d.
  2. Let t be a lift of the generator 1 ∈ Z, so φ(t) = ofAdd(1).
  3. Define M = max{|φ(s)| : s ∈ S} + 1. Then elements in B_S(n) map to integers in [-Mn, Mn].
  4. Define S' = S ∪ {t, t⁻¹} and R = 2M + 1.
  5. Define S_K = {k ∈ K | k ∈ B_{S'}(R)} - the "short" kernel elements.

  For generation: For any s ∈ S', define c_s = s * t^(-φ(s)) ∈ K. Then c_s ∈ S_K
  (since it's in the R-ball). Every element k ∈ K can be written as a word in S',
  and by replacing each s with c_s * t^(φ(s)), we get k as a product of c_s terms
  (the t-powers cancel since φ(k) = 1).

  For growth bound: The key insight is that B_G(n) intersects O(n) cosets of K
  (since elements in B_G(n) have |φ(g)| ≤ Mn). By a counting argument,
  the average size of B_G(n) ∩ (coset) is O(n^{d-1}). The kernel K corresponds to
  the coset at level 0, and with appropriate uniformity arguments,
  |B_K(n)| ≤ C' * n^{d-1}.
  -/
  sorry

/-- The kernel of a surjection from a finitely generated group with polynomial growth to Z
    is finitely generated.

NOTE: This theorem requires polynomial growth (or virtual nilpotency) as a hypothesis.
For general FG groups, the kernel of a surjection to Z need not be FG.
Counterexample: The Baumslag-Solitar group BS(1,2) = ⟨a, t | tat⁻¹ = a²⟩ is FG,
but the kernel of the projection to Z (generated by t) is not FG.

For groups with polynomial growth, the kernel is FG because:
1. Polynomial growth implies virtually nilpotent (Gromov's theorem - the theorem we're proving)
2. Kernels of maps from virtually nilpotent groups to Z are FG

In the descent argument, we use this after establishing that the kernel has polynomial growth
of lower degree, allowing induction.
-/
theorem kernel_fg_of_surj_to_Z_of_polynomialGrowth [FG G] (φ : G →* Multiplicative ℤ)
    (hφ : Function.Surjective φ) (hG : HasPolynomialGrowth G) : FG φ.ker := by
  -- Get a polynomial growth degree from HasPolynomialGrowth
  obtain ⟨d, hd⟩ := hasPolynomialGrowthDegree_of_hasPolynomialGrowth hG
  -- Case split on d
  by_cases hdz : d = 0
  · -- d = 0 means G is finite
    subst hdz
    have hfin : Finite G := by
      obtain ⟨S, hS_fin, hS_gen, C, hC_pos, hC⟩ := hd
      exact finite_of_polynomial_growth_degree_zero hS_fin hS_gen
        ⟨C, hC_pos, fun n hn => by simp only [pow_zero, mul_one] at hC ⊢; exact hC n hn⟩
    -- Finite groups have FG subgroups (subgroups of finite groups are finite hence FG)
    haveI : Fintype G := Fintype.ofFinite G
    -- Use that finite groups are FG
    exact Group.fg_of_finite
  · -- d > 0, use kernel_growth_degree_lt
    have hd_pos : d > 0 := Nat.pos_of_ne_zero hdz
    have hker_growth : HasPolynomialGrowthDegree φ.ker (d - 1) := kernel_growth_degree_lt φ hφ hd_pos hd
    exact fg_of_hasPolynomialGrowthDegree hker_growth

/-- Alternative: The kernel of a surjection from a virtually nilpotent group to Z is FG.

This is the cleanest formulation for the descent argument, since by induction
the kernel is virtually nilpotent (having lower polynomial growth degree).
-/
theorem kernel_fg_of_surj_to_Z_of_virtuallyNilpotent [FG G] (φ : G →* Multiplicative ℤ)
    (hφ : Function.Surjective φ) (hG : IsVirtuallyNilpotent G) : FG φ.ker := by
  -- Strategy: Use that virtually nilpotent groups are polycyclic,
  -- and polycyclic groups have the property that all subgroups are FG.
  -- The kernel φ.ker is a subgroup of G, hence FG.
  sorry

/-- If K is virtually nilpotent and G/K ≅ Z, then G is virtually nilpotent.

This is a fundamental result about extensions. The key insight is that Z is abelian
(hence nilpotent), and extensions of nilpotent groups by nilpotent groups are
"virtually nilpotent" under the right conditions. Since Z is infinite cyclic,
the extension structure is particularly well-behaved.

The proof strategy:
1. K has a finite-index nilpotent subgroup H (by virtual nilpotency)
2. Take N = H.normalCore in K, which is normal in K and has finite index
3. Consider the conjugation action of G on finite-index subgroups of K
4. The intersection of all G-conjugates of N is normal in G
5. This intersection has finite index in K (finitely many conjugates due to
   the finite index), hence finite index in G
6. The intersection is nilpotent (as a subgroup of N)

Note: This requires the hypothesis that K is finitely generated. In a f.g. group,
there are only finitely many subgroups of any given finite index. Since all
G-conjugates of N have the same index in K, there are only finitely many of them,
so the intersection has finite index.

In the context of Gromov's descent, K = ker(G → Z) is f.g. when G is f.g.
(proved in `kernel_fg_of_surj_to_Z`).
-/
theorem isVirtuallyNilpotent_of_extension_by_Z (K : Subgroup G) [K.Normal] [FG K]
    (hQ : Nonempty (G ⧸ K ≃* Multiplicative ℤ))
    (hK : IsVirtuallyNilpotent K) : IsVirtuallyNilpotent G := by
  /-
  Proof strategy:
  1. K has a finite-index normal nilpotent subgroup N (by virtual nilpotency)
  2. Consider conjugates of N by elements of G. Since K ⊴ G, all conjugates lie in K.
  3. Since K is f.g., there are finitely many subgroups of index [K:N] in K.
  4. Therefore, there are finitely many distinct G-conjugates of N.
  5. The intersection M of all G-conjugates is normal in G, nilpotent, and has finite index in K.
  6. To get finite index in G, we use the structure of the extension by Z:
     - Let t ∈ G map to 1 ∈ Z. Then G = ⟨K, t⟩.
     - Consider L = ⟨M, t^n⟩ where n = number of conjugates.
     - L has finite index in G and we can show L is nilpotent using the centralizer argument.

  Note: The key technical lemma needed is that finitely generated groups have only
  finitely many subgroups of any given finite index. This follows from the correspondence
  between index-n subgroups and transitive actions on n-element sets.

  For now, we complete this proof with a sorry, as the full argument requires
  substantial additional infrastructure about counting subgroups.
  -/

  -- Get a normal nilpotent subgroup N of K with finite index
  rw [isVirtuallyNilpotent_iff_exists_normal] at hK
  obtain ⟨N, hN_normal, hN_nil, hN_fin⟩ := hK
  haveI : N.FiniteIndex := hN_fin
  haveI : IsNilpotent N := hN_nil

  /-
  Complete proof strategy (requires additional infrastructure):

  Since G/K ≃* ℤ, pick t ∈ G with φ(t) = 1 where φ : G →* Multiplicative ℤ.
  Then G = ⟨K, t⟩.

  Key lemma needed: In a f.g. group, there are finitely many subgroups of any
  given finite index. This follows from the correspondence:
    {index-n subgroups of H} ↔ {transitive actions of H on Fin n}
  The right side is finite when H is f.g.

  Using this lemma:
  - The conjugates t^m N t^{-m} for m ∈ ℤ are all subgroups of K with the
    same index as N (since K is normal in G).
  - By the lemma, this set is finite, so there exists period p with
    t^p N t^{-p} = N.
  - Define L = ⟨N, t^p⟩ ≤ G. Then [G : L] divides p · [K : N] < ∞.
  - L is a semidirect product N ⋊ ⟨t^p⟩ where t^p normalizes N.
  - Since N is nilpotent and the action of t^p is by an automorphism that
    preserves the lower central series, L is virtually nilpotent.

  The final step uses that semidirect products of nilpotent groups by cyclic
  groups, where the action respects nilpotency, are virtually nilpotent.
  This follows from the fact that the automorphism t^p has finite order on
  N/[N,N] (which is a f.g. abelian group with finitely many automorphisms
  of any given order).
  -/

  -- TODO: Implement the lemma about finitely many subgroups of given index
  -- in finitely generated groups, then complete this proof.
  sorry

/-- Alternative formulation using a surjective homomorphism directly.
    Requires polynomial growth to ensure the kernel is finitely generated. -/
theorem isVirtuallyNilpotent_of_surj_to_Z [FG G] (φ : G →* Multiplicative ℤ)
    (hφ : Function.Surjective φ) (hG : HasPolynomialGrowth G)
    (hK : IsVirtuallyNilpotent φ.ker) : IsVirtuallyNilpotent G := by
  haveI : FG φ.ker := kernel_fg_of_surj_to_Z_of_polynomialGrowth φ hφ hG
  apply isVirtuallyNilpotent_of_extension_by_Z φ.ker
  · exact ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφ⟩
  · exact hK

/-! ## The Descent Theorem -/

/-- Helper lemma: If G has polynomial growth degree d, then G is virtually nilpotent.
    This is the core inductive step, proved by strong induction on d. -/
theorem isVirtuallyNilpotent_of_polynomialGrowthDegree :
    ∀ (d : ℕ) (G : Type*) [Group G] [FG G],
    HasPolynomialGrowthDegree G d → IsVirtuallyNilpotent G := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro G _ _ hd
    by_cases hFin : Finite G
    · -- Finite case: trivial
      exact isVirtuallyNilpotent_of_finite
    · -- Infinite case: use the descent argument
      haveI : Infinite G := not_finite_iff_infinite.1 hFin
      -- Infinite groups with polynomial growth have positive degree
      have hd_pos : d > 0 := by
        by_contra h
        push_neg at h
        interval_cases d
        -- d = 0 means bounded growth, hence finite - contradiction
        have hfin : Finite G := by
          obtain ⟨S, hS_fin, hS_gen, C, hC_pos, hC⟩ := hd
          exact finite_of_polynomial_growth_degree_zero hS_fin hS_gen
            ⟨C, hC_pos, fun n hn => by simp only [pow_zero, mul_one] at hC ⊢; exact hC n hn⟩
        exact hFin hfin
      -- Get polynomial growth from the degree
      have h : HasPolynomialGrowth G := hasPolynomialGrowth_of_hasPolynomialGrowthDegree hd
      -- Get an infinite cyclic quotient
      obtain ⟨φ, hφ⟩ := infinite_cyclic_quotient_of_polynomial_growth h
      -- Kernel has polynomial growth degree d - 1
      have hker_deg : HasPolynomialGrowthDegree φ.ker (d - 1) :=
        kernel_growth_degree_lt φ hφ hd_pos hd
      -- Kernel is finitely generated
      haveI : FG φ.ker := fg_of_hasPolynomialGrowthDegree hker_deg
      -- By induction, kernel is virtually nilpotent (d - 1 < d)
      have hK : IsVirtuallyNilpotent φ.ker :=
        ih (d - 1) (Nat.sub_lt hd_pos Nat.one_pos) φ.ker hker_deg
      -- Extension by Z preserves virtual nilpotency
      exact isVirtuallyNilpotent_of_surj_to_Z φ hφ h hK

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
  -- Get a polynomial growth degree
  obtain ⟨d, hd⟩ := hasPolynomialGrowthDegree_of_hasPolynomialGrowth h
  -- Apply the inductive theorem
  exact isVirtuallyNilpotent_of_polynomialGrowthDegree d G hd

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
