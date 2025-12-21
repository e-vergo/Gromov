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

module

public import Gromov.Definitions.Descent
public import Gromov.Proofs.PolynomialGrowth
public import Gromov.Proofs.VirtuallyNilpotent

set_option linter.style.longLine false

namespace Gromov.Descent

public section

open Gromov Gromov.PolynomialGrowth Group

variable {G : Type*} [Group G]

/-! ## Infinite Cyclic Quotient -/

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
  /-
  PROOF OUTLINE (Kleiner/Tao-Shalom approach):

  This is the deepest theorem in the descent argument. It requires substantial
  infrastructure from harmonic analysis on Cayley graphs that is not yet formalized.

  ═══════════════════════════════════════════════════════════════════════════════
  STAGE 1: Existence of Non-trivial Lipschitz Harmonic Functions
  ═══════════════════════════════════════════════════════════════════════════════

  Theorem (Tao blog, §2): Every infinite f.g. group G admits a non-constant
  function f : G → ℝ that is both harmonic and Lipschitz.

  Proof strategy:
  - Define μ = (1/|S|) ∑_{s∈S} δ_s (averaging measure)
  - Consider f_n = (1/n) ∑_{m=1}^n μ^{(*m)} (Cesàro averages)
  - These are "asymptotically harmonic": ‖f_n - f_n * μ‖ = O(1/n)

  Two cases:

  NON-AMENABLE CASE:
  If ‖f_n - f_n * δ_s‖_{ℓ¹} does not vanish, use duality to find H_n with
  |H_n * f_n(id) - H_n * f_n(s)| > ε. Take a subsequence limit via
  Banach-Alaoglu to get a bounded harmonic function.

  AMENABLE CASE (relevant for polynomial growth):
  If ‖f_n - f_n * δ_s‖_{ℓ¹} → 0, then the discrete Laplacian Δ = I - μ*
  has spectrum accumulating at 0. Using the spectral theorem, construct
  a sequence G_n with ‖ΔG_n‖_{ℓ²} → 0 but ∑ G_n(g) ΔG_n(g) = 1.
  The Dirichlet energy identity gives:
    ∑_g G_n(g) ΔG_n(g) = (1/2|S|) ∑_s ‖G_n - G_n * δ_s‖²_{ℓ²}
  Thus G_n is uniformly Lipschitz and asymptotically harmonic.
  By Arzelá-Ascoli, a subsequence converges to a non-trivial Lipschitz
  harmonic function.

  REQUIRED INFRASTRUCTURE:
  - Spectral theorem for self-adjoint operators on ℓ²(G)
  - Arzelá-Ascoli theorem for locally compact metric spaces
  - Banach-Alaoglu theorem (weak-* compactness)
  - Dirichlet energy identity for discrete Laplacian

  ═══════════════════════════════════════════════════════════════════════════════
  STAGE 2: Finite-Dimensionality via Elliptic Regularity
  ═══════════════════════════════════════════════════════════════════════════════

  Theorem (Kleiner, based on Colding-Minicozzi): If G has polynomial growth,
  then the space V of L-Lipschitz harmonic functions (vanishing at id) is
  finite-dimensional.

  Proof strategy:
  For any Lipschitz harmonic functions u_1, ..., u_D, consider the Gram matrix
    Q_R(u_i, u_j) = ∑_{g ∈ B_S(R)} u_i(g) u_j(g)

  From Lipschitz property: det(Q_R) ≤ C R^D as R → ∞
  From monotonicity: det(Q_R) ≤ det(Q_{4R})

  Key lemma (Elliptic regularity, Tao §3 Lemma 6):
  If f is harmonic and has mean zero on many small balls of radius εR
  covering B_S(4R), then
    ‖f‖_{L²(B_S(R))} ≤ ε‖f‖_{L²(B_S(4R))}

  This is proved using:
  1. REVERSE POINCARÉ: For harmonic f,
     ∑_{x ∈ B(2R)} |∇f(x)|² ≤ C R^{-2} ∑_{x ∈ B(4R)} |f(x)|²
  2. POINCARÉ INEQUALITY: For any f with mean zero on B(r),
     ∑_{x ∈ B(r)} |f(x)|² ≤ C r² |B(r)| ∑_{x ∈ B(3r)} |∇f(x)|²

  Combining these with bounded doubling from polynomial growth:
  - Cover B_S(4R) by O_ε(1) balls of radius εR
  - Subspace of functions with mean zero on all balls has codimension O_ε(1)
  - On this subspace: Q_R ≤ O(ε) Q_{4R}
  - Get improved bound: det(Q_R) ≤ O(ε)^{D - O_ε(1)} det(Q_{4R})

  For ε small and D large, this growth rate contradicts det(Q_R) ≤ C R^D.
  Thus D is bounded, proving finite-dimensionality.

  REQUIRED INFRASTRUCTURE:
  - Reverse Poincaré inequality for harmonic functions
  - Standard Poincaré inequality on balls
  - Bounded doubling property from polynomial growth
  - Linear algebra for Gram determinants
  - Covering lemmas for metric spaces

  ═══════════════════════════════════════════════════════════════════════════════
  STAGE 3: Extracting the ℤ Quotient via Representation Theory
  ═══════════════════════════════════════════════════════════════════════════════

  Now we have a finite-dimensional space V of Lipschitz harmonic functions.
  G acts on V by left translation: (g · f)(x) = f(g⁻¹x).

  Constants are preserved, so G acts on W := V/ℝ (quotient by constants).
  Since all Lipschitz harmonic functions vanishing at id form a normed space,
  this action is by bounded linear operators.

  The unit sphere in W is compact (finite-dimensional), and the action of G
  preserves the Lipschitz norm up to constants, so the image of G in GL(W)
  is precompact. Its closure is a compact Lie group.

  Theorem (Jordan, Tao §4 Theorem 7): Every finite subgroup of U(n) has an
  abelian subgroup of index ≤ C_n (depending only on n).

  Proof uses the commutator estimate for unitary matrices:
    ‖[g,h] - I‖ ≤ 2‖g - I‖ ‖h - I‖
  If g, h are close to I, their commutator is even closer.

  Applying Jordan to our situation, the image of G in GL(W) is either:

  CASE A: Finite image
    Then a finite-index subgroup G' acts trivially on W.
    The action on V is then by translations: g·f = f + λ_g(f)
    where λ_g ∈ V* is a linear functional.

    If the map g ↦ λ_g has infinite image, we get a homomorphism G → ℤ (done!).

    If the map g ↦ λ_g has finite image, then a further finite-index subgroup
    G'' acts trivially on V entirely. But then all Lipschitz harmonic functions
    are G''-invariant.

    Maximum principle: A harmonic function that is constant on cosets of a
    finite-index subgroup must be globally constant (use harmonicity at the
    average value on each coset).

    This contradicts the existence of non-trivial Lipschitz harmonic functions
    from Stage 1.

  CASE B: Infinite image
    Then some finite-index subgroup G' maps into an infinite virtually abelian
    subgroup of GL(W). An infinite f.g. virtually abelian group contains ℤ
    as a quotient, giving us the desired homomorphism G → ℤ.

  REQUIRED INFRASTRUCTURE:
  - Jordan's theorem for finite subgroups of GL_n
  - Maximum principle for harmonic functions
  - Compactness of unit sphere in finite dimensions
  - Abelian groups contain ℤ quotients (when infinite f.g.)
  - Linear algebra for quotient spaces V/ℝ

  ═══════════════════════════════════════════════════════════════════════════════
  SUMMARY OF MISSING INFRASTRUCTURE
  ═══════════════════════════════════════════════════════════════════════════════

  The proof requires approximately 1000-2000 lines of supporting material:

  ANALYSIS & FUNCTIONAL ANALYSIS:
  - Spectral theorem for discrete Laplacian on ℓ²(G)
  - Arzelá-Ascoli theorem
  - Banach-Alaoglu theorem
  - Compactness theorems for bounded Lipschitz functions

  HARMONIC FUNCTION THEORY:
  - Reverse Poincaré inequality
  - Dirichlet energy identities
  - Maximum principle for discrete harmonic functions
  - Elliptic regularity estimates

  GROUP THEORY & REPRESENTATION THEORY:
  - Jordan's theorem (finite subgroups of GL_n)
  - Compact Lie group structure theory
  - Representation theory for f.g. groups
  - Quotient extraction from abelian representations

  GEOMETRIC GROUP THEORY:
  - Bounded doubling from polynomial growth
  - Covering lemmas for Cayley graphs
  - Volume growth estimates

  See Descent_helper.lean for axiomatized versions of the key lemmas.
  A complete formalization of this theorem would be a substantial project
  requiring collaboration between analysts and group theorists.
  -/
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

  -- G is virtually nilpotent and finitely generated, hence polycyclic
  rw [isVirtuallyNilpotent_iff_polycyclic] at hG
  -- Subgroups of polycyclic groups are finitely generated
  exact Subgroup.fg_of_polycyclic hG φ.ker

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
  Complete proof requires several pieces of missing infrastructure:

  Key Challenge: N is of type `Subgroup ↥K` (subgroup of the carrier type of K),
  but we need a `Subgroup G` (subgroup of G) that is normal in G, nilpotent, and has finite index.

  The mathematical idea:
  1. Map N to G via M = Subgroup.map K.subtype N (this gives M ≤ K as a subgroup of G)
  2. Take normal closure or intersection of G-conjugates of M
  3. Use that K is FG, so finitely many distinct conjugates (by counting subgroups of given index)
  4. Intersection of finitely many finite-index subgroups has finite index
  5. This intersection is normal in G and nilpotent

  Missing infrastructure in current Mathlib/codebase:
  - Lemma: FG groups have finitely many subgroups of any given index
  - Lemma: Subgroup.map preserves nilpotency (with appropriate equivalence)
  - Lemma: Composition/tower law for finite index: [G:M] = [G:K]·[K:N]
  - Lemma: Normal closure construction and properties
  - Or alternatively: Direct construction showing N lifts to normal subgroup of G

  The standard approach in group theory textbooks uses one of:
  (a) Correspondence theorem + lifting normal subgroups through short exact sequences
  (b) Frattini argument for finite-index normal subgroups
  (c) Direct construction via semidirect product structure when G/K ≅ ℤ

  For approach (c): Since G/K ≅ ℤ, pick t ∈ G mapping to generator. Then G = ⟨K,t⟩ where
  conjugation by t permutes finite-index subgroups of K. The intersection ⋂ₘ tᵐNt⁻ᵐ has
  finite index (finitely many distinct conjugates) and is t-invariant, hence normal in G.

  This is a cornerstone result but requires careful formalization. Leaving as sorry.
  -/
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

end

end Gromov.Descent
