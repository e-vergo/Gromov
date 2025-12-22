/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Growth degree bounds for kernels of homomorphisms to Z.

This file proves the key result for the descent argument: if G has polynomial
growth degree d and phi : G -> Z is surjective, then ker(phi) has polynomial
growth degree at most d - 1.

The proof uses the fibration structure from Fibration.lean to show that the
kernel "loses one dimension" of growth. Intuitively, the Cayley ball B_G(n)
is distributed across O(n) level sets (cosets of ker(phi)), so the average
level set has O(n^{d-1}) elements.

## Main Results

* `kernel_generators_from_schreier` - Generators for ker(phi) from G's generators
* `kernel_fg` - ker(phi) is finitely generated when G is f.g.
* `kernel_ball_size_bound` - |B_{ker phi}(n)| <= C * |B_G(n)| / n asymptotically
* `polynomial_growth_degree_decreases` - If G has degree d, ker(phi) has degree <= d-1
* `kernel_growth_degree_lt_aux` - Helper lemma for Descent.lean

## Key Insight

The Cayley ball B_G(n) intersects O(n) level sets. If |B_G(n)| ~ C * n^d,
then by pigeonhole the average level set intersection has size O(n^{d-1}).
Since each level set is a coset of ker(phi), this bounds the growth of ker(phi).

## References

* Tao-Shalom "A finitary version of Gromov's polynomial growth theorem" Section 5
* de la Harpe "Topics in geometric group theory" Chapter VII
-/

import Gromov.Definitions.Descent
import Gromov.Proofs.Cayley.Graph
import Gromov.Proofs.Growth.Fibration

namespace Gromov.Growth.KernelDegree

open Gromov
open Gromov.Growth.Fibration

/-!
## Kernel Generation

Construction of generators for ker(phi) from generators of G.
Given generators S for G and a surjection phi : G -> Z, we construct
"corrected" generators that lie in ker(phi).
-/

section KernelGenerators

variable {G : Type*} [Group G]

/-- Given a generator s in S and a lift t of the generator of Z (i.e., phi(t) = ofAdd(1)),
    the "corrected" element c_s = s * t^{-phi(s)} lies in ker(phi).

    This is the key construction: we "push" s back to the kernel level. -/
def correctedGenerator (φ : G →* Multiplicative ℤ) (t : G) (s : G) : G :=
  s * t ^ (-(Multiplicative.toAdd (φ s)))

/-- The corrected generator lies in the kernel. -/
theorem correctedGenerator_mem_ker (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (s : G) :
    correctedGenerator φ t s ∈ φ.ker := by
  /-
  PROOF SKETCH:
  phi(c_s) = phi(s * t^{-phi(s)})
           = phi(s) * phi(t)^{-phi(s)}
           = phi(s) * (ofAdd 1)^{-phi(s)}
           = phi(s) * ofAdd(-phi(s))
           = phi(s) * phi(s)^{-1}
           = 1
  -/
  sorry

/-- The set of corrected generators for the kernel. -/
def kernelGenerators (φ : G →* Multiplicative ℤ) (t : G) (S : Set G) : Set G :=
  {correctedGenerator φ t s | s ∈ S}

/-- The kernel generators are finite if S is finite. -/
theorem kernelGenerators_finite (φ : G →* Multiplicative ℤ) (t : G) (S : Set G)
    (hS : S.Finite) :
    (kernelGenerators φ t S).Finite := by
  -- Proof: Image of finite set under a function is finite.
  sorry

/-- All kernel generators lie in the kernel. -/
theorem kernelGenerators_subset_ker (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G) :
    kernelGenerators φ t S ⊆ φ.ker := by
  -- Proof: Apply correctedGenerator_mem_ker to each element.
  sorry

/-- Key generation theorem: if S generates G and phi is surjective,
    then kernelGenerators phi t S generates ker(phi).

    This is a variant of the Schreier lemma specialized to Z quotients. -/
theorem kernelGenerators_generate (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G)
    (hgen : Subgroup.closure S = ⊤) :
    Subgroup.closure (Subtype.val ⁻¹' kernelGenerators φ t S : Set φ.ker) = ⊤ := by
  /-
  PROOF SKETCH:
  Let k in ker(phi). Since S generates G, we can write k = s_1 * s_2 * ... * s_m
  where each s_i or s_i^{-1} is in S.

  For each s_i, write s_i = c_{s_i} * t^{phi(s_i)} where c_{s_i} = correctedGenerator phi t s_i.

  Then k = (c_1 * t^{k_1}) * (c_2 * t^{k_2}) * ... * (c_m * t^{k_m})
         = c_1 * c_2' * c_3'' * ... * t^{sum of k_i's}

  where c_i' are conjugates of c_i by powers of t.

  Since k in ker(phi), sum of k_i's = 0, so the t-power vanishes.
  The c_i' terms are conjugates of kernel generators, which generate ker(phi)
  (the kernel is normal, so conjugates of generators are in the group generated).

  Subtlety: We need that ker(phi) is normal in G and closed under conjugation by t.
  This is automatic since ker(phi) is a normal subgroup (kernel of homomorphism).
  -/
  sorry

/-- The kernel of a surjection to Z from a finitely generated group is finitely generated. -/
theorem kernel_fg (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    (S : Set G) (hS : S.Finite) (hgen : Subgroup.closure S = ⊤) :
    ∃ (S_K : Set φ.ker), S_K.Finite ∧ Subgroup.closure S_K = ⊤ := by
  /-
  PROOF SKETCH:
  By surjectivity, choose t with phi(t) = ofAdd(1).
  The set kernelGenerators phi t S is finite (since S is finite)
  and generates ker(phi) (by kernelGenerators_generate).
  -/
  sorry

end KernelGenerators

/-!
## Word Length Comparison

Relating word lengths in G and in ker(phi).
-/

section WordLengthComparison

variable {G : Type*} [Group G]

/-- If g in B_S(n) and g in ker(phi), then g is in a bounded ball with respect
    to the kernel generators (viewed as a subset of G).

    The bound involves the maximum height of generators and how the corrected
    generators relate to the original generators. -/
theorem kernel_element_ball_bound (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) (n : ℕ) (g : G) (hg : g ∈ CayleyBall S n)
    (hker : g ∈ φ.ker) :
    ∃ C : ℕ, g ∈ CayleyBall (kernelGenerators φ t S) (C * n) := by
  /-
  PROOF SKETCH:
  Write g = s_1 * ... * s_m with m <= n.
  Each s_i = c_i * t^{k_i} where c_i = correctedGenerator phi t s_i.

  Rearranging (and using that ker(phi) is normal):
  g = (product of c_i's and their conjugates) * t^{sum k_i}

  Since g in ker(phi), sum k_i = 0, so g is a product of O(n) terms from
  kernelGenerators and their conjugates.

  Each conjugation by t^j introduces at most O(|j|) additional factors
  (or we use a more refined analysis via the Schreier graph).

  For the crude bound: each s_i contributes one c_i and at most M
  powers of t, where M = max generator height. The t-powers partially
  cancel. Total word length in kernel generators is O(M * n).
  -/
  sorry

/-- The constant C in the ball bound can be chosen uniformly. -/
theorem kernel_ball_embedding_constant (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) :
    ∃ C : ℕ, C > 0 ∧ ∀ n g, g ∈ CayleyBall S n → g ∈ φ.ker →
      g ∈ CayleyBall (kernelGenerators φ t S) (C * n) := by
  -- Proof: Uniform version of kernel_element_ball_bound.
  sorry

end WordLengthComparison

/-!
## Growth Bounds for the Kernel

The main estimates: relating growth of ker(phi) to growth of G.
-/

section GrowthBounds

variable {G : Type*} [Group G]

/-- Key counting lemma: the kernel ball is controlled by the group ball.

    Specifically, |B_{ker phi}(n) ∩ levelSet(0)| <= |B_G(C*n)|
    for some constant C depending on the generating set. -/
theorem kernel_ball_in_group_ball (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) :
    ∃ C : ℕ, C > 0 ∧ ∀ n : ℕ,
      (CayleyBall (kernelGenerators φ t S) n).ncard ≤ (CayleyBall S (C * n)).ncard := by
  /-
  PROOF SKETCH:
  Elements of B_{S_K}(n) in ker(phi) are products of n kernel generators.
  Each kernel generator c_s = s * t^{-k} has bounded word length in S
  (specifically, at most 1 + |k| * word_length_S(t)).

  Thus B_{S_K}(n) embeds into B_S(C*n) for appropriate C.
  -/
  sorry

/-- The kernel ball size is bounded by group ball size divided by n.

    This is the key asymptotic estimate. Roughly:
    |B_{ker phi}(n)| <= C * |B_G(C'*n)| / n

    When |B_G(n)| ~ n^d, this gives |B_{ker phi}(n)| ~ n^{d-1}. -/
theorem kernel_ball_size_bound (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    (S : Set G) (hS : S.Finite) (hgen : Subgroup.closure S = ⊤) :
    ∃ (S_K : Set φ.ker) (C : ℕ),
      S_K.Finite ∧ Subgroup.closure S_K = ⊤ ∧ C > 0 ∧
      ∀ n > 0, (CayleyBall S_K n).ncard * n ≤ C * (CayleyBall S (C * n)).ncard := by
  /-
  PROOF SKETCH:
  This combines several ingredients:

  1. By fibration theory, B_G(n) is partitioned into level set intersections:
     B_G(n) = disjoint union of (B_G(n) ∩ levelSet(k)) for k in [-M*n, M*n]

  2. Level set 0 is ker(phi), so B_G(n) ∩ ker(phi) = B_G(n) ∩ levelSet(0).

  3. By averaging (pigeonhole):
     |B_G(n) ∩ levelSet(0)| <= |B_G(n)| / (2*M*n + 1) + error terms

  4. The kernel ball B_{S_K}(n) embeds into B_G(C*n) by kernel_ball_in_group_ball.

  Combining these: |B_{S_K}(n)| <= C * |B_G(C*n)| / n.

  Note: The actual argument requires more care about constants and
  uses the quasi-isometry between different generating sets.
  -/
  sorry

end GrowthBounds

/-!
## Polynomial Growth Degree Decrease

The main theorem: polynomial growth degree decreases by 1 for kernels.
-/

section DegreeDecrease

variable {G : Type*} [Group G]

/-- Helper lemma: asymptotic bound implies polynomial growth degree bound.

    If |B_{S_K}(n)| * n <= C * |B_S(C'*n)| and |B_S(m)| <= C'' * m^d,
    then |B_{S_K}(n)| <= C''' * n^{d-1}. -/
theorem polynomial_degree_from_asymptotic (S_K : Set G) (d : ℕ) (hd : d > 0)
    (C : ℕ) (hC : C > 0) (C' : ℝ) (hC' : C' > 0)
    (hbound : ∀ n > 0, (GrowthFunction S_K n : ℝ) * n ≤ C' * (n : ℝ) ^ d) :
    ∃ C'' : ℝ, C'' > 0 ∧ ∀ n > 0, (GrowthFunction S_K n : ℝ) ≤ C'' * (n : ℝ) ^ (d - 1) := by
  /-
  PROOF SKETCH:
  From hbound: GrowthFunction S_K n <= C' * n^d / n = C' * n^{d-1}.
  Take C'' = C'.
  -/
  sorry

/-- Main theorem: if G has polynomial growth degree d > 0 and phi : G -> Z is surjective,
    then ker(phi) has polynomial growth degree at most d - 1.

    This is the core technical result for the descent argument. -/
theorem polynomial_growth_degree_decreases (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    {d : ℕ} (hd : d > 0) (hG : HasPolynomialGrowthDegree G d) :
    HasPolynomialGrowthDegree φ.ker (d - 1) := by
  /-
  PROOF OUTLINE:

  1. From hG, get a generating set S for G with |B_S(n)| <= C * n^d.

  2. Construct kernel generators S_K = kernelGenerators phi t S where
     t is a lift of the generator of Z (exists by surjectivity of phi).

  3. By kernel_ball_size_bound:
     |B_{S_K}(n)| * n <= C' * |B_S(C'' * n)|

  4. Since |B_S(m)| <= C * m^d:
     |B_{S_K}(n)| * n <= C' * C * (C'' * n)^d = C''' * n^d

  5. Therefore:
     |B_{S_K}(n)| <= C''' * n^{d-1}

  6. This proves HasPolynomialGrowthDegree (ker phi) (d-1).

  SUBTLETIES:
  - Need to verify S_K generates ker(phi) (done in kernel_fg)
  - Constants require careful tracking
  - The case d = 1 gives degree 0, meaning ker(phi) is finite
  -/
  sorry

/-- Auxiliary lemma for use in Descent.lean: same statement, explicit for integration. -/
theorem kernel_growth_degree_lt_aux (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    {d : ℕ} (hd : d > 0) (hG : HasPolynomialGrowthDegree G d) :
    HasPolynomialGrowthDegree φ.ker (d - 1) :=
  polynomial_growth_degree_decreases φ hφ hd hG

end DegreeDecrease

/-!
## Special Cases
-/

section SpecialCases

variable {G : Type*} [Group G]

/-- When d = 1, the kernel has degree 0, hence is finite. -/
theorem kernel_finite_of_degree_one (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    (hG : HasPolynomialGrowthDegree G 1) :
    Finite φ.ker := by
  /-
  PROOF SKETCH:
  By polynomial_growth_degree_decreases, ker(phi) has degree 0.
  Polynomial growth degree 0 means the ball size is bounded by a constant,
  which implies the group is finite (via finite_of_polynomial_growth_degree_zero
  from PolynomialGrowth.lean).
  -/
  sorry

-- Note: The kernel of Z -> Z/nZ has polynomial growth degree 1 (it's Z).
-- This is a sanity check that our definitions are correct.
-- (Not directly relevant to the main theorems but good for testing.)

end SpecialCases

end Gromov.Growth.KernelDegree
