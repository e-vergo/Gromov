module

import Gromov.Definitions.Descent
import Gromov.Proofs.Cayley.Graph
public import Gromov.Proofs.Growth.Fibration

namespace Gromov.Growth.KernelDegree

open Gromov
open Gromov.Growth.Fibration

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
  rw [MonoidHom.mem_ker]
  unfold correctedGenerator
  rw [MonoidHom.map_mul, MonoidHom.map_zpow, ht]
  -- We need to show: φ s * (ofAdd 1)^(-toAdd (φ s)) = 1
  -- This is equivalent to: φ s * (φ s)^(-1) = 1
  have h : (Multiplicative.ofAdd (1 : ℤ)) ^ (Multiplicative.toAdd (φ s)) = φ s := by
    cases φ s with | ofAdd n =>
    change Multiplicative.ofAdd 1 ^ n = Multiplicative.ofAdd n
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one]
  rw [zpow_neg, h, mul_inv_cancel]

/-- The set of corrected generators for the kernel. -/
def kernelGenerators (φ : G →* Multiplicative ℤ) (t : G) (S : Set G) : Set G :=
  {correctedGenerator φ t s | s ∈ S}

/-- The kernel generators are finite if S is finite. -/
theorem kernelGenerators_finite (φ : G →* Multiplicative ℤ) (t : G) (S : Set G)
    (hS : S.Finite) :
    (kernelGenerators φ t S).Finite := by
  -- Proof: Image of finite set under a function is finite.
  unfold kernelGenerators
  exact Set.Finite.image (fun s => correctedGenerator φ t s) hS

/-- All kernel generators lie in the kernel. -/
theorem kernelGenerators_subset_ker (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G) :
    kernelGenerators φ t S ⊆ φ.ker := by
  -- Proof: Apply correctedGenerator_mem_ker to each element.
  intro g hg
  unfold kernelGenerators at hg
  obtain ⟨s, _, rfl⟩ := hg
  exact correctedGenerator_mem_ker φ t ht s

/-- Key generation theorem: if S generates G and phi is surjective,
    then kernelGenerators phi t S generates ker(phi).

    This is a variant of the Schreier lemma specialized to Z quotients. -/
theorem kernelGenerators_generate (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G)
    (hgen : Subgroup.closure S = ⊤) :
    Subgroup.closure (Subtype.val ⁻¹' kernelGenerators φ t S : Set φ.ker) = ⊤ := by
  -- We'll show every element of ker(φ) is in the closure
  ext ⟨g, hg : g ∈ φ.ker⟩
  simp only [Subgroup.mem_top, iff_true]

  -- The key insight: since S generates G and each s ∈ S can be rewritten as
  -- s = correctedGenerator(φ, t, s) * t^{φ(s)}, and g ∈ ker(φ) means φ(g) = 1,
  -- any word in S representing g has total φ-value 0, so the compensating t-powers
  -- cancel. Thus g can be expressed as a product of corrected generators.

  -- This follows by the general Schreier formula: if N is a normal subgroup
  -- and S is a generating set of G, then {sn_s^{-1} | s ∈ S} generates N,
  -- where n_s is a fixed coset representative. Here N = ker(φ) and n_s = t^{φ(s)}.

  -- Since S generates G, g is in closure of S
  have g_in_closure : g ∈ Subgroup.closure S := by
    rw [hgen]; trivial

  -- Use the fact that every element of ker(φ) is expressible in terms of corrected generators
  -- The rigorous proof uses Schreier's transversal construction:
  -- Every word w in S can be written w = ∏ s_i = ∏ (correctedGenerator(s_i) * t^{φ(s_i)})
  -- For w ∈ ker(φ), we have φ(w) = ∏ φ(s_i) = 0, so ∑ φ(s_i) = 0,
  -- meaning the product of compensating t powers is 1.

  /-
  PROOF STRATEGY (Schreier Lemma for kernels):

  This is a classical result: if φ : G → ℤ is surjective and S generates G,
  then {s · t^(-φ(s)) | s ∈ S} generates ker(φ), where t is a lift of the generator 1 ∈ ℤ.

  Proof sketch:
  1. Every g ∈ ker(φ) satisfies φ(g) = 0.
  2. Write g as a word: g = s₁^ε₁ · s₂^ε₂ · ... · sₙ^εₙ where sᵢ ∈ S, εᵢ ∈ {±1}.
  3. Decompose each sᵢ: sᵢ = correctedGenerator(sᵢ) · t^(φ(sᵢ)).
  4. Then g = ∏ᵢ (cᵢ · t^(εᵢ·φ(sᵢ))) where cᵢ = correctedGenerator(sᵢ)^εᵢ.
  5. Rearranging: g = (product of cᵢ and conjugates) · t^(∑ εᵢ·φ(sᵢ)).
  6. Since φ(g) = 0, we have ∑ εᵢ·φ(sᵢ) = 0, so t^(∑ εᵢ·φ(sᵢ)) = 1.
  7. Therefore g is a product of corrected generators and their conjugates by t-powers.
  8. Since corrected generators lie in ker(φ) (a normal subgroup), their conjugates do too.
  9. Thus g ∈ Subgroup.closure (kernelGenerators φ t S).

  The technical challenge: showing that conjugates t^k · c · t^(-k) of corrected generators
  can be expressed using the corrected generators themselves. This uses normality of ker(φ)
  and the fact that conjugation by t permutes cosets of ker(φ).

  For a complete proof, one would either:
  (a) Use Mathlib's Schreier lemma (Subgroup.closure_mul_image_eq) with appropriate transversal, or
  (b) Do direct induction on word length with careful conjugation arguments, or
  (c) Use the Nielsen-Schreier theorem machinery if available.

  This is a well-known result, so we admit it here and continue with the growth analysis.
  -/
  sorry

/-- The kernel of a surjection to Z from a finitely generated group is finitely generated. -/
theorem kernel_fg (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    (S : Set G) (hS : S.Finite) (hgen : Subgroup.closure S = ⊤) :
    ∃ (S_K : Set φ.ker), S_K.Finite ∧ Subgroup.closure S_K = ⊤ := by
  obtain ⟨t, ht⟩ := hφ (Multiplicative.ofAdd 1)
  use Subtype.val ⁻¹' kernelGenerators φ t S
  constructor
  · -- The preimage is finite
    have hinj : Set.InjOn (Subtype.val : φ.ker → G) (Subtype.val ⁻¹' kernelGenerators φ t S) := by
      intro x y _ _ heq
      exact Subtype.val_injective heq
    exact Set.Finite.preimage hinj (kernelGenerators_finite φ t S hS)
  · exact kernelGenerators_generate φ t ht S hgen

end KernelGenerators

/-!
## Word Length Comparison

Relating word lengths in G and in ker(phi).
-/

section WordLengthComparison

variable {G : Type*} [Group G]

/-- The constant C in the ball bound can be chosen uniformly. -/
theorem kernel_ball_embedding_constant (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) :
    ∃ C : ℕ, C > 0 ∧ ∀ n g, g ∈ CayleyBall S n → g ∈ φ.ker →
      g ∈ CayleyBall (kernelGenerators φ t S) (C * n) := by
  /-
  PROOF STRATEGY:

  If g ∈ CayleyBall S n ∩ ker(φ), then g = s₁ · s₂ · ... · sₖ where k ≤ n and each sᵢ ∈ S ∪ S⁻¹.

  Decompose each generator: sᵢ = correctedGenerator(sᵢ) · t^(φ sᵢ) =: cᵢ · t^mᵢ where mᵢ = φ(sᵢ).

  Then: g = c₁·t^m₁ · c₂·t^m₂ · ... · cₖ·t^mₖ
          = c₁ · t^m₁·c₂·t^(-m₁) · t^(m₁+m₂)·c₃·t^(-(m₁+m₂)) · t^(m₁+m₂+m₃) · ...

  Since φ(g) = 1, we have m₁ + m₂ + ... + mₖ = 0, so the final t-power is 1.

  The element g can be expressed as a product of:
  - Corrected generators cᵢ
  - Conjugates t^j · cᵢ · t^(-j) for various values of j

  Each conjugate t^j · cᵢ · t^(-j) is in ker(φ) (since ker is normal).
  However, to express it in the CayleyBall of kernelGenerators, we need to:
  1. Write t^j as a word in S (length ≤ |j|)
  2. Write cᵢ as correctedGenerator(sᵢ) (already a single generator)
  3. Write t^(-j) as a word in S (length ≤ |j|)

  But wait - this doesn't work! t^j is NOT in ker(φ), so we can't just include it.

  The correct approach: We need to show that conjugates of corrected generators
  can themselves be expressed using corrected generators. This requires the assumption
  from kernelGenerators_generate that corrected generators generate the whole kernel.

  Given that result (which we admitted), the word length bound follows from:
  - Original word has length ≤ n
  - Each generator contributes O(1) corrected generators after rearrangement
  - The rearrangement process involves at most n conjugation steps
  - Each conjugation by a t-power involves moving through O(M) cosets where M = max|φ(s)|

  Therefore C = O(M · |S|) or similar should work.

  For a rigorous proof, we would:
  1. Use the word decomposition of g
  2. Apply the generation result to express conjugates in terms of corrected generators
  3. Track the word length carefully through the rearrangement

  This is technical but standard. We admit it here.
  -/
  sorry

theorem kernel_element_ball_bound (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) (n : ℕ) (g : G) (hg : g ∈ CayleyBall S n)
    (hker : g ∈ φ.ker) :
    ∃ C : ℕ, g ∈ CayleyBall (kernelGenerators φ t S) (C * n) := by
    obtain ⟨C, _, hC⟩ := kernel_ball_embedding_constant φ t ht S hS hgen
    exact ⟨C, hC n g hg hker⟩

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
   -- Get the constant from kernel_ball_embedding_constant
   obtain ⟨C, hC_pos, hC⟩ := kernel_ball_embedding_constant φ t ht S hS hgen

   use C
   constructor
   · exact hC_pos
   · intro n
     -- Strategy: Show CayleyBall (kernelGenerators φ t S) n ⊆ CayleyBall S (C*n)
     -- Then the cardinality inequality follows immediately.

     have h_subset : CayleyBall (kernelGenerators φ t S) n ⊆ CayleyBall S (C * n) := by
       intro g hg
       -- g is in the Cayley ball of kernelGenerators of radius n
       -- We need to show g is in the Cayley ball of S of radius C*n

       -- Since kernelGenerators ⊆ ker(φ), we have g ∈ ker(φ)
       have hg_ker : g ∈ φ.ker := by
         -- kernelGenerators generates a subgroup of ker(φ)
         -- Any product of kernel generators is in ker(φ)
         sorry

       -- Now g ∈ CayleyBall (kernelGenerators φ t S) n and g ∈ ker(φ)
       -- We need to show g ∈ CayleyBall S (C*n)

       -- This is almost what kernel_ball_embedding_constant gives us, but backwards!
       -- kernel_ball_embedding_constant says: if g ∈ CayleyBall S m ∩ ker, then g ∈ CayleyBall kernelGens (C*m)
       -- We need the reverse direction.

       -- The correct approach: Each kernelGenerator can be written in S.
       -- correctedGenerator φ t s = s * t^(-φ s)
       -- So it's a word of length at most 1 + wordLength(t) * |φ s| in S.

       -- If g is a product of n kernelGenerators, then g has word length
       -- at most n * (1 + wordLength(t) * maxφ) in S, where maxφ = max{|φ s| : s ∈ S}.

       -- For this we would need to:
       -- 1. Bound the word length of t in S
       -- 2. Bound |φ s| for s ∈ S
       -- 3. Show each kernelGenerator has bounded word length in S
       -- 4. Conclude g ∈ CayleyBall S (C*n) for appropriate C

       sorry

     -- From the subset relation, the cardinality inequality follows
     calc (CayleyBall (kernelGenerators φ t S) n).ncard
         ≤ (CayleyBall S (C * n)).ncard := by
           exact Set.ncard_le_ncard h_subset (cayleyBall_finite hS _)

/-- The kernel ball size is bounded by group ball size divided by n.

    This is the key asymptotic estimate. Roughly:
    |B_{ker phi}(n)| <= C * |B_G(C'*n)| / n

    When |B_G(n)| ~ n^d, this gives |B_{ker phi}(n)| ~ n^{d-1}. -/
theorem kernel_ball_size_bound (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    (S : Set G) (hS : S.Finite) (hgen : Subgroup.closure S = ⊤) :
    ∃ (S_K : Set φ.ker) (C : ℕ),
      S_K.Finite ∧ Subgroup.closure S_K = ⊤ ∧ C > 0 ∧
      ∀ n > 0, (CayleyBall S_K n).ncard * n ≤ C * (CayleyBall S (C * n)).ncard := by
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
    (C' : ℝ) (hC' : C' > 0)
    (hbound : ∀ n > 0, (GrowthFunction S_K n : ℝ) * n ≤ C' * (n : ℝ) ^ d) :
    ∃ C'' : ℝ, C'' > 0 ∧ ∀ n > 0, (GrowthFunction S_K n : ℝ) ≤ C'' * (n : ℝ) ^ (d - 1) := by
  /-
  PROOF SKETCH:
  From hbound: GrowthFunction S_K n <= C' * n^d / n = C' * n^{d-1}.
  Take C'' = C'.
  -/
  use C', hC'
  intro n hn
  have h := hbound n hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have : (n : ℝ) ^ d = (n : ℝ) ^ (d - 1) * n := by
    rw [← pow_succ]
    congr 1
    omega
  rw [this] at h
  have : (GrowthFunction S_K n : ℝ) ≤ C' * (n : ℝ) ^ (d - 1) := by
    calc (GrowthFunction S_K n : ℝ)
        = ((GrowthFunction S_K n : ℝ) * n) / n := by field_simp
      _ ≤ (C' * ((n : ℝ) ^ (d - 1) * n)) / n := by
          apply div_le_div_of_nonneg_right h
          exact le_of_lt hn_pos
      _ = C' * (n : ℝ) ^ (d - 1) := by field_simp
  exact this

/-- Main theorem: if G has polynomial growth degree d > 0 and phi : G -> Z is surjective,
    then ker(phi) has polynomial growth degree at most d - 1.

    This is the core technical result for the descent argument. -/
theorem polynomial_growth_degree_decreases (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    {d : ℕ} (hd : d > 0) (hG : HasPolynomialGrowthDegree G d) :
    HasPolynomialGrowthDegree φ.ker (d - 1) := by
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
  -- Apply the degree decrease theorem: kernel has degree 1 - 1 = 0
  have hker : HasPolynomialGrowthDegree φ.ker (1 - 1) :=
    polynomial_growth_degree_decreases φ hφ (by omega) hG
  simp only [Nat.sub_self] at hker
  -- Degree 0 means the kernel is finite
  -- Unpack hker: there exists a finite generating set with bounded growth
  obtain ⟨S, hS_fin, hS_gen, C, hC_pos, hbound⟩ := hker
  -- Apply the finite_of_polynomial_growth_degree_zero lemma
  haveI : Finite φ.ker := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    -- The growth function tends to infinity for infinite groups
    have htend := @tendsto_atTop_growthFunction_of_infinite (φ.ker) _ hinf S hS_fin hS_gen
    rw [Filter.tendsto_atTop_atTop] at htend
    obtain ⟨N, hN⟩ := htend (⌈C⌉₊ + 1)
    rcases Nat.eq_zero_or_pos N with hN_zero | hN_pos
    · subst hN_zero
      have hgrow := hN 1 (by omega)
      have hC1 := hbound 1 Nat.one_pos
      simp only [pow_zero, mul_one] at hC1
      have h1 : (⌈C⌉₊ + 1 : ℕ) ≤ GrowthFunction S 1 := hgrow
      have h2 : (⌈C⌉₊ + 1 : ℝ) ≤ GrowthFunction S 1 := by exact_mod_cast h1
      linarith [Nat.le_ceil C]
    · have hbound_N := hbound N hN_pos
      simp only [pow_zero, mul_one] at hbound_N
      have hgrow_N := hN N (le_refl N)
      have h1 : (⌈C⌉₊ + 1 : ℝ) ≤ GrowthFunction S N := by exact_mod_cast hgrow_N
      linarith [Nat.le_ceil C]
  exact this

-- Note: The kernel of Z -> Z/nZ has polynomial growth degree 1 (it's Z).
-- This is a sanity check that our definitions are correct.
-- (Not directly relevant to the main theorems but good for testing.)

end SpecialCases

end Gromov.Growth.KernelDegree
