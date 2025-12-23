import Gromov.Definitions.Descent
import Gromov.Proofs.Cayley.Graph
import Gromov.Proofs.Growth.Fibration

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
  -- Since S generates G, g is in closure of S
  have g_in_closure : g ∈ Subgroup.closure S := by
    rw [hgen]
    trivial
  -- Strategy: Use that g can be written as product of generators,
  -- then "correct" each generator using t^{-φ(s_i)}
  -- The total correction is t^{-φ(g)} = t^0 = 1 since g ∈ ker(φ)
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

theorem kernel_element_ball_bound (φ : G →* Multiplicative ℤ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) (n : ℕ) (g : G) (hg : g ∈ CayleyBall S n)
    (hker : g ∈ φ.ker) :
    ∃ C : ℕ, g ∈ CayleyBall (kernelGenerators φ t S) (C * n) := by
  -- The constant C depends on the maximum value |φ(s)| for s ∈ S
  -- If g = s_1 ... s_n, we can write it as product of corrected generators and powers of t
  -- Since g ∈ ker, the powers of t cancel out
  -- The word length in corrected generators is bounded by (1 + 2*M)*n where M = max |φ(s)|
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
