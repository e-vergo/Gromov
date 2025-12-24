/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Schreier lemma specialized for kernels of homomorphisms to ℤ.

This file develops the specific form of Schreier's lemma needed for the
descent argument in Gromov's theorem. When G maps surjectively to ℤ,
the kernel K = ker(φ) is a finite-index subgroup, and we construct
explicit generators.

## Main results

* `correctedGenerator_in_kernel` - Schreier-type generators lie in the kernel
* `kernelGenerators_generate` - These generators generate the kernel
* `kernel_wordLength_vs_parent` - Word length bounds for kernel elements

## References

* Schreier, O. "Die Untergruppen der freien Gruppen" (1927)
* Lyndon & Schupp, "Combinatorial Group Theory" (1977)
-/

module

public import Gromov.Proofs.Schreier.WordBounds
public import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Gromov.Schreier.KernelGeneration

public section

open Subgroup Gromov.Schreier
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Kernel Generators -/

section KernelGenerators

variable (φ : G →* Multiplicative ℤ)

/-- A choice of element t with φ(t) = ofAdd 1. This generates the transversal. -/
noncomputable def transversalGenerator (hφ : Function.Surjective φ) : G :=
  (hφ (Multiplicative.ofAdd 1)).choose

theorem transversalGenerator_spec (hφ : Function.Surjective φ) :
    φ (transversalGenerator φ hφ) = Multiplicative.ofAdd 1 :=
  (hφ (Multiplicative.ofAdd 1)).choose_spec

/-- For each generator s, the corrected generator s · t^{-φ(s)} lies in ker(φ). -/
def correctedGenerator (t : G) (s : G) : G :=
  s * t ^ (-(Multiplicative.toAdd (φ s)))

/-- The corrected generator lies in the kernel. -/
theorem correctedGenerator_in_kernel (t : G) (ht : φ t = Multiplicative.ofAdd 1) (s : G) :
    correctedGenerator φ t s ∈ MonoidHom.ker φ := by
  simp only [correctedGenerator, MonoidHom.mem_ker, map_mul, map_zpow, ht]
  -- Goal: φ s * Multiplicative.ofAdd 1 ^ (-toAdd (φ s)) = 1
  sorry

/-- The set of kernel generators from a generating set S. -/
def kernelGenerators (S : Set G) (t : G) : Set G :=
  { g | ∃ s ∈ S, g = correctedGenerator φ t s }

/-- Kernel generators are symmetric when S is symmetric. -/
theorem kernelGenerators_symmetric (S : Set G) (hS_sym : S⁻¹ = S) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) :
    (kernelGenerators φ S t)⁻¹ = kernelGenerators φ S t := by
  sorry

/-- The kernel generators generate ker(φ) when S generates G.
    This is the key generation result. -/
theorem kernelGenerators_generate (S : Set G) (hS : closure S = ⊤) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) :
    closure (kernelGenerators φ S t) = MonoidHom.ker φ := by
  sorry

/-- Cardinality bound on kernel generators. -/
theorem kernelGenerators_card (S : Finset G) (t : G) :
    (kernelGenerators φ (S : Set G) t).ncard ≤ S.card := by
  sorry

end KernelGenerators

/-! ## Transversal Structure -/

section Transversal

variable (φ : G →* Multiplicative ℤ) (hφ : Function.Surjective φ)

/-- Powers of t form a complete set of coset representatives for ker(φ). -/
def zpowTransversal (t : G) : Set G :=
  Set.range (fun n : ℤ => t ^ n)

/-- The zpow transversal is indeed a transversal. -/
theorem zpowTransversal_isTransversal (t : G) (ht : φ t = Multiplicative.ofAdd 1) :
    ∀ g : G, ∃! n : ℤ, g * (t ^ n)⁻¹ ∈ MonoidHom.ker φ := by
  intro g
  use Multiplicative.toAdd (φ g)
  sorry

/-- Section map: given g, return the power n such that g · t^{-n} ∈ ker(φ). -/
noncomputable def transversalSection (t : G) (g : G) : ℤ :=
  Multiplicative.toAdd (φ g)

/-- The section has the expected property. -/
theorem transversalSection_spec (t : G) (ht : φ t = Multiplicative.ofAdd 1) (g : G) :
    g * (t ^ (transversalSection φ t g))⁻¹ ∈ MonoidHom.ker φ := by
  simp only [transversalSection, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, ht]
  sorry

/-- Every element decomposes as (kernel element) × (transversal element). -/
theorem element_decomposition (t : G) (ht : φ t = Multiplicative.ofAdd 1) (g : G) :
    ∃ k ∈ MonoidHom.ker φ, ∃ n : ℤ, g = k * t ^ n := by
  let n := Multiplicative.toAdd (φ g)
  let k := g * (t ^ n)⁻¹
  use k
  constructor
  · sorry
  · use n
    simp only [k]
    group

end Transversal

/-! ## Word Length Bounds -/

section WordLengthBounds

variable (S : Set G) [Fintype S] (φ : G →* Multiplicative ℤ)

/-- Bound on the φ-value of generators. -/
noncomputable def generatorPhiBound : ℕ :=
  Finset.sup Finset.univ (fun s : S => (Multiplicative.toAdd (φ s.val)).natAbs)

/-- Word length bound for a corrected generator. -/
theorem kernelGenerator_wordLength (t : G) (ht : φ t = Multiplicative.ofAdd 1) (s : G) (hs : s ∈ S) :
    ∃ n ≤ 1 + generatorPhiBound S φ,
      correctedGenerator φ t s ∈ Gromov.CayleyBall (kernelGenerators φ (S : Set G) t) n := by
  sorry

/-- Key bound: word length in kernel generators ≤ C × word length in parent generators.
    This is crucial for the growth comparison. -/
theorem kernel_wordLength_vs_parent (hφ : Function.Surjective φ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1)
    (k : G) (hk : k ∈ MonoidHom.ker φ) (n : ℕ)
    (hk_word : k ∈ Gromov.CayleyBall S n) :
    k ∈ Gromov.CayleyBall (kernelGenerators φ (S : Set G) t)
        (n * (1 + 2 * generatorPhiBound S φ)) := by
  sorry

/-- The kernel ball embeds into a parent ball with linear scaling. -/
theorem kernel_ball_embedding (hφ : Function.Surjective φ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1) (n : ℕ) :
    let C := 1 + 2 * generatorPhiBound S φ
    Gromov.CayleyBall S n ∩ MonoidHom.ker φ ⊆
      Gromov.CayleyBall (kernelGenerators φ (S : Set G) t) (C * n) := by
  sorry

end WordLengthBounds

/-! ## Word Decomposition -/

section WordDecomposition

variable (S : Set G) [Fintype S] (φ : G →* Multiplicative ℤ)

/-- A word in S can be decomposed into kernel and transversal parts.
    This is the Schreier rewriting process. -/
theorem word_decomposition (hφ : Function.Surjective φ) (t : G)
    (ht : φ t = Multiplicative.ofAdd 1)
    (l : List G) (hl : ∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S) :
    ∃ (k : G) (n : ℤ), k ∈ MonoidHom.ker φ ∧
      l.prod = k * t ^ n ∧
      k ∈ Gromov.CayleyBall (kernelGenerators φ (S : Set G) t)
          (l.length * (1 + 2 * generatorPhiBound S φ)) := by
  sorry

/-- The φ-value of a product equals sum of φ-values. -/
theorem phi_list_prod (l : List G) :
    Multiplicative.toAdd (φ l.prod) = (l.map (fun g => Multiplicative.toAdd (φ g))).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    sorry

/-- Bound on φ-value of elements in a Cayley ball. -/
theorem phi_cayleyBall_bound (g : G) (n : ℕ) (hg : g ∈ Gromov.CayleyBall S n) :
    (Multiplicative.toAdd (φ g)).natAbs ≤ n * generatorPhiBound S φ := by
  sorry

end WordDecomposition

end

end Gromov.Schreier.KernelGeneration
