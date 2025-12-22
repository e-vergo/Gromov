module

public import Gromov.Proofs.Cayley.Graph
public import Gromov.Definitions.Harmonic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Module.Basic

namespace Gromov

public section

open scoped NNReal

variable {G : Type*} [Group G]

/-! ## Harmonic Functions on Groups

A function f : G → ℝ is harmonic with respect to a finite symmetric generating set S if
at every point g, the value f(g) equals the average of f over the neighbors of g in the
Cayley graph. For a symmetric generating set, this means:

  sum over s in S of f(g * s) = |S| * f(g)

For a general generating set where we use both s and s^(-1) as edges:

  sum over s in S of (f(g * s) + f(g * s^(-1))) = 2 * |S| * f(g)
-/

section Harmonic

variable (S : Set G)

/-- For symmetric generating sets, the two definitions of harmonic coincide -/
theorem isHarmonic_iff_isHarmonicSymmetric [Fintype S] (hS : Gromov.IsSymmetric S) (f : G → ℝ) :
    IsHarmonic S f ↔ IsHarmonicSymmetric S f := by
  constructor
  · intro hf g
    have h := hf g
    have hsum : ∑ s : S, f (g * s.val⁻¹) = ∑ s : S, f (g * s.val) := by
      let invEquiv : S ≃ S := {
        toFun := fun s => ⟨s.val⁻¹, hS s.val s.prop⟩
        invFun := fun s => ⟨s.val⁻¹, hS s.val s.prop⟩
        left_inv := fun s => by simp
        right_inv := fun s => by simp
      }
      rw [← Equiv.sum_comp invEquiv]
      congr 1
      ext s
      simp [invEquiv]
    have heq : ∑ s : S, (f (g * s.val) + f (g * s.val⁻¹)) =
               ∑ s : S, f (g * s.val) + ∑ s : S, f (g * s.val⁻¹) := Finset.sum_add_distrib
    rw [heq, hsum] at h
    linarith
  · intro hf g
    have hsum : ∑ s : S, f (g * s.val⁻¹) = ∑ s : S, f (g * s.val) := by
      let invEquiv : S ≃ S := {
        toFun := fun s => ⟨s.val⁻¹, hS s.val s.prop⟩
        invFun := fun s => ⟨s.val⁻¹, hS s.val s.prop⟩
        left_inv := fun s => by simp
        right_inv := fun s => by simp
      }
      rw [← Equiv.sum_comp invEquiv]
      congr 1
      ext s
      simp [invEquiv]
    have heq : ∑ s : S, (f (g * s.val) + f (g * s.val⁻¹)) =
               ∑ s : S, f (g * s.val) + ∑ s : S, f (g * s.val⁻¹) := Finset.sum_add_distrib
    rw [heq, hsum]
    have := hf g
    linarith

/-- Constant functions are harmonic -/
theorem isHarmonic_const [Fintype S] (c : ℝ) : IsHarmonic S (fun _ => c) := by
  intro g
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The zero function is harmonic -/
theorem isHarmonic_zero [Fintype S] : IsHarmonic S (0 : G → ℝ) := by
  intro g
  simp only [Pi.zero_apply, add_zero, Finset.sum_const_zero, mul_zero]

/-- Scalar multiples of harmonic functions are harmonic -/
theorem isHarmonic_smul [Fintype S] {f : G → ℝ} (hf : IsHarmonic S f) (c : ℝ) :
    IsHarmonic S (c • f) := by
  intro g
  simp only [Pi.smul_apply, smul_eq_mul]
  have := hf g
  have heq : ∑ s : S, (c * f (g * s.val) + c * f (g * s.val⁻¹)) =
             c * ∑ s : S, (f (g * s.val) + f (g * s.val⁻¹)) := by
    rw [Finset.mul_sum]
    congr 1
    ext s
    ring
  rw [heq, this]
  ring

/-- Sums of harmonic functions are harmonic -/
theorem isHarmonic_add [Fintype S] {f₁ f₂ : G → ℝ}
    (hf₁ : IsHarmonic S f₁) (hf₂ : IsHarmonic S f₂) :
    IsHarmonic S (f₁ + f₂) := by
  intro g
  simp only [Pi.add_apply]
  have h1 := hf₁ g
  have h2 := hf₂ g
  have heq : ∑ s : S, ((f₁ (g * s.val) + f₂ (g * s.val)) +
                       (f₁ (g * s.val⁻¹) + f₂ (g * s.val⁻¹))) =
             ∑ s : S, (f₁ (g * s.val) + f₁ (g * s.val⁻¹)) +
             ∑ s : S, (f₂ (g * s.val) + f₂ (g * s.val⁻¹)) := by
    rw [← Finset.sum_add_distrib]
    congr 1
    ext s
    ring
  rw [heq, h1, h2]
  ring

/-- Negation of harmonic functions is harmonic -/
theorem isHarmonic_neg [Fintype S] {f : G → ℝ} (hf : IsHarmonic S f) :
    IsHarmonic S (-f) := by
  have h : -f = (-1 : ℝ) • f := by ext x; simp
  rw [h]
  exact isHarmonic_smul S hf (-1)

/-- Difference of harmonic functions is harmonic -/
theorem isHarmonic_sub [Fintype S] {f₁ f₂ : G → ℝ}
    (hf₁ : IsHarmonic S f₁) (hf₂ : IsHarmonic S f₂) :
    IsHarmonic S (f₁ - f₂) := by
  have h : f₁ - f₂ = f₁ + (-f₂) := by ext; ring_nf
  rw [h]
  exact isHarmonic_add S hf₁ (isHarmonic_neg S hf₂)

end Harmonic

/-! ## Lipschitz Functions with respect to Word Metric -/

section Lipschitz

variable (S : Set G)

/-- Constant functions are 0-Lipschitz -/
theorem isWordLipschitz_const (c : ℝ) : IsWordLipschitz S 0 (fun _ => c) := by
  intro g h
  simp

/-- If f is L-Lipschitz and L ≤ L', then f is L'-Lipschitz -/
theorem IsWordLipschitz.mono {L L' : ℝ} {f : G → ℝ}
    (hf : IsWordLipschitz S L f) (hL : L ≤ L') :
    IsWordLipschitz S L' f := by
  intro g h
  calc |f g - f h| ≤ L * (wordDist S g h : ℝ) := hf g h
    _ ≤ L' * (wordDist S g h : ℝ) := by
        apply mul_le_mul_of_nonneg_right hL
        exact Nat.cast_nonneg _

/-- Scalar multiples of Lipschitz functions are Lipschitz -/
theorem IsWordLipschitz.smul {L : ℝ} {f : G → ℝ} (hf : IsWordLipschitz S L f) (c : ℝ) :
    IsWordLipschitz S (|c| * L) (c • f) := by
  intro g h
  simp only [Pi.smul_apply, smul_eq_mul]
  calc |c * f g - c * f h| = |c| * |f g - f h| := by rw [← mul_sub, abs_mul]
    _ ≤ |c| * (L * (wordDist S g h : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (hf g h) (abs_nonneg c)
    _ = (|c| * L) * (wordDist S g h : ℝ) := by ring

/-- Sums of Lipschitz functions are Lipschitz -/
theorem IsWordLipschitz.add {L₁ L₂ : ℝ} {f₁ f₂ : G → ℝ}
    (hf₁ : IsWordLipschitz S L₁ f₁) (hf₂ : IsWordLipschitz S L₂ f₂) :
    IsWordLipschitz S (L₁ + L₂) (f₁ + f₂) := by
  intro g h
  simp only [Pi.add_apply]
  have h1 : |(f₁ g - f₁ h) + (f₂ g - f₂ h)| ≤ |f₁ g - f₁ h| + |f₂ g - f₂ h| := abs_add_le _ _
  calc |f₁ g + f₂ g - (f₁ h + f₂ h)|
      = |(f₁ g - f₁ h) + (f₂ g - f₂ h)| := by ring_nf
    _ ≤ |f₁ g - f₁ h| + |f₂ g - f₂ h| := h1
    _ ≤ L₁ * (wordDist S g h : ℝ) + L₂ * (wordDist S g h : ℝ) := add_le_add (hf₁ g h) (hf₂ g h)
    _ = (L₁ + L₂) * (wordDist S g h : ℝ) := by ring

/-- Negation of Lipschitz functions is Lipschitz -/
theorem IsWordLipschitz.neg {L : ℝ} {f : G → ℝ} (hf : IsWordLipschitz S L f) :
    IsWordLipschitz S L (-f) := by
  intro g h
  simp only [Pi.neg_apply, neg_sub_neg]
  rw [abs_sub_comm]
  exact hf g h

end Lipschitz

/-! ## Space of Lipschitz Harmonic Functions -/

section LipschitzHarmonicSpace

variable (S : Set G) [Fintype S]

/-- The zero function is in any Lipschitz harmonic space (for L ≥ 0) -/
theorem zero_mem_lipschitzHarmonicSpace {L : ℝ} (hL : 0 ≤ L) :
    (0 : G → ℝ) ∈ LipschitzHarmonicSpace S L := by
  constructor
  · exact isHarmonic_zero S
  · intro g h
    simp only [Pi.zero_apply, sub_self, abs_zero]
    exact mul_nonneg hL (Nat.cast_nonneg _)

/-- Scalar multiples preserve membership in Lipschitz harmonic space (with adjusted constant) -/
theorem smul_mem_lipschitzHarmonicSpace {L : ℝ} {f : G → ℝ}
    (hf : f ∈ LipschitzHarmonicSpace S L) (c : ℝ) :
    (c • f) ∈ LipschitzHarmonicSpace S (|c| * L) := by
  constructor
  · exact isHarmonic_smul S hf.1 c
  · exact IsWordLipschitz.smul S hf.2 c

/-- Addition preserves membership in Lipschitz harmonic space (with adjusted constant) -/
theorem add_mem_lipschitzHarmonicSpace {L₁ L₂ : ℝ} {f₁ f₂ : G → ℝ}
    (hf₁ : f₁ ∈ LipschitzHarmonicSpace S L₁) (hf₂ : f₂ ∈ LipschitzHarmonicSpace S L₂) :
    (f₁ + f₂) ∈ LipschitzHarmonicSpace S (L₁ + L₂) := by
  constructor
  · exact isHarmonic_add S hf₁.1 hf₂.1
  · exact IsWordLipschitz.add S hf₁.2 hf₂.2

/-- Constants are in the Lipschitz harmonic space for any L ≥ 0 -/
theorem const_mem_lipschitzHarmonicSpace {L : ℝ} (hL : 0 ≤ L) (c : ℝ) :
    (fun _ => c) ∈ LipschitzHarmonicSpace S L := by
  constructor
  · exact isHarmonic_const S c
  · intro g h
    simp only [sub_self, abs_zero]
    exact mul_nonneg hL (Nat.cast_nonneg _)

end LipschitzHarmonicSpace

/-! ## Submodule Structure

We can also view the Lipschitz harmonic space as a submodule when using a fixed Lipschitz bound.
For the Gromov theorem proof, one typically works with a fixed L and shows finite-dimensionality.
-/

section Submodule

variable (S : Set G) [Fintype S]

/-- Harmonic functions form a submodule of G → ℝ -/
def harmonicSubmodule : Submodule ℝ (G → ℝ) where
  carrier := {f | IsHarmonic S f}
  add_mem' := fun ha hb => isHarmonic_add S ha hb
  zero_mem' := isHarmonic_zero S
  smul_mem' := fun c _ hf => isHarmonic_smul S hf c

/-- Membership in harmonicSubmodule is equivalent to IsHarmonic -/
theorem mem_harmonicSubmodule (f : G → ℝ) :
    f ∈ harmonicSubmodule S ↔ IsHarmonic S f := Iff.rfl

end Submodule

end

end Gromov
