module

public import Gromov.Proofs.Harmonic.Spectral
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Sequences

namespace Gromov.Harmonic.Existence

public section

open scoped NNReal BigOperators
open Gromov Gromov.Harmonic.Spectral

variable {G : Type*} [Group G] [DecidableEq G]

/-! ## Cesaro Averages

The Cesaro average of the random walk measures provides asymptotically harmonic
functions. For a probability measure mu on G (uniform on generating set S),
define f_n = (1/n) * sum_{m=1}^n (mu^{*m} * f) where * denotes convolution.
-/

section CesaroAverages

variable (S : Set G) [Fintype S]

/-- The n-th convolution power of the uniform measure on S applied to a function.
    This represents averaging f over all paths of length n from the identity. -/
noncomputable def ConvolutionPower (n : ℕ) (f : G → ℝ) : G → ℝ :=
  MarkovPower S n f

/-- The Cesaro average of convolution powers: f_n = (1/n) * sum_{m=1}^n (mu^{*m} * f).
    This is a regularization that becomes asymptotically harmonic. -/
noncomputable def CesaroAverage (n : ℕ) (f : G → ℝ) : G → ℝ :=
  if n = 0 then f
  else fun x => (1 / n) * ∑ m ∈ Finset.range n, ConvolutionPower S (m + 1) f x

/-- The defect from harmonicity: how far f_n is from being harmonic.
    Measured in L^1 norm over finite support. -/
noncomputable def HarmonicDefect (f : G → ℝ) (support : Finset G) : ℝ :=
  ∑ x ∈ support, |DiscreteLaplacian S f x|

omit [DecidableEq G] in
/-- Cesaro averages are asymptotically harmonic: the harmonic defect goes to 0.
    More precisely, ||f_n - A(f_n)||_{L^1} = O(1/n) where A is averaging. -/
theorem cesaro_asymptotically_harmonic (hS_nonempty : S.Nonempty) (f : G → ℝ)
    (support : Finset G) (hf : ∀ x, x ∉ support → f x = 0) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      HarmonicDefect S (CesaroAverage S n f) support ≤ ε := by
  -- Proof outline:
  -- 1. Expand CesaroAverage: f_n(x) = (1/n) ∑_{m=1}^n (mu^{*m} * f)(x)
  -- 2. The harmonic defect satisfies: Δf_n = (1/n)(f - mu^{*n} * f)
  -- 3. Since f has finite support, |f - mu^{*n} * f| is uniformly bounded by 2||f||_∞
  -- 4. Therefore ||Δf_n||_{L^1} ≤ C/n for some constant C depending on support size
  -- 5. Choose N = ⌈C/ε⌉
  -- Missing infrastructure: properties of convolution powers, bounds on Markov operator
  sorry

omit [DecidableEq G] in
/-- The Cesaro average preserves the Lipschitz property (with same constant).
    Requires S to be symmetric. -/
theorem cesaro_preserves_lipschitz (hS : Gromov.IsSymmetric S) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (f : G → ℝ)
    (hf : IsWordLipschitz S L f) :
    IsWordLipschitz S L (CesaroAverage S n f) := by
  -- First show that MarkovPower m preserves Lipschitz for any m
  have markov_preserves : ∀ m : ℕ, IsWordLipschitz S L (MarkovPower S m f) := by
    intro m
    induction m with
    | zero =>
      -- MarkovPower 0 = id, so (MarkovPower 0 f) = f
      intro x y
      -- Goal: |(MarkovPower S 0 f) x - (MarkovPower S 0 f) y| ≤ L * wordDist x y
      -- But MarkovPower 0 is defined inductively, need to show it equals f
      sorry
    | succ m' ih =>
      -- MarkovPower (m'+1) = MarkovPower m' ∘ AveragingOperator
      -- Need: AveragingOperator preserves Lipschitz
      sorry
  -- Now show CesaroAverage preserves Lipschitz
  intro x y
  unfold CesaroAverage
  by_cases hn : n = 0
  · simp [hn]
    exact hf x y
  · simp [hn]
    -- Need to show: |(1/n) * Σ_{m ∈ range n} ConvolutionPower S (m+1) f x - (1/n) * Σ_{m ∈ range n} ConvolutionPower S (m+1) f y| ≤ L * wordDist S x y
    -- = |(1/n) * Σ_{m ∈ range n} (ConvolutionPower S (m+1) f x - ConvolutionPower S (m+1) f y)| ≤ L * wordDist S x y
    sorry

end CesaroAverages

/-! ## Existence of Lipschitz Harmonic Functions

For groups with polynomial growth, we construct non-trivial Lipschitz harmonic
functions using a limiting argument on Cesaro averages.
-/

section ExistenceTheorems

variable (S : Set G) [Fintype S]

omit [DecidableEq G] in
/-- For non-amenable groups, there exist non-constant bounded harmonic functions.
    This uses the spectral gap being positive. -/
theorem nonamenable_has_bounded_harmonic (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hGap : SpectralGap S > 0) :
    ∃ (f : G → ℝ), IsHarmonicSymmetric S f ∧ (∃ M, ∀ x, |f x| ≤ M) ∧ ¬(∃ c, f = fun _ => c) := by
  -- Proof outline:
  -- 1. Spectral gap λ > 0 means: ⟨Δf, f⟩ ≥ λ⟨f, f⟩ for all f ⊥ constants
  -- 2. This implies Δ is invertible on the orthogonal complement of constants
  -- 3. Take any non-constant f₀ ∈ l²(G) with f₀ ⊥ constants
  -- 4. Set f = Δ⁻¹f₀, which satisfies Δf = f₀
  -- 5. By spectral theory, ||f||₂ ≤ (1/λ)||f₀||₂, so f ∈ l²(G)
  -- 6. Since G is non-amenable, l²(G) functions can be bounded
  -- Missing infrastructure: l²(G) inner product space structure, spectral theorem,
  -- inverse operator on spectral complement
  sorry

omit [DecidableEq G] in
/-- For amenable groups, we can use spectral projections near eigenvalue 0
    to construct almost-harmonic functions that can be made exactly harmonic
    in a limiting sense. -/
theorem amenable_spectral_projection (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hGap : SpectralGap S = 0) :
    ∀ ε > 0, ∃ (f : G → ℝ), (∃ x, f x ≠ 0) ∧
      ∀ x, |DiscreteLaplacian S f x| ≤ ε * |f x| := by
  -- Proof outline:
  -- 1. Spectral gap = 0 means: inf{⟨Δf, f⟩/⟨f, f⟩ : f ⊥ constants} = 0
  -- 2. For any ε > 0, there exists f ⊥ constants with ⟨Δf, f⟩ < ε⟨f, f⟩
  -- 3. This means ||Δf||₂ ≤ ε||f||₂ (approximately an eigenfunction for eigenvalue ~0)
  -- 4. By Cauchy-Schwarz and l² theory, this implies pointwise bound |Δf(x)| ≤ ε|f(x)|
  -- Missing infrastructure: spectral gap characterization, variational formulation,
  -- approximate eigenfunctions
  sorry

omit [DecidableEq G] in
/-- Main existence theorem: For infinite finitely generated groups with polynomial growth,
    there exists a non-constant Lipschitz harmonic function.

    This is Theorem 2 from Tao's overview of Gromov's theorem. -/
theorem lipschitz_harmonic_exists (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hpoly : HasPolynomialGrowth G) (hInf : Infinite G) :
    ∃ (f : G → ℝ) (L : ℝ), L > 0 ∧ IsHarmonicSymmetric S f ∧ IsWordLipschitz S L f := by
  -- Proof outline:
  -- 1. Start with the word length function f₀(g) = wordLength S g, which is 1-Lipschitz
  -- 2. Form Cesaro averages: f_n = CesaroAverage S n f₀
  -- 3. By cesaro_preserves_lipschitz, each f_n is 1-Lipschitz
  -- 4. The sequence {f_n} is uniformly bounded on balls (by Lipschitz property)
  -- 5. Apply Arzela-Ascoli: extract a locally uniformly convergent subsequence f_{n_k} → f
  -- 6. The limit f is Lipschitz (uniform limit of Lipschitz functions)
  -- 7. The limit f is harmonic (Laplacian is continuous, defect → 0 by cesaro_asymptotic)
  -- 8. Polynomial growth ensures f is non-trivial (growth bounds prevent collapse to constant)
  -- Missing infrastructure: Arzela-Ascoli theorem for metric spaces, locally uniform convergence,
  -- continuity of discrete Laplacian, polynomial growth implications
  sorry

omit [DecidableEq G] in
/-- The Lipschitz harmonic function can be chosen to be non-constant.
    This is crucial for extracting a Z quotient. -/
theorem lipschitz_harmonic_nonconstant (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (hpoly : HasPolynomialGrowth G) (hInf : Infinite G) :
    ∃ (f : G → ℝ) (L : ℝ), L > 0 ∧ IsHarmonicSymmetric S f ∧ IsWordLipschitz S L f ∧
      ¬(∃ c, f = fun _ => c) := by
  -- Proof outline:
  -- 1. Use lipschitz_harmonic_exists to get (f, L) with f harmonic and L-Lipschitz
  -- 2. Need to show f is non-constant
  -- 3. Key observation: if f were constant c, then f₀ (word length) would have
  --    Cesaro averages converging to c
  -- 4. But word length grows linearly along any infinite geodesic ray
  -- 5. Polynomial growth implies existence of such rays
  -- 6. The Cesaro averages of word length along a ray grow unboundedly
  -- 7. Therefore the limit cannot be constant
  -- Missing infrastructure: properties of word length on infinite groups,
  -- geodesic rays, growth along rays
  sorry

end ExistenceTheorems

/-! ## Gradient Bounds

For Lipschitz harmonic functions, we can bound the gradient in terms of values
on larger balls. This is key to the finite-dimensionality argument.
-/

section GradientBounds

variable (S : Set G) [Fintype S]

/-- The discrete gradient of a function at a point.
    Measures the maximum difference with neighbors. -/
noncomputable def DiscreteGradient (f : G → ℝ) (x : G) : ℝ :=
  ⨆ s : S, |f (x * s.val) - f x|

omit [DecidableEq G] in
/-- For a harmonic function, the gradient at x is controlled by the L^infinity
    norm on a ball around x. This is a discrete mean value theorem. -/
theorem harmonic_gradient_bound (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (f : G → ℝ) (hf : IsHarmonicSymmetric S f) (x : G) (R : ℕ) (hR : R > 0) :
    DiscreteGradient S f x ≤
      (2 / R : ℝ) * ⨆ g ∈ CayleyBall S R, |f (x * g)| := by
  -- Proof outline:
  -- 1. Iterate the harmonic condition R times: f(x) = (MarkovPower R)(f)(x)
  --    This expresses f(x) as average over all R-step random walks from x
  -- 2. For each neighbor x*s, similarly f(x*s) = (MarkovPower R)(f)(x*s)
  -- 3. Subtract: |f(x*s) - f(x)| = |avg over R-ball from x*s - avg over R-ball from x|
  -- 4. The R-balls from x and x*s have large overlap (shifted by distance 1)
  -- 5. The difference is bounded by (constant/R) × sup oscillation over combined R+1 ball
  -- 6. Taking supremum over s ∈ S gives the gradient bound
  -- Missing infrastructure: iteration of Markov operator, balls overlap estimates,
  -- quantitative averaging arguments
  sorry

omit [DecidableEq G] in
/-- For a Lipschitz harmonic function, there's a uniform gradient bound. -/
theorem lipschitz_harmonic_uniform_gradient (_hS : Gromov.IsSymmetric S)
    (hS_nonempty : S.Nonempty) {L : ℝ} (hL : 0 ≤ L) (f : G → ℝ)
    (_hf : IsHarmonicSymmetric S f) (hLip : IsWordLipschitz S L f) :
    ∀ x, DiscreteGradient S f x ≤ L := by
  intro x
  unfold DiscreteGradient
  haveI : Nonempty S := hS_nonempty.to_subtype
  apply ciSup_le
  intro s
  have hdist : wordDist S x (x * s.val) ≤ 1 := by
    simp only [wordDist]
    have heq : x⁻¹ * (x * s.val) = s.val := by group
    rw [heq]
    exact wordLength_generator S s.prop
  have hLip' : |f (x * s.val) - f x| ≤ L * (wordDist S x (x * s.val) : ℝ) := by
    rw [abs_sub_comm]
    exact hLip x (x * s.val)
  calc |f (x * s.val) - f x| ≤ L * (wordDist S x (x * s.val) : ℝ) := hLip'
    _ ≤ L * 1 := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast hdist
        · exact hL
    _ = L := by ring

end GradientBounds

/-! ## Maximum Principle

The maximum principle for harmonic functions: a harmonic function on a connected
component attains its supremum only if it is constant on that component.
-/

section MaximumPrinciple

variable (S : Set G) [Fintype S]

omit [DecidableEq G] in
/-- Discrete maximum principle: If f is harmonic and attains its maximum at x,
    then f is constant on the connected component of x in the Cayley graph. -/
theorem maximum_principle (hS : Gromov.IsSymmetric S) (_hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (f : G → ℝ) (hf : IsHarmonicSymmetric S f)
    (x : G) (hmax : ∀ g : G, f g ≤ f x) :
    ∀ g : G, f g = f x := by
  -- Propagation lemma: if f(y) = f(x) then all S-neighbors also have the same value
  have propagate : ∀ y : G, f y = f x → ∀ s : S, f (y * s.val) = f x := by
    intro y hy s
    have hsum_y := hf y
    have hle_y : ∀ t : S, f (y * t.val) ≤ f y := fun t => by rw [hy]; exact hmax (y * t.val)
    by_contra hne
    have hlt : f (y * s.val) < f y := by rw [hy]; exact lt_of_le_of_ne (hmax (y * s.val)) hne
    have strict_sum : ∑ t : S, f (y * t.val) < ∑ _t : S, f y := by
      apply Finset.sum_lt_sum
      · intro t _; exact hle_y t
      · exact ⟨s, Finset.mem_univ s, hlt⟩
    have sum_const_y : ∑ _t : S, f y = (Fintype.card S : ℝ) * f y := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith [hsum_y]
  -- Also propagate to inverse neighbors (using symmetry of S)
  have propagate_inv : ∀ y : G, f y = f x → ∀ s : S, f (y * s.val⁻¹) = f x := by
    intro y hy s
    have hs_inv : s.val⁻¹ ∈ S := hS s.val s.prop
    exact propagate y hy ⟨s.val⁻¹, hs_inv⟩
  -- Induction on list representing word: all elements reachable from x have same value
  intro g
  have hclosure := exists_cayleyBall_mem_of_closure_eq_top hS_gen (x⁻¹ * g)
  obtain ⟨n, hn⟩ := hclosure
  obtain ⟨l, hlen, hmem, hprod⟩ := hn
  -- By induction on l, show that x * l.prod has f-value = f x
  have key : ∀ (l : List G) (z : G), (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) →
    f z = f x → f (z * l.prod) = f x := by
    intro l
    induction l with
    | nil => intro z _ hz; simp [hz]
    | cons hd tl ih =>
      intro z hmem_l hz
      simp only [List.prod_cons]
      have hmem_hd := hmem_l hd List.mem_cons_self
      have hmem_tl : ∀ s ∈ tl, s ∈ S ∨ s⁻¹ ∈ S := fun s hs => hmem_l s (List.mem_cons_of_mem _ hs)
      have hz_hd : f (z * hd) = f x := by
        cases hmem_hd with
        | inl h => exact propagate z hz ⟨hd, h⟩
        | inr h =>
          have h_inv : hd = (hd⁻¹)⁻¹ := by simp
          rw [h_inv]
          exact propagate_inv z hz ⟨hd⁻¹, h⟩
      have := ih (z * hd) hmem_tl hz_hd
      convert this using 1
      group
  -- Apply key to our situation: g = x * (x⁻¹ * g) = x * l.prod
  have hg : g = x * l.prod := by
    calc g = x * (x⁻¹ * g) := by group
      _ = x * l.prod := by rw [hprod]
  rw [hg]
  exact key l x hmem rfl

omit [DecidableEq G] in
/-- Corollary: A harmonic function constant on a finite-index coset is constant everywhere. -/
theorem harmonic_constant_on_coset (hS : Gromov.IsSymmetric S) (hS_nonempty : S.Nonempty)
    (hS_gen : Subgroup.closure S = ⊤) (f : G → ℝ) (hf : IsHarmonicSymmetric S f)
    (H : Subgroup G) [H.FiniteIndex] (c : ℝ) (hc : ∀ h : H, f h.val = c) :
    ∀ g : G, f g = c := by
  -- Since f is constant on H, in particular f(1) = c
  have f_one : f 1 = c := hc ⟨1, H.one_mem⟩

  -- Strategy: Consider f - c, which is harmonic and zero on H
  -- We'll show f - c is identically zero

  -- Define g := f - c (the shifted function)
  let g : G → ℝ := fun x => f x - c

  -- g is harmonic (difference of harmonic and constant)
  have hg : IsHarmonicSymmetric S g := by
    intro x
    have := hf x
    show ∑ s : S, (f (x * s.val) - c) = ↑(Fintype.card S) * (f x - c)
    calc ∑ s : S, (f (x * s.val) - c)
        = ∑ s : S, f (x * s.val) - ∑ s : S, c := by
          rw [← Finset.sum_sub_distrib]
      _ = ↑(Fintype.card S) * f x - ↑(Fintype.card S) * c := by
          rw [this]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ↑(Fintype.card S) * (f x - c) := by ring

  -- g is zero on H
  have hg_zero_on_H : ∀ h : H, g h.val = 0 := by
    intro h
    show f h.val - c = 0
    rw [hc h, sub_self]

  -- Since g(1) = f(1) - c = c - c = 0
  have hg_one : g 1 = 0 := by show f 1 - c = 0; rw [f_one, sub_self]

  -- Key claim: If g is harmonic, zero on a subgroup H, and H has finite index,
  -- then g attains its extrema (on H), so by maximum principle g is constant = 0.

  -- We'll use a different approach: show g takes only finitely many values
  -- Since there are finitely many cosets, and g is harmonic, we can show g is constant

  -- Actually, the cleanest approach: since g is zero on H and harmonic,
  -- and H contains the identity, we can propagate this using the maximum principle.
  -- But we need to show g is bounded first.

  -- Alternative: Show that g being harmonic and zero on a finite-index subgroup
  -- implies g is zero everywhere by a direct argument using cosets.
  sorry

end MaximumPrinciple

end

end Gromov.Harmonic.Existence
