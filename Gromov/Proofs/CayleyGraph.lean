/-
Copyright 2025 The Formal Conjectures Authors.
SPDX-License-Identifier: Apache-2.0

Cayley graphs and word metrics for groups.
-/

module

public import Gromov.Proofs.GromovPolynomialGrowth
public import Gromov.Definitions.WordMetric
public import Gromov.Definitions.GrowthDegree
public import Mathlib.Data.Nat.Lattice

namespace Gromov

public section

variable {G : Type*} [Group G]

/-! ## Word Length / Word Metric

The word length of an element g with respect to a generating set S is the minimal
length of a word in S and S⁻¹ that represents g.
-/

section WordLengthProperties

variable (S : Set G)

/-- wordLengths is nonempty when S generates G -/
theorem wordLengths_nonempty_of_closure_eq_top (h : Subgroup.closure S = ⊤) (g : G) :
    (wordLengths S g).Nonempty := by
  obtain ⟨n, hn⟩ := exists_cayleyBall_mem_of_closure_eq_top h g
  exact ⟨n, hn⟩

/-- Word length is well-defined for any element when S generates G -/
theorem wordLength_finite_of_closure_eq_top (h : Subgroup.closure S = ⊤) (g : G) :
    ∃ n, g ∈ CayleyBall S n :=
  exists_cayleyBall_mem_of_closure_eq_top h g

/-- The identity is in CayleyBall S 0 -/
theorem one_mem_wordLengths : 0 ∈ wordLengths S 1 :=
  one_mem_cayleyBall S 0

/-- The identity has word length 0 -/
theorem wordLength_one : wordLength S 1 = 0 := by
  have h0 : 0 ∈ wordLengths S 1 := one_mem_wordLengths S
  exact Nat.sInf_eq_zero.mpr (Or.inl h0)

/-- If g is in CayleyBall S n, then wordLength S g ≤ n -/
theorem wordLength_le_of_mem_cayleyBall {g : G} {n : ℕ} (h : g ∈ CayleyBall S n) :
    wordLength S g ≤ n :=
  Nat.sInf_le h

/-- If wordLength S g ≤ n and S generates G, then g is in CayleyBall S n -/
theorem mem_cayleyBall_of_wordLength_le (hclosure : Subgroup.closure S = ⊤)
    {g : G} {n : ℕ} (h : wordLength S g ≤ n) : g ∈ CayleyBall S n := by
  have hne : (wordLengths S g).Nonempty := wordLengths_nonempty_of_closure_eq_top S hclosure g
  have hmem : sInf (wordLengths S g) ∈ wordLengths S g := Nat.sInf_mem hne
  exact cayleyBall_monotone S h hmem

/-- Elements of S have word length at most 1 -/
theorem wordLength_generator {s : G} (hs : s ∈ S) : wordLength S s ≤ 1 := by
  have h : s ∈ CayleyBall S 1 := mem_cayleyBall_one_of_mem hs
  exact wordLength_le_of_mem_cayleyBall S h

/-- Inverses of generators have word length at most 1 -/
theorem wordLength_generator_inv {s : G} (hs : s ∈ S) : wordLength S s⁻¹ ≤ 1 := by
  have h : s⁻¹ ∈ CayleyBall S 1 := by
    simp only [CayleyBall, Set.mem_setOf_eq]
    use [s⁻¹]
    simp [hs]
  exact wordLength_le_of_mem_cayleyBall S h

/-- Word length satisfies the triangle inequality -/
theorem wordLength_mul_le (hclosure : Subgroup.closure S = ⊤) (g₁ g₂ : G) :
    wordLength S (g₁ * g₂) ≤ wordLength S g₁ + wordLength S g₂ := by
  have hne₁ : (wordLengths S g₁).Nonempty := wordLengths_nonempty_of_closure_eq_top S hclosure g₁
  have hne₂ : (wordLengths S g₂).Nonempty := wordLengths_nonempty_of_closure_eq_top S hclosure g₂
  have hmem₁ : sInf (wordLengths S g₁) ∈ wordLengths S g₁ := Nat.sInf_mem hne₁
  have hmem₂ : sInf (wordLengths S g₂) ∈ wordLengths S g₂ := Nat.sInf_mem hne₂
  have hprod : g₁ * g₂ ∈ CayleyBall S (wordLength S g₁ + wordLength S g₂) :=
    cayleyBall_mul S hmem₁ hmem₂
  exact wordLength_le_of_mem_cayleyBall S hprod

/-- Word length of inverse equals word length -/
theorem wordLength_inv (hclosure : Subgroup.closure S = ⊤) (g : G) :
    wordLength S g⁻¹ = wordLength S g := by
  have hne : (wordLengths S g).Nonempty := wordLengths_nonempty_of_closure_eq_top S hclosure g
  have hneinv : (wordLengths S g⁻¹).Nonempty :=
    wordLengths_nonempty_of_closure_eq_top S hclosure g⁻¹
  have hmem : sInf (wordLengths S g) ∈ wordLengths S g := Nat.sInf_mem hne
  have hmeminv : sInf (wordLengths S g⁻¹) ∈ wordLengths S g⁻¹ := Nat.sInf_mem hneinv
  -- g⁻¹ is in CayleyBall S (wordLength S g)
  have hinv : g⁻¹ ∈ CayleyBall S (wordLength S g) := cayleyBall_inv S hmem
  -- g is in CayleyBall S (wordLength S g⁻¹)
  have hinv' : g ∈ CayleyBall S (wordLength S g⁻¹) := by
    have := cayleyBall_inv S hmeminv
    simp only [inv_inv] at this
    exact this
  apply le_antisymm
  · exact wordLength_le_of_mem_cayleyBall S hinv
  · exact wordLength_le_of_mem_cayleyBall S hinv'

end WordLengthProperties

/-! ## Connection to Cayley Balls -/

section CayleyBallConnection

variable (S : Set G)

/-- An element is in the Cayley ball of radius n iff its word length is at most n -/
theorem mem_cayleyBall_iff_wordLength (hclosure : Subgroup.closure S = ⊤) (g : G) (n : ℕ) :
    g ∈ CayleyBall S n ↔ wordLength S g ≤ n := by
  constructor
  · exact wordLength_le_of_mem_cayleyBall S
  · exact mem_cayleyBall_of_wordLength_le S hclosure

/-- The Cayley ball is exactly the set of elements with word length at most n -/
theorem cayleyBall_eq_wordLength_le (hclosure : Subgroup.closure S = ⊤) (n : ℕ) :
    CayleyBall S n = {g : G | wordLength S g ≤ n} := by
  ext g
  exact mem_cayleyBall_iff_wordLength S hclosure g n

end CayleyBallConnection

/-! ## Symmetric Generating Sets -/

section SymmetricGenerators

/-- For symmetric S, the Cayley ball simplifies: elements are just products from S -/
theorem cayleyBall_symmetric_iff {S : Set G} (hS : IsSymmetric S) (g : G) (n : ℕ) :
    g ∈ CayleyBall S n ↔ ∃ (l : List G), l.length ≤ n ∧ (∀ s ∈ l, s ∈ S) ∧ l.prod = g := by
  constructor
  · intro ⟨l, hlen, hmem, hprod⟩
    use l, hlen
    constructor
    · intro s hs
      cases hmem s hs with
      | inl h => exact h
      | inr h =>
        have : s⁻¹⁻¹ ∈ S := hS s⁻¹ h
        simp only [inv_inv] at this
        exact this
    · exact hprod
  · intro ⟨l, hlen, hmem, hprod⟩
    exact ⟨l, hlen, fun s hs => Or.inl (hmem s hs), hprod⟩

end SymmetricGenerators

/-! ## Quasi-isometry and Change of Generators -/

section QuasiIsometry

/-- Given two finite generating sets, word lengths are comparable up to a constant.
    This is a key step toward showing polynomial growth is independent of generating set. -/
theorem wordLength_le_mul_wordLength {S T : Set G}
    (hS : Subgroup.closure S = ⊤) (hT : Subgroup.closure T = ⊤)
    (_hSF : S.Finite) (hTF : T.Finite) :
    ∃ C : ℕ, C > 0 ∧ ∀ g : G, wordLength S g ≤ C * wordLength T g := by
  -- Each generator in T can be expressed using generators in S
  -- The maximum word length of T-generators in S gives the constant C
  -- Define C as max over T of wordLength S t, ensuring C ≥ 1
  let C := (hTF.toFinset.sup (fun t => wordLength S t)) + 1
  use C
  constructor
  · -- C > 0 since C = ... + 1
    exact Nat.succ_pos _
  · intro g
    -- We prove by cases on whether g is in some CayleyBall T n
    obtain ⟨n, hn⟩ := exists_cayleyBall_mem_of_closure_eq_top hT g
    -- Get the actual word length
    have hne : (wordLengths T g).Nonempty := wordLengths_nonempty_of_closure_eq_top T hT g
    have hwl_mem : wordLength T g ∈ wordLengths T g := Nat.sInf_mem hne
    -- g is in CayleyBall T (wordLength T g)
    simp only [wordLengths, Set.mem_setOf_eq, CayleyBall] at hwl_mem
    obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hwl_mem
    -- Each element of l is in T or its inverse is in T
    -- We need to show g = l.prod is in CayleyBall S (C * wordLength T g)
    -- This follows because each generator (or its inverse) from T has wordLength S ≤ C - 1 < C
    have hbound : ∀ t, t ∈ l → wordLength S t ≤ C - 1 := by
      intro t ht
      have ht_in : t ∈ T ∨ t⁻¹ ∈ T := hl_mem t ht
      cases ht_in with
      | inl h =>
        have hmem : t ∈ hTF.toFinset := by simp [Set.Finite.mem_toFinset, h]
        have hle : wordLength S t ≤ hTF.toFinset.sup (fun s => wordLength S s) :=
          Finset.le_sup hmem
        omega
      | inr h =>
        have hmem : t⁻¹ ∈ hTF.toFinset := by simp [Set.Finite.mem_toFinset, h]
        have hle : wordLength S t⁻¹ ≤ hTF.toFinset.sup (fun s => wordLength S s) :=
          Finset.le_sup hmem
        have heq : wordLength S t = wordLength S t⁻¹ := by
          rw [← wordLength_inv S hS t⁻¹]
          simp
        omega
    -- Now we show g ∈ CayleyBall S (C * wordLength T g) by induction on l
    suffices h : g ∈ CayleyBall S (l.length * C) by
      have hlen : l.length * C ≤ C * wordLength T g := by
        calc l.length * C ≤ wordLength T g * C := Nat.mul_le_mul_right C hl_len
          _ = C * wordLength T g := Nat.mul_comm _ _
      exact wordLength_le_of_mem_cayleyBall S (cayleyBall_monotone S hlen h)
    -- Prove g ∈ CayleyBall S (l.length * C) by induction
    rw [← hl_prod]
    clear hn hl_len hl_prod g hne
    induction l with
    | nil => simp [one_mem_cayleyBall]
    | cons hd tl ih =>
      simp only [List.prod_cons, List.length_cons]
      have hhd : hd ∈ CayleyBall S C := by
        have hle : wordLength S hd ≤ C - 1 := hbound hd List.mem_cons_self
        have hle' : wordLength S hd ≤ C := Nat.le_of_lt (Nat.lt_of_le_of_lt hle
        (Nat.sub_lt_self Nat.one_pos (Nat.succ_pos _)))
        exact mem_cayleyBall_of_wordLength_le S hS hle'
      have htl : tl.prod ∈ CayleyBall S (tl.length * C) := by
        apply ih
        · intro s hs
          exact hl_mem s (List.mem_cons_of_mem hd hs)
        · intro t ht
          exact hbound t (List.mem_cons_of_mem hd ht)
      have hprod := cayleyBall_mul S hhd htl
      convert hprod using 2
      ring

/-- The word metrics from different finite generating sets are bi-Lipschitz equivalent -/
theorem wordLength_bilipschitz {S T : Set G}
    (hS : Subgroup.closure S = ⊤) (hT : Subgroup.closure T = ⊤)
    (hSF : S.Finite) (hTF : T.Finite) :
    ∃ C : ℕ, C > 0 ∧ ∀ g : G,
      wordLength S g ≤ C * wordLength T g ∧ wordLength T g ≤ C * wordLength S g := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := wordLength_le_mul_wordLength hS hT hSF hTF
  obtain ⟨C₂, hC₂pos, hC₂⟩ := wordLength_le_mul_wordLength hT hS hTF hSF
  use max C₁ C₂
  constructor
  · exact Nat.lt_of_lt_of_le hC₁pos (le_max_left _ _)
  · intro g
    constructor
    · calc wordLength S g ≤ C₁ * wordLength T g := hC₁ g
        _ ≤ max C₁ C₂ * wordLength T g := Nat.mul_le_mul_right _ (le_max_left _ _)
    · calc wordLength T g ≤ C₂ * wordLength S g := hC₂ g
        _ ≤ max C₁ C₂ * wordLength S g := Nat.mul_le_mul_right _ (le_max_right _ _)

end QuasiIsometry

/-! ## Finiteness of Cayley Balls -/

section Finiteness

/-- Cayley balls are finite when the generating set is finite (re-export) -/
theorem cayleyBall_finite' (S : Set G) (hS : S.Finite) (n : ℕ) : (CayleyBall S n).Finite :=
  cayleyBall_finite hS n

/-- Cayley balls grow at most exponentially -/
theorem cayleyBall_card_le_exp {S : Set G} (hS : S.Finite) (n : ℕ) :
    (CayleyBall S n).ncard ≤ (2 * S.ncard + 1) ^ n := by
  -- Define T as the set of generators, their inverses, and the identity
  let T := (S ∪ (·)⁻¹ '' S) ∪ {1}
  -- T is finite since S is finite
  have hT : T.Finite := by
    apply Set.Finite.union
    · exact hS.union (by simpa using hS.preimage inv_injective.injOn)
    · exact Set.finite_singleton 1
  -- The cardinality of T is at most 2 * |S| + 1
  have hT_card : T.ncard ≤ 2 * S.ncard + 1 := by
    have h1 : T.ncard ≤ (S ∪ (·)⁻¹ '' S).ncard + ({1} : Set G).ncard :=
      Set.ncard_union_le _ _
    have h2 : (S ∪ (·)⁻¹ '' S).ncard ≤ S.ncard + ((·)⁻¹ '' S).ncard :=
      Set.ncard_union_le _ _
    have h3 : ((·)⁻¹ '' S).ncard ≤ S.ncard := Set.ncard_image_le hS
    have h4 : ({1} : Set G).ncard = 1 := Set.ncard_singleton 1
    omega
  -- Use the set of functions Fin n → T
  let FunSet : Set (Fin n → G) := {f | ∀ i, f i ∈ T}
  have hFunSet_finite : FunSet.Finite := Set.Finite.pi' (fun _ => hT)
  -- The Cayley ball is contained in the image of FunSet under list product
  have hsubset : CayleyBall S n ⊆ (fun f => (List.ofFn f).prod) '' FunSet := by
    intro g hg
    obtain ⟨l, hl_len, hl_mem, hl_prod⟩ := hg
    -- Pad l with 1's to make it length n
    let padding : List G := List.replicate (n - l.length) 1
    let l' : List G := l ++ padding
    have hpad_len : padding.length = n - l.length := List.length_replicate ..
    have hl'_len : l'.length = n := by
      simp only [l', List.length_append, hpad_len]
      omega
    have hl'_prod : l'.prod = g := by
      simp only [l']
      rw [List.prod_append, List.prod_replicate, one_pow, mul_one, hl_prod]
    -- Convert l' to a function Fin n → G
    let f : Fin n → G := fun i => l'.get (i.cast hl'_len.symm)
    have hf_mem : f ∈ FunSet := by
      intro i
      simp only [f, T]
      have hi_lt : (i.cast hl'_len.symm).val < l'.length := by simp [hl'_len]
      have hget : l'.get (i.cast hl'_len.symm) ∈ l' := List.get_mem l' (i.cast hl'_len.symm)
      simp only [l', List.mem_append] at hget
      cases hget with
      | inl h =>
        have hmem := hl_mem _ h
        cases hmem with
        | inl hmemS => left; left; exact hmemS
        | inr hmemSinv => left; right; exact ⟨_, hmemSinv, inv_inv _⟩
      | inr h =>
        simp only [padding, List.mem_replicate] at h
        right
        simp only [Set.mem_singleton_iff]
        exact h.2
    have hf_prod : (List.ofFn f).prod = g := by
      have heq : List.ofFn f = l' := by
        apply List.ext_get
        · simp only [List.length_ofFn, hl'_len]
        · intro i hi1 hi2
          simp only [List.get_ofFn, f]
          congr 1
      rw [heq, hl'_prod]
    exact ⟨f, hf_mem, hf_prod⟩
  -- FunSet is Set.pi Set.univ (fun _ => T)
  have heq : FunSet = Set.pi Set.univ (fun (_ : Fin n) => T) := by
    ext f
    simp only [FunSet, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
  -- Bound ncard of FunSet
  have hFunSet_card : FunSet.ncard ≤ T.ncard ^ n := by
    rw [heq]
    haveI : Fintype T := hT.fintype
    -- Define the map from (Fin n → T) to Set.pi Set.univ (fun _ => T)
    let φ : (Fin n → T) → (Fin n → G) := fun f i => (f i : G)
    have hφ_inj : Function.Injective φ := by
      intro f g hfg
      ext i
      have heqi : φ f i = φ g i := congr_fun hfg i
      simp only [φ] at heqi
      exact heqi
    have hφ_range : Set.range φ = Set.pi Set.univ (fun (_ : Fin n) => T) := by
      ext f
      simp only [Set.mem_range, Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · rintro ⟨g, rfl⟩ i
        exact (g i).prop
      · intro hf
        use fun i => ⟨f i, hf i⟩
    rw [← hφ_range]
    calc (Set.range φ).ncard = Nat.card (Fin n → T) := by
          rw [Set.ncard_range_of_injective hφ_inj]
      _ = (Nat.card T) ^ n := by
          rw [Nat.card_fun]
          simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      _ = T.ncard ^ n := by rw [← Nat.card_coe_set_eq]
      _ ≤ T.ncard ^ n := le_refl _
  calc (CayleyBall S n).ncard
      ≤ ((fun f => (List.ofFn f).prod) '' FunSet).ncard := by
        exact Set.ncard_le_ncard hsubset (hFunSet_finite.image _)
      _ ≤ FunSet.ncard := Set.ncard_image_le hFunSet_finite
      _ ≤ T.ncard ^ n := hFunSet_card
      _ ≤ (2 * S.ncard + 1) ^ n := Nat.pow_le_pow_left hT_card n

end Finiteness

/-! ## Word Metric as a Pseudometric -/

section Metric

variable (S : Set G)

theorem wordDist_self (g : G) : wordDist S g g = 0 := by
  simp [wordDist, wordLength_one]

theorem wordDist_comm (hclosure : Subgroup.closure S = ⊤) (g₁ g₂ : G) :
    wordDist S g₁ g₂ = wordDist S g₂ g₁ := by
  simp only [wordDist]
  have heq : g₂⁻¹ * g₁ = (g₁⁻¹ * g₂)⁻¹ := by group
  rw [heq, wordLength_inv S hclosure]

theorem wordDist_triangle (hclosure : Subgroup.closure S = ⊤) (g₁ g₂ g₃ : G) :
    wordDist S g₁ g₃ ≤ wordDist S g₁ g₂ + wordDist S g₂ g₃ := by
  simp only [wordDist]
  have : g₁⁻¹ * g₃ = (g₁⁻¹ * g₂) * (g₂⁻¹ * g₃) := by group
  rw [this]
  exact wordLength_mul_le S hclosure _ _

end Metric

end

end Gromov
