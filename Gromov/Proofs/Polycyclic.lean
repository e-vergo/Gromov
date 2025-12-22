/-
Copyright 2025 The Gromov Project Authors.
SPDX-License-Identifier: Apache-2.0

Polycyclic groups and their relationship to virtual nilpotency.
-/

module

public import Gromov.Proofs.VirtuallyNilpotent

/-!
# Polycyclic Groups

This file develops the theory of polycyclic groups and proves the equivalence
between virtually nilpotent and polycyclic for finitely generated groups.

## Main results

* `Group.isVirtuallyNilpotent_iff_polycyclic`: For finitely generated groups, virtually nilpotent
  iff polycyclic (Mal'cev's theorem).
* `Subgroup.fg_of_polycyclic`: Subgroups of polycyclic groups are finitely generated.

## References

* Mal'cev, A. I. "On certain classes of infinite soluble groups" (1951)
* Segal, D. "Polycyclic Groups" Cambridge University Press (1983)
-/

open Subgroup

namespace Group

public section

variable {G : Type*} [Group G]

/-! ### Polycyclic Group Theorems -/

/-- Finitely generated nilpotent groups are polycyclic.

The proof uses the lower central series G = G_0 > G_1 > ... > G_n = 1 where each
quotient G_i/G_{i+1} is abelian and f.g. (by Mal'cev's theorem on nilpotent groups).
F.g. abelian groups are polycyclic by the structure theorem (Z^r x finite torsion).
Concatenating these polycyclic series gives a polycyclic series for G.

References:
- Segal, D. "Polycyclic Groups" (1983), Theorem 1.5
- Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.4.12
-/
theorem isPolycyclic_of_isNilpotent_fg (H : Type*) [Group H] [FG H] [IsNilpotent H] :
    IsPolycyclic H := by
  sorry

/-- Every polycyclic group has a finite-index normal nilpotent subgroup (Fitting subgroup).

This is the Fitting subgroup theorem: in polycyclic groups, the Fitting subgroup
(the unique maximal normal nilpotent subgroup) has finite index. The Fitting
subgroup is defined as the product of all normal nilpotent subgroups.

References:
- Segal, D. "Polycyclic Groups" (1983), Theorem 1.3
- Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.2.17
-/
theorem polycyclic_has_finiteIndex_nilpotent_normal_subgroup (H : Type*) [Group H]
    (hP : IsPolycyclic H) :
    ∃ N : Subgroup H, N.Normal ∧ IsNilpotent N ∧ N.FiniteIndex := by
  sorry

-- Polycyclic groups are virtually nilpotent (follows from the axiom above)
theorem isVirtuallyNilpotent_of_isPolycyclic (H : Type*) [Group H] (hP : IsPolycyclic H) :
    IsVirtuallyNilpotent H := by
  obtain ⟨N, _, hNilpotent, hFiniteIndex⟩ :=
    polycyclic_has_finiteIndex_nilpotent_normal_subgroup H hP
  exact ⟨N, hNilpotent, hFiniteIndex⟩

/-- Finite solvable groups are polycyclic.

Every finite solvable group has a composition series with cyclic (prime order) factors.
The proof uses induction on cardinality: take a maximal normal subgroup N, then K/N is
simple and solvable hence cyclic of prime order, and N is solvable hence polycyclic by IH.

Note: A finite group is polycyclic iff it is solvable. The alternating group A_5 is
finite but not polycyclic (it's not solvable).

References:
- Robinson, D.J.S. "A Course in the Theory of Groups" 2nd ed. (1996), Theorem 5.4.11
-/
-- Helper: Trivial group is polycyclic
private lemma isPolycyclic_of_subsingleton (K : Type*) [Group K] [Subsingleton K] :
    IsPolycyclic K := by
  refine ⟨0, fun _ => ⊤, rfl, ?_, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  ext x; simp only [Subgroup.mem_top, Subgroup.mem_bot, Subsingleton.elim x 1]

-- Helper: Cyclic groups are polycyclic
lemma isPolycyclic_of_isCyclic (K : Type*) [Group K] [IsCyclic K] :
    IsPolycyclic K := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  refine ⟨1, ![⊤, ⊥], rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    exact bot_le
  · intro i
    fin_cases i
    change (⊥ : Subgroup K).subgroupOf ⊤ |>.Normal
    infer_instance
  · intro i h1 h2
    fin_cases i
    change QuotientIsCyclic (⊥ : Subgroup K) ⊤ bot_le (by infer_instance)
    unfold QuotientIsCyclic
    -- The quotient ⊤/⊥ is essentially K, which is cyclic
    use ⟨g, trivial⟩
    rw [Subgroup.eq_top_iff']
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨n, hn⟩ := hg k.val
      rw [Subgroup.mem_zpowers_iff]
      use n
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
      -- Goal: ↑((⟨g, trivial⟩ ^ n)⁻¹ * k) = 1
      -- We have hn : g ^ n = ↑k
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow]
      -- Goal: (g ^ n)⁻¹ * ↑k = 1
      simp only [← hn, inv_mul_cancel]

theorem isPolycyclic_of_finite (K : Type*) [Group K] [Finite K] [IsSolvable K] :
    IsPolycyclic K := by
  sorry

/-- Subgroups of polycyclic groups are polycyclic.

Given a polycyclic series G = G_0 > G_1 > ... > G_n = 1, intersect with H to get
H_i = H cap G_i. The quotient (H cap G_i)/(H cap G_{i+1}) embeds into G_i/G_{i+1}
which is cyclic. Since subgroups of cyclic groups are cyclic (Mathlib: Subgroup.isCyclic),
the restricted series has cyclic quotients.

References:
- Segal, D. "Polycyclic Groups" (1983), Theorem 1.1
-/
theorem isPolycyclic_subgroup {G : Type*} [Group G] (hG : IsPolycyclic G)
    (H : Subgroup G) : IsPolycyclic H := by
  sorry

-- Variant: If H <= K as subgroups of G and K is polycyclic, then H is polycyclic
-- Note: This requires transferring IsPolycyclic across the isomorphism H ≃* H.subgroupOf K
theorem isPolycyclic_of_le {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (hK : IsPolycyclic K) : IsPolycyclic H := by
  sorry

/-- Extensions of polycyclic groups are polycyclic.

If N is normal in G with both N and G/N polycyclic, then G is polycyclic.
The proof lifts the polycyclic series for G/N via comap (ending at N), then
concatenates with the polycyclic series for N.

References:
- Segal, D. "Polycyclic Groups" (1983), Proposition 1.2
-/
theorem isPolycyclic_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : IsPolycyclic N) (hQ : IsPolycyclic (G ⧸ N)) : IsPolycyclic G := by
  sorry

/-- If H is a finite-index polycyclic subgroup of G, then G is polycyclic.

Proof outline: H polycyclic implies H solvable. H.normalCore is solvable (subgroup of solvable).
For finite-index solvable subgroups, G is solvable. Then G/H.normalCore is finite and solvable,
hence polycyclic. H.normalCore is polycyclic (subgroup of H). G is an extension of polycyclic
groups, hence polycyclic.

References:
- Segal, D. "Polycyclic Groups" (1983), Proposition 1.6
-/
theorem isPolycyclic_of_finiteIndex_polycyclic (H : Subgroup G) [H.FiniteIndex]
    (hH : IsPolycyclic H) : IsPolycyclic G := by
  sorry

/-- Subgroups of polycyclic groups are finitely generated (Mal'cev 1951).

This is Mal'cev's theorem (1951). The proof uses induction on the length of the
polycyclic series. If G = G_0 > G_1 > ... > G_n = 1 with cyclic quotients, then
for H <= G, the quotient H/(H cap G_1) embeds into G/G_1 which is cyclic, so
H/(H cap G_1) is f.g. (cyclic). By induction, H cap G_1 is f.g., so H is f.g.

References:
- Mal'cev, A. I. "On certain classes of infinite soluble groups" (1951)
- Segal, D. "Polycyclic Groups" (1983), Theorem 1.2
-/
theorem Subgroup.fg_of_polycyclic (hG : IsPolycyclic G) (H : Subgroup G) : FG H := by
  sorry

/-! ### Main Theorem -/

/-- **Mal'cev's Theorem**: For finitely generated groups, virtually nilpotent is equivalent
to polycyclic.

The forward direction uses: f.g. nilpotent groups are polycyclic, and finite extensions
of polycyclic groups are polycyclic.

The reverse direction uses: polycyclic groups have finite-index nilpotent subgroups
(the Fitting subgroup).
-/
theorem isVirtuallyNilpotent_iff_polycyclic [FG G] : IsVirtuallyNilpotent G ↔ IsPolycyclic G := by
  constructor
  · -- (=>) Virtually nilpotent => Polycyclic
    intro ⟨H, hNil, hFin⟩
    haveI : H.FiniteIndex := hFin
    haveI : IsNilpotent H := hNil
    -- H is f.g. (finite-index subgroup of f.g. group)
    haveI : FG H := Subgroup.fg_of_index_ne_zero H
    -- H is nilpotent and f.g., hence polycyclic
    have hHP : IsPolycyclic H := isPolycyclic_of_isNilpotent_fg H
    -- G is a finite extension of H, hence polycyclic
    exact isPolycyclic_of_finiteIndex_polycyclic H hHP
  · -- (<=) Polycyclic => Virtually nilpotent
    intro hP
    exact isVirtuallyNilpotent_of_isPolycyclic G hP

end

end Group
