# Gromov's Polynomial Growth Theorem in Lean 4

A formalization of Gromov's polynomial growth theorem in Lean 4 using Mathlib.

## Theorem Statement

**Gromov's Polynomial Growth Theorem (1981):** A finitely generated group has polynomial growth if and only if it is virtually nilpotent.

```lean
theorem GromovPolynomialGrowthTheorem [Group.FG G] :
    HasPolynomialGrowth G ↔ Group.IsVirtuallyNilpotent G
```

## Project Status

| Direction | Statement | Status |
|-----------|-----------|--------|
| **Reverse (easy)** | Virtually nilpotent implies polynomial growth | In progress (2 sorries) |
| **Forward (hard)** | Polynomial growth implies virtually nilpotent | In progress (4 sorries) |

**Current sorry count:** 15 total across 4 files
- Polycyclic.lean: 8 sorries (polycyclic group infrastructure)
- NilpotentGrowth.lean: 2 sorries (reverse direction)
- ResiduallyFinite.lean: 1 sorry
- Descent.lean: 4 sorries (forward direction)

### Completed Infrastructure

- Cayley ball definitions and basic properties
- Word length / word metric infrastructure
- Quasi-isometry between different generating sets
- Polynomial growth definitions and asymptotic equivalence
- Independence of growth rate from choice of generating set
- Polynomial growth examples: finite groups, Z, Z^n
- Products preserve polynomial growth
- F.g. abelian groups have polynomial growth
- Harmonic function infrastructure on Cayley graphs
- Discrete Poincare inequalities
- Descent argument structure (statements)

### Remaining Work

**Polycyclic infrastructure (8 sorries):**
- `isPolycyclic_of_isNilpotent_fg`: F.g. nilpotent groups are polycyclic
- `polycyclic_has_finiteIndex_nilpotent_normal_subgroup`: Fitting subgroup theorem
- `isPolycyclic_of_finite`: Finite solvable groups are polycyclic
- `isPolycyclic_subgroup`: Subgroups of polycyclic are polycyclic
- `isPolycyclic_of_le`: Variant for subgroup inclusion
- `isPolycyclic_of_extension`: Extensions preserve polycyclicity
- `isPolycyclic_of_finiteIndex_polycyclic`: Finite extensions
- `Subgroup.fg_of_polycyclic`: Mal'cev's theorem

**Reverse direction (2 sorries):**
- `cayleyBall_lift_bound_for_center_quotient`: Central extension bounds
- `schreier_rewrite_bound`: Schreier's lemma for word length

**Forward direction (4 sorries):**
- `infinite_cyclic_quotient_of_polynomial_growth`: Kleiner's theorem
- `kernel_growth_degree_lt`: Growth degree reduction
- `isVirtuallyNilpotent_of_extension_by_Z`: Extension lemma (2 sorries)

## File Structure

```
Gromov/
├── Gromov.lean                    # Root imports
├── GromovPolynomialGrowth.lean    # Main theorem, Cayley balls, growth function
├── CayleyGraph.lean               # Word length, word metric, quasi-isometry
├── PolynomialGrowth.lean          # Growth definitions, examples (Z, Z^n)
├── AbelianGrowth.lean             # Abelian group growth, product preservation
├── VirtuallyNilpotent.lean        # Properties of virtually nilpotent groups
├── NilpotentGrowth.lean           # Wolf's theorem (reverse direction)
├── Harmonic.lean                  # Harmonic functions on Cayley graphs
├── Poincare.lean                  # Discrete Poincare inequalities
└── Descent.lean                   # Inductive descent for forward direction
```

## Building

Requires Lean 4 and Mathlib v4.27.0-rc1.

```bash
lake update
lake build
```

## TAIL Verification

This project follows the [TAIL Standard](https://github.com/e-vergo/TAIL) for AI-generated formal proofs. TAIL reduces review burden by structuring projects so that only the theorem statement needs human verification.

### Running Verification

```bash
lake exe tailverify
```

### Project Structure

| Component | Review Status |
|-----------|---------------|
| `MainTheorem.lean` | Human review required |
| `Definitions/` | Human review required |
| `ProofOfMainTheorem.lean` | Machine verified |
| `Proofs/` | Machine verified |

**Current status:** 492 lines require review (6% of 8,017 total lines). TAIL verification passes.

### Development Workflow

TAIL verification should pass at all times during development:

1. **No axiom declarations** - Use `theorem ... := by sorry` for incomplete proofs
2. **No native_decide** - Avoid kernel-level computation
3. **No trivial True** - Don't declare theorems with type `True`
4. **Correct structure** - Keep proof machinery in `Proofs/`, definitions in `Definitions/`

Run `lake exe tailverify` before committing to ensure compliance.

## Mathematical Background

### Reverse Direction (Wolf 1968, Bass-Guivarch)

The proof proceeds by induction on nilpotency class:
1. The center Z(G) is nontrivial for nontrivial nilpotent groups
2. G/Z(G) has lower nilpotency class, so by IH has polynomial growth
3. Z(G) is abelian, hence has polynomial growth
4. Using centrality, Ball_G(n) embeds into Ball_{G/Z}(n) x Ball_Z(n)
5. Product bound gives polynomial growth

### Forward Direction (Gromov 1981, Kleiner 2010)

The modern proof via Kleiner uses harmonic functions:
1. Construct L-Lipschitz harmonic functions on the Cayley graph
2. Show polynomial growth implies finite-dimensional harmonic space (Colding-Minicozzi)
3. Extract infinite cyclic quotient from the representation on harmonic space
4. Apply induction: kernel has lower growth degree
5. Extensions of virtually nilpotent groups by Z are virtually nilpotent

## References

- Gromov, M. "Groups of polynomial growth and expanding maps" (1981)
- Kleiner, B. "A new proof of Gromov's theorem on groups of polynomial growth" (2010)
- Tao, T. "Hilbert's Fifth Problem and Related Topics" (2014)
