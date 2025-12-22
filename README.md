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
| **Reverse (easy)** | Virtually nilpotent implies polynomial growth | In progress |
| **Forward (hard)** | Polynomial growth implies virtually nilpotent | In progress |

**Current sorry count:** 126 total across 17 files

| Directory | Sorries | Description |
|-----------|---------|-------------|
| Growth/ | 30 | Fibration, kernel degree bounds |
| Harmonic/ | 35 | Spectral theory, existence, finite-dimensionality |
| Polycyclic/ | 31 | Core theory, Fitting, Malcev, extensions |
| Schreier/ | 15 | Coset representatives, word bounds |
| Representation/ | 13 | Compact Lie, quotient extraction |
| Descent/ | 2 | Main descent argument |

## File Structure

```
Gromov/
├── Gromov.lean                    # Root imports
├── MainTheorem.lean               # Main theorem statement (human review)
├── ProofOfMainTheorem.lean        # Proof assembly (machine verified)
├── Definitions/                   # Core definitions (human review)
│   ├── PolynomialGrowth.lean
│   ├── WordMetric.lean
│   ├── GrowthDegree.lean
│   ├── Harmonic.lean
│   ├── Poincare.lean
│   ├── Descent.lean
│   └── VirtuallyNilpotent.lean
└── Proofs/                        # All proofs (machine verified)
    ├── Cayley/
    │   └── Graph.lean             # Word length, Cayley graph structure
    ├── Descent/
    │   └── Main.lean              # Inductive descent for forward direction
    ├── Growth/
    │   ├── Abelian.lean           # Abelian group growth
    │   ├── Fibration.lean         # Level sets, fibration structure
    │   ├── GromovMain.lean        # Main growth theorem components
    │   ├── KernelDegree.lean      # Growth degree of kernels
    │   ├── Nilpotent.lean         # Wolf's theorem (reverse direction)
    │   └── Polynomial.lean        # Polynomial growth examples
    ├── Harmonic/
    │   ├── Core.lean              # Basic harmonic function definitions
    │   ├── Spectral.lean          # Discrete Laplacian, spectrum
    │   ├── Existence.lean         # Non-trivial harmonic functions exist
    │   └── FiniteDim.lean         # Kleiner's finite-dimensionality
    ├── Poincare/
    │   └── Main.lean              # Discrete Poincare inequalities
    ├── Polycyclic/
    │   ├── Abelian.lean           # F.g. abelian → polycyclic
    │   ├── Core.lean              # Polycyclic group theory
    │   ├── Extensions.lean        # Series concatenation, lifting
    │   ├── Fitting.lean           # Fitting subgroup theory
    │   ├── Malcev.lean            # Subgroups of polycyclic are f.g.
    │   └── ResiduallyFinite.lean  # Residual finiteness
    ├── Representation/
    │   ├── CompactLie.lean        # Jordan's theorem, compact closure
    │   └── QuotientExtraction.lean # Extract Z quotient
    ├── Schreier/
    │   ├── CosetReps.lean         # Coset representatives, transversals
    │   └── WordBounds.lean        # Schreier rewriting bounds
    └── VirtuallyNilpotent/
        ├── Core.lean              # Virtually nilpotent properties
        └── NilpotencyClass.lean   # Nilpotency class bounds
```

## Building

Requires Lean 4 and Mathlib.

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

**Current status:** 553 lines require review (5% of ~10,600 total lines).

### Development Workflow

TAIL verification should pass when all sorries are cleared:

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
- Tao, T. "A proof of Gromov's theorem" (blog post, 2010)
