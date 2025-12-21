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
| **Reverse (easy)** | Virtually nilpotent implies polynomial growth | Complete |
| **Forward (hard)** | Polynomial growth implies virtually nilpotent | In progress |

### Completed

- Cayley ball definitions and basic properties
- Word length / word metric infrastructure
- Quasi-isometry between different generating sets
- Polynomial growth definitions and asymptotic equivalence
- Independence of growth rate from choice of generating set
- Polynomial growth examples: finite groups, Z, Z^n
- Products preserve polynomial growth
- F.g. abelian groups have polynomial growth
- **Wolf's theorem**: F.g. nilpotent groups have polynomial growth
- **Full reverse direction**: F.g. virtually nilpotent groups have polynomial growth
- Harmonic function infrastructure on Cayley graphs
- Discrete Poincare inequalities
- Descent argument structure (statements)

### In Progress

The forward direction uses Kleiner's harmonic function approach:

- Colding-Minicozzi theorem (polynomial growth implies finite harmonic dimension)
- Infinite cyclic quotient extraction from harmonic functions
- Kernel growth degree reduction
- Extension lemmas for virtual nilpotency

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
