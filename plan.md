# Gromov Polynomial Growth Theorem Formalization Plan

## Theorem Statement
A finitely generated group has polynomial growth ⟺ it is virtually nilpotent.

## Current State
- Project initialized with Mathlib v4.27.0-rc1
- Initial file `Gromov/GromovPolynomialGrowth.lean` created with definitions from formal-conjectures
- Build errors due to import issues (now understood)

## Key Insight: Two Directions of Different Difficulty

| Direction | Statement | Difficulty | Status in Literature |
|-----------|-----------|------------|---------------------|
| **←** | Virtually nilpotent → polynomial growth | **Easier** | Wolf (1968), Bass-Guivarc'h formula |
| **→** | Polynomial growth → virtually nilpotent | **Very Hard** | Gromov (1981), requires deep techniques |

The hard direction originally required Gromov-Hausdorff limits and Hilbert's 5th problem. Modern proofs (Kleiner, Tao-Shalom) use harmonic function theory but remain highly technical.

## Mathlib Tooling Available

**Already exists:**
- `Group.IsNilpotent`, `Group.IsVirtuallyNilpotent` (in `Mathlib.GroupTheory.Nilpotent`)
- `upperCentralSeries`, `lowerCentralSeries`, `nilpotencyClass`
- `Group.FG`, `Subgroup.FG` (in `Mathlib.GroupTheory.Finiteness`)
- `Subgroup.index`, `FiniteIndex` (in `Mathlib.GroupTheory.Index`)
- Basic growth infrastructure (in `Mathlib.Geometry.Group.Growth/`)

**Missing (we must build):**
- Polynomial growth definition for discrete groups
- Word metric / Cayley graph balls (partially in formal-conjectures file)
- Wolf's theorem (nilpotent groups have polynomial growth)
- Bass-Guivarc'h formula (exact degree computation)
- The main theorem itself

## Proposed Architecture

```
Gromov/
├── Gromov.lean                      # Root imports
├── GromovPolynomialGrowth.lean      # Main theorem statement
├── CayleyGraph.lean                 # Word metric, balls, growth function
├── PolynomialGrowth.lean            # Growth rate definitions, asymptotics
├── NilpotentGrowth.lean             # Wolf's theorem (← direction)
└── VirtuallyNilpotent.lean          # Properties of virtually nilpotent groups
```

## Phased Implementation

### Phase 1: Infrastructure (Fix Current File)
1. Fix imports (use `Mathlib.GroupTheory.Finiteness` not `FinitelyGeneratedGroup`)
2. Add missing imports (`Mathlib.Data.Real.Basic` for ℝ)
3. Remove duplicate `IsVirtuallyNilpotent` (already in Mathlib)
4. Get the file compiling with `sorry` on main theorem

### Phase 2: Growth Definitions
1. Formalize Cayley ball properly (current definition looks good)
2. Define polynomial growth class rigorously
3. Prove growth is independent of generating set choice (up to equivalence)
4. Basic lemmas about growth monotonicity, subgroups, quotients

### Phase 3: Easy Direction (← Virtually Nilpotent → Polynomial Growth)
1. **Abelian case:** Finitely generated abelian groups have polynomial growth
2. **Nilpotent case (Wolf's theorem):** Use lower central series
   - Each quotient Gₖ/Gₖ₊₁ is abelian
   - Induction on nilpotency class
3. **Virtually nilpotent case:** Reduce to nilpotent via finite index

### Phase 4: Hard Direction via Kleiner's Proof (→ Polynomial Growth → Virtually Nilpotent)

**Target: Full formalization using Kleiner's harmonic function approach**

#### Phase 4a: Harmonic Function Infrastructure
New file: `Gromov/Harmonic.lean`
- Define harmonic functions on Cayley graphs: `∀ g, ∑ s ∈ S, f(g·s) = |S| · f(g)`
- Define Lipschitz condition: `|f(g) - f(h)| ≤ C · d(g,h)`
- Define the space `H_L(G)` of L-Lipschitz harmonic functions

#### Phase 4b: Poincaré Inequalities
New file: `Gromov/Poincare.lean`
- **Poincaré inequality:** For f with zero mean on B(r):
  `‖f‖²_{L²(B(r))} ≤ C·r² · ∑_{edges} |∂f|²`
- **Reverse Poincaré (harmonic case):**
  `∑_{edges in B(r)} |∂f|² ≤ C/r² · ‖f‖²_{L²(B(2r))}`

#### Phase 4c: Colding-Minicozzi Theorem
New file: `Gromov/ColdingMinicozzi.lean`
- **Main theorem:** If `|B(r)| ≤ C·r^d` (polynomial growth), then `dim(H_L(G)) < ∞`
- Proof via comparing quadratic forms at different scales
- Key lemma: Volume doubling + Poincaré → finite harmonic dimension

#### Phase 4d: Representation Theory Step
New file: `Gromov/Representation.lean`
- Finite-dimensional H_L(G) gives a linear representation G → GL(H_L)
- Extract structural information about G from representation theory

#### Phase 4e: Inductive Descent
New file: `Gromov/Descent.lean`
- If G has infinite cyclic quotient Z and growth degree d, kernel has degree d-1
- Induction: reduce to trivial group, conclude virtually nilpotent
- Base case: finite groups are virtually nilpotent

#### Dependency Graph (Phase 4)
```
Harmonic.lean
    ↓
Poincare.lean
    ↓
ColdingMinicozzi.lean
    ↓
Representation.lean
    ↓
Descent.lean
    ↓
GromovPolynomialGrowth.lean (main theorem)
```

## Execution Strategy: Parallel lean4-prover Agents

All agents use `subagent_type: "lean4-prover"` which has access to Lean LSP tools (`lean_goal`, `lean_diagnostic_messages`, `lean_local_search`, `lean_leansearch`, `lean_loogle`, etc.) for efficient proof development.

### Wave 1: Foundation (Sequential - must complete first)
**Single lean4-prover agent:** Fix imports and get `GromovPolynomialGrowth.lean` compiling with sorries.

### Wave 2: Infrastructure (3 Parallel lean4-prover Agents)
Launch simultaneously:

| Agent | Task | Output File |
|-------|------|-------------|
| **Agent A** | Cayley graph infrastructure: word metric, balls, basic growth lemmas | `CayleyGraph.lean` |
| **Agent B** | Polynomial growth definitions, asymptotic equivalence, independence of generating set | `PolynomialGrowth.lean` |
| **Agent C** | Virtually nilpotent properties, finite index lemmas | `VirtuallyNilpotent.lean` |

### Wave 3: Easy Direction (2 Parallel lean4-prover Agents)
Launch after Wave 2 completes:

| Agent | Task | Output File |
|-------|------|-------------|
| **Agent D** | Abelian group growth bounds | `AbelianGrowth.lean` |
| **Agent E** | Wolf's theorem: nilpotent → polynomial growth via lower central series | `NilpotentGrowth.lean` |

### Wave 4: Hard Direction (3 Parallel lean4-prover Agents)
Launch after Wave 3 completes:

| Agent | Task | Output File |
|-------|------|-------------|
| **Agent F** | Harmonic functions on Cayley graphs, Lipschitz harmonic space | `Harmonic.lean` |
| **Agent G** | Discrete Poincaré and reverse Poincaré inequalities | `Poincare.lean` |
| **Agent H** | Inductive descent argument structure (can start with admitted lemmas) | `Descent.lean` |

### Wave 5: Core Technical (2 Parallel lean4-prover Agents)
Launch after Wave 4 completes:

| Agent | Task | Output File |
|-------|------|-------------|
| **Agent I** | Colding-Minicozzi theorem: polynomial growth → finite harmonic dimension | `ColdingMinicozzi.lean` |
| **Agent J** | Representation theory extraction from harmonic space | `Representation.lean` |

### Wave 6: Integration (Sequential)
**Single lean4-prover agent:** Assemble all pieces into final `GromovPolynomialGrowthTheorem` proof.

## Agent Specifications

Each agent uses `subagent_type: "lean4-prover"` and is given:
1. Clear file ownership
2. List of dependencies (files that must exist)
3. List of exports (theorems/definitions other agents need)
4. Reference to Kleiner's paper or relevant Mathlib files
5. Instruction to use Lean LSP tools (`lean_goal`, `lean_diagnostic_messages`, etc.) throughout

## Immediate Next Steps

1. **Wave 1:** Fix imports and compile main file
2. **Wave 2:** Launch 3 parallel infrastructure agents
3. Continue through waves as dependencies resolve

## Effort Estimate

| Phase | Complexity | Notes |
|-------|------------|-------|
| Phase 1 | Low | Import fixes, standard Mathlib usage |
| Phase 2 | Medium | Growth definitions need careful design |
| Phase 3 | Medium-High | Wolf's theorem requires lower central series induction |
| Phase 4a-b | High | New harmonic/Poincaré infrastructure |
| Phase 4c | Very High | Colding-Minicozzi is the technical core |
| Phase 4d-e | High | Representation theory + induction argument |

**Total: Major formalization project. Phases 1-3 are tractable. Phase 4 is research-level.**

## Key Files

### To Modify
- `/Users/eric/Documents/GitHub/Gromov/Gromov/GromovPolynomialGrowth.lean` - main file

### To Create
- `Gromov/CayleyGraph.lean` - word metric infrastructure
- `Gromov/PolynomialGrowth.lean` - growth rate definitions
- `Gromov/NilpotentGrowth.lean` - Wolf's theorem
- `Gromov/Harmonic.lean` - harmonic functions on groups
- `Gromov/Poincare.lean` - discrete Poincaré inequalities
- `Gromov/ColdingMinicozzi.lean` - finite dimension theorem
- `Gromov/Representation.lean` - linear representation extraction
- `Gromov/Descent.lean` - inductive argument

## Dependencies to Track

- The formal-conjectures file uses `grw` tactic (not standard) - replace with `rw` or `conv`
- Need `Mathlib.Analysis.InnerProductSpace` for L² norms
- May need to develop discrete harmonic analysis from scratch

## References

- [Kleiner's paper](https://arxiv.org/abs/0710.4593) - primary source for hard direction
- [Tao's blog post](https://terrytao.wordpress.com/2010/02/18/a-proof-of-gromovs-theorem/) - accessible exposition
- Mathlib `Geometry.Group.Growth/` - existing growth infrastructure
