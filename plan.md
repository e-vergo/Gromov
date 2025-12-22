# Gromov Formalization: Sorry Clearing Plan

## CRITICAL: Read This After Every Compaction

**After every `/compact` or context reset, immediately:**
1. Read this file: `/Users/eric/Documents/GitHub/Gromov/plan.md`
2. Run `lake build 2>&1 | head -100` to see current errors
3. Run `mcp__lean-lsp-lal__lal_sorry_report` on `/Users/eric/Documents/GitHub/Gromov/Gromov/Proofs` to see current sorries
4. Check the Execution Queue below and spawn an agent for the current priority file
5. **One agent at a time** - wait for completion before spawning next

---

## Autonomous Execution Protocol

This plan is designed for overnight autonomous execution without user intervention.

### Rules:
1. **Sequential execution only** - one agent per file, wait for completion
2. **Fix errors before sorries** - a file with compilation errors blocks downstream files
3. **Create infrastructure as needed** - if a proof requires helper lemmas, build them
4. **New files are allowed** - create `Gromov/Proofs/Helper/*.lean` if needed for shared infrastructure
5. **Never give up** - all theorems here are mathematically provable; persist until solved
6. **Update this plan** - after each file completes, update the Tracking table below

### If an agent fails:
1. Read the agent's output to understand what went wrong
2. If it introduced axioms: revert the file with `git checkout -- <file>` and respawn
3. If it got stuck: spawn a new agent with more specific guidance based on what was learned
4. If infrastructure is missing: create a helper file first, then retry

### Success criteria:
- `lake build` completes with only `sorry` warnings (no errors)
- `lake exe tailverify` passes
- `grep -rn "^axiom" Gromov/` returns nothing
- All sorries cleared (or documented as requiring specific mathematical insight)

---

## Proof Integrity Requirements

**This formalization must be a complete, valid, machine-checked proof.** The following are strictly prohibited:

| Prohibited | Reason |
|------------|--------|
| `axiom` declarations | Introduces unverified assumptions |
| `sorry` in final code | Marks incomplete proofs |
| `native_decide` | Bypasses kernel verification |
| `Trivial` / `True` theorems | Empty mathematical content |
| `decide` on undecidable props | Can cause unsoundness |
| Custom axioms via `constant` | Same as `axiom` |
| `unsafeCoerce` / `unsafe` | Bypasses type safety |

**Verification:** Run `lake exe tailverify` before any commit. All proofs must:
- Type-check without warnings
- Use only Mathlib's standard axioms (propext, Quot.sound, Classical.choice)
- Contain no `sorry` statements
- Pass TAIL verification

**If a proof cannot be completed:** Leave it as `sorry` and document the mathematical obstacle. Do NOT introduce axioms or other workarounds to make it "appear" complete.

---

## Execution Model

**CRITICAL: Sequential agent execution only.** Due to file dependencies, spawn only ONE agent at a time. Wait for the agent to complete and verify success before spawning the next.

Workflow:
1. Run `lake build` to identify current errors
2. Spawn agent for highest-priority file (fix errors before sorries)
3. Wait for agent completion
4. Verify with `lake build` and `lake exe tailverify`
5. Repeat for next file

**Never spawn parallel agents** - files have import dependencies that cause conflicts.

---

## Current Status

- **Total sorries:** 13
- **Files with sorries:** 3 (Polycyclic.lean, NilpotentGrowth.lean, Descent.lean)
- **Files with errors:** 1 (ResiduallyFinite.lean - must fix first)
- **Main theorem:** `Gromov.mainTheorem : StatementOfTheorem`
- **TAIL Status:** PASS

The main theorem has two directions:
- **Forward:** `Descent.isVirtuallyNilpotent_of_polynomialGrowth` (polynomial growth → virtually nilpotent)
- **Reverse:** `NilpotentGrowth.IsVirtuallyNilpotent.hasPolynomialGrowth` (virtually nilpotent → polynomial growth)

---

## Part I: Forward Direction (Descent)

The forward direction uses Kleiner's approach. The proof structure (from Tao-Shalom):

1. Polynomial growth groups admit non-trivial Lipschitz harmonic functions
2. The space of Lipschitz harmonic functions is finite-dimensional (Kleiner)
3. G acts on this space; the image in GL(V) has compact closure
4. Compact Lie case: finitely generated subgroups of compact Lie groups with polynomial growth are virtually abelian
5. Extract an infinite cyclic quotient from the representation
6. Induction: kernel has lower growth degree, apply IH, extend

### Descent.lean (4 sorries)

| Line | Declaration | Description |
|------|-------------|-------------|
| 335 | `infinite_cyclic_quotient_of_polynomial_growth` | Theorems 2-4 from Tao: harmonic function construction, Kleiner's theorem, compact Lie case |
| 411 | `kernel_growth_degree_lt` | Kernel of G → Z has growth degree d-1 if G has degree d |
| 508 | `isVirtuallyNilpotent_of_extension_by_Z` | Extensions of virtually nilpotent by Z are virtually nilpotent |
| 591 | `isVirtuallyNilpotent_of_extension_by_Z` | (same theorem, second sorry location) |

---

## Part II: Reverse Direction (Wolf)

The reverse direction proves virtually nilpotent groups have polynomial growth:
1. Nilpotent groups have polynomial growth (induction on nilpotency class)
2. Finite-index subgroups preserve polynomial growth (Schreier bounds)

### NilpotentGrowth.lean (3 sorries)

| Line | Declaration | Description |
|------|-------------|-------------|
| 145 | `malcev_subgroup_fg_of_fg_nilpotent` | Subgroups of f.g. nilpotent groups are f.g. (Mal'cev 1951) |
| 241 | `cayleyBall_lift_bound_for_center_quotient` | Cayley ball bound for lifted generators in central extensions |
| 669 | `schreier_rewrite_bound` | Schreier's lemma: word length bounds for finite-index subgroups |

### ResiduallyFinite.lean (2 sorries)

| Line | Declaration | Description |
|------|-------------|-------------|
| 223 | `isResiduallyFinite_of_fg_nilpotent` | F.g. nilpotent groups are residually finite |
| 258 | `isResiduallyFinite_of_fg_nilpotent` | (continuation) |

---

## Part III: Polycyclic Infrastructure

The polycyclic group theory underlies both directions:
- Forward: `isVirtuallyNilpotent_iff_polycyclic` connects the characterizations
- Reverse: `isPolycyclic_of_isNilpotent_fg` shows nilpotent → polycyclic

### Polycyclic.lean (23 sorries)

| Lines | Declaration | Sorries | Description |
|-------|-------------|---------|-------------|
| 123, 133, 142, 153 | `isPolycyclic_of_isNilpotent_fg` | 4 | F.g. nilpotent groups are polycyclic |
| 178 | `polycyclic_has_finiteIndex_nilpotent_normal_subgroup` | 1 | Fitting subgroup theory |
| 234 | `isPolycyclic_of_finite` | 1 | Finite solvable groups are polycyclic |
| 284, 290 | `isPolycyclic_subgroup` | 2 | Subgroups of polycyclic are polycyclic |
| 317, 325, 338, 342 | `isPolycyclic_of_le` | 4 | Variant for subgroups via inclusion |
| 445, 450, 456, 472, 476, 479, 485 | `isPolycyclic_of_extension` | 7 | Extensions of polycyclic by polycyclic |
| 515 | `isPolycyclic_of_finiteIndex_polycyclic` | 1 | Finite-index polycyclic subgroup implies polycyclic |
| 585, 591, 598 | `Subgroup.fg_of_polycyclic` | 3 | Mal'cev: subgroups of polycyclic are f.g. |

---

## Part IV: Residual Finiteness

Used in the reverse direction to handle nilpotent group structure.

### ResiduallyFinite.lean (4 sorries)

| Lines | Declaration | Sorries | Description |
|-------|-------------|---------|-------------|
| 211, 223 | `isResiduallyFinite_of_fg_nilpotent` | 2 | F.g. nilpotent groups are residually finite |
| 257, 258 | `isResiduallyFinite_of_fg_nilpotent` | 2 | (same theorem, continuation) |

---

## Critical Path

All sorries are on the critical path. Dependency order:

```
mainTheorem
├── isVirtuallyNilpotent_of_polynomialGrowth (Forward)
│   └── isVirtuallyNilpotent_of_polynomialGrowthDegree (induction on d)
│       ├── infinite_cyclic_quotient_of_polynomial_growth [1 sorry]
│       ├── kernel_growth_degree_lt [1 sorry]
│       └── isVirtuallyNilpotent_of_extension_by_Z [2 sorries]
│
└── IsVirtuallyNilpotent.hasPolynomialGrowth (Reverse)
    ├── IsNilpotent.hasPolynomialGrowth
    │   └── hasPolynomialGrowth_of_nilpotencyClass_le (induction on class)
    │       └── cayleyBall_lift_bound_for_center_quotient [1 sorry]
    ├── malcev_subgroup_fg_of_fg_nilpotent [1 sorry]
    ├── schreier_rewrite_bound [1 sorry]
    └── Polycyclic infrastructure
        ├── isPolycyclic_of_isNilpotent_fg [5 sorries]
        ├── polycyclic_has_finiteIndex_nilpotent_normal_subgroup [1 sorry]
        ├── isPolycyclic_subgroup [2 sorries]
        ├── isPolycyclic_of_le [4 sorries]
        ├── isPolycyclic_of_extension [7 sorries]
        ├── isPolycyclic_of_finiteIndex_polycyclic [1 sorry]
        ├── Subgroup.fg_of_polycyclic [3 sorries]
        └── isPolycyclic_of_finite [1 sorry]
```

---

## Task Sequencing

### Phase 1: Polycyclic Foundation

These form the foundation for both directions.

1. **`isPolycyclic_of_isNilpotent_fg`** (5 sorries, lines 101-150)
   - Requires: Lower central series properties, quotient group infrastructure
   - Approach: Induction on nilpotency class using the series

2. **`isPolycyclic_subgroup`** (2 sorries, lines 281, 287)
   - Requires: Comap preserves normality, subgroups of cyclic are cyclic
   - Approach: Restrict the polycyclic series to the subgroup

3. **`isPolycyclic_of_le`** (4 sorries, lines 314-339)
   - Requires: `isPolycyclic_subgroup`
   - Approach: Transfer via inclusion

4. **`isPolycyclic_of_extension`** (7 sorries, lines 442-482)
   - Requires: Series concatenation, normality preservation
   - Approach: Lift quotient series, concatenate with kernel series

5. **`isPolycyclic_of_finite`** (1 sorry, line 231)
   - Requires: Maximal normal subgroups, simple solvable = prime cyclic
   - Approach: Induction on cardinality

6. **`isPolycyclic_of_finiteIndex_polycyclic`** (1 sorry, line 512)
   - Requires: `isPolycyclic_of_extension`, normal core theory
   - Approach: Use normal core and extension

7. **`polycyclic_has_finiteIndex_nilpotent_normal_subgroup`** (1 sorry, line 175)
   - Requires: Fitting subgroup definition and properties
   - Approach: Build Fitting subgroup as maximal normal nilpotent

8. **`Subgroup.fg_of_polycyclic`** (3 sorries, lines 582-595)
   - Requires: `isPolycyclic_subgroup`, quotient machinery
   - Approach: Induction on series length

### Phase 2: Residual Finiteness

9. **`isResiduallyFinite_of_fg_nilpotent`** (4 sorries, lines 211-258)
   - Requires: Lower central series, abelianization FG
   - Approach: Induction on nilpotency class, use abelianization

### Phase 3: Reverse Direction Completion

10. **`malcev_subgroup_fg_of_fg_nilpotent`** (1 sorry, line 145)
    - Requires: `isPolycyclic_of_isNilpotent_fg`, `Subgroup.fg_of_polycyclic`
    - Approach: Compose: f.g. nilpotent → polycyclic → subgroups f.g.

11. **`cayleyBall_lift_bound_for_center_quotient`** (1 sorry, line 241)
    - Requires: Schreier theory, word length analysis
    - Approach: Bound via quotient map and Schreier rewrites

12. **`schreier_rewrite_bound`** (1 sorry, line 669)
    - Requires: Coset representative theory, word manipulation
    - Approach: Explicit Schreier rewrite algorithm

### Phase 4: Forward Direction

13. **`infinite_cyclic_quotient_of_polynomial_growth`** (1 sorry, line 335)
    - Requires: Harmonic function theory, Kleiner's theorem, Jordan's theorem
    - Approach: Build harmonic functions, analyze representation on finite-dim space

14. **`kernel_growth_degree_lt`** (1 sorry, line 411)
    - Requires: Fibration structure, coset counting, averaging arguments
    - Approach: Analyze level sets of G → Z, bound kernel ball size

15. **`isVirtuallyNilpotent_of_extension_by_Z`** (2 sorries, lines 508, 591)
    - Requires: Polycyclic extension theory, conjugation arguments
    - Approach: Use polycyclic characterization and extension results

---

## Infrastructure Requirements

### New Files/Modules

1. **Harmonic function infrastructure** (for item 13)
   - Discrete Laplacian spectral theory
   - Lipschitz harmonic function space
   - Elliptic regularity (Poincaré inequalities)

2. **Fitting subgroup** (for item 7)
   - Definition as maximal normal nilpotent subgroup
   - Finite index in polycyclic groups

3. **Schreier theory** (for items 11, 12)
   - Coset representatives
   - Word rewriting bounds

### Mathlib Dependencies

The following Mathlib APIs are used:
- `Subgroup.Normal`, `Subgroup.FiniteIndex`
- `Group.FG`, `Group.IsNilpotent`, `Group.IsSolvable`
- `lowerCentralSeries`, `nilpotencyClass`
- `QuotientGroup`, `Abelianization`

---

## Execution Queue

Execute files in this order (one at a time):

| Priority | File | Issue | Action |
|----------|------|-------|--------|
| 1 | NilpotentGrowth.lean | 8 compilation errors | Fix errors first |
| 2 | ResiduallyFinite.lean | 16 compilation errors | Fix errors |
| 3 | Polycyclic.lean | 8 sorries | Clear sorries |
| 4 | Descent.lean | 3 sorries | Clear sorries |

**Current:** NilpotentGrowth.lean (errors blocking build)

### Detailed File Guidance

#### 1. NilpotentGrowth.lean (Priority 1)
**Errors to fix:**
- Line 241: Syntax error - unexpected token '/--'
- Line 260: Unknown `List.map_prod` - use `List.prod_map` or prove manually
- Line 276: Unsolved goals in simp - need explicit term construction
- Line 286: Unknown `Subgroup.coe_list_prod` - use `Subgroup.coe_prod` or manual
- Line 321: Unknown `Set.ncard_bijOn` - use `Set.ncard_image_of_injective` or similar
- Line 361: Apply failed - need different approach for ncard bound
- Line 954: Clear failed - restructure proof to avoid clearing

**Sorries to clear:**
- `cayleyBall_lift_bound_for_center_quotient`: Bound Cayley ball size in central extensions
- `schreier_rewrite_bound`: Schreier's lemma word length bound

**Proof strategies:**
- For Cayley ball bounds: Use that center is normal, quotient map is surjective
- For Schreier: Use coset representatives, bound rewrite length by index * original length

#### 2. ResiduallyFinite.lean (Priority 2)
**Key errors:**
- Unknown constants: `Subgroup.top_le_iff`, `Subgroup.commutator_map_le`, `Subgroup.fg_of_finiteIndex`, `Subgroup.index_mul_index`, `Subgroup.FiniteIndex.normalCore`
- These don't exist in Mathlib - must prove them or find alternatives

**Proof strategy for `isResiduallyFinite_of_fg_nilpotent`:**
- Induction on nilpotency class
- Base case: abelian f.g. groups are residually finite (use structure theorem)
- Inductive step: Use lower central series, quotient by terms

#### 3. Polycyclic.lean (Priority 3)
**8 sorries - all are standard results from Segal's "Polycyclic Groups":**
- `isPolycyclic_of_isNilpotent_fg`: Induction on nilpotency class, each LCS quotient is f.g. abelian
- `polycyclic_has_finiteIndex_nilpotent_normal_subgroup`: Fitting subgroup has finite index
- `isPolycyclic_of_finite`: Induction on cardinality, use Jordan-Holder
- `isPolycyclic_subgroup`: Intersect polycyclic series with subgroup
- `isPolycyclic_of_le`: Transfer via inclusion
- `isPolycyclic_of_extension`: Concatenate series
- `isPolycyclic_of_finiteIndex_polycyclic`: Use normal core
- `Subgroup.fg_of_polycyclic`: Mal'cev's theorem, induction on series length

**If stuck:** These are interdependent. May need to prove them in a specific order or introduce helper lemmas about polycyclic series manipulation.

#### 4. Descent.lean (Priority 4)
**3 sorries - hardest theorems in the project:**
- `infinite_cyclic_quotient_of_polynomial_growth`: Kleiner's theorem - polynomial growth implies finite-dim harmonic function space, extract Z quotient
- `kernel_growth_degree_lt`: Growth degree drops by 1 when passing to kernel of G → Z
- `isVirtuallyNilpotent_of_extension_by_Z`: Extensions of virtually nilpotent by Z are virtually nilpotent

**These require the most infrastructure.** May need:
- Harmonic function theory (partially in Harmonic.lean, Poincare.lean)
- Representation theory on harmonic space
- Compact Lie group theory (Jordan's theorem)

**If infrastructure is missing:** Create helper files in `Gromov/Proofs/` for any needed theory.

---

## Tracking

| File | Errors | Sorries | Status |
|------|--------|---------|--------|
| NilpotentGrowth.lean | 8 | 2 | BLOCKING |
| ResiduallyFinite.lean | 16 | 0 | pending |
| Polycyclic.lean | 0 | 8 | pending |
| Descent.lean | 0 | 3 | pending |
| **Total** | **24** | **13** | |
