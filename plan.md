# Gromov Project Execution Plan

## Quick Reference

**Current focus**: Phase 1 - Quick Wins & Unblocking
**Total sorries**: ~126 across 17 files
**Build command**: `lake build 2>&1 | head -100`
**Verify command**: `lake exe tailverify`

## Execution Queue

### Phase 1: Quick Wins & Unblocking

| Status | File | Sorries | Notes |
|--------|------|---------|-------|
| [ ] | `Polycyclic/ResiduallyFinite.lean` | 1 | Quick win |
| [ ] | `Growth/Nilpotent.lean` | 2 | Reverse direction |
| [ ] | `Descent/Main.lean` | 2 | Main theorem |
| [ ] | `Polycyclic/Core.lean` | 6 | Unblocks 5 files |

### Phase 2: Polycyclic Theory (requires 1.4)

| Status | File | Sorries |
|--------|------|---------|
| [ ] | `Polycyclic/Abelian.lean` | 5 |
| [ ] | `Polycyclic/Fitting.lean` | 5 |
| [ ] | `Polycyclic/Malcev.lean` | 8 |
| [ ] | `Polycyclic/Extensions.lean` | 6 |

### Phase 3: Schreier Theory

| Status | File | Sorries |
|--------|------|---------|
| [ ] | `Schreier/CosetReps.lean` | 7 |
| [ ] | `Schreier/WordBounds.lean` | 8 |

### Phase 4: Growth Theory

| Status | File | Sorries |
|--------|------|---------|
| [ ] | `Growth/Fibration.lean` | 16 |
| [ ] | `Growth/KernelDegree.lean` | 12 |

### Phase 5: Harmonic Analysis (longest chain)

| Status | File | Sorries |
|--------|------|---------|
| [ ] | `Harmonic/Spectral.lean` | 11 |
| [ ] | `Harmonic/Existence.lean` | 10 |
| [ ] | `Harmonic/FiniteDim.lean` | 14 |

### Phase 6: Representation Theory

| Status | File | Sorries |
|--------|------|---------|
| [ ] | `Representation/CompactLie.lean` | 4 |
| [ ] | `Representation/QuotientExtraction.lean` | 9 |

## Dependency Structure

```
FOUNDATION (COMPLETE)
├── Definitions/*, Growth.{GromovMain,Polynomial,Abelian}
├── Cayley.Graph, VirtuallyNilpotent.Core, Harmonic.Core, Poincare.Main

LAYER 1 (Independent)
├── Polycyclic.Core (6) ← BLOCKS all Polycyclic
├── Harmonic.Spectral (11) ← BLOCKS Existence chain
├── Growth.Fibration (16) ← BLOCKS KernelDegree
└── Schreier.CosetReps (7) ← BLOCKS WordBounds

LAYER 2 (Blocked by Layer 1)
├── Polycyclic.{Abelian,Fitting,Malcev,Extensions}
├── Growth.KernelDegree, Growth.Nilpotent
├── Harmonic.Existence, Schreier.WordBounds

LAYER 3 (Blocked by Layer 2)
├── Polycyclic.ResiduallyFinite (1)
├── Harmonic.FiniteDim (14)
└── Representation.CompactLie (4)

LAYER 4 (Final)
├── Representation.QuotientExtraction (9)
└── Descent.Main (2) ← MAIN THEOREM
```

## File Paths

All proof files under `/Users/eric/Documents/GitHub/Gromov/Gromov/Proofs/`

## Agent Instructions Template

When spawning agents, include:

```
STRICT REQUIREMENTS:
1. NEVER write `axiom` or `private axiom` declarations
2. NEVER write `sorry` as a final solution
3. NEVER use `native_decide` on undecidable propositions
4. If stuck, leave existing `sorry` - do NOT convert to axiom
5. Run `lake exe tailverify` before reporting completion
6. Run `grep -n "^axiom" <file>` to verify no axioms introduced
```

## Success Criteria

- All sorries replaced with proofs
- `lake exe tailverify` passes
- No axiom declarations
- Build completes without errors
