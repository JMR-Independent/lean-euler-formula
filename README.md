# Euler's Polyhedron Formula — Lean 4 + Mathlib

Formalization of **V - E + F = 2** for connected planar graphs.

## Main Results

| Theorem | Statement |
|---------|-----------|
| `PlanarGraph.euler_formula` | `V + F = E + 2` |
| `PlanarGraph.euler_int` | `(V : ℤ) - E + F = 2` |
| `PlanarGraph.k5_not_planar` | K₅ is not planar |
| `PlanarGraph.k33_not_planar` | K₃,₃ is not planar |

## Approach

`PlanarGraph V E F` is an inductive type with three constructors:
- `point` — single vertex (1, 0, 1)
- `addLeaf` — attach pendant vertex+edge (V+1, E+1, F)
- `addEdge` — split a face (V, E+1, F+1)

Euler's formula follows by structural induction; `omega` closes all cases.

## Build

```bash
lake build
```

## Background

This formalization accompanies a standalone (no-Mathlib) version:
- Pick's theorem: complete, 0 sorry
- Euler's formula (core Lean 4): complete, 0 sorry
