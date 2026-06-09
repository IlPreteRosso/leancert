# Optimization And Discovery

Use this path when the proof needs a certified global minimum, maximum, or a
candidate bound found by search.

Typical goals:

```lean
∃ M, ∀ x ∈ I, f x ≤ M
∀ x ∈ I, m ≤ f x
```

Main tools:

```lean
interval_minimize
interval_maximize
findGlobalMin
findGlobalMax
```

Discovery mode is useful when you do not yet know the bound or extremum.  See
the existing [Discovery Mode](../tactics/discovery.md) reference for command
syntax and examples.
