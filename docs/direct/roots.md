# Roots And No-Root Proofs

Use this path for root existence, uniqueness, and no-root goals over an
interval.

Typical goals:

```lean
∃ x ∈ I, f x = 0
∃! x ∈ I, f x = 0
∀ x ∈ I, f x ≠ 0
```

Main tools:

```lean
interval_roots
interval_unique_root
root_bound
```

Architecture background for how the certified root pipeline works is in
[Root Finding](../architecture/root-finding.md).

For tactic details, see [Reference → Tactics](../reference/tactics.md).
