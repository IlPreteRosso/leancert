# Integration

Use this path when the goal is a certified definite-integral enclosure.

Typical goals:

```lean
∫ x in a..b, f x ∈ B
lo ≤ ∫ x in a..b, f x
∫ x in a..b, f x ≤ hi
```

Main tools:

```lean
interval_integrate
integrateInterval
```

For Taylor-model generated integral certificates, see
[Proof Templates → ConstantFactory](../proof-templates/constant-factory.md) and the
Taylor integration notes there.
