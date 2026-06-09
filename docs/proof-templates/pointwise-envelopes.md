# Pointwise Envelopes

Use `PointwiseEnvelope` for real-variable estimates:

```text
function on a domain
+ main approximation
+ nonnegative error radius
= pointwise lower and upper bounds
```

Core API:

```lean
PointwiseEnvelope
PointwiseEnvelope.lower
PointwiseEnvelope.upper
PointwiseEnvelope.lower_le_value
PointwiseEnvelope.value_le_upper
PointwiseEnvelope.weakenError
```

Algebra:

```lean
PointwiseEnvelope.add
PointwiseEnvelope.neg
PointwiseEnvelope.sub
PointwiseEnvelope.constMul
```

To convert a discrete summatory `AsympEnv` into a real-variable floor envelope:

```lean
AsympEnv.toPointwiseFloorEnvelope
```

Detailed API reference: [Asymptotic Envelope Certificates](../certificates/ant-asymp.md).
