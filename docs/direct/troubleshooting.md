# Direct Automation Troubleshooting

Most direct automation failures come from one of four causes:

- the expression is not supported by the selected backend;
- the interval is too wide or subdivision depth is too low;
- the requested bound is false or has too little margin;
- the tactic needs a domain side condition such as positivity or nonzero
  denominator information.

Start with the existing troubleshooting guide:

[Tactics Troubleshooting](../tactics/troubleshooting.md)

For generated data or many-row failures, use certificate APIs with audit output
such as `TableCert.failingIndices` or `InequalityTableCert.failingIndices`.
