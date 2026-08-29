# Palomar certificate package

This directory is the minimal, independently compilable surface for the
selected result from Metatheory. It uses Lean 4.33.0 and imports only `Std`.
It does not import the parent `Metatheory` library.

The semantic system has four nodes and five rules:

| label | source | target |
| ---: | --- | --- |
| 3 | `root` | `left` |
| 3 | `root` | `right` |
| 2 | `left` | `join` |
| 2 | `right` | `join` |
| 1 | `join` | `root` |

The only nontrivial local peak is the label-3 fork at `root`. Its two label-2
routes meet at `join`, so the certificate is decreasing. The label-1 return
edge makes the unlabeled system cyclic; confluence comes from the well-founded
label order, not from termination of the node relation.

`SemanticStep` is the proposition-level relation. `semanticStepB` and `checkB`
are executable Boolean definitions. `semanticSteps_complete` proves that the
finite step table covers every semantic rule, and
`strictPackageValid_of_checkB_eq_true` reflects successful execution into the
proposition-level package before the generic decreasing-diagram theorem is
applied.

The reusable theorem `checked_complete_confluence` abstracts the final step:
for any checked certificate list whose exported steps are complete for
`SemanticStep`, the unlabeled union relation is confluent. `main_result`
instantiates that theorem with the concrete five-step package.

The separate `Checks.lean` file contains positive and negative regressions:
the accepted certificate succeeds, while an empty certificate, a symmetric
duplicate, and a bad valley fail.

Run the complete local gate from this directory:

```bash
lake build
./check.sh
```

The root repository can be checked independently with:

```bash
cd ..
lake build Metatheory ddcert
```

`Challenge.lean` contains the two deliberate statement-side holes expected by
the Challenge/Solution comparison. `Solution.lean` is the proof artifact and
has no placeholders.
