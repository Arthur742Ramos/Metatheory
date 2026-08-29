# Palomar certificate package

This is the standalone Lean 4.33.0 submission surface for the decreasing-
diagram certificate formalization. The selected result is generic: a finite
certificate artifact lists every step of a labeled abstract rewriting system,
records decreasing valleys for its local peaks, and is accepted only when its
Boolean checker validates the data. If the table is complete for the semantic
relation, successful checking implies confluence of the unlabeled relation.

The statement in `Challenge.lean` imports only `Std`; it does not import the
parent repository or any project-local implementation module. `PalomarProof.lean`
contains the proof-side development used by `Solution.lean`.

The checked representation has four independent components:

- `Edge` records a labeled one-step reduction.
- `PeakCertificate` records two paths to a common valley.
- `checkB` checks step validity, all finite same-source peaks, decreasing path
  labels, and canonical certificate orientation.
- `StepsComplete` is the explicit semantic bridge that prevents an omitted
  real step from being hidden by a finite checker.

`Checks.lean` exercises the theorem on an eight-node, ten-rule funnel with
three distinct local peaks and a four-step cycle. Its positive certificate is
accepted, while missing peak coverage, an invalid valley, and the reversed
orientation are rejected. The parent repository additionally contains a
generated indexed family and benchmark corpus for measuring canonical
certificate compression; those artifacts are supporting evaluation material,
not hidden dependencies of the Challenge.

The formal result is source-based: it formalizes the symmetric strict
decreasing-diagram proof pattern associated with van Oostrom’s work, while the
certificate data model, executable checker boundary, completeness bridge, and
negative regression suite are the contribution of this package. It claims no
new confluence criterion, no priority over the cited mathematics, and no
termination of the underlying rewrite relation.

Run the local gate from this directory:

```bash
./check.sh
```

For the Palomar submission form, select project directory `palomar`,
Comparator path `palomar/comparator.json`, and metadata path
`formalization.yaml`; the repository-root `LICENSE` covers the snapshot.
