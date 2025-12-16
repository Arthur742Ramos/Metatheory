# Add New Rewriting System Case Study

Create a new case study for a rewriting system following the established patterns in this codebase.

## Arguments
- $ARGUMENTS: Name of the new rewriting system (e.g., "SKI", "SystemF", "PCF")

## Instructions

1. **Analyze the request**: Determine the name and nature of the rewriting system from: $ARGUMENTS

2. **Create directory structure**: Create `Metatheory/<Name>/` with these files:
   - `Syntax.lean` - Term syntax and basic operations
   - `Reduction.lean` or `Rules.lean` - Reduction rules
   - `Confluence.lean` - Confluence proof

3. **Choose proof technique** based on the system:
   - **Diamond property approach** (like Lambda/, CL/): For systems with natural parallel reduction
   - **Newman's lemma approach** (like TRS/, StringRewriting/): For terminating systems

4. **Follow existing patterns**:
   - Use `Metatheory.<Name>` namespace
   - Include module docstrings with `/-! ... -/`
   - Reference relevant literature
   - NO sorries - all proofs must be complete

5. **Update main module**: Add imports to `Metatheory.lean`

## Template for Syntax.lean

```lean
/-
# <Name> - Syntax

Description of the term language.

## References
- [Add relevant papers/books]
-/

namespace Metatheory.<Name>

/-- Term syntax for <Name> -/
inductive Term : Type where
  | -- Add constructors
  deriving Repr, DecidableEq

namespace Term

-- Add notation, basic operations, size function if needed

end Term

end Metatheory.<Name>
```

## Template for Confluence proof (Diamond approach)

```lean
import Metatheory.<Name>.Parallel
import Metatheory.Rewriting.Diamond

namespace Metatheory.<Name>

/-- Diamond property for parallel reduction -/
theorem parRed_diamond : Rewriting.Diamond ParRed := by
  -- Prove via complete development or direct case analysis

/-- Confluence of <Name> -/
theorem confluent : Rewriting.Confluent Step :=
  -- Bridge to ParRed and apply confluent_of_diamond

end Metatheory.<Name>
```

## Template for Confluence proof (Newman approach)

```lean
import Metatheory.<Name>.Rules
import Metatheory.Rewriting.Newman

namespace Metatheory.<Name>

/-- Termination via measure -/
theorem step_terminating : Rewriting.Terminating Step := by
  -- Prove via size/complexity measure

/-- Local confluence by critical pair analysis -/
theorem local_confluent : Rewriting.LocalConfluent Step := by
  -- Exhaustive case analysis

/-- Confluence via Newman's lemma -/
theorem confluent : Rewriting.Confluent Step :=
  Rewriting.confluent_of_terminating_localConfluent step_terminating local_confluent

end Metatheory.<Name>
```
