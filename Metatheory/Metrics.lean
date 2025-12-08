/-
# Project Metrics

This module provides a summary of the Metatheory confluence framework,
useful for documentation and paper submissions.

## Framework Statistics

The framework consists of:
- **Generic ARS layer**: Reusable confluence infrastructure
- **4 case studies**: Lambda calculus, Combinatory Logic, Simple TRS, String Rewriting
- **4 proof techniques**: Diamond property, Newman's lemma, Hindley-Rosen, Decreasing diagrams

## Compile this file to see metrics output
-/

import Metatheory.Rewriting.Basic
import Metatheory.Rewriting.Diamond
import Metatheory.Rewriting.Newman
import Metatheory.Rewriting.HindleyRosen
import Metatheory.Rewriting.DecreasingDiagrams
import Metatheory.Rewriting.Compat
import Metatheory.Lambda.Confluence
import Metatheory.Lambda.Generic
import Metatheory.CL.Confluence
import Metatheory.TRS.Confluence
import Metatheory.StringRewriting.Confluence
import Metatheory.STLC.Typing
import Metatheory.STLC.Normalization

/-! ## Framework Summary -/

#check @Rewriting.Diamond           -- Generic diamond property
#check @Rewriting.Confluent         -- Generic confluence
#check @Rewriting.Terminating       -- Generic termination
#check @Rewriting.LocalConfluent    -- Generic local confluence

/-! ## Main Theorems -/

section MainTheorems

-- Generic framework theorems
#check @Rewriting.confluent_of_diamond
#check @Rewriting.confluent_of_terminating_localConfluent
#check @Rewriting.confluent_union  -- Hindley-Rosen lemma
#check @Rewriting.confluent_of_locallyDecreasing  -- Decreasing diagrams

-- Lambda calculus
#check @Metatheory.Lambda.confluence
#check @Metatheory.Lambda.parRed_diamond

-- Combinatory Logic
#check @Metatheory.CL.confluent
#check @Metatheory.CL.church_rosser

-- Simple TRS
#check @Metatheory.TRS.confluent
#check @Metatheory.TRS.church_rosser

-- String Rewriting
#check @Metatheory.StringRewriting.confluent
#check @Metatheory.StringRewriting.church_rosser

-- Simply Typed Lambda Calculus
#check @Metatheory.STLC.subject_reduction
#check @Metatheory.STLC.subject_reduction_multi
#check @Metatheory.STLC.strong_normalization

end MainTheorems

/-! ## Proof Technique Summary

### Diamond Property Approach (Lambda, CL)

The diamond property approach works by:
1. Defining a parallel reduction relation that allows simultaneous contraction
2. Proving parallel reduction has the diamond property via complete development
3. Showing: weak reduction ⊆ parallel reduction ⊆ weak reduction*
4. Deriving confluence from diamond property

Key advantage: Works for non-terminating systems (e.g., untyped λ-calculus)

### Newman's Lemma Approach (TRS)

Newman's lemma approach works by:
1. Proving the system is terminating (well-founded)
2. Proving local confluence (one-step divergences can be joined)
3. Applying Newman's lemma: termination + local confluence → confluence

Key advantage: Local confluence is often easier to verify than diamond property

## Axiom Summary

Axioms are used for standard lemmas with tedious but well-understood proofs:

### Lambda Calculus De Bruijn Infrastructure
- `shift_shift_comm`: Commuting shifts at different cutoffs
- `shift_subst_below`: Shift-substitution interaction
- `shift_subst`: Shift-substitution at cutoff 0
- `subst_subst`: Double substitution lemma
- `subst_subst_gen`: Generalized substitution composition

### Combinatory Logic
- `parRed_complete`: Parallel reduction reaches complete development

### Hindley-Rosen (Generic Framework)
- `swap_step`: Sequential swap (s;r ⊆ r;s) for commuting relations

### Decreasing Diagrams (Generic Framework)
- `confluent_of_locallyDecreasing`: Main decreasing diagrams theorem (van Oostrom 1994)

### String Rewriting
- `local_confluent`: Local confluence of idempotent string rewriting

### Simply Typed Lambda Calculus (Typing)
- `substitution_typing`: Types are preserved under substitution

### Simply Typed Lambda Calculus (Normalization)
- `subst0_step_left`: Substitution preserves reduction in body
- `subst0_step_right`: Substitution preserves reduction in argument
- `reducible_app_lam`: Beta redexes are reducible given reducible components
- `subst_applySubst_lift`: Interaction between single and parallel substitution

**Note:** The following were proven (not axiomatized):
- `weakening`: Types preserved under context weakening
- `progress`: Well-typed closed terms are values or can reduce
- `typing_shift`: Shifting preserves typing (with generalized shift_at lemma)
- `typing_shift_at`: Generalized shift typing for arbitrary cutoffs
- `cr1_reducible_sn`: Reducible terms are SN (via cr_props_all)
- `cr2_reducible_red`: Reducibility is closed under reduction
- `cr3_neutral`: Neutral terms with reducible reducts are reducible
- `fundamental_lemma`: Well-typed terms are reducible under reducible substitution (uses reducible_app_lam)
- `strong_normalization`: Well-typed terms are SN (uses fundamental_lemma + CR1)

All axioms are standard results from the literature with clear references.
-/

/-! ## File Statistics (approximate)

| Component | Files | Purpose |
|-----------|-------|---------|
| Rewriting/ | 6 | Generic ARS framework |
| Lambda/ | 8 | Lambda calculus case study |
| CL/ | 4 | Combinatory Logic case study |
| TRS/ | 3 | Simple TRS case study |
| StringRewriting/ | 3 | String rewriting case study |
| STLC/ | 4 | Simply typed lambda calculus |
| Root | 2 | Main entry + Metrics |
| **Total** | **30** | |

## Key Definitions Count

| Module | Definitions | Theorems | Axioms |
|--------|-------------|----------|--------|
| Rewriting/Basic | 8 | 15 | 0 |
| Rewriting/Diamond | 0 | 4 | 0 |
| Rewriting/Newman | 0 | 6 | 0 |
| Rewriting/HindleyRosen | 2 | 7 | 1 |
| Rewriting/DecreasingDiagrams | 4 | 8 | 1 |
| Lambda/Term | 8 | 8 | 5 |
| Lambda/* | 10 | 12 | 0 |
| CL/* | 6 | 10 | 1 |
| TRS/* | 4 | 8 | 0 |
| StringRewriting/* | 2 | 8 | 1 |
| STLC/* | 10 | 20 | 5 |
-/
