/-
# Project Metrics

This module provides a summary of the Metatheory confluence framework,
useful for documentation and paper submissions.

## Framework Statistics

The framework consists of:
- **Generic ARS layer**: Reusable confluence infrastructure
- **4 case studies**: Lambda calculus, Combinatory Logic, Simple TRS, String Rewriting
- **3 proof techniques (fully proved)**: Diamond property, Newman's lemma, Hindley-Rosen
- **1 framework module**: Decreasing diagrams (definitions only, theorem requires additional infrastructure)

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
import Metatheory.STLCextBool.CBV
import Metatheory.STLCextBool.Confluence
import Metatheory.SystemF.Confluence

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
  #check @Rewriting.confluent_of_locallyDecreasing
  -- Note: decreasing diagrams are implemented in `Metatheory.Rewriting.DecreasingDiagrams`.

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

-- STLC with Booleans
#check @Metatheory.STLCextBool.confluence
#check @Metatheory.STLCextBool.cbv_confluent

-- System F
#check @Metatheory.SystemF.confluence
#check @Metatheory.SystemF.parRed_diamond
#check @Metatheory.SystemF.strongStep_confluent

end MainTheorems

/-! ## Proof Technique Summary

### Diamond Property Approach (Lambda, CL, System F)

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

## Proof Status

**NO SORRIES** - All theorems in the codebase are fully proved!

The decreasing diagrams confluence theorem is not included yet. The definitions are available
for future work, and the required front-building closure is now available as `Rewriting.StarHead`.
All main confluence results use alternative techniques.

### Lambda Calculus De Bruijn Infrastructure (ALL PROVED)
- `shift_zero`: Shifting by 0 is identity
- `shift_shift`: Composing shifts at same cutoff
- `shift_shift_comm`: Shifts at different cutoffs commute
- `shift_shift_succ`: shift 1 (c+1) (shift 1 c M) = shift 2 c M
- `shift_shift_offset`: shift 1 (c+b) (shift c b N) = shift (c+1) b N
- `shift_subst_at`: Generalized shift-substitution interaction
- `shift_subst`: Shift-substitution interaction at cutoff 0
- `subst_shift_cancel`: Substituting after shift cancels
- **`subst_subst_gen`**: Substitution composition (~90 lines via generalized lemma)

### Combinatory Logic (ALL PROVED)
- **`parRed_complete`**: Parallel reduction reaches complete development

### Simply Typed Lambda Calculus (ALL PROVED)
- `weakening`: Types preserved under context weakening
- `progress`: Well-typed closed terms are values or can reduce
- `typing_shift`: Shifting preserves typing
- `typing_shift_at`: Generalized shift typing for arbitrary cutoffs
- `cr1_reducible_sn`: Reducible terms are SN
- `cr2_reducible_red`: Reducibility is closed under reduction
- `cr3_neutral`: Neutral terms with reducible reducts are reducible
- **`reducible_app_lam`**: Beta redexes are reducible (~108 lines)
- **`liftSubst_n_spec`**: Characterization of iterated liftSubst
- **`subst_applySubst_gen`**: Generalized substitution-applySubst composition
- `fundamental_lemma`: Well-typed terms are reducible
- `strong_normalization`: Well-typed terms are SN
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
| SystemF/ | 11 | System F (polymorphic λ-calculus) |
| Root | 2 | Main entry + Metrics |
| **Total** | **41** | |

## Key Definitions Count

| Module | Definitions | Theorems | Axioms |
|--------|-------------|----------|--------|
| Rewriting/Basic | 8 | 15 | 0 |
| Rewriting/Diamond | 0 | 4 | 0 |
| Rewriting/Newman | 0 | 6 | 0 |
| Rewriting/HindleyRosen | 2 | 7 | 0 |
| Rewriting/DecreasingDiagrams | 4 | 7 | 0 |
| Lambda/Term | 8 | 15 | 0 |
| Lambda/* | 10 | 12 | 0 |
| CL/* | 6 | 10 | 0 |
| TRS/* | 4 | 8 | 0 |
| StringRewriting/* | 2 | 8 | 0 |
| STLC/* | 10 | 25 | 0 |
| SystemF/* | 12 | 50+ | 0 |
| **Total Sorrys** | | | **0** |
-/
