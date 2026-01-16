/-
# Generic Confluence Framework for Lean 4

This is the main entry point for a generic confluence framework
with multiple case studies demonstrating different proof techniques.

## Main Results

1. **Generic Framework** (Rewriting/):
   - Diamond property implies confluence
   - Newman's lemma: termination + local confluence → confluence
   - Decreasing diagrams: labeled confluence criterion (van Oostrom 1994)
   - Hindley-Rosen lemma: commuting confluent relations

2. **Lambda Calculus** (Lambda/):
   - Church-Rosser theorem via parallel reduction
   - Demonstrates diamond property approach

3. **Combinatory Logic** (CL/):
   - Church-Rosser theorem via parallel reduction
   - Simpler than λ-calculus (no binders)

4. **Simple TRS** (TRS/):
   - Expression simplification rewriting
   - Demonstrates Newman's lemma approach

5. **String Rewriting** (StringRewriting/):
   - Idempotent string reduction (aa→a, bb→b)
   - Demonstrates Newman's lemma approach

6. **Simply Typed Lambda Calculus** (STLC/):
   - Simple types and typing relation
   - Subject reduction (type preservation)
   - Strong normalization (all well-typed terms terminate)

7. **STLC with Booleans** (STLCextBool/):
    - Booleans and conditionals
    - Subject reduction and progress
    - Confluence via parallel reduction
    - CBV determinism (strategy-level)
    - Strong normalization via erasure

8. **System F** (SystemF/):
   - Polymorphic types with universal quantification
   - Type abstraction and application
   - Progress theorem for closed terms
   - Church-Rosser theorem via parallel reduction


## Project Structure

The project is organized into layers:

### Layer 0: Generic Framework (Rewriting/)
- Basic.lean: Core ARS definitions (Star, Joinable, Diamond, Confluent, etc.)
- Diamond.lean: Diamond property implies confluence
- Newman.lean: Newman's lemma (termination + local confluence → confluence)
- DecreasingDiagrams.lean: van Oostrom's decreasing diagrams technique
- HindleyRosen.lean: Union of commuting confluent relations

### Layer 1a: Lambda Calculus (Lambda/)
- Term.lean: De Bruijn indexed terms
- Beta.lean: Single-step beta reduction
- Parallel.lean: Parallel reduction (key for Church-Rosser)
- Complete.lean: Complete development (Takahashi method)
- Confluence.lean: The Church-Rosser theorem

### Layer 1b: Combinatory Logic (CL/)
- Syntax.lean: S, K combinators and application
- Reduction.lean: Weak reduction rules
- Parallel.lean: Parallel reduction
- Confluence.lean: Church-Rosser via diamond property

### Layer 2a: Simple TRS (TRS/)
- Syntax.lean: Expression syntax (0, 1, +, *)
- Rules.lean: Rewriting rules
- Confluence.lean: Confluence via Newman's lemma

### Layer 2b: String Rewriting (StringRewriting/)
- Syntax.lean: Alphabet and string operations
- Rules.lean: Idempotent reduction rules
- Confluence.lean: Confluence via Newman's lemma

### Layer 3: Simply Typed Lambda Calculus (STLC/)
- Types.lean: Simple types (base types and arrows)
- Terms.lean: Re-exports untyped terms
- Typing.lean: Typing relation and subject reduction
- Normalization.lean: Strong normalization via logical relations

### Layer 4: Extended STLC with Products and Sums (STLCext/)
- Types.lean: Simple types with products (A × B) and sums (A + B)
- Terms.lean: De Bruijn terms with pairs, projections, injections, case
- Reduction.lean: Beta + product/sum reduction rules
- Typing.lean: Extended typing rules and subject reduction
- Normalization.lean: Strong normalization via logical relations

### Layer 4b: STLC with Booleans (STLCextBool/)
- Types.lean: Simple types with booleans
- Terms.lean: De Bruijn terms with true/false/ite
- Reduction.lean: Beta + conditional reduction rules
- CBV.lean: Call-by-value reduction (deterministic)
- Parallel.lean: Parallel reduction (diamond property tool)
- Complete.lean: Complete development for parallel reduction
- Confluence.lean: Church-Rosser theorem
- Typing.lean: Typing, subject reduction, progress
- Normalization.lean: Strong normalization via erasure

### Layer 5: System F (SystemF/)

- Types.lean: Polymorphic types with de Bruijn indices
- Terms.lean: Terms with type abstraction (Λ) and application ([τ])
- Typing.lean: Typing relation with progress theorem
- Parallel.lean: Parallel reduction (key for Church-Rosser)
- Complete.lean: Complete development (Takahashi method)
- Diamond.lean: Diamond property for parallel reduction
- Confluence.lean: The Church-Rosser theorem

## Proof Techniques Demonstrated

| System | Technique | Key Property |
|--------|-----------|--------------|
| Lambda | Parallel reduction | Diamond property |
| CL     | Parallel reduction | Diamond property |
| TRS    | Size measure | Termination + local confluence |
| StringRewriting | Length measure | Termination + local confluence |
| STLC   | Typing discipline | Subject reduction |
| STLCext | Logical relations | Strong normalization (products + sums) |
| STLCextBool | Parallel reduction + erasure | Confluence + progress + CBV determinism |
| System F | Parallel reduction | Diamond property + Progress theorem |
| Tiny TRS | Diamond/Newman | Confluence comparison |


## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Barendregt, "The Lambda Calculus: Its Syntax and Semantics"
- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
- Terese, "Term Rewriting Systems" (2003)
- Huet, "Confluent Reductions: Abstract Properties and Applications" (1980)
- Hindley & Seldin, "Lambda-Calculus and Combinators" (2008)
-/

-- Generic rewriting framework
import Metatheory.Rewriting.Basic
import Metatheory.Rewriting.Diamond
import Metatheory.Rewriting.Newman
import Metatheory.Rewriting.HindleyRosen
import Metatheory.Rewriting.DecreasingDiagrams
import Metatheory.Rewriting.Compat

-- Lambda calculus instance
import Metatheory.Lambda.Term
import Metatheory.Lambda.Beta
import Metatheory.Lambda.MultiStep
import Metatheory.Lambda.Parallel
import Metatheory.Lambda.Complete
import Metatheory.Lambda.Diamond
import Metatheory.Lambda.Confluence
import Metatheory.Lambda.Generic
import Metatheory.Lambda.CBV

-- Combinatory Logic instance
import Metatheory.CL.Syntax
import Metatheory.CL.Reduction
import Metatheory.CL.Parallel
import Metatheory.CL.Confluence

-- Simple TRS instance
import Metatheory.TRS.Syntax
import Metatheory.TRS.Rules
import Metatheory.TRS.Confluence
import Metatheory.TRS.DiamondComparison


-- String Rewriting instance
import Metatheory.StringRewriting.Syntax
import Metatheory.StringRewriting.Rules
import Metatheory.StringRewriting.Confluence

-- Simply Typed Lambda Calculus
import Metatheory.STLC.Types
import Metatheory.STLC.Terms
import Metatheory.STLC.Typing
import Metatheory.STLC.Normalization

-- Extended STLC with Products and Sums
import Metatheory.STLCext.Types
import Metatheory.STLCext.Terms
import Metatheory.STLCext.Reduction
import Metatheory.STLCext.Parallel
import Metatheory.STLCext.Complete
import Metatheory.STLCext.Confluence
import Metatheory.STLCext.Typing
import Metatheory.STLCext.Normalization

-- STLC with Booleans
import Metatheory.STLCextBool.Types
import Metatheory.STLCextBool.Terms
import Metatheory.STLCextBool.Reduction
import Metatheory.STLCextBool.CBV
import Metatheory.STLCextBool.Parallel
import Metatheory.STLCextBool.Complete
import Metatheory.STLCextBool.Confluence
import Metatheory.STLCextBool.Typing
import Metatheory.STLCextBool.Normalization

-- System F (Polymorphic Lambda Calculus)

import Metatheory.SystemF.Types
import Metatheory.SystemF.Terms
import Metatheory.SystemF.Typing
import Metatheory.SystemF.StrongReduction
import Metatheory.SystemF.StrongNormalization
import Metatheory.SystemF.SubjectReduction
import Metatheory.SystemF.Parallel
import Metatheory.SystemF.Complete
import Metatheory.SystemF.Diamond
import Metatheory.SystemF.Confluence

-- Metrics (optional, for documentation)
import Metatheory.Metrics

namespace Metatheory

/-! ## Main Theorems -/

-- Generic framework: decreasing diagrams (van Oostrom)
#check @Rewriting.LabeledARS
#check @Rewriting.LocallyDecreasing
#check @Rewriting.confluent_of_locallyDecreasing

-- Lambda calculus Church-Rosser
open Lambda in
#check @confluence

-- Combinatory Logic Church-Rosser
open CL in
#check @confluent

-- TRS confluence
open TRS in
#check @confluent

-- String Rewriting confluence
open StringRewriting in
#check @confluent

-- STLC subject reduction
open STLC in
#check @subject_reduction

-- STLC strong normalization
open STLC in
#check @strong_normalization

-- STLCext subject reduction
open STLCext in
#check @subject_reduction

-- STLCext progress
open STLCext in
#check @progress

-- STLCextBool confluence
open STLCextBool in
#check @confluence
open STLCextBool in
#check @cbv_confluent

-- System F typing with progress
open SystemF in
#check @HasType
open SystemF in
#check @progress
open SystemF in
#check @SN

-- System F confluence (Church-Rosser)
open SystemF in
#check @confluence
open SystemF in
#check @strongStep_confluent

end Metatheory
