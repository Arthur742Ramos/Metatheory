# Metatheory

[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-blue.svg)](https://lean-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A comprehensive **programming language metatheory library for Lean 4**, now spanning **130+ Lean files and 58K+ lines** of mechanized proofs and metatheoretic case studies.

## Overview

Metatheory formalizes core results from programming language theory:

- **Generic Rewriting Framework**: Abstract rewriting systems with multiple confluence proof techniques
- **Decreasing Diagrams**: Non-terminating confluence example and parameterized family
- **Lambda Calculus**: Church-Rosser theorem via parallel reduction (Takahashi's method), βη-confluence via Hindley-Rosen, call-by-value reduction
- **Combinatory Logic**: Confluence of SK-combinators, derived combinators (I, B, C, W) with identity proofs
- **Simply Typed Lambda Calculus**: Subject reduction and strong normalization (Tait's method)
- **Extended STLC**: Products, sums, and unit type with progress and strong normalization
- **STLC with Booleans**: Conditional reduction with subject reduction, progress, confluence, and CBV determinism
- **System F** (Polymorphic Lambda Calculus): Subject reduction with type substitution
- **Term/String Rewriting**: Confluence via Newman's lemma, critical pair analysis, and first-order TRS completion (KBO/LPO)
- **TRS Proof Comparison**: Diamond vs Newman confluence for a tiny deterministic TRS
- **Extended Formalizations**: 78 standalone modules covering type systems, semantics, compilation, effects, logic, macros, and automation

### Project Scale

- **Tracked Lean files**: 155 (`git ls-files '*.lean'`)
- **Tracked Lean LOC**: 58,126
- **Lean files under `Metatheory/`**: 153
- **Standalone modules under `Metatheory/*.lean`**: 78
- **Top-level dependency model**: no Mathlib requirement in `lakefile.toml`; many standalone modules are self-contained


### Why Metatheory?

| Feature | Benefit |
|---------|---------|
| **Multiple proof techniques** | Learn different approaches to confluence (Diamond, Newman, Hindley-Rosen) |
| **Layered architecture** | Generic framework instantiated by specific systems |
| **De Bruijn indices** | Capture-avoiding substitution without alpha-equivalence |
| **Dependency-light design** | Top-level build has no Mathlib requirement; many modules are self-contained |
| **Axiom/placeholder free** | No `axiom`/`constant` declarations and no `sorry`/`admit` |
| **Extensively documented** | Docstrings, references, and proof explanations |

## Installation

### Prerequisites

- [Lean 4](https://lean-lang.org/lean4/doc/setup.html) (version 4.24.0 or compatible)
- [Lake](https://github.com/leanprover/lake) (included with Lean)

### Building

```bash
git clone https://github.com/Arthur742Ramos/Metatheory.git
cd Metatheory
lake build
```

Optional strict check (placeholders + axioms/constants):

```bash
powershell -ExecutionPolicy Bypass -File scripts/check.ps1
```

## No Sorries / Axioms

All modules must remain `sorry`-free and axiom-free, including new extensions.


### Using as a Dependency

Add to your `lakefile.toml`:

```toml
[[require]]
name = "Metatheory"
git = "https://github.com/Arthur742Ramos/Metatheory.git"
rev = "main"
```

## Quick Start

### Import the Library

```lean
import Metatheory
```

### Lambda Calculus Example

```lean
import Metatheory.Lambda.Term
import Metatheory.Lambda.Confluence

open Metatheory.Lambda
open Term

-- Define terms using de Bruijn indices
-- λx. λy. x y  is  lam (lam (app (var 1) (var 0)))
def example1 : Term := ƛ (ƛ (var 1 @ var 0))

-- The identity combinator: λx. x
def I : Term := ƛ (var 0)

-- Use the Church-Rosser theorem
example {M N₁ N₂ : Term} (h1 : M →* N₁) (h2 : M →* N₂) :
    ∃ P, (N₁ →* P) ∧ (N₂ →* P) :=
  confluence h1 h2
```

### Generic Rewriting Framework

```lean
import Metatheory.Rewriting.Basic
import Metatheory.Rewriting.Diamond

open Rewriting

-- Use the generic framework for any relation
example {α : Type} {r : α → α → Prop} (h : Diamond r) : Confluent r :=
  confluent_of_diamond h
```

### First-Order TRS (Completion + Orderings)

```lean
import Metatheory.TRS.FirstOrder.Ordering
import Metatheory.TRS.FirstOrder.Confluence

open Metatheory.TRS.FirstOrder

-- LPO-based termination criterion
example {sig : Signature} {rules : RuleSet sig} (prec : Precedence sig)
    (hord : ∀ r, rules r → StableLPOplus prec r.rhs r.lhs) :
    Terminating rules :=
  terminating_of_lpo (sig := sig) (prec := prec) hord
```

### Simply Typed Lambda Calculus

```lean
import Metatheory.STLC.Typing
import Metatheory.STLC.Normalization

open Metatheory.STLC

-- Well-typed terms are strongly normalizing
example {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) : SN M :=
  strong_normalization h
```

### Extended STLC with Products, Sums, and Unit

```lean
import Metatheory.STLCext.Typing
import Metatheory.STLCext.Normalization

open Metatheory.STLCext

-- Progress: well-typed closed terms are values or can step
example {M : Term} {A : Ty} (h : HasType [] M A) : IsValue M ∨ ∃ N, M ⟶ N :=
  progress h

-- Strong normalization for extended STLC
example {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) : SN M :=
  strong_normalization h
```

### STLC with Booleans (CBV Determinism)

```lean
import Metatheory.STLCextBool.CBV

open Metatheory.STLCextBool

example {M N₁ N₂ : Term} (h1 : CBVStep M N₁) (h2 : CBVStep M N₂) : N₁ = N₂ :=
  CBVStep.deterministic h1 h2
```

### System F (Polymorphic Lambda Calculus)

```lean
import Metatheory.SystemF.Typing
import Metatheory.SystemF.SubjectReduction

open Metatheory.SystemF

-- System F types use de Bruijn indices for type variables
-- ∀α. α → α  is  Ty.all (Ty.tvar 0 ⇒ Ty.tvar 0)

-- Subject reduction: types preserved under reduction
example {Γ : Context} {M N : Term} {τ : Ty}
    (hM : Γ ⊢ M : τ) (hstep : M.Step N) : Γ ⊢ N : τ :=
  subject_reduction hM hstep

-- Progress for closed terms
example {M : Term} {τ : Ty} (h : ⊢ M : τ) : M.IsValue ∨ ∃ N, M.Step N :=
  progress h
```

## Extended Formalizations (Standalone Modules)

In addition to the layered core directories (`Rewriting/`, `Lambda/`, `CL/`, `TRS/`, `StringRewriting/`, `STLC/`, `STLCext/`, `STLCextBool/`, `SystemF/`), the project includes **78 standalone modules** at `Metatheory/*.lean`.

### Type systems and typing disciplines

- `AbstractionSafety.lean` — Safety-oriented typing relation with abstraction-preservation lemmas.
- `AffineTypes.lean` — Affine ownership typing inspired by Rust-style single-use resources.
- `Bidirectional.lean` — Bidirectional typing (synthesis/checking) for concise typing derivations.
- `ContractTypes.lean` — Contract-annotated typing with interface-level guarantees.
- `DependentPattern.lean` — Dependently typed pattern matching and indexed elimination structure.
- `EffectSystems.lean` — Type-and-effect judgments with explicit effect labels.
- `Gradual.lean` — Gradual typing with dynamic type and consistency relations.
- `GradedTypeTheory.lean` — Graded modality/type usage tracking (0/1/ω-style discipline).
- `InformationFlow.lean` — Security typing over a lattice of confidentiality levels.
- `Intersection.lean` — Intersection type operators and associated metatheoretic lemmas.
- `LinearTypes.lean` — Linear usage-sensitive typing and structural control.
- `PolymorphismVariants.lean` — Comparative formalization of polymorphism design variants.
- `QuantitativeTypes.lean` — Quantitative type usage accounting for resource-aware typing.
- `RecursiveTypes.lean` — Recursive type constructors with unfold/fold metatheory.
- `Refinement.lean` — Refinement-annotated base types with predicate-indexed judgments.
- `RefinementTypes.lean` — Predicate subtyping and refinement typing rules.
- `RowPoly.lean` — Row polymorphism for extensible typing contexts/signatures.
- `SecrecyTypes.lean` — Secrecy/security labels integrated into typing judgments.
- `SessionTypes.lean` — Binary session type protocols for typed communication.
- `SizedTypes.lean` — Size indices for termination/productivity-aware typing.
- `TemporalTypes.lean` — Temporal type structure over trace-indexed behavior.
- `TypeClasses.lean` — Type-class declarations and resolution-oriented typing scaffolding.
- `TypeInference.lean` — Constraint-based type inference for monomorphic fragments.
- `TypeInhabitance.lean` — Constructive inhabitation results (type-to-term witness style).
- `TypePreservation.lean` — Standalone substitution and preservation theorems.
- `UniversePolymorphism.lean` — Universe-level expressions and polymorphic universe handling.

### Semantics, normalization, and equivalence

- `AbstractInterpretation.lean` — Abstract interpretation skeletons with soundness-oriented structure.
- `AbstractMachines.lean` — CEK/Krivine/SECD-style machine encodings and transitions.
- `CallByPushValue.lean` — Call-by-push-value syntax, translation, and metatheory lemmas.
- `CategorySemantics.lean` — Categorical semantics building blocks for typed languages.
- `Coinduction.lean` — Coinductive streams/processes and bisimulation-style reasoning.
- `DomainTheory.lean` — Domain/path-style order-theoretic lemmas for denotational settings.
- `Erasure.lean` — Erasure translation preserving key typing/evaluation structure.
- `GameSemantics.lean` — Game-semantic traces/plays with compositional properties.
- `LogicalRelations.lean` — Logical-relations framework for normalization/equivalence proofs.
- `ModalTypeTheory.lean` — Modal type-theoretic syntax and proof obligations.
- `NormByEval.lean` — Normalization by evaluation (NbE) core constructions.
- `Normalization.lean` — Generic normalization-oriented lemmas and structures.
- `ObservationalEquality.lean` — Observational/contextual equality formulations.
- `ParallelReduction.lean` — Parallel reduction relation and confluence-support infrastructure.
- `Parametricity.lean` — Relational parametricity setup for polymorphic calculi.
- `ProgramEquivalence.lean` — Program equivalence relations and congruence toolkit.
- `Realizability.lean` — Realizability semantics over combinatory-style structures.
- `Termination.lean` — Well-founded termination analysis and accessibility lemmas.

### Compilation and transformation pipeline

- `ANFRegAlloc.lean` — ANF conversion plus register-allocation metatheory.
- `CPS.lean` — CPS-focused typed syntax and proof support.
- `CPSTransformation.lean` — Source-to-CPS transformation and simulation lemmas.
- `CompilerOptimizations.lean` — Verified optimization rewrites for a small compiler core.
- `ElaborationAlgorithm.lean` — Surface-to-core elaboration algorithm components.
- `StackMachineCompilation.lean` — Compilation to stack machine code with correctness statements.
- `StackMachines.lean` — Stack machine semantics and execution lemmas.
- `SyntaxTransformers.lean` — Generic syntax transformer combinators and properties.

### Effects, concurrency, and resource management

- `AlgebraicEffects.lean` — Algebraic effects with handlers and effect-row-style structure.
- `EffectHandlers.lean` — Typed handler interfaces and operational effect handling.
- `ConcurrencyTypes.lean` — Typing-oriented concurrency process/rewrite structure.
- `MemoryManagement.lean` — Memory-aware terms/types and management invariants.
- `SessionProc.lean` — Session-typed process calculus fragments and safety scaffolding.

### Logic, proof theory, and structural systems

- `Focusing.lean` — Focused proof search structure with polarized connectives.
- `LinearLogic.lean` — Linear logic formulae and proof-theoretic infrastructure.
- `ModalLogic.lean` — Modal proof system lemmas and formula structure.
- `OTT.lean` — OTT-style syntax/typing support definitions.
- `ProofIrrelevance.lean` — Proof irrelevance principles and consequences.
- `ProofNets.lean` — Proof-net representation for linear logic fragments.
- `ResourceLogic.lean` — Resource-sensitive logic connectives and judgments.
- `SeparationLogic.lean` — Separation logic structures and composition lemmas.
- `Sequent.lean` — Sequent calculus style rewriting/judgment relations.
- `Substructural.lean` — Substructural logic framework controlling structural rules.

### Macros, metaprogramming, and proof automation

- `HigherOrderUnification.lean` — Higher-order unification syntax and solving scaffolding.
- `HygienicMacros.lean` — Hygienic macro expansion and scope-safety metatheory.
- `InductionRecursion.lean` — Induction-recursion universes and code interpretations.
- `MacroSystems.lean` — Macro system core with scoped marks and expansion relations.
- `MacroTyping.lean` — Macro typing/staging rules for typed expansion.
- `TacticFrameworks.lean` — Lightweight tactic framework formalization hooks.

### Project scaffolding and integration modules

- `Basic.lean` — Minimal sandbox module used for local sanity checks.
- `Confluence.lean` — Standalone confluence/closure helper development.
- `DeBruijn.lean` — De Bruijn-indexed substitution/renaming infrastructure.
- `Metrics.lean` — Project metrics and theorem inventory checks.
- `MetatheoryGrandTour.lean` — Grand tour module connecting major components.

## Key Theorems

### Generic Rewriting Framework

| Theorem | Statement | File |
|---------|-----------|------|
| `confluent_of_diamond` | Diamond r → Confluent r | `Rewriting/Diamond.lean` |
| `confluent_of_terminating_localConfluent` | Terminating r → LocalConfluent r → Confluent r | `Rewriting/Newman.lean` |
| `confluent_union` | Confluent r → Confluent s → Commute r s → Confluent (Union r s) | `Rewriting/HindleyRosen.lean` |
| `confluent_of_locallyDecreasing` | WellFounded lt → LocallyDecreasing r lt → Confluent (LabeledUnion r) | `Rewriting/DecreasingDiagrams.lean` |
| `church_rosser_of_locallyDecreasing` | WellFounded lt → LocallyDecreasing r lt → Metatheory (LabeledUnion r) | `Rewriting/DecreasingDiagrams.lean` |
| `hasNormalForm_of_terminating` | Terminating r → ∀ a, HasNormalForm r a | `Rewriting/Basic.lean` |

| `existsUnique_normalForm_of_terminating_confluent` | Terminating r → Confluent r → ∀ a, ∃ n, a →* n ∧ NF n ∧ (∀ n', ...) | `Rewriting/Basic.lean` |

### Lambda Calculus

| Theorem | Statement | File |
|---------|-----------|------|
| `confluence` | M →* N₁ → M →* N₂ → ∃ P, N₁ →* P ∧ N₂ →* P | `Lambda/Confluence.lean` |
| `parRed_diamond` | Diamond ParRed | `Lambda/Diamond.lean` |
| `parRed_complete` | M ⇒ N → N ⇒ complete M | `Lambda/Complete.lean` |
| `beta_eta_confluent` | Confluent BetaEtaStep | `Lambda/Eta.lean` |
| `beta_eta_diamond` | β a b → η a c → ∃ d, η* b d ∧ β* c d | `Lambda/Eta.lean` |
| `eta_confluent` | Confluent EtaStep | `Lambda/Eta.lean` |
| `CBVStep.deterministic` | M →cbv N₁ → M →cbv N₂ → N₁ = N₂ | `Lambda/CBV.lean` |
| `progress_trichotomy` | IsValue M ∨ (∃ N, M →cbv N) ∨ IsStuck M | `Lambda/CBV.lean` |

### Combinatory Logic

| Theorem | Statement | File |
|---------|-----------|------|
| `confluent` | Confluent WeakStep | `CL/Confluence.lean` |
| `I_identity` | (I ⬝ x) →* x | `CL/Reduction.lean` |
| `K_identity` | (K ⬝ x ⬝ y) →* x | `CL/Reduction.lean` |
| `S_identity` | (S ⬝ x ⬝ y ⬝ z) →* ((x ⬝ z) ⬝ (y ⬝ z)) | `CL/Reduction.lean` |
| `B_identity` | (B ⬝ f ⬝ g ⬝ x) →* (f ⬝ (g ⬝ x)) | `CL/Reduction.lean` |
| `C_identity` | (C ⬝ x ⬝ y ⬝ z) →* ((x ⬝ z) ⬝ y) | `CL/Reduction.lean` |
| `W_identity` | (W ⬝ x ⬝ y) →* ((x ⬝ y) ⬝ y) | `CL/Reduction.lean` |

### Simply Typed Lambda Calculus

| Theorem | Statement | File |
|---------|-----------|------|
| `subject_reduction` | HasType Γ M A → BetaStep M N → HasType Γ N A | `STLC/Typing.lean` |
| `strong_normalization` | HasType Γ M A → SN M | `STLC/Normalization.lean` |

### Extended STLC (Products and Sums)

| Theorem | Statement | File |
|---------|-----------|------|
| `subject_reduction` | HasType Γ M A → M ⟶ N → HasType Γ N A | `STLCext/Typing.lean` |
| `progress` | HasType [] M A → IsValue M ∨ ∃ N, M ⟶ N | `STLCext/Typing.lean` |
| `strong_normalization` | HasType Γ M A → SN M | `STLCext/Normalization.lean` |

### STLC with Booleans

| Theorem | Statement | File |
|---------|-----------|------|
| `subject_reduction` | HasType Γ M A → M ⟶ N → HasType Γ N A | `STLCextBool/Typing.lean` |
| `progress` | [] ⊢ M : A → IsValue M ∨ ∃ N, M ⟶ N | `STLCextBool/Typing.lean` |
| `confluence` | M ⟶* N₁ → M ⟶* N₂ → ∃ P, N₁ ⟶* P ∧ N₂ ⟶* P | `STLCextBool/Confluence.lean` |
| `cbv_deterministic` | Deterministic CBVStep | `STLCextBool/CBV.lean` |
| `cbv_confluent` | Confluent CBVStep | `STLCextBool/CBV.lean` |
| `strong_normalization` | HasType Γ M A → SN (erase M) | `STLCextBool/Normalization.lean` |

### TRS Proof Comparison

| Theorem | Statement | File |
|---------|-----------|------|
| `confluence_via_diamond` | Confluent TinyStep | `TRS/DiamondComparison.lean` |
| `confluence_via_newman` | Confluent TinyStep | `TRS/DiamondComparison.lean` |

### First-Order TRS (Completion + Orderings)

| Theorem | Statement | File |
|---------|-----------|------|
| `terminating_of_kbo` | Weight ordering orients all rules → Terminating | `TRS/FirstOrder/Ordering.lean` |
| `terminating_of_lpo` | Stable LPO orients all rules → Terminating | `TRS/FirstOrder/Ordering.lean` |
| `confluent_of_knuthBendixComplete` | KB certificate → Confluent | `TRS/FirstOrder/Confluence.lean` |

### System F (Polymorphic Lambda Calculus)


| Theorem | Statement | File |
|---------|-----------|------|
| `subject_reduction` | (Γ ⊢ M : τ) → M.Step N → (Γ ⊢ N : τ) | `SystemF/SubjectReduction.lean` |
| `substitution_typing` | (A :: Γ ⊢ M : B) → (Γ ⊢ N : A) → (Γ ⊢ M[N] : B) | `SystemF/SubjectReduction.lean` |
| `type_substitution_typing` | (shiftContext Γ ⊢ M : τ) → WF k σ → (Γ ⊢ M[σ] : τ[σ]) | `SystemF/SubjectReduction.lean` |
| `progress` | (⊢ M : τ) → IsValue M ∨ ∃ N, M.Step N | `SystemF/Typing.lean` |
| `confluence` | M →ₛ* N₁ → M →ₛ* N₂ → ∃ P, N₁ →ₛ* P ∧ N₂ →ₛ* P | `SystemF/Confluence.lean` |
| `parRed_diamond` | Diamond ParRed | `SystemF/Diamond.lean` |
| `strongStep_confluent` | Confluent StrongStep | `SystemF/Confluence.lean` |
| `strong_normalization` | (Γ ⊢ M : τ) → SN M | `SystemF/StrongNormalization.lean` |

## Project Structure

```
Metatheory/
├── Metatheory.lean              # Main entry point
├── Metrics.lean                 # Project statistics and theorem summary
├── *.lean (78 standalone modules) # Extended formalizations; see section above
│
├── Rewriting/                   # Layer 0: Generic ARS Framework
│   ├── Basic.lean               # Star, Plus, Joinable, Diamond, Confluent
│   ├── Diamond.lean             # Diamond property → Confluence
│   ├── Newman.lean              # Newman's lemma
│   ├── HindleyRosen.lean        # Union of commuting confluent relations
│   ├── DecreasingDiagrams.lean  # van Oostrom's decreasing diagrams
│   ├── DecreasingDiagramsExample.lean # Non-terminating decreasing diagrams example
│   ├── DecreasingDiagramsFamily.lean  # Parameterized non-terminating family
│   └── Compat.lean              # Mathlib-style compatibility
│
├── Lambda/                      # Layer 1a: Untyped Lambda Calculus
│   ├── Term.lean                # De Bruijn terms, shift, substitution
│   ├── Beta.lean                # β-reduction relation
│   ├── MultiStep.lean           # Multi-step reduction (→*)
│   ├── Parallel.lean            # Parallel reduction (⇒)
│   ├── Complete.lean            # Complete development
│   ├── Diamond.lean             # Diamond property for ⇒
│   ├── Confluence.lean          # Church-Rosser theorem
│   ├── Eta.lean                 # η-reduction and βη-confluence
│   ├── Generic.lean             # Bridge to generic framework
│   └── CBV.lean                 # Call-by-value reduction
│
├── CL/                          # Layer 1b: Combinatory Logic
│   ├── Syntax.lean              # S, K, I, B, C, W combinators
│   ├── Reduction.lean           # Weak reduction + combinator identities
│   ├── Parallel.lean            # Parallel reduction
│   └── Confluence.lean          # Church-Rosser for CL
│
├── TRS/                         # Layer 2a: Simple Term Rewriting
│   ├── Syntax.lean              # Expressions (0, 1, +, *)
│   ├── Rules.lean               # Rewrite rules
│   ├── Confluence.lean          # Confluence via Newman
│   └── DiamondComparison.lean   # Diamond vs Newman comparison
│   └── FirstOrder/              # First-order TRS, completion, KBO/LPO

│
├── StringRewriting/             # Layer 2b: String Rewriting
│   ├── Syntax.lean              # Alphabet and strings
│   ├── Rules.lean               # aa→a, bb→b rules
│   └── Confluence.lean          # Confluence via Newman + critical pairs
│
├── STLC/                        # Layer 3: Simply Typed Lambda Calculus
│   ├── Types.lean               # Ty ::= base n | A → B
│   ├── Terms.lean               # Re-exports Lambda.Term
│   ├── Typing.lean              # Γ ⊢ M : A, subject reduction
│   └── Normalization.lean       # Strong normalization (Tait's method)
│
├── STLCext/                     # Layer 4: Extended STLC with Products, Sums, Unit
│   ├── Types.lean               # Ty ::= base n | A → B | A × B | A + B | unit
│   ├── Terms.lean               # De Bruijn terms: pair, fst, snd, inl, inr, case, unit
│   ├── Reduction.lean           # Beta + product/sum reduction rules
│   ├── Typing.lean              # Typing, subject reduction, progress
│   └── Normalization.lean       # Strong normalization (logical relations)
│
├── STLCextBool/                 # Layer 4b: STLC with booleans and conditionals
│   ├── Types.lean               # Ty ::= base n | A → B | bool
│   ├── Terms.lean               # De Bruijn terms with true/false/ite
│   ├── Reduction.lean           # Beta + if-true/if-false reduction rules
│   ├── CBV.lean                 # Call-by-value reduction (deterministic)
│   ├── Parallel.lean            # Parallel reduction (diamond property tool)
│   ├── Complete.lean            # Complete development for parallel reduction
│   ├── Confluence.lean          # Church-Rosser theorem
│   ├── Typing.lean              # Typing, subject reduction, progress
│   └── Normalization.lean       # Strong normalization via erasure
│
└── SystemF/                     # Layer 5: System F (Polymorphic Lambda Calculus)

    ├── Types.lean               # Ty ::= tvar n | τ → σ | ∀α.τ (de Bruijn)
    ├── Terms.lean               # Terms with type abstraction/application
    ├── Typing.lean              # Polymorphic typing, progress
    ├── SubjectReduction.lean    # Type preservation under reduction
    ├── StrongReduction.lean     # Full (strong) β-reduction relation
    ├── Parallel.lean            # Parallel reduction for System F
    ├── Complete.lean            # Complete development
    ├── Diamond.lean             # Diamond property for parallel reduction
    ├── Confluence.lean          # Church-Rosser theorem for System F
    └── StrongNormalization.lean # Strong normalization (Girard/Tait method)
```

## Proof Techniques

### 1. Diamond Property (Takahashi's Method)

Used for: **Lambda Calculus**, **Combinatory Logic**, **Tiny TRS (comparison)**

The key insight is that single-step reduction doesn't have the diamond property, but *parallel reduction* does:

```
      M
     / \
    ⇒   ⇒        Parallel reduction: contract any subset of redexes
   /     \
  N₁     N₂
   \     /
    ⇒   ⇒
     \ /
      P           P = complete(M) contracts ALL redexes
```

**Key definitions:**
- `ParRed M N`: M parallel-reduces to N (any subset of redexes)
- `complete M`: Contracts all redexes simultaneously
- `parRed_complete`: Any parallel reduction reaches the complete development

### 2. Hindley-Rosen Lemma

Used for: **βη-Confluence**

When two confluent relations commute, their union is confluent:

```
Confluent β + Confluent η + Commute(β, η) → Confluent (β ∪ η)
```

**Key lemmas for βη:**
- `beta_eta_diamond`: β and η single-step divergences can be joined
- `eta_beta_seq_swap`: Sequential η;β can be reordered to β*;η*
- `commute_beta_eta_stars`: Star relations β* and η* commute
- `betaeta_decompose`: Any βη* path decomposes into β* followed by η*

### 3. Newman's Lemma

Used for: **TRS**, **String Rewriting**, **η-reduction**, **Tiny TRS (comparison)**

For *terminating* systems, local confluence implies global confluence:

```
Terminating + LocalConfluent → Confluent
```

**Strategy:**
1. Prove termination via a well-founded measure (size, length)
2. Prove local confluence (one-step divergences join)
3. Apply Newman's lemma

### 4. Logical Relations (Tait's Method)

Used for: **Strong Normalization of STLC**

Define a "reducibility" predicate by induction on types:

```lean
def Reducible : Ty → Term → Prop
  | base _, M => SN M
  | A → B, M => ∀ N, Reducible A N → Reducible B (M @ N)
```

**Key properties (CR1-CR3):**
- CR1: Reducible terms are SN
- CR2: Reducibility is closed under reduction
- CR3: Neutral terms with reducible reducts are reducible

**Fundamental Lemma:** Well-typed terms are reducible under reducible substitutions.

## Mathematical Background

### De Bruijn Indices

Variables are represented by natural numbers indicating the number of binders between the variable and its binding λ:

```
λx. λy. x y    →    λ. λ. (var 1) (var 0)
    │   │ │              │        │
    │   │ └──────────────┼────────┘ bound by inner λ
    │   └────────────────┘          bound by outer λ
    └─ binds x
```

**Advantages:**
- No α-equivalence needed (terms equal up to renaming are identical)
- Substitution is capture-avoiding by construction

### Reflexive-Transitive Closure

```lean
inductive Star (r : α → α → Prop) : α → α → Prop where
  | refl : Star r a a
  | tail : Star r a b → r b c → Star r a c
```

### Confluence

```
      a
     / \
    *   *
   /     \
  b       c
   \     /
    *   *
     \ /
      d
```

A relation r is **confluent** if whenever a →* b and a →* c, there exists d with b →* d and c →* d.

## API Reference

### Core Definitions

```lean
-- Reflexive-transitive closure
inductive Star (r : α → α → Prop) : α → α → Prop

-- Joinability
def Joinable (r : α → α → Prop) (a b : α) : Prop :=
  ∃ c, Star r a c ∧ Star r b c

-- Diamond property
def Diamond (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → ∃ d, r b d ∧ r c d

-- Confluence
def Confluent (r : α → α → Prop) : Prop :=
  ∀ a b c, Star r a b → Star r a c → Joinable r b c

-- Termination (well-foundedness)
def Terminating (r : α → α → Prop) : Prop :=
  ∀ a, Acc (fun x y => r y x) a
```

### Lambda Calculus

```lean
-- Terms
inductive Term : Type where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term

-- Shifting (adjusts free variables)
def shift (d : Int) (c : Nat) : Term → Term

-- Substitution
def subst (j : Nat) (N : Term) : Term → Term

-- Notation: M[N] = subst 0 N M
notation M "[" N "]" => subst0 N M

-- β-reduction
inductive BetaStep : Term → Term → Prop where
  | beta : BetaStep (app (lam M) N) (M[N])
  | appL : BetaStep M M' → BetaStep (app M N) (app M' N)
  | appR : BetaStep N N' → BetaStep (app M N) (app M N')
  | lam  : BetaStep M M' → BetaStep (lam M) (lam M')

-- Call-by-value reduction (CBV)
def IsValue : Term → Prop
  | lam _ => True
  | _ => False

inductive CBVStep : Term → Term → Prop where
  | beta : IsValue V → CBVStep (app (lam M) V) (M[V])
  | appL : CBVStep M M' → CBVStep (app M N) (app M' N)
  | appR : IsValue V → CBVStep N N' → CBVStep (app V N) (app V N')
```

### Combinatory Logic

```lean
-- Terms: S, K combinators and application
inductive Term : Type where
  | S : Term
  | K : Term
  | app : Term → Term → Term

-- Derived combinators
def I : Term := S ⬝ K ⬝ K           -- Identity: I x →* x
def B : Term := S ⬝ (K ⬝ S) ⬝ K     -- Composition: B f g x →* f (g x)
def C : Term := S ⬝ (S ⬝ (K ⬝ B) ⬝ S) ⬝ (K ⬝ K)  -- Flip: C x y z →* x z y
def W : Term := S ⬝ S ⬝ (S ⬝ K)     -- Duplicate: W x y →* x y y

-- Weak reduction
inductive WeakStep : Term → Term → Prop where
  | k_red : WeakStep (K ⬝ M ⬝ N) M
  | s_red : WeakStep (S ⬝ M ⬝ N ⬝ P) ((M ⬝ P) ⬝ (N ⬝ P))
  | appL  : WeakStep M M' → WeakStep (M ⬝ N) (M' ⬝ N)
  | appR  : WeakStep N N' → WeakStep (M ⬝ N) (M ⬝ N')
```

### STLC

```lean
-- Simple types
inductive Ty : Type where
  | base : Nat → Ty
  | arr : Ty → Ty → Ty

-- Typing judgment
inductive HasType : Context → Term → Ty → Prop where
  | var : Γ.get? n = some A → HasType Γ (var n) A
  | lam : HasType (A :: Γ) M B → HasType Γ (lam M) (A → B)
  | app : HasType Γ M (A → B) → HasType Γ N A → HasType Γ (app M N) B

-- Strong normalization
def SN (M : Term) : Prop := Acc (fun a b => BetaStep b a) M
```

### Extended STLC

```lean
-- Types with products, sums, and unit
inductive Ty where
  | base : Nat → Ty           -- Base type
  | arr  : Ty → Ty → Ty       -- A → B
  | prod : Ty → Ty → Ty       -- A × B
  | sum  : Ty → Ty → Ty       -- A + B
  | unit : Ty                 -- Unit type

-- Terms with pairs, projections, injections, case, and unit
inductive Term where
  | var  : Nat → Term                    -- Variable
  | lam  : Term → Term                   -- λ.M
  | app  : Term → Term → Term            -- M N
  | pair : Term → Term → Term            -- (M, N)
  | fst  : Term → Term                   -- π₁ M
  | snd  : Term → Term                   -- π₂ M
  | inl  : Term → Term                   -- inl M
  | inr  : Term → Term                   -- inr M
  | case : Term → Term → Term → Term     -- case M of inl → N₁ | inr → N₂
  | unit : Term                          -- Unit value ()

-- Values
inductive IsValue : Term → Prop where
  | lam  : IsValue (lam M)
  | pair : IsValue M → IsValue N → IsValue (pair M N)
  | inl  : IsValue M → IsValue (inl M)
  | inr  : IsValue M → IsValue (inr M)
  | unit : IsValue unit
```

## References

### Papers

1. **Takahashi, M.** (1995). "Parallel Reductions in λ-Calculus". *Information and Computation*, 118(1), 120-127.
   - The parallel reduction technique for Church-Rosser

2. **Newman, M.H.A.** (1942). "On Theories with a Combinatorial Definition of 'Equivalence'". *Annals of Mathematics*, 43(2), 223-243.
   - Newman's lemma: termination + local confluence → confluence

3. **van Oostrom, V.** (1994). "Confluence for Abstract and Higher-Order Rewriting". PhD thesis, Vrije Universiteit Amsterdam.
   - Decreasing diagrams technique

4. **Tait, W.W.** (1967). "Intensional Interpretations of Functionals of Finite Type I". *Journal of Symbolic Logic*, 32(2), 198-212.
   - Logical relations method for strong normalization

5. **Hindley, J.R.** (1969). "An Abstract Church-Rosser Theorem". *Journal of Symbolic Logic*, 34(4), 545-560.
   - Hindley-Rosen lemma for union of relations

### Books

1. **Barendregt, H.P.** (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.
   - Comprehensive reference for lambda calculus

2. **Terese** (2003). *Term Rewriting Systems*. Cambridge University Press.
   - Standard reference for term rewriting theory

3. **Girard, J.-Y., Lafont, Y., & Taylor, P.** (1989). *Proofs and Types*. Cambridge University Press.
   - Logical relations and normalization proofs

4. **Pierce, B.C., et al.** (2023). *Software Foundations*, Volume 2: Programming Language Foundations.
   - Formal verification of PL metatheory in Coq

### Related Formalizations

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) (Coq)
- [CoLoR](https://github.com/fblanqui/color) - Certified termination and confluence (Coq)
- [Nominal Isabelle](https://isabelle.in.tum.de/nominal/) - Lambda calculus with names
- [PLFA](https://plfa.github.io/) - Programming Language Foundations in Agda

## Contributing

Contributions are welcome! Please feel free to submit issues and pull requests.

### Development Guidelines

1. **No `sorry`**: All theorems must be fully proven (current count: **0 sorries**)
2. **Documentation**: Add docstrings to public definitions
3. **References**: Cite sources for non-trivial lemmas
4. **Style**: Follow existing code conventions

### Running Tests

```bash
lake build  # Compiles and type-checks all proofs
```

## License

MIT License - see [LICENSE](LICENSE) for details.

## Acknowledgments

This project was developed with assistance from [Claude Code](https://claude.ai/), Anthropic's AI assistant for software engineering.
