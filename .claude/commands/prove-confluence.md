# Prove Confluence

Analyze a rewriting system and create a confluence proof using the appropriate technique.

## Arguments
- $ARGUMENTS: Description of the rewriting system or file path to analyze

## Instructions

1. **Analyze the system** to determine its properties:
   - Does it terminate? (size decreases, well-founded measure exists)
   - Does it have natural parallel reduction? (can contract multiple redexes at once)
   - Are there complex interactions between rules?

2. **Choose the proof technique**:

### Option A: Diamond Property Approach
**Use when**: Parallel reduction is natural and has the diamond property

Steps:
1. Define parallel reduction `ParRed` (contracts zero or more redexes)
2. Define complete development `complete` (contracts ALL redexes)
3. Prove `parRed_complete`: M ⇒ N → N ⇒ complete M
4. Prove `parRed_diamond`: Diamond ParRed
5. Bridge to single-step: Star Step ⊆ Star ParRed ⊆ Star Step
6. Apply `Rewriting.confluent_of_diamond`

Example systems: Lambda calculus, Combinatory Logic

### Option B: Newman's Lemma Approach
**Use when**: System terminates and local confluence is easier than diamond

Steps:
1. Define a termination measure (size, lexicographic order, etc.)
2. Prove `step_terminating`: Rewriting.Terminating Step
3. Prove `local_confluent` by critical pair analysis
4. Apply `Rewriting.confluent_of_terminating_localConfluent`

Example systems: Simple TRS, String rewriting

### Option C: Hindley-Rosen Lemma
**Use when**: System is union of simpler confluent systems that commute

Steps:
1. Split relation into r and s where Step = Union r s
2. Prove `Confluent r` and `Confluent s`
3. Prove `Commute r s`
4. Apply `Rewriting.confluent_union`

3. **Implement the proof** following patterns from existing case studies:
   - Lambda/ for diamond approach
   - TRS/ for Newman's lemma approach

4. **Verify**: Run `lake build` to ensure the proof compiles

## Critical Pair Analysis Guide

For Newman's lemma approach, identify all critical pairs:
1. List all reduction rules
2. For each pair of rules that can apply to overlapping positions:
   - Find the minimal overlapping term
   - Apply both rules to get e₁ and e₂
   - Show ∃ e', e₁ →* e' ∧ e₂ →* e'

## Output

Provide:
1. Analysis of which technique is appropriate
2. Complete Lean 4 proof code
3. Any auxiliary lemmas needed
