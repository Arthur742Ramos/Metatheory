# Claude Workflow for Metatheory

Repo-specific guidance for using Claude-style agent workflows in Metatheory: follow the project constraints (no sorry), reuse existing .claude/commands templates, and validate with lake build.

## Arguments
- $ARGUMENTS: Optional specific task or question about the workflow

## Instructions

Use this command when working on this repository with Claude (or Claude-like agents) and you want the canonical project rules and built-in task templates.

### Start Here

1. Read `CLAUDE.md` for project overview, structure, and the "no sorries" rule.
2. If the task matches a template, open the relevant file under `.claude/commands/` and follow it.

### Non-negotiables

- Do not introduce or keep `sorry`.
- Keep proofs fully constructive/complete; prefer auxiliary lemmas over brittle tactics.
- Run `lake build` after changes.

### Template Commands (Recommended)

The `.claude/commands/` directory contains reusable task playbooks:

| Command | Purpose |
|---------|---------|
| `/add-lemma` | Add a new lemma following project conventions |
| `/add-rewriting-system` | Add a new rewriting system case study |
| `/add-typed-system` | Add a new typed system |
| `/check-sorries` | Check for sorry placeholders in the codebase |
| `/create-parallel-reduction` | Create parallel reduction for confluence proofs |
| `/critical-pair-analysis` | Analyze critical pairs for local confluence |
| `/debruijn-helper` | Help with de Bruijn index operations |
| `/explain-theorem` | Explain a theorem in the codebase |
| `/prove-confluence` | Prove confluence for a rewriting system |
| `/strong-normalization` | Prove strong normalization |
| `/verify-build` | Verify the project builds successfully |

Use these as the default workflow when applicable.

### Validation

```bash
lake build
```

## Checklist
- [ ] Read CLAUDE.md for project context
- [ ] Identify applicable command template
- [ ] Follow template instructions
- [ ] Ensure no sorry in code
- [ ] Run lake build to validate
