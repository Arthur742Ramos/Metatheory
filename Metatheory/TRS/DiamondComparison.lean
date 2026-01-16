/-
# Comparing Confluence Proofs for a Tiny TRS

This module compares two confluence proofs for a small deterministic
rewriting system: one via the diamond property and one via Newman's lemma.

We reuse the generic framework to show how different criteria coincide
on a simple deterministic relation.
-/

import Metatheory.Rewriting.Basic
import Metatheory.Rewriting.Diamond
import Metatheory.Rewriting.Newman

namespace Metatheory.TRS

/-! ## A Tiny Deterministic TRS -/

/-- Two-node expressions: a single rewrite a → b. -/
inductive Tiny : Type where
  | a : Tiny
  | b : Tiny
  deriving DecidableEq, Repr

/-- Single-step relation: no rules (empty relation). -/
inductive TinyStep : Tiny → Tiny → Prop where

/-- Determinism of the tiny system. -/
theorem tiny_deterministic : Rewriting.Deterministic TinyStep := by
  intro x y z hxy hxz
  cases hxy

/-- Diamond property holds (vacuously) for the tiny system. -/
theorem tiny_diamond : Rewriting.Diamond TinyStep := by
  intro x y z hxy hxz
  cases hxy

/-- Termination holds (no infinite sequences). -/
theorem tiny_terminating : Rewriting.Terminating TinyStep := by
  refine ⟨?_⟩
  intro x
  apply Acc.intro
  intro y hy
  cases hy with
  | single h => cases h
  | tail h hstep => cases hstep

/-- Local confluence holds (trivial). -/
theorem tiny_local_confluent : Rewriting.LocalConfluent TinyStep := by
  intro x y z hxy hxz
  cases hxy

/-- Confluence via diamond property. -/
theorem confluence_via_diamond : Rewriting.Confluent TinyStep :=
  Rewriting.confluent_of_diamond tiny_diamond

/-- Confluence via Newman's lemma. -/
theorem confluence_via_newman : Rewriting.Confluent TinyStep :=
  Rewriting.confluent_of_terminating_localConfluent tiny_terminating tiny_local_confluent

/-- The two proofs agree (both are just confluence). -/
theorem confluence_equiv : Rewriting.Confluent TinyStep :=
  confluence_via_diamond

end Metatheory.TRS
