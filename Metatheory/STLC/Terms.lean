/-
# Simply Typed Lambda Calculus - Terms

This module re-exports the untyped lambda calculus terms for use in STLC.
The term syntax is identical; typing is layered on top.

## References

- Pierce, "Types and Programming Languages" (2002)
-/

import Metatheory.Lambda.Term
import Metatheory.Lambda.Beta
import Metatheory.Lambda.MultiStep
import Metatheory.STLC.Types

namespace Metatheory.STLC

/-! ## Term Re-exports -/

/-- STLC uses the same term syntax as untyped lambda calculus -/
abbrev Term := Lambda.Term

open Lambda.Term

/-! ## Basic Constructors -/

/-- Variable term -/
abbrev var := Lambda.Term.var

/-- Application term -/
abbrev app := Lambda.Term.app

/-- Lambda abstraction (untyped at term level) -/
abbrev lam := Lambda.Term.lam

/-! ## Reduction -/

/-- Single-step beta reduction (from untyped) -/
abbrev BetaStep := Lambda.BetaStep

/-- Multi-step reduction -/
abbrev MultiStep := Lambda.MultiStep

/-- Notation for single-step reduction -/
scoped infix:50 " → " => BetaStep

/-- Notation for multi-step reduction -/
scoped infix:50 " →* " => MultiStep

/-! ## Substitution -/

/-- Substitution (from untyped) -/
abbrev subst := Lambda.Term.subst

/-- Shifting (from untyped) -/
abbrev shift := Lambda.Term.shift

end Metatheory.STLC
