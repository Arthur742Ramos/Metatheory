/-
# Critical Pair Theorem (First-Order TRSs)

This module states the critical pair theorem and the Knuth-Bendix
completion soundness criterion for first-order TRSs.
-/

import Metatheory.Rewriting.Newman
import Metatheory.TRS.FirstOrder.CriticalPairs
import Metatheory.TRS.FirstOrder.Rules
import Metatheory.TRS.FirstOrder.Unification

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Joinability and Confluence -/

/-- Joinability for a rule set. -/
abbrev Joinable {sig : Signature} (rules : RuleSet sig) :=
  Rewriting.Joinable (Step rules)

/-- Local confluence for a rule set. -/
abbrev LocalConfluent {sig : Signature} (rules : RuleSet sig) :=
  Rewriting.LocalConfluent (Step rules)

/-- Confluence for a rule set. -/
abbrev Confluent {sig : Signature} (rules : RuleSet sig) :=
  Rewriting.Confluent (Step rules)

/-! ## Critical Pair Criterion -/

/-- All critical pairs are joinable. -/
def CriticalPairsJoinable {sig : Signature} (rules : RuleSet sig) : Prop :=
  ∀ cp, CriticalPairs rules cp → Joinable rules cp.left cp.right

/-- Peak decomposition hypothesis for critical pairs.

    Every local peak is either immediately joinable in one step or
    corresponds to a critical pair (up to symmetry). This abstracts the
    standard overlap analysis used in critical pair theorems. -/
def CriticalPairsComplete {sig : Signature} (rules : RuleSet sig) : Prop :=
  ∀ s b c, Step rules s b → Step rules s c →
    (∃ d, Step rules b d ∧ Step rules c d) ∨
    ∃ cp p, CriticalPairs rules cp ∧
      ((replace s p cp.left = some b ∧ replace s p cp.right = some c) ∨
        (replace s p cp.left = some c ∧ replace s p cp.right = some b))

/-! ## Peak Decomposition -/

-- subterm_replace_same is not needed; use Term.replace_self directly where needed.

open Term

/-- Peak decomposition for first-order steps. -/
theorem criticalPairsComplete_of_steps {sig : Signature} {rules : RuleSet sig} :
    CriticalPairsComplete rules := by
  intro s b c hb hc
  have hb0 : Step rules s b := hb
  have hc0 : Step rules s c := hc
  rcases hb with ⟨r1, hr1, p1, sub1, hsub1, hrep1⟩
  rcases hc with ⟨r2, hr2, p2, sub2, hsub2, hrep2⟩
  by_cases hprefix12 : PosPrefix p1 p2
  ·
    rcases hprefix12 with ⟨q, hq⟩
    subst hq
    have hsub_q : subterm (Term.subst sub1 r1.lhs) q = some (Term.subst sub2 r2.lhs) := by
      have hsub_append := Term.subterm_append (t := s) (p := p1) (q := q)
        (u := Term.subst sub1 r1.lhs) hsub1
      have hsub2' : subterm s (p1 ++ q) = some (Term.subst sub2 r2.lhs) := hsub2
      simpa [hsub_append] using hsub2'
    have hnonvar : NonVar (Term.subst sub2 r2.lhs) := by
      cases r2.lhs <;> simp [NonVar, IsVar]
    have hover : Overlap r1 r2 q sub1 sub2 := by
      exact ⟨hsub_q, hnonvar⟩
    rcases Term.replace_append_inv (t := s) (u := Term.subst sub1 r1.lhs) (p := p1) (q := q)
        (v := Term.subst sub2 r2.rhs) hsub1 hrep2 with ⟨u', hrep_inner, hrep_outer⟩
    have hcp : CriticalPairs rules ⟨Term.subst sub1 r1.rhs, u'⟩ := by
      refine ⟨r1, r2, q, sub1, sub2, hr1, hr2, hover, ?_⟩
      simp [mkCriticalPair, hrep_inner]
    have hrep_left : replace s p1 (Term.subst sub1 r1.rhs) = some b := hrep1
    exact Or.inr ⟨_, p1, hcp, Or.inl ⟨hrep_left, hrep_outer⟩⟩
  ·
    by_cases hprefix21 : PosPrefix p2 p1
    ·
      rcases hprefix21 with ⟨q, hq⟩
      subst hq
      have hsub_q : subterm (Term.subst sub2 r2.lhs) q = some (Term.subst sub1 r1.lhs) := by
        have hsub_append := Term.subterm_append (t := s) (p := p2) (q := q)
          (u := Term.subst sub2 r2.lhs) hsub2
        have hsub1' : subterm s (p2 ++ q) = some (Term.subst sub1 r1.lhs) := hsub1
        simpa [hsub_append] using hsub1'
      have hnonvar : NonVar (Term.subst sub1 r1.lhs) := by
        cases r1.lhs <;> simp [NonVar, IsVar]
      have hover : Overlap r2 r1 q sub2 sub1 := by
        exact ⟨hsub_q, hnonvar⟩
      rcases Term.replace_append_inv (t := s) (u := Term.subst sub2 r2.lhs) (p := p2) (q := q)
        (v := Term.subst sub1 r1.rhs) hsub2 hrep1 with ⟨u', hrep_inner, hrep_outer⟩
      have hcp : CriticalPairs rules ⟨Term.subst sub2 r2.rhs, u'⟩ := by
        refine ⟨r2, r1, q, sub2, sub1, hr2, hr1, hover, ?_⟩
        simp [mkCriticalPair, hrep_inner]
      have hrep_left : replace s p2 (Term.subst sub2 r2.rhs) = some c := hrep2
      exact Or.inr ⟨_, p2, hcp, Or.inr ⟨hrep_left, hrep_outer⟩⟩
    ·
      -- Disjoint case: close the peak by commuting disjoint replacements.
      have hsub_b : Term.subterm b p2 = some (Term.subst sub2 r2.lhs) := by
        have hsub_b' : Term.subterm b p2 = Term.subterm s p2 :=
          Term.subterm_replace_of_disjoint (t := s) (u := Term.subst sub1 r1.rhs) (t' := b)
            (p := p1) (q := p2) hrep1 hprefix12 hprefix21
        simpa [hsub2] using hsub_b'
      have hsub_c : Term.subterm c p1 = some (Term.subst sub1 r1.lhs) := by
        have hsub_c' : Term.subterm c p1 = Term.subterm s p1 :=
          Term.subterm_replace_of_disjoint (t := s) (u := Term.subst sub2 r2.rhs) (t' := c)
            (p := p2) (q := p1) hrep2 hprefix21 hprefix12
        simpa [hsub1] using hsub_c'
      obtain ⟨d, hrep_bd, hrep_cd⟩ :=
        Term.replace_comm_of_disjoint (t := s) (p := p1) (q := p2)
          (u := Term.subst sub1 r1.rhs) (v := Term.subst sub2 r2.rhs)
          (t1 := b) (t2 := c) hrep1 hrep2 hprefix12 hprefix21
      have hbd : Step rules b d := by
        refine ⟨r2, hr2, p2, sub2, hsub_b, hrep_bd⟩
      have hcd : Step rules c d := by
        refine ⟨r1, hr1, p1, sub1, hsub_c, hrep_cd⟩
      exact Or.inl ⟨d, hbd, hcd⟩
/-- Critical pair theorem (soundness direction).

    If a TRS is locally confluent, then every critical pair is joinable. -/
theorem criticalPairsJoinable_of_localConfluent
    {sig : Signature} {rules : RuleSet sig} (hlocal : LocalConfluent rules) :
    CriticalPairsJoinable rules := by
  intro cp hcp
  rcases hcp with ⟨r1, r2, p, sub1, sub2, hr1, hr2, hover, hmk⟩
  have hsubterm : Term.subterm (Term.subst sub1 r1.lhs) p = some (Term.subst sub2 r2.lhs) := hover
  cases hreplace : Term.replace (Term.subst sub1 r1.lhs) p (Term.subst sub2 r2.rhs) with
    | none =>
      have : False := by
        simp [mkCriticalPair, hreplace] at hmk
        exact hmk
      cases this
  | some t' =>
      have hcp' : cp = ⟨Term.subst sub1 r1.rhs, t'⟩ := by
        simp [mkCriticalPair, hreplace] at hmk
        exact hmk.symm
      subst hcp'
      set s : Term sig := Term.subst sub1 r1.lhs
      have hleft : Step rules s (Term.subst sub1 r1.rhs) := by
        simpa [s] using step_of_rule r1 hr1 sub1
      have hright : Step rules s t' := by
        refine ⟨r2, hr2, p, sub2, ?_, ?_⟩
        · simpa [s] using hsubterm
        simpa [s] using hreplace
      exact hlocal s (Term.subst sub1 r1.rhs) t' hleft hright

private theorem step_context {sig : Signature} {rules : RuleSet sig}
    {t u v b c : Term sig} {p : Pos} :
    Step rules u v →
    Term.replace t p u = some b →
    Term.replace t p v = some c →
    Step rules b c := by
  intro hstep hrep_u hrep_v
  rcases hstep with ⟨r, hr, q, sub, hsub, hrep⟩
  refine ⟨r, hr, p ++ q, sub, ?_, ?_⟩
  ·
    have hsub_b : Term.subterm b p = some u := Term.subterm_replace hrep_u
    have hsub_b' := Term.subterm_append (t := b) (p := p) (q := q) (u := u) hsub_b
    simpa [hsub] using hsub_b'
  ·
    have hsub_b : Term.subterm b p = some u := Term.subterm_replace hrep_u
    have hrep_b : Term.replace b p v = some c :=
      Term.replace_override (t := t) (p := p) (u := u) (v := v)
        (t1 := b) (t2 := c) hrep_u hrep_v
    exact Term.replace_append (t := b) (u := u) (u' := v) (t' := c)
      (p := p) (q := q) (v := Term.subst sub r.rhs) hsub_b hrep hrep_b

private theorem star_context {sig : Signature} {rules : RuleSet sig}
    {t : Term sig} {p : Pos} {u v b0 c0 : Term sig} :
    Rewriting.Star (Step rules) u v →
    Term.replace t p u = some b0 →
    Term.replace t p v = some c0 →
    Rewriting.Star (Step rules) b0 c0 := by
  intro hstar hrep_u hrep_v
  induction hstar generalizing b0 c0 with
  | refl =>
      have hb : b0 = c0 := by
        have : (some b0 : Option (Term sig)) = some c0 := by
          simpa [hrep_u] using hrep_v
        exact Option.some.inj this
      subst hb
      exact Rewriting.Star.refl _
  | tail hstar hstep ih =>
      rename_i b c
      obtain ⟨b1, hrep_b1⟩ :=
        Term.replace_defined_of_replace (t := t) (p := p) (u := u) (t' := b0) hrep_u b
      have hstar_b0_b1 := ih hrep_u hrep_b1
      have hstep_b1 : Step rules b1 c0 :=
        step_context (rules := rules) (t := t) (p := p) (u := b) (v := c)
          (b := b1) (c := c0) hstep hrep_b1 hrep_v
      exact Rewriting.Star.tail hstar_b0_b1 hstep_b1

/-- Critical pair theorem (completeness direction). -/
theorem localConfluent_of_criticalPairsJoinable
    {sig : Signature} {rules : RuleSet sig}
    (hjoin : CriticalPairsJoinable rules) :
    LocalConfluent rules := by
  intro s b c hb hc
  have hcomplete := criticalPairsComplete_of_steps (rules := rules) s b c hb hc
  rcases hcomplete with ⟨d, hbd, hcd⟩ | ⟨cp, p, hcp, hcases⟩
  · exact ⟨d, Rewriting.Star.single hbd, Rewriting.Star.single hcd⟩
  ·
    have hjoin_cp := hjoin cp hcp
    rcases hjoin_cp with ⟨d, hleft, hright⟩
    rcases hcases with ⟨hrep_left, hrep_right⟩ | ⟨hrep_left, hrep_right⟩
    ·
      obtain ⟨d', hrep_d⟩ :=
        Term.replace_defined_of_replace (t := s) (p := p) (u := cp.left) (t' := b) hrep_left d
      have hleft' := star_context (rules := rules) (t := s) (p := p) hleft hrep_left hrep_d
      have hright' := star_context (rules := rules) (t := s) (p := p) hright hrep_right hrep_d
      exact ⟨d', hleft', hright'⟩
    ·
      obtain ⟨d', hrep_d⟩ :=
        Term.replace_defined_of_replace (t := s) (p := p) (u := cp.left) (t' := c) hrep_left d
      have hleft' := star_context (rules := rules) (t := s) (p := p) hleft hrep_left hrep_d
      have hright' := star_context (rules := rules) (t := s) (p := p) hright hrep_right hrep_d
      exact ⟨d', hright', hleft'⟩

/-- A TRS is terminating when its Step relation is terminating. -/
def Terminating {sig : Signature} (rules : RuleSet sig) : Prop :=
  Rewriting.Terminating (Step rules)

/-! ## Termination via Reduction Orderings -/

/-- A reduction ordering for first-order terms. -/
structure ReductionOrdering (sig : Signature) where
  lt : Term sig → Term sig → Prop
  wf : WellFounded lt
  trans : Transitive lt
  subst_closed : ∀ {sub : Subst sig} {s t : Term sig}, lt s t → lt (Term.subst sub s) (Term.subst sub t)
  replace_closed : ∀ {t : Term sig} {p : Pos} {u v t' t'' : Term sig},
    lt u v →
    Term.replace t p u = some t' →
    Term.replace t p v = some t'' →
    lt t' t''

/-! ## Size-Based Ordering -/

/-- Stable size ordering: size decreases under all substitutions. -/
def stableSizeLt {sig : Signature} (s t : Term sig) : Prop :=
  ∀ sub : Subst sig, Term.size (Term.subst sub s) < Term.size (Term.subst sub t)

theorem stableSizeLt_wf {sig : Signature} : WellFounded (stableSizeLt (sig := sig)) := by
  apply Subrelation.wf
  · intro a b h
    have h' := h Term.idSubst
    simpa [stableSizeLt, Term.subst_id] using h'
  · exact InvImage.wf Term.size Nat.lt_wfRel.wf

theorem stableSizeLt_trans {sig : Signature} : Transitive (stableSizeLt (sig := sig)) := by
  intro a b c hab hbc sub
  exact Nat.lt_trans (hab sub) (hbc sub)

theorem stableSizeLt_subst {sig : Signature} {sub : Subst sig} {s t : Term sig} :
    stableSizeLt (sig := sig) s t →
      stableSizeLt (sig := sig) (Term.subst sub s) (Term.subst sub t) := by
  intro h sub'
  have := h (Term.compSubst sub' sub)
  simpa [Term.subst_comp] using this

theorem stableSizeLt_replace {sig : Signature} {t : Term sig} {p : Pos} {u v t' t'' : Term sig}
    (h : stableSizeLt (sig := sig) u v)
    (hrep1 : Term.replace t p u = some t')
    (hrep2 : Term.replace t p v = some t'') :
    stableSizeLt (sig := sig) t' t'' := by
  intro sub
  have hrep1' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := u) (t' := t') hrep1
  have hrep2' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := v) (t' := t'') hrep2
  have hsize : Term.size (Term.subst sub u) < Term.size (Term.subst sub v) := h sub
  simpa using Term.size_replace_lt (t := Term.subst sub t)
    (u := Term.subst sub u) (v := Term.subst sub v)
    (t' := Term.subst sub t') (t'' := Term.subst sub t'') hrep1' hrep2' hsize

/-- Stable size ordering packaged as a reduction ordering. -/
def stableSizeOrdering (sig : Signature) : ReductionOrdering sig :=
  { lt := stableSizeLt
    wf := stableSizeLt_wf
    trans := stableSizeLt_trans
    subst_closed := stableSizeLt_subst
    replace_closed := by
      intro t p u v t' t'' h hrep1 hrep2
      exact stableSizeLt_replace (t := t) (p := p) (u := u) (v := v) (t' := t') (t'' := t'') h hrep1 hrep2 }

/-- A rewrite step decreases any reduction ordering that orients all rules. -/
theorem step_decreasing_of_ordering {sig : Signature} {rules : RuleSet sig}
    {ord : ReductionOrdering sig}
    (hord : ∀ r, rules r → ord.lt r.rhs r.lhs) :
    ∀ {s t : Term sig}, Step rules s t → ord.lt t s := by
  intro s t hstep
  rcases hstep with ⟨r, hr, p, sub, hsub, hrep⟩
  have hlt : ord.lt (Term.subst sub r.rhs) (Term.subst sub r.lhs) :=
    ord.subst_closed (hord r hr)
  have hrep_self : Term.replace s p (Term.subst sub r.lhs) = some s :=
    Term.replace_self (t := s) (p := p) (u := Term.subst sub r.lhs) hsub
  exact ord.replace_closed hlt hrep hrep_self

/-- Multi-step reduction also decreases a reduction ordering. -/
theorem plus_decreasing_of_ordering {sig : Signature} {rules : RuleSet sig}
    {ord : ReductionOrdering sig}
    (hord : ∀ r, rules r → ord.lt r.rhs r.lhs) :
    ∀ {s t : Term sig}, Rewriting.Plus (Step rules) s t → ord.lt t s := by
  intro s t hplus
  induction hplus with
  | single hstep =>
      exact step_decreasing_of_ordering (ord := ord) hord hstep
  | tail hst hstep ih =>
      have hstep' := step_decreasing_of_ordering (ord := ord) hord hstep
      exact ord.trans hstep' ih

/-- Termination criterion via a reduction ordering. -/
theorem terminating_of_ordering {sig : Signature} {rules : RuleSet sig}
    (ord : ReductionOrdering sig)
    (hord : ∀ r, rules r → ord.lt r.rhs r.lhs) :
    Terminating rules := by
  apply Subrelation.wf
  · intro a b hplus
    exact plus_decreasing_of_ordering (ord := ord) hord hplus
  · exact ord.wf

/-! ## Termination + Local Confluence -/

/-- Specialized Newman's lemma for a rule set. -/
theorem confluent_of_terminating_localConfluent
    {sig : Signature} {rules : RuleSet sig} :
    Terminating rules → LocalConfluent rules → Confluent rules := by
  intro hterm hlocal
  exact Rewriting.confluent_of_terminating_localConfluent hterm hlocal

/-- Knuth-Bendix completion soundness: terminating + joinable critical pairs imply confluence. -/
theorem confluent_of_terminating_criticalPairsJoinable
    {sig : Signature} {rules : RuleSet sig}
    (hterm : Terminating rules)
    (hjoin : CriticalPairsJoinable rules) :
    Confluent rules := by
  apply confluent_of_terminating_localConfluent hterm
  exact localConfluent_of_criticalPairsJoinable hjoin

/-! ## Knuth-Bendix Completion Certificates -/

/-- Knuth-Bendix completion certificate: oriented rules + joinable critical pairs. -/
structure KnuthBendixComplete {sig : Signature} (rules : RuleSet sig)
    (ord : ReductionOrdering sig) : Prop where
  orient : ∀ r, rules r → ord.lt r.rhs r.lhs
  criticalPairsJoinable : CriticalPairsJoinable rules

/-- Completion soundness: a Knuth-Bendix certificate yields confluence. -/
theorem confluent_of_knuthBendixComplete {sig : Signature} {rules : RuleSet sig}
    {ord : ReductionOrdering sig}
    (hkb : KnuthBendixComplete rules ord) :
    Confluent rules := by
  apply confluent_of_terminating_criticalPairsJoinable
  · exact terminating_of_ordering (ord := ord) hkb.orient
  · exact hkb.criticalPairsJoinable

end Metatheory.TRS.FirstOrder
