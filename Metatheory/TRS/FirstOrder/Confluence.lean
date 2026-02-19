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
/-- Rules with non-variable left-hand sides (standard TRS assumption). -/
def NonVarLHS {sig : Signature} (rules : RuleSet sig) : Prop :=
  ∀ r, rules r → NonVar r.lhs

def CriticalPairsComplete {sig : Signature} (rules : RuleSet sig) : Prop :=
  NonVarLHS rules →
  ∀ s b c, Step rules s b → Step rules s c →
    (∃ d, Step rules b d ∧ Step rules c d) ∨
    ∃ cp p, CriticalPairs rules cp ∧
      ((replace s p cp.left = some b ∧ replace s p cp.right = some c) ∨
        (replace s p cp.left = some c ∧ replace s p cp.right = some b))

/-! ## Peak Decomposition -/

-- subterm_replace_same is not needed; use Term.replace_self directly where needed.

open Term

/-- Position trichotomy: two positions are either prefix-related or disjoint. -/
private theorem pos_trichotomy (p q : Pos) :
    PosPrefix p q ∨ PosPrefix q p ∨ (¬ PosPrefix p q ∧ ¬ PosPrefix q p) := by
  induction p generalizing q with
  | nil => exact Or.inl ⟨q, by simp⟩
  | cons i ps ih =>
    cases q with
    | nil => exact Or.inr (Or.inl ⟨i :: ps, by simp⟩)
    | cons j qs =>
      by_cases hij : i = j
      · subst hij
        rcases ih qs with h | h | ⟨h1, h2⟩
        · rcases h with ⟨r, rfl⟩
          exact Or.inl ⟨r, by simp⟩
        · rcases h with ⟨r, rfl⟩
          exact Or.inr (Or.inl ⟨r, by simp⟩)
        · exact Or.inr (Or.inr ⟨
            fun ⟨r, hr⟩ => h1 ⟨r, by simpa using hr⟩,
            fun ⟨r, hr⟩ => h2 ⟨r, by simpa using hr⟩⟩)
      · exact Or.inr (Or.inr ⟨
          fun ⟨r, hr⟩ => hij (by simpa using List.cons_eq_cons.mp hr |>.1),
          fun ⟨r, hr⟩ => hij (by simpa using List.cons_eq_cons.mp hr |>.1).symm⟩)

/-- Peak decomposition for first-order steps. -/
theorem criticalPairsComplete_of_steps {sig : Signature} {rules : RuleSet sig} :
    CriticalPairsComplete rules := by
  intro hnvl s b c hb hc
  -- Unpack the two steps
  rcases hb with ⟨r1, hr1, p1, sub1, hsub1, hrep1⟩
  rcases hc with ⟨r2, hr2, p2, sub2, hsub2, hrep2⟩
  -- Case split on position relationship
  rcases pos_trichotomy p1 p2 with hp | hp | ⟨hnotp, hnotq⟩
  · -- Case 1: p1 is prefix of p2 (p2 = p1 ++ q)
    rcases hp with ⟨q, rfl⟩
    -- r2 is applied inside the subterm matched by r1
    -- This is an overlap: a critical pair
    -- The subterm of s at p1 is sub1(r1.lhs), and at p1++q is sub2(r2.lhs)
    -- So sub1(r1.lhs) has sub2(r2.lhs) at position q
    have hsub2' : Term.subterm (Term.subst sub1 r1.lhs) q = some (Term.subst sub2 r2.lhs) := by
      have := Term.subterm_append (t := s) (p := p1) (q := q) (u := Term.subst sub1 r1.lhs) hsub1
      simpa using this ▸ hsub2
    -- Build the critical pair
    have hnonvar : NonVar (Term.subst sub2 r2.lhs) := by
      have h_nvl := hnvl r2 hr2
      cases r2.lhs with
      | var y => exact (h_nvl (by simp [IsVar])).elim
      | app f args => simp [NonVar, IsVar]
    -- Build the overlap and critical pair
    have hoverlap : Overlap r1 r2 q sub1 sub2 := ⟨hsub2', hnonvar⟩
    -- mkCriticalPair builds the pair
    cases hmk : mkCriticalPair r1 r2 q sub1 sub2 with
    | none =>
      -- If mkCriticalPair returns none, replace failed, but we know replace succeeds
      exfalso
      unfold mkCriticalPair at hmk
      cases hrep_inner : Term.replace (Term.subst sub1 r1.lhs) q (Term.subst sub2 r2.rhs) with
      | none =>
        -- replace at q must succeed since subterm at q exists
        rcases Term.replace_defined_of_replace (t := Term.subst sub1 r1.lhs) (p := q)
          (u := Term.subst sub2 r2.lhs) (t' := Term.subst sub1 r1.lhs)
          (Term.replace_self (t := Term.subst sub1 r1.lhs) (p := q)
            (u := Term.subst sub2 r2.lhs) hsub2')
          (Term.subst sub2 r2.rhs) with ⟨_, hrep_ok⟩
        simp [hrep_inner] at hrep_ok
      | some _ => simp [hrep_inner] at hmk
    | some cp =>
      -- We have a critical pair
      right
      refine ⟨cp, p1, ?_, ?_⟩
      · exact ⟨r1, r2, q, sub1, sub2, hr1, hr2, hoverlap, hmk⟩
      · -- Show b and c correspond to replacing at p1
        unfold mkCriticalPair at hmk
        cases hrep_inner : Term.replace (Term.subst sub1 r1.lhs) q (Term.subst sub2 r2.rhs) with
        | none => simp [hrep_inner] at hmk
        | some t_inner =>
          simp [hrep_inner] at hmk
          left
          constructor
          · -- b = replace(s, p1, sub1(r1.rhs)) and cp.left = sub1(r1.rhs)
            have hcp_left : cp.left = Term.subst sub1 r1.rhs := hmk.1
            rw [hcp_left]
            exact hrep1
          · -- c = replace(s, p1++q, sub2(r2.rhs)) and cp.right = t_inner
            -- = replace(sub1(r1.lhs), q, sub2(r2.rhs))
            have hcp_right : cp.right = t_inner := hmk.2
            rw [hcp_right]
            -- c = replace(s, p1++q, sub2(r2.rhs))
            -- = replace(s, p1, replace(sub1(r1.lhs), q, sub2(r2.rhs)))
            -- = replace(s, p1, t_inner)
            -- This follows from replace_append_inv and the relationship
            rcases Term.replace_append_inv (t := s) (u := Term.subst sub1 r1.lhs)
              (t' := c) (p := p1) (q := q) (v := Term.subst sub2 r2.rhs)
              hsub1 hrep2 with ⟨u', hrep_u', hrep_s⟩
            have : u' = t_inner := by
              have : (some u' : Option (Term sig)) = some t_inner := by
                rw [← hrep_u', ← hrep_inner]
              exact Option.some.inj this
            rw [this] at hrep_s
            exact hrep_s
  · -- Case 2: p2 is prefix of p1 (p1 = p2 ++ q)
    rcases hp with ⟨q, rfl⟩
    -- Symmetric to case 1: r1 is applied inside the subterm matched by r2
    have hsub1' : Term.subterm (Term.subst sub2 r2.lhs) q = some (Term.subst sub1 r1.lhs) := by
      have := Term.subterm_append (t := s) (p := p2) (q := q) (u := Term.subst sub2 r2.lhs) hsub2
      simpa using this ▸ hsub1
    have hnonvar : NonVar (Term.subst sub1 r1.lhs) := by
      have h_nvl := hnvl r1 hr1
      cases r1.lhs with
      | var y => exact (h_nvl (by simp [IsVar])).elim
      | app f args => simp [NonVar, IsVar]
    have hoverlap : Overlap r2 r1 q sub2 sub1 := ⟨hsub1', hnonvar⟩
    cases hmk : mkCriticalPair r2 r1 q sub2 sub1 with
    | none =>
      exfalso
      unfold mkCriticalPair at hmk
      cases hrep_inner : Term.replace (Term.subst sub2 r2.lhs) q (Term.subst sub1 r1.rhs) with
      | none =>
        rcases Term.replace_defined_of_replace (t := Term.subst sub2 r2.lhs) (p := q)
          (u := Term.subst sub1 r1.lhs) (t' := Term.subst sub2 r2.lhs)
          (Term.replace_self (t := Term.subst sub2 r2.lhs) (p := q)
            (u := Term.subst sub1 r1.lhs) hsub1')
          (Term.subst sub1 r1.rhs) with ⟨_, hrep_ok⟩
        simp [hrep_inner] at hrep_ok
      | some _ => simp [hrep_inner] at hmk
    | some cp =>
      right
      refine ⟨cp, p2, ?_, ?_⟩
      · exact ⟨r2, r1, q, sub2, sub1, hr2, hr1, hoverlap, hmk⟩
      · unfold mkCriticalPair at hmk
        cases hrep_inner : Term.replace (Term.subst sub2 r2.lhs) q (Term.subst sub1 r1.rhs) with
        | none => simp [hrep_inner] at hmk
        | some t_inner =>
          simp [hrep_inner] at hmk
          -- cp.left = sub2(r2.rhs), cp.right = t_inner
          right
          constructor
          · -- c corresponds to cp.left
            have hcp_left : cp.left = Term.subst sub2 r2.rhs := hmk.1
            rw [hcp_left]
            exact hrep2
          · -- b corresponds to cp.right
            have hcp_right : cp.right = t_inner := hmk.2
            rw [hcp_right]
            rcases Term.replace_append_inv (t := s) (u := Term.subst sub2 r2.lhs)
              (t' := b) (p := p2) (q := q) (v := Term.subst sub1 r1.rhs)
              hsub2 hrep1 with ⟨u', hrep_u', hrep_s⟩
            have : u' = t_inner := by
              have : (some u' : Option (Term sig)) = some t_inner := by
                rw [← hrep_u', ← hrep_inner]
              exact Option.some.inj this
            rw [this] at hrep_s
            exact hrep_s
  · -- Case 3: Disjoint positions
    -- Both rewrites can be applied independently
    left
    rcases Term.replace_comm_of_disjoint (t := s) (u := Term.subst sub1 r1.rhs)
      (v := Term.subst sub2 r2.rhs) (t1 := b) (t2 := c) (p := p1) (q := p2)
      hrep1 hrep2 hnotp hnotq with ⟨d, hrepd_from_b, hrepd_from_c⟩
    refine ⟨d, ?_, ?_⟩
    · -- Step from b to d: apply r2 at p2 in b
      -- subterm of b at p2 = subterm of s at p2 (since p1 and p2 are disjoint)
      have hsub2_in_b : Term.subterm b p2 = some (Term.subst sub2 r2.lhs) := by
        have := Term.subterm_replace_of_disjoint (t := s) (u := Term.subst sub1 r1.rhs)
          (t' := b) (p := p1) (q := p2) hrep1 hnotq hnotp
        rw [this]
        exact hsub2
      exact ⟨r2, hr2, p2, sub2, hsub2_in_b, hrepd_from_b⟩
    · -- Step from c to d: apply r1 at p1 in c
      have hsub1_in_c : Term.subterm c p1 = some (Term.subst sub1 r1.lhs) := by
        have := Term.subterm_replace_of_disjoint (t := s) (u := Term.subst sub2 r2.rhs)
          (t' := c) (p := p2) (q := p1) hrep2 hnotp hnotq
        rw [this]
        exact hsub1
      exact ⟨r1, hr1, p1, sub1, hsub1_in_c, hrepd_from_c⟩

theorem criticalPairsJoinable_of_localConfluent
    {sig : Signature} {rules : RuleSet sig} (hlocal : LocalConfluent rules) :
    CriticalPairsJoinable rules := by
  intro cp hcp
  rcases hcp with ⟨r1, r2, p, sub1, sub2, hr1, hr2, hover, hmk⟩
  rcases hover with ⟨hsub_eq, hnonvar⟩
  -- The overlap gives us two steps from the same term
  -- Step 1: r1 applied at root gives cp.left (i.e., sub1(r1.rhs))
  -- Step 2: r2 applied at position p gives cp.right
  -- Both rewrite the same source term = sub1(r1.lhs)
  -- This is a local peak, so by local confluence they are joinable
  have hsource := Term.subst sub1 r1.lhs
  have hstep1 : Step rules hsource (Term.subst sub1 r1.rhs) := by
    exact ⟨r1, hr1, [], sub1, by simp [Term.subterm], by simp [Term.replace]⟩
  -- For step2 we need to extract the critical pair structure
  -- mkCriticalPair r1 r2 p sub1 sub2 = some cp means
  -- cp.left = sub1(r1.rhs), cp.right = replace(sub1(r1.lhs), p, sub2(r2.rhs))
  unfold mkCriticalPair at hmk
  cases hrep : Term.replace (Term.subst sub1 r1.lhs) p (Term.subst sub2 r2.rhs) with
  | none => simp [hrep] at hmk
  | some t =>
    simp [hrep] at hmk
    have hcp_left : cp.left = Term.subst sub1 r1.rhs := hmk.1
    have hcp_right : cp.right = t := hmk.2
    have hstep2 : Step rules hsource t := by
      exact ⟨r2, hr2, p, sub2, hsub_eq, hrep⟩
    rcases hlocal hsource (Term.subst sub1 r1.rhs) t hstep1 hstep2 with ⟨d, hd1, hd2⟩
    rw [hcp_left, hcp_right]
    exact ⟨d, hd1, hd2⟩

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
    (hnvl : NonVarLHS rules)
    (hjoin : CriticalPairsJoinable rules) :
    LocalConfluent rules := by
  intro s b c hb hc
  have hcomplete := criticalPairsComplete_of_steps (rules := rules) hnvl s b c hb hc
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
  trans : ∀ {a b c}, lt a b → lt b c → lt a c
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

theorem stableSizeLt_trans {sig : Signature} {a b c : Term sig} (hab : stableSizeLt a b) (hbc : stableSizeLt b c) : stableSizeLt a c := by
  intro sub
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
    trans := fun hab hbc => stableSizeLt_trans hab hbc
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
    (hnvl : NonVarLHS rules)
    (hterm : Terminating rules)
    (hjoin : CriticalPairsJoinable rules) :
    Confluent rules := by
  apply confluent_of_terminating_localConfluent hterm
  exact localConfluent_of_criticalPairsJoinable hnvl hjoin

/-! ## Knuth-Bendix Completion Certificates -/

/-- Knuth-Bendix completion certificate: oriented rules + joinable critical pairs. -/
structure KnuthBendixComplete {sig : Signature} (rules : RuleSet sig)
    (ord : ReductionOrdering sig) : Prop where
  nonVarLHS : NonVarLHS rules
  orient : ∀ r, rules r → ord.lt r.rhs r.lhs
  criticalPairsJoinable : CriticalPairsJoinable rules

/-- Completion soundness: a Knuth-Bendix certificate yields confluence. -/
theorem confluent_of_knuthBendixComplete {sig : Signature} {rules : RuleSet sig}
    {ord : ReductionOrdering sig}
    (hkb : KnuthBendixComplete rules ord) :
    Confluent rules := by
  apply confluent_of_terminating_criticalPairsJoinable hkb.nonVarLHS
  · exact terminating_of_ordering (ord := ord) hkb.orient
  · exact hkb.criticalPairsJoinable

end Metatheory.TRS.FirstOrder
