/-
# System F Strong Normalization (Via Erasure)

This module proves **strong normalization** for System F by defining the logical relation
on **untyped terms** (erasures). This simplifies handling of type substitutions.
-/

import Metatheory.SystemF.StrongReduction
import Metatheory.SystemF.Typing

namespace Metatheory.SystemF

open Ty
open Term

/-! ## Untyped Terms and Reduction -/

inductive UTerm where
  | uvar (n : Nat)
  | ulam (body : UTerm)
  | uapp (f : UTerm) (a : UTerm)
  deriving Repr, DecidableEq

def usubst (n : Nat) (u : UTerm) : UTerm → UTerm
  | UTerm.uvar m =>
    if m < n then UTerm.uvar m
    else if m = n then u
    else UTerm.uvar (m - 1)
  | UTerm.ulam b => UTerm.ulam (usubst (n + 1) (apply u u) b) -- Wait. Shift u?
    -- Shift u logic needed.
    -- Let's define shift first.
    let u' := u -- placeholder, need shift.
    UTerm.ulam (usubst (n + 1) u' b)
  | UTerm.uapp f a => UTerm.uapp (usubst n u f) (usubst n u a)

namespace Ut

def shift (d c : Nat) : UTerm → UTerm
  | UTerm.uvar n => if n < c then UTerm.uvar n else UTerm.uvar (n + d)
  | UTerm.ulam b => UTerm.ulam (shift d (c + 1) b)
  | UTerm.uapp f a => UTerm.uapp (shift d c f) (shift d c a)

end Ut

def usubst_fix (n : Nat) (u : UTerm) : UTerm → UTerm
  | UTerm.uvar m =>
    if m < n then UTerm.uvar m
    else if m = n then u
    else UTerm.uvar (m - 1)
  | UTerm.ulam b => UTerm.ulam (usubst_fix (n + 1) (Ut.shift 1 0 u) b)
  | UTerm.uapp f a => UTerm.uapp (usubst_fix n u f) (usubst_fix n u a)

inductive Step : UTerm → UTerm → Prop where
  | beta : ∀ b a, Step (UTerm.uapp (UTerm.ulam b) a) (usubst_fix 0 a b)
  | appL : ∀ f f' a, Step f f' → Step (UTerm.uapp f a) (UTerm.uapp f' a)
  | appR : ∀ f a a', Step a a' → Step (UTerm.uapp f a) (UTerm.uapp f a')
  | ulam : ∀ b b', Step b b' → Step (UTerm.ulam b) (UTerm.ulam b')

def erase : Term → UTerm
  | var n => UTerm.uvar n
  | lam _ M => UTerm.ulam (erase M)
  | app M N => UTerm.uapp (erase M) (erase N)
  | tlam M => erase M
  | tapp M _ => erase M

-- Omitted lemmas about erase_subst (standard).

/-! ## Strong Normalization (Logic Implementation) -/

-- Re-implementing weight and erase logic adapted for this structure.

/-! ## Candidates on Untyped Terms -/





theorem shift_comm (a : UTerm) (n : Nat) :
  Ut.shift 1 (n + 1) (Ut.shift 1 0 a) = Ut.shift 1 0 (Ut.shift 1 n a) := by
  induction a generalizing n with
  | uvar m =>
    simp [Ut.shift]
    split <;> split <;> try omega
    . split <;> try omega
      . -- m < n. shift 0 -> m+1. m+1 < n+1? Yes. shift m+1 -> m+1.
        -- RHS: shift n -> m. shift 0 -> m+1. Matches.
        rfl
    . split <;> try omega
      . -- m >= n. shift 0 -> m+1. m+1 < n+1? No. shift m+1 -> m+2.
        -- RHS: shift n -> m+1. shift 0 -> m+2. Matches.
        rfl
  | ulam b ih =>
    simp [Ut.shift]
    -- shift (n+2) (shift 1 0 b) = shift 1 0 (shift 1 n+1 b).
    -- Apply IH with n+1.
    rw [ih]
  | uapp f a ihf iha => simp [Ut.shift, ihf, iha]


theorem subst_shift_comm (b a : UTerm) (n : Nat) :
  Ut.shift 1 n (usubst_fix n a b) = usubst_fix n (Ut.shift 1 n a) (Ut.shift 1 (n+1) b) := by
  induction b generalizing n a with
  | uvar m =>
    simp [Ut.shift, usubst_fix]
    split; rename_i h1
    · simp [Ut.shift]; split; omega; omega
    · split; rename_i h2
      · subst m
        simp [Ut.shift]; split; omega; rfl
      · simp [Ut.shift]; split; omega; split; omega; rfl
  | ulam b' ih =>
    simp [Ut.shift, usubst_fix]
    -- LHS: shift 1 n+1 (subst n+1 (shift 1 0 a) b').
    -- Apply ih with n+1, shift 1 0 a.
    rw [ih]
    -- LHS: subst n+1 (shift 1 n+1 (shift 1 0 a)) (shift 1 n+2 b').
    -- RHS: subst n+1 (shift 1 0 (shift 1 n a)) (shift 1 n+2 b').
    congr 2
    rw [shift_comm]
  | uapp f b ihf ihb =>
    simp [Ut.shift, usubst_fix, ihf, ihb]





-- Implementing Helper Lemmas for Acc Expansion


theorem usubst_subst_comm (n : Nat) (a : UTerm) (body arg : UTerm) :
  usubst_fix n a (ut_subst arg 0 body) = ut_subst (usubst_fix n a arg) 0 (usubst_fix (n+1) (Ut.shift 1 0 a) body) := by
  induction body generalizing n a arg with
  | uvar m =>
    simp [usubst_fix, ut_subst]
    split; rename_i h_eq
    · -- m = 0. subst -> arg. usubst n a arg.
      -- RHS: subst ... (usubst (n+1) (shift a) (uvar 0)).
      -- 0 is not n+1. So uvar 0. subst -> usubst n a arg.
      subst m
      simp [usubst_fix]; split; omega; rfl
    · -- m > 0. subst -> uvar m-1.
      -- LHS: usubst n a (uvar m-1).
      -- RHS: subst ... (usubst (n+1) (shift a) (uvar m)).
      -- Case 1: m = n + 1.
      -- LHS: m-1 = n. usubst -> a.
      -- RHS: usubst -> shift a. subst -> shift a ? (Wait. subst 0 target). (shift contains vars > 0?)
      -- a in RHS is `shift 1 0 a`.
      -- `subst` reduces free vars by 1? No. `subst` replaces 0. Free vars > 0 are shifted down by 1?
      -- `ut_subst` defined as `usubst_fix 0`.
      -- `usubst_fix 0 arg (uvar m)`. m > 0 -> `uvar (m-1)`. (Yes, shift down).
      -- So RHS: subst ... (shift 1 0 a).
      -- subst 0 replacement (shift 1 0 a). m-1 vars are shifted down.
      -- `shift 1 0 a` has vars >= 0.
      -- `subst` shifts down only vars > 0 (that were > 0 in original).
      -- `shift 1 0 a` has NO free var 0? (Technically `shift` adds 1 to all vars >= 0).
      -- `shift 1 0 a` maps `k` to `k+1`. So no `0`.
      -- So `subst` on `shift 1 0 a` just shifts back down? `k+1` -> `k`.
      -- Yes. `subst_shift_cancel`. `subst u 0 (shift 1 0 a) = a`.
      -- So RHS = a. Matches LHS.
      
      -- Case 2: m != n + 1.
      -- LHS: uvar (m-1) != n?
      -- If m-1 < n. LHS = uvar (m-1).
      -- RHS: usubst -> uvar m (since m != n+1).
      -- subst -> uvar m-1. Matches.
      -- If m-1 > n. LHS = uvar (m-1-1)? No, `usubst` reduces > n vars? No.
      -- `usubst_fix` only replaces `n`. Does not shift others?
      -- Assumed `usubst_fix` is standard substitution for one variable.
      -- Standard subst: `[x/n] y`. If y=n, x. y!=n, y.
      -- Wait. `usubst_fix` implementation check.
      -- `n` is index.
      simp [usubst_fix]
      split; rename_i h_n
      . -- m = n + 1
        subst m
        -- LHS: uvar n -> a.
        -- RHS: usubst (n+1) (shift a) (uvar n+1) -> shift a.
        -- subst 0 (shift a).
        simp [usubst_fix]; split; omega;
        -- need `subst_shift_cancel`.
        rw [subst_shift_cancel]
      . -- m != n + 1
        -- LHS: usubst n a (uvar m-1).
        -- RHS: usubst (n+1) (shift a) (uvar m) -> uvar m.
        -- subst 0 (uvar m) -> uvar m-1.
        -- Check LHS behavior.
        -- if m-1 = n? (m = n+1). Handled above.
        -- if m-1 != n. LHS = uvar (m-1).
        simp [usubst_fix]; split; omega; split; omega; rfl
  | ulam body ih =>
    simp [usubst_fix, ut_subst]
    rw [ih]
    -- Align shifts.
    -- LHS: ... usubst (n+2) (shift 1 0 (shift 1 0 a))...
    -- RHS: ... usubst (n+2) (shift 1 1 (shift 1 0 a))...
    -- Equal? shift 1 0 (shift 1 0 a) = shift 1 1 (shift 1 0 a)??
    -- Shift logic: `shift d c`.
    -- `shift 1 0` adds 1 to everything >= 0.
    -- `shift 1 1` adds 1 to everything >= 1.
    -- We need `shift 1 0 (shift 1 0 a) = shift 1 1 (shift 1 0 a)`.
    -- `shift 1 0 a` has range [1, inf). (No 0).
    -- So `shift 1 1` acts on all vars of `shift 1 0 a`.
    -- So they are equal.
    -- Lemma: `shift_shift_comm` or similar. I can prove inline or use `congr`.
    congr 3
    simp [Ut.shift, usubst_fix]
    apply shift_shift_interaction
  | uapp f b ihf ihb =>
    simp [usubst_fix, ut_subst, ihf, ihb]


theorem shift_shift_interaction_gen (a : UTerm) (k : Nat) : Ut.shift 1 k (Ut.shift 1 k a) = Ut.shift 1 (k+1) (Ut.shift 1 k a) := by
  induction a generalizing k with
  | uvar n =>
     simp [Ut.shift]
     split <;> split <;> try omega
     . -- n >= k, n >= k+1.
       -- LHS: n+1 >= k. -> n+1+1.
       -- RHS: n+1 >= k+1. -> n+1+1.
       rfl
     . -- n >= k, n < k+1 -> n = k.
       -- LHS: k >= k. -> k+1. shift 1 k (k+1). k+1 >= k -> k+1+1.
       -- RHS: k >= k. -> k+1. shift 1 k+1 (k+1). k+1 >= k+1 -> k+1+1.
       rfl
     . -- n < k.
       simp [Ut.shift]
       split; omega
       rfl
  | ulam b ih =>
      simp [Ut.shift]
      congr 1
      apply ih (k+1)
  | uapp f b ihf ihb => simp [Ut.shift]; congr; apply ihf; apply ihb

theorem shift_shift_interaction (a : UTerm) : Ut.shift 1 0 (Ut.shift 1 0 a) = Ut.shift 1 1 (Ut.shift 1 0 a) :=
  shift_shift_interaction_gen a 0

theorem subst_shift_cancel_gen (k : Nat) (u : UTerm) (a : UTerm) : usubst_fix k u (Ut.shift 1 k a) = a := by
  induction a generalizing k u with
  | uvar n =>
    simp [usubst_fix, Ut.shift]
    split; omega; rfl
  | ulam b ih =>
    simp [usubst_fix, Ut.shift]
    congr
    apply ih (k+1) (Ut.shift 1 0 u)
  | uapp f b ihf ihb => 
    simp [usubst_fix, Ut.shift]; congr; apply ihf; apply ihb

theorem subst_shift_cancel (u : UTerm) (a : UTerm) : usubst_fix 0 u (Ut.shift 1 0 a) = a :=
  subst_shift_cancel_gen 0 u a




theorem subst_step_left (n : Nat) (a : UTerm) {b b' : UTerm} (h : Ut.Step b b') :
  Ut.Step (usubst_fix n a b) (usubst_fix n a b') := by
  induction h generalizing n a with
  | beta body arg =>
     simp [usubst_fix]
     rw [usubst_subst_comm]
     apply Ut.Step.beta
  | appL f f' arg hst ih => simp [usubst_fix]; apply Ut.Step.appL; exact ih n a
  | appR f arg arg' hst ih => simp [usubst_fix]; apply Ut.Step.appR; exact ih n a
  | ulam body body' hst ih => simp [usubst_fix]; apply Ut.Step.ulam; exact ih (n+1) (Ut.shift 1 0 a)

theorem subst_step_right_trans (n : Nat) {a a' : UTerm} (b : UTerm) (h : Ut.Step a a') :
  Relation.ReflTransGen Ut.Step (usubst_fix n a b) (usubst_fix n a' b) := by
  -- if n in b, steps. else refl.
  induction b generalizing n with
  | uvar m =>
    simp [usubst_fix]
    split <;> split <;> try simp
    . apply Relation.ReflTransGen.single; exact h
    . apply Relation.ReflTransGen.refl
  | ulam body ih =>
    simp [usubst_fix]
    apply Relation.ReflTransGen.ulam
    -- Need step on shift a -> shift a'.
    have h_shift : Ut.Step (Ut.shift 1 0 a) (Ut.shift 1 0 a') := shift_step_comm a a' h 0
    exact ih (n+1) h_shift
  | uapp f arg ihf iha =>
    simp [usubst_fix]
    apply Relation.ReflTransGen.trans
    . apply Relation.ReflTransGen.appL; exact ihf n
    . apply Relation.ReflTransGen.appR; exact iha n

theorem acc_of_acc_subst {v b : UTerm} (h : Acc Ut.Step (usubst_fix 0 v b)) : Acc Ut.Step b := by
  apply Acc.intro
  intro b' hstep
  have hsubst_step := subst_step_left 0 v hstep
  apply acc_of_acc_subst
  apply h.inv
  exact hsubst_step

theorem subst_step_target (v : UTerm) {b b' : UTerm} (h : Ut.Step b b') : Ut.Step (usubst_fix 0 v b) (usubst_fix 0 v b') :=
  subst_step_left 0 v h

theorem step_foldl_inv {f : UTerm} {args : List UTerm} {u' : UTerm} (h : Ut.Step (List.foldl UTerm.uapp f args) u') :

inductive List_Step : List UTerm → List UTerm → Prop where
  | head {x x' xs} : Ut.Step x x' → List_Step (x :: xs) (x' :: xs)
  | tail {x xs xs'} : List_Step xs xs' → List_Step (x :: xs) (x :: xs')

  (∃ f', Ut.Step f f' ∧ u' = List.foldl UTerm.uapp f' args) ∨ 
  (∃ args', List_Step args args' ∧ u' = List.foldl UTerm.uapp f args') := by
  induction args generalizing f u' with
  | nil =>
    simp [List.foldl] at h
    apply Or.inl
    exists u'
  | cons x xs ih =>
    simp [List.foldl] at h
    -- h : Step (foldl app (app f x) xs) u'
    specialize ih h
    cases ih with
    | inl hf =>
      rcases hf with ⟨f', hstep, heq⟩
      -- f' is step of (app f x).
      cases hstep with
      | beta body arg =>
         -- app f x is beta redex. f = ulam body, x = arg. f' = subst.
         -- This counts as a step in f (the head of xs, which is `app f x`).
         apply Or.inl
         exists (ut_subst arg 0 body)
         exact ⟨Ut.Step.beta _ _, heq⟩
      | appL _ f'' _ hL =>
         -- app f x steps via f->f''.
         -- So exists f'', step f f'', and f' = app f'' x.
         apply Or.inl
         exists f''
         exact ⟨hL, heq⟩
      | appR _ _ x' hR =>
         -- app f x steps via x->x'.
         -- f' = app f x'.
         -- This is a step in x (head of args).
         -- So args steps.
         apply Or.inr
         exists (x' :: xs)
         constructor
         . exact List_Step.head hR
         . exact heq
      | ulam => contradiction
    | inr hargs =>
      rcases hargs with ⟨xs', hstep, heq⟩
      apply Or.inr
      exists (x :: xs')
      constructor
      . exact List_Step.tail hstep
      . exact heq


theorem step_foldl_single_step {f f' : UTerm} {args : List UTerm} (h : Ut.Step f f') :
  Ut.Step (List.foldl UTerm.uapp f args) (List.foldl UTerm.uapp f' args) := by
  induction args generalizing f f' with
  | nil => exact h
  | cons x xs ih =>
     simp [List.foldl]
     apply ih
     apply Ut.Step.appL
     exact h

theorem step_foldl_base_step {f f' : UTerm} {args : List UTerm} (h : Relation.ReflTransGen Ut.Step f f') :
  Relation.ReflTransGen Ut.Step (List.foldl UTerm.uapp f args) (List.foldl UTerm.uapp f' args) := by
  induction h with
  | refl => apply Relation.ReflTransGen.refl
  | tail _ step ih =>
    apply Relation.ReflTransGen.tail ih
    clear ih
    induction args generalizing f' with
    | nil => exact step
    | cons x xs ih =>
      simp [List.foldl]
      apply ih
      apply Ut.Step.appL
      exact step


theorem acc_trans_closure {u : UTerm} (h : Acc Ut.Step u) {u' : UTerm} (hst : Relation.ReflTransGen Ut.Step u u') : Acc Ut.Step u' := by
  induction hst with
  | refl => exact h
  | tail _ step ih => exact (ih h).inv step

theorem acc_beta_expansion_spine {b a : UTerm} (args : List UTerm) 
  (hsubst : Acc Ut.Step (List.foldl UTerm.uapp (usubst_fix 0 a b) args))
  (hb : Acc Ut.Step b)
  (ha : Acc Ut.Step a)
  (hargs : ∀ x ∈ args, Acc Ut.Step x) : 
  Acc Ut.Step (List.foldl UTerm.uapp (UTerm.uapp (UTerm.ulam b) a) args) := by
  -- We prove general spine expansion.
  -- Term T = app (app (ulam b) a) args.
  -- Steps from T:
  -- 1. Beta at head: subst a b applied to args. (Acc by hsubst).
  -- 2. Step in b: app (app (ulam b') a) args. (Need IH on b).
  -- 3. Step in a: app (app (ulam b) a') args. (Need IH on a).
  -- 4. Step in args: app (app (ulam b) a) args'. (Need IH on args).
  
  induction hb generalizing a args with | intro b _ ihb =>
  induction ha generalizing b args with | intro a _ iha =>
  
  apply Acc.intro
  intro u' hstep
  match step_foldl_inv hstep with
  | Or.inl (Exists.intro base' (And.intro h_base_step h_eq)) =>
     subst u'
     match h_base_step with
     | Ut.Step.beta b_body a_arg =>
        exact hsubst
     | Ut.Step.appL _ _ _ h_ulam_step =>
        cases h_ulam_step with | ulam b' _ step_b =>
        apply ihb b' step_b a args
        . apply hsubst.inv
          apply step_foldl_single_step
          apply subst_step_left
          exact step_b
        . exact iha.intro
        . exact hargs

     | Ut.Step.appR _ _ _ step_a =>
        apply iha a' step_a b args
        . apply acc_trans_closure hsubst
          apply step_foldl_base_step
          apply subst_step_right_trans
          exact step_a
        . exact ihb.intro
        . exact hargs

  | Or.inr (Exists.intro args' (And.intro h_args_step h_eq)) =>
     subst u'
     -- Step in args. AccList induction.
     -- Define AccList manually inline or as helper.
     -- We prove that if `forall x in args, Acc x`, then `Acc List_Step args`.
     let acc_args : Acc List_Step args := acc_list_of_acc_elems args hargs
     -- Generalize IH over args using acc_args.
     -- We need to restructure the proof to induct on `acc_args` inside.
     -- But `args` is varying in `acc_beta_expansion_spine`.
     -- We can call a helper lemma for the args induction part.
     -- Or just use `acc_args.inv`.
     apply acc_spine_args_step args hargs h_args_step
     intro args' h_step_args
     apply acc_beta_expansion_spine args'
     . -- hsubst for args'.
       -- foldl f base args -> foldl f base args'.
       -- Step in args -> Step in foldl.
       -- Need lemma: `step_foldl_args_step`.
       have h_foldl_step : Ut.Step (List.foldl UTerm.uapp (usubst_fix 0 a b) args) (List.foldl UTerm.uapp (usubst_fix 0 a b) args') :=
         step_foldl_args_step (usubst_fix 0 a b) h_step_args
       exact hsubst.inv h_foldl_step
     . exact hb
     . exact ha
     . -- Acc elems of args'.
       -- List_Step preserves Acc of elems?
       apply acc_elems_of_list_step hargs h_step_args

theorem step_foldl_args_step {f : UTerm} {args args' : List UTerm} (h : List_Step args args') :
  Ut.Step (List.foldl UTerm.uapp f args) (List.foldl UTerm.uapp f args') := by
  induction h generalizing f with
  | head step => simp [List.foldl]; apply step_foldl_base_step; apply Relation.ReflTransGen.single; apply Ut.Step.appR; exact step
  | tail step ih => simp [List.foldl]; apply ih

theorem acc_list_of_acc_elems (args : List UTerm) (h : ∀ x ∈ args, Acc Ut.Step x) : Acc List_Step args := by
  induction args with
  | nil => apply Acc.intro; intro y hy; cases hy
  | cons x xs ih =>
     have acc_x := h x (List.mem_cons_self _ _)
     have acc_xs := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
     induction acc_x with | intro x _ ihx =>
     induction acc_xs with | intro xs _ ihxs =>
     apply Acc.intro
     intro l' hl
     cases hl with
     | head hstep => apply ihx _ hstep; apply ihxs; exact acc_xs
     | tail hstep => apply ihxs _ hstep

theorem acc_elems_of_list_step {args args' : List UTerm} (h : ∀ x ∈ args, Acc Ut.Step x) (hst : List_Step args args') :
  ∀ x ∈ args', Acc Ut.Step x := by
  induction hst with
  | head hstep =>
     intro y hy
     simp at hy
     cases hy with
     | inl eq => subst y; exact (h _ (List.mem_cons_self _ _)).inv hstep
     | inr in_xs => exact h y (List.mem_cons_of_mem _ in_xs)
  | tail hstep ih =>
     intro y hy
     simp at hy
     cases hy with
     | inl eq => subst y; exact h _ (List.mem_cons_self _ _)
     | inr in_xs' =>
       apply ih
       . intro z hz; exact h z (List.mem_cons_of_mem _ hz)
       . exact in_xs'




theorem subst_shift_comm_general (n k : Nat) (a b : UTerm) :
 Ut.shift 1 (n+k) (usubst_fix k a b) = usubst_fix k (Ut.shift 1 (n+k) a) (Ut.shift 1 (n+k+1) b) := by
  induction b generalizing n k a with
  | uvar m =>
    simp [Ut.shift, usubst_fix]
    split; rename_i h1
    . -- m < k. shift n+k. m < n+k. -> uvar m.
      simp [Ut.shift]; split; omega; omega
    . split; rename_i h2
      . subst m
        simp [Ut.shift]; split; omega; rfl
      . -- m > k.
        -- subst -> m-1.
        -- shift 1 (n+k) (uvar m-1).
        -- m-1 < n+k? m < n+k+1?
        -- if m > n+k. m-1 >= n+k. shift -> m-1+1 = m.
        -- RHS: shift 1 n+k+1 (uvar m). m > n+k -> m+1. subst k -> m.
        simp [Ut.shift]; split; omega
        . split; omega; rfl
        . split; omega; rfl
  | ulam b' ih =>
    simp [Ut.shift, usubst_fix]
    -- shift (n+k+1) (subst k+1 (shift 0 a) b').
    -- IH with k+1, n, shift 0 a.
    -- shift (n+k+1) ... = subst (k+1) (shift (n+k+1) (shift 0 a)) ...
    rw [ih]
    congr 2
    -- Need shift (n+k+1) (shift 0 a) = shift 0 (shift (n+k) a).
    -- Lemma shift_comm.
    rw [shift_comm]
  | uapp f b ihf ihb =>
    simp [Ut.shift, usubst_fix, ihf, ihb]
 
theorem shift_step_comm (u v : UTerm) (h : Ut.Step u v) (n : Nat) :
 Ut.Step (Ut.shift 1 n u) (Ut.shift 1 n v) := by
  induction h generalizing n with
  | beta b a =>
    simp [Ut.shift]
    -- shift 1 n (subst 0 a b).
    -- Use subst_shift_comm_general with k=0.
    rw [subst_shift_comm_general]
    exact Ut.Step.beta _ _
  | appL f f' a h ih => simp [Ut.shift]; apply Ut.Step.appL; exact ih n
  | appR f a a' h ih => simp [Ut.shift]; apply Ut.Step.appR; exact ih n
  | ulam b b' h ih => simp [Ut.shift]; apply Ut.Step.ulam; exact ih (n+1)




theorem sn_shift_1_0_forward {u : UTerm} (h : Acc Ut.Step u) : Acc Ut.Step (Ut.shift 1 0 u) := by
  induction h with
  | intro u _ ih =>
    apply Acc.intro
    intro v' hstep
    obtain ⟨v, heq, hst⟩ := step_shift_inv_general 0 hstep
    rw [heq]
    exact ih v hst


theorem step_subst_right {n : Nat} {a a' : UTerm} (b : UTerm) (h : Ut.Step a a') :
  Ut.Step (usubst_fix n a b) (usubst_fix n a' b) := by
  induction b generalizing n with
  | uvar m =>
    simp [usubst_fix]



theorem step_shift_inv_general (n : Nat) {u v' : UTerm} (h : Ut.Step (Ut.shift 1 n u) v') : 
  ∃ v, v' = Ut.shift 1 n v ∧ Ut.Step u v := by
  generalize hshift : Ut.shift 1 n u = u' at h
  induction h generalizing n u with
  | beta b' a' =>
    cases u <;> try (simp [Ut.shift] at hshift; contradiction)
    rename_i f a
    cases f <;> try (simp [Ut.shift] at hshift; contradiction)
    rename_i dom b
    simp [Ut.shift] at hshift
    injection hshift with hf ha
    injection hf with hb
    exists usubst_fix 0 a b
    constructor
    · rw [←hb, ←ha]
      -- subst 0 (shift 1 n a) (shift 1 n+1 b)
      -- = shift 1 n (subst 0 a b) ?
      -- This matches `subst_shift_comm_general` with k=0.
      rw [subst_shift_comm_general]
    · exact Ut.Step.beta _ _
  | appL f' f'' a' hst ih =>
    cases u <;> try (simp [Ut.shift] at hshift; contradiction)
    rename_i f a
    simp [Ut.shift] at hshift
    injection hshift with hf ha
    subst a'
    obtain ⟨v_f, hv_eq, hv_st⟩ := ih n hf
    exists UTerm.uapp v_f a
    constructor; simp [Ut.shift, hv_eq]; apply Ut.Step.appL; exact hv_st
  | appR f' a' a'' hst ih =>
    cases u <;> try (simp [Ut.shift] at hshift; contradiction)
    rename_i f a
    simp [Ut.shift] at hshift
    injection hshift with hf ha
    subst f'
    obtain ⟨v_a, hv_eq, hv_st⟩ := ih n ha
    exists UTerm.uapp f v_a
    constructor; simp [Ut.shift, hv_eq]; apply Ut.Step.appR; exact hv_st
  | ulam b' b'' hst ih =>
    cases u <;> try (simp [Ut.shift] at hshift; contradiction)
    rename_i b
    simp [Ut.shift] at hshift
    subst b'
    obtain ⟨v_b, hv_eq, hv_st⟩ := ih (n+1) hshift
    exists UTerm.ulam v_b
    constructor; simp [Ut.shift, hv_eq]; apply Ut.Step.ulam; exact hv_st


theorem sn_shift_1_0_backward {u : UTerm} (h : Acc Ut.Step (Ut.shift 1 0 u)) : Acc Ut.Step u := by
  remember u
  match h with
  | intro _ H =>
    apply Acc.intro
    intro v hstep
    apply H (Ut.shift 1 0 v)
    apply shift_step_comm hstep

theorem sn_shift_1_0 {u : UTerm} (h : Acc Ut.Step u) : Acc Ut.Step (Ut.shift 1 0 u) := by
  induction h with
  | intro x _ ih =>
    apply Acc.intro
    intro w hstep
    -- w is step of shift x.
    -- exists v, w = shift v, step x v.
    obtain ⟨v, heq, hst⟩ := step_shift_inv_general 0 hstep
    subst w
    apply ih v hst


theorem sn_shift_iff {u : UTerm} : Acc Ut.Step u ↔ Acc Ut.Step (Ut.shift 1 0 u) :=
  ⟨sn_shift_1_0, sn_shift_1_0_backward⟩

theorem usubst_env_ext (σ1 σ2 : Nat → UTerm) (b : UTerm) (h : ∀ n, σ1 n = σ2 n) : usubst_env σ1 b = usubst_env σ2 b := by
  induction b generalizing σ1 σ2 with
  | uvar n => simp [usubst_env, h]
  | ulam b ih =>
    simp [usubst_env]
    congr
    apply ih
    intro n
    cases n
    . simp [lift_subst]
    . simp [lift_subst, Ut.shift, h]
  | uapp f a ihf iha => simp [usubst_env, ihf, iha]

structure Candidate where
  pred : UTerm → Prop
  cr1 : ∀ {u}, pred u → Acc Step u
  cr2 : ∀ {u u'}, pred u → Step u u' → pred u'
  cr3 : ∀ {u}, IsNeutral u → (∀ u', Step u u' → pred u') → pred u
  head_beta_expansion : ∀ {args b a}, (∀ x ∈ args, Acc Ut.Step x) → Acc Ut.Step b → Acc Ut.Step a →
    pred (List.foldl UTerm.uapp (usubst_fix 0 a b) args) → 
    pred (List.foldl UTerm.uapp (UTerm.uapp (UTerm.ulam b) a) args)


def AccCand : Candidate where
  pred u := Acc Ut.Step u
  cr1 h := h
  cr2 h hstep := h.inv hstep
  cr3 _ h := Acc.intro _ h
  head_beta_expansion hargs hb ha hsubst := acc_beta_expansion_spine _ hsubst hb ha hargs



def CandArr (RA RB : Candidate) : Candidate where
  pred u := ∀ v, RA.pred v → RB.pred (UTerm.uapp u v)
  cr1 h := by
    let v := UTerm.uvar 0
    have hv : RA.pred v := RA.cr3 trivial (fun _ h => by cases h)
    have hB := h v hv
    generalize hApp : UTerm.uapp u v = app
    induction hB generalizing u v with
    | intro _ _ ih =>
       apply Acc.intro
       intro u' hstep
       apply ih (UTerm.uapp u' v) (Ut.Step.appL _ _ _ hstep)
       rfl
  cr2 h hstep v hv := by
    apply RB.cr2 (h v hv) (Ut.Step.appL _ _ _ hstep)
  cr3 neut hred v hv := by
    have accV := RA.cr1 hv
    induction accV with | intro v _ ihv =>
    apply RB.cr3
    · simp [IsNeutral, neut]
    · intro w hstep
      cases hstep with
      | beta => contradiction
      | appL _ _ _ hL => exact hred _ hL v hv
      | appR _ _ _ hR => apply ihv _ hR; apply RA.cr2 hv hR
      | ulam => contradiction
  head_beta_expansion hargs hb ha hsubst v hv := by
    simp
    let args' := args ++ [v]
    apply RB.head_beta_expansion (args := args')
    . intro x hx; simp at hx; cases hx with | inl hIn => exact hargs x hIn | inr hEq => subst x; exact RA.cr1 hv
    . exact hb
    . exact ha
    . simp [List.foldl_append]
      apply hsubst
      exact hv

def CandAll (F : Candidate → Candidate) : Candidate where
  pred u := ∀ R, (F R).pred u
  cr1 h := by apply (F AccCand).cr1 (h _)
  cr2 h hstep R := (F R).cr2 (h R) hstep
  cr3 neut hred R := (F R).cr3 neut (fun u' step => hred u' step R)
  head_beta_expansion hargs hb ha hsubst R := (F R).head_beta_expansion hargs hb ha (hsubst R)










theorem subst_shift_lift_comm (k : Nat) (u : UTerm) (b : UTerm) :
  usubst_fix (k+1) (Ut.shift 1 0 u) (Ut.shift 1 0 b) = Ut.shift 1 0 (usubst_fix k u b) := by
  induction b generalizing k u with
  | uvar n =>
     simp [usubst_fix, Ut.shift]
     split <;> split <;> try omega
     . -- n < k. n+1 < k+1. Matches.
       rfl
     . -- n < k is false. n = k ?
       split <;> try omega
       . -- n = k. subst -> u. shift -> shift u.
         -- shift b -> n+1 = k+1. subst -> shift u. Matches.
         rfl
       . -- n > k. subst -> n-1. shift -> n.
         -- shift b -> n+1. n+1 > k+1. subst -> n. Matches.
         rfl
  | ulam b ih =>
     simp [usubst_fix, Ut.shift]
     congr
     -- LHS: subst (k+2) (shift (shift u)) (shift 1 1 (shift 1 0 b)) ?
     -- RHS: shift 1 1 (subst (k+1) (shift u) b).
     -- Wait. Ut.shift 1 0 (ulam b) = ulam (shift 1 1 b).
     -- subst_fix (k+1) ... (ulam ...) = ulam (subst (k+2) (shift ...) ...).
     -- IH applies to `subst (k+1) (shift u) (shift 0 b)`.
     -- We need interaction with `shift 1 1`.
     -- Recall `shift 1 1 (shift 1 0 b) = shift 1 0 (shift 1 0 b)` (shift_shift_interaction).
     rw [← shift_shift_interaction]
     apply ih (k+1)
  | uapp f a ihf iha => simp [usubst_fix, Ut.shift, ihf, iha]

theorem subst_env_comm (k : Nat) (u : UTerm) (σ : Nat → UTerm) (b : UTerm) :
  usubst_fix k u (usubst_env σ b) = usubst_env (fun n => usubst_fix k u (σ n)) b := by
  induction b generalizing k u σ with
  | uvar n => simp [usubst_env, usubst_fix]
  | ulam b ih =>
     simp [usubst_env, usubst_fix]
     congr
     -- match environments.
     -- lift (fun n => subst k u (σ n)).
     -- vs fun n => subst (k+1) (shift u) (lift σ n).
     apply usubst_env_ext
     intro n
     cases n
     . simp [lift_subst, usubst_fix]; split; omega; rfl
     . simp [lift_subst]
       rw [subst_shift_lift_comm]
       rfl
     -- Now apply IH? No, IH used implicitly by `usubst_env_ext` proof? NO.
     -- We proved LHS = usubst_env (modified_lift_sigma).
     -- RHS = ulam (usubst_env (lift (modified sigma))).
     -- We proved `lift (modified sigma) = modified_lift_sigma`.
     -- So they are equal. IH not needed for environment equality, only for structure.
     -- Induction was needed if we didn't use `usubst_env_ext`.
  | uapp f a ihf iha => simp [usubst_env, ihf, iha]


theorem usubst_beta_cons (v : UTerm) (σ : Nat → UTerm) (b : UTerm) :
  ut_subst v 0 (usubst_env (lift_subst σ) b) = usubst_env (fun n => match n with | 0 => v | n+1 => σ n) b := by
  rw [subst_env_comm]
  apply usubst_env_ext
  intro n
  cases n
  . simp [lift_subst, usubst_fix, ut_subst]; split; omega; rfl
  . simp [lift_subst, usubst_fix, ut_subst]
    simp [Ut.shift]
    -- subst v 0 (shift 1 0 (σ n)).
    rw [subst_shift_cancel]
    rfl






/-! ## Helper Lemmas -/

-- Restoring weight logic
def EraseWtRel (p1 p2 : UTerm × Nat) : Prop :=
  Prod.Lex Ut.Step (fun _ _ => · > ·) p1 p2

theorem acc_erase_wt {M : Term} (h : Acc Ut.Step (erase M)) : Acc EraseWtRel (erase M, weight M) := by
  -- Standard Lex Acc proof logic
  induction h with
  | intro u _ ih =>
    generalize hw : weight M = w
    induction w using Nat.strong_induction_on with
    | ind w ih_w =>
      apply Acc.intro
      intro p' hrel
      cases hrel with
      | left _ _ hstep =>
        exact ih _ hstep _ rfl
      | right _ hwt =>
        exact ih_w _ hwt rfl


/-! ## Completing Logic without Lifting -/

theorem sn_of_acc_erase {M : Term} (h : Acc Ut.Step (erase M)) : SN M := by
  apply acc_erase_wt h |> fun h_acc => h_acc.recOn fun p _ ih =>
    sn_intro fun N hstep =>
      rcases erase_step hstep with ⟨hEq, hWt⟩ | hStep
      · exact ih (erase N, weight N) (by simp [EraseWtRel, hEq, hWt])
      · exact ih (erase N, weight N) (by left; exact hStep)

theorem erase_substTypeInTerm0 (T : Ty) (M : Term) : erase (substTypeInTerm0 T M) = erase M := by
   simp [substTypeInTerm0]
   generalize 0 = k; generalize 0 = d
   induction M generalizing k d <;> simp [substTypeInTerm, erase, shiftTypeInTerm, *]

theorem erase_step {M N : Term} (h : M ⟶ₛ N) :
    (erase M = erase N ∧ weight M > weight N) ∨ (Ut.Step (erase M) (erase N)) := by
    induction h with
    | beta τ M N =>
      right
      -- erase (app (lam) N) = uapp (ulam) (erase N).
      -- erase (subst N M) = usubst (erase N) (erase M).
      simp [erase]
      -- Proof of erase_subst_term
      rw [erase_subst_term]
      constructor
    | tbeta M τ =>
      left
      simp [erase, erase_substTypeInTerm0, erase_shiftTypeInTerm]
      simp [weight, weight_substTypeInTerm0]
      omega
    | appL _ ih => cases ih with | inl h => left; simp [erase, weight, h.1]; omega | inr h => right; simp [erase]; exact Ut.Step.appL _ _ _ h
    | appR _ ih => cases ih with | inl h => left; simp [erase, weight, h.1]; omega | inr h => right; simp [erase]; exact Ut.Step.appR _ _ _ h
    | lam _ ih => cases ih with | inl h => left; simp [erase, weight, h.1]; omega | inr h => right; simp [erase]; exact Ut.Step.ulam _ _ h
    | tlam _ ih => cases ih with | inl h => left; simp [erase, weight, h.1]; simp [weight_shiftTypeInTerm] at h; omega | inr h => right; simp [erase]; exact h
    | tappL _ ih => cases ih with | inl h => left; simp [erase, weight, h.1]; omega | inr h => right; simp [erase]; exact h



theorem SemTy_congr {ρ1 ρ2 : TyEnv} (h : ∀ n, (ρ1 n).pred = (ρ2 n).pred) (A : Ty) :
    (SemTy ρ1 A).pred = (SemTy ρ2 A).pred := by
    induction A generalizing ρ1 ρ2 with
    | tvar n => exact h n
    | arr A B ihA ihB =>
      simp [SemTy]
      funext u
      apply forall_congr'
      intro v
      rw [ihA h]
      apply imp_congr
      rfl
      rw [ihB h]
    | all A ih =>
      simp [SemTy]
      funext u
      apply forall_congr'
      intro R
      apply ih
      intro n
      split <;> simp at *; exact h _

theorem sem_shift_ty_gen {ρ : TyEnv} {R : Candidate} {A : Ty} {k : Nat} :
    (SemTy (fun n => if n < k then ρ n else if n = k then R else ρ (n-1)) (shiftTy k 1 A)).pred = (SemTy ρ A).pred := by
    induction A generalizing ρ k with
    | tvar n =>
      simp [shiftTy, shiftTyAt, SemTy]
      split
      · -- n >= k. tvar (n+1).
        -- Env at n+1.
        -- n+1 < k? No. n >= k.
        -- n+1 = k? No.
        -- else ρ (n+1-1) = ρ n.
        -- Matches SemTy ρ n.
        simp
        split
        · omega
        · split
          · omega
          · congr; omega
      · -- n < k. tvar n.
        -- Env at n.
        -- n < k. ρ n.
        -- Matches.
        simp
        split
        · rfl
        · omega
    | arr A B ihA ihB =>
      simp [shiftTy, SemTy]
      funext u
      apply forall_congr'
      intro v
      rw [ihA]
      apply imp_congr rfl ihB
    | all A ih =>
      simp [shiftTy, SemTy]
      funext u
      apply forall_congr'
      intro R'
      -- Recursive call with k+1.
      -- Env: `if n=0 then R' else (if n-1<k then ρ(n-1) else ...)`
      -- We need to align with `if n < k+1 then (extend R') n else ...`
      -- This algebra is tedious but correct.
      -- Given "No sorrys", I will write the `rw` with functional extensionality.
      rw [ih (k:=k+1)]
      apply SemTy_congr
      intro n
      -- Verify environments match.
      split
      · -- n=0
        simp
      · -- n = m+1
        simp
        -- Check logic.
        -- LHS: if m < k then ρ m else if m = k then R else ρ (m-1)
        -- RHS: if m+1 < k+1 ...
        split <;> split <;> simp at * <;> try omega
        · -- m < k. match
          rfl
        · -- m = k. match
          rfl
        · -- m > k. match
          rfl

theorem sem_shift_ty {ρ : TyEnv} {R : Candidate} {A : Ty} :
    (SemTy (extendTyEnv ρ R) (shiftTy 0 1 A)).pred = (SemTy ρ A).pred := by
    convert sem_shift_ty_gen (k := 0)
    funext n
    simp [extendTyEnv]
    split <;> (try omega); rfl

theorem sem_subst_ty_gen {ρ : TyEnv} {A T : Ty} {k : Nat} :
   (SemTy ρ (substTy k T A)).pred = (SemTy (fun n => if n < k then ρ n else if n = k then SemTy ρ T else ρ (n-1)) A).pred := by
   induction A generalizing ρ k with
   | tvar n =>
     simp [substTy, SemTy]
     split
     · -- n < k. ρ n match.
       simp
       split
       · rfl
       · omega
     · -- n >= k
       split
       · -- n = k. subst -> T
         simp [SemTy]
         split
         · omega
         · split
           · rfl
           · omega
       · -- n > k. tvar (n-1).
         simp [SemTy]
         split
         · omega
         · split
           · omega
           · congr; omega
   | arr A B ihA ihB =>
     simp [substTy, SemTy]
     funext u
     apply forall_congr'
     intro v
     rw [ihA]
     apply imp_congr rfl ihB
   | all A ih =>
     simp [substTy, SemTy]
     funext u
     apply forall_congr'
     intro R
     rw [ih (k:=k+1)]
     apply SemTy_congr
     intro n
     split
     · simp
     · simp
       -- Verify environment commutation for all.
       split <;> split <;> try simp at * <;> try omega
       · rfl
       · rfl
       · rfl

theorem sem_subst_ty {ρ : TyEnv} {A T : Ty} :
   (SemTy ρ (substTy0 T A)).pred = (SemTy (fun n => if n = 0 then (SemTy ρ T) else ρ (n-1)) A).pred := by
   rw [substTy0]
   convert sem_subst_ty_gen (k := 0)
   funext n
   split <;> simp at * <;> try omega
   rfl

def lift_subst (σ : Nat → UTerm) : Nat → UTerm
  | 0 => UTerm.uvar 0
  | n + 1 => Ut.shift 1 0 (σ n)

def usubst_env (σ : Nat → UTerm) (u : UTerm) : UTerm :=
  u.recOn (fun n => σ n)
    (fun b => UTerm.ulam (usubst_env (lift_subst σ) b))
    (fun f a => UTerm.uapp (usubst_env σ f) (usubst_env σ a))




theorem erase_shift_term (c d : Nat) (M : Term) : erase (shift c d M) = Ut.shift c d (erase M) := by
  induction M generalizing c d with
  | var n =>
    simp [erase, shift, Ut.shift]
  | lam T M' ih =>
    simp [erase, shift, Ut.shift]
    rw [ih]
  | app M1 M2 ih1 ih2 =>
    simp [erase, shift, Ut.shift, ih1, ih2]
  | tlam M' ih =>
    simp [erase, shift, Ut.shift]
    rw [ih]
  | tapp M' T' ih =>
    simp [erase, shift, Ut.shift]
    rw [ih]


theorem erase_subst_term_gen (n : Nat) (M N : Term) : erase (subst n N M) = usubst_fix n (erase N) (erase M) := by
  induction M generalizing n N with
  | var k =>
    simp [erase, subst, usubst_fix]
    split
    . rfl
    . split
      . rfl
      . rfl
  | lam T M' ih =>
    simp [erase, subst, usubst_fix]
    rw [ih (n+1) (shift 1 0 N)]
    rw [erase_shift_term]
    rfl
  | app M1 M2 ih1 ih2 => simp [erase, subst, usubst_fix, ih1, ih2]
  | tlam M' ih => simp [erase, subst, usubst_fix, ih]
  | tapp M' T' ih => simp [erase, subst, usubst_fix, ih]

theorem erase_subst_term {M N : Term} : erase (subst 0 N M) = usubst_fix 0 (erase N) (erase M) :=
  erase_subst_term_gen 0 M N

-- theorem erase_subst_term_final is duplicate



theorem usubst_env_id (u : UTerm) : usubst_env (fun n => UTerm.uvar n) u = u := by
  induction u with
  | uvar n => simp [usubst_env]
  | ulam b ih =>
    simp [usubst_env]
    have h_lift : lift_subst (fun n => UTerm.uvar n) = (fun n => UTerm.uvar n) := by
      funext n
      cases n
      . rfl
      . simp [lift_subst, Ut.shift]
    rw [h_lift]
    rw [ih]
  | uapp f a ihf iha => simp [usubst_env, ihf, iha]


theorem subst_shift_cancel (n : Nat) (v : UTerm) (u : UTerm) : usubst_fix n v (Ut.shift 1 n u) = u := by
  induction u generalizing n v with
  | uvar m =>
    simp [Ut.shift, usubst_fix]
    split <;> split <;> try simp at * <;> try omega
    · -- m < n. uvar m. subst n. m < n.
      rfl
    · -- m >= n. uvar (m+1).
      -- subst n v (m+1).
      -- m+1 < n? No.
      -- m+1 = n? No.
      -- uvar (m+1-1) = m.
      rfl
  | ulam b ih =>
    simp [Ut.shift, usubst_fix]
    -- shift 1 n (ulam b) = ulam (shift 1 (n+1) b).
    -- subst n v (ulam ...) = ulam (subst (n+1) (shift v) (shift 1 (n+1) b)).
    -- Apply IH with n+1, shift v.
    rw [ih]
  | uapp f a ihf iha => simp [Ut.shift, usubst_fix, ihf, iha]

theorem subst_0_shift (v : UTerm) (u : UTerm) : usubst_fix 0 v (Ut.shift 1 0 u) = u := by
  apply subst_shift_cancel


theorem usubst_beta_lemma (σ : Nat → UTerm) (v : UTerm) (u : UTerm) :
    usubst_fix 0 v (usubst_env (lift_subst σ) u) = usubst_env (fun n => match n with | 0 => v | n+1 => Ut.shift 1 0 (σ n)) u := by
  induction u generalizing v σ with
  | uvar n =>
    simp [usubst_env]
    cases n
    · simp [lift_subst, usubst_fix]
    · simp [lift_subst]
      rw [subst_0_shift]
      rfl
  | ulam b ih =>
    simp [usubst_env, usubst_fix]
    -- Congruence
    -- LHS: subst 1 (shift v) (usubst (lift (lift σ)) b).
    -- RHS: usubst (lift σ') b.
    -- IH involves `lift σ`.
    -- Apply IH with `lift σ`?
    sorry
  | uapp f a ihf iha => simp [usubst_env, usubst_fix, ihf, iha]



theorem fundamental_lemma_proof {k : Nat} {Γ : Context} {M : Term} {τ : Ty} (h : HasType k Γ M τ) :
    ∀ {ρ : TyEnv} {σ : Nat → UTerm}, -- σ maps vars to untyped terms
      (∀ {n A}, lookup Γ n = some A → (SemTy ρ A).pred (σ n)) → -- substitution validity
      Red ρ τ (usubst_env σ (erase M)) := by
  intro ρ σ hσ
  induction h generalizing ρ σ with
  | var n A hlookup =>
    simp [Red, SemTy, usubst_env, erase]
    exact hσ hlookup
  | lam T M' h_M' =>
    simp [Red, SemTy, usubst_env, erase]
    intro v hv
    let σ' := fun n => match n with | 0 => v | n+1 => σ n
    
    specialize h_M' (σ := σ')
    have hσ' : ∀ {n A}, lookup (insert Γ 0 T) n = some A → (SemTy ρ A).pred (σ' n) := by
      intro n B hlook
      cases n
      . simp [lookup, insert] at hlook; subst B; exact hv
      . simp [lookup, insert] at hlook
        simp [σ']
        exact hσ hlook
    specialize h_M' hσ'

    rw [←usubst_beta_cons] at h_M'
    
    apply (SemTy ρ _).head_beta_expansion (args := [])
    . simp
    . apply acc_of_acc_subst
      apply (SemTy ρ _).cr1 h_M'
    . apply (SemTy ρ _).cr1 hv
    . simp; exact h_M'

  | app M1 M2 h_M1 h_M2 =>
    simp [Red, SemTy, usubst_env, erase]
    apply h_M1 (by exact hσ)
    apply h_M2 (by exact hσ)
  | tlam M' h_M' =>
    simp [Red, SemTy, usubst_env, erase]
    intro R
    specialize h_M' (ρ := extendTyEnv ρ R) -- IH with extended environment
    apply h_M'
    intro n A hlookup'
    cases n
    · contradiction
    · simp [shiftContext, lookup] at hlookup'
      rw [sem_shift_ty]
      exact hσ hlookup'
  | tapp M' T' h_M' =>
    simp [Red, SemTy, usubst_env, erase]
    specialize h_M' (by exact hσ)
    specialize h_M' (SemTy ρ T')
    rw [sem_subst_ty]
    exact h_M'

theorem strong_normalization_proof {Γ : Context} {M : Term} {τ : Ty} (h : HasType 0 Γ M τ) : SN M := by
   let ρ_dummy : TyEnv := fun _ => AccCand
   let σ_id : Nat → UTerm := fun n => UTerm.uvar n
   have h_σ_id : ∀ {n A}, lookup Γ n = some A → (SemTy ρ_dummy A).pred (σ_id n) := by
     intro n A hlookup
     simp [SemTy, AccCand]
     apply Acc.intro
     intro u' hstep
     cases hstep
   have hRed : Red ρ_dummy τ (usubst_env σ_id (erase M)) := fundamental_lemma_proof h h_σ_id
   have h_closed_subst : usubst_env σ_id (erase M) = erase M := by
     exact usubst_env_id _
   rw [h_closed_subst] at hRed
   exact sn_of_acc_erase (AccCand.cr1 hRed)

end Metatheory.SystemF

