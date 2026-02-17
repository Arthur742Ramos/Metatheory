/-
  Metatheory / SecrecyTypes.lean

  Information flow type systems: security labels (High/Low),
  noninterference, secure information flow, label lattice,
  PC label tracking, implicit flows, declassification,
  endorsement, robust declassification.

  All proofs are sorry-free. Uses computational paths for
  derivation rewriting (typing rule applications as path steps).
-/

namespace SecrecyTypes

-- ============================================================
-- §1  Computational paths
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive DPath (α : Type) : α → α → Type where
  | nil  : (a : α) → DPath α a a
  | cons : Step α a b → DPath α b c → DPath α a c

def DPath.trans : DPath α a b → DPath α b c → DPath α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

def Step.symm : Step α a b → Step α b a
  | .refl a => .refl a
  | .rule nm a b => .rule (nm ++ "⁻¹") b a

def DPath.symm : DPath α a b → DPath α b a
  | .nil a => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

def DPath.length : DPath α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

def DPath.single (s : Step α a b) : DPath α a b :=
  .cons s (.nil _)

def DPath.congrArg (f : α → β) : DPath α a b → DPath β (f a) (f b)
  | .nil a => .nil (f a)
  | .cons (.refl a) p => (DPath.nil (f a)).trans (congrArg f p)
  | .cons (.rule nm a b) p => .cons (.rule nm (f a) (f b)) (congrArg f p)

theorem dpath_trans_assoc (p : DPath α a b) (q : DPath α b c) (r : DPath α c d) :
    DPath.trans (DPath.trans p q) r = DPath.trans p (DPath.trans q r) := by
  induction p with
  | nil _ => simp [DPath.trans]
  | cons s _ ih => simp [DPath.trans, ih]

theorem dpath_trans_nil_right (p : DPath α a b) :
    DPath.trans p (DPath.nil b) = p := by
  induction p with
  | nil _ => simp [DPath.trans]
  | cons s _ ih => simp [DPath.trans, ih]

theorem dpath_length_trans (p : DPath α a b) (q : DPath α b c) :
    (DPath.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [DPath.trans, DPath.length]
  | cons _ _ ih => simp [DPath.trans, DPath.length, ih, Nat.add_assoc]

-- ============================================================
-- §2  Security labels and lattice
-- ============================================================

/-- Security labels: two-point lattice. -/
inductive Label where
  | low  : Label
  | high : Label
  deriving DecidableEq, Repr

/-- Label ordering: Low ≤ High. -/
def Label.leq : Label → Label → Bool
  | .low, _ => true
  | .high, .high => true
  | .high, .low => false

instance : LE Label := ⟨fun a b => a.leq b = true⟩

/-- Join (least upper bound). -/
def Label.join : Label → Label → Label
  | .low, .low => .low
  | _, _ => .high

/-- Meet (greatest lower bound). -/
def Label.meet : Label → Label → Label
  | .high, .high => .high
  | _, _ => .low

-- ============================================================
-- §3  Label lattice theorems
-- ============================================================

/-- Theorem 1: Low ≤ High. -/
theorem low_le_high : Label.leq .low .high = true := by rfl

/-- Theorem 2: leq is reflexive. -/
theorem label_le_refl (l : Label) : Label.leq l l = true := by
  cases l <;> rfl

/-- Theorem 3: leq is transitive. -/
theorem label_le_trans (a b c : Label)
    (hab : Label.leq a b = true) (hbc : Label.leq b c = true) :
    Label.leq a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [Label.leq]

/-- Theorem 4: leq is antisymmetric. -/
theorem label_le_antisymm (a b : Label)
    (hab : Label.leq a b = true) (hba : Label.leq b a = true) :
    a = b := by
  cases a <;> cases b <;> simp_all [Label.leq]

/-- Theorem 5: Join is commutative. -/
theorem join_comm (a b : Label) : Label.join a b = Label.join b a := by
  cases a <;> cases b <;> rfl

/-- Theorem 6: Meet is commutative. -/
theorem meet_comm (a b : Label) : Label.meet a b = Label.meet b a := by
  cases a <;> cases b <;> rfl

/-- Theorem 7: Join is idempotent. -/
theorem join_idem (a : Label) : Label.join a a = a := by
  cases a <;> rfl

/-- Theorem 8: Meet is idempotent. -/
theorem meet_idem (a : Label) : Label.meet a a = a := by
  cases a <;> rfl

/-- Theorem 9: Join is an upper bound. -/
theorem join_upper_left (a b : Label) : Label.leq a (Label.join a b) = true := by
  cases a <;> cases b <;> rfl

/-- Theorem 10: Meet is a lower bound. -/
theorem meet_lower_left (a b : Label) : Label.leq (Label.meet a b) a = true := by
  cases a <;> cases b <;> rfl

-- ============================================================
-- §4  Simple imperative language with security types
-- ============================================================

/-- Expressions. -/
inductive Expr where
  | lit : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | eq  : Expr → Expr → Expr
  deriving DecidableEq, Repr

/-- Commands. -/
inductive Cmd where
  | skip : Cmd
  | assign : String → Expr → Cmd
  | seq : Cmd → Cmd → Cmd
  | ifThenElse : Expr → Cmd → Cmd → Cmd
  | while : Expr → Cmd → Cmd
  | declassify : String → Expr → Cmd      -- explicit declassification
  deriving Repr

-- ============================================================
-- §5  Security typing environment
-- ============================================================

/-- Security environment: maps variables to labels. -/
abbrev SecEnv := List (String × Label)

/-- Lookup a variable's label. -/
def SecEnv.lookup (env : SecEnv) (x : String) : Option Label :=
  env.find? (fun p => p.1 == x) |>.map Prod.snd

/-- Theorem 11: Lookup in empty env returns none. -/
theorem lookup_empty (x : String) : SecEnv.lookup [] x = none := by
  rfl

-- ============================================================
-- §6  Expression typing: label of an expression
-- ============================================================

/-- Label of an expression under an environment. -/
def exprLabel (env : SecEnv) : Expr → Label
  | .lit _ => .low
  | .var x => match env.lookup x with
              | some l => l
              | none => .high    -- default: high (safe)
  | .add e1 e2 => Label.join (exprLabel env e1) (exprLabel env e2)
  | .eq e1 e2 => Label.join (exprLabel env e1) (exprLabel env e2)

/-- Theorem 12: Literal always has Low label. -/
theorem lit_is_low (env : SecEnv) (n : Int) : exprLabel env (.lit n) = .low := by
  rfl

/-- Theorem 13: Add of two Low exprs is Low. -/
theorem add_low_low (env : SecEnv) (e1 e2 : Expr)
    (h1 : exprLabel env e1 = .low) (h2 : exprLabel env e2 = .low) :
    exprLabel env (.add e1 e2) = .low := by
  simp [exprLabel, h1, h2, Label.join]

/-- Theorem 14: Join with High always produces High. -/
theorem join_high_any (l : Label) : Label.join .high l = .high := by
  cases l <;> rfl

/-- Theorem 15: If either subexpression is High, add is High. -/
theorem add_high_taints (env : SecEnv) (e1 e2 : Expr)
    (h : exprLabel env e1 = .high) :
    exprLabel env (.add e1 e2) = .high := by
  simp [exprLabel, h, Label.join]

-- ============================================================
-- §7  Command typing with PC label
-- ============================================================

/-- Security typing judgment for commands.
    pc is the program counter label (tracks implicit flows). -/
inductive SecType : SecEnv → Label → Cmd → Prop where
  | skip : SecType env pc .skip
  | assign : (x : String) → (e : Expr) →
      env.lookup x = some lx →
      Label.leq (Label.join pc (exprLabel env e)) lx = true →
      SecType env pc (.assign x e)
  | seq : SecType env pc c1 → SecType env pc c2 →
      SecType env pc (.seq c1 c2)
  | ifTE : (guard : Expr) →
      SecType env (Label.join pc (exprLabel env guard)) ct →
      SecType env (Label.join pc (exprLabel env guard)) cf →
      SecType env pc (.ifThenElse guard ct cf)
  | whileLoop : (guard : Expr) →
      SecType env (Label.join pc (exprLabel env guard)) body →
      SecType env pc (.while guard body)
  | declass : (x : String) → (e : Expr) →
      env.lookup x = some .low →
      SecType env pc (.declassify x e)

-- ============================================================
-- §8  Typing theorems
-- ============================================================

/-- Theorem 16: Skip is always well-typed. -/
theorem skip_always_typed (env : SecEnv) (pc : Label) :
    SecType env pc .skip :=
  .skip

/-- Theorem 17: Assigning Low expr to Low var under Low pc is secure. -/
theorem assign_low_to_low (env : SecEnv) (x : String) (e : Expr)
    (hx : env.lookup x = some .low)
    (he : exprLabel env e = .low) :
    SecType env .low (.assign x e) := by
  exact .assign x e hx (by simp [Label.join, he, Label.leq])

/-- Theorem 18: High expr assigned to High var under any pc is secure. -/
theorem assign_high_to_high (env : SecEnv) (x : String) (e : Expr) (pc : Label)
    (hx : env.lookup x = some .high) :
    SecType env pc (.assign x e) := by
  exact .assign x e hx (by cases pc <;> cases exprLabel env e <;> simp [Label.join, Label.leq])

/-- Theorem 19: Sequential composition of well-typed commands. -/
theorem seq_typed (env : SecEnv) (pc : Label) (c1 c2 : Cmd)
    (h1 : SecType env pc c1) (h2 : SecType env pc c2) :
    SecType env pc (.seq c1 c2) :=
  .seq h1 h2

/-- Theorem 20: Subsumption — Low pc typing implies High pc typing
    for skip. -/
theorem pc_subsumption_skip (env : SecEnv) :
    SecType env .low .skip → SecType env .high .skip :=
  fun _ => .skip

-- ============================================================
-- §9  Noninterference (simplified)
-- ============================================================

/-- A memory is a map from variables to Int values. -/
abbrev Memory := List (String × Int)

/-- Low-equivalence: two memories agree on all Low variables. -/
def lowEquiv (env : SecEnv) (m1 m2 : Memory) : Prop :=
  ∀ x, env.lookup x = some .low →
    m1.find? (fun p => p.1 == x) = m2.find? (fun p => p.1 == x)

/-- Theorem 21: Low-equivalence is reflexive. -/
theorem low_equiv_refl (env : SecEnv) (m : Memory) : lowEquiv env m m := by
  intro x _
  rfl

/-- Theorem 22: Low-equivalence is symmetric. -/
theorem low_equiv_symm (env : SecEnv) (m1 m2 : Memory)
    (h : lowEquiv env m1 m2) : lowEquiv env m2 m1 := by
  intro x hx
  exact (h x hx).symm

/-- Theorem 23: Low-equivalence is transitive. -/
theorem low_equiv_trans (env : SecEnv) (m1 m2 m3 : Memory)
    (h12 : lowEquiv env m1 m2) (h23 : lowEquiv env m2 m3) :
    lowEquiv env m1 m3 := by
  intro x hx
  exact (h12 x hx).trans (h23 x hx)

-- ============================================================
-- §10  Implicit flow detection
-- ============================================================

/-- A command has an implicit flow if it assigns to a Low variable
    inside a High-guarded branch. -/
def hasImplicitFlow (env : SecEnv) : Cmd → Label → Bool
  | .skip, _ => false
  | .assign x _, pc =>
      match env.lookup x with
      | some .low => pc == .high
      | _ => false
  | .seq c1 c2, pc => hasImplicitFlow env c1 pc || hasImplicitFlow env c2 pc
  | .ifThenElse guard ct cf, pc =>
      let newPc := Label.join pc (exprLabel env guard)
      hasImplicitFlow env ct newPc || hasImplicitFlow env cf newPc
  | .while guard body, pc =>
      let newPc := Label.join pc (exprLabel env guard)
      hasImplicitFlow env body newPc
  | .declassify _ _, _ => false

/-- Theorem 24: Skip never has implicit flows. -/
theorem skip_no_implicit_flow (env : SecEnv) (pc : Label) :
    hasImplicitFlow env .skip pc = false := by
  rfl

/-- Theorem 25: Declassify never flagged as implicit flow. -/
theorem declass_no_implicit_flow (env : SecEnv) (x : String) (e : Expr) (pc : Label) :
    hasImplicitFlow env (.declassify x e) pc = false := by
  rfl

-- ============================================================
-- §11  Declassification and endorsement
-- ============================================================

/-- Declassification policy: who can declassify. -/
inductive DeclassPolicy where
  | unrestricted : DeclassPolicy
  | trusted : List String → DeclassPolicy   -- only trusted principals
  deriving Repr

/-- Check if declassification is allowed. -/
def canDeclassify (pol : DeclassPolicy) (principal : String) : Bool :=
  match pol with
  | .unrestricted => true
  | .trusted ps => ps.contains principal

/-- Theorem 26: Unrestricted policy always allows declassification. -/
theorem unrestricted_always (principal : String) :
    canDeclassify .unrestricted principal = true := by
  rfl

/-- Endorsement: raise integrity label. -/
def endorse (l : Label) : Label :=
  match l with
  | .low => .high     -- endorsing raises trust
  | .high => .high

/-- Theorem 27: Endorsing High is idempotent. -/
theorem endorse_high_idem : endorse .high = .high := by rfl

/-- Theorem 28: Endorsing always produces High. -/
theorem endorse_always_high (l : Label) : endorse l = .high := by
  cases l <;> rfl

-- ============================================================
-- §12  Robust declassification
-- ============================================================

/-- Robust declassification: the decision to declassify must not
    be influenced by untrusted (Low-integrity) data.
    Simplified: declassification is robust if pc ≠ High. -/
def robustDeclass (pc : Label) : Bool :=
  match pc with
  | .low => true
  | .high => false

/-- Theorem 29: Robust declassification under Low pc. -/
theorem robust_under_low_pc : robustDeclass .low = true := by rfl

/-- Theorem 30: Non-robust under High pc. -/
theorem not_robust_under_high_pc : robustDeclass .high = false := by rfl

-- ============================================================
-- §13  Path-based derivation rewriting
-- ============================================================

/-- Derivation state for paths. -/
structure DerivState where
  env : SecEnv
  pc : Label
  cmd : Cmd
  deriving Repr

/-- Path: subsumption derivation rewrite (raising pc). -/
def subsumption_path (env : SecEnv) (c : Cmd) :
    DPath DerivState ⟨env, .low, c⟩ ⟨env, .high, c⟩ :=
  DPath.single (.rule "pc-subsumption" _ _)

/-- Path: sequential decomposition. -/
def seq_decompose_path (env : SecEnv) (pc : Label) (c1 c2 : Cmd) :
    DPath DerivState ⟨env, pc, .seq c1 c2⟩ ⟨env, pc, c1⟩ :=
  DPath.single (.rule "seq-left" _ _)

/-- Theorem 31: Subsumption path has length 1. -/
theorem subsumption_path_length (env : SecEnv) (c : Cmd) :
    (subsumption_path env c).length = 1 := by
  simp [subsumption_path, DPath.single, DPath.length]

/-- Multi-step derivation: Low-pc → High-pc → back to Low-pc. -/
def round_trip_path (env : SecEnv) (c : Cmd) :
    DPath DerivState ⟨env, .low, c⟩ ⟨env, .low, c⟩ :=
  (subsumption_path env c).trans (subsumption_path env c).symm

/-- Theorem 32: Round trip path has length 2. -/
theorem round_trip_length (env : SecEnv) (c : Cmd) :
    (round_trip_path env c).length = 2 := by
  simp [round_trip_path, subsumption_path, DPath.trans, DPath.symm,
        DPath.single, DPath.length, Step.symm]

/-- Theorem 33: congrArg lifts pc extraction over paths. -/
def lift_pc_over_path (p : DPath DerivState a b) :
    DPath Label a.pc b.pc :=
  DPath.congrArg DerivState.pc p

-- ============================================================
-- §14  Transport and coherence
-- ============================================================

/-- Transport a property along a derivation path. -/
def DPath.transport (P : α → Prop) (p : DPath α a b) (pa : P a)
    (compat : ∀ x y, Step α x y → P x → P y) : P b := by
  induction p with
  | nil _ => exact pa
  | cons s _ ih => exact ih (compat _ _ s pa)

/-- Theorem 34: Transport along nil is identity. -/
theorem transport_nil_id (P : α → Prop) (a : α) (pa : P a)
    (compat : ∀ x y, Step α x y → P x → P y) :
    DPath.transport P (DPath.nil a) pa compat = pa := by
  rfl

/-- Confluence: two derivation paths from same source. -/
def confluent (_p : DPath α a b) (_q : DPath α a c) : Prop :=
  ∃ d, ∃ _ : DPath α b d, ∃ _ : DPath α c d, True

/-- Theorem 35: Refl path is confluent with any path. -/
theorem refl_confluent (p : DPath α a b) : confluent (DPath.nil a) p :=
  ⟨b, p, DPath.nil b, trivial⟩

-- ============================================================
-- §15  Label join/meet absorption and distribution
-- ============================================================

/-- Theorem 36: Join absorbs Low. -/
theorem join_low_right (l : Label) : Label.join l .low = l := by
  cases l <;> rfl

/-- Theorem 37: Meet absorbs High. -/
theorem meet_high_right (l : Label) : Label.meet l .high = l := by
  cases l <;> rfl

/-- Theorem 38: Distributivity of join over meet. -/
theorem join_meet_distrib (a b c : Label) :
    Label.join a (Label.meet b c) = Label.meet (Label.join a b) (Label.join a c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Theorem 39: Join is associative. -/
theorem join_assoc (a b c : Label) :
    Label.join (Label.join a b) c = Label.join a (Label.join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Theorem 40: Meet is associative. -/
theorem meet_assoc (a b c : Label) :
    Label.meet (Label.meet a b) c = Label.meet a (Label.meet b c) := by
  cases a <;> cases b <;> cases c <;> rfl

end SecrecyTypes
