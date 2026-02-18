/-
  Armada 638: Binary Session Types
  Core definitions: session type syntax, duality, properties.
-/

-- Base types carried in messages
inductive BaseType where
  | unit : BaseType
  | nat  : BaseType
  | bool : BaseType
  deriving DecidableEq, Repr

-- Binary session types
inductive SType where
  | send   : BaseType → SType → SType
  | recv   : BaseType → SType → SType
  | choice : SType → SType → SType
  | branch : SType → SType → SType
  | done   : SType
  deriving DecidableEq, Repr

-- Duality
def SType.dual : SType → SType
  | .send t s    => .recv t s.dual
  | .recv t s    => .send t s.dual
  | .choice a b  => .branch a.dual b.dual
  | .branch a b  => .choice a.dual b.dual
  | .done        => .done

-- ========== DUALITY THEOREMS ==========

theorem dual_send (t : BaseType) (s : SType) :
    (SType.send t s).dual = .recv t s.dual := rfl

theorem dual_recv (t : BaseType) (s : SType) :
    (SType.recv t s).dual = .send t s.dual := rfl

theorem dual_choice (a b : SType) :
    (SType.choice a b).dual = .branch a.dual b.dual := rfl

theorem dual_branch (a b : SType) :
    (SType.branch a b).dual = .choice a.dual b.dual := rfl

theorem dual_done : SType.done.dual = .done := rfl

theorem dual_involutive (s : SType) : s.dual.dual = s := by
  induction s with
  | send t s ih => simp [SType.dual, ih]
  | recv t s ih => simp [SType.dual, ih]
  | choice a b iha ihb => simp [SType.dual, iha, ihb]
  | branch a b iha ihb => simp [SType.dual, iha, ihb]
  | done => rfl

theorem dual_injective (s1 s2 : SType) (h : s1.dual = s2.dual) : s1 = s2 := by
  have h1 := dual_involutive s1
  have h2 := dual_involutive s2
  rw [← h1, ← h2, h]

theorem done_self_dual : SType.done.dual = .done := rfl

-- ========== SIZE ==========

def SType.size : SType → Nat
  | .send _ s    => 1 + s.size
  | .recv _ s    => 1 + s.size
  | .choice a b  => 1 + a.size + b.size
  | .branch a b  => 1 + a.size + b.size
  | .done        => 0

theorem dual_preserves_size (s : SType) : s.dual.size = s.size := by
  induction s with
  | send t s ih => simp [SType.dual, SType.size, ih]
  | recv t s ih => simp [SType.dual, SType.size, ih]
  | choice a b iha ihb => simp [SType.dual, SType.size, iha, ihb]
  | branch a b iha ihb => simp [SType.dual, SType.size, iha, ihb]
  | done => rfl

-- ========== DEPTH ==========

def SType.depth : SType → Nat
  | .send _ s    => 1 + s.depth
  | .recv _ s    => 1 + s.depth
  | .choice a b  => 1 + max a.depth b.depth
  | .branch a b  => 1 + max a.depth b.depth
  | .done        => 0

theorem dual_preserves_depth (s : SType) : s.dual.depth = s.depth := by
  induction s with
  | send t s ih => simp [SType.dual, SType.depth, ih]
  | recv t s ih => simp [SType.dual, SType.depth, ih]
  | choice a b iha ihb => simp [SType.dual, SType.depth, iha, ihb]
  | branch a b iha ihb => simp [SType.dual, SType.depth, iha, ihb]
  | done => rfl

-- ========== COMPLETED ==========

def SType.completed : SType → Bool
  | .done => true
  | _     => false

theorem completed_done : SType.done.completed = true := rfl
theorem completed_send (t s) : (SType.send t s).completed = false := rfl
theorem completed_recv (t s) : (SType.recv t s).completed = false := rfl

theorem completed_dual (s : SType) : s.dual.completed = s.completed := by
  cases s <;> simp [SType.dual, SType.completed]

-- ========== ACTIONS ==========

inductive Action where
  | snd : BaseType → Action
  | rcv : BaseType → Action
  | selL : Action
  | selR : Action
  | bra  : Action
  deriving DecidableEq, Repr

def Action.complement : Action → Action
  | .snd t => .rcv t
  | .rcv t => .snd t
  | .selL  => .bra
  | .selR  => .bra
  | .bra   => .selL

theorem complement_snd_rcv (t : BaseType) :
    (Action.snd t).complement = .rcv t := rfl

theorem complement_rcv_snd (t : BaseType) :
    (Action.rcv t).complement = .snd t := rfl

theorem complement_snd_invol (t : BaseType) :
    (Action.snd t).complement.complement = .snd t := rfl

theorem complement_rcv_invol (t : BaseType) :
    (Action.rcv t).complement.complement = .rcv t := rfl

-- ========== TRANSITIONS ==========

inductive Step : SType → Action → SType → Prop where
  | stepSend    : ∀ t s, Step (.send t s) (.snd t) s
  | stepRecv    : ∀ t s, Step (.recv t s) (.rcv t) s
  | stepChoiceL : ∀ a b, Step (.choice a b) .selL a
  | stepChoiceR : ∀ a b, Step (.choice a b) .selR b
  | stepBranchL : ∀ a b, Step (.branch a b) .bra a
  | stepBranchR : ∀ a b, Step (.branch a b) .bra b

theorem done_no_step (act : Action) (s' : SType) : ¬ Step .done act s' := by
  intro h; cases h

theorem step_send_det (t : BaseType) (s s1 s2 : SType) (a : Action)
    (h1 : Step (.send t s) a s1) (h2 : Step (.send t s) a s2) : s1 = s2 := by
  cases h1; cases h2; rfl

theorem step_recv_det (t : BaseType) (s s1 s2 : SType) (a : Action)
    (h1 : Step (.recv t s) a s1) (h2 : Step (.recv t s) a s2) : s1 = s2 := by
  cases h1; cases h2; rfl

-- Dual steps: if s steps with send, dual s steps with recv
theorem dual_step_send (t : BaseType) (s : SType) :
    Step (SType.dual (.send t s)) (.rcv t) (SType.dual s) :=
  Step.stepRecv t (SType.dual s)

theorem dual_step_recv (t : BaseType) (s : SType) :
    Step (SType.dual (.recv t s)) (.snd t) (SType.dual s) :=
  Step.stepSend t (SType.dual s)

theorem dual_step_choiceL (a b : SType) :
    Step (SType.dual (.choice a b)) .bra (SType.dual a) :=
  Step.stepBranchL (SType.dual a) (SType.dual b)

theorem dual_step_choiceR (a b : SType) :
    Step (SType.dual (.choice a b)) .bra (SType.dual b) :=
  Step.stepBranchR (SType.dual a) (SType.dual b)

-- Progress: non-done can step
theorem progress (s : SType) (h : s ≠ .done) : ∃ a s', Step s a s' := by
  cases s with
  | send t s => exact ⟨.snd t, s, Step.stepSend t s⟩
  | recv t s => exact ⟨.rcv t, s, Step.stepRecv t s⟩
  | choice a b => exact ⟨.selL, a, Step.stepChoiceL a b⟩
  | branch a b => exact ⟨.bra, a, Step.stepBranchL a b⟩
  | done => exact absurd rfl h

-- ========== COMPATIBILITY ==========

def compatible (s1 s2 : SType) : Prop := s2 = s1.dual

theorem compatible_sym (s1 s2 : SType) (h : compatible s1 s2) : compatible s2 s1 := by
  unfold compatible at *; rw [h, dual_involutive]

theorem compatible_done : compatible .done .done := by
  unfold compatible; rfl

theorem compatible_send_recv (t : BaseType) (s : SType) :
    compatible (.send t s) (.recv t s.dual) := by
  unfold compatible; rfl

theorem compatible_recv_send (t : BaseType) (s : SType) :
    compatible (.recv t s) (.send t s.dual) := by
  unfold compatible; rfl

theorem compatible_equal_depth (s1 s2 : SType) (h : compatible s1 s2) :
    s1.depth = s2.depth := by
  unfold compatible at h; rw [h, dual_preserves_depth]

theorem compatible_equal_size (s1 s2 : SType) (h : compatible s1 s2) :
    s1.size = s2.size := by
  unfold compatible at h; rw [h, dual_preserves_size]

-- ========== CONTEXT ==========

abbrev Ctx := List (Nat × SType)

def Ctx.lookup : Ctx → Nat → Option SType
  | [], _ => none
  | (n, s) :: rest, m => if n = m then some s else Ctx.lookup rest m

def Ctx.update : Ctx → Nat → SType → Ctx
  | [], n, s => [(n, s)]
  | (m, t) :: rest, n, s => if m = n then (n, s) :: rest else (m, t) :: Ctx.update rest n s

def Ctx.allDone : Ctx → Bool
  | [] => true
  | (_, s) :: rest => s.completed && Ctx.allDone rest

theorem ctx_nil_allDone : Ctx.allDone [] = true := rfl
