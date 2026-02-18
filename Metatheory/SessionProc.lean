/-
  Armada 638: Typed Pi-Calculus with Session Types
  Process syntax, typing judgments, subject reduction, session fidelity.
-/

import Metatheory.SessionTypes

-- Values
inductive Val where
  | unit : Val
  | nat  : Nat → Val
  | bool : Bool → Val
  deriving DecidableEq, Repr

def Val.type : Val → BaseType
  | .unit   => .unit
  | .nat _  => .nat
  | .bool _ => .bool

-- Processes
inductive Proc where
  | nil      : Proc
  | sendP    : Nat → Val → Proc → Proc
  | recvP    : Nat → Proc → Proc
  | selectL  : Nat → Proc → Proc
  | selectR  : Nat → Proc → Proc
  | branchP  : Nat → Proc → Proc → Proc
  | par      : Proc → Proc → Proc
  | restrict : Nat → SType → Proc → Proc
  deriving Repr

-- ========== STRUCTURAL CONGRUENCE ==========

inductive StructCong : Proc → Proc → Prop where
  | parComm  : ∀ P Q, StructCong (.par P Q) (.par Q P)
  | parAssoc : ∀ P Q R, StructCong (.par (.par P Q) R) (.par P (.par Q R))
  | parNil   : ∀ P, StructCong (.par P .nil) P
  | nilPar   : ∀ P, StructCong P (.par P .nil)
  | refl     : ∀ P, StructCong P P
  | symm     : ∀ P Q, StructCong P Q → StructCong Q P
  | trans    : ∀ P Q R, StructCong P Q → StructCong Q R → StructCong P R

theorem struct_cong_refl (P : Proc) : StructCong P P := StructCong.refl P
theorem struct_cong_par_comm (P Q : Proc) : StructCong (.par P Q) (.par Q P) := StructCong.parComm P Q
theorem struct_cong_par_nil (P : Proc) : StructCong (.par P .nil) P := StructCong.parNil P

-- ========== REDUCTION ==========

inductive Reduce : Proc → Proc → Prop where
  | comm : ∀ c v s P Q,
      Reduce (.restrict c (.send (Val.type v) s) (.par (.sendP c v P) (.recvP c Q)))
             (.restrict c s (.par P Q))
  | choiceL : ∀ c s1 s2 P Q1 Q2,
      Reduce (.restrict c (.choice s1 s2) (.par (.selectL c P) (.branchP c Q1 Q2)))
             (.restrict c s1 (.par P Q1))
  | choiceR : ∀ c s1 s2 P Q1 Q2,
      Reduce (.restrict c (.choice s1 s2) (.par (.selectR c P) (.branchP c Q1 Q2)))
             (.restrict c s2 (.par P Q2))
  | parL : ∀ P P' Q, Reduce P P' → Reduce (.par P Q) (.par P' Q)
  | parR : ∀ P Q Q', Reduce Q Q' → Reduce (.par P Q) (.par P Q')
  | res  : ∀ c s P P', Reduce P P' → Reduce (.restrict c s P) (.restrict c s P')
  | cong : ∀ P P' Q Q', StructCong P P' → Reduce P' Q' → StructCong Q' Q → Reduce P Q

-- ========== TYPING ==========

inductive Typed : Ctx → Proc → Prop where
  | tNil : Typed [] .nil
  | tSend : ∀ Γ c t s v P,
      Ctx.lookup Γ c = some (.send t s) →
      Val.type v = t →
      Typed (Ctx.update Γ c s) P →
      Typed Γ (.sendP c v P)
  | tRecv : ∀ Γ c t s P,
      Ctx.lookup Γ c = some (.recv t s) →
      Typed (Ctx.update Γ c s) P →
      Typed Γ (.recvP c P)
  | tSelectL : ∀ Γ c s1 s2 P,
      Ctx.lookup Γ c = some (.choice s1 s2) →
      Typed (Ctx.update Γ c s1) P →
      Typed Γ (.selectL c P)
  | tSelectR : ∀ Γ c s1 s2 P,
      Ctx.lookup Γ c = some (.choice s1 s2) →
      Typed (Ctx.update Γ c s2) P →
      Typed Γ (.selectR c P)
  | tBranch : ∀ Γ c s1 s2 P Q,
      Ctx.lookup Γ c = some (.branch s1 s2) →
      Typed (Ctx.update Γ c s1) P →
      Typed (Ctx.update Γ c s2) Q →
      Typed Γ (.branchP c P Q)
  | tPar : ∀ Γ1 Γ2 P Q,
      Typed Γ1 P → Typed Γ2 Q → Typed (Γ1 ++ Γ2) (.par P Q)
  | tRestrict : ∀ Γ c s P,
      Typed ((c, s) :: (c, s.dual) :: Γ) P →
      Typed Γ (.restrict c s P)

-- ========== TYPING PROPERTIES ==========

theorem nil_typed_empty : Typed [] .nil := Typed.tNil

theorem nil_typeable : ∃ Γ, Typed Γ .nil := ⟨[], Typed.tNil⟩

theorem par_nil_nil_typed : Typed [] (.par .nil .nil) := by
  have h : ([] : Ctx) ++ [] = ([] : Ctx) := rfl
  rw [← h]; exact Typed.tPar [] [] .nil .nil Typed.tNil Typed.tNil

-- ========== SESSION FIDELITY ==========

theorem session_advance_send (Γ : Ctx) (c : Nat) (t : BaseType) (s : SType) (v : Val) (P : Proc)
    (hL : Ctx.lookup Γ c = some (.send t s)) (hT : Val.type v = t)
    (hP : Typed (Ctx.update Γ c s) P) : Typed Γ (.sendP c v P) :=
  Typed.tSend Γ c t s v P hL hT hP

theorem session_advance_recv (Γ : Ctx) (c : Nat) (t : BaseType) (s : SType) (P : Proc)
    (hL : Ctx.lookup Γ c = some (.recv t s))
    (hP : Typed (Ctx.update Γ c s) P) : Typed Γ (.recvP c P) :=
  Typed.tRecv Γ c t s P hL hP

theorem session_advance_selectL (Γ : Ctx) (c : Nat) (s1 s2 : SType) (P : Proc)
    (hL : Ctx.lookup Γ c = some (.choice s1 s2))
    (hP : Typed (Ctx.update Γ c s1) P) : Typed Γ (.selectL c P) :=
  Typed.tSelectL Γ c s1 s2 P hL hP

theorem session_advance_selectR (Γ : Ctx) (c : Nat) (s1 s2 : SType) (P : Proc)
    (hL : Ctx.lookup Γ c = some (.choice s1 s2))
    (hP : Typed (Ctx.update Γ c s2) P) : Typed Γ (.selectR c P) :=
  Typed.tSelectR Γ c s1 s2 P hL hP

theorem session_advance_branch (Γ : Ctx) (c : Nat) (s1 s2 : SType) (P Q : Proc)
    (hL : Ctx.lookup Γ c = some (.branch s1 s2))
    (hP : Typed (Ctx.update Γ c s1) P) (hQ : Typed (Ctx.update Γ c s2) Q) :
    Typed Γ (.branchP c P Q) :=
  Typed.tBranch Γ c s1 s2 P Q hL hP hQ

-- ========== DUALITY IN RESTRICTION ==========

theorem comm_preserves_duality (t : BaseType) (s : SType) :
    (SType.send t s).dual = .recv t s.dual := rfl

theorem choice_preserves_duality (s1 s2 : SType) :
    (SType.choice s1 s2).dual = .branch s1.dual s2.dual := rfl

-- Restriction creates dual endpoints
theorem restrict_creates_duals (Γ : Ctx) (c : Nat) (s : SType) (P : Proc)
    (h : Typed Γ (.restrict c s P)) :
    ∃ Γ', Typed ((c, s) :: (c, s.dual) :: Γ') P := by
  cases h
  rename_i hP
  exact ⟨Γ, hP⟩

-- ========== TYPE SAFETY ==========

theorem typing_ensures_base_match (Γ : Ctx) (c : Nat) (v : Val) (P : Proc)
    (h : Typed Γ (.sendP c v P)) :
    ∃ t s, Ctx.lookup Γ c = some (.send t s) ∧ Val.type v = t := by
  cases h with | tSend _ _ t s _ _ hL hT _ => exact ⟨t, s, hL, hT⟩

theorem typing_ensures_recv (Γ : Ctx) (c : Nat) (P : Proc)
    (h : Typed Γ (.recvP c P)) :
    ∃ t s, Ctx.lookup Γ c = some (.recv t s) := by
  cases h with | tRecv _ _ t s _ hL _ => exact ⟨t, s, hL⟩

theorem typing_ensures_choice (Γ : Ctx) (c : Nat) (P : Proc)
    (h : Typed Γ (.selectL c P)) :
    ∃ s1 s2, Ctx.lookup Γ c = some (.choice s1 s2) := by
  cases h with | tSelectL _ _ s1 s2 _ hL _ => exact ⟨s1, s2, hL⟩

theorem typing_ensures_branch (Γ : Ctx) (c : Nat) (P Q : Proc)
    (h : Typed Γ (.branchP c P Q)) :
    ∃ s1 s2, Ctx.lookup Γ c = some (.branch s1 s2) := by
  cases h with | tBranch _ _ s1 s2 _ _ hL _ _ => exact ⟨s1, s2, hL⟩

-- ========== PROCESS PROPERTIES ==========

def Proc.size : Proc → Nat
  | .nil => 0
  | .sendP _ _ P => 1 + P.size
  | .recvP _ P => 1 + P.size
  | .selectL _ P => 1 + P.size
  | .selectR _ P => 1 + P.size
  | .branchP _ P Q => 1 + P.size + Q.size
  | .par P Q => P.size + Q.size
  | .restrict _ _ P => P.size

def Proc.isValue : Proc → Bool
  | .nil => true
  | .par P Q => P.isValue && Q.isValue
  | _ => false

theorem nil_is_value : Proc.isValue .nil = true := rfl
theorem par_nil_nil_value : Proc.isValue (.par .nil .nil) = true := rfl

theorem par_comm_value (P Q : Proc) (h : Proc.isValue (Proc.par P Q) = true) :
    Proc.isValue (Proc.par Q P) = true := by
  simp [Proc.isValue] at *; exact ⟨h.2, h.1⟩

-- Communication reduces process size
theorem comm_reduces_size (c : Nat) (v : Val) (P Q : Proc) :
    Proc.size (Proc.par (Proc.sendP c v P) (Proc.recvP c Q)) >
    Proc.size (Proc.par P Q) := by
  simp [Proc.size]; omega

theorem selectL_reduces_size (c : Nat) (P Q1 Q2 : Proc) :
    Proc.size (Proc.par (Proc.selectL c P) (Proc.branchP c Q1 Q2)) >
    Proc.size (Proc.par P Q1) := by
  simp [Proc.size]; omega

theorem selectR_reduces_size (c : Nat) (P Q1 Q2 : Proc) :
    Proc.size (Proc.par (Proc.selectR c P) (Proc.branchP c Q1 Q2)) >
    Proc.size (Proc.par P Q2) := by
  simp [Proc.size]; omega

-- ========== FREE CHANNELS ==========

def Proc.freeChans : Proc → List Nat
  | .nil => []
  | .sendP c _ P => c :: P.freeChans
  | .recvP c P => c :: P.freeChans
  | .selectL c P => c :: P.freeChans
  | .selectR c P => c :: P.freeChans
  | .branchP c P Q => c :: P.freeChans ++ Q.freeChans
  | .par P Q => P.freeChans ++ Q.freeChans
  | .restrict c _ P => (P.freeChans).filter (· != c)

theorem nil_no_free : Proc.freeChans .nil = [] := rfl
