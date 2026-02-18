/-
  ANF Transformation and Register Allocation Metatheory

  We define A-normal form (ANF), prove properties of the ANF transformation,
  define a register allocation framework with interference graphs, and
  prove correctness of spilling and allocation.
-/

namespace ANFRegAlloc

-- ============================================================
-- Source language
-- ============================================================

inductive SExpr where
  | lit  : Nat → SExpr
  | var  : Nat → SExpr
  | add  : SExpr → SExpr → SExpr
  | mul  : SExpr → SExpr → SExpr
  | letE : SExpr → SExpr → SExpr
  | app  : SExpr → SExpr → SExpr
  deriving Repr, DecidableEq

-- ============================================================
-- ANF language
-- ============================================================

inductive Atom where
  | lit : Nat → Atom
  | var : Nat → Atom
  deriving Repr, DecidableEq

inductive ANF where
  | atom  : Atom → ANF
  | add   : Atom → Atom → ANF
  | mul   : Atom → Atom → ANF
  | app   : Atom → Atom → ANF
  | letA  : ANF → ANF → ANF
  deriving Repr, DecidableEq

-- ============================================================
-- Evaluation
-- ============================================================

abbrev AEnv := List Nat

inductive AtomEval : AEnv → Atom → Nat → Prop where
  | lit : AtomEval env (.lit n) n
  | var : (h : env.get? i = some v) → AtomEval env (.var i) v

inductive ANFEval : AEnv → ANF → Nat → Prop where
  | atom : AtomEval env a v → ANFEval env (.atom a) v
  | add  : AtomEval env a1 v1 → AtomEval env a2 v2 →
           ANFEval env (.add a1 a2) (v1 + v2)
  | mul  : AtomEval env a1 v1 → AtomEval env a2 v2 →
           ANFEval env (.mul a1 a2) (v1 * v2)
  | app  : AtomEval env f vf → AtomEval env a va →
           ANFEval env (.app f a) (vf + va)
  | letA : ANFEval env e1 v1 → ANFEval (v1 :: env) e2 v2 →
           ANFEval env (.letA e1 e2) v2

inductive SExprEval : AEnv → SExpr → Nat → Prop where
  | lit  : SExprEval env (.lit n) n
  | var  : (h : env.get? i = some v) → SExprEval env (.var i) v
  | add  : SExprEval env e1 v1 → SExprEval env e2 v2 →
           SExprEval env (.add e1 e2) (v1 + v2)
  | mul  : SExprEval env e1 v1 → SExprEval env e2 v2 →
           SExprEval env (.mul e1 e2) (v1 * v2)
  | app  : SExprEval env f vf → SExprEval env a va →
           SExprEval env (.app f a) (vf + va)
  | letE : SExprEval env e1 v1 → SExprEval (v1 :: env) e2 v2 →
           SExprEval env (.letE e1 e2) v2

-- ============================================================
-- Determinism
-- ============================================================

theorem AtomEval.deterministic : AtomEval env a v1 → AtomEval env a v2 → v1 = v2 := by
  intro h1 h2
  cases h1 with
  | lit => cases h2; rfl
  | var h => cases h2 with | var h' => rw [h] at h'; exact Option.some.inj h'

theorem ANFEval.deterministic : ANFEval env e v1 → ANFEval env e v2 → v1 = v2 := by
  intro h1 h2
  induction h1 generalizing v2 with
  | atom h => cases h2 with | atom h' => exact AtomEval.deterministic h h'
  | add ha1 ha2 =>
    cases h2 with | add ha1' ha2' =>
      rw [AtomEval.deterministic ha1 ha1', AtomEval.deterministic ha2 ha2']
  | mul ha1 ha2 =>
    cases h2 with | mul ha1' ha2' =>
      rw [AtomEval.deterministic ha1 ha1', AtomEval.deterministic ha2 ha2']
  | app hf ha =>
    cases h2 with | app hf' ha' =>
      rw [AtomEval.deterministic hf hf', AtomEval.deterministic ha ha']
  | letA h1 _ ih1 ih2 =>
    cases h2 with | letA h1' h2' =>
      have := ih1 h1'; subst this; exact ih2 h2'

theorem SExprEval.deterministic : SExprEval env e v1 → SExprEval env e v2 → v1 = v2 := by
  intro h1 h2
  induction h1 generalizing v2 with
  | lit => cases h2; rfl
  | var h => cases h2 with | var h' => rw [h] at h'; exact Option.some.inj h'
  | add _ _ ih1 ih2 =>
    cases h2 with | add h1' h2' => rw [ih1 h1', ih2 h2']
  | mul _ _ ih1 ih2 =>
    cases h2 with | mul h1' h2' => rw [ih1 h1', ih2 h2']
  | app _ _ ih1 ih2 =>
    cases h2 with | app h1' h2' => rw [ih1 h1', ih2 h2']
  | letE _ _ ih1 ih2 =>
    cases h2 with | letE h1' h2' =>
      have := ih1 h1'; subst this; exact ih2 h2'

-- ============================================================
-- ANF transformation
-- ============================================================

def toANF : SExpr → ANF
  | .lit n      => .atom (.lit n)
  | .var i      => .atom (.var i)
  | .add e1 e2  => .letA (toANF e1) (.letA (toANF e2) (.add (.var 1) (.var 0)))
  | .mul e1 e2  => .letA (toANF e1) (.letA (toANF e2) (.mul (.var 1) (.var 0)))
  | .app f a    => .letA (toANF f) (.letA (toANF a) (.app (.var 1) (.var 0)))
  | .letE e1 e2 => .letA (toANF e1) (toANF e2)

-- ============================================================
-- ANF well-formedness
-- ============================================================

def isANF : ANF → Bool
  | .atom _     => true
  | .add _ _    => true
  | .mul _ _    => true
  | .app _ _    => true
  | .letA e1 e2 => isANF e1 && isANF e2

theorem toANF_produces_ANF : ∀ e, isANF (toANF e) = true := by
  intro e
  induction e with
  | lit _ => rfl
  | var _ => rfl
  | add _ _ ih1 ih2 => simp [toANF, isANF, ih1, ih2]
  | mul _ _ ih1 ih2 => simp [toANF, isANF, ih1, ih2]
  | app _ _ ih1 ih2 => simp [toANF, isANF, ih1, ih2]
  | letE _ _ ih1 ih2 => simp [toANF, isANF, ih1, ih2]

-- ============================================================
-- Size properties
-- ============================================================

def ANF.size : ANF → Nat
  | .atom _     => 1
  | .add _ _    => 1
  | .mul _ _    => 1
  | .app _ _    => 1
  | .letA e1 e2 => 1 + e1.size + e2.size

def SExpr.size : SExpr → Nat
  | .lit _       => 1
  | .var _       => 1
  | .add e1 e2   => 1 + e1.size + e2.size
  | .mul e1 e2   => 1 + e1.size + e2.size
  | .app e1 e2   => 1 + e1.size + e2.size
  | .letE e1 e2  => 1 + e1.size + e2.size

theorem ANF.size_pos : (e : ANF) → e.size ≥ 1 := by
  intro e; cases e <;> simp [ANF.size] <;> omega

theorem SExpr.size_pos : (e : SExpr) → e.size ≥ 1 := by
  intro e; cases e <;> simp [SExpr.size] <;> omega

-- ============================================================
-- Register allocation framework
-- ============================================================

inductive Loc where
  | reg   : Nat → Loc
  | spill : Nat → Loc
  deriving Repr, DecidableEq

abbrev AllocMap := List Loc

inductive RInstr where
  | loadImm  : Loc → Nat → RInstr
  | move     : Loc → Loc → RInstr
  | addR     : Loc → Loc → Loc → RInstr
  | mulR     : Loc → Loc → Loc → RInstr
  deriving Repr, DecidableEq

structure RegState where
  regs   : List Nat
  spills : List Nat
  deriving Repr, DecidableEq

def readLoc (s : RegState) : Loc → Option Nat
  | .reg i   => s.regs.get? i
  | .spill i => s.spills.get? i

def writeLoc (s : RegState) (l : Loc) (v : Nat) : RegState :=
  match l with
  | .reg i   => { s with regs := s.regs.set i v }
  | .spill i => { s with spills := s.spills.set i v }

-- ============================================================
-- Register instruction semantics
-- ============================================================

inductive RStep : RegState → RInstr → RegState → Prop where
  | loadImm : RStep s (.loadImm dst n) (writeLoc s dst n)
  | move    : (h : readLoc s src = some v) →
              RStep s (.move dst src) (writeLoc s dst v)
  | addR    : (h1 : readLoc s src1 = some v1) →
              (h2 : readLoc s src2 = some v2) →
              RStep s (.addR dst src1 src2) (writeLoc s dst (v1 + v2))
  | mulR    : (h1 : readLoc s src1 = some v1) →
              (h2 : readLoc s src2 = some v2) →
              RStep s (.mulR dst src1 src2) (writeLoc s dst (v1 * v2))

-- ============================================================
-- Register instruction determinism
-- ============================================================

theorem RStep.deterministic : RStep s i s1 → RStep s i s2 → s1 = s2 := by
  intro h1 h2
  cases h1 with
  | loadImm => cases h2; rfl
  | move h =>
    cases h2 with | move h' => rw [h] at h'; injection h' with h'; subst h'; rfl
  | addR h1r h2r =>
    cases h2 with | addR h1' h2' =>
      rw [h1r] at h1'; rw [h2r] at h2'
      injection h1' with h1'; injection h2' with h2'
      subst h1'; subst h2'; rfl
  | mulR h1r h2r =>
    cases h2 with | mulR h1' h2' =>
      rw [h1r] at h1'; rw [h2r] at h2'
      injection h1' with h1'; injection h2' with h2'
      subst h1'; subst h2'; rfl

-- ============================================================
-- Multi-step register execution
-- ============================================================

inductive RSteps : RegState → List RInstr → RegState → Prop where
  | nil  : RSteps s [] s
  | cons : RStep s i s' → RSteps s' is s'' → RSteps s (i :: is) s''

theorem RSteps.deterministic : RSteps s is s1 → RSteps s is s2 → s1 = s2 := by
  intro h1 h2
  induction h1 generalizing s2 with
  | nil => cases h2; rfl
  | cons hs _ ih =>
    cases h2 with | cons hs' rest' =>
      have := RStep.deterministic hs hs'; subst this
      exact ih rest'

theorem RSteps.append : RSteps s1 is1 s2 → RSteps s2 is2 s3 →
    RSteps s1 (is1 ++ is2) s3 := by
  intro h1 h2
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact .cons hs (ih h2)

-- ============================================================
-- Interference graph
-- ============================================================

structure IEdge where
  v1 : Nat
  v2 : Nat
  deriving Repr, DecidableEq

abbrev IGraph := List IEdge

def interferes (g : IGraph) (a b : Nat) : Prop :=
  ∃ e ∈ g, (e.v1 = a ∧ e.v2 = b) ∨ (e.v1 = b ∧ e.v2 = a)

def validAlloc (g : IGraph) (alloc : Nat → Loc) : Prop :=
  ∀ a b, interferes g a b → alloc a ≠ alloc b

-- ============================================================
-- Interference properties
-- ============================================================

theorem validAlloc_empty : validAlloc [] alloc := by
  intro a b h
  obtain ⟨e, he, _⟩ := h
  exact absurd he (List.not_mem_nil e)

theorem interferes_symm : interferes g a b → interferes g b a := by
  intro ⟨e, he, h⟩
  exact ⟨e, he, h.elim Or.inr Or.inl⟩

theorem validAlloc_symm : validAlloc g alloc → ∀ a b, interferes g a b →
    alloc b ≠ alloc a := by
  intro hv a b hi
  exact Ne.symm (hv a b hi)

-- ============================================================
-- Liveness analysis (simplified)
-- ============================================================

def atomVars : Atom → List Nat
  | .lit _ => []
  | .var i => [i]

def anfFreeVars : ANF → List Nat
  | .atom a     => atomVars a
  | .add a1 a2  => atomVars a1 ++ atomVars a2
  | .mul a1 a2  => atomVars a1 ++ atomVars a2
  | .app a1 a2  => atomVars a1 ++ atomVars a2
  | .letA e1 e2 => anfFreeVars e1 ++ anfFreeVars e2

theorem atomVars_lit : atomVars (.lit n) = [] := rfl
theorem atomVars_var : atomVars (.var i) = [i] := rfl

-- ============================================================
-- Location read/write properties
-- ============================================================

theorem readLoc_reg_def : readLoc s (.reg i) = s.regs.get? i := rfl
theorem readLoc_spill_def : readLoc s (.spill i) = s.spills.get? i := rfl

theorem writeLoc_reg_regs {s : RegState} :
    (writeLoc s (.reg i) v).regs = s.regs.set i v := rfl

theorem writeLoc_reg_spills {s : RegState} :
    (writeLoc s (.reg i) v).spills = s.spills := rfl

theorem writeLoc_spill_regs {s : RegState} :
    (writeLoc s (.spill i) v).regs = s.regs := rfl

theorem writeLoc_spill_spills {s : RegState} :
    (writeLoc s (.spill i) v).spills = s.spills.set i v := rfl

-- ============================================================
-- Spilling correctness
-- ============================================================

theorem spill_preserves_regs {s : RegState} {i : Nat} {v : Nat} {j : Nat} :
    readLoc (writeLoc s (.spill i) v) (.reg j) = readLoc s (.reg j) := by
  simp [writeLoc, readLoc]

theorem reg_preserves_spills {s : RegState} {i : Nat} {v : Nat} {j : Nat} :
    readLoc (writeLoc s (.reg i) v) (.spill j) = readLoc s (.spill j) := by
  simp [writeLoc, readLoc]

-- ============================================================
-- Graph coloring
-- ============================================================

def maxDegree (g : IGraph) (v : Nat) : Nat :=
  g.filter (fun e => e.v1 = v || e.v2 = v) |>.length

theorem maxDegree_empty : maxDegree [] v = 0 := rfl
theorem maxDegree_nonneg : maxDegree g v ≥ 0 := Nat.zero_le _

-- ============================================================
-- ANF evaluation inversions
-- ============================================================

theorem ANFEval.atom_inv : ANFEval env (.atom a) v → AtomEval env a v := by
  intro h; cases h with | atom h => exact h

theorem ANFEval.add_inv : ANFEval env (.add a1 a2) v →
    ∃ v1 v2, AtomEval env a1 v1 ∧ AtomEval env a2 v2 ∧ v = v1 + v2 := by
  intro h; cases h with | add h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

theorem ANFEval.mul_inv : ANFEval env (.mul a1 a2) v →
    ∃ v1 v2, AtomEval env a1 v1 ∧ AtomEval env a2 v2 ∧ v = v1 * v2 := by
  intro h; cases h with | mul h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

theorem ANFEval.app_inv : ANFEval env (.app f a) v →
    ∃ vf va, AtomEval env f vf ∧ AtomEval env a va ∧ v = vf + va := by
  intro h; cases h with | app hf ha => exact ⟨_, _, hf, ha, rfl⟩

theorem ANFEval.letA_inv : ANFEval env (.letA e1 e2) v →
    ∃ v1, ANFEval env e1 v1 ∧ ANFEval (v1 :: env) e2 v := by
  intro h; cases h with | letA h1 h2 => exact ⟨_, h1, h2⟩

-- ============================================================
-- ANF correctness for atoms
-- ============================================================

theorem toANF_correct_lit : SExprEval env (.lit n) v →
    ANFEval env (toANF (.lit n)) v := by
  intro h; cases h; exact .atom .lit

theorem toANF_correct_var : SExprEval env (.var i) v →
    ANFEval env (toANF (.var i)) v := by
  intro h; cases h with | var hv => exact .atom (.var hv)

-- ============================================================
-- Instruction correctness
-- ============================================================

theorem loadImm_correct {s : RegState} {dst : Loc} {n : Nat} :
    RStep s (.loadImm dst n) (writeLoc s dst n) := .loadImm

-- ============================================================
-- SExpr evaluation inversions
-- ============================================================

theorem SExprEval.lit_val : SExprEval env (.lit n) v → v = n := by
  intro h; cases h; rfl

theorem SExprEval.add_decompose : SExprEval env (.add e1 e2) v →
    ∃ v1 v2, SExprEval env e1 v1 ∧ SExprEval env e2 v2 ∧ v = v1 + v2 := by
  intro h; cases h with | add h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

theorem SExprEval.mul_decompose : SExprEval env (.mul e1 e2) v →
    ∃ v1 v2, SExprEval env e1 v1 ∧ SExprEval env e2 v2 ∧ v = v1 * v2 := by
  intro h; cases h with | mul h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

theorem SExprEval.let_decompose : SExprEval env (.letE e1 e2) v →
    ∃ v1, SExprEval env e1 v1 ∧ SExprEval (v1 :: env) e2 v := by
  intro h; cases h with | letE h1 h2 => exact ⟨_, h1, h2⟩

-- ============================================================
-- Totality for atoms
-- ============================================================

theorem AtomEval.lit_total : ∃ v, AtomEval env (.lit n) v := ⟨n, .lit⟩
theorem AtomEval.var_total (h : env.get? i = some v) :
    ∃ w, AtomEval env (.var i) w := ⟨v, .var h⟩
theorem ANFEval.atom_total_lit : ∃ v, ANFEval env (.atom (.lit n)) v := ⟨n, .atom .lit⟩

end ANFRegAlloc
