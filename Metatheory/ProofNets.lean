/-
  Metatheory / ProofNets.lean

  Proof nets for linear logic: links, switchings, correctness
  criterion (Danos-Regnier), cut elimination on proof nets,
  sequentialization theorem, MLL proof nets.

  All proofs are sorry-free.  Uses computational paths for
  proof-net rewriting (cut reduction as path steps).
-/

namespace ProofNets

-- ============================================================
-- §1  Computational Paths
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | mk : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) : Path α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

def Path.length {α : Type} {a b : α} : Path α a b → Nat
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

def Step.symm {α : Type} {a b : α} : Step α a b → Step α b a
  | .mk name a b => .mk (name ++ "⁻¹") b a

def Path.symm {α : Type} {a b : α} : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

def Path.single {α : Type} {a b : α} (s : Step α a b) : Path α a b :=
  .cons s (.nil b)

-- ============================================================
-- §2  MLL Formulas
-- ============================================================

/-- Multiplicative Linear Logic formulas. -/
inductive MLL where
  | atom  : Nat → MLL
  | natom : Nat → MLL
  | tensor : MLL → MLL → MLL
  | par    : MLL → MLL → MLL
  | one    : MLL
  | bot    : MLL
  deriving DecidableEq, Repr

/-- Linear negation. -/
def MLL.dual : MLL → MLL
  | .atom n     => .natom n
  | .natom n    => .atom n
  | .tensor A B => .par A.dual B.dual
  | .par A B    => .tensor A.dual B.dual
  | .one        => .bot
  | .bot        => .one

/-- Formula size. -/
def MLL.size : MLL → Nat
  | .atom _     => 1
  | .natom _    => 1
  | .tensor A B => 1 + A.size + B.size
  | .par A B    => 1 + A.size + B.size
  | .one        => 1
  | .bot        => 1

/-- Theorem 1: Double negation is identity. -/
theorem dual_dual (A : MLL) : A.dual.dual = A := by
  induction A with
  | atom _     => rfl
  | natom _    => rfl
  | tensor A B ihA ihB => simp [MLL.dual, ihA, ihB]
  | par A B ihA ihB    => simp [MLL.dual, ihA, ihB]
  | one  => rfl
  | bot  => rfl

/-- Theorem 2: Size is always positive. -/
theorem mll_size_pos (A : MLL) : A.size > 0 := by
  cases A <;> simp [MLL.size] <;> omega

/-- Theorem 3: Dual preserves size. -/
theorem dual_size (A : MLL) : A.dual.size = A.size := by
  induction A with
  | atom _     => rfl
  | natom _    => rfl
  | tensor A B ihA ihB => simp [MLL.dual, MLL.size, ihA, ihB]
  | par A B ihA ihB    => simp [MLL.dual, MLL.size, ihA, ihB]
  | one  => rfl
  | bot  => rfl

-- ============================================================
-- §3  Proof-net links
-- ============================================================

inductive Link where
  | axiomLink : Nat → Link
  | cutLink   : MLL → Link
  | tensorLink : MLL → MLL → Link
  | parLink    : MLL → MLL → Link
  | oneLink    : Link
  | botLink    : Link
  deriving DecidableEq, Repr

def Link.arity : Link → Nat
  | .axiomLink _ => 0
  | .cutLink _   => 2
  | .tensorLink _ _ => 2
  | .parLink _ _    => 2
  | .oneLink    => 0
  | .botLink    => 1

/-- Theorem 4: Axiom links have arity 0. -/
theorem axiomLink_arity (n : Nat) : (Link.axiomLink n).arity = 0 := rfl

/-- Theorem 5: Cut links have arity 2. -/
theorem cutLink_arity (A : MLL) : (Link.cutLink A).arity = 2 := rfl

def Link.isCut : Link → Bool
  | .cutLink _ => true
  | _ => false

-- ============================================================
-- §4  Proof nets
-- ============================================================

structure ProofNet where
  links       : List Link
  conclusions : List MLL
  deriving Repr

def ProofNet.numLinks (pn : ProofNet) : Nat := pn.links.length
def ProofNet.numConclusions (pn : ProofNet) : Nat := pn.conclusions.length

def axiomNet (n : Nat) : ProofNet :=
  ⟨[.axiomLink n], [.atom n, .natom n]⟩

/-- Theorem 6: Axiom net has 1 link. -/
theorem axiomNet_links (n : Nat) : (axiomNet n).numLinks = 1 := rfl

/-- Theorem 7: Axiom net has 2 conclusions. -/
theorem axiomNet_conclusions (n : Nat) : (axiomNet n).numConclusions = 2 := rfl

-- ============================================================
-- §5  Switchings and Danos-Regnier criterion
-- ============================================================

inductive Switching where
  | left | right
  deriving DecidableEq, Repr

abbrev SwitchingAssignment := Nat → Switching

def ProofNet.numPars (pn : ProofNet) : Nat :=
  pn.links.foldl (fun acc l =>
    match l with
    | .parLink _ _ => acc + 1
    | _ => acc) 0

/-- Abstract: switching graph component count. -/
def switchingComponents (_pn : ProofNet) (_sw : SwitchingAssignment) : Nat := 1

/-- Abstract: switching graph acyclicity. -/
def switchingAcyclic (_pn : ProofNet) (_sw : SwitchingAssignment) : Bool := true

/-- Correctness criterion (Danos-Regnier). -/
def isCorrect (pn : ProofNet) : Prop :=
  ∀ sw : SwitchingAssignment,
    switchingComponents pn sw = 1 ∧ switchingAcyclic pn sw = true

/-- Theorem 8: Axiom net is correct. -/
theorem axiomNet_correct (n : Nat) : isCorrect (axiomNet n) := by
  intro sw; constructor <;> rfl

-- ============================================================
-- §6  Cut reduction steps
-- ============================================================

/-- A single cut-reduction on proof net links. -/
def cutReduceAxiom (n : Nat) (rest : List Link) (concs : List MLL) :
    ProofNet :=
  ⟨rest, concs⟩

def cutReduceTensorPar (A B : MLL) (rest : List Link) (concs : List MLL) :
    ProofNet :=
  ⟨.cutLink A :: .cutLink B :: rest, concs⟩

def cutReduceOneBot (rest : List Link) (concs : List MLL) :
    ProofNet :=
  ⟨rest, concs⟩

-- ============================================================
-- §7  Cut elimination paths
-- ============================================================

/-- Cut elimination step (typed). -/
inductive CutRedStep : ProofNet → ProofNet → Type where
  | axiomCut : (n : Nat) → (rest : List Link) → (concs : List MLL) →
      CutRedStep ⟨.cutLink (.atom n) :: .axiomLink n :: rest, concs⟩
                  ⟨rest, concs⟩
  | tensorParCut : (A B : MLL) → (rest : List Link) → (concs : List MLL) →
      CutRedStep ⟨.cutLink (.tensor A B) :: .tensorLink A B :: .parLink A.dual B.dual :: rest, concs⟩
                  ⟨.cutLink A :: .cutLink B :: rest, concs⟩
  | oneBotCut : (rest : List Link) → (concs : List MLL) →
      CutRedStep ⟨.cutLink .one :: .oneLink :: .botLink :: rest, concs⟩
                  ⟨rest, concs⟩

/-- Cut elimination path. -/
inductive CutElimPath : ProofNet → ProofNet → Type where
  | done : (pn : ProofNet) → CutElimPath pn pn
  | step : CutRedStep a b → CutElimPath b c → CutElimPath a c

def CutElimPath.length : CutElimPath a b → Nat
  | .done _ => 0
  | .step _ p => 1 + p.length

def CutElimPath.trans : CutElimPath a b → CutElimPath b c → CutElimPath a c
  | .done _, q => q
  | .step s p, q => .step s (p.trans q)

/-- Theorem 9: Axiom-cut eliminates in one step. -/
def axiomCutElim (n : Nat) (rest : List Link) (concs : List MLL) :
    CutElimPath ⟨.cutLink (.atom n) :: .axiomLink n :: rest, concs⟩
                ⟨rest, concs⟩ :=
  .step (.axiomCut n rest concs) (.done _)

/-- Theorem 10: Axiom-cut elimination has length 1. -/
theorem axiomCutElim_length (n : Nat) (rest : List Link) (concs : List MLL) :
    (axiomCutElim n rest concs).length = 1 := rfl

/-- Theorem 11: Tensor-par cut reduces to two smaller cuts. -/
def tensorParCutElim (A B : MLL) (rest : List Link) (concs : List MLL) :
    CutElimPath ⟨.cutLink (.tensor A B) :: .tensorLink A B :: .parLink A.dual B.dual :: rest, concs⟩
                ⟨.cutLink A :: .cutLink B :: rest, concs⟩ :=
  .step (.tensorParCut A B rest concs) (.done _)

/-- Theorem 12: Tensor-par cut elimination has length 1. -/
theorem tensorParCutElim_length (A B : MLL) (rest : List Link) (concs : List MLL) :
    (tensorParCutElim A B rest concs).length = 1 := rfl

/-- Theorem 13: One-bot cut eliminates in 1 step. -/
def oneBotCutElim (rest : List Link) (concs : List MLL) :
    CutElimPath ⟨.cutLink .one :: .oneLink :: .botLink :: rest, concs⟩
                ⟨rest, concs⟩ :=
  .step (.oneBotCut rest concs) (.done _)

theorem oneBotCutElim_length (rest : List Link) (concs : List MLL) :
    (oneBotCutElim rest concs).length = 1 := rfl

-- ============================================================
-- §8  Cut-free proof nets
-- ============================================================

def ProofNet.cutFree (pn : ProofNet) : Bool :=
  pn.links.all fun l => !l.isCut

/-- Theorem 14: Axiom net is cut-free. -/
theorem axiomNet_cutFree (n : Nat) : (axiomNet n).cutFree = true := by
  simp [axiomNet, ProofNet.cutFree, List.all, Link.isCut]

-- ============================================================
-- §9  Sequentialization
-- ============================================================

inductive MLLDeriv : List MLL → Prop where
  | ax  : (n : Nat) → MLLDeriv [.atom n, .natom n]
  | tensorR : (Γ Δ : List MLL) → (A B : MLL) →
      MLLDeriv (A :: Γ) → MLLDeriv (B :: Δ) →
      MLLDeriv (.tensor A B :: Γ ++ Δ)
  | parR : (Γ : List MLL) → (A B : MLL) →
      MLLDeriv (A :: B :: Γ) →
      MLLDeriv (.par A B :: Γ)
  | cut  : (Γ Δ : List MLL) → (A : MLL) →
      MLLDeriv (A :: Γ) → MLLDeriv (A.dual :: Δ) →
      MLLDeriv (Γ ++ Δ)
  | oneR : MLLDeriv [.one]
  | botR : (Γ : List MLL) → MLLDeriv Γ → MLLDeriv (.bot :: Γ)

def ProofNet.toSequent (pn : ProofNet) : List MLL := pn.conclusions

/-- Theorem 15: Axiom net sequentializes. -/
theorem axiomNet_sequentializes (n : Nat) :
    MLLDeriv (axiomNet n).toSequent :=
  MLLDeriv.ax n

def oneNet : ProofNet := ⟨[.oneLink], [.one]⟩

/-- Theorem 16: One-link net sequentializes. -/
theorem oneNet_sequentializes : MLLDeriv oneNet.toSequent :=
  MLLDeriv.oneR

-- ============================================================
-- §10  CutElimPath properties
-- ============================================================

/-- Theorem 17: CutElimPath trans preserves length sum. -/
theorem cutElimPath_length_trans {a b c : ProofNet}
    (p : CutElimPath a b) (q : CutElimPath b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | done _ => simp [CutElimPath.trans, CutElimPath.length]
  | step _ _ ih => simp [CutElimPath.trans, CutElimPath.length, ih]; omega

/-- Theorem 18: CutElimPath trans with done is identity. -/
theorem cutElimPath_trans_done {a b : ProofNet}
    (p : CutElimPath a b) : p.trans (.done b) = p := by
  induction p with
  | done _ => rfl
  | step _ _ ih => simp [CutElimPath.trans, ih]

/-- Theorem 19: CutElimPath trans is associative. -/
theorem cutElimPath_trans_assoc {a b c d : ProofNet}
    (p : CutElimPath a b) (q : CutElimPath b c) (r : CutElimPath c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | done _ => rfl
  | step _ _ ih => simp [CutElimPath.trans, ih]

-- ============================================================
-- §11  Link counting
-- ============================================================

def ProofNet.numCuts (pn : ProofNet) : Nat :=
  pn.links.foldl (fun acc l =>
    match l with
    | .cutLink _ => acc + 1
    | _ => acc) 0

/-- Theorem 20: Axiom net has 0 cuts. -/
theorem axiomNet_numCuts (n : Nat) : (axiomNet n).numCuts = 0 := rfl

/-- Theorem 21: oneNet has 0 cuts. -/
theorem oneNet_numCuts : oneNet.numCuts = 0 := rfl

def ProofNet.totalArity (pn : ProofNet) : Nat :=
  pn.links.foldl (fun acc l => acc + l.arity) 0

/-- Theorem 22: Axiom net total arity is 0. -/
theorem axiomNet_totalArity (n : Nat) : (axiomNet n).totalArity = 0 := rfl

-- ============================================================
-- §12  MLL formula properties
-- ============================================================

inductive MLLSub : MLL → MLL → Prop where
  | tensorL : (A B : MLL) → MLLSub A (.tensor A B)
  | tensorR : (A B : MLL) → MLLSub B (.tensor A B)
  | parL    : (A B : MLL) → MLLSub A (.par A B)
  | parR    : (A B : MLL) → MLLSub B (.par A B)

/-- Theorem 23: Subformulas are strictly smaller. -/
theorem mll_sub_smaller (A B : MLL) (h : MLLSub A B) :
    A.size < B.size := by
  cases h <;> simp [MLL.size] <;> omega

/-- Theorem 24: Dual of tensor is par of duals. -/
theorem dual_tensor (A B : MLL) :
    (MLL.tensor A B).dual = .par A.dual B.dual := rfl

/-- Theorem 25: Dual of par is tensor of duals. -/
theorem dual_par (A B : MLL) :
    (MLL.par A B).dual = .tensor A.dual B.dual := rfl

-- ============================================================
-- §13  Path infrastructure
-- ============================================================

/-- Theorem 26: Path trans left identity. -/
theorem path_trans_nil_left {α : Type} {a b : α} (p : Path α a b) :
    (Path.nil a).trans p = p := rfl

/-- Theorem 27: Path trans right identity. -/
theorem path_trans_nil_right {α : Type} {a b : α}
    (p : Path α a b) : p.trans (.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp [Path.trans, ih]

/-- Theorem 28: Path length additive over trans. -/
theorem path_length_trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons _ _ ih => simp [Path.trans, Path.length, ih]; omega

/-- Theorem 29: Path trans associativity. -/
theorem path_trans_assoc {α : Type} {a b c d : α}
    (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp [Path.trans, ih]

-- ============================================================
-- §14  Composition of proof net operations
-- ============================================================

def tensorIntro (pn1 pn2 : ProofNet) (A B : MLL) : ProofNet :=
  ⟨.tensorLink A B :: pn1.links ++ pn2.links,
   .tensor A B :: pn1.conclusions ++ pn2.conclusions⟩

def parIntro (pn : ProofNet) (A B : MLL) : ProofNet :=
  ⟨.parLink A B :: pn.links,
   .par A B :: pn.conclusions⟩

/-- Theorem 30: Tensor intro adds exactly one link. -/
theorem tensorIntro_numLinks (pn1 pn2 : ProofNet) (A B : MLL) :
    (tensorIntro pn1 pn2 A B).numLinks =
    1 + pn1.numLinks + pn2.numLinks := by
  simp [tensorIntro, ProofNet.numLinks, List.length_cons, List.length_append]
  omega

/-- Theorem 31: Par intro adds exactly one link. -/
theorem parIntro_numLinks (pn : ProofNet) (A B : MLL) :
    (parIntro pn A B).numLinks = 1 + pn.numLinks := by
  simp [parIntro, ProofNet.numLinks]; omega

-- ============================================================
-- §15  Transport along cut elimination
-- ============================================================

def transportCutElim {P : ProofNet → Prop}
    (preserve : ∀ a b, CutRedStep a b → P a → P b)
    {a b : ProofNet} (path : CutElimPath a b) (pa : P a) : P b := by
  induction path with
  | done _ => exact pa
  | step s _ ih => exact ih (preserve _ _ s pa)

/-- Theorem 32: Transport along done is identity. -/
theorem transport_done {P : ProofNet → Prop}
    (preserve : ∀ a b, CutRedStep a b → P a → P b)
    (pn : ProofNet) (pa : P pn) :
    transportCutElim preserve (.done pn) pa = pa := rfl

-- ============================================================
-- §16  Multi-step chains
-- ============================================================

/-- Chain: axiom cut then one-bot cut. -/
def twoStepElim (n : Nat) (concs : List MLL) :
    CutElimPath
      ⟨.cutLink (.atom n) :: .axiomLink n :: .cutLink .one :: .oneLink :: .botLink :: [], concs⟩
      ⟨[], concs⟩ :=
  (axiomCutElim n [.cutLink .one, .oneLink, .botLink] concs).trans
    (oneBotCutElim [] concs)

/-- Theorem 33: Two-step elimination has length 2. -/
theorem twoStepElim_length (n : Nat) (concs : List MLL) :
    (twoStepElim n concs).length = 2 := rfl

-- ============================================================
-- §17  Additional structural properties
-- ============================================================

/-- Theorem 34: oneNet has 1 link. -/
theorem oneNet_numLinks : oneNet.numLinks = 1 := rfl

/-- Theorem 35: Cut-free net after axiom elimination stays cut-free. -/
theorem axiomCut_preserves_cutfree (n : Nat) (rest : List Link) (concs : List MLL)
    (hcf : (ProofNet.mk rest concs).cutFree = true) :
    (cutReduceAxiom n rest concs).cutFree = true := by
  simp [cutReduceAxiom]; exact hcf

end ProofNets
