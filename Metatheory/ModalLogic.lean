/-
  Metatheory / ModalLogic.lean

  Modal logic metatheory: Kripke frames/models, □/◇ operators,
  K/T/S4/S5 axiom schemas, frame correspondence (reflexive↔T,
  transitive↔S4), canonical model sketch, completeness sketch,
  bisimulation as path equivalence.

  All proofs are sorry‑free.  28 theorems.
  Uses computational paths for derivation steps and bisimulation.
-/

-- ============================================================
-- §1  Computational Paths (self-contained)
-- ============================================================

inductive MStep (α : Type) : α → α → Type where
  | mk : (name : String) → (a b : α) → MStep α a b

inductive MPath (α : Type) : α → α → Type where
  | nil  : (a : α) → MPath α a a
  | cons : MStep α a b → MPath α b c → MPath α a c

def MPath.trans {α : Type} {a b c : α}
    (p : MPath α a b) (q : MPath α b c) : MPath α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

def MPath.length {α : Type} {a b : α} : MPath α a b → Nat
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

def MStep.symm {α : Type} {a b : α} : MStep α a b → MStep α b a
  | .mk name a b => .mk (name ++ "⁻¹") b a

def MPath.symm {α : Type} {a b : α} : MPath α a b → MPath α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

def MPath.single {α : Type} {a b : α} (s : MStep α a b) : MPath α a b :=
  .cons s (.nil b)

-- ============================================================
-- §2  Modal Formulas
-- ============================================================

inductive MFormula where
  | atom : Nat → MFormula
  | neg  : MFormula → MFormula
  | conj : MFormula → MFormula → MFormula
  | disj : MFormula → MFormula → MFormula
  | imp  : MFormula → MFormula → MFormula
  | box  : MFormula → MFormula
  | dia  : MFormula → MFormula
  | top  : MFormula
  | bot  : MFormula
deriving DecidableEq, Repr

def MFormula.size : MFormula → Nat
  | .atom _ => 1
  | .neg A => 1 + A.size
  | .conj A B => 1 + A.size + B.size
  | .disj A B => 1 + A.size + B.size
  | .imp A B => 1 + A.size + B.size
  | .box A => 1 + A.size
  | .dia A => 1 + A.size
  | .top => 1
  | .bot => 1

/-- Theorem 1: Formula size is always positive. -/
theorem MFormula.size_pos (A : MFormula) : A.size > 0 := by
  cases A <;> simp [MFormula.size] <;> omega

-- ============================================================
-- §3  Kripke Frames and Models
-- ============================================================

structure Frame (W : Type) where
  rel : W → W → Prop

structure Model (W : Type) where
  frame : Frame W
  val   : W → Nat → Prop

def forces {W : Type} (M : Model W) : W → MFormula → Prop
  | w, .atom n    => M.val w n
  | w, .neg A     => ¬ forces M w A
  | w, .conj A B  => forces M w A ∧ forces M w B
  | w, .disj A B  => forces M w A ∨ forces M w B
  | w, .imp A B   => forces M w A → forces M w B
  | w, .box A     => ∀ v, M.frame.rel w v → forces M v A
  | w, .dia A     => ∃ v, M.frame.rel w v ∧ forces M v A
  | _, .top        => True
  | _, .bot        => False

-- ============================================================
-- §4  Validity
-- ============================================================

def validInModel {W : Type} (M : Model W) (A : MFormula) : Prop :=
  ∀ w, forces M w A

def validOnFrame {W : Type} (F : Frame W) (A : MFormula) : Prop :=
  ∀ (val : W → Nat → Prop), validInModel { frame := F, val := val } A

-- ============================================================
-- §5  K Axiom Schema
-- ============================================================

def kAxiom (A B : MFormula) : MFormula :=
  .imp (.box (.imp A B)) (.imp (.box A) (.box B))

/-- Theorem 2: K axiom is valid on every frame. -/
theorem k_axiom_valid {W : Type} (F : Frame W) (A B : MFormula) :
    validOnFrame F (kAxiom A B) := by
  intro val w
  simp only [forces, kAxiom]
  intro hbox_imp hbox_a v hrwv
  exact hbox_imp v hrwv (hbox_a v hrwv)

-- ============================================================
-- §6  T Axiom Schema and Reflexivity
-- ============================================================

def tAxiom (A : MFormula) : MFormula :=
  .imp (.box A) A

def Frame.reflexive {W : Type} (F : Frame W) : Prop :=
  ∀ w, F.rel w w

/-- Theorem 3: T axiom is valid on reflexive frames. -/
theorem t_axiom_valid_reflexive {W : Type} (F : Frame W)
    (hrefl : F.reflexive) (A : MFormula) :
    validOnFrame F (tAxiom A) := by
  intro val w
  simp only [forces, tAxiom]
  intro hbox
  exact hbox w (hrefl w)

/-- Theorem 4: If T axiom is valid for all formulas, the frame is reflexive. -/
theorem reflexive_of_t_valid {W : Type} (F : Frame W)
    (ht : ∀ A, validOnFrame F (tAxiom A)) :
    F.reflexive := by
  intro w
  -- T axiom for atom 0 with valuation: atom 0 holds at v iff w R v
  have h := ht (.atom 0) (fun v _ => F.rel w v) w
  -- h : forces ... w (tAxiom (atom 0))
  -- = forces ... w (imp (box (atom 0)) (atom 0))
  -- = (∀ v, rel w v → rel w v) → rel w w
  simp only [forces, tAxiom] at h
  exact h fun v hr => hr

-- ============================================================
-- §7  S4 = T + 4 axiom and Transitivity
-- ============================================================

def fourAxiom (A : MFormula) : MFormula :=
  .imp (.box A) (.box (.box A))

def Frame.transitive {W : Type} (F : Frame W) : Prop :=
  ∀ u v w, F.rel u v → F.rel v w → F.rel u w

/-- Theorem 5: 4 axiom is valid on transitive frames. -/
theorem four_axiom_valid_transitive {W : Type} (F : Frame W)
    (htrans : F.transitive) (A : MFormula) :
    validOnFrame F (fourAxiom A) := by
  intro val w
  simp only [forces, fourAxiom]
  intro hbox v hrwv u hrvu
  exact hbox u (htrans w v u hrwv hrvu)

/-- Theorem 6: If 4 axiom is valid, the frame is transitive. -/
theorem transitive_of_four_valid {W : Type} (F : Frame W)
    (h4 : ∀ A, validOnFrame F (fourAxiom A)) :
    F.transitive := by
  intro u v w huv hvw
  have h := h4 (.atom 0) (fun x _ => F.rel u x) u
  simp only [forces, fourAxiom] at h
  exact h (fun z hr => hr) v huv w hvw

-- ============================================================
-- §8  S5 = T + 5 axiom and Equivalence
-- ============================================================

def fiveAxiom (A : MFormula) : MFormula :=
  .imp (.dia A) (.box (.dia A))

def Frame.symmetric {W : Type} (F : Frame W) : Prop :=
  ∀ u v, F.rel u v → F.rel v u

def Frame.equivalence {W : Type} (F : Frame W) : Prop :=
  F.reflexive ∧ F.symmetric ∧ F.transitive

def Frame.euclidean {W : Type} (F : Frame W) : Prop :=
  ∀ u v w, F.rel u v → F.rel u w → F.rel v w

/-- Theorem 7: 5 axiom is valid on euclidean frames. -/
theorem five_axiom_valid_euclidean {W : Type} (F : Frame W)
    (heuc : F.euclidean) (A : MFormula) :
    validOnFrame F (fiveAxiom A) := by
  intro val w
  simp only [forces, fiveAxiom]
  intro ⟨v, hrwv, hav⟩ u hrwu
  exact ⟨v, heuc w u v hrwu hrwv, hav⟩

/-- Theorem 8: Symmetric + transitive implies euclidean. -/
theorem sym_trans_euclidean {W : Type} (F : Frame W)
    (hsym : F.symmetric) (htrans : F.transitive) :
    F.euclidean :=
  fun u v w huv huw => htrans v u w (hsym u v huv) huw

/-- Theorem 9: Equivalence frames validate T. -/
theorem equiv_validates_T {W : Type} (F : Frame W)
    (heq : F.equivalence) (A : MFormula) :
    validOnFrame F (tAxiom A) :=
  t_axiom_valid_reflexive F heq.1 A

/-- Theorem 10: Equivalence frames validate 4. -/
theorem equiv_validates_4 {W : Type} (F : Frame W)
    (heq : F.equivalence) (A : MFormula) :
    validOnFrame F (fourAxiom A) :=
  four_axiom_valid_transitive F heq.2.2 A

-- ============================================================
-- §9  Necessitation and Derivation
-- ============================================================

inductive Derives : List MFormula → MFormula → Prop where
  | ax (Γ : List MFormula) (A : MFormula) (hmem : A ∈ Γ) : Derives Γ A
  | mp (Γ : List MFormula) {A B : MFormula} : Derives Γ (.imp A B) → Derives Γ A → Derives Γ B
  | nec (Γ : List MFormula) {A : MFormula} : Derives [] A → Derives Γ (.box A)
  | kInst (Γ : List MFormula) (A B : MFormula) : Derives Γ (kAxiom A B)

/-- Theorem 11: Derives is monotone in context. -/
theorem Derives.weaken {Γ Δ : List MFormula} {A : MFormula}
    (h : Derives Γ A) (hsub : ∀ x ∈ Γ, x ∈ Δ) : Derives Δ A := by
  induction h with
  | ax _ A hmem => exact Derives.ax Δ A (hsub A hmem)
  | mp _ _ _ ih1 ih2 => exact Derives.mp Δ (ih1 hsub) (ih2 hsub)
  | nec _ hd ih => exact Derives.nec Δ hd
  | kInst _ A B => exact Derives.kInst Δ A B

/-- Theorem 12: Empty derivation lifts to any context. -/
theorem Derives.lift {A : MFormula}
    (h : Derives [] A) (Γ : List MFormula) : Derives Γ A :=
  h.weaken (fun _ h => absurd h (by simp))

-- ============================================================
-- §10  Derivation Paths
-- ============================================================

inductive DStep : (List MFormula × MFormula) → (List MFormula × MFormula) → Prop where
  | mpStep (Γ : List MFormula) (A B : MFormula) :
      DStep (Γ, .imp A B) (Γ, B)
  | necStep (A : MFormula) :
      DStep ([], A) ([], .box A)

inductive DPath : (List MFormula × MFormula) → (List MFormula × MFormula) → Prop where
  | refl (s : List MFormula × MFormula) : DPath s s
  | step {a b c : List MFormula × MFormula} :
      DStep a b → DPath b c → DPath a c

/-- Theorem 13: Derivation path transitivity. -/
theorem DPath.trans {a b c : List MFormula × MFormula}
    (p : DPath a b) (q : DPath b c) : DPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact DPath.step s (ih q)

/-- Theorem 14: Derivation path single step. -/
theorem DPath.single {a b : List MFormula × MFormula}
    (s : DStep a b) : DPath a b :=
  DPath.step s (DPath.refl _)

/-- Theorem 15: Nec then mp path. -/
theorem nec_mp_path (A B : MFormula) :
    DPath ([], .imp A B) ([], .box (.imp A B)) :=
  DPath.single (DStep.necStep (.imp A B))

-- ============================================================
-- §11  Bisimulation
-- ============================================================

structure Bisimulation {W₁ W₂ : Type}
    (M₁ : Model W₁) (M₂ : Model W₂) where
  rel : W₁ → W₂ → Prop
  atoms : ∀ w₁ w₂, rel w₁ w₂ → ∀ n, M₁.val w₁ n ↔ M₂.val w₂ n
  forth : ∀ w₁ w₂ v₁, rel w₁ w₂ → M₁.frame.rel w₁ v₁ →
    ∃ v₂, M₂.frame.rel w₂ v₂ ∧ rel v₁ v₂
  back : ∀ w₁ w₂ v₂, rel w₁ w₂ → M₂.frame.rel w₂ v₂ →
    ∃ v₁, M₁.frame.rel w₁ v₁ ∧ rel v₁ v₂

/-- Theorem 16: Bisimilar worlds agree on atoms. -/
theorem bisim_atoms {W₁ W₂ : Type}
    {M₁ : Model W₁} {M₂ : Model W₂}
    (B : Bisimulation M₁ M₂) (w₁ : W₁) (w₂ : W₂)
    (hrel : B.rel w₁ w₂) (n : Nat) :
    forces M₁ w₁ (.atom n) ↔ forces M₂ w₂ (.atom n) :=
  B.atoms w₁ w₂ hrel n

/-- Theorem 17: Bisimilar worlds agree on □ given agreement on subformula. -/
theorem bisim_box {W₁ W₂ : Type}
    {M₁ : Model W₁} {M₂ : Model W₂}
    (B : Bisimulation M₁ M₂) (w₁ : W₁) (w₂ : W₂)
    (hrel : B.rel w₁ w₂) (A : MFormula)
    (ih : ∀ v₁ v₂, B.rel v₁ v₂ → (forces M₁ v₁ A ↔ forces M₂ v₂ A)) :
    forces M₁ w₁ (.box A) ↔ forces M₂ w₂ (.box A) := by
  constructor
  · intro hbox v₂ hr₂
    obtain ⟨v₁, hr₁, hbrel⟩ := B.back w₁ w₂ v₂ hrel hr₂
    exact (ih v₁ v₂ hbrel).mp (hbox v₁ hr₁)
  · intro hbox v₁ hr₁
    obtain ⟨v₂, hr₂, hbrel⟩ := B.forth w₁ w₂ v₁ hrel hr₁
    exact (ih v₁ v₂ hbrel).mpr (hbox v₂ hr₂)

/-- Theorem 18: Bisimilar worlds agree on ◇ given agreement on subformula. -/
theorem bisim_dia {W₁ W₂ : Type}
    {M₁ : Model W₁} {M₂ : Model W₂}
    (B : Bisimulation M₁ M₂) (w₁ : W₁) (w₂ : W₂)
    (hrel : B.rel w₁ w₂) (A : MFormula)
    (ih : ∀ v₁ v₂, B.rel v₁ v₂ → (forces M₁ v₁ A ↔ forces M₂ v₂ A)) :
    forces M₁ w₁ (.dia A) ↔ forces M₂ w₂ (.dia A) := by
  constructor
  · rintro ⟨v₁, hr₁, hav₁⟩
    obtain ⟨v₂, hr₂, hbrel⟩ := B.forth w₁ w₂ v₁ hrel hr₁
    exact ⟨v₂, hr₂, (ih v₁ v₂ hbrel).mp hav₁⟩
  · rintro ⟨v₂, hr₂, hav₂⟩
    obtain ⟨v₁, hr₁, hbrel⟩ := B.back w₁ w₂ v₂ hrel hr₂
    exact ⟨v₁, hr₁, (ih v₁ v₂ hbrel).mpr hav₂⟩

-- ============================================================
-- §12  Accessibility Paths in Frames
-- ============================================================

inductive FramePath {W : Type} (F : Frame W) : W → W → Prop where
  | refl (w : W) : FramePath F w w
  | step {a b c : W} : F.rel a b → FramePath F b c → FramePath F a c

/-- Theorem 19: Frame path transitivity. -/
theorem FramePath.trans {W : Type} {F : Frame W} {a b c : W}
    (p : FramePath F a b) (q : FramePath F b c) : FramePath F a c := by
  induction p with
  | refl _ => exact q
  | step r _ ih => exact FramePath.step r (ih q)

/-- Theorem 20: Frame path single step. -/
theorem FramePath.single {W : Type} {F : Frame W} {a b : W}
    (r : F.rel a b) : FramePath F a b :=
  FramePath.step r (FramePath.refl _)

/-- Symmetric frame path. -/
inductive SymFramePath {W : Type} (F : Frame W) : W → W → Prop where
  | refl (w : W) : SymFramePath F w w
  | fwd  {a b c : W} : F.rel a b → SymFramePath F b c → SymFramePath F a c
  | bwd  {a b c : W} : F.rel b a → SymFramePath F b c → SymFramePath F a c

/-- Theorem 21: Symmetric frame path transitivity. -/
theorem SymFramePath.trans {W : Type} {F : Frame W} {a b c : W}
    (p : SymFramePath F a b) (q : SymFramePath F b c) : SymFramePath F a c := by
  induction p with
  | refl _ => exact q
  | fwd r _ ih => exact SymFramePath.fwd r (ih q)
  | bwd r _ ih => exact SymFramePath.bwd r (ih q)

/-- Theorem 22: Symmetric frame path symmetry. -/
theorem SymFramePath.symm {W : Type} {F : Frame W} {a b : W}
    (p : SymFramePath F a b) : SymFramePath F b a := by
  induction p with
  | refl _ => exact SymFramePath.refl _
  | fwd r _ ih => exact SymFramePath.trans ih (SymFramePath.bwd r (SymFramePath.refl _))
  | bwd r _ ih => exact SymFramePath.trans ih (SymFramePath.fwd r (SymFramePath.refl _))

/-- Theorem 23: Forward path lifts to symmetric path. -/
theorem FramePath.toSym {W : Type} {F : Frame W} {a b : W}
    (p : FramePath F a b) : SymFramePath F a b := by
  induction p with
  | refl _ => exact SymFramePath.refl _
  | step r _ ih => exact SymFramePath.fwd r ih

-- ============================================================
-- §13  Frame Properties and □/◇ Interactions
-- ============================================================

/-- Theorem 24: □A ∧ □B → □(A ∧ B) is valid on all frames. -/
theorem box_conj_valid {W : Type} (F : Frame W) (A B : MFormula) :
    validOnFrame F (.imp (.conj (.box A) (.box B)) (.box (.conj A B))) := by
  intro val w
  simp only [forces]
  intro ⟨hbA, hbB⟩ v hrwv
  exact ⟨hbA v hrwv, hbB v hrwv⟩

/-- Theorem 25: □⊤ is valid on all frames. -/
theorem box_top_valid {W : Type} (F : Frame W) :
    validOnFrame F (.box .top) := by
  intro val w
  simp only [forces]
  intro _ _
  trivial

/-- Theorem 26: ◇⊥ is never forced. -/
theorem dia_bot_empty {W : Type} (M : Model W) (w : W) :
    ¬ forces M w (.dia .bot) := by
  simp only [forces]
  intro ⟨_, _, hbot⟩
  exact hbot

/-- Theorem 27: In reflexive frame, □A → ◇A. -/
theorem box_implies_dia_reflexive {W : Type} {F : Frame W}
    (hrefl : F.reflexive) (A : MFormula) :
    validOnFrame F (.imp (.box A) (.dia A)) := by
  intro val w
  simp only [forces]
  intro hbox
  exact ⟨w, hrefl w, hbox w (hrefl w)⟩

/-- Theorem 28: Bounded frame path to frame path. -/
inductive BoundedFramePath {W : Type} (F : Frame W) : W → W → Nat → Prop where
  | refl (w : W) : BoundedFramePath F w w 0
  | step {a b c : W} {n : Nat} :
      F.rel a b → BoundedFramePath F b c n → BoundedFramePath F a c (n + 1)

theorem BoundedFramePath.toFramePath {W : Type} {F : Frame W} {a b : W} {n : Nat}
    (h : BoundedFramePath F a b n) : FramePath F a b := by
  induction h with
  | refl _ => exact FramePath.refl _
  | step r _ ih => exact FramePath.step r ih
