import Solution

/-!
# Concrete certificate regression

The generic theorem is exercised on a non-terminating eight-node funnel with
three distinct local peaks. Its positive application supplies
`Nat.lt_wfRel.wf` as the well-founded label-order witness; the rewrite relation
itself contains a cycle. The positive and negative computations are kept
outside the Challenge/Solution pair so that they document the executable
boundary without enlarging the statement surface.
-/

namespace Metatheory.Palomar433

open Certificate

universe u

inductive Plus {α : Type u} (r : Relation α) : α → α → Prop where
  | single {a b : α} : r a b → Plus r a b
  | tail {a b c : α} : Plus r a b → r b c → Plus r a c

inductive FunnelStep : Nat → Nat → Nat → Prop where
  | zeroOne : FunnelStep 6 0 1
  | zeroTwo : FunnelStep 5 0 2
  | zeroThree : FunnelStep 4 0 3
  | oneFour : FunnelStep 2 1 4
  | fourSeven : FunnelStep 1 4 7
  | twoSeven : FunnelStep 1 2 7
  | threeFive : FunnelStep 3 3 5
  | fiveSix : FunnelStep 2 5 6
  | sixSeven : FunnelStep 1 6 7
  | sevenZero : FunnelStep 0 7 0

def funnelStepB (l a b : Nat) : Bool :=
  decide ((l = 6 ∧ a = 0 ∧ b = 1) ∨
    (l = 5 ∧ a = 0 ∧ b = 2) ∨
    (l = 4 ∧ a = 0 ∧ b = 3) ∨
    (l = 2 ∧ a = 1 ∧ b = 4) ∨
    (l = 1 ∧ a = 4 ∧ b = 7) ∨
    (l = 1 ∧ a = 2 ∧ b = 7) ∨
    (l = 3 ∧ a = 3 ∧ b = 5) ∨
    (l = 2 ∧ a = 5 ∧ b = 6) ∨
    (l = 1 ∧ a = 6 ∧ b = 7) ∨
    (l = 0 ∧ a = 7 ∧ b = 0))

def funnelLtB (l₁ l₂ : Nat) : Bool := decide (l₁ < l₂)

def funnelKey (s : Certificate.Edge Nat Nat) : Nat := 100 * s.source + s.target

def funnelSteps : List (Certificate.Edge Nat Nat) :=
  [ ⟨6, 0, 1⟩
  , ⟨5, 0, 2⟩
  , ⟨4, 0, 3⟩
  , ⟨2, 1, 4⟩
  , ⟨1, 4, 7⟩
  , ⟨1, 2, 7⟩
  , ⟨3, 3, 5⟩
  , ⟨2, 5, 6⟩
  , ⟨1, 6, 7⟩
  , ⟨0, 7, 0⟩ ]

def funnelCertificates : List (Certificate.PeakCertificate Nat Nat) :=
  [ { leftStep := ⟨6, 0, 1⟩
      rightStep := ⟨5, 0, 2⟩
      join := 7
      leftPath := [⟨2, 1, 4⟩, ⟨1, 4, 7⟩]
      rightPath := [⟨1, 2, 7⟩] }
  , { leftStep := ⟨6, 0, 1⟩
      rightStep := ⟨4, 0, 3⟩
      join := 7
      leftPath := [⟨2, 1, 4⟩, ⟨1, 4, 7⟩]
      rightPath := [⟨3, 3, 5⟩, ⟨2, 5, 6⟩, ⟨1, 6, 7⟩] }
  , { leftStep := ⟨5, 0, 2⟩
      rightStep := ⟨4, 0, 3⟩
      join := 7
      leftPath := [⟨1, 2, 7⟩]
      rightPath := [⟨3, 3, 5⟩, ⟨2, 5, 6⟩, ⟨1, 6, 7⟩] } ]

def funnelCheck : Bool :=
  Certificate.checkB funnelStepB funnelLtB funnelKey funnelSteps funnelCertificates

def funnelMissingPeak : List (Certificate.PeakCertificate Nat Nat) :=
  funnelCertificates.drop 1

def funnelBadValley : List (Certificate.PeakCertificate Nat Nat) :=
  [ { leftStep := ⟨6, 0, 1⟩
      rightStep := ⟨5, 0, 2⟩
      join := 7
      leftPath := [⟨2, 1, 4⟩, ⟨1, 4, 7⟩]
      rightPath := [⟨1, 2, 7⟩, ⟨0, 7, 0⟩] } ]

def funnelSymmetric : List (Certificate.PeakCertificate Nat Nat) :=
  [ { leftStep := ⟨5, 0, 2⟩
      rightStep := ⟨6, 0, 1⟩
      join := 7
      leftPath := [⟨1, 2, 7⟩]
      rightPath := [⟨2, 1, 4⟩, ⟨1, 4, 7⟩] } ]

theorem funnelStepB_iff : ∀ l a b, funnelStepB l a b = true ↔ FunnelStep l a b := by
  intro l a b
  constructor
  · intro h
    have h' :
        (l = 6 ∧ a = 0 ∧ b = 1) ∨
          (l = 5 ∧ a = 0 ∧ b = 2) ∨
          (l = 4 ∧ a = 0 ∧ b = 3) ∨
          (l = 2 ∧ a = 1 ∧ b = 4) ∨
          (l = 1 ∧ a = 4 ∧ b = 7) ∨
          (l = 1 ∧ a = 2 ∧ b = 7) ∨
          (l = 3 ∧ a = 3 ∧ b = 5) ∨
          (l = 2 ∧ a = 5 ∧ b = 6) ∨
          (l = 1 ∧ a = 6 ∧ b = 7) ∨
          (l = 0 ∧ a = 7 ∧ b = 0) :=
      of_decide_eq_true (by simpa [funnelStepB] using h)
    rcases h' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact FunnelStep.zeroOne
    · exact FunnelStep.zeroTwo
    · exact FunnelStep.zeroThree
    · exact FunnelStep.oneFour
    · exact FunnelStep.fourSeven
    · exact FunnelStep.twoSeven
    · exact FunnelStep.threeFive
    · exact FunnelStep.fiveSix
    · exact FunnelStep.sixSeven
    · exact FunnelStep.sevenZero
  · intro h
    cases h <;> rfl

theorem funnelLtB_iff : ∀ l₁ l₂, funnelLtB l₁ l₂ = true ↔ l₁ < l₂ := by
  intro l₁ l₂
  simp [funnelLtB]

theorem funnel_steps_complete : Certificate.StepsComplete funnelSteps FunnelStep := by
  intro l a b h
  cases h <;> simp [funnelSteps]

theorem funnel_check : funnelCheck = true := by
  decide

theorem funnel_confluent : Confluent (LabeledUnion FunnelStep) := by
  exact checked_complete_confluence funnelStepB_iff funnelLtB_iff funnel_check
    funnel_steps_complete Nat.lt_wfRel.wf

theorem funnel_not_terminating :
    ¬ (∀ x, Acc (fun u v => Plus (LabeledUnion FunnelStep) v u) x) := by
  intro hterm
  have h01 : LabeledUnion FunnelStep 0 1 := ⟨6, FunnelStep.zeroOne⟩
  have h14 : LabeledUnion FunnelStep 1 4 := ⟨2, FunnelStep.oneFour⟩
  have h47 : LabeledUnion FunnelStep 4 7 := ⟨1, FunnelStep.fourSeven⟩
  have h70 : LabeledUnion FunnelStep 7 0 := ⟨0, FunnelStep.sevenZero⟩
  have hloop : Plus (LabeledUnion FunnelStep) 0 0 :=
    Plus.tail (Plus.tail (Plus.tail (Plus.single h01) h14) h47) h70
  have no_loop : ∀ {x : Nat},
      Acc (fun u v => Plus (LabeledUnion FunnelStep) v u) x →
        ¬ Plus (LabeledUnion FunnelStep) x x := by
    intro x hacc
    induction hacc with
    | intro y _ ih =>
        intro hyy
        exact ih y hyy hyy
  exact no_loop (hterm 0) hloop

example : funnelCheck = true := by decide

example : Certificate.checkB funnelStepB funnelLtB funnelKey funnelSteps funnelMissingPeak = false := by
  decide

example : Certificate.checkB funnelStepB funnelLtB funnelKey funnelSteps funnelBadValley = false := by
  decide

example : Certificate.checkB funnelStepB funnelLtB funnelKey funnelSteps funnelSymmetric = false := by
  decide

end Metatheory.Palomar433
