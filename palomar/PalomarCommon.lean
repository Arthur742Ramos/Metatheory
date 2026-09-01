import Std

/-!
# Generic decreasing-diagram foundation

This file is the proof-only, standard-library foundation for the Palomar
certificate package. It defines the labeled relation, the two star closures,
and the well-founded decreasing-diagram theorem used by `PalomarProof.lean`.
That theorem requires `WellFounded lt` for the label relation, but it does not
require termination of the underlying rewrite relation. It deliberately does
not import the parent Metatheory project.
-/

namespace Metatheory.Palomar433

universe u v

abbrev Relation (α : Type u) := α → α → Prop
abbrev LabeledARS (α : Type u) (L : Type v) := L → α → α → Prop

def LabeledUnion {α : Type u} {L : Type v} (r : LabeledARS α L) : Relation α :=
  fun a b => ∃ l, r l a b

inductive Star {α : Type u} (r : Relation α) : α → α → Prop where
  | refl (a : α) : Star r a a
  | tail {a b c : α} : Star r a b → r b c → Star r a c

namespace Star

theorem single {α : Type u} {r : Relation α} {a b : α} (h : r a b) : Star r a b :=
  Star.tail (Star.refl a) h

theorem trans {α : Type u} {r : Relation α} {a b c : α}
    (h₁ : Star r a b) (h₂ : Star r b c) : Star r a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hstep ih => exact Star.tail ih hstep

end Star

theorem star_cases {α : Type u} {r : Relation α} {a b : α} (h : Star r a b) :
    a = b ∨ ∃ c, r a c ∧ Star r c b := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hab hbc ih =>
      rcases ih with hEq | ⟨d, had, hdb⟩
      · cases hEq
        exact Or.inr ⟨_, hbc, Star.refl _⟩
      · exact Or.inr ⟨d, had, Star.tail hdb hbc⟩

inductive StarPred {α : Type u} {L : Type v} (r : LabeledARS α L)
    (P : L → Prop) : α → α → Prop where
  | refl (a : α) : StarPred r P a a
  | tail {a b c : α} : StarPred r P a b → (l : L) → P l → r l b c → StarPred r P a c

namespace StarPred

theorem trans {α : Type u} {L : Type v} {r : LabeledARS α L} {P : L → Prop}
    {a b c : α} (h₁ : StarPred r P a b) (h₂ : StarPred r P b c) :
    StarPred r P a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ l hl hstep ih => exact StarPred.tail ih l hl hstep

theorem mono {α : Type u} {L : Type v} {r : LabeledARS α L}
    {P Q : L → Prop} (hPQ : ∀ l, P l → Q l)
    {a b : α} (h : StarPred r P a b) : StarPred r Q a b := by
  induction h with
  | refl => exact StarPred.refl _
  | tail _ l hl hstep ih => exact StarPred.tail ih l (hPQ l hl) hstep

end StarPred

theorem starPred_to_star {α : Type u} {L : Type v} {r : LabeledARS α L}
    {P : L → Prop} {a b : α} (h : StarPred r P a b) :
    Star (LabeledUnion r) a b := by
  induction h with
  | refl => exact Star.refl _
  | tail _ l _ hstep ih => exact Star.tail ih ⟨l, hstep⟩

theorem starPred_and_left {α : Type u} {L : Type v} {r : LabeledARS α L}
    {P Q : L → Prop} {a b : α}
    (h : StarPred r (fun l => P l ∧ Q l) a b) : StarPred r P a b :=
  StarPred.mono (fun _ h => h.1) h

def Joinable {α : Type u} (r : Relation α) (a b : α) : Prop :=
  ∃ c, Star r a c ∧ Star r b c

def Confluent {α : Type u} (r : Relation α) : Prop :=
  ∀ a b c, Star r a b → Star r a c → Joinable r b c

def SemiConfluent {α : Type u} (r : Relation α) : Prop :=
  ∀ a b c, r a b → Star r a c → Joinable r b c

def LocallyDecreasing {α : Type u} {L : Type v}
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  ∀ a b c l₁ l₂, r l₁ a b → r l₂ a c →
    ∃ d,
      StarPred r (fun l => lt l l₁ ∧ lt l l₂) b d ∧
      StarPred r (fun l => lt l l₁ ∧ lt l l₂) c d

theorem joinable_of_starPred_lt {α : Type u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop} {l₀ : L}
    (hsemi : ∀ l, lt l l₀ → ∀ {a b c : α}, r l a b →
      Star (LabeledUnion r) a c → Joinable (LabeledUnion r) b c)
    {a b c : α} (hab : StarPred r (fun l => lt l l₀) a b)
    (hac : Star (LabeledUnion r) a c) : Joinable (LabeledUnion r) b c := by
  induction hab with
  | refl => exact ⟨c, hac, Star.refl c⟩
  | tail _ l hl hstep ih =>
      obtain ⟨d, hbd, hcd⟩ := ih
      obtain ⟨e, hbe, hde⟩ := hsemi l hl hstep hbd
      exact ⟨e, hbe, Star.trans hcd hde⟩

theorem semiConfluent_of_locallyDecreasing {α : Type u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop}
    (wf : WellFounded lt) (hld : LocallyDecreasing r lt) :
    SemiConfluent (LabeledUnion r) := by
  intro a b c hab hac
  obtain ⟨l₀, hab⟩ := hab
  have hlabel : ∀ l : L, ∀ {a b c : α},
      r l a b → Star (LabeledUnion r) a c →
        Joinable (LabeledUnion r) b c := by
    intro l
    refine WellFounded.induction (r := lt) wf (C := fun l => ∀ {a b c : α},
      r l a b → Star (LabeledUnion r) a c → Joinable (LabeledUnion r) b c) l ?_
    intro l ih a b c hab hac
    cases star_cases hac with
    | inl hEq =>
        subst c
        exact ⟨b, Star.refl b, Star.single ⟨l, hab⟩⟩
    | inr h =>
        obtain ⟨c₁, hac₁, hc₁c⟩ := h
        obtain ⟨l₂, hac₁⟩ := hac₁
        obtain ⟨d, hbd, hc₁d⟩ := hld a b c₁ l l₂ hab hac₁
        have hb_d : Star (LabeledUnion r) b d := starPred_to_star hbd
        have hc₁d_lt : StarPred r (fun l' => lt l' l) c₁ d :=
          starPred_and_left hc₁d
        obtain ⟨e, hde, hce⟩ :=
          joinable_of_starPred_lt (r := r) (lt := lt) (l₀ := l)
            (fun l' hl => ih l' hl) hc₁d_lt hc₁c
        exact ⟨e, Star.trans hb_d hde, hce⟩
  exact hlabel l₀ hab hac

theorem confluent_of_semiConfluent {α : Type u} {r : Relation α}
    (hsemi : SemiConfluent r) : Confluent r := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl => exact ⟨c, hac, Star.refl c⟩
  | tail hab hstep ih =>
      obtain ⟨d, hbd, hcd⟩ := ih (c := c) hac
      obtain ⟨e, hbe, hde⟩ := hsemi _ _ _ hstep hbd
      exact ⟨e, hbe, Star.trans hcd hde⟩

theorem confluent_of_locallyDecreasing {α : Type u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop}
    (wf : WellFounded lt) (hld : LocallyDecreasing r lt) :
    Confluent (LabeledUnion r) :=
  confluent_of_semiConfluent (semiConfluent_of_locallyDecreasing wf hld)

end Metatheory.Palomar433
