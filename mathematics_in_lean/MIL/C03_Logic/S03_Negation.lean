import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by {
  unfold FnHasLb
  intro h'
  rcases h' with ⟨c, h'c⟩
  unfold FnLb at h'c
  specialize h c
  rcases h with ⟨d, hd⟩
  specialize h'c d
  linarith
}

example : ¬FnHasUb fun x ↦ x := by{
  unfold FnHasUb
  rintro ⟨c, hc⟩
  have : c + 1 ≤ c := hc (c + 1)
  linarith

}


#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by{
  apply lt_of_not_ge
  intro h1
  unfold Monotone at h
  apply h at h1
  apply not_le_of_gt at h'
  apply h' at h1
  exact h1

}

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by{
  intro hf
  apply hf at h
  apply not_le_of_gt at h
  exact h
  exact h'

}

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f' := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f' := by {
    unfold Monotone
    intro a b hab
    rfl
  }
  have h' : f' 1 ≤ f' 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith



example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by {
  apply le_of_not_gt
  intro hx
  specialize h x hx
  linarith

}

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by {
  intro x hx
  apply h
  use x

}

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by {
  rintro ⟨x, hx⟩
  specialize h x
  apply h at hx
  exact hx
}

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by{
  by_contra h'
  apply h
  intro x
  by_contra h''
  apply h'
  use x

}


example (h : ∃ x, ¬P x) : ¬∀ x, P x := by{
  intro ha
  rcases h with ⟨b, hb⟩
  specialize ha b
  exact hb ha
}

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by{
  by_contra h'
  exact h h'

}

example (h : Q) : ¬¬Q := by{
  rw[not_not]
  exact h

}

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by{
  intro a
  by_contra ha
  unfold FnHasUb at h; unfold FnUb at h
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro hx
  apply ha
  use x

}

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by {
  dsimp [Monotone] at h
  push_neg at h
  rcases h with ⟨b, b', hb⟩
  use b; use b'

}
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso -- turns the goal into false
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
