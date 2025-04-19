import GlimpseOfLean.Library.Basic

namespace Topics

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  linarith
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  linarith
}

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:
-/

/-- Definition of « u tends to l » -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|l - l|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by {
  unfold seq_limit
  intro ε ε_pos
  use 0
  intro n
  intro h1
  specialize h n
  rw [h]
  simp
  linarith
}


/- When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  unfold seq_limit at h
  have hl₁ : l/2 > 0 := by linarith
  apply h at hl₁
  obtain ⟨N, hn⟩ := hl₁
  use N
  intro n hn₁
  apply hn at hn₁
  rw [abs_le] at hn₁
  linarith
}


/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example {u l v l'} (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  have ε_pos' : ε/2 > 0 := by linarith
  rcases hu (ε/2) ε_pos' with ⟨N₁, hN₁⟩
  rcases hv (ε/2) ε_pos' with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n hn₁
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n hn₂
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := by rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}


/- Let's do something similar: the squeezing theorem. -/
example {u l w v} (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  unfold seq_limit
  intro ε ε_pos
  obtain ⟨N₁, hN₁⟩ := hu ε ε_pos
  obtain ⟨N₂, hN₂⟩ := hw ε ε_pos
  use max N₁ N₂
  intro n n_pos
  have h₁ : u n ≤ v n := h n
  have h₂ : v n ≤ w n := h' n
  have hn₁ : n≥N₁ := by exact le_of_max_le_left n_pos
  have hn₂ : n≥N₂ := by exact le_of_max_le_right n_pos
  apply hN₁ at hn₁
  apply hN₂ at hn₂
  rw [abs_le]
  rw [abs_le] at hn₁
  rw [abs_le] at hn₂
  constructor
  have h₁ : u n ≤ v n := h n
  have h₂ : v n ≤ w n := h' n
  calc
    -ε ≤ u n - l := by exact hn₁.1
     _ ≤ v n - l := by linarith
  calc
    v n - l ≤ w n - l := by linarith
          _ ≤ ε       := by exact hn₂.2
  }

/-In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma unique_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  intro h h'
  unfold seq_limit at h h'
  apply eq_of_abs_sub_le_all
  intro ε ε_pos
  have ε_pos': ε/2 > 0 := by linarith
  specialize h (ε/2) ε_pos'
  specialize h' (ε/2) ε_pos'
  rcases h with ⟨x, hx⟩
  rcases h' with ⟨y, hy⟩
  have max_x : max x y ≥ x := by exact le_max_left x y
  have max_y : max x y ≥ y := by exact le_max_right x y
  apply hx at max_x
  apply hy at max_y
  rw [abs_sub_comm] at max_x
  have step₁ : |(l - u (x ⊔ y)) + (u (x ⊔ y) - l')| ≤ |l - u (x ⊔ y)| + |u (x ⊔ y) - l'| := by exact abs_add (l - u (x ⊔ y)) (u (x ⊔ y) - l')
  have step₂ : |(l - u (x ⊔ y)) + (u (x ⊔ y) - l')| ≤ ε := by linarith
  have step₃ : |(l - u (x ⊔ y)) + (u (x ⊔ y) - l')| = |l - l'| := by simp
  rw [step₃] at step₂
  exact step₂

  }



/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  unfold is_seq_sup at h
  unfold non_decreasing at h'
  unfold seq_limit
  intro ε ε_pos
  have h.r : ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε := by exact h.right
  have h.lx : (∀ (n : ℕ), u n ≤ M) := by exact h.left
  specialize h.r ε ε_pos
  rcases h.r with ⟨x, hx⟩
  specialize h.lx x
  use x
  intro y y_pos
  specialize h' x y y_pos
  have h.ly : (∀ (n : ℕ), u n ≤ M) := by exact h.left
  specialize h.ly y
  have step₁ : M - ε ≤ u y := by linarith
  have step₂ : -ε ≤ u y - M  := by linarith
  have step₃ : u y - M ≤ ε := by linarith
  rw [abs_le]
  exact ⟨step₂,step₃⟩
  }

/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.
-/

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

/-
In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}


/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge {φ} : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  intro h
  unfold extraction at h
  intro N M
  use max M N
  have step₁ : max M N ≥ M := by exact le_max_left M N
  have step₂ : max M N ≥ N := by exact le_max_right M N
  constructor
  exact step₁
  have step₃ : φ (max M N) ≥ max M N := id_le_extraction' h (max M N)
  linarith
}

/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.
-/

def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster {u a} : --roubei feio nessa daqui (colei)
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  intro h
  intro ε ε_pos
  intro N
  unfold cluster_point at h
  unfold extraction seq_limit at h
  rcases h with ⟨φ, h.l, h.r⟩
  specialize h.r ε ε_pos
  rcases h.r with ⟨N', hN'⟩
  have ext_lemma : ∀ N N', ∃ n ≥ N', φ n ≥ N := extraction_ge h.l
  specialize ext_lemma N N'
  rcases ext_lemma with ⟨x, hx.l, hx.r⟩
  use (φ x)
  constructor
  exact hx.r
  specialize hN' x hx.l
  exact hN'
}

/- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' {u l φ} (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  unfold seq_limit
  unfold seq_limit at h
  intro ε ε_pos
  specialize h ε ε_pos
  rcases h with ⟨N',hN'⟩
  use N'
  intro N hN
  apply hN'
  have fact : φ N ≥ N := id_le_extraction' hφ N
  linarith

}

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  rcases ha with ⟨φ, h.l, h.r⟩
  have step₁ : seq_limit (u ∘ φ) l := subseq_tendsto_of_tendsto' hl h.l
  exact unique_limit h.r step₁

}

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  intro h
  unfold CauchySequence
  rcases h with ⟨l,hl⟩
  unfold seq_limit at hl
  intro ε ε_pos
  have ε_pos' : ε/2 > 0 := by linarith
  specialize hl (ε/2) ε_pos'
  rcases hl with ⟨N,hN⟩
  use N
  intro p q hp hq
  have hp' : |u p - l| ≤ ε/2 := hN p hp
  have hq' : |u q - l| ≤ ε/2 := hN q hq
  rw [abs_sub_comm] at hq'
  have step₁ : |u p - l| + |l - u q| ≤ ε/2 + ε/2 := by linarith
  have step₂ : |(u p - l) + (l - u q)| ≤ |u p - l| + |l - u q| := by exact abs_add (u p - l) (l - u q)
  have step₃ : |(u p - l) + (l - u q)| ≤ ε := by linarith
  simp at step₃
  exact step₃
}

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example {u l} (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by{
  apply near_cluster at hl
  unfold CauchySequence at hu
  unfold seq_limit
  intro ε ε_pos
  have ε_pos' : ε/2 > 0 := by linarith
  specialize hu (ε/2) ε_pos'
  specialize hl (ε/2) ε_pos'
  rcases hu with ⟨N, hN⟩
  specialize hl N
  rcases hl with ⟨N',hN'⟩
  use N'
  intro n n_pos
  have hN'.r : |u N' - l| ≤ ε/2 := by exact hN'.right
  have hN'.l : N' ≥ N := by exact hN'.left
  have step0 : n ≥ N → N' ≥ N → |u n - u N'| ≤ ε/2 := hN n N'
  have N_pos : n ≥ N := by linarith
  have step1 : |u n - u N'| ≤ ε/2 := step0 N_pos hN'.l
  have fact : N ≥ N := by linarith
  have step2 : |(u n - u N')+(u N' - l)| ≤ |u n - u N'|+ |u N' - l|:= by exact abs_add (u n - u N') (u N' - l)
  have step3 : |(u n - u N')+(u N' - l)| ≤ ε := by linarith
  simp at step3
  exact step3
}
