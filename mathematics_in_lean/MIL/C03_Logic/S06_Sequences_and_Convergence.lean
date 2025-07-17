import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by {
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have hn1 :n ≥ Ns := by {
    calc
      n ≥ Ns ⊔ Nt := by linarith
      _ ≥ Ns      := by exact Nat.le_max_left Ns Nt
  }
  have hn2 :n ≥ Nt := by {
    calc
      n ≥ Ns ⊔ Nt := by linarith
      _ ≥ Nt      := by exact Nat.le_max_right Ns Nt
  }
  specialize ht n hn2; specialize hs n hn1
  calc
    |s n + t n - (a + b)| = |(t n - b) + (s n - a)|  := by ring_nf
                        _ ≤ |t n - b| + |s n - a|    := by apply abs_add
                        _ < ε / 2 + ε / 2            := by linarith
                        _ = ε                        := by simp

  }

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by {
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  unfold ConvergesTo
  intro ε εpos
  unfold ConvergesTo at cs
  have εcpos : 0 < ε / |c| := by apply div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨N, hN⟩
  dsimp
  use N
  intro N' hN'
  specialize hN N' hN'
  have step₁ : |c| * |s N' - a| < |c| * (ε / |c|) := by {
    apply mul_lt_mul_of_pos_left<;>assumption

  }
  calc
    |c * s N' - c * a| = |c| * |s N' - a|   := by rw [← abs_mul, mul_sub]
                      _ < |c| * (ε / |c|)   := by {apply mul_lt_mul_of_pos_left<;>assumption}--(mul_lt_mul_of_pos_left (hN N' hN') acpos)
                      _ = ε                 := by {apply mul_div_cancel₀;exact abs_ne_zero.mpr h}



  }


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by{
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  specialize h n hn
  calc
    |s n| = |s n - a + a|   := by congr; ring
        _ ≤ |s n - a| + |a| := by apply abs_add
        _ < |a| + 1         := by linarith

  }


theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  have hn0 : n ≥ N₀ := le_of_max_le_left hn
  have hn1 : n ≥ N₁ := le_of_max_le_right hn
  specialize h₀ n hn0; specialize h₁ n hn1
  calc
    |s n * t n - 0| = |s n| * |t n - 0| := by rw [sub_zero, abs_mul, sub_zero]
                  _ < B * (ε / B)       := by{apply mul_lt_mul''; assumption; assumption;apply abs_nonneg; apply abs_nonneg;}
                  _ = ε                 := by{apply mul_div_cancel₀; exact Ne.symm (ne_of_lt Bpos)}


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by exact abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by {
    have hN1 : N ≥ Na := by exact Nat.le_max_left Na Nb
    exact hNa N hN1
  }
  have absb : |s N - b| < ε := by {
    have hN1 : N ≥ Nb := by exact Nat.le_max_right Na Nb
    exact hNb N hN1
  }
  have : |a - b| < |a - b| := by {
    calc
      |a - b| = |(-(s N - a)) + (s N - b)| := by congr; ring
            _ ≤ |(-(s N - a))| + |s N - b| := by apply abs_add
            _ = |s N - a| + |s N - b|      := by rw [abs_neg]
            _ < ε + ε                      := by linarith
            _ = |a - b|                    := by ring
  }

  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
