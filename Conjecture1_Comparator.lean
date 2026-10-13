
import Mathlib

open Real

noncomputable section

namespace StrictFormalConjecture1

def InS (x : ℝ) : Prop :=
  0 < |x| ∧ |x| ≤ 1.2 ∧
  ∃ (a₀ : ℕ) (a : ℕ → ℕ),
    (a₀ = 0 ∨ a₀ = 1) ∧
    (∀ n : ℕ, a n = 0 ∨ a n = 1) ∧
    (∀ N : ℕ, ∃ n ≥ N, a n = 1) ∧
    |x| = (a₀ : ℝ) +
      ∑' (n : ℕ), (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1)

def IsFiniteProductOfS (y : ℝ) : Prop :=
  ∃ (k : ℕ) (hk : 0 < k) (f : Fin k → ℝ),
    (∀ i : Fin k, InS (f i)) ∧
    (∏ i : Fin k, f i) = y

theorem Conjecture1 :
    ∀ (y : ℝ), y ≠ 0 → IsFiniteProductOfS y := by
  sorry

#check Conjecture1

end StrictFormalConjecture1
