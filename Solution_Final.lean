import Mathlib

open Real BigOperators Finset

noncomputable section

/-!
======================================================================
  前置工具箱（来自你的第四部分，全部 0 sorry）
======================================================================
-/

lemma prod_le_prod_of_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (hle : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction' s using Finset.induction_on with a s ha ih
  · simp
  · rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have hfga : f a ≤ g a := hle a (Finset.mem_insert_self a s)
    have h0_s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hle_s : ∀ i ∈ s, f i ≤ g i := fun i hi => hle i (Finset.mem_insert_of_mem hi)
    have ih_le := ih h0_s hle_s
    have h_prod_f_nonneg : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg h0_s
    nlinarith

lemma prod_update_sub_prod (f : Fin 20 → ℝ) (j : Fin 20) (ε : ℝ) :
    (∏ k, Function.update f j (f j + ε) k) - (∏ k, f k) =
      ε * ∏ k ∈ Finset.univ.erase j, f k := by
  have hj : j ∈ (Finset.univ : Finset (Fin 20)) := Finset.mem_univ j
  have h_not : j ∉ Finset.univ.erase j := by simp
  set g := Function.update f j (f j + ε)
  have hg_prod : (∏ k, g k) = g j * ∏ k ∈ Finset.univ.erase j, g k := by
    nth_rw 1 [← Finset.insert_erase hj]
    exact Finset.prod_insert h_not
  have hf_prod : (∏ k, f k) = f j * ∏ k ∈ Finset.univ.erase j, f k := by
    nth_rw 1 [← Finset.insert_erase hj]
    exact Finset.prod_insert h_not
  have h_same : g j = f j + ε := by simp [g]
  have h_erase : (∏ k ∈ Finset.univ.erase j, g k) = (∏ k ∈ Finset.univ.erase j, f k) := by
    apply Finset.prod_congr rfl
    intro k hk
    have h_ne : k ≠ j := by
      intro h
      subst h
      exact h_not hk
    simp [g, h_ne]
  rw [hg_prod, hf_prod, h_same, h_erase]
  ring

lemma prod_erase_ge_one (f : Fin 20 → ℝ)
    (hf_ge : ∀ k, 1 ≤ f k) (j : Fin 20) :
    1 ≤ ∏ k ∈ Finset.univ.erase j, f k := by
  have h_one : (∏ k ∈ Finset.univ.erase j, (1 : ℝ)) = 1 := by simp
  rw [← h_one]
  apply prod_le_prod_of_nonneg
  · intro _ _
    norm_num
  · intro k _
    exact hf_ge k

lemma prod_erase_le_const (f : Fin 20 → ℝ)
    (hf_ge : ∀ k, 1 ≤ f k)
    (hf_le : ∀ k, f k ≤ 1 + 1 / 900)
    (j : Fin 20) :
    ∏ k ∈ Finset.univ.erase j, f k ≤ 1.03 := by
  have h_nonneg : ∀ k ∈ Finset.univ.erase j, (0 : ℝ) ≤ f k := by
    intro k _
    have := hf_ge k
    linarith
  have h_le_const : ∏ k ∈ Finset.univ.erase j, f k ≤
      ∏ k ∈ Finset.univ.erase j, (1 + 1 / 900 : ℝ) := by
    apply prod_le_prod_of_nonneg (Finset.univ.erase j) f (fun _ => (1 + 1 / 900 : ℝ)) h_nonneg
    intro k _
    exact hf_le k
  have h_card : (Finset.univ.erase j).card = 19 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
    rfl
  rw [Finset.prod_const, h_card] at h_le_const
  have h_num : (1 + 1 / 900 : ℝ) ^ 19 ≤ 1.03 := by norm_num
  linarith

theorem single_step_increment_bounds (f : Fin 20 → ℝ)
    (hf_ge : ∀ k, 1 ≤ f k)
    (hf_le : ∀ k, f k ≤ 1 + 1 / 900)
    (j : Fin 20) (ε : ℝ) (hε : 0 ≤ ε) :
    ε ≤ (∏ k, Function.update f j (f j + ε) k) - (∏ k, f k) ∧
    (∏ k, Function.update f j (f j + ε) k) - (∏ k, f k) ≤ 1.03 * ε := by
  have h_diff := prod_update_sub_prod f j ε
  rw [h_diff]
  have h_prod_ge := prod_erase_ge_one f hf_ge j
  have h_prod_le := prod_erase_le_const f hf_ge hf_le j
  constructor
  · nlinarith
  · nlinarith

/-!
======================================================================
  【里程碑 A】顶级规范化定义与代数引理
======================================================================
-/

/-- 前 s 个因子置 1，其余置 0 -/
def prefix_bits (s : ℕ) (j : Fin 20) : ℕ :=
  if j.val < s then 1 else 0

lemma prefix_bits_binary (s : ℕ) (j : Fin 20) :
    prefix_bits s j = 0 ∨ prefix_bits s j = 1 := by
  dsimp [prefix_bits]
  split_ifs <;> [right; left] <;> rfl

lemma prefix_bits_succ_eq (s : ℕ) (j : Fin 20) (h : j.val ≠ s) :
    prefix_bits (s + 1) j = prefix_bits s j := by
  dsimp [prefix_bits]
  split_ifs with h1 h2
  · rfl
  · omega
  · omega
  · rfl

lemma prefix_bits_succ_self (s : ℕ) (hs : s < 20) :
    prefix_bits (s + 1) ⟨s, hs⟩ = 1 := by
  dsimp [prefix_bits]
  split_ifs with h
  · rfl
  · omega

lemma prefix_bits_self (s : ℕ) (hs : s < 20) :
    prefix_bits s ⟨s, hs⟩ = 0 := by
  dsimp [prefix_bits]
  split_ifs with h
  · omega
  · rfl

/-- 前 s 个分量加 ε 的新向量 -/
def update_prefix (f : Fin 20 → ℝ) (ε : ℝ) (s : ℕ) : Fin 20 → ℝ :=
  fun j => f j + (prefix_bits s j : ℝ) * ε

lemma update_prefix_zero (f : Fin 20 → ℝ) (ε : ℝ) :
    update_prefix f ε 0 = f := by
  ext k
  dsimp [update_prefix, prefix_bits]
  ring

lemma update_prefix_succ (f : Fin 20 → ℝ) (ε : ℝ) (s : ℕ) (hs : s < 20) :
    update_prefix f ε (s + 1) =
      Function.update (update_prefix f ε s) ⟨s, hs⟩ (update_prefix f ε s ⟨s, hs⟩ + ε) := by
  ext j
  by_cases hj : j = ⟨s, hs⟩
  · subst hj
    rw [Function.update_self]
    dsimp [update_prefix]
    rw [prefix_bits_succ_self s hs, prefix_bits_self s hs]
    ring
  · have hj_val : j.val ≠ s := by
      intro h
      apply hj
      ext
      exact h
    rw [Function.update_of_ne hj]
    dsimp [update_prefix]
    rw [prefix_bits_succ_eq s j hj_val]

/-- 连乘积映射 -/
def prefix_prod (f : Fin 20 → ℝ) (ε : ℝ) (s : ℕ) : ℝ :=
  ∏ k, update_prefix f ε s k

lemma prefix_prod_zero (f : Fin 20 → ℝ) (ε : ℝ) :
    prefix_prod f ε 0 = ∏ k, f k := by
  dsimp [prefix_prod]
  rw [update_prefix_zero]

lemma prefix_prod_step (f : Fin 20 → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hf_ge : ∀ k, 1 ≤ f k) (hf_le : ∀ k, f k + ε ≤ 1 + 1 / 900)
    (s : ℕ) (hs : s < 20) :
    ε ≤ prefix_prod f ε (s + 1) - prefix_prod f ε s ∧
    prefix_prod f ε (s + 1) - prefix_prod f ε s ≤ 1.03 * ε := by
  dsimp [prefix_prod]
  rw [update_prefix_succ f ε s hs]
  have hg_ge : ∀ k, 1 ≤ update_prefix f ε s k := by
    intro k
    dsimp [update_prefix]
    have := hf_ge k
    rcases prefix_bits_binary s k with h0 | h1
    · simp [h0]; linarith
    · simp [h1]; linarith
  have hg_le : ∀ k, update_prefix f ε s k ≤ 1 + 1 / 900 := by
    intro k
    dsimp [update_prefix]
    have := hf_le k
    rcases prefix_bits_binary s k with h0 | h1
    · simp [h0]; linarith
    · simp [h1]; linarith
  exact single_step_increment_bounds (update_prefix f ε s) hg_ge hg_le ⟨s, hs⟩ ε hε

lemma prefix_prod_ge (f : Fin 20 → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hf_ge : ∀ k, 1 ≤ f k) (hf_le : ∀ k, f k + ε ≤ 1 + 1 / 900) :
    ∀ (s : ℕ), s ≤ 20 → (∏ k, f k) + (s : ℝ) * ε ≤ prefix_prod f ε s
  | 0, _ => by
    rw [prefix_prod_zero]
    simp
  | s + 1, hs => by
    have hs_lt : s < 20 := by omega
    have ih := prefix_prod_ge f ε hε hf_ge hf_le s (by omega)
    have h_step := (prefix_prod_step f ε hε hf_ge hf_le s hs_lt).1
    push_cast
    linarith

/-!
======================================================================
  离散介值截断引理
======================================================================
-/

lemma exists_step_cut (P : ℕ → ℝ) (x : ℝ) :
    ∀ n, P 0 ≤ x → x < P n → ∃ s < n, P s ≤ x ∧ x < P (s + 1)
  | 0, h0, hn => by linarith
  | n + 1, h0, hn => by
    by_cases h : P n ≤ x
    · exact ⟨n, Nat.lt_succ_self n, h, hn⟩
    · have h_gt : x < P n := not_le.mp h
      obtain ⟨s, hs, hs_le, hs_succ⟩ := exists_step_cut P x n h0 h_gt
      exact ⟨s, by omega, hs_le, hs_succ⟩

/-!
======================================================================
  【核心攻克目标】：single_step_greedy_leap（全部 0 sorry 完成）
======================================================================
-/

theorem single_step_greedy_leap (f : Fin 20 → ℝ) (ε : ℝ) (hε_pos : 0 < ε)
    (hf_ge : ∀ k, 1 ≤ f k) (hf_le : ∀ k, f k + ε ≤ 1 + 1 / 900)
    (x : ℝ) (h_prod_le : ∏ k, f k ≤ x)
    (hε_bound : x - (∏ k, f k) ≤ 10.3 * ε) :
    ∃ (s : ℕ), s ≤ 20 ∧
      prefix_prod f ε s ≤ x ∧
      x - prefix_prod f ε s ≤ 1.03 * ε := by
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hP0_le : prefix_prod f ε 0 ≤ x := by
    rw [prefix_prod_zero]
    exact h_prod_le
  -- 全加满 20 步后的增量必定越过 x（直接传递性）
  have hP20_gt : x < prefix_prod f ε 20 := by
    have h_ge20 := prefix_prod_ge f ε hε_nonneg hf_ge hf_le 20 le_rfl
    push_cast at h_ge20
    have h_gt : x < (∏ k, f k) + (20 : ℝ) * ε := by
      have : (10.3 : ℝ) < 20 := by norm_num
      nlinarith
    exact lt_of_lt_of_le h_gt h_ge20
  obtain ⟨s_star, hs_lt20, hs_le_x, hs_succ_gt_x⟩ :=
    exists_step_cut (prefix_prod f ε) x 20 hP0_le hP20_gt
  have hs_le20 : s_star ≤ 20 := by omega
  refine ⟨s_star, hs_le20, hs_le_x, ?_⟩
  have h_step_bound := (prefix_prod_step f ε hε_nonneg hf_ge hf_le s_star hs_lt20).2
  linarith


/-!
======================================================================
  Strict crossing helpers for the attempted proof of test.lean's axiom.

  Unlike `exists_step_cut`, the strict version keeps the left endpoint
  strictly below x. This prevents the residual from becoming zero, which
  is essential when every digit sequence must contain infinitely many 1s.
======================================================================
-/

lemma exists_step_cut_strict (P : ℕ → ℝ) (x : ℝ) :
    ∀ n, P 0 < x → x ≤ P n → ∃ s < n, P s < x ∧ x ≤ P (s + 1)
  | 0, h0, hn => by
      linarith
  | n + 1, h0, hn => by
      by_cases h : P n < x
      · exact ⟨n, Nat.lt_succ_self n, h, hn⟩
      · have hxn : x ≤ P n := le_of_not_gt h
        obtain ⟨s, hs, hs_left, hs_right⟩ := exists_step_cut_strict P x n h0 hxn
        exact ⟨s, by omega, hs_left, hs_right⟩

theorem single_step_greedy_leap_strict (f : Fin 20 → ℝ) (ε : ℝ) (hε_pos : 0 < ε)
    (hf_ge : ∀ k, 1 ≤ f k) (hf_le : ∀ k, f k + ε ≤ 1 + 1 / 900)
    (x : ℝ) (h_prod_lt : (∏ k, f k) < x)
    (hε_bound : x - (∏ k, f k) ≤ 10.3 * ε) :
    ∃ (s : ℕ), s ≤ 20 ∧
      prefix_prod f ε s < x ∧
      x ≤ prefix_prod f ε (s + 1) ∧
      x - prefix_prod f ε s ≤ 1.03 * ε := by
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hP0_lt : prefix_prod f ε 0 < x := by
    rw [prefix_prod_zero]
    exact h_prod_lt
  have h_ge20 := prefix_prod_ge f ε hε_nonneg hf_ge hf_le 20 le_rfl
  have hratio : (10.3 : ℝ) < 20 := by norm_num
  have hscaled : 10.3 * ε < (20 : ℝ) * ε :=
    mul_lt_mul_of_pos_right hratio hε_pos
  have h_gt : x < (∏ k, f k) + (20 : ℝ) * ε := by
    linarith
  have hP20_gt : x < prefix_prod f ε 20 := by
    exact lt_of_lt_of_le h_gt h_ge20
  obtain ⟨s, hs_lt20, hs_left, hs_right⟩ :=
    exists_step_cut_strict (prefix_prod f ε) x 20 hP0_lt (le_of_lt hP20_gt)
  refine ⟨s, by omega, hs_left, hs_right, ?_⟩
  have h_step_bound := (prefix_prod_step f ε hε_nonneg hf_ge hf_le s hs_lt20).2
  linarith

#print axioms single_step_greedy_leap


open Real BigOperators Finset Filter Topology

noncomputable section

namespace StrictFormalConjecture1

/-!
======================================================================
  第一部分：核心概念定义（原题定义，原汁原味）
======================================================================
-/

/-- 属于题设集合 S 的条件 -/
def InS (x : ℝ) : Prop :=
  0 < |x| ∧ |x| ≤ 1.2 ∧
  ∃ (a₀ : ℕ) (a : ℕ → ℕ),
    (a₀ = 0 ∨ a₀ = 1) ∧
    (∀ n : ℕ, a n = 0 ∨ a n = 1) ∧
    (∀ N : ℕ, ∃ n ≥ N, a n = 1) ∧
    |x| = (a₀ : ℝ) + ∑' (n : ℕ), (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1)

/-- 有限个 S 中元素的乘积；定义与 Comparator 目标代码一致。 -/
def IsFiniteProductOfS (y : ℝ) : Prop :=
  ∃ (k : ℕ) (_hk : 0 < k) (f : Fin k → ℝ),
    (∀ i : Fin k, InS (f i)) ∧ (∏ i : Fin k, f i) = y

/-- Conjecture 1 的原命题形式。 -/
def Conjecture1Statement : Prop :=
  ∀ (y : ℝ), y ≠ 0 → IsFiniteProductOfS y

/-- S 中几个元素连乘生成的乘法半群 -/
inductive InP : ℝ → Prop where
  | of_S {x : ℝ} (hx : InS x) : InP x
  | mul {x y : ℝ} (hx : InP x) (hy : InP y) : InP (x * y)


/-!
======================================================================
  第二部分：你已完成的前三步工具箱
======================================================================
-/

theorem step1_scalar_greedy_step (ε : ℝ) (hε : 0 < ε) (Δ : ℝ)
    (hΔ_ge : 0 ≤ Δ) (hΔ_le : Δ ≤ 10 * ε) :
    ∃ (s : ℕ), s ≤ 10 ∧ |Δ - (s : ℝ) * ε| ≤ ε := by
  have h_div_nonneg : 0 ≤ Δ / ε := div_nonneg hΔ_ge (le_of_lt hε)
  have h_div_le : Δ / ε ≤ 10 := (div_le_iff₀ hε).mpr hΔ_le
  set s := Nat.floor (Δ / ε)
  have hs_real : (s : ℝ) ≤ 10 := le_trans (Nat.floor_le h_div_nonneg) h_div_le
  have hs_le : s ≤ 10 := by exact_mod_cast hs_real
  refine ⟨s, hs_le, ?_⟩
  have hs_le_val : (s : ℝ) ≤ Δ / ε := Nat.floor_le h_div_nonneg
  have h_lt_succ : Δ / ε < (s : ℝ) + 1 := Nat.lt_floor_add_one (Δ / ε)
  have h_sub_nonneg : 0 ≤ Δ - (s : ℝ) * ε := by
    have h_mul := (le_div_iff₀ hε).mp hs_le_val
    linarith
  have h_sub_le : Δ - (s : ℝ) * ε ≤ ε := by
    have h_mul := (div_lt_iff₀ hε).mp h_lt_succ
    linarith
  rw [abs_le]
  constructor <;> linarith

lemma step2_decompose_bits : ∀ (m s : ℕ), s ≤ m →
    ∃ (b : Fin m → ℕ), (∀ j, b j = 0 ∨ b j = 1) ∧ (∑ j, b j) = s
  | 0, s, hs => by
    have hs0 : s = 0 := Nat.le_zero.mp hs
    subst hs0
    refine ⟨Fin.elim0, fun j => j.elim0, by rw [Fin.sum_univ_zero]⟩
  | m + 1, s, hs => by
    rcases lt_or_ge s (m + 1) with h_lt | h_ge
    · have hs_le_m : s ≤ m := Nat.lt_succ_iff.mp h_lt
      obtain ⟨b', hb'_range, hb'_sum⟩ := step2_decompose_bits m s hs_le_m
      refine ⟨Fin.cons 0 b', ?_, ?_⟩
      · rw [Fin.forall_fin_succ]
        exact ⟨Or.inl rfl, hb'_range⟩
      · rw [Fin.sum_cons, hb'_sum, zero_add]
    · have hs_eq : s = m + 1 := le_antisymm hs h_ge
      obtain ⟨b', hb'_range, hb'_sum⟩ := step2_decompose_bits m m le_rfl
      subst hs_eq
      refine ⟨Fin.cons 1 b', ?_, ?_⟩
      · rw [Fin.forall_fin_succ]
        exact ⟨Or.inr rfl, hb'_range⟩
      · rw [Fin.sum_cons, hb'_sum, add_comm]

theorem step2_sequence_decomposition (s : ℕ → ℕ) (hs : ∀ n, s n ≤ 10) :
    ∃ (a : Fin 10 → ℕ → ℕ),
      (∀ j n, a j n = 0 ∨ a j n = 1) ∧
      (∀ n, ∑ j : Fin 10, a j n = s n) := by
  choose b hb_range hb_sum using fun n => step2_decompose_bits 10 (s n) (hs n)
  refine ⟨fun j n => b n j, fun j n => hb_range n j, fun n => hb_sum n⟩

theorem step3_fin_prod_in_InP : ∀ {m : ℕ} (_hm : 0 < m) (f : Fin m → ℝ),
    (∀ j, InS (f j)) → InP (∏ j, f j)
  | 1, _, f, hf => by
    rw [Fin.prod_univ_one]
    exact InP.of_S (hf 0)
  | m + 2, _, f, hf => by
    rw [Fin.prod_univ_succ]
    have h0 : InP (f 0) := InP.of_S (hf 0)
    have h_rest : InP (∏ i : Fin (m + 1), f i.succ) :=
      step3_fin_prod_in_InP (Nat.succ_pos m) (fun i => f i.succ) (fun i => hf i.succ)
    exact InP.mul h0 h_rest


/-!
======================================================================
  第三部分：单因子入集系统（0 sorry）
======================================================================
-/

lemma ten_inv_nonneg : (0 : ℝ) ≤ (10 : ℝ)⁻¹ := by norm_num

lemma ten_inv_lt_one : (10 : ℝ)⁻¹ < (1 : ℝ) := by norm_num

lemma hasSum_pow_ten_inv :
    HasSum (fun n : ℕ => ((10 : ℝ)⁻¹) ^ n) (10 / 9) := by
  have h := hasSum_geometric_of_lt_one ten_inv_nonneg ten_inv_lt_one
  convert h using 1
  norm_num

lemma hasSum_ten_inv_pow_succ :
    HasSum (fun n : ℕ => ((10 : ℝ)⁻¹) ^ (n + 1)) (1 / 9) := by
  have h := hasSum_pow_ten_inv.mul_left ((10 : ℝ)⁻¹)
  have h_eq : (fun n : ℕ => (10 : ℝ)⁻¹ * ((10 : ℝ)⁻¹) ^ n) = (fun n : ℕ => ((10 : ℝ)⁻¹) ^ (n + 1)) := by
    ext n
    rw [← pow_succ']
  rw [h_eq] at h
  have h_num : (10 : ℝ)⁻¹ * (10 / 9) = (1 / 9 : ℝ) := by norm_num
  rw [h_num] at h
  exact h

lemma summable_ten_inv_pow_succ : Summable (fun n : ℕ => ((10 : ℝ)⁻¹) ^ (n + 1)) :=
  hasSum_ten_inv_pow_succ.summable

lemma tsum_ten_inv_pow_succ :
    (∑' (n : ℕ), ((10 : ℝ)⁻¹) ^ (n + 1)) = 1 / 9 :=
  hasSum_ten_inv_pow_succ.tsum_eq

lemma digit_le_one (a : ℕ → ℕ) (ha_bin : ∀ n, a n = 0 ∨ a n = 1) (n : ℕ) :
    (a n : ℝ) ≤ 1 := by
  rcases ha_bin n with h0 | h1
  · rw [h0]; norm_num
  · rw [h1]; norm_num

lemma summable_digit_series (a : ℕ → ℕ) (ha_bin : ∀ n, a n = 0 ∨ a n = 1) :
    Summable (fun n : ℕ => (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1)) := by
  have h_nonneg : ∀ n, 0 ≤ (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1) := fun _ => by positivity
  have h_le : ∀ n, (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1) ≤ ((10 : ℝ)⁻¹) ^ (n + 1) := by
    intro n
    have h_pow_nonneg : 0 ≤ ((10 : ℝ)⁻¹) ^ (n + 1) := by positivity
    have h_mul := mul_le_mul_of_nonneg_right (digit_le_one a ha_bin n) h_pow_nonneg
    rwa [one_mul] at h_mul
  exact Summable.of_nonneg_of_le h_nonneg h_le summable_ten_inv_pow_succ

lemma tsum_digit_nonneg (a : ℕ → ℕ) :
    0 ≤ ∑' (n : ℕ), (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1) :=
  tsum_nonneg (fun _ => by positivity)

lemma tsum_digit_le_one_ninth (a : ℕ → ℕ) (ha_bin : ∀ n, a n = 0 ∨ a n = 1) :
    (∑' (n : ℕ), (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1)) ≤ 1 / 9 := by
  have h_le : ∀ n : ℕ, (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1) ≤ ((10 : ℝ)⁻¹) ^ (n + 1) := by
    intro n
    have h_pow_nonneg : 0 ≤ ((10 : ℝ)⁻¹) ^ (n + 1) := by positivity
    have h_mul := mul_le_mul_of_nonneg_right (digit_le_one a ha_bin n) h_pow_nonneg
    rwa [one_mul] at h_mul
  exact hasSum_le h_le (summable_digit_series a ha_bin).hasSum hasSum_ten_inv_pow_succ

lemma periodic_infinite_ones (period offset : ℕ) (hp : 0 < period)
    (a : ℕ → ℕ) (h_per : ∀ k : ℕ, a (period * (k + 1) + offset) = 1) :
    ∀ N : ℕ, ∃ n ≥ N, a n = 1 := by
  intro N
  use period * (N + 1) + offset
  constructor
  · have h_mul : N + 1 ≤ period * (N + 1) := by
      have hp_ge : 1 ≤ period := hp
      nlinarith
    omega
  · exact h_per N

theorem factor_satisfies_InS (a : ℕ → ℕ)
    (ha_bin : ∀ n, a n = 0 ∨ a n = 1)
    (ha_inf : ∀ N, ∃ n ≥ N, a n = 1) :
    InS (1 + ∑' (n : ℕ), (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1)) := by
  set S := ∑' (n : ℕ), (a n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1)
  have hS_nonneg : 0 ≤ S := tsum_digit_nonneg a
  have hS_le : S ≤ 1 / 9 := tsum_digit_le_one_ninth a ha_bin
  set x := 1 + S
  have hx_ge_one : 1 ≤ x := by
    dsimp [x]
    linarith
  have hx_pos : 0 < x := by linarith
  have hx_abs : |x| = x := abs_of_pos hx_pos
  have hx_le_12 : |x| ≤ 1.2 := by
    rw [hx_abs]
    dsimp [x]
    have h12 : (1 : ℝ) + 1 / 9 ≤ 1.2 := by norm_num
    linarith
  refine ⟨?_, hx_le_12, ?_⟩
  · rw [hx_abs]; linarith
  · refine ⟨1, a, Or.inr rfl, ha_bin, ha_inf, ?_⟩
    rw [hx_abs]
    dsimp [x, S]
    push_cast
    rfl


/-!
======================================================================
  第四部分：多因子乘积网络与摄动控制系统（0 sorry）
======================================================================
-/

lemma prod_le_prod_of_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (hle : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction' s using Finset.induction_on with a s ha ih
  · simp
  · rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have hfga : f a ≤ g a := hle a (Finset.mem_insert_self a s)
    have h0_s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hle_s : ∀ i ∈ s, f i ≤ g i := fun i hi => hle i (Finset.mem_insert_of_mem hi)
    have ih_le := ih h0_s hle_s
    have h_prod_f_nonneg : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg h0_s
    nlinarith

lemma prod_update_sub_prod (f : Fin 20 → ℝ) (j : Fin 20) (ε : ℝ) :
    (∏ k, Function.update f j (f j + ε) k) - (∏ k, f k) =
      ε * ∏ k ∈ Finset.univ.erase j, f k := by
  have hj : j ∈ (Finset.univ : Finset (Fin 20)) := Finset.mem_univ j
  have h_not : j ∉ Finset.univ.erase j := by simp
  set g := Function.update f j (f j + ε)
  have hg_prod : (∏ k, g k) = g j * ∏ k ∈ Finset.univ.erase j, g k := by
    nth_rw 1 [← Finset.insert_erase hj]
    exact Finset.prod_insert h_not
  have hf_prod : (∏ k, f k) = f j * ∏ k ∈ Finset.univ.erase j, f k := by
    nth_rw 1 [← Finset.insert_erase hj]
    exact Finset.prod_insert h_not
  have h_same : g j = f j + ε := by simp [g]
  have h_erase : (∏ k ∈ Finset.univ.erase j, g k) = (∏ k ∈ Finset.univ.erase j, f k) := by
    apply Finset.prod_congr rfl
    intro k hk
    have h_ne : k ≠ j := by
      intro h
      subst h
      exact h_not hk
    simp [g, h_ne]
  rw [hg_prod, hf_prod, h_same, h_erase]
  ring

lemma prod_erase_ge_one (f : Fin 20 → ℝ)
    (hf_ge : ∀ k, 1 ≤ f k) (j : Fin 20) :
    1 ≤ ∏ k ∈ Finset.univ.erase j, f k := by
  have h_one : (∏ k ∈ Finset.univ.erase j, (1 : ℝ)) = 1 := by simp
  rw [← h_one]
  apply prod_le_prod_of_nonneg
  · intro _ _
    norm_num
  · intro k _
    exact hf_ge k

lemma prod_erase_le_const (f : Fin 20 → ℝ)
    (hf_ge : ∀ k, 1 ≤ f k)
    (hf_le : ∀ k, f k ≤ 1 + 1 / 900)
    (j : Fin 20) :
    ∏ k ∈ Finset.univ.erase j, f k ≤ 1.03 := by
  have h_nonneg : ∀ k ∈ Finset.univ.erase j, (0 : ℝ) ≤ f k := by
    intro k _
    have := hf_ge k
    linarith
  have h_le_const : ∏ k ∈ Finset.univ.erase j, f k ≤
      ∏ k ∈ Finset.univ.erase j, (1 + 1 / 900 : ℝ) := by
    apply prod_le_prod_of_nonneg (Finset.univ.erase j) f (fun _ => (1 + 1 / 900 : ℝ)) h_nonneg
    intro k _
    exact hf_le k
  have h_card : (Finset.univ.erase j).card = 19 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
    rfl
  rw [Finset.prod_const, h_card] at h_le_const
  have h_num : (1 + 1 / 900 : ℝ) ^ 19 ≤ 1.03 := by norm_num
  linarith

theorem single_step_increment_bounds (f : Fin 20 → ℝ)
    (hf_ge : ∀ k, 1 ≤ f k)
    (hf_le : ∀ k, f k ≤ 1 + 1 / 900)
    (j : Fin 20) (ε : ℝ) (hε : 0 ≤ ε) :
    ε ≤ (∏ k, Function.update f j (f j + ε) k) - (∏ k, f k) ∧
    (∏ k, Function.update f j (f j + ε) k) - (∏ k, f k) ≤ 1.03 * ε := by
  have h_diff := prod_update_sub_prod f j ε
  rw [h_diff]
  have h_prod_ge := prod_erase_ge_one f hf_ge j
  have h_prod_le := prod_erase_le_const f hf_ge hf_le j
  constructor
  · nlinarith
  · nlinarith

theorem discrete_step_le_tail_span (n : ℕ) :
    (1.03 : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1) < (19 / 9 : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1) := by
  have h_pow_pos : 0 < (10 : ℝ)⁻¹ ^ (n + 1) := by positivity
  have h_ratio : (1.03 : ℝ) < 19 / 9 := by norm_num
  exact mul_lt_mul_of_pos_right h_ratio h_pow_pos


/-!
======================================================================
  第五部分：对原自定义公理进行构造性替换
======================================================================
-/

/-- 20 个因子的具体解析式映射 -/
def factor_of_bits (a : Fin 20 → ℕ → ℕ) (j : Fin 20) : ℝ :=
  1 + ∑' (n : ℕ), (a j n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1)

/-- 截断有限前 N 项部分和因子 -/
def factor_partial (a : Fin 20 → ℕ → ℕ) (j : Fin 20) (N : ℕ) : ℝ :=
  1 + ∑ n ∈ range N, (a j n : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1)

lemma all_factors_satisfy_InS (a : Fin 20 → ℕ → ℕ)
    (ha_bin : ∀ j n, a j n = 0 ∨ a j n = 1)
    (ha_inf : ∀ j N, ∃ n ≥ N, a j n = 1) :
    ∀ j : Fin 20, InS (factor_of_bits a j) := by
  intro j
  exact factor_satisfies_InS (a j) (ha_bin j) (ha_inf j)

theorem inP_of_bits_product (a : Fin 20 → ℕ → ℕ)
    (ha_bin : ∀ j n, a j n = 0 ∨ a j n = 1)
    (ha_inf : ∀ j N, ∃ n ≥ N, a j n = 1)
    (x : ℝ) (hx : (∏ j : Fin 20, factor_of_bits a j) = x) :
    InP x := by
  rw [← hx]
  have h_inS := all_factors_satisfy_InS a ha_bin ha_inf
  have h_pos : 0 < (20 : ℕ) := by norm_num
  exact step3_fin_prod_in_InP h_pos (factor_of_bits a) h_inS

def targetA : ℝ := 1.002
def targetB : ℝ := 1.003

lemma target_interval_valid : 1 < targetA ∧ targetA < targetB := by
  dsimp [targetA, targetB]
  constructor <;> norm_num

/-- 截断部分积收敛至无限连乘积 -/
lemma tendsto_partial_prod_to_inf_prod (a : Fin 20 → ℕ → ℕ)
    (ha_bin : ∀ j n, a j n = 0 ∨ a j n = 1) :
    Tendsto (fun N : ℕ => ∏ j : Fin 20, factor_partial a j N) atTop
      (𝓝 (∏ j : Fin 20, factor_of_bits a j)) := by
  have h_factor_tendsto : ∀ j : Fin 20,
      Tendsto (fun N : ℕ => factor_partial a j N) atTop (𝓝 (factor_of_bits a j)) := by
    intro j
    dsimp [factor_partial, factor_of_bits]
    have h_hasSum := (summable_digit_series (a j) (ha_bin j)).hasSum
    have h_lim := h_hasSum.tendsto_sum_nat
    exact Tendsto.const_add 1 h_lim
  exact tendsto_finsetProd Finset.univ (fun j _ => h_factor_tendsto j)

/-!
======================================================================
  A constructive attempt at replacing `exists_bits_for_target_axiom`.
  The state advances one decimal place per round. A cyclic cursor assigns
  each chosen digit to a cyclic interval of factor indices.
======================================================================
-/

def digitEps (n : ℕ) : ℝ := (1 / 10 : ℝ) ^ (n + 3)

lemma digitEps_pos (n : ℕ) : 0 < digitEps n := by
  change 0 < (1 / 10 : ℝ) ^ (n + 3)
  positivity

lemma digitEps_succ (n : ℕ) : digitEps (n + 1) = digitEps n / 10 := by
  change (1 / 10 : ℝ) ^ ((n + 1) + 3) = (1 / 10 : ℝ) ^ (n + 3) / 10
  have hexp : (n + 1) + 3 = (n + 3) + 1 := by omega
  rw [hexp, pow_succ]
  ring

lemma digitEps_sum_formula (n : ℕ) :
    (∑ k ∈ Finset.range n, digitEps k) =
      (1 / 900 : ℝ) * (1 - (1 / 10 : ℝ) ^ n) := by
  induction n with
  | zero => simp [digitEps]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      change (1 / 900 : ℝ) * (1 - (1 / 10 : ℝ) ^ n) +
          (1 / 10 : ℝ) ^ (n + 3) =
        (1 / 900 : ℝ) * (1 - (1 / 10 : ℝ) ^ (n + 1))
      have hpow : (1 / 10 : ℝ) ^ (n + 3) =
          (1 / 10 : ℝ) ^ n * (1 / 10 : ℝ) ^ 3 := by
        exact pow_add _ _ _
      have hpow' : (1 / 10 : ℝ) ^ (n + 1) =
          (1 / 10 : ℝ) ^ n * (1 / 10 : ℝ) := by
        exact pow_succ _ _
      rw [hpow, hpow']
      norm_num
      ring

lemma digitEps_sum_le (n : ℕ) :
    (∑ k ∈ Finset.range n, digitEps k) ≤ 1 / 900 := by
  rw [digitEps_sum_formula]
  have hpow_nonneg : 0 ≤ (1 / 10 : ℝ) ^ n := by positivity
  have hpow_le : (1 / 10 : ℝ) ^ n ≤ 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have ih' : (1 / 10 : ℝ) ^ n ≤ 1 := ih (by positivity)
        calc
          (1 / 10 : ℝ) ^ n * (1 / 10 : ℝ) ≤ 1 * (1 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_right ih' (by norm_num)
          _ ≤ 1 := by norm_num
  nlinarith

/-- Addition of one digit at the next decimal place, in cyclic factor order. -/
def rotateIdx (c : ℕ) (i : Fin 20) : Fin 20 :=
  ⟨(c % 20 + i.val) % 20, Nat.mod_lt _ (by norm_num)⟩

def rotatePos (c : ℕ) (j : Fin 20) : ℕ :=
  (j.val + 20 - c % 20) % 20

lemma rotatePos_rotateIdx (c : ℕ) (i : Fin 20) :
    rotatePos c (rotateIdx c i) = i.val := by
  have hc : c % 20 < 20 := Nat.mod_lt _ (by norm_num)
  have hi : i.val < 20 := i.isLt
  dsimp [rotatePos, rotateIdx]
  omega

lemma rotateIdx_rotatePos (c : ℕ) (j : Fin 20) :
    rotateIdx c ⟨rotatePos c j, Nat.mod_lt _ (by norm_num)⟩ = j := by
  apply Fin.ext
  have hc : c % 20 < 20 := Nat.mod_lt _ (by norm_num)
  have hj : j.val < 20 := j.isLt
  dsimp [rotatePos, rotateIdx]
  omega

def rotateEquiv (c : ℕ) : Fin 20 ≃ Fin 20 where
  toFun := rotateIdx c
  invFun := fun j => ⟨rotatePos c j, Nat.mod_lt _ (by norm_num)⟩
  left_inv := by
    intro i
    apply Fin.ext
    exact rotatePos_rotateIdx c i
  right_inv := by
    intro j
    exact rotateIdx_rotatePos c j

lemma prod_rotateIdx (f : Fin 20 → ℝ) (c : ℕ) :
    (∏ i : Fin 20, f (rotateIdx c i)) = ∏ j : Fin 20, f j := by
  simpa [rotateEquiv] using (Equiv.prod_comp (rotateEquiv c) f)

def roundUpdate (f : Fin 20 → ℝ) (c : ℕ) (ε : ℝ) (s : ℕ) (j : Fin 20) : ℝ :=
  f j + (if rotatePos c j < s then ε else 0)

lemma roundUpdate_product (f : Fin 20 → ℝ) (c : ℕ) (ε : ℝ) (s : ℕ) :
    (∏ j : Fin 20, roundUpdate f c ε s j) =
      prefix_prod (fun i => f (rotateIdx c i)) ε s := by
  classical
  calc
    (∏ j : Fin 20, roundUpdate f c ε s j) =
        ∏ i : Fin 20, roundUpdate f c ε s (rotateIdx c i) := by
      symm
      exact Equiv.prod_comp (rotateEquiv c) (roundUpdate f c ε s)
    _ = ∏ i : Fin 20, update_prefix (fun i => f (rotateIdx c i)) ε s i := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [roundUpdate, update_prefix, prefix_bits, rotatePos_rotateIdx]
    _ = prefix_prod (fun i => f (rotateIdx c i)) ε s := rfl

def greedyGood (x : ℝ) (n : ℕ) (f : Fin 20 → ℝ) : Prop :=
  (∏ j : Fin 20, f j) < x ∧
  x - (∏ j : Fin 20, f j) ≤ 10.3 * digitEps n ∧
  (∀ j, 1 ≤ f j) ∧
  (∀ j, f j + digitEps n ≤ 1 + 1 / 900)

theorem greedy_count_exists (x : ℝ) (n : ℕ) (f : Fin 20 → ℝ) (c : ℕ)
    (h : greedyGood x n f) :
    ∃ s : ℕ, s ≤ 20 ∧
      prefix_prod (fun i => f (rotateIdx c i)) (digitEps n) s < x ∧
      x ≤ prefix_prod (fun i => f (rotateIdx c i)) (digitEps n) (s + 1) ∧
      x - prefix_prod (fun i => f (rotateIdx c i)) (digitEps n) s ≤
        1.03 * digitEps n := by
  rcases h with ⟨hprod, hres, hge, hle⟩
  let g : Fin 20 → ℝ := fun i => f (rotateIdx c i)
  have hrot := prod_rotateIdx f c
  have hprod' : (∏ i : Fin 20, g i) < x := by
    dsimp [g]
    rw [hrot]
    exact hprod
  have hres' : x - (∏ i : Fin 20, g i) ≤ 10.3 * digitEps n := by
    dsimp [g]
    rw [hrot]
    exact hres
  have hge' : ∀ i, 1 ≤ g i := by
    intro i
    exact hge (rotateIdx c i)
  have hle' : ∀ i, g i + digitEps n ≤ 1 + 1 / 900 := by
    intro i
    exact hle (rotateIdx c i)
  exact single_step_greedy_leap_strict g (digitEps n) (digitEps_pos n)
    hge' hle' x hprod' hres'

noncomputable def greedyChosenCount (x : ℝ) (n : ℕ) (f : Fin 20 → ℝ) (c : ℕ) : ℕ := by
  classical
  exact if h : greedyGood x n f then Classical.choose (greedy_count_exists x n f c h) else 0

lemma greedyChosenCount_spec (x : ℝ) (n : ℕ) (f : Fin 20 → ℝ) (c : ℕ)
    (h : greedyGood x n f) :
    greedyChosenCount x n f c ≤ 20 ∧
      prefix_prod (fun i => f (rotateIdx c i)) (digitEps n)
        (greedyChosenCount x n f c) < x ∧
      x ≤ prefix_prod (fun i => f (rotateIdx c i)) (digitEps n)
        (greedyChosenCount x n f c + 1) ∧
      x - prefix_prod (fun i => f (rotateIdx c i)) (digitEps n)
        (greedyChosenCount x n f c) ≤ 1.03 * digitEps n := by
  classical
  classical
  simp only [greedyChosenCount, dite_eq_left h]
  exact Classical.choose_spec (greedy_count_exists x n f c h)

noncomputable def greedyStates (x : ℝ) : ℕ → (Fin 20 → ℝ) × ℕ
  | 0 => (fun _ => 1, 0)
  | n + 1 =>
      let st := greedyStates x n
      let s := greedyChosenCount x n st.1 st.2
      (roundUpdate st.1 st.2 (digitEps n) s, st.2 + s)

noncomputable def greedyFactors (x : ℝ) (n : ℕ) : Fin 20 → ℝ :=
  (greedyStates x n).1

noncomputable def greedyCursor (x : ℝ) (n : ℕ) : ℕ :=
  (greedyStates x n).2

noncomputable def greedyCountAt (x : ℝ) (n : ℕ) : ℕ :=
  greedyChosenCount x n (greedyFactors x n) (greedyCursor x n)

lemma greedyStates_succ (x : ℝ) (n : ℕ) :
    greedyStates x (n + 1) =
      (roundUpdate (greedyFactors x n) (greedyCursor x n) (digitEps n)
        (greedyCountAt x n),
       greedyCursor x n + greedyCountAt x n) := by
  simp [greedyStates, greedyFactors, greedyCursor, greedyCountAt]

lemma greedyFactors_succ (x : ℝ) (n : ℕ) :
    greedyFactors x (n + 1) =
      roundUpdate (greedyFactors x n) (greedyCursor x n) (digitEps n)
        (greedyCountAt x n) := by
  have h := congrArg Prod.fst (greedyStates_succ x n)
  simpa [greedyFactors] using h

lemma greedyCursor_succ (x : ℝ) (n : ℕ) :
    greedyCursor x (n + 1) = greedyCursor x n + greedyCountAt x n := by
  have h := congrArg Prod.snd (greedyStates_succ x n)
  simpa [greedyCursor] using h

def greedyInv (x : ℝ) (n : ℕ) (f : Fin 20 → ℝ) : Prop :=
  (∀ j, 1 ≤ f j) ∧
  (∀ j, f j ≤ 1 + (∑ k ∈ Finset.range n, digitEps k)) ∧
  (∏ j : Fin 20, f j) < x ∧
  x - (∏ j : Fin 20, f j) ≤ 10.3 * digitEps n

lemma greedyInv_to_good (x : ℝ) (n : ℕ) (f : Fin 20 → ℝ)
    (h : greedyInv x n f) : greedyGood x n f := by
  rcases h with ⟨hge, hpartial, hprod, hres⟩
  refine ⟨hprod, hres, hge, ?_⟩
  intro j
  have hsum := digitEps_sum_le (n + 1)
  rw [Finset.sum_range_succ] at hsum
  calc
    f j + digitEps n ≤
        1 + (∑ k ∈ Finset.range n, digitEps k) + digitEps n := by
          linarith [hpartial j]
    _ ≤ 1 + 1 / 900 := by linarith

lemma greedyStates_succ_count_zero (x : ℝ) (n : ℕ)
    (h : greedyCountAt x n = 0) : greedyStates x (n + 1) = greedyStates x n := by
  rw [greedyStates_succ, h]
  apply Prod.ext
  · funext j
    simp [roundUpdate, greedyFactors]
  · simp [greedyCursor]

lemma greedyFactors_inv (x : ℝ) (hx : x ∈ Set.Icc targetA targetB) :
    ∀ n, greedyInv x n (greedyFactors x n) := by
  intro n
  induction n with
  | zero =>
      rcases hx with ⟨hxA, hxB⟩
      have hx_gt : 1 < x := by norm_num [targetA] at hxA ⊢; linarith
      have hx_le : x ≤ 1.003 := by norm_num [targetB] at hxB ⊢; linarith
      constructor
      · intro j
        simp [greedyFactors, greedyStates]
      constructor
      · intro j
        simp [greedyFactors, greedyStates]
      constructor
      · simpa [greedyFactors, greedyStates] using hx_gt
      · have hres : x - 1 ≤ 10.3 * digitEps 0 := by
          norm_num [digitEps]
          linarith
        simpa [greedyFactors, greedyStates] using hres
  | succ n ih =>
      rcases ih with ⟨hge, hpartial, hprod, hres⟩
      have hgood : greedyGood x n (greedyFactors x n) :=
        greedyInv_to_good x n (greedyFactors x n) ⟨hge, hpartial, hprod, hres⟩
      have hspec := greedyChosenCount_spec x n (greedyFactors x n)
        (greedyCursor x n) hgood
      have hspec' : greedyCountAt x n ≤ 20 ∧
          prefix_prod (fun i => greedyFactors x n (rotateIdx (greedyCursor x n) i))
            (digitEps n) (greedyCountAt x n) < x ∧
          x ≤ prefix_prod (fun i => greedyFactors x n (rotateIdx (greedyCursor x n) i))
            (digitEps n) (greedyCountAt x n + 1) ∧
          x - prefix_prod (fun i => greedyFactors x n (rotateIdx (greedyCursor x n) i))
            (digitEps n) (greedyCountAt x n) ≤ 1.03 * digitEps n := by
        simpa [greedyCountAt] using hspec
      rcases hspec' with ⟨hs, hleft, hright, hresNext⟩
      rw [greedyInv, greedyFactors_succ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j
        have hu : greedyFactors x n j ≤
            roundUpdate (greedyFactors x n) (greedyCursor x n) (digitEps n)
              (greedyCountAt x n) j := by
          dsimp [roundUpdate]
          split_ifs <;> linarith [digitEps_pos n]
        exact le_trans (hge j) hu
      · intro j
        have hu : roundUpdate (greedyFactors x n) (greedyCursor x n) (digitEps n)
              (greedyCountAt x n) j ≤ greedyFactors x n j + digitEps n := by
          dsimp [roundUpdate]
          split_ifs <;> linarith [digitEps_pos n]
        calc
          roundUpdate (greedyFactors x n) (greedyCursor x n) (digitEps n)
              (greedyCountAt x n) j ≤ greedyFactors x n j + digitEps n := hu
          _ ≤ 1 + (∑ k ∈ Finset.range n, digitEps k) + digitEps n := by
                linarith [hpartial j]
          _ = 1 + (∑ k ∈ Finset.range (n + 1), digitEps k) := by
                rw [Finset.sum_range_succ]
                ring
      · rw [roundUpdate_product]
        exact hleft
      · rw [roundUpdate_product]
        calc
          x - prefix_prod
              (fun i => greedyFactors x n (rotateIdx (greedyCursor x n) i))
              (digitEps n) (greedyCountAt x n) ≤ 1.03 * digitEps n := hresNext
          _ = 10.3 * digitEps (n + 1) := by
                rw [digitEps_succ]
                norm_num
                ring

lemma greedyCountAt_le_twenty (x : ℝ) (hx : x ∈ Set.Icc targetA targetB) (n : ℕ) :
    greedyCountAt x n ≤ 20 := by
  have hInv := greedyFactors_inv x hx n
  have hgood := greedyInv_to_good x n (greedyFactors x n) hInv
  simpa [greedyCountAt] using
    (greedyChosenCount_spec x n (greedyFactors x n) (greedyCursor x n) hgood).1

def greedyDigits (x : ℝ) (j : Fin 20) (n : ℕ) : ℕ :=
  if n < 2 then 0 else
    if rotatePos (greedyCursor x (n - 2)) j < greedyCountAt x (n - 2) then 1 else 0

lemma greedyDigits_binary (x : ℝ) (j : Fin 20) (n : ℕ) :
    greedyDigits x j n = 0 ∨ greedyDigits x j n = 1 := by
  by_cases hn : n < 2
  · simp [greedyDigits, hn]
  · by_cases hbit : rotatePos (greedyCursor x (n - 2)) j < greedyCountAt x (n - 2)
    · simp [greedyDigits, hn, hbit]
    · simp [greedyDigits, hn, hbit]

lemma greedyDigits_stage (x : ℝ) (j : Fin 20) (n : ℕ) :
    greedyDigits x j (n + 2) =
      if rotatePos (greedyCursor x n) j < greedyCountAt x n then 1 else 0 := by
  have hn : ¬ n + 2 < 2 := by omega
  simp [greedyDigits, hn]

lemma greedyFactors_succ_digit (x : ℝ) (n : ℕ) (j : Fin 20) :
    greedyFactors x (n + 1) j = greedyFactors x n j +
      (greedyDigits x j (n + 2) : ℝ) * digitEps n := by
  rw [greedyFactors_succ]
  dsimp [roundUpdate]
  rw [greedyDigits_stage]
  by_cases h : rotatePos (greedyCursor x n) j < greedyCountAt x n
  · simp [h]
  · simp [h]

lemma greedyCursor_monotone (x : ℝ) : Monotone (greedyCursor x) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [greedyCursor_succ]
  exact Nat.le_add_right _ _

lemma digitEps_tendsto_zero : Tendsto digitEps atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 10 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hshift : Tendsto (fun n : ℕ => n + 3) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  change Tendsto (fun n : ℕ => (1 / 10 : ℝ) ^ (n + 3)) atTop (𝓝 0)
  exact hpow.comp hshift

lemma greedy_nonzero_after (x : ℝ) (hx : x ∈ Set.Icc targetA targetB) (N : ℕ) :
    ∃ n ≥ N, 0 < greedyCountAt x n := by
  by_contra h
  have hallzero : ∀ n, N ≤ n → greedyCountAt x n = 0 := by
    intro n hn
    by_contra hne
    have hpos : 0 < greedyCountAt x n := by omega
    exact h ⟨n, hn, hpos⟩
  have hstate : ∀ k, greedyStates x (N + k) = greedyStates x N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hz : greedyCountAt x (N + k) = 0 := hallzero (N + k) (by omega)
        have hstep := greedyStates_succ_count_zero x (N + k) hz
        rw [show N + (k + 1) = (N + k) + 1 by omega, hstep, ih]
  have hshift : Tendsto (fun k : ℕ => N + k) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    omega
  have heps : Tendsto (fun k : ℕ => 10.3 * digitEps (N + k)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (digitEps_tendsto_zero.comp hshift)
  have hInvN := greedyFactors_inv x hx N
  have hprod_lt : (∏ j : Fin 20, greedyFactors x N j) < x := hInvN.2.2.1
  have hrpos : 0 < x - (∏ j : Fin 20, greedyFactors x N j) := sub_pos.mpr hprod_lt
  have hevent : ∀ᶠ k : ℕ in atTop,
      10.3 * digitEps (N + k) < x - (∏ j : Fin 20, greedyFactors x N j) :=
    heps.eventually (Iio_mem_nhds hrpos)
  obtain ⟨k, hk⟩ := hevent.exists
  have hstatefun : greedyFactors x (N + k) = greedyFactors x N := by
    exact congrArg Prod.fst (hstate k)
  have hstateprod :
      (∏ j : Fin 20, greedyFactors x (N + k) j) =
        ∏ j : Fin 20, greedyFactors x N j := by
    exact congrArg (fun f : Fin 20 → ℝ => ∏ j : Fin 20, f j) hstatefun
  have hbound := (greedyFactors_inv x hx (N + k)).2.2.2
  rw [hstateprod] at hbound
  linarith

theorem greedyCursor_unbounded (x : ℝ) (hx : x ∈ Set.Icc targetA targetB) :
    ∀ t : ℕ, ∃ n, t ≤ greedyCursor x n := by
  intro t
  induction t with
  | zero => exact ⟨0, by simp [greedyCursor, greedyStates]⟩
  | succ t ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hmn, hmpos⟩ := greedy_nonzero_after x hx n
      have hcur : greedyCursor x n ≤ greedyCursor x m :=
        greedyCursor_monotone x hmn
      refine ⟨m + 1, ?_⟩
      rw [greedyCursor_succ]
      omega

theorem greedyDigits_infinite_ones (x : ℝ) (hx : x ∈ Set.Icc targetA targetB)
    (j : Fin 20) : ∀ N : ℕ, ∃ n ≥ N, greedyDigits x j n = 1 := by
  intro N
  let t : ℕ := 20 * (greedyCursor x N + N + 1) + j.val
  have htmod : t % 20 = j.val := by
    dsimp [t]
    omega
  have htN : greedyCursor x N ≤ t := by
    dsimp [t]
    have hj := j.isLt
    omega
  obtain ⟨m, hm⟩ := greedyCursor_unbounded x hx (t + 1)
  have htm : (t : ℝ) < (greedyCursor x m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (Nat.lt_succ_self t) hm)
  have hP0 : (greedyCursor x 0 : ℝ) ≤ (t : ℝ) := by
    simp [greedyCursor, greedyStates]
  obtain ⟨s, hs_lt, hsleft, hsright⟩ :=
    exists_step_cut (fun k : ℕ => (greedyCursor x k : ℝ)) (t : ℝ) m hP0 htm
  have hcurle : greedyCursor x s ≤ t := by exact_mod_cast hsleft
  have hcurgt : t < greedyCursor x (s + 1) := by exact_mod_cast hsright
  have hsge : N ≤ s := by
    by_contra hnot
    have hsn : s < N := Nat.lt_of_not_ge hnot
    have hmon : greedyCursor x (s + 1) ≤ greedyCursor x N := by
      apply greedyCursor_monotone x
      omega
    have hcurgtNat : t < greedyCursor x (s + 1) := by
      exact_mod_cast hcurgt
    omega
  have hcountle := greedyCountAt_le_twenty x hx s
  have hdiff : t - greedyCursor x s < greedyCountAt x s := by
    rw [greedyCursor_succ] at hcurgt
    omega
  have hdiff20 : t - greedyCursor x s < 20 := lt_of_lt_of_le hdiff hcountle
  have hpos : rotatePos (greedyCursor x s) j = t - greedyCursor x s := by
    have hcs : greedyCursor x s ≤ t := hcurle
    dsimp [rotatePos, t]
    omega
  have hbit : greedyDigits x j (s + 2) = 1 := by
    rw [greedyDigits_stage]
    have hsmall : rotatePos (greedyCursor x s) j < greedyCountAt x s := by
      rw [hpos]
      exact hdiff
    simp [hsmall]
  exact ⟨s + 2, by omega, hbit⟩

lemma factor_partial_succ (a : Fin 20 → ℕ → ℕ) (j : Fin 20) (N : ℕ) :
    factor_partial a j (N + 1) =
      factor_partial a j N + (a j N : ℝ) * (10 : ℝ)⁻¹ ^ (N + 1) := by
  dsimp [factor_partial]
  rw [Finset.sum_range_succ]
  ring

lemma factor_partial_eq_greedy_state (x : ℝ) (j : Fin 20) (n : ℕ) :
    factor_partial (greedyDigits x) j (n + 2) = greedyFactors x n j := by
  induction n with
  | zero =>
      simp [factor_partial, greedyDigits, greedyFactors, greedyStates, Finset.sum_range_succ]
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega]
      rw [factor_partial_succ, ih]
      have heps : (10 : ℝ)⁻¹ ^ ((n + 2) + 1) = digitEps n := by
        norm_num [digitEps]
      rw [heps, greedyFactors_succ_digit]

lemma greedy_product_tendsto (x : ℝ) (hx : x ∈ Set.Icc targetA targetB) :
    Tendsto (fun n : ℕ => ∏ j : Fin 20, greedyFactors x n j) atTop (𝓝 x) := by
  have hinv := greedyFactors_inv x hx
  have hupper : Tendsto (fun n : ℕ => 10.3 * digitEps n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul digitEps_tendsto_zero
  have hres : Tendsto (fun n : ℕ => x - (∏ j : Fin 20, greedyFactors x n j))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
    · exact Filter.Eventually.of_forall fun n => by
        have hp := (hinv n).2.2.1
        linarith
    · exact Filter.Eventually.of_forall fun n => (hinv n).2.2.2
  have hfun : (fun n : ℕ => ∏ j : Fin 20, greedyFactors x n j) =
      fun n => x - (x - (∏ j : Fin 20, greedyFactors x n j)) := by
    funext n
    ring
  rw [hfun]
  simpa only [sub_zero] using (tendsto_const_nhds.sub hres)

/-- Replacement for the custom axiom in `test.lean`. -/
theorem exists_bits_for_target_axiom (x : ℝ)
    (hx : x ∈ Set.Icc targetA targetB) :
    ∃ (a : Fin 20 → ℕ → ℕ),
      (∀ j n, a j n = 0 ∨ a j n = 1) ∧
      (∀ j N, ∃ n ≥ N, a j n = 1) ∧
      Tendsto (fun N : ℕ => ∏ j : Fin 20, factor_partial a j N) atTop (𝓝 x) := by
  let a : Fin 20 → ℕ → ℕ := greedyDigits x
  have ha_bin : ∀ j n, a j n = 0 ∨ a j n = 1 := by
    intro j n
    exact greedyDigits_binary x j n
  have ha_inf : ∀ j N, ∃ n ≥ N, a j n = 1 := by
    intro j N
    exact greedyDigits_infinite_ones x hx j N
  have hshift : Tendsto (fun n : ℕ => n + 2) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hpartial_shift := (tendsto_partial_prod_to_inf_prod a ha_bin).comp hshift
  have hpair :
      (fun n : ℕ => ∏ j : Fin 20, factor_partial a j (n + 2)) =
        fun n => ∏ j : Fin 20, greedyFactors x n j := by
    funext n
    apply Finset.prod_congr rfl
    intro j hj
    simpa [a] using factor_partial_eq_greedy_state x j n
  have hstate_inf :
      Tendsto (fun n : ℕ => ∏ j : Fin 20, greedyFactors x n j) atTop
        (𝓝 (∏ j : Fin 20, factor_of_bits a j)) := by
    simpa only [Function.comp_def, hpair] using hpartial_shift
  have hstate_x := greedy_product_tendsto x hx
  have hprod_eq : (∏ j : Fin 20, factor_of_bits a j) = x :=
    tendsto_nhds_unique hstate_inf hstate_x
  refine ⟨a, ha_bin, ha_inf, ?_⟩
  have hpartial := tendsto_partial_prod_to_inf_prod a ha_bin
  rw [hprod_eq] at hpartial
  exact hpartial

theorem exists_bits_for_target (x : ℝ) (hx : x ∈ Set.Icc targetA targetB) :
    ∃ (a : Fin 20 → ℕ → ℕ),
      (∀ j n, a j n = 0 ∨ a j n = 1) ∧
      (∀ j N, ∃ n ≥ N, a j n = 1) ∧
      (∏ j : Fin 20, factor_of_bits a j) = x := by
  obtain ⟨a, ha_bin, ha_inf, h_lim⟩ := exists_bits_for_target_axiom x hx
  refine ⟨a, ha_bin, ha_inf, ?_⟩
  have h_top := tendsto_partial_prod_to_inf_prod a ha_bin
  exact tendsto_nhds_unique h_top h_lim

theorem cantor_product_contains_interval :
    ∃ A B : ℝ, 1 < A ∧ A < B ∧ ∀ x ∈ Set.Icc A B, InP x := by
  refine ⟨targetA, targetB, target_interval_valid.1, target_interval_valid.2, ?_⟩
  intro x hx
  obtain ⟨a, ha_bin, ha_inf, h_prod⟩ := exists_bits_for_target x hx
  exact inP_of_bits_product a ha_bin ha_inf x h_prod

/-!
======================================================================
  第六部分：公理依赖检查
======================================================================
-/
#print axioms cantor_product_contains_interval


/-! 局部区间覆盖半射线，并桥接到 Comparator 所需的有限乘积命题。 -/

lemma InP_pow {t : ℝ} (ht : InP t) : ∀ {n : ℕ}, 0 < n → InP (t ^ n)
  | 1, _ => by
    rw [pow_one]
    exact ht
  | n + 2, _ => by
    rw [pow_succ]
    exact InP.mul (InP_pow ht (Nat.succ_pos n)) ht

/-- 引理 2：非负项的伯努利不等式 (1 + d)^n ≥ 1 + n * d -/
lemma one_add_mul_le_pow (d : ℝ) (hd : 0 ≤ d) : ∀ (n : ℕ), 1 + (n : ℝ) * d ≤ (1 + d) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ]
    have ih := one_add_mul_le_pow d hd n
    have h1 : 1 ≤ (1 + d) ^ n := one_le_pow₀ (by linarith)
    have h2 : d ≤ (1 + d) ^ n * d := by
      calc d = 1 * d := (one_mul d).symm
      _ ≤ (1 + d) ^ n * d := mul_le_mul_of_nonneg_right h1 hd
    have h3 : 1 + (↑(n + 1) : ℝ) * d = (1 + (n : ℝ) * d) + d := by
      push_cast
      ring
    rw [h3]
    calc (1 + (n : ℝ) * d) + d
      _ ≤ (1 + d) ^ n + d := by linarith
      _ ≤ (1 + d) ^ n + (1 + d) ^ n * d := by linarith
      _ = (1 + d) ^ n * (1 + d) := by ring

/--
引理 3：若集合 P 包含区间 [A, B] (1 < A < B)，
则 P 在乘法下生成的元素能够完全覆盖无穷半射线 [M, ∞)。
-/
lemma interval_generates_ray {A B : ℝ} (hA : 1 < A) (hAB : A < B)
    (h_int : ∀ x ∈ Set.Icc A B, InP x) : ∃ M : ℝ, ∀ y ≥ M, InP y := by
  have hA_pos : 0 < A := by linarith
  have hB_pos : 0 < B := by linarith
  have hr_gt1 : 1 < B / A := (one_lt_div hA_pos).mpr hAB
  set d := B / A - 1 with hd_def
  have hd_pos : 0 < d := sub_pos.mpr hr_gt1
  have hd_nonneg : 0 ≤ d := le_of_lt hd_pos

  obtain ⟨n0, hn0⟩ := exists_nat_gt ((A - 1) / d)
  have hn0_le : A ≤ (B / A) ^ n0 := by
    have h_trans : A - 1 < (n0 : ℝ) * d := (div_lt_iff₀ hd_pos).mp hn0
    have h_bern := one_add_mul_le_pow d hd_nonneg n0
    have hr_eq : 1 + d = B / A := by linarith
    rw [hr_eq] at h_bern
    linarith

  have h_ratio_pos : 0 < (A - 1) / d := div_pos (by linarith) hd_pos
  have hn0_pos : 0 < n0 := Nat.cast_pos.mp (lt_trans h_ratio_pos hn0)

  have h_overlap : ∀ n ≥ n0, A ^ (n + 1) ≤ B ^ n := by
    intro n hn
    have h_pow_mono : (B / A) ^ n0 ≤ (B / A) ^ n :=
      pow_le_pow_right₀ (le_of_lt hr_gt1) hn
    have h_ge_A : A ≤ (B / A) ^ n := le_trans hn0_le h_pow_mono
    have h_mul := mul_le_mul_of_nonneg_right h_ge_A (pow_nonneg (le_of_lt hA_pos) n)
    rw [div_pow, div_mul_cancel₀ _ (ne_of_gt (pow_pos hA_pos n))] at h_mul
    rw [pow_succ]
    linarith

  use A ^ n0
  intro y hy
  have hy_pos : 0 < y := by
    have : 0 < A ^ n0 := pow_pos hA_pos n0
    linarith

  set dA := A - 1 with hdA_def
  have hdA_pos : 0 < dA := sub_pos.mpr hA
  obtain ⟨K, hK⟩ := exists_nat_gt (y / dA)
  have hy_lt_powK : y < A ^ K := by
    have h_K_mul : y < (K : ℝ) * dA := (div_lt_iff₀ hdA_pos).mp hK
    have h_bernA := one_add_mul_le_pow dA (le_of_lt hdA_pos) K
    have hA_eq : 1 + dA = A := by linarith
    rw [hA_eq] at h_bernA
    linarith

  have h_ex : ∃ K_val : ℕ, y < A ^ K_val := ⟨K, hy_lt_powK⟩
  set m := Nat.find h_ex
  have hm_spec : y < A ^ m := Nat.find_spec h_ex

  have hm_ne_zero : m ≠ 0 := by
    intro hm_zero
    have hm_spec' := hm_spec
    rw [hm_zero, pow_zero] at hm_spec'
    have hM_gt1 : 1 < A ^ n0 := one_lt_pow₀ hA (ne_of_gt hn0_pos)
    linarith

  set n := m - 1
  have hm_eq : m = n + 1 := (Nat.succ_pred hm_ne_zero).symm
  rw [hm_eq] at hm_spec

  have hn_min : A ^ n ≤ y :=
    not_lt.mp (Nat.find_min h_ex (Nat.pred_lt hm_ne_zero))

  have hn_ge_n0 : n0 ≤ n := by
    by_contra h_not
    have h_lt : n < n0 := not_le.mp h_not
    have hn_succ_le_n0 : n + 1 ≤ n0 := h_lt
    have h_pow_le : A ^ (n + 1) ≤ A ^ n0 :=
      pow_le_pow_right₀ (le_of_lt hA) hn_succ_le_n0
    linarith

  have hn_pos : 0 < n := lt_of_lt_of_le hn0_pos hn_ge_n0
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos

  have hy_le_Bn : y ≤ B ^ n := le_trans (le_of_lt hm_spec) (h_overlap n hn_ge_n0)

  set t := y ^ ((n : ℝ)⁻¹) with ht_def
  have ht_nonneg : 0 ≤ t := Real.rpow_nonneg (le_of_lt hy_pos) _
  have ht_pow_n : t ^ n = y := Real.rpow_inv_natCast_pow (le_of_lt hy_pos) hn_ne

  have ht_ge_A : A ≤ t := by
    rw [← pow_le_pow_iff_left₀ (le_of_lt hA_pos) ht_nonneg hn_ne]
    rw [ht_pow_n]
    exact hn_min

  have ht_le_B : t ≤ B := by
    rw [← pow_le_pow_iff_left₀ ht_nonneg (le_of_lt hB_pos) hn_ne]
    rw [ht_pow_n]
    exact hy_le_Bn

  have ht_in_icc : t ∈ Set.Icc A B := ⟨ht_ge_A, ht_le_B⟩
  have ht_in_P : InP t := h_int t ht_in_icc
  have hy_in_P : InP (t ^ n) := InP_pow ht_in_P hn_pos
  rwa [ht_pow_n] at hy_in_P

/--
【稀疏康托集乘积生成半射线定理】
（已由原先的代码公理提升为严格证明的定理）
-/
theorem cantor_product_generates_ray :
    ∃ M : ℝ, ∀ y ≥ M, InP y := by
  obtain ⟨A, B, hA, hAB, h_int⟩ := cantor_product_contains_interval
  exact interval_generates_ray hA hAB h_int



lemma isFiniteProductOfS_of_inS {x : ℝ} (hx : InS x) : IsFiniteProductOfS x := by
  use 1, Nat.one_pos, fun _ => x
  refine ⟨fun _ => hx, ?_⟩
  rw [Fin.prod_univ_one]

lemma isFiniteProductOfS_mul {x y : ℝ}
    (hx : IsFiniteProductOfS x) (hy : IsFiniteProductOfS y) :
    IsFiniteProductOfS (x * y) := by
  rcases hx with ⟨k1, hk1, f1, hf1, rfl⟩
  rcases hy with ⟨k2, hk2, f2, hf2, rfl⟩
  refine ⟨k1 + k2, add_pos hk1 hk2, Fin.append f1 f2, ?_, ?_⟩
  · rw [Fin.forall_fin_add]
    refine ⟨?_, ?_⟩
    · intro i
      rw [Fin.append_left]
      exact hf1 i
    · intro j
      rw [Fin.append_right]
      exact hf2 j
  · rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem InP_to_IsFiniteProductOfS {y : ℝ} (h : InP y) : IsFiniteProductOfS y := by
  induction h with
  | of_S hx => exact isFiniteProductOfS_of_inS hx
  | mul hx hy ihx ihy => exact isFiniteProductOfS_mul ihx ihy

/-- 对称性引理：若 x ∈ S，则 -x ∈ S -/
lemma inS_neg (x : ℝ) (hx : InS x) : InS (-x) := by
  rcases hx with ⟨hpos, hle, a₀, a, ha₀, ha, hinf, heq⟩
  refine ⟨by rwa [abs_neg], by rwa [abs_neg], a₀, a, ha₀, ha, hinf, ?_⟩
  rwa [abs_neg]

/-- 等比级数严格求和引理：∑_{n=0}^∞ (1/10)^(n+1) = 1/9 -/
lemma sum_tenth_pow : ∑' (n : ℕ), (10 : ℝ)⁻¹ ^ (n + 1) = 1 / 9 := by
  have h0 : (0 : ℝ) ≤ (10 : ℝ)⁻¹ := by norm_num
  have h1 : ((10 : ℝ)⁻¹ : ℝ) < 1 := by norm_num
  have h_geom := hasSum_geometric_of_lt_one h0 h1
  have h_mul := h_geom.mul_left ((10 : ℝ)⁻¹)
  have h_eq : (fun n : ℕ => (10 : ℝ)⁻¹ * (10 : ℝ)⁻¹ ^ n) = (fun n => (10 : ℝ)⁻¹ ^ (n + 1)) := by
    funext n
    rw [pow_succ']
  rw [h_eq] at h_mul
  have h_val : (10 : ℝ)⁻¹ * (1 - (10 : ℝ)⁻¹)⁻¹ = 1 / 9 := by norm_num
  rw [h_val] at h_mul
  exact h_mul.tsum_eq

/-- 严格证明：1/9 属于集合 S -/
theorem one_ninth_in_S : InS (1 / 9) := by
  refine ⟨by norm_num, by norm_num, 0, (fun _ => 1), Or.inl rfl, (fun _ => Or.inr rfl), ?_, ?_⟩
  · intro N
    exact ⟨N, le_rfl, rfl⟩
  · have h_abs : |(1 / 9 : ℝ)| = 1 / 9 := abs_of_pos (by norm_num)
    rw [h_abs, Nat.cast_zero, zero_add]
    have h_seq : (fun n : ℕ => ((1 : ℕ) : ℝ) * (10 : ℝ)⁻¹ ^ (n + 1)) = (fun n => (10 : ℝ)⁻¹ ^ (n + 1)) := by
      funext n
      simp
    rw [h_seq]
    exact sum_tenth_pow.symm

/-- 严格证明：-1/9 属于集合 S -/
theorem neg_one_ninth_in_S : InS (- (1 / 9)) :=
  inS_neg (1 / 9) one_ninth_in_S

theorem one_ninth_in_P : InP (1 / 9) :=
  InP.of_S one_ninth_in_S

theorem neg_one_ninth_in_P : InP (- (1 / 9)) :=
  InP.of_S neg_one_ninth_in_S

/-- (1/9)^(k+1) 归纳属于半群 P -/
theorem InP_ninth_pow : ∀ (k : ℕ), InP ((1 / 9 : ℝ) ^ (k + 1))
  | 0 => by
    rw [Nat.zero_add, pow_one]
    exact one_ninth_in_P
  | k + 1 => by
    rw [pow_succ]
    exact InP.mul (InP_ninth_pow k) one_ninth_in_P


/-!
======================================================================
  第五部分：标度放大与归约引理（无 sorry，完全证明）
======================================================================
-/

lemma nat_le_nine_pow (n : ℕ) : (n : ℝ) ≤ (9 : ℝ) ^ (n + 1) := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ]
    have h1 : (1 : ℝ) ≤ (9 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    linarith

/-- 阿基米德标度放大（严格证明） -/
theorem archimedean_scale (M y : ℝ) (hy : 0 < y) :
    ∃ k : ℕ, M ≤ y * (9 : ℝ) ^ (k + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (M / y)
  use n
  have h_nine := nat_le_nine_pow n
  have h_trans : M / y ≤ (9 : ℝ) ^ (n + 1) := le_trans hn h_nine
  have h_le := (div_le_iff₀ hy).mp h_trans
  rwa [mul_comm] at h_le

/-- 引理 1：阿基米德尺度下行压缩 -/
theorem lemma_scale_reduction (M : ℝ)
    (h_ray : ∀ y ≥ M, InP y) : ∀ y > 0, InP y := by
  intro y hy
  obtain ⟨k, hk_ge⟩ := archimedean_scale M y hy
  have hz_in : InP (y * (9 : ℝ) ^ (k + 1)) := h_ray (y * (9 : ℝ) ^ (k + 1)) hk_ge
  have h_pow_in : InP ((1 / 9 : ℝ) ^ (k + 1)) := InP_ninth_pow k
  have hy_eq : (y * (9 : ℝ) ^ (k + 1)) * ((1 / 9 : ℝ) ^ (k + 1)) = y := by
    rw [mul_assoc, ← mul_pow]
    have h9 : (9 : ℝ) * (1 / 9 : ℝ) = 1 := by norm_num
    rw [h9, one_pow, mul_one]
  have h_prod : InP ((y * (9 : ℝ) ^ (k + 1)) * ((1 / 9 : ℝ) ^ (k + 1))) :=
    InP.mul hz_in h_pow_in
  rw [hy_eq] at h_prod
  exact h_prod

/-- 引理 2：负符号镜像对称翻转 -/
theorem lemma_sign_reduction (h_pos : ∀ y > 0, InP y) : ∀ y ≠ 0, InP y := by
  intro y hy
  rcases lt_trichotomy y 0 with h_neg | rfl | h_pos_y
  · have hz_pos : 0 < -9 * y := by linarith
    have hz_in : InP (-9 * y) := h_pos (-9 * y) hz_pos
    have hy_eq : y = - (1 / 9) * (-9 * y) := by ring
    rw [hy_eq]
    exact InP.mul neg_one_ninth_in_P hz_in
  · contradiction
  · exact h_pos y h_pos_y



/-- 主定理 (Conjecture 1) 严格闭环证明 -/
theorem Conjecture1 :
    ∀ (y : ℝ), y ≠ 0 → IsFiniteProductOfS y := by
  intro y hy
  obtain ⟨M, h_ray⟩ := cantor_product_generates_ray
  have h_pos : ∀ x > 0, InP x := lemma_scale_reduction M h_ray
  have h_inp : InP y := lemma_sign_reduction h_pos y hy
  exact InP_to_IsFiniteProductOfS h_inp


#print axioms Conjecture1

end StrictFormalConjecture1
