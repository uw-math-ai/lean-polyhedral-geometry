import PolyhedralGeometry.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap

section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma halfspace_convex : ∀ (s : Set V), Halfspace s → Convex ℝ s := by
  intro s h_s_halfspace
  unfold Convex
  intro x h_x_in_s
  unfold StarConvex
  intro y h_y_in_s a b h_a_nonneg h_b_nonneg h_a_b_one
  show a • x + b • y ∈ s
  unfold Halfspace at h_s_halfspace
  rcases h_s_halfspace with ⟨f, ⟨c, rfl⟩⟩
  -- rw [Set.mem_def] at h_x_in_s
  -- dsimp at h_x_in_s -- doesn't work!
  have h_x_in_s : f x ≤ c := by assumption
  have h_y_in_s : f y ≤ c := by assumption
  show f (a • x + b • y) ≤ c
  calc
    f (a • x + b • y) = f (a • x) + f (b • y) := by
      apply LinearMap.map_add
    _ = a * f x + b * f y := by
      repeat rw [LinearMap.map_smul]
      rfl
    _ ≤ a * c + b * c := by
      apply add_le_add
      <;> apply mul_le_mul_of_nonneg_left
      <;> assumption
    _ = (a + b) * c := by rw [add_mul]
    _ = 1 * c := by rw [h_a_b_one]
    _ = c := one_mul c

theorem poly_convex : ∀ (s : Set V), Polyhedron s → Convex ℝ s := by
  intro s h_s_poly
  unfold Polyhedron at h_s_poly
  rcases h_s_poly with ⟨I, H, h_I_finite, h_Hi_halfspace, rfl⟩
  apply convex_iInter
  intro i
  exact halfspace_convex _ (h_Hi_halfspace i)

--lemma 1.2.2
lemma translate_halfspace_of_cone_subset (s : Set V) (f : V →ₗ[ℝ] ℝ) (c : ℝ) : Cone s → (∀ x ∈ s, f x ≤ c) → c ≥ 0 ∧ ∀ x ∈ s, f x ≤ 0 := by
  intro h_s_cone h_s_fc
  constructor
  · revert h_s_fc
    contrapose!
    intro h_c_lt_0
    use 0
    constructor
    · unfold Cone at h_s_cone
      obtain ⟨x, hx⟩ := h_s_cone.left
      have h₀ : (0 : ℝ) • x ∈ s := h_s_cone.right (0 : ℝ) (by norm_num) x hx
      rw [Module.zero_smul x] at h₀
      exact h₀
    · rw [LinearMap.map_zero f]
      exact h_c_lt_0
  · intro x₀ x_in_s
    apply not_lt.mp
    intro assump_0_le_fx
    have h_0_le_inv_fx : 0 < (f x₀)⁻¹ := by exact inv_pos_of_pos assump_0_le_fx
    unfold Cone at h_s_cone
    have lt_c : f x₀ ≤ c := h_s_fc x₀ x_in_s
    have ge_0_c : 0 < c := lt_of_lt_of_le assump_0_le_fx lt_c
    have gq_2c_fxinv : 0 < 2 * c * (f x₀)⁻¹ := by
      apply mul_pos
      norm_num
      apply ge_0_c
      norm_num
      apply assump_0_le_fx
    have : (2 * c * (f x₀)⁻¹) • x₀ ∈ s := h_s_cone.right (2 * c * (f x₀)⁻¹) (by linarith) x₀ x_in_s
    have le_c : f ((2 * c * (f x₀)⁻¹) • x₀) ≤ c := h_s_fc ((2 * c * (f x₀)⁻¹) • x₀) this
    have : f x₀ ≠ 0 := Ne.symm (ne_of_lt assump_0_le_fx)
    rw [LinearMap.map_smul] at le_c
    dsimp at le_c
    rw [mul_assoc, inv_mul_cancel₀ this, mul_one] at le_c
    show False
    linarith

-- theorem min_elt (s : Set ℕ) (h_s_nonempty : s.Nonempty) : ∃ n ∈ s, ∀ m < n, m ∉ s := by
--   rcases h_s_nonempty with ⟨n, h⟩
--   induction' n using Nat.strong_induction_on with n ih
--   by_cases h' : ∀ m < n, m ∉ s
--   . use n
--   . push_neg at h'
--     rcases h' with ⟨n', h₁, h₂⟩
--     exact ih n' h₁ h₂

section

lemma sum_bijon {α β γ : Type*} [AddCommMonoid γ] {t : Finset α} {s : Finset β} {T : α → β} (h_bij : Set.BijOn T t s) {f : α → γ} {g : β → γ} (h_fg : f = g ∘ T) : ∑ i ∈ t, f i = ∑ j ∈ s, g j := by
  rcases h_bij with ⟨h_mapsto, h_inj, h_surj⟩
  apply Finset.sum_bij
  . apply h_mapsto
  . apply h_inj
  . convert h_surj
    simp [Set.SurjOn]
    rfl
  . tauto

open Classical

lemma Finset.sum_enlarge {ι α : Type*} [AddCommMonoid α] {t s : Finset ι} {f : ι → α} (h_ts : t ⊆ s) (h_f : ∀ i ∉ t, f i = 0) : ∑ i ∈ t, f i = ∑ i ∈ s, f i := by
  induction' s using Finset.strongInductionOn with s ih
  by_cases h : t = s
  . rw [h]
  have : t ⊂ s := ssubset_of_subset_of_ne h_ts h
  rcases (Finset.ssubset_iff_of_subset h_ts).mp this with ⟨x, h_xs, h_xt⟩
  let s' := s.erase x
  have h_ts' : t ⊆ s' := by
    refine Finset.subset_erase.mpr ?_
    constructor <;> assumption
  rw [ih s' (Finset.erase_ssubset h_xs) h_ts']
  apply Finset.sum_erase
  exact h_f x h_xt

end

lemma reindex_conicalCombo' {s : Set V} {x : V} {ι : Type*} (t : Finset ι) (a : ι → ℝ) (v : ι → V) : isConicalCombo' s x t a v → isConicalCombo_aux s x t.card := by
  rintro ⟨h_av, h_x_combo⟩
  have := (Finset.equivFin t).symm
  set N := t.card
  by_cases hN : N = 0
  . rw [hN]
    use (λ n ↦ 0), (λ n ↦ 0), by simp
    rw [Finset.sum_range_zero, h_x_combo]
    have : t = ∅ := Finset.card_eq_zero.mp hN
    rw [this]
    simp
  replace hN : N > 0 := Nat.zero_lt_of_ne_zero hN
  set F : ℕ → ι := Subtype.val ∘ (Finset.equivFin t).symm ∘ λ n ↦ if hn : n < N then (⟨n, hn⟩ : Fin N) else (⟨0, hN⟩ : Fin N)
  have h_F : Set.BijOn F (Finset.range N) t := by
    repeat' constructor
    . simp [Set.MapsTo, F]
    . simp [Set.InjOn, F]
      intro n₁ hn₁ n₂ hn₂ h_eq
      rw [dif_pos hn₁, dif_pos hn₂] at h_eq
      have : Function.Injective (Subtype.val : { x // x ∈ t } → ι) := by simp
      replace h_eq := this h_eq
      have : Function.Injective t.equivFin.symm := t.equivFin.symm.injective
      have := this h_eq
      exact Fin.val_congr this
    . intro i h_it
      simp
      have : Function.Surjective t.equivFin.symm := t.equivFin.symm.surjective
      rcases this ⟨i, h_it⟩ with ⟨⟨n, hn⟩, h_eq⟩
      use n, hn
      simp [F]
      rw [dif_pos hn, h_eq]
  set a' : ℕ → ℝ := a ∘ F
  set v' : ℕ → V := v ∘ F
  use a', v'
  repeat' constructor
  . intro i _
    dsimp [a', v']
    apply h_av
    apply h_F.1
    simpa
  . dsimp [a', v']
    rw [h_x_combo]
    symm
    apply sum_bijon
    . simp; convert h_F; simp [h_F]
    . ext; simp

lemma reindex_conicalCombo (s : Set V) (x : V) : isConicalCombo s x ↔ ∃ n, isConicalCombo_aux s x n := by
  constructor
  . rintro ⟨ι, t, a, v, h⟩
    use t.card
    exact reindex_conicalCombo' _ _ _ h
  . rintro ⟨n, a, v, h_av, h_x_combo⟩
    let ℕ' := ULift ℕ
    let I := Finset.map (Function.Embedding.mk (@ULift.up Nat) (@ULift.up.inj Nat)) (Finset.range n)
    let a' : ℕ' → ℝ := fun i ↦ a i.down
    let v' : ℕ' → V := fun i ↦ v i.down
    use ℕ', I, a', v'
    simp [isConicalCombo', ℕ', I, a', v', Finset.mem_range]
    use h_av

lemma reduce_conicalCombo (s : Set V) (x : V) {n : ℕ} {a : ℕ → ℝ} (v : ℕ → V) : (∃ j < n + 1, a j = 0) → isConicalCombo_aux' s x (n + 1) a v → isConicalCombo_aux s x n := by
  rintro ⟨j, h_j⟩ ⟨h_av, h_x_combo⟩
  convert reindex_conicalCombo' ((Finset.range (n + 1)).erase j) a v ?_
  . have := Finset.card_erase_add_one (Finset.mem_range.mpr h_j.1)
    simp at this
    rw [this]
  . unfold isConicalCombo'
    constructor
    . intro i h_i
      rw [Finset.mem_erase, Finset.mem_range] at h_i
      exact h_av i h_i.2
    . have : a j • v j = 0 := by rw [h_j.2]; simp
      rw[Finset.sum_erase (Finset.range (n + 1)) this]

def ULift.list.{u, v} {α : Type v} : List α → List (ULift.{u, v} α)
  | [] => []
  | a :: t => ULift.up a :: ULift.list t

lemma isconicalCombo_aux_le (s : Set V) (x : V) : m ≤ n → isConicalCombo_aux s x m → isConicalCombo_aux s x n := by
  intro h_mn
  rintro ⟨a, v, h_av, h_x_combo⟩
  let a' : ℕ → ℝ := fun i => if h_im : i < m then a i else 0
  use a', v
  repeat' constructor
  . intro i h_in
    by_cases h_im : i < m
    . simp [a', if_pos h_im]
      exact h_av i h_im
    . simp [a', if_neg h_im]
  . have h₁ : Finset.range m ⊆ Finset.range n := by simp; linarith
    have h₂ : ∀ i ∈ Finset.range n, i ∉ Finset.range m → a' i • v i = 0 := by
      simp [a']
      intros
      linarith
    rw [←Finset.sum_subset h₁ h₂]
    simp [a']
    rw [Finset.sum_ite_of_true, h_x_combo]
    intro i hi
    rw [Finset.mem_range] at hi
    exact hi

variable [FiniteDimensional ℝ V]
open Finset Module

theorem caratheordory (s : Set V) : ∀ x ∈ conicalHull.{_,0} s, isConicalCombo_aux s x (finrank ℝ V) := by
  rintro x h
  rcases (reindex_conicalCombo s x).mp h with ⟨n, h⟩
  induction' n with N ih
  . exact isconicalCombo_aux_le s x (Nat.zero_le _) h
  by_cases hN : N + 1 ≤ finrank ℝ V
  . exact isconicalCombo_aux_le s x hN h
  push_neg at hN
  rcases h with ⟨a, v, h_av, h_x_combo⟩
  apply ih

  wlog h_a_all_pos : ∀ i < N + 1, a i ≠ 0 generalizing
  . push_neg at h_a_all_pos
    apply reduce_conicalCombo s x v h_a_all_pos
    exact ⟨h_av, h_x_combo⟩
    
  have : ¬ LinearIndepOn ℝ v (range (N + 1)) := by
    intro h
    absurd hN
    rw [not_lt]
    have := LinearIndepOn.encard_le_toENat_rank h
    simp only [Set.encard_coe_eq_coe_finsetCard] at this
    simp at this
    have := ENat.toNat_le_toNat this
      (by simp; exact Module.rank_lt_aleph0 ℝ V)
    exact this
  replace := (not_congr linearIndepOn_iff'').mp this
  push_neg at this
  rcases this with ⟨t, b, h_t_sub_range, h_b_comp, h_b_combo_eq_0, j, h_jt, h_j_ne_0⟩
  wlog h' : t = range (N + 1) generalizing t
  . apply this (range (N + 1))
    all_goals clear this h'; try simp
    . intro i hiN
      have : i ∉ t := by
        intro h_it
        have := h_t_sub_range h_it
        have := mem_range.mp this
        linarith
      exact h_b_comp i this
    . rw [←h_b_combo_eq_0]
      symm
      apply sum_enlarge
      . assumption
      . intro i h_it
        rw [h_b_comp i h_it]
        simp
    . have := h_t_sub_range h_jt
      apply mem_range.mp
      exact this
  rw [h'] at h_b_combo_eq_0 h_jt
  clear h_t_sub_range h_b_comp h' t
  wlog h_b_j_pos : b j > 0 generalizing b
  . let b' := -b
    apply this b' <;> simp [b']
    . assumption
    . simp [h_b_combo_eq_0]
    . simp at h_b_j_pos
      exact lt_of_le_of_ne h_b_j_pos h_j_ne_0
  clear h_j_ne_0

  let ratios : Finset ℝ := ((Finset.range (N + 1)).filter (λ i => b i ≠ 0)).image (λ i => a i / b i)
  let ratios_non_neg : Finset ℝ := ratios.filter (λ r => r ≥ 0)
  have hratio_nonem : ratios_non_neg.Nonempty := by
    unfold ratios_non_neg
    unfold ratios
    have a_j_geq_zero : a j ≥ 0 := by
      cases (h_av j (List.mem_range.mp h_jt)) <;> linarith
    unfold Finset.Nonempty
    use a j / b j
    have hj₁ : j ∈ {i ∈ range (N + 1) | b i ≠ 0} := by
      simp
      refine ⟨?_,?_⟩
      · apply List.mem_range.mp h_jt
      · linarith
    simp
    refine ⟨?_,?_⟩
    · use j
      refine ⟨⟨?_,?_⟩,?_⟩
      · apply List.mem_range.mp h_jt
      · linarith
      · rfl
    apply div_nonneg <;> linarith

  set β := (ratios_non_neg : Finset ℝ).min' hratio_nonem with hβ_def
  have hβ_mem : β ∈ ratios_non_neg := (ratios_non_neg).min'_mem hratio_nonem
  have ⟨h_ratios, h_βgeq0⟩ := mem_filter.mp hβ_mem
  rcases mem_image.mp h_ratios with ⟨i₀,i₀_in_range,hi₀_is_index_β⟩

  replace h_b_combo_eq_0 : ∑ i ∈ range (N + 1),  (β * b i) • v i = 0 := by
    have : β • (∑ i ∈ range (N + 1),  b i • v i) = 0 := by
      exact smul_eq_zero_of_right β h_b_combo_eq_0
    have : ∑ i ∈ range (N + 1),  β • b i • v i = 0 := by
      rw [← Finset.smul_sum]
      exact this
    simp [← smul_assoc] at this
    exact this
  rw [← sub_zero (∑ i ∈ range (N + 1), a i • v i)] at h_x_combo
  rw [← h_b_combo_eq_0] at h_x_combo
  have x_plus_zero : x = ∑ i ∈ range (N + 1), ((a - β • b) i • v i) := by
    simp [sub_smul, Finset.sum_sub_distrib]
    exact h_x_combo

  have h_all_ai_βbi_nonneg : ∀ i < N + 1, 0 ≤ (a i - β * b i)  := by
    intro j h_j_in_range
    have h_aj_non_neg : 0 ≤ a j  := by
          rcases h_av j h_j_in_range with h_aj_zero | ⟨h_ai_geq_zero,_⟩ <;> linarith
    by_cases h_bj_zero : b j ≤ 0
    · have : β * b j ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos h_βgeq0 h_bj_zero
      have : - β * b j ≥ 0 := by
        simp
        exact this
      linarith
    · push_neg at h_bj_zero
      have h_β_is_min : β ≤ a j / b j  := by
        have h_ajbj_in_ratios_non_neg : (a j / b j) ∈ ratios_non_neg := by
          unfold ratios_non_neg
          repeat rw [mem_filter, mem_image]
          refine ⟨?_,?_⟩
          · use j
            refine ⟨?_,rfl⟩
            · apply mem_filter.mpr
              refine ⟨?_,?_⟩
              · exact mem_range.mpr h_j_in_range
              · linarith
          · apply div_nonneg
            · exact h_aj_non_neg
            · linarith [h_bj_zero]
        apply Finset.min'_le ratios_non_neg (a j / b j) h_ajbj_in_ratios_non_neg

      have : β * b j ≤ a j / b j * b j  := by
        exact mul_le_mul_of_nonneg_right h_β_is_min (le_of_lt h_bj_zero)

      have : β * b j ≤ a j := by
        exact (le_div_iff₀ h_bj_zero).mp h_β_is_min

      exact sub_nonneg_of_le this

  have h_i₀_ai_βbi_zero : (a - β • b) i₀ = 0 := by
    rw [← hi₀_is_index_β]
    have hbi₀_nonzero : b i₀ ≠ 0 := (mem_filter.mp i₀_in_range).2
    simp [hbi₀_nonzero]

  have : i₀ < N + 1 := by
    rw [←mem_range]
    exact (mem_filter.mp i₀_in_range).1
  apply reduce_conicalCombo s x v ⟨i₀, this, h_i₀_ai_βbi_zero⟩
  refine ⟨?_, x_plus_zero⟩
  intro i h_i
  right
  constructor
  . exact h_all_ai_βbi_nonneg i h_i
  . rcases h_av i h_i with h | h
    . absurd h
      exact h_a_all_pos i h_i
    . exact h.2

end

section
variable {ι : Type u}

lemma nonneg_orthant_closed : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i } := by
  rw [Set.setOf_forall fun i (x : ι → ℝ) => 0 ≤ x i]
  apply isClosed_iInter
  intro i
  apply IsClosed.preimage (continuous_apply i) isClosed_Ici

variable [Finite ι] [DecidableEq ι]

def std_basis : ι → (ι → ℝ) := fun i j => if i = j then 1 else 0

lemma nonneg_orthant_gens : {x : ι → ℝ | ∀ i, 0 ≤ x i } = conicalHull.{_, u} (std_basis '' Set.univ) := by
  ext x; constructor <;> intro h
  have := Fintype.ofFinite ι
  . use ι, Finset.univ, x, std_basis
    constructor
    . intro i h'
      right
      constructor
      . exact h i
      . use i, ?_
        apply Set.mem_univ
    . exact pi_eq_sum_univ x
  . rcases h with ⟨α, t, a, v, h₁, rfl⟩
    intro i
    simp
    apply Finset.sum_nonneg
    intro x h_xt
    rcases h₁ x h_xt with h | h
    . simp [h]
    . apply mul_nonneg
      . exact h.left
      . rcases h.right with ⟨j, _, h⟩
        rw [←h]
        unfold std_basis
        apply ite_nonneg <;> norm_num

--lemma nonneg_orthant_gens' : {x : ι → ℝ | ∀ i, 0 ≤ x i } = conicalHull {x : ι → ℝ | ∃ i, x i = 1 ∧ ∀ j ≠ i, x j = 0 } := by sorry
end

section
variable {V : Type*} [NormedAddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
open Set Module

--proposition 1.3.3(b)
theorem conical_hull_closed_of_finite (s : Set V) : s.Finite → IsClosed (conicalHull s) := by
  generalize h_dim : finrank ℝ V = n
  revert V
  induction' n with n ih <;> intro V _ _ _ s h_dim h_s
  . rw [finrank_zero_iff] at h_dim
    have : s = ∅ ∨ ∃ (x : V), s = {x} := Subsingleton.eq_empty_or_singleton subsingleton_of_subsingleton
    rcases this with h | h <;> exact isClosed_discrete (conicalHull s)
  . --use caratheordory to get a finset t of s of card n+1
    --proof by cases : t linearly independent or not
    --if not, induct
    --else:
    --use basisOfLinearIndependentOfCardEqFinrank
    --unpack the Basis to get the linear equiv to ℝ^n that we want
    --use nonneg_orthant_gens and nonneg_orthant_closed
    sorry

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
open Bornology RealInnerProductSpace

lemma infDist_points (A B : Set V) (h_closed : IsClosed A ∧ IsClosed B) (h_nonempty : A.Nonempty ∧ B.Nonempty) (hA_Bounded : IsBounded A) : ∃ a₀ ∈ A, ∃ b₀ ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a₀ b₀ ≤ dist a b := by
  rcases h_nonempty.left with ⟨a, h_aA⟩
  rcases h_nonempty.right with ⟨b, h_bB⟩
  let K (r : ℝ) : Set V := { x : V | Metric.infDist x A ≤ r}
  have BcapK : ∃ r ≥ 0, ((K r) ∩ B).Nonempty := by
    use (dist b a)
    simp[dist_nonneg]
    use b
    constructor
    . dsimp [K]
      apply Metric.infDist_le_dist_of_mem
      exact h_aA
    . exact h_bB
  have h_continuous : Continuous (fun x ↦ Metric.infDist x A) := by
    exact Metric.continuous_infDist_pt A
  have Kclosed (r: ℝ) (hr : r ≥ 0) : IsClosed (K r) := by
    have h_closed_Iic : IsClosed (Set.Iic r) := isClosed_Iic
    exact IsClosed.preimage h_continuous h_closed_Iic
  have Kbounded (r: ℝ) (hr: r ≥ 0) : IsBounded (K r) := by
    have subset: K r ⊆ Metric.ball a (Metric.diam A + r+1) := by
      dsimp[K,Metric.ball]
      simp
      intro b
      have ex_a' : ∃ a', a' ∈ A ∧ Metric.infDist b A  = dist b a' := by
        apply IsClosed.exists_infDist_eq_dist h_closed.1 h_nonempty.1 b
      obtain ⟨a', ha', hdist⟩ := ex_a'
      rw[hdist]
      intro hba'
      calc
        dist b a  ≤  dist b a' + dist a' a:= by apply dist_triangle
        _ ≤ r +  dist a' a:= by simp[hba']
        _ ≤ r +  Metric.diam A:= by linarith[Metric.dist_le_diam_of_mem hA_Bounded ha' h_aA]
      linarith
    rw [Metric.isBounded_iff_subset_ball a]
    use (Metric.diam A + r+1)
  have Kcompact (r : ℝ) (hr : r ≥ 0) : IsCompact (K r) := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    exact ⟨Kclosed r hr, Kbounded r hr⟩
  have Knempty (r : ℝ) (hr : r ≥ 0) : (K r).Nonempty := by
    use a
    dsimp [K]
    rw[Metric.infDist_zero_of_mem]
    exact hr
    exact h_aA
  have closedInter (r: ℝ) {hr: r ≥ 0} : IsClosed ((K r) ∩ B) := by
    exact IsClosed.inter (Kclosed r hr) (h_closed.2)
  rcases BcapK with ⟨r₀, h_r₀_ge_0, h_inter_nonempty⟩
  let distBtoA := Set.image (fun b => Metric.infDist b A) ((K r₀) ∩ B)
  --maybe this instead
  --let distBtoA := (fun b => Metric.infDist b A)'' B
  --show that (K r) ∩ B is bounded, therefore compact
  have h_compact : IsCompact (K r₀ ∩ B) := by
    rw[Metric.isCompact_iff_isClosed_bounded]
    simp[IsClosed.inter (Kclosed r₀ h_r₀_ge_0) (h_closed.2)]
    have h: (K r₀ ∩ B) ⊆ K r₀ := by exact Set.inter_subset_left
    exact Bornology.IsBounded.subset (Kbounded r₀ h_r₀_ge_0) h
  have := IsCompact.exists_isMinOn h_compact h_inter_nonempty (Continuous.continuousOn h_continuous)
  rcases this with ⟨b', hb'⟩
  have min_a : ∃ a, a ∈ A ∧ Metric.infDist b' A  = dist b' a := by
    apply IsClosed.exists_infDist_eq_dist h_closed.1 h_nonempty.1 b'
  rcases min_a with ⟨a', ha'⟩
  clear! a b
  use a', ha'.1, b', hb'.1.2
  intro a h_aA b h_bB
  by_cases h_bK : b ∈ K r₀
  . rw [dist_comm, ←ha'.2, dist_comm]
    have min_infDist := isMinOn_iff.mp hb'.2 b ⟨h_bK, h_bB⟩
    suffices h : Metric.infDist b A ≤ dist b a by linarith
    exact Metric.infDist_le_dist_of_mem h_aA
  calc
    dist a' b' ≤ r₀ := by
      rw [dist_comm, ←ha'.2]
      exact hb'.1.1
    _ ≤ Metric.infDist b A := by
      apply le_of_not_ge
      exact h_bK
    _ ≤ dist a b := by
      rw [dist_comm]
      exact Metric.infDist_le_dist_of_mem h_aA

theorem hyperplane_separation  (A B : Set V) (hA : Convex ℝ A) (hB : Convex ℝ B) (hclosed : IsClosed A ∧ IsClosed B ) (hNempty : A.Nonempty ∧ B.Nonempty) (hA_Bounded: IsBounded A) (hAB : Disjoint A B) : ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), (∀ a ∈ A, f a < c) ∧ (∀ b ∈ B, c < f b) := by
  rcases infDist_points A B hclosed hNempty hA_Bounded with ⟨a', h_a'A, b', h_b'B, h_a'b'_min_dist⟩
  let f: V → ℝ  := fun x => ⟪b'-a', x⟫
  have a_not_b: a' ≠ b' := by
    intro h
    have h_a'B: a' ∈ B := by
      rw [h]
      exact h_b'B
    have h_inter: a' ∈ A ∩ B := by exact Set.mem_inter h_a'A h_a'B
    rw[Set.disjoint_iff_inter_eq_empty] at hAB
    have contra: A ∩ B ≠ ∅  := by
      simp[Set.nonempty_of_mem h_inter, ← Set.nonempty_iff_ne_empty]
    contradiction

  have h_prods_ineq: f b' > f a' := by
    have h_greater_zero: 0 < ‖b'-a'‖^2:= by
      have h1: 0 ≤   ‖b'-a'‖^2 := by simp[sq_nonneg]
      have h2 :  ‖b' - a'‖ ≠ 0 := by
        intro h
        rw[norm_eq_zero] at h
        rw[sub_eq_zero] at h
        symm at h
        contradiction
      simp[h1, h2, sq_pos_iff]
    have intermediate_step: 0 < f b' - f a' := by
      calc
        0 < ‖b'-a'‖^2 := by exact h_greater_zero
        _ = ⟪b', b'⟫ - 2*⟪b', a'⟫ + ⟪a', a'⟫ := by
          simp [norm_sub_sq_real, real_inner_self_eq_norm_sq]
        _ = ⟪b', b'⟫ - ⟪b', a'⟫ - (⟪b', a'⟫ - ⟪a', a'⟫) := by linarith
        _ = ⟪b', b'⟫ - ⟪b', a'⟫ - ⟪b'-a', a'⟫ := by rw [← inner_sub_left]
        _ = ⟪b', b'⟫ - ⟪a', b'⟫ - ⟪b'-a', a'⟫ := by simp[real_inner_comm]
        _ = ⟪b'-a', b'⟫ - ⟪b'-a', a'⟫ := by rw [← inner_sub_left]
        _ = f b' - f a' := by simp[f]
    linarith
  have minf : ∀ b₀ ∈ B, f b₀ ≥ f b' := by
    intro b₀ hb₀
    have lin_dep (γ : ℝ) : (0 ≤ γ) ∧ (γ ≤ 1) → γ • b' + (1-γ) • b₀ ∈ B :=
      fun ⟨h, _⟩ => hB h_b'B hb₀ h (by linarith) (by simp)
    have equality_inner_prods (γ : ℝ) (hγ: γ ≥ 0) (hγ': γ ≤ 1): ‖γ•b' + (1-γ)•b₀-a'‖^2 = ‖b'-a'‖^2 + (1-γ)^2*‖b₀-b'‖^2 + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫  := by
      calc
        ‖γ•b' + (1-γ)•b₀-a'‖^2 = ‖γ•b' + b' - b' + (1-γ)•b₀-a'‖^2 := by simp
        _ = ‖(b' - a') + (1-γ )•(b₀- b')‖^2 := by congr 2; module
        _ = ⟪ (b' - a') + ((1-γ )•(b₀- b')) ,  (b' - a') + ((1-γ )•(b₀- b')) ⟫  := by simp[real_inner_self_eq_norm_sq]
        _ = ⟪b'-a', b'-a'⟫ + ⟪b'-a', (1-γ )• (b₀-b')⟫ + ⟪ (1-γ )• (b₀-b'), b'-a' ⟫  + ⟪(1-γ)• (b₀-b'), (1-γ)• (b₀-b')⟫ := by simp[inner_add_add_self]
        _ = ⟪b'-a', b'-a'⟫ + (1-γ)*⟪b'-a', b₀-b'⟫ + (1-γ)*⟪ b'-a', b₀ -b' ⟫  + (1-γ)*(⟪(1-γ)•(b₀-b'),  b₀-b'⟫) := by simp[real_inner_smul_left , real_inner_smul_right, real_inner_comm]
        _ = ⟪b'-a', b'-a'⟫ + 2*(1-γ)*⟪ b'-a', b₀ -b' ⟫  + (1-γ)*(⟪(1-γ)• (b₀-b'), b₀-b'⟫):= by ring
        _ = ⟪b'-a', b'-a'⟫ + 2*(1-γ)*⟪ b'-a', b₀ -b' ⟫  + (1-γ)*((1-γ)*⟪ b₀-b', b₀-b'⟫) := by simp[real_inner_smul_left]
        _ = ⟪(b'-a'), (b'-a')⟫ + (1-γ)^2 * ⟪(b₀-b'), (b₀-b')⟫ + 2*(1-γ)*⟪ b'- a', b₀ - b'⟫:= by ring
        _ = ‖b'-a'‖^2 + (1-γ)^2 * ‖b₀-b'‖^2  + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫ := by simp [real_inner_self_eq_norm_sq]

    have ineq1 (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1): 0 ≤  ‖b'-a'‖^2 + (1-γ)^2 * ‖b₀-b'‖^2  + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫ := by
      rw[← equality_inner_prods]; simp[norm_nonneg]; exact hγ; exact hγ'

    have ineq2 (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1):  ‖b' - a'‖ ≤ ‖(γ • b' + (1-γ) • b₀) - a'‖ := by
      rw[←dist_eq_norm, ←dist_eq_norm, dist_comm, dist_comm _ a']
      apply h_a'b'_min_dist _ h_a'A _ (lin_dep γ ⟨hγ, hγ'⟩)

    have combo_inequalities (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1) : 0 ≤ (1-γ)^2*‖b₀-b'‖^2 + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫ := by
      --have intermediate: ‖‖ ≤ ‖b'-a'‖^2 + (1-γ)^2*‖b₀-b'‖^2 + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫
      have dummy: ‖b'-a'‖^2  ≤ ‖b'-a'‖^2 + (1-γ)^2 * ‖b₀-b'‖^2  + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫:= by
        rw[← equality_inner_prods]
        rw[sq_le_sq]; repeat rw[abs_norm]
        apply ineq2; exact hγ; exact hγ'; exact hγ; exact hγ'
      linarith

    by_cases h : ⟪b'-a', b₀ - b'⟫ = 0
    . suffices h' : f b₀ = f b' by linarith
      rw[inner_sub_right] at h
      linarith
    have hb_ne_b : b₀ ≠ b' := by
      intro h'
      rw[inner_sub_right] at h
      have h_lemma: ⟪b'-a', b'⟫ - ⟪b'-a', b'⟫ = 0 := by linarith
      rw[h'] at h
      contradiction
    have almost_done' : 2* ⟪b'-a', b₀ - b'⟫ ≥ 0 := by
      by_contra! le_0_inner
      let γ' := 1 - |2* ⟪b'-a', b₀ - b'⟫| / (‖b₀ - b'‖^2)

      have not_zero_denom: ‖b₀-b'‖^2 ≠ 0 := by
           simp; have hb_minus_b: b₀ - b' ≠ 0 := by rw[sub_ne_zero]; exact hb_ne_b
           by_contra; contradiction
      have greater_zero_denom : 0 < ‖b₀ -b'‖^2 := by
          apply LE.le.lt_of_ne'
          simp[norm_nonneg]
          exact not_zero_denom

      have choice_γ (γ : ℝ) (h_ineqγ: γ' < γ ): (1-γ)*‖b₀-b'‖^2 < -2* ⟪b'-a', b₀ - b'⟫ := by
        have refined: 1- γ < |2* ⟪b'-a', b₀ - b'⟫| / (‖b₀ - b'‖^2) := by
          unfold γ' at h_ineqγ; linarith
        calc
          (1-γ)*‖b₀-b'‖^2 < (|2* ⟪b'-a', b₀ - b'⟫| / (‖b₀ - b'‖^2)) * ‖b₀-b'‖^2 := by
            rw[mul_lt_mul_right]
            exact refined; exact greater_zero_denom
          _ = |2* ⟪b'-a', b₀ - b'⟫| * 1 / ‖b₀ - b'‖^2 * ‖b₀-b'‖^2 := by simp
          _ = |2* ⟪b'-a', b₀ - b'⟫| * (1 / ‖b₀ - b'‖^2 * ‖b₀-b'‖^2) := by ring
          _ = |2* ⟪b'-a', b₀ - b'⟫| *1 := by rw[one_div_mul_cancel]; exact not_zero_denom
          _ = -2* ⟪b'-a', b₀ - b'⟫ := by simp; apply LT.lt.le; simp[le_0_inner]

      have factored (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1)(γ_ne1: 1 ≠ γ)  :  -2* ⟪b'-a', b₀ - b'⟫ ≤ (1-γ)*‖b₀-b'‖^2  := by
        have h_pos_γ: 0 < 1-γ  := by
            by_contra; have h'_1 : 1 -γ ≤ 0 := by linarith
            have h'_2: 1 ≤ γ := by linarith
            have h'_3: 1 < γ := by rw[lt_iff_le_and_ne]; exact ⟨h'_2, γ_ne1⟩
            linarith [h'_3, hγ']
        have h: 0 ≤ (1-γ)*((1-γ)*‖b₀-b'‖^2 + 2 * ⟪b'-a', b₀ - b'⟫) := by
           calc
             0 ≤ (1-γ)^2*‖b₀-b'‖^2 + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫ := by apply combo_inequalities; exact hγ; exact hγ'
             _ = (1-γ)*(1-γ)*‖b₀-b'‖^2 + (1-γ) * 2 * ⟪b'-a', b₀ - b'⟫ := by simp[sq, mul_comm]
             _ = (1-γ)*((1-γ)*‖b₀-b'‖^2) + (1-γ) * (2 * ⟪b'-a', b₀ - b'⟫) := by repeat rw[mul_assoc]
             _ = (1-γ)*((1-γ)*‖b₀-b'‖^2 + 2*⟪b'-a', b₀ - b'⟫) := by rw[← mul_add]
        have simplify: 0 ≤ ((1-γ )*‖b₀-b'‖^2 + 2 * ⟪b'-a', b₀ - b'⟫) := by apply nonneg_of_mul_nonneg_right h h_pos_γ
        simp[simplify]; linarith

      have inRange:  γ' < 1 := by
          have h1: |2* ⟪b'-a', b₀ - b'⟫| / ‖b₀ - b'‖ ^ 2 = |2* ⟪b'-a', b₀ - b'⟫| / |‖b₀ - b'‖ ^ 2| := by simp[← sq_abs]
          have h2: |2* ⟪b'-a', b₀ - b'⟫| / |‖b₀ - b'‖ ^ 2| = |2* ⟪b'-a', b₀ - b'⟫ / ‖b₀ - b'‖ ^ 2| := by simp[abs_div]
          have h3: |2* ⟪b'-a', b₀ - b'⟫ / ‖b₀ - b'‖ ^ 2| > 0 := by
            simp[abs_pos]
            have h_right: ¬b₀ - b' = 0 := by
              exact sub_ne_zero_of_ne hb_ne_b
            have h_left: ¬⟪b' - a', b₀ - b'⟫ = 0 := by
              exact h
            exact ⟨h_left, h_right⟩
          simp; unfold γ'; rw[h1]; rw[h2]; linarith

      have cases_γ : γ' < 0 := by
        by_contra! h
        let γ_fit := (γ' + 1)/2
        have less_upper: γ_fit < 1 :=  by
          unfold γ_fit; rw[add_div_two_lt_right]; exact inRange
        have greater_lower: γ' < γ_fit := by
          unfold γ_fit; rw[left_lt_add_div_two]; exact inRange
        have ge_zero: γ_fit ≥ 0 := by linarith
        have le_one: γ_fit ≤ 1 := by linarith
        have not_one: 1 ≠ γ_fit  := by symm; exact ne_of_lt less_upper
        absurd factored γ_fit ge_zero le_one not_one
        exact LT.lt.not_le (choice_γ γ_fit greater_lower)
      have cases_γ2 : 0 ≤ γ' := by
        by_contra! h
        let γ_fit: ℝ := 0
        have ge_zero: γ_fit ≥ 0 := by unfold γ_fit; linarith
        have le_one: γ_fit ≤ 1 := by unfold γ_fit; linarith
        have not_one: 1 ≠ γ_fit  := by unfold γ_fit; linarith
        absurd factored γ_fit ge_zero le_one not_one
        exact LT.lt.not_le (choice_γ γ_fit h)
      absurd LT.lt.not_le cases_γ
      exact cases_γ2
    rw[inner_sub_right] at almost_done'
    unfold f
    linarith

  have minf' : ∀ a₀ ∈ A, f a₀ ≤ f a' := by
    intro a₀ ha₀
    have lin_dep (γ : ℝ) : (0 ≤ γ) ∧ (γ ≤ 1) → γ • a' + (1-γ) • a₀ ∈ A :=
      fun ⟨h, _⟩ => hA h_a'A ha₀ h (by linarith) (by simp)

    have equality_inner_prods (γ : ℝ) (hγ: γ ≥ 0) (hγ': γ ≤ 1): ‖γ•a' + (1-γ)•a₀-b'‖^2 = ‖b'-a'‖^2 + (1-γ)^2*‖a₀-a'‖^2 + 2*(1-γ) * ⟪a'-b', a₀ - a'⟫  := by
      calc
        ‖γ•a' + (1-γ)•a₀-b'‖^2 = ‖γ•a' + a' - a' + (1-γ)•a₀-b'‖^2 := by simp
        _ = ‖(a' - b') + (1-γ )•(a₀- a')‖^2 := by congr 2; module
        _ = ⟪ (a' - b') + ((1-γ )•(a₀- a')) ,  (a' - b') + ((1-γ )•(a₀- a')) ⟫  := by simp[real_inner_self_eq_norm_sq]
        _ = ⟪a'-b', a'-b'⟫ + ⟪a'-b', (1-γ )• (a₀-a')⟫ + ⟪ (1-γ )• (a₀-a'), a'-b' ⟫  + ⟪(1-γ)• (a₀-a'), (1-γ)• (a₀-a')⟫ := by simp[inner_add_add_self]
        _ = ⟪a'-b', a'-b'⟫ + (1-γ)*⟪a'-b', a₀-a'⟫ + (1-γ)*⟪ a'-b', a₀ -a' ⟫  + (1-γ)*(⟪(1-γ)•(a₀-a'),  a₀-a'⟫) := by simp[real_inner_smul_left , real_inner_smul_right, real_inner_comm]
        _ = ⟪a'-b', a'-b'⟫ + 2*(1-γ)*⟪ a'-b', a₀ -a' ⟫  + (1-γ)*(⟪(1-γ)• (a₀-a'), a₀-a'⟫):= by ring
        _ = ⟪a'-b', a'-b'⟫ + 2*(1-γ)*⟪ a'-b', a₀ -a' ⟫  + (1-γ)*((1-γ)*⟪ a₀-a', a₀-a'⟫) := by simp[real_inner_smul_left]
        _ = ⟪(a'-b'), (a'-b')⟫ + (1-γ)^2 * ⟪(a₀-a'), (a₀-a')⟫ + 2*(1-γ)*⟪ a'- b', a₀ - a'⟫:= by ring
        _ = ‖a'-b'‖^2 + (1-γ)^2 * ‖a₀-a'‖^2  + 2*(1-γ) * ⟪a'-b', a₀ - a'⟫ := by simp [real_inner_self_eq_norm_sq]
        _ = ‖b'-a'‖^2 + (1-γ)^2 * ‖a₀-a'‖^2  + 2*(1-γ) * ⟪a'-b', a₀ - a'⟫ := by simp[norm_sub_rev]

    have ineq1 (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1): 0 ≤  ‖b'-a'‖^2 + (1-γ)^2 * ‖a₀-a'‖^2  + 2*(1-γ) * ⟪a'-b', a₀ - a'⟫ := by
      rw[← equality_inner_prods]; simp[norm_nonneg]; exact hγ; exact hγ'

    have ineq2 (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1):  ‖b' - a'‖ ≤ ‖(γ • a' + (1-γ) • a₀) - b'‖ := by
      repeat rw[ ←dist_eq_norm]
      rw[dist_comm]
      apply h_a'b'_min_dist
      exact (lin_dep γ ⟨hγ, hγ'⟩); exact h_b'B

    have combo_inequalities (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1) : 0 ≤ (1-γ)^2*‖a₀-a'‖^2 + 2*(1-γ) * ⟪a'-b', a₀ - a'⟫ := by
      --have intermediate: ‖‖ ≤ ‖b'-a'‖^2 + (1-γ)^2*‖b₀-b'‖^2 + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫
      have dummy: ‖b'-a'‖^2  ≤ ‖b'-a'‖^2 + (1-γ)^2 * ‖a₀-a'‖^2  + 2*(1-γ) * ⟪a'-b', a₀ - a'⟫:= by
        rw[← equality_inner_prods]
        rw[sq_le_sq]; repeat rw[abs_norm]
        apply ineq2; exact hγ; exact hγ'; exact hγ; exact hγ'
      linarith

    by_cases h : ⟪a'-b', a₀ - a'⟫ = 0
    . suffices h' : f a₀ = f a' by linarith
      rw[inner_sub_right] at h
      unfold f
      have this_neg_case : ⟪-(b' - a'), a₀⟫ = ⟪-(b' - a'), a'⟫ := by simp; linarith
      repeat rw[inner_neg_left] at this_neg_case
      linarith
    have ha_ne_a : a₀ ≠ a' := by
      intro h'
      rw[inner_sub_right] at h
      have h_lemma: ⟪a'-b', a'⟫ - ⟪a'-b', a'⟫ = 0 := by linarith
      rw[h'] at h
      absurd h; exact h_lemma
    have almost_done' : 2* ⟪a'-b', a₀ - a'⟫ ≥ 0 := by
      by_contra! le_0_inner
      let γ' := 1 - |2* ⟪a'-b', a₀ - a'⟫| / (‖a₀ - a'‖^2)

      have not_zero_denom: ‖a₀-a'‖^2 ≠ 0 := by
           simp; have ha_minus_a: a₀ - a' ≠ 0 := by rw[sub_ne_zero]; exact ha_ne_a
           by_contra; contradiction
      have greater_zero_denom : 0 < ‖a₀ -a'‖^2 := by
          apply LE.le.lt_of_ne'
          simp[norm_nonneg]
          exact not_zero_denom

      have choice_γ (γ : ℝ) (h_ineqγ: γ' < γ ): (1-γ)*‖a₀-a'‖^2 < -2* ⟪a'-b', a₀ - a'⟫ := by
        have refined: 1- γ < |2* ⟪a'-b', a₀ - a'⟫| / (‖a₀ - a'‖^2) := by
          unfold γ' at h_ineqγ; linarith
        calc
          (1-γ)*‖a₀-a'‖^2 < (|2* ⟪a'-b', a₀ - a'⟫| / (‖a₀ - a'‖^2)) * ‖a₀-a'‖^2 := by
            rw[mul_lt_mul_right]
            exact refined; exact greater_zero_denom
          _ = |2* ⟪a'-b', a₀ - a'⟫| * 1 / ‖a₀ - a'‖^2 * ‖a₀-a'‖^2 := by simp
          _ = |2* ⟪a'-b', a₀ - a'⟫| * (1 / ‖a₀ - a'‖^2 * ‖a₀-a'‖^2) := by ring
          _ = |2* ⟪a'-b', a₀ - a'⟫| *1 := by rw[one_div_mul_cancel]; exact not_zero_denom
          _ = -2* ⟪a'-b', a₀ - a'⟫ := by simp; apply LT.lt.le; simp[le_0_inner]

      have factored (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1)(γ_ne1: 1 ≠ γ)  :  -2* ⟪a'-b', a₀ - a'⟫ ≤ (1-γ)*‖a₀-a'‖^2  := by
        have h_pos_γ: 0 < 1-γ  := by
            by_contra; have h'_1 : 1 -γ ≤ 0 := by linarith
            have h'_2: 1 ≤ γ := by linarith
            have h'_3: 1 < γ := by rw[lt_iff_le_and_ne]; exact ⟨h'_2, γ_ne1⟩
            linarith [h'_3, hγ']
        have h: 0 ≤ (1-γ)*((1-γ)*‖a₀-a'‖^2 + 2 * ⟪a'-b', a₀ - a'⟫) := by
           calc
             0 ≤ (1-γ)^2*‖a₀-a'‖^2 + 2*(1-γ) * ⟪a'-b', a₀ - a'⟫ := by apply combo_inequalities; exact hγ; exact hγ'
             _ = (1-γ)*(1-γ)*‖a₀-a'‖^2 + (1-γ) * 2 * ⟪a'-b', a₀ - a'⟫ := by simp[sq, mul_comm]
             _ = (1-γ)*((1-γ)*‖a₀-a'‖^2) + (1-γ) * (2 * ⟪a'-b', a₀ - a'⟫) := by repeat rw[mul_assoc]
             _ = (1-γ)*((1-γ)*‖a₀-a'‖^2 + 2*⟪a'-b', a₀ - a'⟫) := by rw[← mul_add]
        have simplify: 0 ≤ ((1-γ )*‖a₀-a'‖^2 + 2 * ⟪a'-b', a₀ - a'⟫) := by apply nonneg_of_mul_nonneg_right h h_pos_γ
        simp[simplify]; linarith

      have inRange:  γ' < 1 := by
          have h1: |2* ⟪a'-b', a₀ - a'⟫| / ‖a₀ - a'‖ ^ 2 = |2* ⟪a'-b', a₀ - a'⟫| / |‖a₀ - a'‖ ^ 2| := by simp[← sq_abs]
          have h2: |2* ⟪a'-b', a₀ - a'⟫| / |‖a₀ - a'‖ ^ 2| = |2* ⟪a'-b', a₀ - a'⟫ / ‖a₀ - a'‖ ^ 2| := by simp[abs_div]
          have h3: |2* ⟪a'-b', a₀ - a'⟫ / ‖a₀ - a'‖ ^ 2| > 0 := by
            simp[abs_pos]
            have h_right: ¬a₀ - a' = 0 := by
              exact sub_ne_zero_of_ne ha_ne_a
            have h_left: ¬⟪a' - b', a₀ - a'⟫ = 0 := by
              exact h
            exact ⟨h_left, h_right⟩
          simp; unfold γ'; rw[h1]; rw[h2]; linarith

      have cases_γ : γ' < 0 := by
        by_contra! h
        let γ_fit := (γ' + 1)/2
        have less_upper: γ_fit < 1 :=  by
          unfold γ_fit; rw[add_div_two_lt_right]; exact inRange
        have greater_lower: γ' < γ_fit := by
          unfold γ_fit; rw[left_lt_add_div_two]; exact inRange
        have ge_zero: γ_fit ≥ 0 := by linarith
        have le_one: γ_fit ≤ 1 := by linarith
        have not_one: 1 ≠ γ_fit  := by symm; exact ne_of_lt less_upper
        absurd factored γ_fit ge_zero le_one not_one
        exact LT.lt.not_le (choice_γ γ_fit greater_lower)
      have cases_γ2 : 0 ≤ γ' := by
        by_contra! h
        let γ_fit: ℝ := 0
        have ge_zero: γ_fit ≥ 0 := by unfold γ_fit; linarith
        have le_one: γ_fit ≤ 1 := by unfold γ_fit; linarith
        have not_one: 1 ≠ γ_fit  := by unfold γ_fit; linarith
        absurd factored γ_fit ge_zero le_one not_one
        exact LT.lt.not_le (choice_γ γ_fit h)
      absurd LT.lt.not_le cases_γ
      exact cases_γ2
    rw[inner_sub_right] at almost_done'
    unfold f
    have intermed_this: ⟪-(b' - a'), a₀⟫ - ⟪-(b' - a'), a'⟫ ≥ 0 := by simp; linarith
    repeat rw[inner_neg_left] at intermed_this
    linarith

  let fc := (f a'+f b')/2
  have lt_fb: fc < f b' := by unfold fc; rw[add_div_two_lt_right]; apply h_prods_ineq
  have gt_fa: f a' < fc := by unfold fc; rw[left_lt_add_div_two]; exact h_prods_ineq
  have lt_b : ∀ b ∈ B, fc < f b := fun b hbB => lt_of_lt_of_le lt_fb (minf b hbB)
  have gt_a : ∀ a ∈ A, f a < fc := fun a haA => lt_of_le_of_lt (minf' a haA) gt_fa

  let inner_bilin := @bilinFormOfRealInner V inferInstance inferInstance
  unfold LinearMap.BilinForm LinearMap.BilinMap at inner_bilin
  let f_lin := inner_bilin (b' - a')
  have f_eq : f_lin = f := by
    ext v
    rfl
  use f_lin, fc
  rw [f_eq]
  exact ⟨gt_a, lt_b⟩

lemma farkas (u: V)(C: Set V) (convC: Convex ℝ C) (closedC: IsClosed C)(coneC: Cone C): u ∉ C → ∃(y : V →ₗ[ℝ] ℝ), (y u > 0) ∧ (∀ x ∈ C, y x ≤ 0):= by
  intro hu
  have cu_Nempty :  (Set.singleton u).Nonempty ∧ C.Nonempty := by
    unfold Cone at coneC
    exact ⟨Set.singleton_nonempty u, coneC.1⟩
  have andCU :  IsClosed (Set.singleton u) ∧ IsClosed C:= by
    exact ⟨isClosed_singleton, closedC⟩
  have convex_u: Convex ℝ {u} := convex_singleton u
  have disjoint_cu: Disjoint {u} C := by
    rw[Set.disjoint_singleton_left]; exact hu
  have boundedU : IsBounded {u} := by exact Bornology.isBounded_singleton
  rcases hyperplane_separation {u} C convex_u convC andCU cu_Nempty boundedU disjoint_cu with ⟨f, c, hfc⟩
  let g : V →ₗ[ℝ] ℝ := -f
  let c' :ℝ := -c
  --apply (translate_halfspace_of_cone_subset C g c)
  have le_hyp: c' ≥ 0 ∧ ∀ x ∈ C, g x ≤ 0 := by
    apply (translate_halfspace_of_cone_subset C g c')
    exact coneC; unfold g; unfold c'; simp
    intro x hx
    exact le_of_lt (hfc.right x hx)
  use g
  have u_gt: g u > 0 := by
    unfold g; simp
    have obvious: f u < c := by apply hfc.left; simp
    have le_c : c ≤ 0 := by
      unfold c' at le_hyp; linarith
    linarith
  exact ⟨u_gt, le_hyp.2⟩
  
end

section
variable {V : Type*} [NormedAddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

--proposition 1.3.3(b)
theorem conical_hull_closed_of_finite' (s : Set V) : s.Finite → IsClosed (conicalHull s) := by
  intro hs
  let sFin := hs.toFinset
  revert s  
  #check Finset.induction




  --use nonneg_orthant_gens and nonneg_orthant_closed
  sorry

section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

--might be useful:
example (s : Set V) : PolyhedralCone s → ∃ s' : ConvexCone ℝ V, s'.carrier = s := sorry
example (s : Set V) : ∃ s' : ConvexCone ℝ V, s'.carrier = conicalHull s := by sorry

end

--todo:

--theorem farkas : _ := by sorry --uses lemma 1.2.2 and hyperplane_separation
--OR, use hyperplane separation theorem already in mathlib (we only need the statement of Farkas

--see NormedSpace.polar
--theorem 1.5.1
--proposition 1.5.2(b)

--theorem 1.6.1
