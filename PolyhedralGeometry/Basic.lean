import PolyhedralGeometry.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Dimension.Basic
--import Mathlib.Topology.MetricSpace.Defs
--import Mathlib.LinearAlgebra.Dual
--import Mathlib.Topology.Defs.Basic

variable {V: Type*} [AddCommGroup V] [Module ℝ V]

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

def conicalCombo_cards (s : Set V) (x : V) : Set ℕ := Finset.card '' { (t : Finset V) | ∃ (a : V → ℝ), (∀ v ∈ t, 0 ≤ a v) ∧ ↑t ⊆ s ∧ x = ∑ v ∈ t, a v • v}

lemma conicalCombo_cards_nonempty (s : Set V) (x : V) : x ∈ conicalHull s → (conicalCombo_cards s x).Nonempty := by
  intro ⟨vectors,h⟩
  use vectors.card
  exists vectors

--maybe don't need this?
theorem min_elt (s : Set ℕ) (h_s_nonempty : s.Nonempty) : ∃ n ∈ s, ∀ m < n, m ∉ s := by
  rcases h_s_nonempty with ⟨n, h⟩
  induction' n using Nat.strong_induction_on with n ih
  by_cases h' : ∀ m < n, m ∉ s
  . use n
  . push_neg at h'
    rcases h' with ⟨n', h₁, h₂⟩
    exact ih n' h₁ h₂

-- noncomputable def Finset.toIndex {α : Type*} (s : Finset α) : ι → α := by
--   let s' := s.toList

variable [FiniteDimensional ℝ V]

-- open Classical
--theorem 1.3.2(b)
-- theorem caratheordory (s : Set V) (x : V) (h : x ∈ conicalHull s) :
--   ∃ (t : Finset V), ↑t ⊆ s ∧ t.card ≤ Module.finrank ℝ V ∧ x ∈ conicalHull t := by
--   -- rcases h with ⟨u, a, h_a_nonneg, h_u_subset, h_x_combo⟩
--   -- rcases le_or_gt u.card (Module.finrank ℝ V) with h_u_card | h_u_card
--   -- . use u, h_u_subset, h_u_card, u, a
--   -- induction' u using Finset.induction_on with v u h_v_nin_u ih
--   -- . sorry
--   -- . sorry
--   rcases min_elt (conicalCombo_cards s x) (conicalCombo_cards_nonempty s x h) with ⟨n, h', h_minimality⟩
--   rcases h' with ⟨t, ⟨a, h_a_nonneg, h_t_subset, h_x_combo⟩, rfl⟩
--   rcases le_or_gt t.card (Module.finrank ℝ V) with h_t_card | h_t_card
--   . use t, h_t_subset, h_t_card, t, a
--   apply False.elim
--   have h_not_lin_indep : ¬(LinearIndependent ℝ (fun x => x : {x // x ∈ t} → V)) := by
--     intro h
--     have := LinearIndependent.cardinal_le_rank h
--     have := Cardinal.toNat_le_toNat this (Module.rank_lt_aleph0 ℝ V)
--     simp at this
--     linarith!
--   have := Fintype.not_linearIndependent_iff.mp h_not_lin_indep
--   rcases this with ⟨b, h_b_combo, ⟨u, h_u_t⟩, h_b_u_ne_0⟩
--   let b' : V → ℝ := fun v =>
--     if hvt : v ∈ t then b { val := v, property := hvt} else 0
--   have h_b'_u_ne_0 : b' u ≠ 0 := by simp [b']; use h_u_t
--   have h_b'_combo : ∑ v ∈ t, b' v • v = 0 := by
--     simp [b']
--     rw [←h_b_combo, Finset.sum_dite_of_true]
--     simp
--   wlog h' : b' u > 0 generalizing b
--   . push_neg at h'
--     by_cases h'' : b' u = 0
--     . contradiction
--     have h' : b' u < 0 := by
--       apply lt_of_le_of_ne <;> assumption
--     apply this (fun x => - b x)
--     . simpa
--     . simp [h_b_u_ne_0]
--     . simp
--       use h_u_t
--     . suffices ∑ v ∈ t, (if hvt : v ∈ t then -b ⟨v, hvt⟩ • v else 0) = 0 by
--         rw [←this]; congr; simp
--       rw [Finset.sum_dite_of_true (by tauto : ∀ v ∈ t, v ∈ t)]
--       simpa
--     . simp
--       rw [dif_pos h_u_t, lt_neg_iff_add_neg]
--       simp [b', dif_pos h_u_t] at h'
--       linarith

--   show False
--   let ratio : V → ℝ := fun i => (b' i) / (a i)
--   have h_t_nonempty : {x | x ∈ t}.Nonempty := by
--     apply Set.nonempty_of_ncard_ne_zero
--     have : t.card > 0 := by linarith
--     show (↑t : Set V).ncard ≠ 0
--     rw [Set.ncard_coe_Finset]
--     linarith
--   have := Set.exists_max_image {x | x ∈ t} ratio (Set.finite_mem_finset t) h_t_nonempty
--   rcases this with ⟨u', h_u'_t, h_u'_max⟩
--   simp [ratio] at h_u'_max
--   let α := a u' / b' u'
--   have h_b'_u'_ne_0 : b' u' ≠ 0 := by sorry
--   have h₁ : (a - α • b') u' = 0 := by sorry
--   have h₂ : ∀ v ∈ t, (a - α • b') v ≥ 0 := by sorry
--   have h_x_combo' : x = ∑ v ∈ t, (a - α • b') v • v := by sorry
--   have : t.card - 1 ∈ conicalCombo_cards s x := by
--     have h' : {x | x ∈ t ∧ x ≠ u'} ⊆ t := by sorry
--     have : {x | x ∈ t ∧ x ≠ u'}.Finite := Set.Finite.subset (by sorry : (t.toSet).Finite) h'
--     let t' : Finset V := Set.Finite.toFinset this
--     use t'
--     have h_t'_ss_t : t' ⊆ t := by simp [t']; exact h'
--     have t'_def : t = {u'} ∪ t' := by
--       ext v
--       constructor
--       . intro _
--         by_cases h' : v = u'
--         . rw [h']
--           apply Finset.mem_union_left
--           apply Finset.mem_singleton_self
--         . apply Finset.mem_union_right
--           simp [t']
--           constructor <;> assumption
--       . intro h
--         rw [Finset.mem_union] at h
--         rcases h with h | h
--         . have : v = u' := Finset.mem_singleton.mp h
--           rw [this]
--           assumption
--         . simp [t'] at h
--           exact h.left
--     constructor
--     . use a - α • b'
--       constructor
--       . sorry
--       . constructor
--         . sorry
--         . sorry
--     . apply Nat.eq_sub_of_add_eq
--       apply Eq.symm
--       rw [t'_def]
--       calc
--         ({u'} ∪ t').card = ({u'} ∪ t').card + ({u'} ∩ t').card := by sorry
--         _ = ({u'} : Finset V).card + t'.card := by apply Finset.card_union_add_card_inter
--         _ = 1 + t'.card := by congr
--         _ = t'.card + 1 := add_comm _ _
--   have : t.card - 1 < t.card := by sorry -- this is not trivial since 0 - 1 = 0 in Nat (so linarith can't solve it without some help)
--   have := h_minimality (t.card - 1) this
--   contradiction

--================ alternative proof ====================

-- lemma reindex_conicalCombo (s : Set V) (x : V) : isConicalCombo s x ↔ ∃ n, isConicalCombo_aux s x n := by
--   constructor
--   . rintro ⟨α, t, a, v, h_a, h_v, h_x_combo⟩
--     use t.card
--     unfold isConicalCombo_aux
--     have := (Finset.equivFin t).invFun
--     set a' := a ∘ (Finset.equivFin t).invFun
--     set v' := v ∘ (Finset.equivFin t).invFun
--     use a', v'
--     repeat' constructor
--     . simp [a', h_a]
--     . simp [v', h_v]
--     . simp [a', v']
--       rw [h_x_combo]
--       refine Finset.sum_equiv (Finset.equivFin t) (fun i ↦ (by simp)) (by simp)
--   . rintro ⟨n, a, v, h_a, h_v, h_x_combo⟩
--     set a' : Finset.univ → ℝ := a ∘ Subtype.val
--     set v' : Finset.univ → V := v ∘ Subtype.val
--     use Fin n, Finset.univ, a', v'
--     repeat' constructor
--     repeat simpa

-- --set_option pp.explicit true

-- lemma isconicalCombo_aux_le (s : Set V) (x : V) : m < n → isConicalCombo_aux s x m → isConicalCombo_aux s x n := by
--   intro h_mn
--   rintro ⟨a, v, h_a, h_v, h_x_combo⟩
--   by_cases h_s : s.Nonempty
--   . let v₀ : ↑s := ⟨h_s.some, h_s.some_mem⟩
--     let a' : Fin n → ℝ := fun i => if h_im : ↑i < m then a ⟨↑i, h_im⟩ else 0
--     let v' : Fin n → V := fun i => if h_im : ↑i < m then v ⟨↑i, h_im⟩ else v₀
--     use a', v'
--     repeat' constructor
--     . intro i
--       by_cases h_im : i < m
--       . simp [a', dif_pos h_im]
--         exact h_a ⟨i, h_im⟩
--       . simp [a', dif_neg h_im]
--     . intro i
--       by_cases h_im : i < m
--       . simp [v', dif_pos h_im]
--         exact h_v ⟨i, h_im⟩
--       . simp [v', dif_neg h_im]
--     . show x = ∑ i ∈ (Finset.univ : Finset (Fin n)), a' i • v' i
--       simp [a']
--       rw [Finset.sum_dite, Finset.sum_const_zero, add_zero]
--       --show x = ∑ i ∈ (Finset.univ : Finset (Fin n)), a' i • v' i
--       simp [v']
--       rw [Finset.sum_dite_of_true]
--       simp
--       . sorry
--       . intro i h
--         simp at h
--         rcases i with ⟨val, prop⟩
--         simp
--         convert prop
--         --have : val ∈ {x : Fin n | ↑x < m} := prop
--         sorry
--   . sorry

--------------- second try -----------------

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

lemma reindex_conicalCombo' (s : Set V) (x : V) : isConicalCombo' s x ↔ ∃ n, isConicalCombo_aux' s x n := by
  constructor
  . rintro ⟨α, t, a, v, h_av, h_x_combo⟩
    use t.card
    unfold isConicalCombo_aux'
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
    set F : ℕ → α := Subtype.val ∘ (Finset.equivFin t).symm ∘ λ n ↦ if hn : n < N then (⟨n, hn⟩ : Fin N) else (⟨0, hN⟩ : Fin N)
    have h_F : Set.BijOn F (Finset.range N) t := by
      repeat' constructor
      . simp [Set.MapsTo, F]
      . simp [Set.InjOn, F]
        intro n₁ hn₁ n₂ hn₂ h_eq
        rw [dif_pos hn₁, dif_pos hn₂] at h_eq
        have : Function.Injective (Subtype.val : { x // x ∈ t } → α) := by simp
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
  . rintro ⟨n, a, v, h_av, h_x_combo⟩
    use ℕ, Finset.range n, a, v
    simp [Finset.mem_range]
    use h_av

lemma isconicalCombo_aux_le' (s : Set V) (x : V) : m ≤ n → isConicalCombo_aux' s x m → isConicalCombo_aux' s x n := by
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

theorem caratheordory' (s : Set V) : ∀ x ∈ conicalHull' s, isConicalCombo_aux' s x (finrank ℝ V) := by
  rintro x h
  rcases (reindex_conicalCombo' s x).mp h with ⟨n, h⟩
  induction' n with N ih
  . exact isconicalCombo_aux_le' s x (Nat.zero_le _) h
  by_cases hN : N + 1 ≤ finrank ℝ V
  . exact isconicalCombo_aux_le' s x hN h
  push_neg at hN
  rcases h with ⟨a, v, h_av, h_x_combo⟩
  apply ih
  by_cases coefficents_all_zero : ∀ i ∈ (range (N + 1)), a i = 0
  · unfold isConicalCombo_aux'
    · use a
      use v
      constructor
      · intro i i_lt_N
        have i_in_range : i ∈ range (N + 1) := by
          apply mem_range.mpr
          linarith
        apply Or.inl (coefficents_all_zero i i_in_range)
      · have x_is_zero : x = 0 := by
          rw [h_x_combo]
          apply sum_eq_zero
          intro i₀ i₀_in_range
          have a_i₀_eq_zero : a i₀ = 0 := by
            exact coefficents_all_zero i₀ i₀_in_range
          rw [a_i₀_eq_zero]
          simp
        rw [x_is_zero]
        apply Eq.symm
        apply sum_eq_zero
        intro i₀ i₀_in_range
        have i₀_lq_N : i₀ < N := by
          apply mem_range.mp
          exact i₀_in_range
        have i₀_in_range_plus_one : i₀ ∈ range (N + 1) := by
          simp
          linarith
        have a_i₀_eq_zero : a i₀ = 0 := by
          exact coefficents_all_zero i₀ i₀_in_range_plus_one
        rw [a_i₀_eq_zero]
        simp
  push_neg at coefficents_all_zero
  rcases coefficents_all_zero with ⟨i₀,i₀_in_range,a₀_not_zero⟩
  replace a₀_not_zero : ¬(a i₀ = 0) := by simp [a₀_not_zero]
  have h_a₀_pos : 0 < a i₀ := by
    have : i₀ < N + 1 := by apply mem_range.mp i₀_in_range
    exact lt_of_le_of_ne (Or.resolve_left (h_av i₀ this) a₀_not_zero).left (id (Ne.symm a₀_not_zero))
  --let t : Finset V := image v (range (N + 1))
  have : ¬ LinearIndepOn ℝ v (range (N + 1)) := by
    intro h
    absurd hN
    rw [not_lt]
    have := LinearIndepOn.encard_le_toENat_rank h
    simp only [Set.encard_coe_eq_coe_finsetCard] at this
    simp at this
    have := ENat.toNat_le_toNat this
      (by simp; exact Module.rank_lt_aleph0 ℝ V)
    -- simp at this
    -- rw [←finrank] at this
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
  clear h_t_sub_range h_b_comp h' t a₀_not_zero
  wlog h' : b j > 0 generalizing b
  . let b' := -b
    apply this b'
    . sorry
    . sorry
    . sorry
  clear h_j_ne_0
  sorry

--figure out how closure operators work (to define conicalHull like mathlib's convexHull)

-- 𝕜 is the underlying scalar field (e.g., ℝ or ℚ), assumed to be an ordered ring.
--variable {𝕜 : Type*} [OrderedRing 𝕜]

--Seems like this migh just be (`exists_closed_hyperplane_separating`) in Mathlib 
--Requirements: both A,B convex, at least one compact, A,B disjoint, Normed Vector Space V.
--So theorem HyperPlaneSeparation is just apply exists_closed_hyperplane_separating

-- E is the vector space type, equipped with:
-- 1. An additive commutative group structure (`AddCommGroup`).
-- 2. A module structure over 𝕜 (generalizing vector spaces to arbitrary rings).
-- 3. A topology (`TopologicalSpace`) compatible with addition (`TopologicalAddGroup`).
-- 4. Continuous scalar multiplication (`ContinuousConstSMul`).
variable {E : Type*} [AddCommGroup E] [Module ℝ E][TopologicalSpace E][PseudoMetricSpace E]

#check PseudoMetricSpace
-- A and B are the convex sets we want to separate.

open Bornology
-- The goal: Prove there exists a continuous linear functional `f` and a scalar `c` 
-- such that `f` separates A and B (i.e., `f(a) ≤ c ≤ f(b)` for all `a ∈ A`, `b ∈ B`).

--theorem Metric.isCompact_iff_isClosed_bounded {α : Type u} [PseudoMetricSpace α] {s : Set α} [T2Space α] [ProperSpace α] :
--IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s
theorem HyperplaneSeparation  (A B : Set E) (hA : Convex ℝ A)(hB : Convex ℝ B)  (hB_closed : IsClosed B) (hNempty : A.Nonempty ∧ B.Nonempty) (hA_Bounded: IsBounded A) (hAB : Disjoint A B) : ∃ (f : E →L[ℝ] ℝ) (c : ℝ), (∀ a ∈ A, f a ≤ c) ∧ (∀ b ∈ B, c ≤ f b) := by
  let K_r (r : ℝ) : Set E := { x : E | Metric.infDist x A ≤ r}
  have : ∃ (r : ℝ), (K_r r ∩ B).Nonempty := by
    rcases hNempty.left with ⟨a, h_aA⟩
    rcases hNempty.right with ⟨b, h_bB⟩
    use (dist a b)
    use b
    constructor
    . dsimp [K_r]
      sorry
    . exact h_bB
  sorry

  --WLOG, let A Construct a Set K_r compact around A, defined as all points within r of A, the compact 
  --set within the relation. Let r such that K_r ∩ B ≠ ∅ ∧ K_r ∩ A = A

  --K_r ∩ B ∪ A is compact (show) implies existence of a∈ A, b∈ B ∩ K_r such that d(a,b) is minimal. 
  --In space E, can draw vector f' from a to b.


  -- f' is norm to hyperplane separating A,B. Use this to define hyperplane with f = ⟨f', _ ⟩ 
  -- hyperplane P = f x = c, x ∈ E. Choose c by middle line segment between a,b.


--might be useful:
example (s : Set V) : PolyhedralCone s → ∃ s' : ConvexCone ℝ V, s'.carrier = s := sorry
example (s : Set V) : ∃ s' : ConvexCone ℝ V, s'.carrier = conicalHull s := by sorry

--todo:

variable [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

--proposition 1.3.3(b)
--theorem conical_hull_closed_of_finite : _ := by sorry

--theorem hyperplane_separation : _ := by sorry --use heine-borel for compactness (Metric.isCompact_iff_isClosed_bounded)
--theorem farkas : _ := by sorry --uses lemma 1.2.2 and hyperplane_separation
--OR, use hyperplane separation theorem already in mathlib (we only need the statement of Farkas

--see NormedSpace.polar
--theorem 1.5.1
--proposition 1.5.2(b)

--theorem 1.6.1
