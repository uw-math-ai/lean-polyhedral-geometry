import PolyhedralGeometry.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
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

--todo: eliminate the need to have an explicit inner product on V; i.e., show that it doesn't depend on the choice of inner product, so the definition can be made without such a choice)

example (s : Set V) : PolyhedralCone s → ∃ s' : ConvexCone ℝ V, s'.carrier = s := sorry

--lemma 1.2.2
example (s : Set V) (f : V →ₗ[ℝ] ℝ) (c : ℝ) : Cone s → (∀ x ∈ s, f x ≤ c) → c ≥ 0 ∧ ∀ x ∈ s, f x ≤ 0 := by
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

open Classical

section

variable (α β : Type*) [AddCommMonoid β]


lemma reduce_by_one (t : Finset V) (a : V → ℝ) (x : V) (h₁ : ∀ v ∈ t, 0 ≤ a v)
  (h₂ : x = ∑ v in t, a v • v)
  (h₃ : t.card > Module.finrank ℝ V) :
  ∃ (t' : Finset V) (a' : V → ℝ), t'.card < t.card ∧ t' ⊆ t ∧ (∀ v ∈ t', 0 ≤ a' v) ∧ x = ∑ v ∈ t', a' v • v := by
  by_cases all_zero : ∀ v ∈ t, a v = 0
  -- Case 1: All Coefficients are 0
  · use ∅
    use a
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : t.card > 0 := by
        exact Nat.zero_lt_of_lt h₃
      have : (↑∅ : Finset V).card = 0 := by
        exact rfl
      linarith
    · exact Finset.empty_subset t
    · intro x x_in_empty
      apply False.elim
      exact (List.mem_nil_iff x).mp x_in_empty
    · have : x = 0 := by
        rw [h₂]
        apply Finset.sum_eq_zero
        intro v₀ v₀_in_t
        have : a v₀ = 0 := all_zero v₀ v₀_in_t
        exact smul_eq_zero_of_left (all_zero v₀ v₀_in_t) v₀
      simp; exact this

  -- Case 2: At Least One Coefficient is nonzero
  · push_neg at all_zero
    rcases all_zero with ⟨v₁,hv₁, h_a_v₁_nonzero⟩
    have h_a_v₁_pos : 0 < a v₁ := by
      exact lt_of_le_of_ne (h₁ v₁ hv₁) (id (Ne.symm h_a_v₁_nonzero))
    -- Since t.card > finrank ℝ V the set of vectors t is linearly dependent.
    have ld : ¬ (LinearIndependent ℝ (fun x => x : {x // x ∈ t} → V)):= by
        intro h
        have := LinearIndependent.cardinal_le_rank h
        have := Cardinal.toNat_le_toNat this (Module.rank_lt_aleph0 ℝ V)
        simp at this
        linarith!
    -- obtain ⟨c₀, hc₀_nonzero, hc₀_sum⟩ : ∃ c₀ : V → ℝ, (∃ v ∈ t, c₀ v ≠ 0) ∧ (∑ v in t, c₀ v • v = 0)
    -- ·
    sorry


-- theorem 1.3.2(b)
theorem caratheordory' (s : Set V) (x : V) (h : x ∈ conicalHull s) :
  ∃ (t : Finset V), ↑t ⊆ s ∧ t.card ≤ Module.finrank ℝ V ∧ x ∈ conicalHull t := by
  rcases min_elt (conicalCombo_cards s x) (conicalCombo_cards_nonempty s x h) with ⟨n, h', h_minimality⟩
  rcases h' with ⟨t, ⟨a, h_a_nonneg, h_t_subset, h_x_combo⟩, rfl⟩
  rcases le_or_gt t.card (Module.finrank ℝ V) with h_t_card | h_t_card
  . use t, h_t_subset, h_t_card, t, a
  apply False.elim
  have := reduce_by_one t a x h_a_nonneg h_x_combo h_t_card
  rcases this with ⟨t',a',t'_le_t,t'_sub_t,a'_nonneg,t'_x_conic_combo⟩
  have t'_subset_s : ↑t' ⊆ s := by
    have : (↑t' : Set V) ⊆ (t : Set V) := by
      exact t'_sub_t
    apply subset_trans this h_t_subset
  have t'_is_in_conicalCombos : t'.card ∈ conicalCombo_cards s x := by
    use t'
    use ⟨a',a'_nonneg,t'_subset_s,t'_x_conic_combo⟩
  have := h_minimality t'.card t'_le_t
  show False
  exact this t'_is_in_conicalCombos
variable {ι : Type*} [Finite ι] (B : Basis ι ℝ V)

--figure out how closure operators work (to define conicalHull like mathlib's convexHull)
