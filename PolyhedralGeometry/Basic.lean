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
--use this instead!
#check convex_halfSpace_le

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

def conicalCombo_cards (s : Set V) (x : V) : Set ℕ := Finset.card '' { (t : Finset V) | ∃ (a : V → ℝ), (∀ v ∈ t, 0 ≤ a v) ∧ ↑t ⊆ s ∧ x = ∑ v in t, a v • v}

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

-- theorem 1.3.2(b)
theorem caratheordory (s : Set V) (x : V) (h : x ∈ conicalHull s) :
  ∃ (t : Finset V), ↑t ⊆ s ∧ t.card ≤ Module.finrank ℝ V ∧ x ∈ conicalHull t := by
  -- rcases h with ⟨u, a, h_a_nonneg, h_u_subset, h_x_combo⟩
  -- rcases le_or_gt u.card (Module.finrank ℝ V) with h_u_card | h_u_card
  -- . use u, h_u_subset, h_u_card, u, a
  -- induction' u using Finset.induction_on with v u h_v_nin_u ih
  -- . sorry
  -- . sorry
  rcases min_elt (conicalCombo_cards s x) (conicalCombo_cards_nonempty s x h) with ⟨n, h₁, h₂⟩
  rcases h₁ with ⟨t, ⟨a, h_a_nonneg, h_t_subset, h_x_combo⟩, rfl⟩
  rcases le_or_gt t.card (Module.finrank ℝ V) with h_t_card | h_t_card
  . use t, h_t_subset, h_t_card, t, a
  apply False.elim
  have h_not_lin_indep : ¬(LinearIndependent ℝ (fun x => x : ↑t → V)) := by
    intro h
    have h₁ := LinearIndependent.cardinal_le_rank h
    have := Cardinal.toNat_le_toNat h₁ (Module.rank_lt_aleph0 ℝ V)
    simp at this
    linarith!
  have := Fintype.not_linearIndependent_iff.mp h_not_lin_indep
  rcases this with ⟨b, h_combo, u, h_b_u_ne_0⟩
  let b' : V → ℝ := fun v =>
    if hvt : v ∈ t then b { val := v, property := hvt} else 0
  --have h_combo₁ : ∑ v ∈ t, b' v = 0 := sorry
  by_cases h' : b' u > 0
  #check { x // x ∈ t}
  . let ratio : V → ℝ := fun i => (b' i) / (a i)
    have : {x | x ∈ t}.Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero
      have : t.card > 0 := by linarith
      show (↑t : Set V).ncard ≠ 0
      rw [Set.ncard_coe_Finset]
      linarith
    have := Set.exists_max_image {x | x ∈ t} ratio (Set.finite_mem_finset t) this
    rcases this with ⟨u', h_u'_t, h_u'_max⟩
    dsimp at h_u'_t
    simp [ratio] at h_u'_max
    sorry
  . let b_neg : { x // x ∈ t } → ℝ := fun i => -(b i)
    sorry

#check not_linearIndependent_iff

variable {ι : Type*} [Finite ι] (B : Basis ι ℝ V)

--figure out how closure operators work (to define conicalHull like mathlib's convexHull)
