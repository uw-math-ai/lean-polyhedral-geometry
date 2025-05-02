import PolyhedralGeometry.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
--import Mathlib.Topology.MetricSpace.Defs
--import Mathlib.LinearAlgebra.Dual
--import Mathlib.Topology.Defs.Basic

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
    · use a, v
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
  wlog b_j_pos : b j > 0 generalizing b
  . let b' := -b
    apply this b' <;> simp [b']
    . assumption
    . simp [h_b_combo_eq_0]
    . simp at b_j_pos
      exact lt_of_le_of_ne b_j_pos h_j_ne_0
  clear h_j_ne_0
  let ratios : Finset ℝ := (Finset.range (N + 1)).image (λ i => a i / b i)
  let ratios_non_neg : Finset ℝ := ratios.filter (λ r => r ≥ 0)
  have : ratios_non_neg.Nonempty := by
    unfold ratios_non_neg
    unfold ratios
    have a_j : a j ≥ 0 := by
      #check h_av j
      sorry
    sorry
  have β : ℝ := Finset.min' ratios sorry
  replace h_b_combo_eq_0 : ∑ i ∈ range (N + 1),  (β * b i) • v i = 0 := by
    sorry
  rw [← sub_zero (∑ i ∈ range (N + 1), a i • v i)] at h_x_combo
  rw [← h_b_combo_eq_0] at h_x_combo
  have x_plus_zero : x = ∑ i ∈ range (N + 1), ((a i - β * b i) • v i) := by
    simp [sub_smul, Finset.sum_sub_distrib]
    exact h_x_combo
  sorry

end

namespace Testing
variable {ι : Type*}

lemma nonneg_orthant_closed : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i } := by
  rw [Set.setOf_forall fun i (x : ι → ℝ) => 0 ≤ x i]
  apply isClosed_iInter
  intro i
  apply IsClosed.preimage (continuous_apply i) isClosed_Ici

variable [Finite ι] [DecidableEq ι] --why isn't this automatic

def std_basis : ι → (ι → ℝ) := fun i j => if i = j then 1 else 0

lemma nonneg_orthant_gens : {x : ι → ℝ | ∀ i, 0 ≤ x i } = conicalHull'

end Testing

section
variable {V : Type*} [NormedAddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

--maybe easier to work with Cone(T) directly, rather than trying to work with ℝ^d

--proposition 1.3.3(b)
theorem conical_hull_closed_of_finite (s : Set V) : s.Finite → IsClosed (conicalHull' s) := by sorry

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

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
open Bornology RealInnerProductSpace

#check PseudoMetricSpace
-- A and B are the convex sets we want to separate.

open Bornology

-- The goal: Prove there exists a continuous linear functional `f` and a scalar `c`
-- such that `f` separates A and B (i.e., `f(a) ≤ c ≤ f(b)` for all `a ∈ A`, `b ∈ B`).

#print Set.Nonempty
#check Metric.infDist
#check dist_nonneg
#check Metric.continuous_infDist_pt
#check Convex
--theorem Metric.isCompact_iff_isClosed_bounded {α : Type u} [PseudoMetricSpace α] {s : Set α} [T2Space α] [ProperSpace α] :
--IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s

--gonna have to add Metric.hausdorffDist_nonneg for latest goal
--changed f : V → L[ℝ] ℝ to f: V → ℝ. Not sure whether we want to cover non-finite-dimensional cases?
theorem hyperplane_separation  (A B : Set V) (hA : Convex ℝ A)(hB : Convex ℝ B)  (hclosed: IsClosed A ∧ IsClosed B ) (hNempty : A.Nonempty ∧ B.Nonempty) (hA_Bounded: IsBounded A) (hAB : Disjoint A B) : ∃ (f : V → ℝ) (c : ℝ), (∀ a ∈ A, f a ≤ c) ∧ (∀ b ∈ B, c ≤ f b) := by
  rcases hNempty.left with ⟨a, h_aA⟩
  rcases hNempty.right with ⟨b, h_bB⟩
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
        apply IsClosed.exists_infDist_eq_dist hclosed.1 hNempty.1 b
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
    exact IsClosed.inter (Kclosed r hr) (hclosed.2)
  rcases BcapK with ⟨r₀, h_r₀_ge_0, h_inter_nonempty⟩
  let distBtoA := Set.image (fun b => Metric.infDist b A) ((K r₀) ∩ B)
  --maybe this instead
  --let distBtoA := (fun b => Metric.infDist b A)'' B
  --show that (K r) ∩ B is bounded, therefore compact
  have h_compact : IsCompact (K r₀ ∩ B) := by
    rw[Metric.isCompact_iff_isClosed_bounded]
    simp[IsClosed.inter (Kclosed r₀ h_r₀_ge_0) (hclosed.2)]
    have h: (K r₀ ∩ B) ⊆ K r₀ := by exact Set.inter_subset_left
    exact Bornology.IsBounded.subset (Kbounded r₀ h_r₀_ge_0) h
  have := IsCompact.exists_isMinOn h_compact h_inter_nonempty (Continuous.continuousOn h_continuous)
  rcases this with ⟨b', hb'⟩
  have min_a : ∃ a, a ∈ A ∧ Metric.infDist b' A  = dist b' a := by
    apply IsClosed.exists_infDist_eq_dist hclosed.1 hNempty.1 b'
  rcases min_a with ⟨a', ha'⟩
  let f: V → ℝ  := fun x => ⟪b'-a', x⟫
  have a_not_b: a' ≠ b' := by
    intro h
    have h1: b' ∈ B := by exact Set.mem_of_mem_inter_right hb'.1
    have h2: a' ∈ B := by
      rw [h]
      exact h1
    have h_inter: a' ∈ A ∩ B := by exact Set.mem_inter ha'.1 h2
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
        _ = (inner b' b') - 2*(inner b' a') + (inner a' a') := by
          simp [norm_sub_sq_real, real_inner_self_eq_norm_sq]
        _ = (inner b' b') - (inner b' a') - ((inner b' a') - (inner a' a')) := by linarith
        _ = (inner b' b') - (inner b' a') - inner (b'-a') a' := by rw [← inner_sub_left]
        _ = (inner b' b') - (inner a' b') - inner (b'-a') a' := by simp[real_inner_comm]
        _ = inner (b' - a') b'- inner (b'-a') a' := by rw [← inner_sub_left]
        _ = f b' - f a' := by simp[f]
    linarith
  have minf : ∀ b₀ ∈ B, f b' ≥ f b₀ := by
    intro b₀ hb₀
    have lin_dep (γ : ℝ) : (0 ≤ γ) ∧ (γ ≤ 1) → γ • b' + (1-γ) • b₀  ∈ B :=
      fun ⟨h, _⟩ => hB (Set.mem_of_mem_inter_right hb'.1) hb₀ h (by linarith) (by simp)
    have ineq (γ : ℝ) (hγ: γ ≥ 0) (hγ': γ ≤ 1): ‖b'-a'‖^2 + γ^2*‖b'-a'‖^2 + 2*γ * ⟪b'-a', b₀ - b'⟫ ≥ 0 := by
      calc
        0 ≤ ‖γ•b' + (1-γ)•b₀-a'‖^2  := by simp[norm_nonneg]
        _ = ‖γ•b' + b' - b' + (1-γ)•b₀-a'‖^2 := by simp
        _ = ‖b' - a' + γ•b' + (1-γ)•b₀ - b'‖^2 := by congr 2; module
        _ = ‖b'-a'‖^2 + γ^2*‖b'-a'‖^2 + 2*γ * ⟪b'-a', b₀ - b'⟫ := by sorry
    sorry
  sorry
  --#check IsCompact.exists_isMinOn

  --rcases this

 --WLOG, let A Construct a Set K_r compact around A, defined as all points within r of A, the compact
 --set within the relation. Let r such that K_r ∩ B ≠ ∅ ∧ K_r ∩ A = A

 --K_r ∩ B ∪ A is compact (show) implies existence of a∈ A, b∈ B ∩ K_r such that d(a,b) is minimal.

  -- f' is norm to hyperplane separating A,B. Use this to define hyperplane with f = ⟨f', _ ⟩
  -- hyperplane P = f x = c, x ∈ E. Choose c by middle line segment between a,b.

end

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
