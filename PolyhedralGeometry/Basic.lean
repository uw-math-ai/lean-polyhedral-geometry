import PolyhedralGeometry.Cone
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

section
variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

lemma halfspace_convex (s : Set V) (h_halfspace_s : Halfspace s) : Convex ℝ s := by
  intro x _ y _ a b _ _ h_a_b_one
  rcases h_halfspace_s with ⟨f, ⟨c, rfl⟩⟩
  simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul]
  calc
    a * f x + b * f y
      ≤ a * c + b * c := by apply add_le_add <;> apply mul_le_mul_of_nonneg_left <;> assumption
    _ = (a + b) * c := by rw [add_mul]
    _ = 1 * c := by rw [h_a_b_one]
    _ = c := one_mul c

theorem poly_convex (s : Set V) (h_poly_s : IsPolyhedron s) : Convex ℝ s := by
  rcases h_poly_s with ⟨_, _, _, h_halfspace, rfl⟩
  exact convex_iInter fun i => halfspace_convex _ (h_halfspace i)

-- theorem min_elt (s : Set ℕ) (h_s_nonempty : s.Nonempty) : ∃ n ∈ s, ∀ m < n, m ∉ s := by
--   rcases h_s_nonempty with ⟨n, h⟩
--   induction' n using Nat.strong_induction_on with n ih
--   by_cases h' : ∀ m < n, m ∉ s
--   · use n
--   · push_neg at h'
--     rcases h' with ⟨n', h₁, h₂⟩
--     exact ih n' h₁ h₂

-- use Finset.sum_subset!
-- lemma Finset.sum_enlarge {ι α : Type*} [AddCommMonoid α] {t s : Finset ι} {f : ι → α} (h_ts : t ⊆ s) (h_f : ∀ i ∉ t, f i = 0) : ∑ i ∈ t, f i = ∑ i ∈ s, f i := by
--   classical
--   induction' s using Finset.strongInductionOn with s ih
--   by_cases h : t = s
--   · rw [h]
--   have : t ⊂ s := ssubset_of_subset_of_ne h_ts h
--   rcases (Finset.ssubset_iff_of_subset h_ts).mp this with ⟨x, h_xs, h_xt⟩
--   let s' := s.erase x
--   have h_ts' : t ⊆ s' := by
--     refine Finset.subset_erase.mpr ?_
--     constructor <;> assumption
--   rw [ih s' (Finset.erase_ssubset h_xs) h_ts']
--   apply Finset.sum_erase
--   exact h_f x h_xt

end

section
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
open Finset Module

theorem caratheordory (s : Set V) : ∀ x ∈ conicalHull.{_,0} s, isConicalCombo_aux s x (finrank ℝ V) := by
  rintro x h
  rcases (reindex_conicalCombo s x).mp h with ⟨n, h⟩
  induction' n with N ih
  · exact isconicalCombo_aux_le s x (Nat.zero_le _) h
  by_cases hN : N + 1 ≤ finrank ℝ V
  · exact isconicalCombo_aux_le s x hN h
  push_neg at hN
  rcases h with ⟨a, v, h_av, h_x_combo⟩
  apply ih

  wlog h_a_all_pos : ∀ i < N + 1, a i ≠ 0 generalizing
  · push_neg at h_a_all_pos
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
  · apply this (range (N + 1))
    all_goals clear this h'; try simp
    · intro i hiN
      have : i ∉ t := by
        intro h_it
        have := h_t_sub_range h_it
        have := mem_range.mp this
        linarith
      exact h_b_comp i this
    · rw [← h_b_combo_eq_0]
      symm
      apply sum_subset
      · assumption
      · intro i _ h_it
        rw [h_b_comp i h_it]
        simp
    · have := h_t_sub_range h_jt
      apply mem_range.mp
      exact this
  rw [h'] at h_b_combo_eq_0 h_jt
  clear h_t_sub_range h_b_comp h' t
  wlog h_b_j_pos : b j > 0 generalizing b
  · let b' := -b
    apply this b' <;> simp [b']
    · assumption
    · simp [h_b_combo_eq_0]
    · simp at h_b_j_pos
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
    rw [← mem_range]
    exact (mem_filter.mp i₀_in_range).1
  apply reduce_conicalCombo s x v ⟨i₀, this, h_i₀_ai_βbi_zero⟩
  refine ⟨?_, x_plus_zero⟩
  intro i h_i
  right
  constructor
  · exact h_all_ai_βbi_nonneg i h_i
  · rcases h_av i h_i with h | h
    · absurd h
      exact h_a_all_pos i h_i
    · exact h.2

end

section
variable {ι : Type u}

lemma nonneg_orthant_closed : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i } :=
  (Set.setOf_forall fun i (x : ι → ℝ) => 0 ≤ x i) ▸
  isClosed_iInter fun i => IsClosed.preimage (continuous_apply i) isClosed_Ici

variable [Finite ι] [DecidableEq ι]

abbrev std_basis : ι → (ι → ℝ) := fun i j => if i = j then 1 else 0

lemma nonneg_orthant_gens : {x : ι → ℝ | ∀ i, 0 ≤ x i } = conicalHull.{_, u} (Set.range std_basis) := by
  ext x; constructor <;> intro h
  haveI := Fintype.ofFinite ι
  · use ι, Finset.univ, x, std_basis
    constructor
    · intro i h'
      right
      constructor
      · exact h i
      · use i
    · exact pi_eq_sum_univ x
  · rcases h with ⟨α, t, a, v, h₁, rfl⟩
    intro i
    simp
    apply Finset.sum_nonneg
    intro x h_xt
    rcases h₁ x h_xt with h | h
    · simp [h]
    · apply mul_nonneg
      · exact h.left
      · rcases h.right with ⟨j, h⟩
        rw [← h]
        unfold std_basis
        apply ite_nonneg <;> norm_num

end

section
variable {V : Type*} [DecidableEq V] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
open Set Module

private abbrev d_subsets (s : Set V) := {t : Finset V | ↑t ⊆ s ∧ t.card = finrank ℝ V}

lemma d_subsets_finite (s : Set V) : s.Finite → (d_subsets s).Finite := by
  sorry

lemma conical_hull_union_conical_hull_d_subsets (s : Set V) : conicalHull s = ⋃ t ∈ d_subsets s, conicalHull t.toSet := by
  --use caratheordory to get a finset t of s of card n+1
  sorry

--worth including this in Mathlib.Data.Finsupp.Single?
theorem Finsupp.single_map [Zero M] {a : α} {b : M} [DecidableEq α] : Finsupp.single a b = fun a' => if a = a' then b else 0 := by
  ext a'
  exact single_apply

--proposition 1.3.3(b)
theorem conical_hull_closed_of_finite (s : Set V) : s.Finite → IsClosed (conicalHull s) := by
  generalize h_dim : finrank ℝ V = n
  revert V
  induction' n using Nat.strong_induction_on with n ih
  intro V _ _ _ _ s h_dim h_s
  by_cases h_n : n = 0
  · rw [h_n] at h_dim
    rw [finrank_zero_iff] at h_dim
    have : s = ∅ ∨ ∃ (x : V), s = {x} := Subsingleton.eq_empty_or_singleton subsingleton_of_subsingleton
    rcases this with h | h <;> exact isClosed_discrete (conicalHull s)
  replace h_n : n > 0 := Nat.zero_lt_of_ne_zero h_n
  rw [conical_hull_union_conical_hull_d_subsets s]
  apply Finite.isClosed_biUnion (d_subsets_finite s h_s)
  intro t ⟨h_ts, h_tcard⟩
  clear h_ts h_s s
  let t' : {x // x ∈ t} → V := Subtype.val
  haveI : Nonempty {x // x ∈ t} := by
    simp only [nonempty_subtype]
    have : Set.Nonempty t.toSet := by
      apply nonempty_of_ncard_ne_zero
      rw [ncard_coe_Finset, h_tcard, h_dim]
      exact Nat.ne_zero_of_lt h_n
    exact this
  by_cases h_t_lin_ind : LinearIndependent ℝ t'
  · let B : Basis { x // x ∈ t } ℝ V := (basisOfLinearIndependentOfCardEqFinrank h_t_lin_ind (h_tcard ▸ Fintype.card_coe t))
    let φ : V ≃ₗ[ℝ] { x // x ∈ t } → ℝ := B.equivFun
    have h_φ (x : V) (hxt : x ∈ t) : φ x = std_basis ⟨x, hxt⟩ := by
      unfold φ
      have : x = B ⟨x, hxt⟩ := by
        simp only [coe_basisOfLinearIndependentOfCardEqFinrank, B, t']
      nth_rewrite 1 [this]
      simp only [Basis.equivFun_apply, Basis.repr_self]
      exact Finsupp.single_map
    have h_φ_symm : φ.symm ∘ std_basis = Subtype.val := by
      ext ⟨x, h_xt⟩
      exact (LinearEquiv.symm_apply_eq φ).mpr (h_φ x h_xt).symm
    have h_φ_symm_image : φ.symm '' (range std_basis) = t := by
      rw [← image_univ, ← image_comp, h_φ_symm]
      simp
    have h_cont_φ : Continuous φ := continuous_equivFun_basis B
    have := nonneg_orthant_closed (ι := { x // x ∈ t })
    rw [nonneg_orthant_gens] at this
    convert IsClosed.preimage h_cont_φ this
    have := conicalHull_image φ.symm.toLinearMap (range std_basis (ι := { x // x ∈ t }))
    rw [← LinearEquiv.image_symm_eq_preimage]
    show conicalHull t = ↑φ.symm '' conicalHull (range std_basis)
    rw [LinearEquiv.coe_coe] at this
    rw [this, h_φ_symm_image]
  · have h_eq_t : range t' = t := Subtype.range_val
    rw [← h_eq_t]
    let V' := Submodule.span ℝ (range t')
    rw [linearIndependent_iff_card_eq_finrank_span.not, Fintype.card_coe, h_tcard] at h_t_lin_ind
    push_neg at h_t_lin_ind
    replace h_t_lin_ind : Set.finrank ℝ (range t') < finrank ℝ V := lt_of_le_of_ne (Submodule.finrank_le _) h_t_lin_ind.symm
    have : V' < ⊤ := Submodule.lt_top_of_finrank_lt_finrank h_t_lin_ind
    replace h_t_lin_ind : finrank ℝ V' < n := h_dim ▸ h_t_lin_ind
    let t'' : { x // x ∈ t } → V' := fun x => ⟨t' x, Submodule.subset_span (mem_range_self x)⟩
    --have := ih (finrank ℝ V') h_t_lin_ind (range t'') rfl
    sorry

-- theorem linearIndepOn_iff_card_eq_finrank_span (s : Finset V) :
--     LinearIndepOn ℝ id s.toSet ↔ s.card = finrank ℝ (Submodule.span ℝ s.toSet) := by
--   rw [linearIndepOn_id_range_iff]


example (f : ι → V) [Fintype ι] : finrank ℝ (Submodule.span ℝ (range f)) ≤ Fintype.card ι := finrank_range_le_card f

-- #check finrank_span_le_card
-- #check span_lt_top_of_card_lt_finrank
-- #check Submodule.lt_top_of_finrank_lt_finrank
-- #check Submodule.finrank_le

example (f : ι → V) [Fintype ι] : LinearIndependent ℝ f ↔ Fintype.card ι = finrank ℝ (Submodule.span ℝ (range f)) := linearIndependent_iff_card_eq_finrank_span

example (f : ι → V) [Fintype ι] : Submodule.span ℝ (range f) = ⊤ ↔ finrank ℝ (Submodule.span ℝ (range f)) = finrank ℝ V :=
  Iff.intro
    (fun h => h ▸ finrank_top ℝ V)
    (fun h => Submodule.eq_top_of_finrank_eq h)

end

-- section
-- variable {V : Type*} [NormedAddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

--proposition 1.3.3(b)
-- theorem conical_hull_closed_of_finite' (s : Set V) : s.Finite → IsClosed (conicalHull s) := by
--  generalize h_dim : finrank ℝ V = n
--  revert V
--  induction' n with n ih <;> intro V _ _ _ s h_dim h_s
--  · rw [finrank_zero_iff] at h_dim
--    have : s = ∅ ∨ ∃ (x : V), s = {x} := Subsingleton.eq_empty_or_singleton subsingleton_of_subsingleton
--    rcases this with h | h <;> exact isClosed_discrete (conicalHull s)
--  · by_cases hs : s.Nonempty
--    · rcases hs with ⟨x, hx⟩
--      rcases caratheordory s x with h
--      have hCon: x ∈  conicalHull s := by
--        apply subset_conicalHull_of_set s at hx; exact hx
--      have ofRank: isConicalCombo_aux s x (finrank ℝ V) := by
--        exact (h hCon)
--      unfold isConicalCombo_aux isConicalCombo_aux' at ofRank
--      rcases ofRank with ⟨ a, v, hv, h_basis⟩
--      let N_Fin : Finset ℕ := Finset.range (finrank ℝ V)
--      --let v_fin := v.restrict N_Fin
--      --let a_fin := a.restrict N_Fin
--      by_cases lin_ind: LinearIndependent ℝ v
--      · have form_Basis: Basis ℕ ℝ V := by
--          sorry
        --#check basisOfLinearIndependentOfCardEqFinrank lin_ind
        --#check LinearIndependent
        --#check FiniteDimensional
--        sorry
--      · sorry
--    · push_neg at hs
--      have h_empty : conicalHull s = {0} := by
--        rw[hs]
--        simp only [conicalHull, mem_setOf_eq]
--        unfold isConicalCombo isConicalCombo'
--        simp only [mem_empty_iff_false, and_false, or_false]
--        ext x; simp[Set.mem_setOf]
--        constructor
--        · rintro ⟨ι, t, a, ha, v, pv⟩
--          sorry
          --simp only [ha, zero_smul, Finset.sum_const_zero]
--        · intro hx
--          sorry
--      rw[h_empty]
--      simp
--  sorry

    --have inst: s.Nonempty := by
    --rcases caratheordory s
    --use caratheordory to get a finset t of s of card n+1
    --proof by cases : t linearly independent or not
    --if not, induct
    --else:
    --use basisOfLinearIndependentOfCardEqFinrank
    --unpack the Basis to get the linear equiv to ℝ^n that we want
    --use nonneg_orthant_gens and nonneg_orthant_closed
    
  --use nonneg_orthant_gens and nonneg_orthant_closed

--========================================================--
--========================= todo =========================--
--========================================================--

--theorem farkas : _ := by sorry --uses lemma 1.2.2 and hyperplane_separation
--OR, use hyperplane separation theorem already in mathlib (we only need the statement of Farkas

--see NormedSpace.polar
--theorem 1.5.1
--proposition 1.5.2(b)

--theorem 1.6.1
