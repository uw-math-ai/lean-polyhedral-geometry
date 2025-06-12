import PolyhedralGeometry.Cone
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

--lemma 1.2.2
lemma translate_halfspace_of_cone_subset (s : Set V) (f : V →ₗ[ℝ] ℝ) (c : ℝ) (h_s_cone : Cone s)
    (h : ∀ x ∈ s, f x ≤ c) : c ≥ 0 ∧ ∀ x ∈ s, f x ≤ 0 := by
  constructor
  · contrapose! h
    exact ⟨0, zero_mem_of_cone h_s_cone, LinearMap.map_zero f ▸ h⟩
  intro x₀ x_in_s
  rw [← not_lt]
  intro h_0_le_fx
  have h_0_le_inv_fx : 0 < (f x₀)⁻¹ := inv_pos_of_pos h_0_le_fx
  have lt_c : f x₀ ≤ c := h x₀ x_in_s
  have ge_0_c : 0 < c := lt_of_lt_of_le h_0_le_fx lt_c
  have gq_2c_fxinv : 0 < 2 * c * (f x₀)⁻¹ := by
    apply mul_pos
    norm_num
    apply ge_0_c
    norm_num
    apply h_0_le_fx
  have : (2 * c * (f x₀)⁻¹) • x₀ ∈ s := h_s_cone.right (2 * c * (f x₀)⁻¹) (by linarith) x₀ x_in_s
  have le_c : f ((2 * c * (f x₀)⁻¹) • x₀) ≤ c := h ((2 * c * (f x₀)⁻¹) • x₀) this
  have : f x₀ ≠ 0 := Ne.symm (ne_of_lt h_0_le_fx)
  rw [LinearMap.map_smul] at le_c
  dsimp at le_c
  simp [this] at le_c
  linarith

open Bornology RealInnerProductSpace Metric
variable [FiniteDimensional ℝ V]

lemma exists_dist_min_points_of_closed_of_bounded ⦃A : Set V⦄ (h_nonempty_A : A.Nonempty)
    (h_isClosed_A : IsClosed A) (h_isBounded_A : IsBounded A) ⦃B : Set V⦄
    (h_nonempty_B : B.Nonempty) (h_isClosed_B : IsClosed B) :
    ∃ a₀ ∈ A, ∃ b₀ ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a₀ b₀ ≤ dist a b := by
  rcases h_nonempty_A with ⟨a, h_aA⟩
  rcases h_nonempty_B with ⟨b, h_bB⟩
  let K (r : ℝ) : Set V := { x : V | infDist x A ≤ r}
  have BcapK : ∃ r ≥ 0, ((K r) ∩ B).Nonempty :=
    ⟨dist b a, dist_nonneg, b, infDist_le_dist_of_mem h_aA, h_bB⟩
  have h_continuous : Continuous (fun x ↦ infDist x A) := continuous_infDist_pt A
  have Kclosed (r: ℝ) (hr : r ≥ 0) : IsClosed (K r) := IsClosed.preimage h_continuous isClosed_Iic
  have Kbounded (r: ℝ) (hr: r ≥ 0) : IsBounded (K r) := by
    rw [isBounded_iff_subset_ball a]
    use (diam A + r + 1)
    simp[K, ball]
    intro b hba'
    rcases IsClosed.exists_infDist_eq_dist h_isClosed_A ⟨a, h_aA⟩ b with ⟨a', ha', hdist⟩
    rw [hdist] at hba'
    calc
      dist b a
        ≤ dist b a' + dist a' a := by apply dist_triangle
      _ ≤ r + dist a' a:= by simp [hba']
      _ ≤ r + diam A:= by linarith [dist_le_diam_of_mem h_isBounded_A ha' h_aA]
    linarith
  have Kcompact (r : ℝ) (hr : r ≥ 0) : IsCompact (K r) := by
    rw [isCompact_iff_isClosed_bounded]
    exact ⟨Kclosed r hr, Kbounded r hr⟩
  have Knempty (r : ℝ) (hr : r ≥ 0) : (K r).Nonempty := by
    use a
    dsimp [K]
    rw[infDist_zero_of_mem]
    exact hr
    exact h_aA
  have closedInter (r: ℝ) {hr: r ≥ 0} : IsClosed ((K r) ∩ B) := by
    exact IsClosed.inter (Kclosed r hr) h_isClosed_B
  rcases BcapK with ⟨r₀, h_r₀_ge_0, h_inter_nonempty⟩
  let distBtoA := Set.image (fun b => infDist b A) ((K r₀) ∩ B)
  --maybe this instead
  --let distBtoA := (fun b => infDist b A)'' B
  --show that (K r) ∩ B is bounded, therefore compact
  have h_compact : IsCompact (K r₀ ∩ B) := by
    rw[isCompact_iff_isClosed_bounded]
    simp[IsClosed.inter (Kclosed r₀ h_r₀_ge_0) h_isClosed_B]
    have h: (K r₀ ∩ B) ⊆ K r₀ := by exact Set.inter_subset_left
    exact IsBounded.subset (Kbounded r₀ h_r₀_ge_0) h
  have := IsCompact.exists_isMinOn h_compact h_inter_nonempty (Continuous.continuousOn h_continuous)
  rcases this with ⟨b', hb'⟩
  have min_a : ∃ a, a ∈ A ∧ infDist b' A  = dist b' a := by
    apply IsClosed.exists_infDist_eq_dist h_isClosed_A ⟨a, h_aA⟩ b'
  rcases min_a with ⟨a', ha'⟩
  clear! a b
  use a', ha'.1, b', hb'.1.2
  intro a h_aA b h_bB
  by_cases h_bK : b ∈ K r₀
  · rw [dist_comm, ← ha'.2, dist_comm]
    have min_infDist := isMinOn_iff.mp hb'.2 b ⟨h_bK, h_bB⟩
    suffices h : infDist b A ≤ dist b a by linarith
    exact infDist_le_dist_of_mem h_aA
  calc
    dist a' b'
      ≤ r₀                 := by rw [dist_comm, ← ha'.2]; exact hb'.1.1
    _ ≤ infDist b A := le_of_not_ge h_bK
    _ ≤ dist a b           := dist_comm a b ▸ infDist_le_dist_of_mem h_aA

theorem hyperplane_separation  (A B : Set V) (hA : Convex ℝ A) (hB : Convex ℝ B) (hclosed : IsClosed A ∧ IsClosed B ) (hNempty : A.Nonempty ∧ B.Nonempty) (hA_Bounded: IsBounded A) (hAB : Disjoint A B) : ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), (∀ a ∈ A, f a < c) ∧ (∀ b ∈ B, c < f b) := by
  rcases exists_dist_min_points_of_closed_of_bounded hNempty.1 hclosed.1 hA_Bounded
    hNempty.2 hclosed.2 with ⟨a', h_a'A, b', h_b'B, h_a'b'_min_dist⟩
  let f : V → ℝ := fun x => ⟪b' - a', x⟫
  have a_not_b : b' ≠ a' := by
    rintro rfl
    absurd hAB
    rw [Set.not_disjoint_iff]
    exact ⟨b', h_a'A, h_b'B⟩
  have h_prods_ineq: f a' < f b' := by
    have : 0 < f b' - f a' := by
      calc
        0 < ‖b'-a'‖^2 := by rw [sq_pos_iff, norm_ne_zero_iff]; exact sub_ne_zero_of_ne a_not_b
        _ = ⟪b', b'⟫ - 2*⟪b', a'⟫ + ⟪a', a'⟫ := by
          simp [norm_sub_sq_real, real_inner_self_eq_norm_sq]
        _ = ⟪b', b'⟫ - ⟪b', a'⟫ - (⟪b', a'⟫ - ⟪a', a'⟫) := by linarith
        _ = ⟪b', b'⟫ - ⟪b', a'⟫ - ⟪b'-a', a'⟫ := by rw [← inner_sub_left]
        _ = ⟪b', b'⟫ - ⟪a', b'⟫ - ⟪b'-a', a'⟫ := by simp[real_inner_comm]
        _ = ⟪b'-a', b'⟫ - ⟪b'-a', a'⟫ := by rw [← inner_sub_left]
        _ = f b' - f a' := by simp[f]
    linarith
  -- use this to simplify minf and minf'
  -- maybe move this to a separate lemma eventually? probably just requires convexity of A and B
  have foo {a₀ b₀ b : V} (h_a₀ : a₀ ∈ A) (h_b₀ : b₀ ∈ B)
      (h_infDist : ∀ a ∈ A, ∀ b ∈ B, dist a₀ b₀ ≤ dist a b) (h_b : b ∈ B) :
      ⟪b₀ - a₀, b₀⟫ ≤ ⟪b₀ - a₀, b⟫ := by
    sorry
  have minf : ∀ b₀ ∈ B, f b₀ ≥ f b' := by
    intro b₀ hb₀
    have lin_dep (γ : ℝ) : (0 ≤ γ) ∧ (γ ≤ 1) → γ • b' + (1-γ) • b₀ ∈ B :=
      fun ⟨h, _⟩ => hB h_b'B hb₀ h (by linarith) (by simp)
    have equality_inner_prods (γ : ℝ) (hγ: γ ≥ 0) (hγ': γ ≤ 1): ‖γ•b' + (1-γ)•b₀-a'‖^2 = ‖b'-a'‖^2 + (1-γ)^2*‖b₀-b'‖^2 + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫ := by
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
      rw[← dist_eq_norm, ← dist_eq_norm, dist_comm, dist_comm _ a']
      apply h_a'b'_min_dist _ h_a'A _ (lin_dep γ ⟨hγ, hγ'⟩)

    have combo_inequalities (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1) : 0 ≤ (1-γ)^2*‖b₀-b'‖^2 + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫ := by
      --have intermediate: ‖‖ ≤ ‖b'-a'‖^2 + (1-γ)^2*‖b₀-b'‖^2 + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫
      have dummy: ‖b'-a'‖^2  ≤ ‖b'-a'‖^2 + (1-γ)^2 * ‖b₀-b'‖^2  + 2*(1-γ) * ⟪b'-a', b₀ - b'⟫:= by
        rw[← equality_inner_prods]
        rw[sq_le_sq]; repeat rw[abs_norm]
        apply ineq2; exact hγ; exact hγ'; exact hγ; exact hγ'
      linarith

    by_cases h : ⟪b'-a', b₀ - b'⟫ = 0
    · suffices h' : f b₀ = f b' by linarith
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
             _ = (1-γ)*(1-γ)*‖b₀-b'‖^2 + (1-γ) * 2 * ⟪b'-a', b₀ - b'⟫ := by simp [sq, mul_comm]
             _ = (1-γ)*((1-γ)*‖b₀-b'‖^2) + (1-γ) * (2 * ⟪b'-a', b₀ - b'⟫) := by repeat rw [mul_assoc]
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

    have ineq1 (γ : ℝ) (hγ : γ ≥ 0) (hγ' : γ ≤ 1) : 0 ≤ ‖b'-a'‖^2 + (1-γ)^2 * ‖a₀-a'‖^2 + 2*(1-γ) * ⟪a'-b', a₀ - a'⟫ := by
      rw[← equality_inner_prods]; simp[norm_nonneg]; exact hγ; exact hγ'

    have ineq2 (γ : ℝ)(hγ: γ ≥ 0) (hγ': γ ≤ 1):  ‖b' - a'‖ ≤ ‖(γ • a' + (1-γ) • a₀) - b'‖ := by
      repeat rw[← dist_eq_norm]
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
    · suffices h' : f a₀ = f a' by linarith
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
  have f_eq : f_lin = f := rfl
  use f_lin, fc
  rw [f_eq]
  exact ⟨gt_a, lt_b⟩

lemma farkas (u: V)(C: Set V) (convC : Convex ℝ C) (closedC : IsClosed C) (coneC : Cone C): u ∉ C → ∃ (y : V →ₗ[ℝ] ℝ), (y u > 0) ∧ (∀ x ∈ C, y x ≤ 0) := by
  intro hu
  have cu_Nempty : (Set.singleton u).Nonempty ∧ C.Nonempty := by
    unfold Cone at coneC
    exact ⟨Set.singleton_nonempty u, coneC.1⟩
  have andCU : IsClosed (Set.singleton u) ∧ IsClosed C := by
    exact ⟨isClosed_singleton, closedC⟩
  have convex_u: Convex ℝ {u} := convex_singleton u
  have disjoint_cu: Disjoint {u} C := by
    rw[Set.disjoint_singleton_left]; exact hu
  have boundedU : IsBounded {u} := by exact Bornology.isBounded_singleton
  rcases hyperplane_separation {u} C convex_u convC andCU cu_Nempty boundedU disjoint_cu with ⟨f, c, hfc⟩
  let g : V →ₗ[ℝ] ℝ := -f
  let c' :ℝ := -c
  have le_hyp: c' ≥ 0 ∧ ∀ x ∈ C, g x ≤ 0 := by
    apply (translate_halfspace_of_cone_subset C g c')
    exact coneC; unfold g c'; simp
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
