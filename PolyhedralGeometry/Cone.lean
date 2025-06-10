import PolyhedralGeometry.Defs
import Mathlib.Analysis.Convex.Cone.Basic

section Definitions
variable {V : Type*} [AddCommMonoid V] [Module ℝ V] (s : Set V)

def Cone : Prop :=
  s.Nonempty ∧ ∀ c ≥ (0 : ℝ), ∀ x ∈ s, c • x ∈ s

def PolyhedralCone.{u} : Prop :=
  IsPolyhedron.{_, u} s ∧ Cone s

def isConicalCombo' (x : V) {ι : Type*} (t : Finset ι) (a : ι → ℝ) (v : ι → V) : Prop :=
  (∀ i ∈ t, a i = 0 ∨ 0 ≤ a i ∧ v i ∈ s) ∧ x = ∑ i ∈ t, a i • v i

def isConicalCombo (x : V) : Prop :=
  ∃ (ι : Type*) (t : Finset ι) (a : ι → ℝ) (v : ι → V), isConicalCombo' s x t a v

def isConicalCombo_aux' (x : V) (n : ℕ) (a : ℕ → ℝ) (v : ℕ → V) : Prop :=
  (∀ i < n, a i = 0 ∨ 0 ≤ a i ∧ v i ∈ s) ∧ x = ∑ i ∈ Finset.range n, a i • v i

def isConicalCombo_aux (x : V) (n : ℕ) : Prop :=
  ∃ (a : ℕ → ℝ) (v : ℕ → V), isConicalCombo_aux' s x n a v

def conicalHull.{u} : Set V :=
  { x | isConicalCombo.{_, u} s x }

end Definitions

section Lemmas
variable {V W : Type*} [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W] (s : Set V) (f : V →ₗ[ℝ] W)

theorem zero_mem_of_cone {s : Set V} (h_cone_s : Cone s) : 0 ∈ s :=
  have ⟨⟨x, h_xs⟩, h_smul_closed⟩ := h_cone_s
  zero_smul ℝ x ▸ h_smul_closed 0 (le_refl 0) x h_xs

lemma cone_conicalHull (s : Set V) : Cone (conicalHull s) := by
  constructor
  · use 0, ULift Empty, ∅, fun x => Empty.elim (ULift.down x), fun x => Empty.elim (ULift.down x)
    simp [isConicalCombo']
  · rintro c h_c _ ⟨ι, t, a, v, h_av, rfl⟩
    use ι, t, c • a, v
    constructor
    · intro i h_it
      rcases h_av i h_it with h | ⟨h₁, h₂⟩
      · left
        simp
        right
        exact h
      · right
        refine ⟨mul_nonneg h_c h₁, h₂⟩
    · rw [Finset.smul_sum]
      congr
      ext i
      rw [← smul_assoc]
      simp

lemma conicalHull_eq_zero_of_empty {s : Set V} (h_s : s = ∅) : conicalHull s = {0} := by
  rw [h_s]
  refine subset_antisymm ?_ (by simp; exact zero_mem_of_cone (cone_conicalHull _))
  intro x h_x
  simp
  rcases h_x with ⟨ι, t, a, v, h_av, rfl⟩
  apply Finset.sum_eq_zero
  intro i h_it
  rcases h_av i h_it with h | ⟨_, h⟩
  · simp [h]
  contradiction

lemma subset_conicalHull_of_set (s: Set V): s ⊆ conicalHull s := by
  intro y hy
  unfold conicalHull isConicalCombo isConicalCombo'
  use ULift ℕ , {1}, (λ x => 1), (λ x => y)
  simp; exact hy

lemma sum_bijon {α β γ : Type*} [AddCommMonoid γ] {t : Finset α} {s : Finset β} {T : α → β} (h_bij : Set.BijOn T t s) {f : α → γ} {g : β → γ} (h_fg : f = g ∘ T) : ∑ i ∈ t, f i = ∑ j ∈ s, g j := by
  rcases h_bij with ⟨h_mapsto, h_inj, h_surj⟩
  apply Finset.sum_bij
  · apply h_mapsto
  · apply h_inj
  · convert h_surj
    simp [Set.SurjOn]
    rfl
  · tauto

lemma reindex_conicalCombo' {s : Set V} {x : V} {ι : Type*} (t : Finset ι) (a : ι → ℝ) (v : ι → V) : isConicalCombo' s x t a v → isConicalCombo_aux s x t.card := by
  rintro ⟨h_av, h_x_combo⟩
  have := (Finset.equivFin t).symm
  set N := t.card
  by_cases hN : N = 0
  · rw [hN]
    use (λ n ↦ 0), (λ n ↦ 0), by simp
    rw [Finset.sum_range_zero, h_x_combo]
    have : t = ∅ := Finset.card_eq_zero.mp hN
    rw [this]
    simp
  replace hN : N > 0 := Nat.zero_lt_of_ne_zero hN
  set F : ℕ → ι := Subtype.val ∘ (Finset.equivFin t).symm ∘ λ n ↦ if hn : n < N then (⟨n, hn⟩ : Fin N) else (⟨0, hN⟩ : Fin N)
  have h_F : Set.BijOn F (Finset.range N) t := by
    repeat' constructor
    · simp [Set.MapsTo, F]
    · simp [Set.InjOn, F]
      intro n₁ hn₁ n₂ hn₂ h_eq
      rw [dif_pos hn₁, dif_pos hn₂] at h_eq
      have : Function.Injective (Subtype.val : { x // x ∈ t } → ι) := by simp
      replace h_eq := this h_eq
      have : Function.Injective t.equivFin.symm := t.equivFin.symm.injective
      have := this h_eq
      exact Fin.val_congr this
    · intro i h_it
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
  · intro i _
    dsimp [a', v']
    apply h_av
    apply h_F.1
    simpa
  · dsimp [a', v']
    rw [h_x_combo]
    symm
    apply sum_bijon
    · simp; convert h_F; simp [h_F]
    · ext; simp

lemma reindex_conicalCombo (s : Set V) (x : V) : isConicalCombo s x ↔ ∃ n, isConicalCombo_aux s x n := by
  constructor
  · rintro ⟨ι, t, a, v, h⟩
    use t.card
    exact reindex_conicalCombo' _ _ _ h
  · rintro ⟨n, a, v, h_av, h_x_combo⟩
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
  · have := Finset.card_erase_add_one (Finset.mem_range.mpr h_j.1)
    simp at this
    rw [this]
  · unfold isConicalCombo'
    constructor
    · intro i h_i
      rw [Finset.mem_erase, Finset.mem_range] at h_i
      exact h_av i h_i.2
    · have : a j • v j = 0 := by rw [h_j.2]; simp
      rw[Finset.sum_erase (Finset.range (n + 1)) this]

lemma isconicalCombo_aux_le (s : Set V) (x : V) : m ≤ n → isConicalCombo_aux s x m → isConicalCombo_aux s x n := by
  intro h_mn
  rintro ⟨a, v, h_av, h_x_combo⟩
  let a' : ℕ → ℝ := fun i => if h_im : i < m then a i else 0
  use a', v
  repeat' constructor
  · intro i h_in
    by_cases h_im : i < m
    · simp [a', if_pos h_im]
      exact h_av i h_im
    · simp [a', if_neg h_im]
  · have h₁ : Finset.range m ⊆ Finset.range n := by simp; linarith
    have h₂ : ∀ i ∈ Finset.range n, i ∉ Finset.range m → a' i • v i = 0 := by
      simp [a']
      intros
      linarith
    rw [← Finset.sum_subset h₁ h₂]
    simp [a']
    rw [Finset.sum_ite_of_true, h_x_combo]
    intro i hi
    rw [Finset.mem_range] at hi
    exact hi

theorem zero_mem_conicalHull (s : Set V) : 0 ∈ conicalHull s := by
  use ULift Empty, ∅, fun x => Empty.elim (ULift.down x), fun x => Empty.elim (ULift.down x)
  simp [isConicalCombo']

open Finset

theorem conicalHull_image (s : Set V) : f '' (conicalHull.{_,u} s) = conicalHull.{_,u} (f '' s) := by
  apply subset_antisymm <;> rintro y h_y
  · rcases h_y with ⟨x, ⟨ι, t, a, v, h_av, h_combo⟩, rfl⟩
    use ι, t, a, f ∘ v
    constructor
    · intro i h_it
      rcases h_av i h_it with h | ⟨h₁, h₂⟩
      · exact Or.inl h
      · exact Or.inr ⟨h₁, v i, h₂, rfl⟩
    · rw [h_combo]
      simp
  · rcases h_y with ⟨ι, t, a, w, h_av, rfl⟩
    let t' := filter (fun i ↦ a i ≠ 0) t
    classical
    have h_key : ∀ i ∈ t', 0 ≤ a i ∧ w i ∈ f '' s := fun i h_it' ↦
      h_av i (mem_of_mem_filter i h_it') |>.resolve_left <| by simp [t'] at h_it'; exact h_it'.2
    let v : ι → V := fun i ↦ if h : i ∈ t' then (h_key i h).2.choose else 0
    have : ∀ i ∈ t', f (v i) = w i := fun i h ↦ by
      simp [v, h]
      exact Exists.choose_spec (h_key i h).2 |>.2
    have : ∀ i ∈ t, a i • f (v i) = a i • w i := by
      intro i h_it
      by_cases h_it' : i ∈ t'
      · simp [this i h_it']
      simp [t'] at h_it'
      simp [h_it' h_it]
    use ∑ i ∈ t, a i • v i
    constructor; swap
    · simp [this]
      exact sum_congr rfl this
    use ι, t', a, v
    constructor
    · intro i h_it'
      right
      constructor
      · exact (h_key i h_it').1
      simp [v, h_it']
      exact Exists.choose_spec (h_key i h_it').2 |>.1
    symm
    apply sum_subset (Finset.filter_subset _ _)
    intro i h_it h_it'
    simp at h_it'
    simp [h_it' h_it]

theorem conicalHull_preimage_subset_preimage_conicalHull (s : Set W) : conicalHull.{_,u} (f ⁻¹' s) ⊆ f ⁻¹' (conicalHull.{_,u} s) := by
  rintro x ⟨ι, t, a, v, h₁, h₂⟩
  use ι, t, a, f ∘ v
  constructor
  · exact h₁
  rw [h₂]
  simp only [map_sum, map_smul, Function.comp_apply]
  
--might be useful:
example (s : Set V) : PolyhedralCone s → ∃ s' : ConvexCone ℝ V, s'.carrier = s := sorry
example (s : Set V) : ∃ s' : ConvexCone ℝ V, s'.carrier = conicalHull s := by sorry

end Lemmas
