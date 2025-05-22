import PolyhedralGeometry.Defs
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
--import Mathlib.Topology.Bases
import Mathlib.Topology.Order.OrderClosed
--import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.Algebra.Module.ModuleTopology

section
open TopologicalSpace Set

theorem Real.isTopologicalBasis_Ioo : @IsTopologicalBasis ℝ _ (⋃ (a : ℝ) (b : ℝ) (_ : a < b), { Ioo a b }) :=
  isTopologicalBasis_of_isOpen_of_nhds (by simp +contextual [isOpen_Ioo])
  fun a s has hs =>
    let ⟨l, u, ⟨hl, hu⟩, h⟩ := mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hs has)
    ⟨Ioo l u, by
      simp only [mem_iUnion]
      exact ⟨⟨l, u, lt_trans hl hu, rfl⟩, ⟨hl, hu⟩, h⟩⟩
      
-- theorem Real.isTopologicalBasis_Ioo : @IsTopologicalBasis ℝ _ (⋃ (a : ℝ) (b : ℝ) (_ : a < b), {Ioo a b}) where
--   exists_subset_inter := by
--     intro s hs t ht x hx
--     simp at hs ht
--     rcases hs with ⟨a, b, h_ab, rfl⟩
--     rcases ht with ⟨a', b', h_a'b', rfl⟩
--     use Ioo (max a a') (min b b')
--     rcases hx with ⟨⟨h_ax, h_xb⟩, h_a'x, h_xb'⟩
--     refine ⟨?_, ?_, ?_⟩
--     . simp
--       use max a a', min b b'
--       constructor
--       . apply max_lt <;> apply lt_min <;> linarith
--       . rfl
--     . exact ⟨max_lt h_ax h_a'x, lt_min h_xb h_xb'⟩
--     . intro y hy
--       simp at hy
--       exact ⟨⟨hy.1.1, hy.2.1⟩, hy.1.2, hy.2.2⟩
--   sUnion_eq := by
--     apply subset_antisymm
--     . exact fun _ _ => trivial
--     intro x _
--     show x ∈ ⋃₀ ⋃ a, ⋃ b, ⋃ (_ : a < b), {Ioo a b}
--     use Ioo (x - 1) (x + 1)
--     simp
--     use x - 1, x + 1
--     simp
--     linarith        
--   eq_generateFrom := by
--     apply le_antisymm
--     . rw [le_generateFrom_iff_subset_isOpen]
--       intro s hs
--       simp at hs
--       rcases hs with ⟨a, b, hab, rfl⟩
--       simp
--       rw [isOpen_iff_generate_intervals]
--       set g := {s : Set ℝ | ∃ a, s = Ioi a ∨ s = Iio a}      
--       have hb : @IsOpen ℝ (generateFrom g) (Iio b) := isOpen_generateFrom_of_mem (by simp [g]; use b; tauto)
--       have ha : @IsOpen ℝ (generateFrom g) (Ioi a) := isOpen_generateFrom_of_mem (by simp [g]; use a; tauto)
--       convert GenerateOpen.inter _ _ hb ha
--       exact Eq.symm Iio_inter_Ioi
--     . rw [OrderTopology.topology_eq_generate_intervals (α := ℝ), le_generateFrom_iff_subset_isOpen]
--       rintro s ⟨a, h_or⟩
--       wlog h : s = Ioi a generalizing s a with h_symm
--       . let s' : Set ℝ := -s
--         have : s' = Ioi (-a) := by
--           have : s = Iio a := by
--             rcases h_or with h' | h'
--             . absurd h'; exact h
--             . exact h'
--           simp only [involutiveNeg, s', this]
--           exact neg_Iio a
--         have h_s' := h_symm (-a) (.inl this) this
--         letI _ : TopologicalSpace ℝ := generateFrom (⋃ a, ⋃ b, ⋃ (_ : a < b), {Ioo a b})
--         have h_cts_neg : Continuous (fun x : ℝ => -x) := by
--           apply continuous_generateFrom_iff.mpr
--           simp only [mem_iUnion, mem_singleton_iff, exists_prop, neg_preimage, forall_exists_index, and_imp, s']
--           rintro _ a b h_ab rfl
--           rw [neg_Ioo a b]
--           apply isOpen_generateFrom_of_mem
--           simp only [mem_iUnion, mem_singleton_iff, exists_prop]
--           use -b, -a, (by linarith)
--         have := IsOpen.preimage h_cts_neg (mem_setOf_eq ▸ h_s')
--         simp [s'] at this
--         exact this
--       have : Ioi a = ⋃₀ {Ioo a (a + i) | i > 0 } := by
--         ext x
--         simp
--         constructor <;> intro hx
--         use x - a + 1
--         refine ⟨?_, ?_, ?_⟩ <;> linarith
--         rcases hx with ⟨i, hi⟩
--         exact hi.2.1
--       rw [h, this]
--       exact GenerateOpen.sUnion {Ioo a (a + i) | i > 0 }
--         fun _ ⟨i, hi, hs⟩ => hs ▸
--           GenerateOpen.basic (Ioo a (a + i)) (by 
--             simp only [mem_iUnion, mem_singleton_iff]
--             use a, a + i, lt_add_of_pos_right a hi)

end

namespace Polyhedral
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
open Module

def Polar (s : Set V) : Set (Dual ℝ V) := {f | ∀ x ∈ s, f x ≤ 1}

scoped notation (name := polar_of) s "ᵒ" => Polar s

theorem polar_mem_iff {f : Dual ℝ V} (s : Set V) : f ∈ sᵒ ↔ ∀ x ∈ s, f x ≤ 1 := Iff.rfl
theorem polar_mem {f : Dual ℝ V} (s : Set V) : f ∈ sᵒ → ∀ x ∈ s, f x ≤ 1 := id
theorem polar_zero_mem (s : Set V) : 0 ∈ sᵒ :=
  fun _ _ => by simp only [LinearMap.zero_apply, zero_le_one]
theorem polar_nonempty (s : Set V) : Set.Nonempty (sᵒ) := ⟨0, polar_zero_mem s⟩
theorem polar_eq_iInter (s : Set V) : sᵒ = ⋂ x ∈ s, {f | f x ≤ 1} := by
  ext f
  simp only [Polar, Set.mem_setOf_eq, Set.mem_iInter]
theorem polar_convex (s : Set V) : Convex ℝ (sᵒ) := by
  intro f h_f g h_g a b h_a h_b h_ab
  rw [polar_mem_iff] at *
  intro x h_x
  calc
    (a • f + b • g) x = a * (f x) + b * (g x) := by simp
    _ ≤ a + b := by
      apply add_le_add
      exact mul_le_of_le_one_right h_a (h_f x h_x)
      exact mul_le_of_le_one_right h_b (h_g x h_x)
    _ = 1 := h_ab
theorem polar_subset_double (s : Set V) : Dual.eval ℝ V '' s ⊆ sᵒᵒ := by
  rintro _ ⟨x, h_x, rfl⟩
  simp [Polar]
  intro f h
  exact h x h_x

def τ : TopologicalSpace V := ⨅ f : Dual ℝ V, TopologicalSpace.induced f inferInstance

def τ' [FiniteDimensional ℝ V] : TopologicalSpace (Dual ℝ V) := ⨅ x : V, TopologicalSpace.induced (Module.evalEquiv ℝ V x) inferInstance  

theorem τ_eq_τ' [FiniteDimensional ℝ V] : (τ : TopologicalSpace (Dual ℝ V)) = τ' := by
  simp only [τ]
  apply le_antisymm <;> apply le_iInf
  . intro x
    exact iInf_le _ (Module.evalEquiv ℝ V x)
  . intro x'
    apply iInf_le_of_le ((Module.evalEquiv ℝ V).symm x')
    simp only [LinearEquiv.apply_symm_apply, le_refl]

instance (priority := low) : letI _ : TopologicalSpace V := τ; ContinuousAdd V := by
  letI _ : TopologicalSpace V := τ
  apply ContinuousAdd.mk
  rw [continuous_iff_le_induced, instTopologicalSpaceProd]
  rw [τ, induced_iInf, induced_iInf, induced_iInf]
  rw [←iInf_inf_eq]
  simp only [le_iInf_iff]
  intro f
  rw [induced_compose]
  apply iInf_le_of_le f
  rw [induced_compose, induced_compose]
  rw [←coinduced_le_iff_le_induced]
  rw [TopologicalSpace.le_def]
  have : OrderTopology ℝ := inferInstance
  intro U h_U
  rw [isOpen_iff_generate_intervals] at h_U
  sorry

open scoped Topology

theorem polar_isClosed [FiniteDimensional ℝ V] (s : Set V) :
  let _ : TopologicalSpace (Dual ℝ V) := τ; IsClosed (sᵒ) := by
  rw [τ_eq_τ', polar_eq_iInter]
  apply @isClosed_biInter _ _ τ'
  intro x h_xs
  let τ'' : TopologicalSpace (Dual ℝ V) := TopologicalSpace.induced (fun f => f x) inferInstance
  have : IsClosed[τ''] {f | f x ≤ 1} := by
    rw [isClosed_induced_iff]
    use Set.Iic 1
    constructor
    . exact isClosed_Iic
    . ext f
      simp
  exact IsClosed.mono this (iInf_le _ x)

theorem LinearEquiv.preimage_eq_iff_eq_image {R α β : Type*} [Semiring R] [AddCommMonoid α] [Module R α] [AddCommMonoid β] [Module R β]
  (f : α ≃ₗ[R] β) (s : Set β) (t : Set α)  : f ⁻¹' s = t ↔ s = f '' t := Set.preimage_eq_iff_eq_image <| LinearEquiv.bijective f

theorem polar_eq_double_iff [FiniteDimensional ℝ V] (s : Set V) :
  let _ : TopologicalSpace V := τ
  let _ : TopologicalSpace (Dual ℝ (Dual ℝ V)) := τ
  evalEquiv ℝ V '' s = sᵒᵒ ↔ 0 ∈ s ∧ Convex ℝ s ∧ IsClosed s := by
  intro _ _
  let φ := evalEquiv ℝ V
  constructor
  . intro h
    have h_s_closed : IsClosed s := by
      rw [eq_comm, ←LinearEquiv.preimage_eq_iff_eq_image] at h
      rw [←h]
      refine IsClosed.preimage ?_ ?_
      . sorry
      . exact polar_isClosed (sᵒ)
    rw [LinearEquiv.image_eq_preimage] at h
    replace h : φ.symm '' (φ.symm ⁻¹' s) = φ.symm '' (sᵒᵒ) :=
      congrArg (Set.image φ.symm) h
    rw [Set.image_preimage_eq _ (LinearEquiv.surjective φ.symm)] at h
    rw [h]
    refine ⟨?_, ?_, ?_⟩
    . use 0, polar_zero_mem _, LinearEquiv.map_zero φ.symm
    . exact Convex.is_linear_image (polar_convex _)
            { map_add := (by apply LinearEquiv.map_add),
              map_smul := (by apply LinearEquiv.map_smul) }
    . exact h ▸ h_s_closed
      
  . rintro ⟨h_zero, h_convex, h_closed⟩
    ext x'
    simp only [Set.mem_image, Polar, Set.mem_setOf_eq]
    constructor
    . rintro ⟨x, h_xs, rfl⟩
      intro f h_f
      exact h_f x h_xs
    . intro h
      use φ.symm x'
      constructor
      . sorry
      . simp only [φ, LinearEquiv.apply_symm_apply]
  
end Polyhedral
