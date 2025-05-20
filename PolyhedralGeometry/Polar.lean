import PolyhedralGeometry.Defs
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Order.OrderClosed
--import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.Algebra.Module.ModuleTopology

section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
open Module

--theorem 1.5.1

namespace Polyhedral

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

section
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
  rw [TopologicalSpace.le_def]
  intro s h_s_open_f_add
  sorry

end

#synth letI _ : TopologicalSpace V := τ; ContinuousAdd V

open scoped Topology

--private local instance (priority := low) instModuleTopology : TopologicalSpace V := moduleTopology ℝ V

-- lemma moduleTopology_eq_τ : instModuleTopology (V := V) = τ := by
--   ext s
--   constructor <;> intro h_s_open
--   . sorry
--   . apply IsOpen.mono h_s_open
--     apply moduleTopology_le

-- def foo (α : Type) : TopologicalSpace α := ⊥
-- example (s : Set α) : @IsClosed α (foo α) s := @IsClosed.mk α (foo α) s trivial --ok
-- set_option pp.explicit true in
-- example (s : Set α) : @IsClosed α (foo α) s := IsClosed.mk trivial --fails

theorem polar_isClosed [FiniteDimensional ℝ V] (s : Set V) :
  let _ : TopologicalSpace (Dual ℝ V) := τ; IsClosed (sᵒ) := by
  intro τ_
  have : τ_ = τ' := τ_eq_τ'
  rw [this, polar_eq_iInter]
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

theorem polar_eq_double_iff [FiniteDimensional ℝ V] (s : Set V) :
  let _ : TopologicalSpace V := τ
  evalEquiv ℝ V '' s = sᵒᵒ ↔ 0 ∈ s ∧ Convex ℝ s ∧ IsClosed s := by
  let φ := evalEquiv ℝ V
  constructor
  . intro h
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
    -- . refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp ?_
    --   . exact τ₁
    --   . apply?
    --   . exact polar_isClosed (sᵒ)
    sorry
      
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
