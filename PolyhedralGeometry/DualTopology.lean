import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Basic

open Module TopologicalSpace

section
variable (R : Type*) [CommSemiring R] [τR : TopologicalSpace R] (M : Type*) [AddCommMonoid M] [Module R M]

abbrev DualTopology : TopologicalSpace M :=
  ⨅ f : Dual R M, induced f τR

class IsDualTopology [τ : TopologicalSpace M] : Prop where
  eq_DualTopology' : τ = DualTopology R M

theorem eq_DualTopology [τ : TopologicalSpace M] [IsDualTopology R M] : τ = DualTopology R M :=
  IsDualTopology.eq_DualTopology' (R := R) (M := M)

theorem DualTopology_le : ∀ f : Dual R M, DualTopology R M ≤ induced f τR := fun f => iInf_le _ f

abbrev CodualTopology : TopologicalSpace (Dual R M) := ⨅ x : M, TopologicalSpace.induced (Dual.eval R M x) τR

class IsCodualTopology [τ : TopologicalSpace (Dual R M)] : Prop where
  eq_CodualTopology' : τ = CodualTopology R M

theorem eq_CodualTopology [τ : TopologicalSpace (Dual R M)] [IsCodualTopology R M] : τ = CodualTopology R M :=
  IsCodualTopology.eq_CodualTopology' (R := R) (M := M)

end

section finite
variable (R : Type*) [Field R] [TopologicalSpace R] (M : Type*) [AddCommGroup M] [Module R M] [FiniteDimensional R M] 

theorem DualTopology_eq_CodualTopology_of_finite : DualTopology R (Dual R M) = CodualTopology R M :=
  le_antisymm
    (le_iInf fun _ => iInf_le _ _)
    (le_iInf fun _ => iInf_le_of_le ((evalEquiv _ _).symm _)
      (by rw [←Module.evalEquiv_apply, LinearEquiv.apply_symm_apply]))

instance [TopologicalSpace (Dual R M)] [IsDualTopology R (Dual R M)] : IsCodualTopology R M where
  eq_CodualTopology' := DualTopology_eq_CodualTopology_of_finite R M ▸ eq_DualTopology R (Dual R M)

instance [TopologicalSpace (Dual R M)] [IsCodualTopology R M] : IsDualTopology R (Dual R M) where
  eq_DualTopology' := DualTopology_eq_CodualTopology_of_finite R M ▸ eq_CodualTopology R M

end finite

section finite
variable (R : Type*) [Field R] (M : Type*) [AddCommGroup M] [Module R M] [FiniteDimensional R M] [τM : TopologicalSpace M]

private abbrev DDual := Dual R (Dual R M)
  
-- instance (priority := low) [τ : TopologicalSpace M] [IsDualTopology R M] : TopologicalSpace (Dual R (Dual R M)) := induced (evalEquiv R M).symm τ

-- instance [τM : TopologicalSpace M] [IsDualTopology R M] [τ : TopologicalSpace (Dual R (Dual R M))] : τ = induced (evalEquiv R M).symm τM → IsDualTopology R (Dual R (Dual R M)) := by sorry

abbrev EvalTopology : TopologicalSpace (DDual R M) :=
  induced (evalEquiv R M).symm τM

class IsEvalTopology [τ : TopologicalSpace (DDual R M)] : Prop where
  eq_EvalTopology' : τ = EvalTopology R M

theorem eq_EvalTopology [τ : TopologicalSpace (DDual R M)] [IsEvalTopology R M] : τ = EvalTopology R M :=
  IsEvalTopology.eq_EvalTopology' (R := R) (M := M)

variable [TopologicalSpace R] [IsDualTopology R M]

theorem CodualTopology_eq_EvalTopology : CodualTopology R (Dual R M) = EvalTopology R M := by
  rw [eq_DualTopology R M]
  simp only [induced_iInf, induced_compose]
  have (f : Dual R M) : f ∘ ⇑(evalEquiv R M).symm = (Dual.eval R (Dual R M)) f :=
    (LinearEquiv.comp_symm_eq (Dual.eval _ _ _) _).mpr rfl
  exact iInf_congr fun f => this f ▸ rfl

theorem DualTopology_eq_EvalTopology : DualTopology R (DDual R M) = EvalTopology R M := CodualTopology_eq_EvalTopology R M ▸ DualTopology_eq_CodualTopology_of_finite R (Dual R M)

variable [TopologicalSpace (DDual R M)] [IsEvalTopology R M]

instance : IsDualTopology R (DDual R M) where
  eq_DualTopology' := DualTopology_eq_EvalTopology R M ▸ eq_EvalTopology R M

-- theorem evalEquiv_symm_IsHomeomorph : IsHomeomorph (evalEquiv R M).symm where
--   continuous := Topology.IsInducing.continuous (evalEquiv_symm_IsInducing _ _)
--   isOpenMap := Topology.IsInducing.isOpenMap (evalEquiv_symm_IsInducing _ _)
--     (by simp only [EquivLike.range_eq_univ, isOpen_univ])
--   bijective := LinearEquiv.bijective (evalEquiv R M).symm

-- theorem evalEquiv_IsHomeomorph : IsHomeomorph (evalEquiv R M) := by
--   refine isHomeomorph_iff_exists_inverse.mpr ?_
  
--   sorry

end finite
section finite
variable (R : Type*) [Field R] (M : Type*) [AddCommGroup M] [Module R M] [FiniteDimensional R M] [TopologicalSpace M] [TopologicalSpace (DDual R M)] [IsEvalTopology R M]

theorem evalEquiv_symm_IsInducing : Topology.IsInducing (evalEquiv R M).symm :=
  { eq_induced := by rw [eq_EvalTopology R M] }

private noncomputable def evalEquivTop_aux : DDual R M ≃L[R] M :=
  ContinuousLinearEquiv.mk (evalEquiv R M).symm
    (Topology.IsInducing.continuous (evalEquiv_symm_IsInducing _ _))
    { isOpen_preimage := fun s hs => by
        simp
        rw [←LinearEquiv.image_symm_eq_preimage (evalEquiv R M) s]
        exact Topology.IsInducing.isOpenMap (evalEquiv_symm_IsInducing R M)
          (by simp only [EquivLike.range_eq_univ, isOpen_univ]) s hs }

noncomputable def evalEquivTop : M ≃L[R] DDual R M := (evalEquivTop_aux R M).symm

@[simp] lemma evalEquivTop_toLinearMap : evalEquivTop R M = Dual.eval R M := rfl

@[simp] lemma evalEquivTop_apply (m : M) : evalEquivTop R M m = Dual.eval R M m := rfl

@[simp] lemma apply_evalEquivTop_symm_apply (f : Dual R M) (g : Dual R (Dual R M)) :
    f ((evalEquivTop R M).symm g) = g f := by
  set m := (evalEquivTop R M).symm g
  rw [← (evalEquivTop R M).apply_symm_apply g, evalEquivTop_apply, Dual.eval_apply]

end finite

namespace DualTopology
variable {R : Type*} [CommSemiring R] [TopologicalSpace R] {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [IsDualTopology R M] 

theorem continuous_functional (f : Dual R M) : Continuous f where
  isOpen_preimage := fun _ h => eq_DualTopology R M ▸ (Iff.subst (p := id) TopologicalSpace.le_def (DualTopology_le R M f)) _ (isOpen_induced h)
      
end DualTopology

