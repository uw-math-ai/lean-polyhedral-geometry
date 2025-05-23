import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Module TopologicalSpace

section
variable (R : Type*) [CommSemiring R] [TopologicalSpace R] (M : Type*) [AddCommMonoid M] [Module R M]

abbrev DualTopology : TopologicalSpace M :=
  ⨅ f : Dual R M, induced f inferInstance

class IsDualTopology [τ : TopologicalSpace M] : Prop where
  eq_DualTopology' : τ = DualTopology R M

theorem eq_DualTopology [τ : TopologicalSpace M] [IsDualTopology R M] : τ = DualTopology R M :=
  IsDualTopology.eq_DualTopology' (R := R) (M := M)

theorem DualTopology_le : ∀ f : Dual R M, DualTopology R M ≤ induced f inferInstance := fun f => iInf_le _ f

abbrev CodualTopology : TopologicalSpace (Dual R M) := ⨅ x : M, TopologicalSpace.induced (Dual.eval R M x) inferInstance

class IsCodualTopology [τ : TopologicalSpace (Dual R M)] : Prop where
  eq_CodualTopology' : τ = CodualTopology R M

theorem eq_CodualTopology [τ : TopologicalSpace (Dual R M)] [IsCodualTopology R M] : τ = CodualTopology R M :=
  IsCodualTopology.eq_CodualTopology' (R := R) (M := M)

end

section finite
variable (R : Type*) [Field R] [TopologicalSpace R] (M : Type*) [AddCommGroup M] [Module R M]

theorem DualTopology_eq_CodualTopology_of_finite [FiniteDimensional R M] : DualTopology R (Dual R M) = CodualTopology R M :=
  le_antisymm
    (le_iInf fun _ => iInf_le _ _)
    (le_iInf fun _ => iInf_le_of_le ((evalEquiv _ _).symm _)
      (by rw [←Module.evalEquiv_apply, LinearEquiv.apply_symm_apply]))

instance instCodualTopology_ofDualTopology [FiniteDimensional R M] [TopologicalSpace (Dual R M)] [IsDualTopology R (Dual R M)] : IsCodualTopology R M where
  eq_CodualTopology' := DualTopology_eq_CodualTopology_of_finite R M ▸ eq_DualTopology R (Dual R M)

instance instDualTopology_ofCodualTopology [FiniteDimensional R M] [TopologicalSpace (Dual R M)] [IsCodualTopology R M] : IsCodualTopology R M where
  eq_CodualTopology' := DualTopology_eq_CodualTopology_of_finite R M ▸ eq_CodualTopology R M
      
end finite

namespace DualTopology
variable {R : Type*} [CommSemiring R] [TopologicalSpace R] {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [IsDualTopology R M] 

theorem continuous_functional (f : Dual R M) : Continuous f where
  isOpen_preimage := fun _ h => eq_DualTopology R M ▸ (Iff.subst (p := id) TopologicalSpace.le_def (DualTopology_le R M f)) _ (isOpen_induced h)
      
end DualTopology
