import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.InnerProductSpace.Defs

section
variable {V : Type*} [AddCommMonoid V] [Module ℝ V] (s : Set V)

def Halfspace : Prop :=
  ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), s = { x | f x ≤ c }

def IsPolyhedron : Prop :=
  ∃ (ι : Type*) (H : ι → Set V), Finite ι ∧ (∀ i : ι, Halfspace (H i)) ∧ s = ⋂ (i : ι), H i

variable (V) in
@[ext]
structure Polyhedron where
  carrier : Set V
  protected is_polyhedron' : ∃ (ι : Type*) (H : ι → Set V), Finite ι ∧ (∀ i : ι, Halfspace (H i)) ∧ carrier = ⋂ (i : ι), H i

theorem isPolyhedron_def (s : Polyhedron.{_,u} V) : IsPolyhedron.{_,u} s.carrier := s.is_polyhedron'

end

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (s : Set V)

def Polytope.{u} : Prop :=
  IsPolyhedron.{_, u} s ∧ Bornology.IsBounded s

-- theorem bounded_iff_bounded_all (s : Set V) : Polytope' s ↔ IsPolyhedron s ∧ ∃ (_ : SeminormedAddCommGroup V) (_ : InnerProductSpace ℝ V), Bornology.IsBounded s := by sorry
  
end
