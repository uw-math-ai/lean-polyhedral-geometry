import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
-- import Mathlib.LinearAlgebra.LinearIndependent.Defs
-- import Mathlib.Topology.MetricSpace.Defs
-- import Mathlib.LinearAlgebra.Dual
-- import Mathlib.Topology.Defs.Basic

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

end

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (s : Set V)

def Polytope.{u} : Prop :=
  IsPolyhedron.{_, u} s ∧ Bornology.IsBounded s

-- theorem bounded_iff_bounded_all (s : Set V) : Polytope' s ↔ IsPolyhedron s ∧ ∃ (_ : SeminormedAddCommGroup V) (_ : InnerProductSpace ℝ V), Bornology.IsBounded s := by sorry
  
end
