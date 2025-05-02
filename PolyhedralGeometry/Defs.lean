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
variable {V : Type*} [AddCommGroup V] [Module ℝ V] (s : Set V)

/-- a term `h : Halfspace s` is a proof that `s` is a halfspace -/
def Halfspace : Prop :=
  -- "there exists a linear functional f and a constant c such that s equals the set of all points x in V such that f(x) ≤ c"
  ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), s = { x | f x ≤ c }

-- why does making `I` of Type* screw up `Polytope`?
def Polyhedron : Prop :=
  ∃ (I : Type) (H : I → Set V), Finite I ∧ (∀ i : I, Halfspace (H i)) ∧ s = ⋂ (i : I), H i

--todo: eliminate the need to have an explicit inner product on V; i.e., show that it doesn't depend on the choice of inner product, so the definition can be made without such a choice)

-- def Polytope' (s : Set V) : Prop :=
--   Polyhedron s ∧ ∀ _ : SeminormedAddCommGroup V, ∀ _ : InnerProductSpace ℝ V, Bornology.IsBounded s

-- theorem bounded_iff_bounded_all (s : Set V) : Polytope' s ↔ Polyhedron s ∧ ∃ (_ : SeminormedAddCommGroup V) (_ : InnerProductSpace ℝ V), Bornology.IsBounded s := by sorry

def Cone : Prop :=
  s.Nonempty ∧ ∀ c ≥ (0 : ℝ), ∀ x ∈ s, c • x ∈ s

def PolyhedralCone : Prop :=
  Polyhedron s ∧ Cone s

#print convexHull

def isConicalCombo' (x : V) : Prop :=
  ∃ (ι : Type) (t : Finset ι) (a : ι → ℝ) (v : ι → V),
    (∀ i ∈ t, a i = 0 ∨ 0 ≤ a i ∧ v i ∈ s) ∧ x = ∑ i ∈ t, a i • v i

def isConicalCombo_aux' (x : V) (n : ℕ) : Prop :=
  ∃ (a : ℕ → ℝ) (v : ℕ → V),
    (∀ i < n, a i = 0 ∨ 0 ≤ a i ∧ v i ∈ s) ∧ x = ∑ i ∈ Finset.range n, a i • v i

def conicalHull' : Set V :=
  { x | isConicalCombo' s x }

end

--figure out how closure operators work (to define conicalHull like mathlib's convexHull)

--make alt defs of polyhedron and polytope in terms of convex hulls

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (s : Set V)

#check (inferInstance : PseudoMetricSpace V)
#check (inferInstance : T2Space V)
#check (inferInstance : ProperSpace V)

def Polytope : Prop :=
  Polyhedron s ∧ Bornology.IsBounded s
  
end
