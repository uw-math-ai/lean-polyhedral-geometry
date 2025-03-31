import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
-- import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- import Mathlib.LinearAlgebra.LinearIndependent.Defs
-- import Mathlib.Topology.MetricSpace.Defs
-- import Mathlib.LinearAlgebra.Dual
-- import Mathlib.Topology.Defs.Basic

-- this says that V is a vector space over ℝ
variable {V: Type*} [AddCommGroup V] [Module ℝ V]

/-- a term `h : Halfspace s` is a proof that `s` is a halfspace -/
def Halfspace (s : Set V) : Prop :=
  -- "there exists a linear functional f and a constant c such that s equals the set of all points x in V such that f(x) ≤ c"
  ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), s = { x | f x ≤ c }

-- why does making `I` of Type* screw up `Polytope`?
def Polyhedron (s : Set V) : Prop :=
  ∃ (I : Type) (H : I → Set V), Finite I ∧ (∀ i : I, Halfspace (H i)) ∧ s = ⋂ (i : I), H i

--todo: eliminate the need to have an explicit inner product on V; i.e., show that it doesn't depend on the choice of inner product, so the definition can be made without such a choice)

section
variable [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

def Polytope (s : Set V) : Prop :=
  Polyhedron s ∧ Bornology.IsBounded s

end

def Cone (s : Set V) : Prop :=
  s.Nonempty ∧ ∀ c ≥ (0 : ℝ), ∀ x ∈ s, c • x ∈ s

def PolyhedralCone (s : Set V) : Prop :=
  Polyhedron s ∧ Cone s

#print convexHull

def conicalHull (s : Set V) : Set V :=
  { x | ∃ (t : Finset V) (a : V → ℝ),
    (∀ v ∈ t, 0 ≤ a v) ∧ ↑t ⊆ s ∧ x = ∑ v ∈ t, a v • v }

def isConicalCombo (s : Set V) (x : V) : Prop :=
  ∃ (ι : Type) (t : Finset ι) (a : t → ℝ) (v : t → V),
    (∀ i, 0 ≤ a i) ∧ (∀ i, v i ∈ s) ∧ x = ∑ i, a i • v i

def isConicalCombo_aux (s : Set V) (x : V) (n : ℕ) : Prop :=
  ∃ (a : Fin n → ℝ) (v : Fin n → V),
    (∀ i, 0 ≤ a i) ∧ (∀ i, v i ∈ s) ∧ x = ∑ i, a i • v i

--what's best?

def isConicalCombo' (s : Set V) (x : V) : Prop :=
  ∃ (ι : Type) (t : Finset ι) (a : ι → ℝ) (v : ι → V),
    (∀ i ∈ t, a i = 0 ∨ 0 ≤ a i ∧ v i ∈ s) ∧ x = ∑ i ∈ t, a i • v i

def isConicalCombo_aux' (s : Set V) (x : V) (n : ℕ) : Prop :=
  ∃ (a : ℕ → ℝ) (v : ℕ → V),
    (∀ i < n, a i = 0 ∨ 0 ≤ a i ∧ v i ∈ s) ∧ x = ∑ i ∈ Finset.range n, a i • v i

def conicalHull' (s : Set V) : Set V :=
  { x | isConicalCombo' s x }

--make alt defs of polyhedron and polytope in terms of convex hulls
