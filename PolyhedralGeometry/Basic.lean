import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
--import Mathlib.LinearAlgebra.FiniteDimensional.Defs
--import Mathlib.LinearAlgebra.Dual
--import Mathlib.Topology.Defs.Basic
--import Mathlib.Topology.MetricSpace.Defs

-- this says that V is a vector space over ℝ
variable {V: Type*} [AddCommGroup V] [Module ℝ V]

/-- a term `h : Halfspace s` is a proof that `s` is a halfspace -/
def Halfspace (s : Set V) : Prop :=
  -- "there exists a linear functional f and a constant c such that s equals the set of all points x in V such that f(x) ≤ c"
  ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), s = { x | f x ≤ c }

--define polyhedron (we need a notion of finite set/type for this!)
def Polyhedron (s : Set V) : Prop := sorry

--show that a halfspace is convex
lemma halfspace_convex : ∀ (s : Set V), Halfspace s → Convex ℝ s := by
  sorry

--show that a polyhedron is convex
theorem poly_convex : ∀ (s : Set V), Polyhedron s → Convex ℝ s := by
  sorry

--todo:
--variable [FiniteDimensional ℝ V] {ι : Type*} [Finite ι] (B : Basis ι ℝ V)



































