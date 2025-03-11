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

def Polyhedron (s : Set V) : Prop :=
  ∃ (I : Type*) (H : I → Set V), Finite I ∧ (∀ i : I, Halfspace (H i)) ∧ s = ⋂ (i : I), H i

lemma halfspace_convex : ∀ (s : Set V), Halfspace s → Convex ℝ s := by
  intro s h_s_halfspace
  rcases h_s_halfspace with ⟨f, ⟨c, rfl⟩⟩
  convert convex_halfSpace_le ?_ ?_
  . exact inferInstance
  . exact inferInstance
  . exact LinearMap.isLinear f

theorem poly_convex : ∀ (s : Set V), Polyhedron s → Convex ℝ s := by
  --to do it the easy way, use `convex_iInter`
  sorry

--todo:
--variable [FiniteDimensional ℝ V] {ι : Type*} [Finite ι] (B : Basis ι ℝ V)




--todo:
--define polytope (needs notion of boundedness; show that it doesn't depend on the choice of inner product, so the definition can be made without such a choice)
































