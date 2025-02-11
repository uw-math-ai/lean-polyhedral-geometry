import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
--import Mathlib.Topology.MetricSpace.Defs
--import Mathlib.LinearAlgebra.Dual
--import Mathlib.Topology.Defs.Basic

-- this says that V is a vector space over ℝ
variable {V: Type*} [AddCommGroup V] [Module ℝ V]

/-- a term `h : Halfspace s` is a proof that `s` is a halfspace -/
def Halfspace (s : Set V) : Prop :=
  -- "there exists a linear functional f and a constant c such that s equals the set of all points x in V such that f(x) ≤ c"
  ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), s = { x | f x ≤ c }

-- why does making `I` of Type* screw up `Polytope`?
def Polyhedron (s : Set V) : Prop :=
  ∃ (I : Type) (H : I → Set V), Finite I ∧ (∀ i : I, Halfspace (H i)) ∧ s = ⋂ (i : I), H i

lemma halfspace_convex : ∀ (s : Set V), Halfspace s → Convex ℝ s := by
  intro s h_s_halfspace
  unfold Convex
  intro x h_x_in_s
  unfold StarConvex
  intro y h_y_in_s a b h_a_nonneg h_b_nonneg h_a_b_one
  show a • x + b • y ∈ s
  unfold Halfspace at h_s_halfspace
  rcases h_s_halfspace with ⟨f, ⟨c, rfl⟩⟩
  -- rw [Set.mem_def] at h_x_in_s
  -- dsimp at h_x_in_s -- doesn't work!
  have h_x_in_s : f x ≤ c := by assumption
  have h_y_in_s : f y ≤ c := by assumption
  show f (a • x + b • y) ≤ c
  calc
    f (a • x + b • y) = f (a • x) + f (b • y) := by
      apply LinearMap.map_add
    _ = a * f x + b * f y := by
      repeat rw [LinearMap.map_smul]
      rfl
    _ ≤ a * c + b * c := by
      apply add_le_add
      <;> apply mul_le_mul_of_nonneg_left
      <;> assumption
    _ = (a + b) * c := by rw [add_mul]
    _ = 1 * c := by rw [h_a_b_one]
    _ = c := one_mul c
--use this instead!
#check convex_halfSpace_le

theorem poly_convex : ∀ (s : Set V), Polyhedron s → Convex ℝ s := by
  intro s h_s_poly
  unfold Polyhedron at h_s_poly
  rcases h_s_poly with ⟨I, H, h_I_finite, h_Hi_halfspace, rfl⟩
  apply convex_iInter
  intro i
  exact halfspace_convex _ (h_Hi_halfspace i)

--todo: eliminate the need to have an explicit inner product on V; i.e., show that it doesn't depend on the choice of inner product, so the definition can be made without such a choice)
variable [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

def Polytope (s : Set V) : Prop :=
  Polyhedron s ∧ Bornology.IsBounded s

def Cone (s : Set V) : Prop :=
  Nonempty s ∧ ∀ c ≥ 0, ∀ x ∈ s, c • x ∈ s

def PolyhedralCone (s : Set V) : Prop :=
  Polyhedron s ∧ Cone s

example (s : Set V) : PolyhedralCone s → ∃ s' : ConvexCone ℝ V, s'.carrier = s := sorry

example (s : Set V) (f : V →ₗ[ℝ] ℝ) (c : ℝ) : Cone s → (∀ x ∈ s, f x ≤ c) → c ≥ 0 ∧ ∀ x ∈ s, f x ≤ 0 := by
  intro h_s_cone h_s_fc
  constructor
  . revert h_s_fc
    contrapose!
    intro h_c_lt_0
    use 0
    constructor
    . sorry
    . rw [LinearMap.map_zero f]
      exact h_c_lt_0
  . sorry
  -- contrapose
  -- push_neg
  -- intro h
  
variable [FiniteDimensional ℝ V] {ι : Type*} [Finite ι] (B : Basis ι ℝ V)



--todo:
--make alt defs of polyhedron and polytope in terms of convex hulls
