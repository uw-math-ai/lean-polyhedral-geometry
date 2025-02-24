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
  s.Nonempty ∧ ∀ c ≥ (0 : ℝ), ∀ x ∈ s, c • x ∈ s

def PolyhedralCone (s : Set V) : Prop :=
  Polyhedron s ∧ Cone s

example (s : Set V) : PolyhedralCone s → ∃ s' : ConvexCone ℝ V, s'.carrier = s := sorry

--lemma 1.2.2
example (s : Set V) (f : V →ₗ[ℝ] ℝ) (c : ℝ) : Cone s → (∀ x ∈ s, f x ≤ c) → c ≥ 0 ∧ ∀ x ∈ s, f x ≤ 0 := by
  intro h_s_cone h_s_fc
  constructor
  · revert h_s_fc
    contrapose!
    intro h_c_lt_0
    use 0
    constructor
    · unfold Cone at h_s_cone
      obtain ⟨x, hx⟩ := h_s_cone.left
      have h₀ : (0 : ℝ) • x ∈ s := h_s_cone.right (0 : ℝ) (by norm_num) x hx
      rw [Module.zero_smul x] at h₀
      exact h₀
    · rw [LinearMap.map_zero f]
      exact h_c_lt_0
  · intro x₀ x_in_s
    apply not_lt.mp
    intro assump_0_le_fx
    have h_0_le_inv_fx : 0 < (f x₀)⁻¹ := by exact inv_pos_of_pos assump_0_le_fx
    unfold Cone at h_s_cone
    have lt_c : f x₀ ≤ c := h_s_fc x₀ x_in_s
    have ge_0_c : 0 < c := lt_of_lt_of_le assump_0_le_fx lt_c
    have gq_2c_fxinv : 0 < 2 * c * (f x₀)⁻¹ := by
      apply mul_pos
      norm_num
      apply ge_0_c
      norm_num
      apply assump_0_le_fx
    have : (2 * c * (f x₀)⁻¹) • x₀ ∈ s := h_s_cone.right (2 * c * (f x₀)⁻¹) (by linarith) x₀ x_in_s
    have le_c : f ((2 * c * (f x₀)⁻¹) • x₀) ≤ c := h_s_fc ((2 * c * (f x₀)⁻¹) • x₀) this
    have : f x₀ ≠ 0 := Ne.symm (ne_of_lt assump_0_le_fx)
    rw [LinearMap.map_smul] at le_c
    dsimp at le_c
    rw [mul_assoc, inv_mul_cancel₀ this, mul_one] at le_c
    show False
    linarith

--todo:
--define conical hulls
--smallest conic set that contains s

open Lean.Parser.Module.prelude
#check convexHull

-- def LinearCombo [Finite I] {n : ℕ} (I : Type) (vecs : I → Set V) (scals : I → ℝ) : V := ∑ i ∈ (Finset.univ I), (scals i) • (vecs i)

def LinearCombo (x : V) : Prop :=
  ∃ (I : Finset) (vecs : I → V) (scal)


def conicHull (s : Set V) :  Set V :=
  { x : V | ∃ (n : ℕ) (v : Fin n → V) (a : Fin n → ℝ),
  (∀ i, 0 ≤ a i) ∧ (∀ i, v i ∈ s)
  ∧ (x = ∑ i ∈ (Finset.univ : Finset (Fin n)), a i • v i) }

--define conical combination
variable [FiniteDimensional ℝ V] {ι : Type*} [Finite ι] (B : Basis ι ℝ V)
--state our version of Caratheodory's theorem

-- theorem caratheordory_theorem (s : Set V) : (x ∈ (convexHull s) → ∃ (b : V)) ∧ (x ∈ (conicHull s) → )

theorem caratheordory_theorem
  {d : Nat}
  (s : Set V)
  (x : V)
  (hx : x ∈ conicHull s)
  : (∃ (T : Finset V),
      T ⊆ S ∧            -- T is a subset of S
      T.card ≤ d + 1 ∧    -- T has at most d+1 elements
      x ∈ conicHull T)
  := sorry

--prove it, either by hand or by using mathlib's version

--make alt defs of polyhedron and polytope in terms of convex hulls


theorem noGreatestNumber : (∀ (x : ℝ), ∃ y, y > x)
