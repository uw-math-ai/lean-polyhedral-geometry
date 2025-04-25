import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

section
open Finset

theorem Finset.induction_on_nonempty_base {α : Type*} [DecidableEq α] (p : Finset α → Prop) (t₀ : Finset α) (base : p t₀) (ih : ∀ (t : Finset α) (a : α), t₀ ⊆ t → p t → p (insert a t)) : ∀ t : Finset α, t₀ ⊆ t → p t := by
  intro t h_subset_t
  by_cases h_eq : t₀ = t
  . rw[←h_eq]; exact base
  have h_ssubset_t : t₀ ⊂ t := by apply ssubset_of_ne_of_subset <;> assumption
  clear h_eq
  rcases Finset.exists_of_ssubset h_ssubset_t with ⟨a, h_at, h_at₀⟩
  let t' := t.erase a
  have h_t' : t = insert a t' := by rw [Finset.insert_erase h_at]
  rw [h_t']
  have h_subset_t' : t₀ ⊆ t' := by
    rw [h_t'] at h_subset_t
    exact (Finset.subset_insert_iff_of_not_mem h_at₀).mp h_subset_t
  apply ih
  . exact h_subset_t'
  have : a ∉ t' := not_mem_erase a t
  have h_card : #t' < #t := by
    rw[h_t']
    exact Finset.card_lt_card (Finset.ssubset_insert this)
  apply induction_on_nonempty_base p t₀ base ih t' h_subset_t'
  termination_by t _ => #t

end
