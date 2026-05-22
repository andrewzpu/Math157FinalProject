import Mathlib

open Finset

variable {α : Type*}

variable {α : Type*} [DecidableEq α]

theorem card_union_two (A B : Finset α) :
    card (A ∪ B) = card A + card B - card (A ∩ B) := by
  induction A using Finset.induction_on with
  | empty =>
      simp
  | insert a s hnotmem ih =>
      by_cases hb : a ∈ B
      · rw [Finset.insert_inter_of_mem hb]
        rw [Finset.card_insert_of_notMem
          (by simp [hnotmem])]
        grind
      · rw [Finset.insert_inter_of_notMem hb]
        rw [Finset.card_insert_of_notMem hnotmem]
        grind

theorem disjoint_union (A B : Finset α) :
    Disjoint A B → card (A ∪ B) = card A + card B := by
  intro h
  rw [card_union_two]
  have : A ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h
  simp [this]

theorem same_union (A : Finset α) :
    card (A ∪ A) = card A := by
  rw [card_union_two]
  simp
