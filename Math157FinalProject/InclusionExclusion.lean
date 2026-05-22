import Mathlib

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]

lemma biUnion_insert (s : Finset β) (b : β) (S : β → Finset α) :
  (insert b s).biUnion S = S b ∪ s.biUnion S := by
  sorry

lemma biUnion_empty (S : β → Finset α) :
  (∅ : Finset β).biUnion S = ∅ := by
  sorry

lemma mem_biUnion (x : α) (s : Finset β) (S : β → Finset α) :
  x ∈ s.biUnion S ↔ ∃ b ∈ s, x ∈ S b := by
  sorry

lemma mem_inf_iff_forall (x : α) (T : Finset β) (S : β → Finset α)  :
  x ∈ T.inf S ↔ ∀ b ∈ T, x ∈ S b := by
  sorry

lemma mem_powerset (T : Finset β) (s : Finset β):
  T ∈ s.powerset ↔ T ⊆ s := by
  sorry

lemma alternating_sum_powerset (T : Finset β) (s : Finset β) (h : s.Nonempty):
  ∑ T ∈ s.powerset, (-1 : ℤ) ^ T.card = 0 := by
  sorry

theorem inclusion_exclusion
    (s : Finset β)
    (S : β → Finset α) :
    (card (s.biUnion S) : ℤ) =
      ∑ T ∈ (s.powerset.erase ∅),
        ((-1 : ℤ) ^ (T.card + 1)) *
          (card (T.inf S) : ℤ) := by
  sorry
