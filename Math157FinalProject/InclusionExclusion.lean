import Mathlib

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]

omit [Fintype α] in
lemma biUnion_insert (s : Finset β) (b : β) (S : β → Finset α) :
  (insert b s).biUnion S = S b ∪ s.biUnion S := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨c, hc | hc, hx⟩
    · left; subst hc; exact hx
    · right; exact ⟨c, hc, hx⟩
  · rintro (hx | ⟨c, hc, hx⟩)
    · exact ⟨b, Or.inl rfl, hx⟩
    · exact ⟨c, Or.inr hc, hx⟩

omit [DecidableEq β] [Fintype α] in
lemma biUnion_empty (S : β → Finset α) :
  (∅ : Finset β).biUnion S = ∅ := by
  ext x
  simp only [Finset.biUnion_empty, notMem_empty]

set_option linter.unusedDecidableInType false in
omit [Fintype α] in
lemma mem_biUnion (x : α) (s : Finset β) (S : β → Finset α) :
    x ∈ s.biUnion S ↔ ∃ b ∈ s, x ∈ S b := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert b t hnotmem ih =>
      rw [_root_.biUnion_insert]
      simp only [Finset.mem_union, Finset.mem_insert, ih]
      constructor
      · rintro (hx | ⟨c, hc, hx⟩)
        · exact ⟨b, Or.inl rfl, hx⟩
        · exact ⟨c, Or.inr hc, hx⟩
      · rintro ⟨c, hc | hc, hx⟩
        · left; subst hc; exact hx
        · right; exact ⟨c, hc, hx⟩

set_option linter.unusedDecidableInType false in
lemma mem_inf_iff_forall (x : α) (T : Finset β) (S : β → Finset α) :
    x ∈ T.inf S ↔ ∀ b ∈ T, x ∈ S b := by
  induction T using Finset.induction_on with
  | empty =>
      simp [Finset.inf_empty]
  | insert b t hnotmem ih =>
      rw [Finset.inf_insert]
      simp only [inf_eq_inter', mem_inter, Finset.mem_insert, ih]
      constructor
      · rintro ⟨hx, hall⟩ c (rfl | hc)
        · exact hx
        · exact hall c hc
      · intro hall
        exact ⟨hall b (Or.inl rfl), fun c hc => hall c (Or.inr hc)⟩

set_option linter.unusedDecidableInType false in
omit [Fintype α] in
lemma mem_powerset (T : Finset β) (s : Finset β) :
    T ∈ s.powerset ↔ T ⊆ s := by
  induction s using Finset.induction_on with
  | empty =>
      simp [Finset.powerset_empty, Finset.subset_empty]
  | insert a t hnotmem ih =>
      rw [Finset.powerset_insert]
      simp only [Finset.mem_union, Finset.mem_image, ih]
      constructor
      · rintro (hT | ⟨U, hU, rfl⟩)
        · exact Finset.Subset.trans hT (Finset.subset_insert _ t)
        · intro y hy
          simp only [Finset.mem_insert] at hy
          cases hy with
          | inl h => subst h; exact Finset.mem_insert_self _ t
          | inr h => exact Finset.mem_insert_of_mem (Finset.mem_powerset.mp hU h)
      · intro hT
        by_cases ha : a ∈ T
        · right
          refine ⟨T.erase a, ?_, ?_⟩
          · rw [Finset.mem_powerset]
            intro x hx
            have hx' := hT (Finset.mem_of_mem_erase hx)
            simp only [Finset.mem_insert] at hx'
            exact hx'.resolve_left (Finset.ne_of_mem_erase hx)
          · exact Finset.insert_erase ha
        · left
          intro x hx
          have hx' := hT hx
          simp only [Finset.mem_insert] at hx'
          exact hx'.resolve_left (fun h => ha (h ▸ hx))

lemma alternating_sum_powerset (T : Finset β) (s : Finset β) (h : s.Nonempty):
  ∑ T ∈ s.powerset, (-1 : ℤ) ^ T.card = 0 := by
  rcases h with ⟨a, ha⟩
  let t := s.erase a
  have hs : s = insert a t := by
    simp [t, ha]
  have hat : a ∉ t := by
    simp [t]
  rw [hs, Finset.sum_powerset_insert hat]
  have hneg :
      ∑ u ∈ t.powerset, (-1 : ℤ) ^ (insert a u).card =
        -∑ u ∈ t.powerset, (-1 : ℤ) ^ u.card := by
    calc
      ∑ u ∈ t.powerset, (-1 : ℤ) ^ (insert a u).card
          = ∑ u ∈ t.powerset, -((-1 : ℤ) ^ u.card) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              have hau : a ∉ u := Finset.notMem_of_mem_powerset_of_notMem hu hat
              rw [Finset.card_insert_of_notMem hau, pow_succ]
              ring
      _ = -∑ u ∈ t.powerset, (-1 : ℤ) ^ u.card := by
            rw [Finset.sum_neg_distrib]
  rw [hneg]
  ring

theorem inclusion_exclusion
    (s : Finset β)
    (S : β → Finset α) :
    (card (s.biUnion S) : ℤ) =
      ∑ T ∈ (s.powerset.erase ∅),
        ((-1 : ℤ) ^ (T.card + 1)) *
          (card (T.inf S) : ℤ) := by
  sorry
