/-
The first 2 lemmas are basically just a recursive definition of unioning over a finite set of sets.
Lemma 1 is basically saying that the finite union of s + 1 sets is the union of one of the sest and the finite union of the remaining sets.
We prove this by showing that an element belongs to the left-hand side if and only if it belongs to the right-hand side.
We then split into cases depending on whether the element comes from the newly inserted set or from one of the sets already in the family.

Lemma 2 is saying that the finite union over an empty set of sets is empty.
This follows directly from the definition of a finite union, and the proof simply shows that no element can belong to either side.

Lemma 3 provides a definition for what it means for an element to be in the finite union of a family of sets.
It says that an element is in the finite union if and only if there is some set in the family that contains the element.
We prove this by induction on the size of the set. The base case is the empty family of sets, where the statement is immediate.
For the inductive step, we use Lemma 1 to rewrite the union as a union of two pieces and then verify the membership condition directly.

Lemma 4 provides an analogous definition for what it means for an element to be in the finite intersection of a family of sets.
It says that an element is in the finite intersection if and only if it is in every set in the family.
Again, we prove this by induction on the indexing set. The base case uses the fact that the intersection of an empty family is the universal set.
For the inductive step, we rewrite the intersection as the intersection of one set with the intersection of the remaining sets and then apply the induction hypothesis.

Lemma 5 provides a definition for what it means for a set to be in the powerset of another set.
It says that a set is in the powerset of another set if and only if it is a subset of that set.
The proof proceeds by induction on the larger set. We use the recursive description of the powerset, splitting into the cases where a subset contains the newly inserted element and where it does not.
We then apply the induction hypothesis to the remaining elements.

Lastly, Lemma 6 proves a very important combinatorial identity that is used in the proof of the inclusion-exclusion principle.
It says that the alternating sum of the sizes of the subsets of a nonempty set is zero.
This is a key step in the proof of the inclusion-exclusion principle, as it allows us to
show that the contributions from the various intersections of sets cancel out in a certain way,
which allows us to later show that each element contributes exactly once to the final count of the size of the union of the sets.
The proof chooses an element of the set and partitions all subsets into pairs: those that contain the chosen element and those that do not.
Adding the chosen element changes the parity of the subset size, which changes the sign of its contribution in the alternating sum.
As a result, every subset is paired with another subset contributing the opposite value, causing all terms to cancel and leaving a total of zero.

Our final theorem, the inclusion-exclusion principle, states that the size of the union of a finite family of sets can be expressed as an alternating sum of the sizes of the intersections of those sets.
We have not proven this yet.
-/

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

set_option linter.unusedDecidableInType false in
lemma alternating_sum_powerset (s : Finset β) (h : s.Nonempty) :
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
