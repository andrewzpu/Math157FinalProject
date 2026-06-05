import Mathlib

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]

omit [Fintype α] in
lemma biUnion_insert (s : Finset β) (b : β) (S : β → Finset α) :
  (insert b s).biUnion S = S b ∪ s.biUnion S := by
  ext x
  simp only [Finset.mem_union, Finset.biUnion, Finset.mem_val,
             Multiset.mem_toFinset, Finset.insert_val, Multiset.mem_bind,
             Multiset.mem_ndinsert]
  constructor
  · rintro ⟨a, (rfl | ha), hx⟩
    · left; exact hx
    · right; exact ⟨a, ha, hx⟩
  · rintro (hx | ⟨a, ha, hx⟩)
    · exact ⟨b, Or.inl rfl, hx⟩
    · exact ⟨a, Or.inr ha, hx⟩

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
  induction s using Finset.induction_on generalizing T with
  | empty =>
      simp [Finset.powerset_empty, Finset.subset_empty]
  | insert a t hnotmem ih =>
      rw [Finset.powerset_insert]
      simp only [Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (hT | ⟨U, hU, rfl⟩)
        · rw [ih] at hT
          exact Finset.Subset.trans hT (Finset.subset_insert _ t)
        · intro y hy
          simp only [Finset.mem_insert] at hy
          cases hy with
          | inl h => subst h; exact Finset.mem_insert_self _ t
          | inr h =>
              exact Finset.mem_insert_of_mem ((ih U).mp hU h)
      · intro hT
        by_cases ha : a ∈ T
        · right
          refine ⟨T.erase a, ?_, ?_⟩
          · rw [ih]
            intro x hx
            have hx' := hT (Finset.mem_of_mem_erase hx)
            simp only [Finset.mem_insert] at hx'
            exact hx'.resolve_left (Finset.ne_of_mem_erase hx)
          · exact Finset.insert_erase ha
        · left
          rw [ih]
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
  classical
  conv_lhs =>
    rw [show (card (s.biUnion S) : ℤ) = ∑ _x ∈ s.biUnion S, (1 : ℤ) by simp]
  have h_card_inf :
      ∀ T ∈ s.powerset.erase ∅,
        (card (T.inf S) : ℤ) =
          ∑ x ∈ s.biUnion S, if x ∈ T.inf S then (1 : ℤ) else 0 := by
    intro T hT
    have hTmem : T ∈ s.powerset := Finset.mem_of_mem_erase hT
    have hTsub : T ⊆ s := (mem_powerset T s).mp hTmem
    have hTne  : T ≠ ∅ := Finset.ne_of_mem_erase hT
    have h_subset : T.inf S ⊆ s.biUnion S := by
      intro x hx
      rw [_root_.mem_biUnion]
      rw [mem_inf_iff_forall] at hx
      obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hTne
      exact ⟨b, hTsub hb, hx b hb⟩
    have : (card (T.inf S) : ℤ) =
        ∑ x ∈ T.inf S, (1 : ℤ) := by
      simp
    rw [this]
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => ⟨h_subset hx, hx⟩, fun ⟨_, hx⟩ => hx⟩
  have h_card_inf' :
      ∀ T ∈ s.powerset.erase ∅,
        ((-1 : ℤ) ^ (T.card + 1)) * (card (T.inf S) : ℤ) =
        ((-1 : ℤ) ^ (T.card + 1)) * ∑ x ∈ s.biUnion S, if x ∈ T.inf S then (1 : ℤ) else 0 := by
    intro T hT
    congr 1
    exact h_card_inf T hT
  rw [Finset.sum_congr rfl h_card_inf']
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  set A := s.filter (fun b => x ∈ S b) with hA_def
  have hA_nonempty : A.Nonempty := by
    rw [_root_.mem_biUnion] at hx
    obtain ⟨b, hbs, hxb⟩ := hx
    exact ⟨b, Finset.mem_filter.mpr ⟨hbs, hxb⟩⟩
  have h_inf_iff_subset :
      ∀ T ∈ s.powerset.erase ∅,
        x ∈ T.inf S ↔ T ⊆ A := by
    intro T hT
    have hTsub : T ⊆ s :=
      (mem_powerset T s).mp (Finset.mem_of_mem_erase hT)
    rw [mem_inf_iff_forall]
    constructor
    · intro hall b hb
      exact Finset.mem_filter.mpr ⟨hTsub hb, hall b hb⟩
    · intro hTA b hb
      exact (Finset.mem_filter.mp (hTA hb)).2
  have h_filter_eq :
      (s.powerset.erase ∅).filter (fun T => x ∈ T.inf S) =
      A.powerset.erase ∅ := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_erase, mem_powerset, ne_eq]
    constructor
    · intro ⟨⟨hTne, hTsub⟩, hxT⟩
      refine ⟨hTne, ?_⟩
      exact (h_inf_iff_subset T
        (Finset.mem_erase.mpr ⟨hTne, (mem_powerset T s).mpr hTsub⟩)).mp hxT
    · intro ⟨hTne, hTA⟩
      have hTsub_A : T ⊆ s :=
        Finset.Subset.trans hTA (Finset.filter_subset _ s)
      refine ⟨⟨hTne, hTsub_A⟩, ?_⟩
      exact (h_inf_iff_subset T
        (Finset.mem_erase.mpr ⟨hTne, (mem_powerset T s).mpr hTsub_A⟩)).mpr hTA
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, h_filter_eq]
  have h_alt : ∑ T ∈ A.powerset.erase ∅, (-1 : ℤ) ^ (T.card + 1) = 1 := by
    have hmem : (∅ : Finset β) ∈ A.powerset :=
      (mem_powerset ∅ A).mpr (Finset.empty_subset A)
    have h_alt : ∑ T ∈ A.powerset.erase ∅, (-1 : ℤ) ^ (T.card + 1) = 1 := by
      have h0 := alternating_sum_powerset A hA_nonempty
      have hfull : ∑ T ∈ A.powerset, (-1 : ℤ) ^ (T.card + 1) = 0 := by
        have : ∑ T ∈ A.powerset, (-1 : ℤ) ^ (T.card + 1)
             = -1 * ∑ T ∈ A.powerset, (-1 : ℤ) ^ T.card := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T _
          ring
        rw [this, h0, mul_zero]
      have hsplit := Finset.sum_erase_add A.powerset
                      (fun T => (-1:ℤ)^(T.card+1)) hmem
      simp only [Finset.card_empty, zero_add, pow_one] at hsplit
      linarith
    have hfull : ∑ T ∈ A.powerset, (-1 : ℤ) ^ (T.card + 1) = 0 := by
      have h0 := alternating_sum_powerset A hA_nonempty
      have : ∑ T ∈ A.powerset, (-1 : ℤ) ^ (T.card + 1)
           = -1 * ∑ T ∈ A.powerset, (-1 : ℤ) ^ T.card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _; ring
      linarith [this.symm ▸ (show (-1 : ℤ) * 0 = 0 by ring) ▸ (h0 ▸ this)]
    have hempty_val : (-1 : ℤ) ^ ((∅ : Finset β).card + 1) = -1 := by simp
    linarith [Finset.add_sum_erase _ (fun T => (-1:ℤ)^(T.card+1)) hmem,
              hfull, hempty_val]
  exact h_alt.symm
