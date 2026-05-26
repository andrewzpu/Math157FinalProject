# Proof Sketch for the Principle of Inclusion-Exclusion

## Goal

Let `s : Finset β` be a finite index set, and let `S : β → Finset α` be a finite family of subsets of a finite type `α`.

We want to prove

```text
card (s.biUnion S)
  = ∑ T ∈ (s.powerset.erase ∅), (-1)^(|T|+1) * card (T.inf S).
```

Informally, this says:

```text
|⋃_{b ∈ s} S_b|
  = ∑ |S_b|
    - ∑ |S_b ∩ S_c|
    + ∑ |S_b ∩ S_c ∩ S_d|
    - ···
```

where the sums range over all nonempty finite subsets `T` of the index set `s`.

## Definitions Behind the Formula

- `s.biUnion S` is the union of all sets `S b` with `b ∈ s`.
- `T.inf S` is the intersection of all sets `S b` with `b ∈ T`.
- `s.powerset.erase ∅` is the collection of all nonempty subsets `T ⊆ s`.

So the right-hand side adds the sizes of all single sets, subtracts all pairwise intersections, adds all triple intersections, and so on.

## Main Idea

Instead of counting sets directly, count how many times each element `x : α` contributes to the right-hand side.

There are two cases:

1. `x` is not in the union `s.biUnion S`.
2. `x` is in the union `s.biUnion S`.

We will show:

- if `x ∉ s.biUnion S`, then its total contribution to the alternating sum is `0`;
- if `x ∈ s.biUnion S`, then its total contribution is `1`.

Once that is proved, summing over all `x : α` gives the desired formula, since the left side counts exactly the elements in the union.

## Step 1: Rewrite Membership in the Union

Your lemma

```lean
mem_biUnion (x : α) (s : Finset β) (S : β → Finset α) :
  x ∈ s.biUnion S ↔ ∃ b ∈ s, x ∈ S b
```

shows that `x` lies in the union exactly when it belongs to at least one `S b` with `b ∈ s`.

For a fixed element `x`, define its index set:

```text
I_x = { b ∈ s : x ∈ S b }.
```

Then:

- `x ∈ s.biUnion S` iff `I_x` is nonempty.

This turns the union question into a finite combinatorics question about subsets of `I_x`.

## Step 2: Rewrite Membership in the Intersections

Your lemma

```lean
mem_inf_iff_forall (x : α) (T : Finset β) (S : β → Finset α) :
  x ∈ T.inf S ↔ ∀ b ∈ T, x ∈ S b
```

shows that `x` lies in the intersection over `T` exactly when `x` lies in every `S b` for `b ∈ T`.

Equivalently:

```text
x ∈ T.inf S  iff  T ⊆ I_x.
```

So for a fixed `x`, the subsets `T` that contribute on the right-hand side are exactly the nonempty subsets of `I_x`.

## Step 3: Compute the Contribution of a Fixed Element

Fix `x : α`. Its contribution to the right-hand side is

```text
∑_{∅ ≠ T ⊆ s} (-1)^(|T|+1) · 1_{x ∈ T.inf S}.
```

By the membership rewrite above, this becomes

```text
∑_{∅ ≠ T ⊆ I_x} (-1)^(|T|+1).
```

So everything reduces to evaluating an alternating sum over the powerset of `I_x`.

## Step 4: Alternating Sum Over a Nonempty Powerset

The key finite combinatorial identity is:

```text
∑_{T ⊆ A} (-1)^|T| = 0
```

for every nonempty finite set `A`.

Equivalently,

```text
1 + ∑_{∅ ≠ T ⊆ A} (-1)^|T| = 0,
```

so

```text
∑_{∅ ≠ T ⊆ A} (-1)^(|T|+1) = 1.
```

This is exactly the value we need when `A = I_x` is nonempty.

That is the purpose of the unfinished lemma:

```lean
alternating_sum_powerset ...
```

Its clean mathematical statement should be something like:

```text
If `A` is nonempty, then ∑_{T ⊆ A} (-1)^|T| = 0.
```

From that, removing the empty set term gives

```text
∑_{∅ ≠ T ⊆ A} (-1)^(|T|+1) = 1.
```

## Step 5: Finish the Two Cases

### Case 1: `x ∉ s.biUnion S`

Then `I_x = ∅`.

There are no nonempty subsets `T ⊆ I_x`, so the sum of contributions for `x` is `0`.

This matches the fact that `x` should contribute `0` to the cardinality of the union.

### Case 2: `x ∈ s.biUnion S`

Then `I_x` is nonempty.

The contribution of `x` becomes

```text
∑_{∅ ≠ T ⊆ I_x} (-1)^(|T|+1) = 1
```

by the alternating powerset identity.

So each element in the union contributes exactly `1`.

## Step 6: Sum Over All Elements

Now add the contribution over all `x : α`.

On the left, summing `1_{x ∈ s.biUnion S}` over `x : α` gives

```text
card (s.biUnion S).
```

On the right, summing over `x` and then over nonempty `T ⊆ s` gives

```text
∑_{∅ ≠ T ⊆ s} (-1)^(|T|+1) · card (T.inf S),
```

because `card (T.inf S)` counts exactly the number of elements lying in that intersection.

Since each `x` contributes the same amount to both sides, the two total sums are equal. This proves inclusion-exclusion.

## How This Matches the Lean Development

The current Lean file already contains most of the structural lemmas:

- `biUnion_insert`: lets you decompose unions inductively.
- `biUnion_empty`: base case for unions.
- `mem_biUnion`: rewrites union membership as an existential statement.
- `mem_inf_iff_forall`: rewrites intersection membership as a universal statement.
- `mem_powerset`: identifies powerset membership with subset inclusion.

The remaining Lean work is to formalize the counting argument above:

1. State the alternating powerset identity cleanly.
2. Prove it by induction on the finite set.
3. For each fixed `x`, rewrite the inclusion-exclusion sum in terms of the set `I_x`.
4. Show the contribution is `0` or `1` depending on whether `x` lies in the union.
5. Sum over all `x : α` to obtain the theorem.

## Suggested Intermediate Lemmas

A clean formal proof will likely go more smoothly if you add lemmas of the following form:

```text
1. x ∈ T.inf S  ↔  T ⊆ I_x
2. x ∈ s.biUnion S ↔ I_x.Nonempty
3. ∑_{T ⊆ A, T ≠ ∅} (-1)^(|T|+1) = 1   when A.Nonempty
4. ∑_{T ⊆ ∅, T ≠ ∅} (-1)^(|T|+1) = 0
```

These are not new mathematical ideas; they just package the proof into Lean-friendly chunks.

## Short Version

The proof works because every element `x` is counted:

- once if it belongs to at least one set, and
- zero times if it belongs to none.

The alternating signs exactly cancel the overcounting from pairwise, triple, and higher intersections.
