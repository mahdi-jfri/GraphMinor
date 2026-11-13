module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Pigeonhole
import GraphMinor.GM01.BinaryLeafCover
import Mathlib.Data.Set.Finite.List

/-!
# Choosing attachments on one covering path

In Graph Minors I, page 60, each attachment endpoint lies on at least
one of the binary leaf paths. Assign each endpoint to one such path.
The pigeonhole principle gives a path with at least `δ` assigned
endpoints. Select exactly `δ` of their indices. Overlap between the
covering paths causes no problem because each endpoint is assigned
only once.
-/

public section

namespace GraphMinor.GM01

/-- The pigeonhole selection of `J'` on page 60 of GM01, stated for
any finite cover so it also applies to paths with shared initial segments. -/
theorem exists_attachment_subset_on_cover_member {α ι I : Type*} [Fintype I] [Nonempty I]
    (J : Finset ι) (x : ι → α) (Q : I → Set α) {δ : ℕ}
    (hCover : ∀ j ∈ J, ∃ i, x j ∈ Q i)
    (hCard : Fintype.card I * δ ≤ J.card) :
    ∃ i : I, ∃ J' : Finset ι, J' ⊆ J ∧ J'.card = δ ∧ ∀ j ∈ J', x j ∈ Q i := by
  classical
  choose f hf using hCover
  let g : ι → I := fun j ↦ if hj : j ∈ J then f j hj else Classical.choice inferInstance
  obtain ⟨i, _, hi⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := J) (t := Finset.univ) (f := g) (fun _ _ ↦ Finset.mem_univ _) Finset.univ_nonempty
    (by simpa only [Finset.card_univ] using hCard)
  obtain ⟨J', hSub, hSize⟩ := Finset.exists_subset_card_eq hi
  refine ⟨i, J', ?_, hSize, ?_⟩
  · exact hSub.trans (Finset.filter_subset _ _)
  · intro j hj
    obtain ⟨hjJ, hgi⟩ := Finset.mem_filter.mp (hSub hj)
    have hEq : f j hjJ = i := by simpa only [g, dite_eq_left hjJ] using hgi
    exact hEq ▸ hf j hjJ


/-- With `δ * 2^γ` endpoints on the binary leaf cover, exactly `δ`
lie on one member, as required for `J'` on GM01 page 60. -/
theorem exists_attachment_subset_on_binary_leaf_cover {α ι : Type*} {γ δ : ℕ}
    (J : Finset ι) (x : ι → α)
    (Q : {leaf : List Bool // leaf.length = γ} → Set α)
    (hCover : ∀ j ∈ J, ∃ leaf, x j ∈ Q leaf)
    (hCard : J.card = δ * 2 ^ γ) :
    ∃ leaf, ∃ J' : Finset ι, J' ⊆ J ∧ J'.card = δ ∧ ∀ j ∈ J', x j ∈ Q leaf := by
  classical
  have hfin : {word : List Bool | word.length = γ}.Finite :=
    (List.finite_length_le Bool γ).subset (fun _ h ↦ h.le)
  let : Fintype {word : List Bool // word.length = γ} := hfin.fintype
  let : Nonempty {word : List Bool // word.length = γ} :=
    ⟨⟨List.replicate γ false, List.length_replicate⟩⟩
  have hCount : Fintype.card {word : List Bool // word.length = γ} = 2 ^ γ := by
    rw [← Nat.card_eq_fintype_card]
    change {word : List Bool | word.length = γ}.ncard = 2 ^ γ
    exact binaryTree_full_height_ncard γ
  apply exists_attachment_subset_on_cover_member J x Q hCover
  rw [hCount, hCard, Nat.mul_comm]

end GraphMinor.GM01
