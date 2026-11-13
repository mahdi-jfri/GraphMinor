module

public import Mathlib.Data.Set.Card

/-!
# Trimming one side to equal halves

In Case 2 of II (2.5), let `W` be the heavier side of the endpoint-bag
cut. The strict majority on the opposite side says that fewer than its
`Q` vertices lie in `W` outside the bag. Remove exactly the surplus from
the `Q` vertices of `W` inside the bag. The two remaining sides then have
equal `Q` counts, each half of the remaining total.
-/

public section
namespace GraphMinor.GM02
open Set Classical

/-- The balancing step of II (2.5), Case 2, page 313. Here `A` is the cut,
`B` is its endpoint bag, and `R` is the opposite side. The removed set lies
inside the bag and outside the cut. -/
theorem exists_trim_balanced_halves {α : Type*} {Q A B W R : Set α}
    (hQ : Q.Finite) (hpart : Q \ A = (W ∩ Q) ∪ (R ∩ Q))
    (hdis : Disjoint W R) (hAB : A ⊆ B) (hBR : Disjoint B R)
    (hheavy : (R ∩ Q).ncard ≤ (W ∩ Q).ncard)
    (hmajority : (Q \ B).ncard < 2 * (R ∩ Q).ncard) :
    ∃ Y ⊆ B \ A, Y ⊆ W ∩ Q ∧
      ((W \ Y) ∩ Q).ncard = (R ∩ Q).ncard ∧
      (Q \ (A ∪ Y)).ncard = 2 * (R ∩ Q).ncard := by
  let L := W ∩ Q
  let R' := R ∩ Q
  change R'.ncard ≤ L.ncard at hheavy
  change (Q \ B).ncard < 2 * R'.ncard at hmajority
  have hLf : L.Finite := hQ.subset Set.inter_subset_right
  have hRf : R'.Finite := hQ.subset Set.inter_subset_right
  have hLR : Disjoint L R' := hdis.mono Set.inter_subset_left Set.inter_subset_left
  have hLA : ∀ x ∈ L, x ∉ A := by
    intro x hx
    have h : x ∈ Q \ A := by rw [hpart]; exact Or.inl hx
    exact h.2
  have hRA : ∀ x ∈ R', x ∉ A := by
    intro x hx
    have h : x ∈ Q \ A := by rw [hpart]; exact Or.inr hx
    exact h.2
  have hQB : Q \ B = (L \ B) ∪ R' := by
    ext x
    constructor
    · intro hx
      have hxA : x ∈ Q \ A := ⟨hx.1, fun h => hx.2 (hAB h)⟩
      rw [hpart] at hxA
      rcases hxA with hxL | hxR
      · exact Or.inl ⟨hxL, hx.2⟩
      · exact Or.inr hxR
    · rintro (⟨hxL, hxB⟩ | hxR)
      · exact ⟨hxL.2, hxB⟩
      · exact ⟨hxR.2, fun hxB => Set.disjoint_left.1 hBR hxB hxR.1⟩
  have hQBcount : (Q \ B).ncard = (L \ B).ncard + R'.ncard := by
    rw [hQB]
    exact Set.ncard_union_eq (hLR.mono Set.sdiff_subset (Subset.refl _)) hLf.sdiff hRf
  have hsplit : (L ∩ B).ncard + (L \ B).ncard = L.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard L B hLf
  have hneed : L.ncard - R'.ncard ≤ (L ∩ B).ncard := by omega
  obtain ⟨Y, hYD, hYcount⟩ := Set.exists_subset_card_eq hneed
  have hYL : Y ⊆ L := fun _ h => (hYD h).1
  have hYBA : Y ⊆ B \ A := fun x hx => ⟨(hYD hx).2, hLA x (hYL hx)⟩
  have htrim : ((W \ Y) ∩ Q) = L \ Y := by
    ext x
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩
  have hLcount : (L \ Y).ncard = R'.ncard := by
    rw [Set.ncard_sdiff' hYL hLf, hYcount]
    omega
  have hremaining : Q \ (A ∪ Y) = (L \ Y) ∪ R' := by
    ext x
    constructor
    · intro hx
      have hxA : x ∈ Q \ A := ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
      rw [hpart] at hxA
      rcases hxA with hxL | hxR
      · exact Or.inl ⟨hxL, fun h => hx.2 (Or.inr h)⟩
      · exact Or.inr hxR
    · rintro (hxL | hxR)
      · exact ⟨hxL.1.2, fun h => h.elim (hLA x hxL.1) hxL.2⟩
      · exact ⟨hxR.2, fun h => h.elim (hRA x hxR)
          (fun hxY => Set.disjoint_left.1 hLR (hYL hxY) hxR)⟩
  refine ⟨Y, hYBA, hYL, htrim ▸ hLcount, ?_⟩
  change (Q \ (A ∪ Y)).ncard = 2 * R'.ncard
  rw [hremaining, Set.ncard_union_eq (hLR.mono Set.sdiff_subset (Subset.refl _)) hLf.sdiff hRf,
    hLcount]
  omega

end GraphMinor.GM02
