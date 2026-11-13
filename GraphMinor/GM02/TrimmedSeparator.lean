module

public import GraphMinor.GM02.SeparatorComponents
import GraphMinor.GM02.BalanceCut

/-!
# A balanced separator inside an endpoint bag

In the second case of II (2.5), the cut splits the graph into two separated
sides. Trim the heavier side inside the endpoint bag until their counts in
`Q` agree. The enlarged cut stays in that bag, and each remaining component
lies in one of the two equal sides.
-/

public section
namespace GraphMinor.GM02
open Graph Set
universe u v

/-- The final trimming argument of II (2.5), Case 2, page 313. -/
theorem exists_balanced_separator_in_bag {α : Type u} {β : Type v}
    {G : Graph α β} {Q A B W R : Set α} {w : ℕ}
    (hG : (V(G)).Finite) (hQG : Q ⊆ V(G))
    (hpart : W ∪ R = V(G) \ A) (hdis : Disjoint W R)
    (hsep : Separates G A W R) (hAB : A ⊆ B) (hBG : B ⊆ V(G))
    (hB : B.ncard ≤ w) (hBR : Disjoint B R)
    (hheavy : (R ∩ Q).ncard ≤ (W ∩ Q).ncard)
    (hmajority : (Q \ B).ncard < 2 * (R ∩ Q).ncard) :
    ∃ S ⊆ V(G), S.ncard ≤ w ∧
      ∀ a ∈ V(G) \ S,
        2 * (deletedComponent G S a ∩ Q).ncard ≤ (Q \ S).ncard := by
  have hQ := hG.subset hQG
  have hQpart : Q \ A = (W ∩ Q) ∪ (R ∩ Q) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ W ∪ R := by rw [hpart]; exact ⟨hQG hx.1, hx.2⟩
      exact hx'.elim (fun h => Or.inl ⟨h, hx.1⟩) (fun h => Or.inr ⟨h, hx.1⟩)
    · rintro (hx | hx)
      · have hx' : x ∈ V(G) \ A := by rw [← hpart]; exact Or.inl hx.1
        exact ⟨hx.2, hx'.2⟩
      · have hx' : x ∈ V(G) \ A := by rw [← hpart]; exact Or.inr hx.1
        exact ⟨hx.2, hx'.2⟩
  obtain ⟨Y, hYBA, hYWQ, hcounts, htotal⟩ :=
    exists_trim_balanced_halves hQ hQpart hdis hAB hBR hheavy hmajority
  have hSB : A ∪ Y ⊆ B := fun _ hx => hx.elim (fun h => hAB h) (fun h => (hYBA h).1)
  refine ⟨A ∪ Y, hSB.trans hBG, (Set.ncard_le_ncard hSB (hG.subset hBG)).trans hB, ?_⟩
  apply component_bound_of_separated_partition hQ (Y := W \ Y) (Y' := R)
  · intro a ha
    have ha' : a ∈ W ∪ R := by
      rw [hpart]
      exact ⟨ha.1, fun h => ha.2 (Or.inl h)⟩
    exact ha'.elim (fun h => Or.inl ⟨h, fun hy => ha.2 (Or.inr hy)⟩) Or.inr
  · intro a ha b hb haS hbS hp
    exact (hsep.mono_separator Set.subset_union_left) a ha.1 b hb haS hbS hp
  · rw [hcounts, htotal]
  · rw [htotal]

end GraphMinor.GM02
