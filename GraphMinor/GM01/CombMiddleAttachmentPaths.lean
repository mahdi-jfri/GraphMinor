module

public import GraphMinor.GM01.CombSecondEndAttachmentPaths
import GraphMinor.GM01.CombSegmentInclusions

/-!
# Disjoint paths through the two ends to the middle

Graph Minors I, (4.14), page 59, contracts the two ends independently.
The first path stays in the first three cells and the second path
stays in the last three. When the comb has at least six cells these
supports are disjoint. Each path meets the middle only at its chosen
spine centre and avoids the opposite end.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The two disjoint internal paths used to join the retained middle
in GM01 (4.14), page 59. -/
theorem exists_disjoint_paths_from_ends_to_middle {α β : Type*} {γ L : ℕ}
    (hL : 6 ≤ L) {D : Graph α β}
    (c : (pathComb γ L).verts → α) (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    {d₁ d₂ : α} (hd₁ : d₁ ∈ combFirstEndSupport (by omega) c P)
    (hd₂ : d₂ ∈ combSecondEndSupport (by omega) c P) :
    let a := c ⟨Sum.inl ⟨2, by omega⟩, pathComb_spine_mem γ L _⟩
    let b := c ⟨Sum.inl ⟨L - 3, by omega⟩, pathComb_spine_mem γ L _⟩
    let M := combSegmentSupport c P 2 (by omega : 2 + (L - 4) ≤ L)
    ∃ Q₁ Q₂ : Graph α β, IsGraphPathWithEnds D Q₁ d₁ a ∧
      IsGraphPathWithEnds D Q₂ d₂ b ∧ V(Q₁) ∩ M = {a} ∧ V(Q₂) ∩ M = {b} ∧
      Disjoint V(Q₁) V(Q₂) ∧ Disjoint V(Q₁) (combSecondEndSupport (by omega) c P) ∧
      Disjoint V(Q₂) (combFirstEndSupport (by omega) c P) := by
  have hcentres : ∀ v, c v ∈ V(D) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  obtain ⟨Q₁, hQ₁, hMeet₁, hSupp₁⟩ := exists_path_from_first_end_to_tail_with_support
    (by omega : 0 < L - 4) (by omega : 2 + (L - 4) ≤ L) c hc hcentres P hPaths hInter hd₁
  obtain ⟨Q₂, hQ₂, hMeet₂, hSupp₂⟩ := exists_path_from_second_end_to_middle
    (by omega : 5 ≤ L) c hc P hV hPaths hInter hd₂
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hDis := disjoint_combSegmentSupports hc P hRanges (fun e f hne ↦ (hInter e f hne).1)
    0 (L - 3) (by omega : 0 + 3 ≤ L) (by omega : L - 3 + 3 ≤ L) (by omega)
  have hFirst3 : combFirstEndSupport (by omega) c P ⊆
      combSegmentSupport c P 0 (by omega : 0 + 3 ≤ L) :=
    combSegmentSupport_mono c P 0 0 (by omega : 0 + 2 ≤ L) (by omega : 0 + 3 ≤ L) le_rfl (by omega)
  have hLast3 : combSecondEndSupport (by omega) c P ⊆
      combSegmentSupport c P (L - 3) (by omega : L - 3 + 3 ≤ L) :=
    combSegmentSupport_mono c P (L - 2) (L - 3) (by omega : L - 2 + 2 ≤ L)
      (by omega : L - 3 + 3 ≤ L) (by omega) (by omega)
  exact ⟨Q₁, Q₂, hQ₁, hQ₂, hMeet₁, hMeet₂, hDis.mono hSupp₁ hSupp₂,
    hDis.mono hSupp₁ hLast3, hDis.symm.mono hSupp₂ hFirst3⟩

end GraphMinor.GM01
