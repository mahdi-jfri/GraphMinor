module

public import GraphMinor.GM01.CombSegmentModels
public import GraphMinor.GM01.SelectedBoundaryPath
import GraphMinor.GM01.CombSegmentInclusions
import GraphMinor.GM01.CombShiftRanges
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.GraphSeparators

/-!
# From an attachment in the first end to the retained tail

Graph Minors I, (4.10), page 58, contracts the first end of `D` and
keeps its remaining cells. A path inside the connected first end joins
the attachment to its last spine centre. The next replacing path joins
that centre to the first retained tail centre. The first end is
disjoint from the tail, and the boundary replacing path meets the tail
only at that centre. A path in their connected union therefore enters
the retained tail only at its root.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The clean path through the first end used in GM01 (4.10), page 58.
It meets the retained segment starting at cell two only at its root. -/
theorem exists_path_from_first_end_to_tail_with_support {α β : Type*} {γ L m : ℕ}
    (hm : 0 < m) (hbound : 2 + m ≤ L) {D : Graph α β}
    (c : (pathComb γ L).verts → α) (hc : Injective c) (hcentres : ∀ v, c v ∈ V(D))
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    {x : α} (hx : x ∈ combFirstEndSupport (by omega) c P) :
    ∃ Q : Graph α β, IsGraphPathWithEnds D Q x (rootedCombSegment hm D c P 2 hbound).root.val ∧
      V(Q) ∩ V((rootedCombSegment hm D c P 2 hbound).graph) =
        {(rootedCombSegment hm D c P 2 hbound).root.val} ∧
      V(Q) ⊆ combSegmentSupport c P 0 (by omega : 0 + 3 ≤ L) := by
  let f := combShiftEmbedding (γ := γ) 2 hbound
  let hf := fun {a b} (h : (pathComb γ m).coe.Adj a b) ↦ combShiftEmbedding_adj 2 hbound h
  let root := (rootedPathComb γ m hm).root
  let t := c (f root)
  let tail := combSegmentSupport c P 2 hbound
  let first := combFirstEndSupport (by omega : 2 ≤ L) c P
  let a : (pathComb γ L).verts := ⟨Sum.inl ⟨1, by omega⟩, pathComb_spine_mem γ L _⟩
  have hadj : (pathComb γ L).coe.Adj a (f root) := by
    apply pathComb_spine_adj (γ := γ)
    apply pathGraph_adj.mpr
    exact Or.inl (by change 1 + 1 = 2 + 0; omega)
  let e : (pathComb γ L).coe.edgeSet := ⟨s(a,f root), hadj⟩
  obtain ⟨a', b', he, hP, _⟩ := hPaths e
  have hPair : s(a,f root) = s(a',b') := he
  have hBoundary : IsGraphPathWithEnds D (P e) (c a) t := by
    rcases Sym2.eq_iff.mp hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hP
    · exact hP.symm
  have haOutside : a ∉ range f := by
    intro ha
    have h := (mem_range_combShiftEmbedding_iff 2 hbound a).mp ha
    change 2 ≤ 1 ∧ 1 < 2 + m at h
    omega
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hBoundaryMeet : V(P e) ∩ tail = {t} :=
    selected_subdivision_boundary_intersection f hf hc P hRanges
      (fun e f hne ↦ (hInter e f hne).1) root a haOutside e rfl
  have hdis : Disjoint first tail :=
    disjoint_combSegmentSupports hc P hRanges (fun e f hne ↦ (hInter e f hne).1)
      0 2 (by omega : 0 + 2 ≤ L) hbound (by omega)
  have hFirst := combSegment_model (by omega : 0 < 2) c hc hcentres P hPaths hInter
    0 (by omega : 0 + 2 ≤ L)
  have haFirst : c a ∈ first := by
    let v : (pathComb γ 2).verts := ⟨Sum.inl (1 : Fin 2), pathComb_spine_mem γ 2 _⟩
    exact Or.inl ⟨v, rfl⟩
  let K := subgraphUnion D (rootedCombSegment (by omega : 0 < 2) D c P 0 (by omega)).graph (P e)
  have hKconn : GraphConnected K := graphConnected_subgraphUnion hFirst.1 hBoundary.le
    hFirst.2.1 (graphConnected_of_isGraphPath hBoundary) ⟨c a, haFirst, hBoundary.left_mem⟩
  have hxK : x ∈ V(K) := Or.inl hx
  have htK : t ∈ V(K) := Or.inr hBoundary.right_mem
  obtain ⟨Q, hQ⟩ := exists_path_of_adj_reachable hxK (hKconn.2 x hxK t htK)
  have hKD : K ≤ D := subgraphUnion_le hFirst.1 hBoundary.le
  refine ⟨Q, hQ.mono hKD, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro y hy
      rcases hQ.le.vertexSet_mono hy.1 with hyFirst | hyP
      · exact False.elim (Set.disjoint_left.mp hdis hyFirst hy.2)
      · exact hBoundaryMeet ▸ ⟨hyP, hy.2⟩
    · intro y hy
      have hyt : y = t := hy
      subst y
      exact ⟨hQ.right_mem, Or.inl (mem_range_self root)⟩
  · intro y hy
    rcases hQ.le.vertexSet_mono hy with hyFirst | hyBoundary
    · exact combSegmentSupport_mono c P 0 0 (by omega : 0 + 2 ≤ L)
        (by omega : 0 + 3 ≤ L) le_rfl (by omega) hyFirst
    · exact path_subset_combSegmentSupport c P 0 (by omega : 0 + 3 ≤ L) e rfl
        ⟨Nat.zero_le _, by change 1 < 0 + 3; omega⟩
        ⟨Nat.zero_le _, by change 2 + 0 < 0 + 3; omega⟩ hyBoundary

/-- The clean path through the first end used in GM01 (4.10), page 58,
with the support bound omitted. -/
theorem exists_path_from_first_end_to_tail {α β : Type*} {γ L m : ℕ}
    (hm : 0 < m) (hbound : 2 + m ≤ L) {D : Graph α β}
    (c : (pathComb γ L).verts → α) (hc : Injective c) (hcentres : ∀ v, c v ∈ V(D))
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    {x : α} (hx : x ∈ combFirstEndSupport (by omega) c P) :
    ∃ Q : Graph α β, IsGraphPathWithEnds D Q x (rootedCombSegment hm D c P 2 hbound).root.val ∧
      V(Q) ∩ V((rootedCombSegment hm D c P 2 hbound).graph) =
        {(rootedCombSegment hm D c P 2 hbound).root.val} := by
  obtain ⟨Q, hQ, hMeet, _⟩ := exists_path_from_first_end_to_tail_with_support hm hbound c hc
    hcentres P hPaths hInter hx
  exact ⟨Q, hQ, hMeet⟩

end GraphMinor.GM01
