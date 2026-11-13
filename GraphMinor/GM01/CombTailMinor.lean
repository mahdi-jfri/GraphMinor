module

public import GraphMinor.GM01.CombTailCentres
public import GraphMinor.GM01.CombShifts
public import GraphMinor.GM01.SubdivisionRestriction
import GraphMinor.GM01.PathsInRegions

/-!
# The comb minor in a tail region

The parenthetical assertion in the proof of Graph Minors I, (4.1),
page 55, retains a long comb in the last block. Shift its source vertices
onto a later spine interval. All its centres lie beyond the earlier cut,
and its replacing paths avoid that cut centre. Each selected path lies
in the region containing its ends. Restricting the subdivision to those
paths gives the claimed ordinary comb model in the induced tail region.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- A consecutive subcomb strictly after a spine cut has an ordinary
minor model in the induced tail region. This proves the long-tail minor
construction used in Graph Minors I, (4.1), page 55. -/
theorem comb_tail_minor_model {α β : Type*} [Nonempty β] {γ δ m : ℕ}
    {N : Graph α β} {c : (pathComb γ δ).verts → α} (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(N))
    (P : (pathComb γ δ).coe.edgeSet → Graph α β)
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e e' : (pathComb γ δ).coe.edgeSet, e ≠ e' →
      V(P e) ∩ V(P e') ⊆ range c ∧ Disjoint E(P e) E(P e'))
    (i : Fin δ) (offset : ℕ) (hio : i.val < offset) (hbound : offset + m ≤ δ) :
    ∃ (ηv : (pathComb γ m).verts → Set α) (ηe : Sym2 (pathComb γ m).verts → β),
      IsMinorModel (Graph.ofSimpleGraph (pathComb γ m).coe)
        (N.induce (vertexAvoidanceRegion N
          (c ⟨Sum.inl ⟨δ - 1, by omega⟩, pathComb_spine_mem γ δ _⟩)
          (c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩))) ηv ηe := by
  let : Finite (pathComb γ m).verts := (pathComb_vertices_finite γ m).to_subtype
  let f := combShiftEmbedding (γ := γ) offset hbound
  have hf : ∀ {a b : (pathComb γ m).verts}, (pathComb γ m).coe.Adj a b →
      (pathComb γ δ).coe.Adj (f a) (f b) := combShiftEmbedding_adj offset hbound
  let mapEdge := subdivisionEmbeddingEdges f hf
  let D := vertexAvoidanceRegion N
    (c ⟨Sum.inl ⟨δ - 1, by omega⟩, pathComb_spine_mem γ δ _⟩)
    (c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩)
  let r : (pathComb γ δ).verts := ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩
  have hIndex : ∀ v : (pathComb γ m).verts,
      (pathCombSpineIndex (f v).val).val = offset + (pathCombSpineIndex v.val).val := by
    rintro ⟨v, hv⟩
    cases v <;> rfl
  have hLater : ∀ v : (pathComb γ m).verts, i.val < (pathCombSpineIndex (f v).val).val := by
    intro v
    rw [hIndex]
    omega
  have hcentreD : ∀ v, c (f v) ∈ D := fun v ↦
    comb_subdivision_later_vertex_mem_region hc hcentres hPaths i (f v) (hLater v)
  have hneq : ∀ v : (pathComb γ m).verts, r ≠ f v := by
    intro v heq
    have hval := congrArg (fun z : (pathComb γ δ).verts ↦
      (pathCombSpineIndex z.val).val) heq
    change i.val = (pathCombSpineIndex (f v).val).val at hval
    have hlt := hLater v
    omega
  have hD : ∀ e : (pathComb γ m).coe.edgeSet, V(P (mapEdge e)) ⊆ D := by
    intro e
    obtain ⟨edge, he⟩ := e
    induction edge using Sym2.inductionOn with
    | hf a b =>
      let e : (pathComb γ m).coe.edgeSet := ⟨s(a,b), he⟩
      have hmap : (mapEdge e).val = s(f a,f b) := subdivisionEmbeddingEdges_ends f hf rfl
      obtain ⟨a', b', he', hP, hRange⟩ := hPaths (mapEdge e)
      have hpair : s(f a,f b) = s(a',b') := hmap.symm.trans he'
      have hPab : IsGraphPathWithEnds N (P (mapEdge e)) (c (f a)) (c (f b)) := by
        rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hP
        · exact hP.symm
      have hcut : c r ∉ V(P (mapEdge e)) := by
        intro hm
        have hmem := (subdivision_centre_mem_path_iff hc (fun e ↦ by
          obtain ⟨a, b, he, _, hR⟩ := hPaths e
          exact ⟨a, b, he, hR⟩) (mapEdge e) r).mp hm
        rw [hmap, Sym2.mem_iff] at hmem
        exact hmem.elim (hneq a) (hneq b)
      exact path_subset_vertexAvoidanceRegion hPab (hcentreD a) hcut
  exact exists_minorModel_of_subdivision_restriction f hf c hc D
    (fun v ↦ ⟨hcentres (f v), hcentreD v⟩) P hPaths hInter hD

end GraphMinor.GM01
