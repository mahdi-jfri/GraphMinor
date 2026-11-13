module

public import GraphMinor.GM04.Painting
public import GraphMinor.GM16.FiniteLineGraphDrawing
public import GraphMinor.GM01.Basic
import GraphMinor.GM04.DiscPairingLines
import GraphMinor.Surface.ArcTools
import GraphMinor.GM04.Patchwork.Menger
import GraphMinor.GM14.DiscSlope
import GraphMinor.GM11.PaintingCells

/-!
# Drawing a subgraph of a painting realization

In IV (9.2), page 254, each edge of a spanning forest is drawn in a cell
whose pairing supplies that edge. Chords in the same cell are disjoint,
since a pairing has no shared ends and its pairs do not cross. Lines from
different cells meet only at nodes. The finite-line construction therefore
gives a drawing with each vertex represented by itself.
-/

public section

namespace GraphMinor.GM04

open Set Surface Graph

universe u w

/-- Distinct cells of an IV painting have closures meeting only at nodes. -/
theorem DiscPainting.closure_inter_subset_nodes {S : Type u} [TopologicalSpace S]
    (P : DiscPainting S) {e f : Set S} (he : e ∈ P.E) (hf : f ∈ P.E) (hne : e ≠ f) :
    closure e ∩ closure f ⊆ P.V := by
  rintro x ⟨hxe, hxf⟩
  by_contra hxN
  have hxE : x ∈ e := by
    by_contra h
    have hn : x ∈ closure e ∩ P.V := P.cell_complement e he ▸ ⟨hxe, h⟩
    exact hxN hn.2
  have hxF : x ∈ f := by
    by_contra h
    have hn : x ∈ closure f ∩ P.V := P.cell_complement f hf ▸ ⟨hxf, h⟩
    exact hxN hn.2
  exact hne (GM11.arcComponent_eq he hf hxE hxF)

/-- A subgraph of a realization of the noncrossing patches can be drawn
with its vertices fixed, using only the undeleted cells. This is the drawing
construction in the proof of IV (9.2), page 254. -/
theorem LabelledPainting.exists_drawing_of_realization_subgraph
    {Ω : Type w} {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (P : LabelledPainting Ω S) (Z : Set (Set S))
    {H : (⊤ : SimpleGraph S).Subgraph}
    (hH : (P.toPatchwork.deleteEdges Z).IsRealization H)
    (F : Graph S (Sym2 S)) (hF : F ≤ GM01.toGraph H) (hVF : V(F) = P.painting.V)
    (hEF : E(F).Finite) :
    ∃ Γ : GraphDrawing F S, Γ.drawing.V = P.painting.V ∧
      (∀ v : V(F), (Γ.iso.vertexEquiv v).val = v.val) ∧
      ∀ f ∈ Γ.drawing.E, ∃ e ∈ P.painting.E \ Z, f ⊆ e := by
  classical
  obtain ⟨δ, hδ, hHeq⟩ := hH
  have hδmem (e : Set S) (he : e ∈ P.painting.E \ Z) :
      IsPairing (P.toRootedHypergraph.ends e) (δ e) ∧
      (δ e).verts = P.toRootedHypergraph.ends e ∧
      ∀ a c b d, (δ e).Adj a c → (δ e).Adj b d →
        ¬ GM06.CrossesOn (subBd (closure e)) a c b d := hδ e he
  have hex (e : E(F)) : ∃ a b t, F.IsLink e a b ∧
      t ∈ P.painting.E \ Z ∧ (δ t).Adj a b := by
    obtain ⟨a, b, hab⟩ := F.exists_isLink_of_mem_edgeSet e.property
    have hAdj : H.Adj a b := (hab.mono hF).2
    rw [hHeq, realizationOf_adj] at hAdj
    obtain ⟨t, ht, htab⟩ := hAdj
    exact ⟨a, b, t, hab, ht, htab⟩
  choose a b cell hlink hcell hadj using hex
  have hnoloop (e : Sym2 S) (v : S) : ¬ F.IsLoopAt e v := by
    intro hv
    exact GM01.not_isLoopAt_toGraph H e v (hv.mono hF)
  have hab (e : E(F)) : a e ≠ b e := by
    intro h
    exact hnoloop e (b e) (h ▸ hlink e)
  have hδadj (e : E(F)) {x y : S} (hxy : F.IsLink e x y) : (δ (cell e)).Adj x y := by
    rcases (hlink e).isLink_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj e
    · exact (hadj e).symm
  have hbd (e : E(F)) {x : S} (hx : x ∈ (δ (cell e)).verts) :
      x ∈ discBd (closure (cell e)) := by
    rw [(hδmem _ (hcell e)).2.1, P.ends_eq (hcell e).1,
      ← P.painting.cell_complement _ (hcell e).1] at hx
    rw [← GM14.IsClosedDisc.subBd_eq_discBd hS (P.painting.edge_cond _ (hcell e).1).1]
    exact (P.painting.edge_cond _ (hcell e).1).2 hx
  have hend (e : E(F)) : a e ∈ discBd (closure (cell e)) ∧ b e ∈ discBd (closure (cell e)) :=
    ⟨hbd e ((δ (cell e)).edge_vert (hadj e)), hbd e ((δ (cell e)).edge_vert (hadj e).symm)⟩
  have hlines (t : P.painting.E) := exists_disc_pairing_lines (P.painting.edge_cond t t.property).1
  choose L hL hdis using hlines
  let A (e : E(F)) : Set S := L ⟨cell e, (hcell e).1⟩ (a e) (b e)
  have hA (e : E(F)) : IsLineWithEnds (A e) (a e) (b e) ∧
      A e ⊆ closure (cell e) ∧ A e ∩ discBd (closure (cell e)) = {a e, b e} :=
    hL _ _ (hend e).1 _ (hend e).2 (hab e)
  have hNode (e : E(F)) {x : S} (hx : x ∈ A e) (hxN : x ∈ P.painting.V) :
      x = a e ∨ x = b e := by
    have hxbd : x ∈ discBd (closure (cell e)) := by
      rw [← GM14.IsClosedDisc.subBd_eq_discBd hS (P.painting.edge_cond _ (hcell e).1).1]
      exact (P.painting.edge_cond _ (hcell e).1).2 ⟨(hA e).2.1 hx, hxN⟩
    have hxpair : x ∈ ({a e, b e} : Set S) := by
      rw [← (hA e).2.2]
      exact ⟨hx, hxbd⟩
    exact hxpair
  have hEndNe (e f : E(F)) (hne : e ≠ f) (hce : cell e = cell f)
      {x y z t : S} (hxy : F.IsLink e x y) (hzt : F.IsLink f z t) : x ≠ z := by
    intro hxz
    subst z
    have h1 := hδadj e hxy
    have h2 := hδadj f hzt
    rw [← hce] at h2
    have hfin : (P.toRootedHypergraph.ends (cell e)).Finite :=
      P.toRootedHypergraph.vertexSet_finite.subset (fun _ h ↦ P.toRootedHypergraph.vertex_mem_of_inc h)
    have hyt := ((isPairing_iff hfin).mp (hδmem _ (hcell e)).1).2 _ _ _ h1 h2
    apply hne
    apply Subtype.ext
    exact (hxy.mono hF).1.trans (hyt ▸ (hzt.mono hF).1.symm)
  have hMeet (e f : E(F)) (hne : e ≠ f) : A e ∩ A f ⊆ P.painting.V := by
    by_cases hce : cell e = cell f
    · have hnc := (hδmem _ (hcell e)).2.2 _ _ _ _ (hadj e) (by rw [hce]; exact hadj f)
      rw [GM14.IsClosedDisc.subBd_eq_discBd hS (P.painting.edge_cond _ (hcell e).1).1] at hnc
      have hfa : a f ∈ discBd (closure (cell e)) := by rw [hce]; exact (hend f).1
      have hfb : b f ∈ discBd (closure (cell e)) := by rw [hce]; exact (hend f).2
      have hzero := hdis ⟨cell e, (hcell e).1⟩ _ (hend e).1 _ (hend e).2
        _ hfa _ hfb (hab e) (hab f)
        (hEndNe e f hne hce (hlink e) (hlink f))
        (hEndNe e f hne hce (hlink e) (hlink f).symm)
        (hEndNe e f hne hce (hlink e).symm (hlink f))
        (hEndNe e f hne hce (hlink e).symm (hlink f).symm) hnc
      have hAf : A f = L ⟨cell e, (hcell e).1⟩ (a f) (b f) := by
        dsimp only [A]
        congr 1
        exact Subtype.ext hce.symm
      rw [← hAf] at hzero
      exact fun _ hx ↦ False.elim (Set.disjoint_left.mp hzero hx.1 hx.2)
    · exact fun _ hx ↦ P.painting.closure_inter_subset_nodes (hcell e).1 (hcell f).1 hce
        ⟨(hA e).2.1 hx.1, (hA f).2.1 hx.2⟩
  let lines (e : Sym2 S) : Set S := if he : e ∈ E(F) then A ⟨e, he⟩ else ∅
  have hLine : ∀ e ∈ E(F), ∀ x y, F.IsLink e x y → IsLineWithEnds (lines e) x y := by
    intro e he x y hxy
    simp only [lines, he, ↓reduceDIte]
    rcases (hlink ⟨e, he⟩).isLink_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hA _).1
    · exact (hA _).1.symm
  obtain ⟨Γ, hΓV, hΓid, hΓE⟩ := GM16.exists_graphDrawing_of_finite_lines F
    (hVF ▸ P.painting.finite_V) hEF id (Set.injOn_id _) lines hnoloop hLine
    (by
      intro e he v hv hvl
      have hvl' : v ∈ A ⟨e, he⟩ := by simpa only [lines, he, ↓reduceDIte, id_eq] using hvl
      rcases hNode ⟨e, he⟩ hvl' (hVF ▸ hv) with rfl | rfl
      · exact (hlink ⟨e, he⟩).inc_left
      · exact (hlink ⟨e, he⟩).inc_right)
    (by
      intro e he f hf hne
      simpa only [lines, he, hf, ↓reduceDIte, Set.image_id, hVF] using
        hMeet ⟨e, he⟩ ⟨f, hf⟩ (fun h ↦ hne (congrArg Subtype.val h)))
  have hΓV' : Γ.drawing.V = P.painting.V := by simpa only [Set.image_id, hVF] using hΓV
  refine ⟨Γ, hΓV', hΓid, ?_⟩
  intro f hf
  let e := Γ.iso.edgeEquiv.symm ⟨f, hf⟩
  refine ⟨cell e, hcell e, fun x hx ↦ ?_⟩
  have hxL : x ∈ A e := by
    have hcl := hΓE e
    rw [Γ.iso.edgeEquiv.apply_symm_apply] at hcl
    have hxcl : x ∈ closure f := subset_closure hx
    rw [hcl] at hxcl
    simpa only [lines, e.property, ↓reduceDIte] using hxcl
  have hxnot : x ∉ P.painting.V := by
    rw [← hΓV']
    exact (hf.2.1 hx).2
  by_contra hxcell
  have hn : x ∈ closure (cell e) ∩ P.painting.V :=
    P.painting.cell_complement _ (hcell e).1 ▸ ⟨(hA e).2.1 hxL, hxcell⟩
  exact hxnot hn.2

end GraphMinor.GM04
