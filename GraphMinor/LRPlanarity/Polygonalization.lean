module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.PolygonalizationEdges

/-!
# Polygonalization of a finite plane drawing

Part IV, Section 7a of the planarity note chooses vertex discs, replaces
endpoint tails by radii, and samples the separated middle arcs. Simple paths
in the finite segment arrangements remove self-intersections. The edge-family
construction verifies that all replacements meet only at common original
vertices. This file assigns the same replacement to both orientations of an
edge and assembles the polygonal plane embedding with the original points.
-/

public section
namespace GraphMinor.LRPlanarity

open Set

/-- Part IV, Section 7a: every finite continuous plane drawing has a polygonal
plane drawing with exactly the same vertex points. -/
theorem polygonalizationStatement : PolygonalizationStatement := by
  intro N G drawing
  classical
  let E := {e : Fin N × Fin N // G.Adj e.1 e.2 ∧ e.1 < e.2}
  obtain ⟨L, hL, hcross, havoid⟩ := exists_polygonal_edge_family drawing
  let index : ∀ u v : Fin N, G.Adj u v → E := fun u v h =>
    if hlt : u < v then ⟨(u, v), h, hlt⟩
    else ⟨(v, u), h.symm, (lt_or_gt_of_ne (G.ne_of_adj h)).resolve_left hlt⟩
  have index_ends : ∀ u v h, (index u v h).val = (u, v) ∨ (index u v h).val = (v, u) := by
    intro u v h
    dsimp only [index]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have index_pair : ∀ u v h,
      s((index u v h).val.1, (index u v h).val.2) = s(u, v) := by
    intro u v h
    rcases index_ends u v h with he | he
    · simp only [he]
    · simp only [he, Sym2.eq_swap]
  have index_vertices : ∀ u v h,
      ({(index u v h).val.1, (index u v h).val.2} : Set (Fin N)) = {u, v} := by
    intro u v h
    rcases index_ends u v h with he | he
    · simp only [he]
    · simp only [he, pair_comm]
  have edge_ext : ∀ e f : E, s(e.val.1, e.val.2) = s(f.val.1, f.val.2) → e = f := by
    intro e f he
    rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Subtype.ext (Prod.ext h₁ h₂)
    · have hlt : f.val.2 < f.val.1 := by rw [← h₁, ← h₂]; exact e.property.2
      exact (lt_asymm hlt f.property.2).elim
  have index_comm : ∀ u v h, index u v h = index v u h.symm := by
    intro u v h
    apply edge_ext
    rw [index_pair u v h, index_pair v u h.symm]
    exact Sym2.eq_swap
  let line : Fin N → Fin N → Set ℂ := fun u v =>
    if h : G.Adj u v then L (index u v h) else ∅
  have line_edge : ∀ u v h, line u v = L (index u v h) := by
    intro u v h
    simp only [line, h, ↓reduceDIte]
  have line_comm : ∀ u v, line u v = line v u := by
    intro u v
    by_cases h : G.Adj u v
    · rw [line_edge u v h, line_edge v u h.symm, index_comm u v h]
    · have hrev : ¬ G.Adj v u := fun he => h he.symm
      simp only [line, h, hrev, ↓reduceDIte]
  let polygonal : HP25.PlaneEmbedding G univ := {
    pt := drawing.pt
    line := line
    finite := drawing.finite
    injOn := drawing.injOn
    line_comm := line_comm
    isLine := by
      intro u _ v _ huv
      rw [line_edge u v huv]
      have hl := (hL (index u v huv)).1
      rcases index_ends u v huv with he | he
      · simpa only [he] using hl
      · simpa only [he] using hl.symm
    inter := by
      intro u _ v _ u' _ v' _ huv huv' hne x hx
      rw [line_edge u v huv, line_edge u' v' huv'] at hx
      have hidx : index u v huv ≠ index u' v' huv' := by
        intro he
        apply hne
        exact (index_pair u v huv).symm.trans
          ((congrArg (fun e : E => s(e.val.1, e.val.2)) he).trans (index_pair u' v' huv'))
      have hm := hcross _ _ hidx hx
      rw [index_vertices u v huv, index_vertices u' v' huv'] at hm
      exact hm
    avoid := by
      intro u _ v _ huv w _ hw
      rw [line_edge u v huv] at hw
      have hm : w ∈ ({(index u v huv).val.1, (index u v huv).val.2} : Set (Fin N)) :=
        havoid _ _ hw
      rw [index_vertices u v huv] at hm
      exact hm
  }
  refine ⟨polygonal, ?_, rfl⟩
  intro u v huv
  change ∃ pieces : Finset (ℂ × ℂ), line u v = ⋃ p ∈ pieces, segment ℝ p.1 p.2
  rw [line_edge u v huv]
  exact (hL (index u v huv)).2

end GraphMinor.LRPlanarity
