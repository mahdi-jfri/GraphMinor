module

public import GraphMinor.GM02.MinorWidth
public import GraphMinor.Planar.Defs
import GraphMinor.GM07.Section9Grid
import GraphMinor.GM10.Section7
import GraphMinor.GM10.TreeWidth

/-!
# A planar graph outside each bounded tree-width class

A grid has a tangle whose order is its side length, by X (7.3). X (5.2)
therefore bounds that side length by one plus its tree-width. Take a larger
grid and rename its vertices and edges to the types used by the recognition
program. The graph and its planar drawing are preserved by this renaming.
-/

public section

namespace GraphMinor.GM02

open Graph Set Function

/-- Renaming a graph with finite ambient vertex and edge types to the types
used by the recognition program preserves the graph up to an explicit
isomorphism. Vertices and edges are numbered independently. -/
theorem exists_numbered_iso {α β : Type} [Fintype α] [Fintype β] (G : Graph α β) :
    ∃ K : Graph ℕ (ℕ × ℕ × ℕ), Nonempty (Iso G K) := by
  classical
  let f : α → ℕ := fun a => (Fintype.equivFin α a).val
  let g : β → ℕ × ℕ × ℕ := fun e => ((Fintype.equivFin β e).val, 0, 0)
  have hf : Injective f := fun _ _ h => (Fintype.equivFin α).injective (Fin.ext h)
  have hg : Injective g := fun _ _ h => (Fintype.equivFin β).injective
    (Fin.ext (congrArg Prod.fst h))
  let K : Graph ℕ (ℕ × ℕ × ℕ) := {
    vertexSet := f '' V(G)
    edgeSet := g '' E(G)
    IsLink := fun e a b => ∃ e' a' b', G.IsLink e' a' b' ∧ g e' = e ∧ f a' = a ∧ f b' = b
    isLink_symm := by
      intro e _
      refine ⟨?_⟩
      rintro a b ⟨e', a', b', h, rfl, rfl, rfl⟩
      exact ⟨e', b', a', h.symm, rfl, rfl, rfl⟩
    eq_or_eq_of_isLink_of_isLink := by
      rintro e a b c d ⟨e', a', b', h, he, rfl, rfl⟩ ⟨e'', c', d', h', he', rfl, rfl⟩
      have heq : e' = e'' := hg (he.trans he'.symm)
      subst e''
      exact (h.left_eq_or_eq h').imp (congrArg f) (congrArg f)
    edge_mem_iff_exists_isLink := by
      intro e
      constructor
      · rintro ⟨e', he', rfl⟩
        obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he'
        exact ⟨f a, f b, e', a, b, hab, rfl, rfl, rfl⟩
      · rintro ⟨a, b, e', a', b', hab, rfl, _, _⟩
        exact ⟨e', hab.edge_mem, rfl⟩
    left_mem_of_isLink := by
      rintro e a b ⟨e', a', b', hab, _, rfl, _⟩
      exact ⟨a', hab.left_mem, rfl⟩ }
  refine ⟨K, ⟨{
    vertexEquiv := Equiv.Set.image f V(G) hf
    edgeEquiv := Equiv.Set.image g E(G) hg
    isLink_iff := ?_ }⟩⟩
  intro e a b
  constructor
  · intro hab
    exact ⟨e, a, b, hab, rfl, rfl, rfl⟩
  · rintro ⟨e', a', b', hab, he, ha, hb⟩
    have he' : e' = e := hg he
    have ha' : a' = a := hf ha
    have hb' : b' = b := hf hb
    simpa only [he', ha', hb'] using hab

/-- For each nonnegative width bound, there is a finite planar graph on the
recognition program's vertex and edge types that has no decomposition of
that width. The witness is a renamed grid of side length `w + 2`. -/
theorem exists_planar_not_treeWidthLE (w : ℕ) :
    ∃ H : Graph ℕ (ℕ × ℕ × ℕ), IsPlanar H ∧ ¬ TreeWidthLE H w := by
  classical
  let G := GM01.gridGraph (w + 2)
  have hPlanar : IsPlanar G := by
    have hS := (Surface.isSurface_model 0 0 0).1
    let : T2Space (Surface.SurfaceModel 0 0 0) := hS.2.1
    obtain ⟨Γ, _, φ, _, _, _, _⟩ :=
      GM07.exists_isGridDrawing (S := Surface.SurfaceModel 0 0 0)
        GM12.isSphere_model_zero (w + 2)
    exact IsPlanar.of_graphDrawing hS GM12.isSphere_model_zero ⟨Γ, φ⟩
  obtain ⟨H, ⟨φ⟩⟩ := exists_numbered_iso G
  have hHPlanar := IsPlanar.of_iso φ.symm hPlanar
  refine ⟨H, hHPlanar, ?_⟩
  intro hw
  have hGwidth : TreeWidthLE G w := hw.of_isIsoMinor hHPlanar.finite_V
    hHPlanar.finite_E (φ.isIsoMinor_left (IsIsoMinor.refl H))
  have hbound := (treeWidthLE_iff G hPlanar.finite_V hPlanar.finite_E w).1 hGwidth
  have htangle := GM10.theorem_7_3_proof (θ := w + 2) (by omega)
  have hlow := htangle.le_tangleNumber.trans (GM10.theorem_5_2_proof (GM10.gridHypergraph (w + 2))).1
  change w + 2 ≤ GM10.treeWidthPlusOne (Hypergraph.ofGraph G hPlanar.finite_V hPlanar.finite_E) at hlow
  omega

end GraphMinor.GM02
