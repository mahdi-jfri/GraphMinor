module

import GraphMinor.GM13.Defs
import GraphMinor.GM13.Section10
import GraphMinor.GM13.ComputeBridge
import GraphMinor.GM14.Suppress

/-!
# Examples and sanity checks for Graph Minors XIII definitions

* The `0`-folio example on journal page 69 of Graph Minors XIII: let `G` be the digraph with four
  vertices `u, v₁, v₂, v₃` and three edges `uv₁, uv₂, uv₃`. For `i = 1, 2, 3` let `Nᵢ` be the
  edgeless digraph on `{1, …, i}`. We verify that `(N₁, 1, 1, 1)`, `(N₂, 1, 1, 2)`, and
  `(N₃, 1, 2, 3)` belong to the `0`-folio of `(G, v₁, v₂, v₃)`, and that `(N₁, 1, 1, 1)` does not
  belong to the `0`-folio of `(G \ {u}, v₁, v₂, v₃)`.
* An elementary wall of height `2`: we construct `wallHeight2 : Wall (ℕ × ℕ) (Sym2 (ℕ × ℕ))` and
  verify its height, four corners `(1, 0), (0, 2), (4, 2), (5, 0)`, and two middle vertices
  `(2, 1), (3, 1)`.
-/

namespace GraphMinor.GM13Examples

open Set Graph GraphMinor GraphMinor.Surface GraphMinor.GM13 GraphMinor.GM14

/-- The digraph `G` on page 69 with four vertices `0, 1, 2, 3 : Fin 4` (representing `u, v₁, v₂, v₃`)
and three edges `0, 1, 2 : Fin 3` with tail `0` and heads `1, 2, 3`. -/
def starDigraph : Digraph (Fin 4) (Fin 3) where
  vertexSet := univ
  edgeSet := univ
  tail _ := 0
  head e := ⟨e.val + 1, by omega⟩
  tail_mem _ _ := mem_univ _
  head_mem _ _ := mem_univ _

/-- The rooted digraph `(G, v₁, v₂, v₃)` from the page 69 example. -/
def starRooted : RootedDigraph (Fin 4) (Fin 3) 3 where
  digraph := starDigraph
  roots i := ⟨i.val + 1, by omega⟩
  roots_mem _ := mem_univ _

/-- For `n ≥ 1`, the edgeless digraph `N_n` on `ℕ` with vertex set `{1, …, n}` (Graph Minors XIII,
page 69: "For $i = 1, 2, 3$ let $N_i$ be the digraph with vertex set $\{1, \dots, i\}$ and no
edges."). -/
def edgelessDigraph (n : ℕ) : Digraph ℕ ℕ where
  vertexSet := Icc 1 n
  edgeSet := ∅
  head _ := 1
  tail _ := 1
  head_mem _ h := False.elim h
  tail_mem _ h := False.elim h

theorem edgelessDigraph_isFinite (n : ℕ) : (edgelessDigraph n).IsFinite :=
  ⟨finite_Icc 1 n, finite_empty⟩

/-- The rooted digraph `(N₁, 1, 1, 1)` from the page 69 example. -/
def rootedN1 : RootedDigraph ℕ ℕ 3 where
  digraph := edgelessDigraph 1
  roots _ := 1
  roots_mem _ := by simp [edgelessDigraph]

/-- The rooted digraph `(N₂, 1, 1, 2)` from the page 69 example. -/
def rootedN2_112 : RootedDigraph ℕ ℕ 3 where
  digraph := edgelessDigraph 2
  roots i := if i.val < 2 then 1 else 2
  roots_mem i := by fin_cases i <;> simp [edgelessDigraph]

/-- The rooted digraph `(N₃, 1, 2, 3)` from the page 69 example. -/
def rootedN3 : RootedDigraph ℕ ℕ 3 where
  digraph := edgelessDigraph 3
  roots i := i.val + 1
  roots_mem i := by fin_cases i <;> simp [edgelessDigraph]

/-- `starDigraph` is connected. -/
theorem starDigraph_isConnected : starDigraph.IsConnected := by
  refine ⟨⟨0, mem_univ 0⟩, ?_⟩
  intro x _ y _
  have h0 : ∀ z : Fin 4, Nonempty (GraphWalk starDigraph.toGraph 0 z) := by
    intro z
    fin_cases z
    · exact ⟨GraphWalk.nil (mem_univ 0)⟩
    · exact ⟨GraphWalk.cons (e := 0) (v := 1) ⟨mem_univ 0, Or.inr ⟨rfl, rfl⟩⟩
        (GraphWalk.nil (mem_univ 1))⟩
    · exact ⟨GraphWalk.cons (e := 1) (v := 2) ⟨mem_univ 1, Or.inr ⟨rfl, rfl⟩⟩
        (GraphWalk.nil (mem_univ 2))⟩
    · exact ⟨GraphWalk.cons (e := 2) (v := 3) ⟨mem_univ 2, Or.inr ⟨rfl, rfl⟩⟩
        (GraphWalk.nil (mem_univ 3))⟩
  rcases h0 x with ⟨wx⟩
  rcases h0 y with ⟨wy⟩
  exact ⟨wx.reverse.append wy⟩

/-- `(N₁, 1, 1, 1)` belongs to the `0`-folio of `(G, v₁, v₂, v₃)` (Graph Minors XIII, page 69). -/
theorem rootedN1_mem_starRooted_zeroFolio : rootedN1 ∈ starRooted.deltaFolio 0 := by
  refine ⟨⟨edgelessDigraph_isFinite 1, ?_⟩, ?_⟩
  · refine ⟨fun _ => starDigraph, fun _ => 0, ⟨{
      sub_of_mem := fun _ _ => ⟨subset_rfl, subset_rfl, fun _ _ => rfl, fun _ _ => rfl⟩
      connected_of_mem := fun _ _ => starDigraph_isConnected
      disjoint_of_ne := fun ⦃u v⦄ hu hv huv => by
        simp only [rootedN1, edgelessDigraph, mem_Icc] at hu hv
        omega
      edge_mem := fun _ h => False.elim h
      head_tail_mem := fun _ h => False.elim h
      loop_not_mem := fun _ h => False.elim h
      eMap_injOn := fun _ h => False.elim h
    }, fun _ => mem_univ _⟩⟩
  · have hdetail : rootedN1.detail = 0 := by
      unfold RootedDigraph.detail
      have h1 : rootedN1.digraph.edgeSet = ∅ := rfl
      have h2 : rootedN1.digraph.vertexSet \ range rootedN1.roots = ∅ := by
        ext x
        simp only [rootedN1, edgelessDigraph, mem_sdiff, mem_Icc, mem_range, not_exists,
          mem_empty_iff_false, iff_false, not_and]
        intro ⟨hx1, hx2⟩ hno
        have hx : x = 1 := by omega
        exact hno 0 hx.symm
      simp [h1, h2]
    omega

/-- `(N₂, 1, 1, 2)` belongs to the `0`-folio of `(G, v₁, v₂, v₃)` (Graph Minors XIII, page 69). -/
theorem rootedN2_112_mem_starRooted_zeroFolio : rootedN2_112 ∈ starRooted.deltaFolio 0 := by
  let branch1 : Digraph (Fin 4) (Fin 3) := starDigraph.induce ({0, 1, 2} : Set (Fin 4))
  let branch2 : Digraph (Fin 4) (Fin 3) := starDigraph.induce ({3} : Set (Fin 4))
  refine ⟨⟨edgelessDigraph_isFinite 2, ?_⟩, ?_⟩
  · refine ⟨fun u => if u = 1 then branch1 else branch2, fun _ => 0, ⟨{
      sub_of_mem := fun ⦃u⦄ _ => by
        by_cases hu : u = 1 <;> simp only [hu, ↓reduceIte, branch1, branch2, Digraph.induce] <;>
          exact ⟨inter_subset_left, sep_subset _ _, fun _ _ => rfl, fun _ _ => rfl⟩
      connected_of_mem := fun ⦃u⦄ _ => by
        by_cases hu1 : u = 1
        · subst hu1
          simp only [↓reduceIte]
          refine ⟨⟨0, mem_univ 0, by simp⟩, ?_⟩
          intro x hx y hy
          have h0 : ∀ z ∈ branch1.vertexSet, Nonempty (GraphWalk branch1.toGraph 0 z) := by
            intro z hz
            have h0_mem : (0 : Fin 4) ∈ V(branch1.toGraph) := ⟨mem_univ 0, by simp⟩
            have h1_mem : (1 : Fin 4) ∈ V(branch1.toGraph) := ⟨mem_univ 1, by simp⟩
            have h2_mem : (2 : Fin 4) ∈ V(branch1.toGraph) := ⟨mem_univ 2, by simp⟩
            rcases hz.2 with rfl | rfl | rfl
            · exact ⟨GraphWalk.nil h0_mem⟩
            · have hlk0 : branch1.toGraph.IsLink 0 0 1 :=
                ⟨⟨mem_univ 0, by simp [starDigraph]⟩, Or.inr ⟨rfl, rfl⟩⟩
              exact ⟨GraphWalk.cons hlk0 (GraphWalk.nil h1_mem)⟩
            · have hlk1 : branch1.toGraph.IsLink 1 0 2 :=
                ⟨⟨mem_univ 1, by simp [starDigraph]⟩, Or.inr ⟨rfl, rfl⟩⟩
              exact ⟨GraphWalk.cons hlk1 (GraphWalk.nil h2_mem)⟩
          rcases h0 x hx with ⟨wx⟩
          rcases h0 y hy with ⟨wy⟩
          exact ⟨wx.reverse.append wy⟩
        · simp only [hu1, ↓reduceIte]
          refine ⟨⟨3, mem_univ 3, rfl⟩, ?_⟩
          intro x hx y hy
          have hx3 : x = 3 := hx.2
          have hy3 : y = 3 := hy.2
          subst hx3 hy3
          exact ⟨GraphWalk.nil hx⟩
      disjoint_of_ne := fun ⦃u v⦄ hu hv huv => by
        simp only [rootedN2_112, edgelessDigraph, mem_Icc] at hu hv
        have : (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by omega
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [disjoint_iff_inter_eq_empty]
          ext x
          simp only [branch1, branch2, Digraph.induce, mem_inter_iff, mem_insert_iff,
            mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
          rintro ⟨_, rfl | rfl | rfl⟩ ⟨_, h⟩ <;> revert h <;> decide
        · rw [disjoint_iff_inter_eq_empty]
          ext x
          simp only [branch1, branch2, Digraph.induce, mem_inter_iff, mem_insert_iff,
            mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
          rintro ⟨_, rfl⟩ ⟨_, h | h | h⟩ <;> revert h <;> decide
      edge_mem := fun _ h => False.elim h
      head_tail_mem := fun _ h => False.elim h
      loop_not_mem := fun _ h => False.elim h
      eMap_injOn := fun _ h => False.elim h
    }, fun i => by
      fin_cases i <;> simp [starRooted, rootedN2_112, branch1, branch2, Digraph.induce, starDigraph]⟩⟩
  · have hdetail : rootedN2_112.detail = 0 := by
      unfold RootedDigraph.detail
      have h1 : rootedN2_112.digraph.edgeSet = ∅ := rfl
      have h2 : rootedN2_112.digraph.vertexSet \ range rootedN2_112.roots = ∅ := by
        ext x
        simp only [rootedN2_112, edgelessDigraph, mem_sdiff, mem_Icc, mem_range, not_exists,
          mem_empty_iff_false, iff_false, not_and]
        intro ⟨hx1, hx2⟩ hno
        have : x = 1 ∨ x = 2 := by omega
        rcases this with rfl | rfl
        · exact hno 0 rfl
        · exact hno 2 rfl
      simp [h1, h2]
    omega

/-- `(N₃, 1, 2, 3)` belongs to the `0`-folio of `(G, v₁, v₂, v₃)` (Graph Minors XIII, page 69). -/
theorem rootedN3_mem_starRooted_zeroFolio : rootedN3 ∈ starRooted.deltaFolio 0 := by
  let singleBranch (u : ℕ) : Digraph (Fin 4) (Fin 3) :=
    starDigraph.induce {x : Fin 4 | x.val = u}
  refine ⟨⟨edgelessDigraph_isFinite 3, ?_⟩, ?_⟩
  · refine ⟨singleBranch, fun _ => 0, ⟨{
      sub_of_mem := fun _ _ =>
        ⟨inter_subset_left, sep_subset _ _, fun _ _ => rfl, fun _ _ => rfl⟩
      connected_of_mem := fun ⦃u⦄ hu => by
        simp only [rootedN3, edgelessDigraph, mem_Icc] at hu
        have hu4 : u < 4 := by omega
        refine ⟨⟨⟨u, hu4⟩, mem_univ _, rfl⟩, ?_⟩
        intro x hx y hy
        have hxy : x = y := Fin.ext (hx.2.trans hy.2.symm)
        subst hxy
        exact ⟨GraphWalk.nil hx⟩
      disjoint_of_ne := fun ⦃u v⦄ _ _ huv => by
        rw [disjoint_iff_inter_eq_empty]
        ext x
        simp only [singleBranch, Digraph.induce, mem_inter_iff,
          mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        rintro ⟨_, rfl⟩ _ hxv
        exact huv hxv
      edge_mem := fun _ h => False.elim h
      head_tail_mem := fun _ h => False.elim h
      loop_not_mem := fun _ h => False.elim h
      eMap_injOn := fun _ h => False.elim h
    }, fun i => by fin_cases i <;> simp [starRooted, rootedN3, singleBranch, Digraph.induce, starDigraph]⟩⟩
  · have hdetail : rootedN3.detail = 0 := by
      unfold RootedDigraph.detail
      have h1 : rootedN3.digraph.edgeSet = ∅ := rfl
      have h2 : rootedN3.digraph.vertexSet \ range rootedN3.roots = ∅ := by
        ext x
        simp only [rootedN3, edgelessDigraph, mem_sdiff, mem_Icc, mem_range, not_exists,
          mem_empty_iff_false, iff_false, not_and]
        intro ⟨hx1, hx2⟩ hno
        have : x = 1 ∨ x = 2 ∨ x = 3 := by omega
        rcases this with rfl | rfl | rfl
        · exact hno 0 rfl
        · exact hno 1 rfl
        · exact hno 2 rfl
      simp [h1, h2]
    omega

/-- Deleting the center vertex `0` leaves an edgeless digraph, so `(N₁, 1, 1, 1)` is no longer in
the `0`-folio of `(G \ 0, v₁, v₂, v₃)`. -/
theorem rootedN1_not_mem_deleted_zeroFolio :
    let R' : RootedDigraph (Fin 4) (Fin 3) 3 := {
      digraph := starDigraph.deleteVertex 0
      roots := fun i => ⟨i.val + 1, by omega⟩
      roots_mem := fun i => ⟨mem_univ _, mem_univ _, by fin_cases i <;> simp⟩
    }
    rootedN1 ∉ R'.deltaFolio 0 := by
  intro R' ⟨⟨_, vMap, eMap, hM⟩, _⟩
  have h1 : (1 : Fin 4) ∈ (vMap 1).vertexSet := hM.root_mem 0
  have h2 : (2 : Fin 4) ∈ (vMap 1).vertexSet := hM.root_mem 1
  have hconn := (hM.connected_of_mem (by simp [rootedN1, edgelessDigraph])).2 1 h1 2 h2
  rcases hconn with ⟨w⟩
  cases w with
  | @cons _ _ _ e hlink _ =>
    have he : e ∈ (starDigraph.deleteVertex 0).edgeSet :=
      (hM.sub_of_mem (v := 1) (by simp [rootedN1, edgelessDigraph])).edgeSet_subset hlink.1
    exact he.2.2.2 rfl

/-- No edge of `elementaryWall h` is a loop. -/
theorem elementaryWall_no_loops (h : ℕ) (e : Sym2 (ℕ × ℕ)) (v : ℕ × ℕ) :
    ¬ (elementaryWall h).IsLink e v v := by
  rintro ⟨⟨_, _, hadj⟩, _⟩
  rcases hadj with ⟨_, h1 | h1⟩ | ⟨_, ⟨h1, _⟩ | ⟨h1, _⟩⟩ <;> omega

/-- Trivial subdivision paths of `elementaryWall h`. -/
noncomputable def elementaryWallSubdivPaths (h : ℕ) :
    Sym2 (ℕ × ℕ) → Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ)) :=
  Classical.choose (GM14.Whitney.isSubdivisionOf_self (elementaryWall_no_loops h)).2

/-- Every elementary wall of even height `h ≥ 2` is a `Wall` via the trivial subdivision. -/
noncomputable def wallOfElementary (h : ℕ) (h2 : 2 ≤ h) (heven : Even h) :
    Wall (ℕ × ℕ) (Sym2 (ℕ × ℕ)) where
  graph := elementaryWall h
  height := h
  two_le_height := h2
  even_height := heven
  baseGraph := elementaryWall h
  baseIso := {
    vertexEquiv := Equiv.refl _
    edgeEquiv := Equiv.refl _
    isLink_iff := fun _ _ _ => Iff.rfl
  }
  subdivisionPaths := elementaryWallSubdivPaths h
  base_verts_subset :=
    (GM14.Whitney.isSubdivisionOf_self (elementaryWall_no_loops h)).1
  path_of_edge :=
    (Classical.choose_spec (GM14.Whitney.isSubdivisionOf_self (elementaryWall_no_loops h)).2).1
  paths_disjoint :=
    (Classical.choose_spec (GM14.Whitney.isSubdivisionOf_self (elementaryWall_no_loops h)).2).2.1
  vertexSet_eq :=
    (Classical.choose_spec (GM14.Whitney.isSubdivisionOf_self (elementaryWall_no_loops h)).2).2.2.1
  edgeSet_eq :=
    (Classical.choose_spec (GM14.Whitney.isSubdivisionOf_self (elementaryWall_no_loops h)).2).2.2.2

/-- An elementary wall of height `2` as a `Wall`. -/
noncomputable def wallHeight2 : Wall (ℕ × ℕ) (Sym2 (ℕ × ℕ)) :=
  wallOfElementary 2 (by decide) ⟨1, rfl⟩

theorem wallHeight2_height : wallHeight2.height = 2 := by
  simp [wallHeight2, wallOfElementary]

theorem wallHeight2_corners :
    wallHeight2.corner 0 = (1, 0) ∧
    wallHeight2.corner 1 = (0, 2) ∧
    wallHeight2.corner 2 = (4, 2) ∧
    wallHeight2.corner 3 = (5, 0) := by
  dsimp [wallHeight2, wallOfElementary, Wall.corner, Wall.branchVertex,
    elementaryWallCorner, Equiv.refl]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem wallHeight2_middleVertices :
    wallHeight2.middleVertex₁ = (2, 1) ∧
    wallHeight2.middleVertex₂ = (3, 1) ∧
    wallHeight2.middleVertex₁ ≠ wallHeight2.middleVertex₂ := by
  dsimp [wallHeight2, wallOfElementary, Wall.middleVertex₁, Wall.middleVertex₂,
    Wall.branchVertex, elementaryWallMiddle₁, elementaryWallMiddle₂, Equiv.refl]
  exact ⟨rfl, rfl, by decide⟩

/-! ## Section 10 sanity checks: subwalls, attachment sequences, visions, and `𝒯_1` -/

theorem wallHeight2_isSubwallOf_self : wallHeight2.IsSubwallOf wallHeight2 :=
  Wall.IsSubwallOf.refl wallHeight2

theorem wallHeight2_subwallZero_isSubwallOf :
    (wallHeight2.subwallZero 2 (by decide) ⟨1, rfl⟩ (by simp [wallHeight2_height])).IsSubwallOf
      wallHeight2 :=
  wallHeight2.isSubwallOf_subwallZero 2 (by decide) ⟨1, rfl⟩ (by simp [wallHeight2_height])

theorem starRooted_mem_folioClassT1 :
    sigmaDeltaFolio 1 0 (by decide) starRooted ∈ folioClassT1 1 0 :=
  mem_folioClassT1_of_rootedDigraph 1 0 (by decide) starRooted

theorem isHomogeneousSubwall_empty_division
    (G : Digraph (ℕ × ℕ) (Sym2 (ℕ × ℕ)))
    (S_H : GM09.Society (ℕ × ℕ) (Sym2 (ℕ × ℕ)))
    (vis : Vision G ∅ wallHeight2 S_H ∅)
    (δ h : ℕ) :
    IsHomogeneousSubwall vis δ h wallHeight2 :=
  ⟨Wall.IsSubwallOf.refl wallHeight2, fun _ hInt => False.elim hInt.1⟩

/-! ## ComputeBridge sanity checks (`digraphOfSimpleGraph`) -/

theorem digraphOfSimpleGraph_top_fin3 :
    let G : SimpleGraph (Fin 3) := ⊤
    let D := digraphOfSimpleGraph G
    D.vertexSet.ncard = 3 ∧
    D.edgeSet.ncard = 3 ∧
    GM09.IsSimpleGraph D.toGraph ∧
    HasGraphModel (GM16.completeGraph 2) D.toGraph := by
  intro G D
  refine ⟨digraphOfSimpleGraph_vertexSet_ncard G, ?_, digraphOfSimpleGraph_isSimpleGraph G, ?_⟩
  · rw [digraphOfSimpleGraph_edgeSet_ncard]
    decide
  · exact digraphOfSimpleGraph_hasGraphModel_of_faithful_bound G (by decide) (by decide) (by decide)

end GraphMinor.GM13Examples
