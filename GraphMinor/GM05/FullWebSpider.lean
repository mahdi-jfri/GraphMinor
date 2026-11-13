module

public import GraphMinor.GM05.FullWebDefs
public import GraphMinor.GM05.Section4
import GraphMinor.GM05.Quoted
import GraphMinor.Minor.Basic

/-!
# Selecting a subweb with an actual spider

Use the same two cases of the auxiliary graph argument in V (4.4). In the
second case its spider support uses only the A paths and discarded B paths.
Delete the retained B edges from the actual host, then lift this support by
choosing one edge per shadow edge. The lift preserves valency one at leaves.
-/

public section
namespace GraphMinor.GM05.Full
open Graph Set SimpleGraph GM01
variable {α β : Type*}

/-- Paths in one vertex-disjoint family have disjoint actual edge sets. -/
theorem path_edges_disjoint {G : Graph α β} {P Q : Path α β}
    (hP : P.IsIn G) (hQ : Q.IsIn G) (hd : Disjoint P.verts Q.verts) :
    Disjoint P.edgeSet Q.edgeSet := by
  rw [Set.disjoint_left]
  intro e heP heQ
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heP
  obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet heQ
  have hG := hxy.mono hP
  have hG' := hab.mono hQ
  have hxP : x ∈ P.verts := P.vertexSet_eq ▸ hxy.left_mem
  have hxQ : x ∈ Q.verts := by
    rcases hG.left_eq_or_eq hG' with rfl | rfl
    · exact Q.vertexSet_eq ▸ hab.left_mem
    · exact Q.vertexSet_eq ▸ hab.right_mem
  exact Set.disjoint_left.mp hd hxP hxQ

/-- Graph Minors V, (4.4), pages 98–99, for paths with actual multigraph edges.
Select a `(p,q)`-subweb with a spider. The same correction `0 < p` as in
`GM05.theorem_4_4_simple` excludes the empty-host counterexample. -/
theorem theorem_4_4_proof {G : Graph α β} {θ p q : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) (hp : 0 < p)
    {A : Fin (p * 2 ^ (p * θ ^ 2)) → Path α β}
    {B : Fin (p + q + p * 2 ^ (p * θ ^ 2)) → Path α β} (hw : IsWeb G A B) :
    ∃ (embI : Fin p ↪ Fin (p * 2 ^ (p * θ ^ 2)))
      (embJ : Fin q ↪ Fin (p + q + p * 2 ^ (p * θ ^ 2))) (K : Graph α β),
      IsSpider G (fun i => A (embI i)) (fun j => B (embJ j)) K := by
  classical
  let As := fun i => (A i).seq
  let Bs := fun j => (B j).seq
  have hshadow : simpleShadow G ∈ 𝓕 θ :=
    fun hm => hno (hm.trans (simpleShadow_isIsoMinor G hV hE))
  by_cases hcase : ∀ a X, IsWalkConnectedIn (webAuxGraph As Bs) a X →
      (extNeigh (webAuxGraph As Bs) X).ncard < p
  · exact False.elim (GM05.theorem_4_4_case_1 hθ heven hV hshadow hp hw.vertexWeb hcase)
  push Not at hcase
  obtain ⟨a, X, hconn, hlarge⟩ := hcase
  obtain ⟨embI, embJ, C, _, hc, hleaf, hsupp⟩ :=
    spider_support_of_large_boundary hw.vertexWeb hconn hlarge
  let F : Set β := ⋃ j, (B (embJ j)).edgeSet
  let G' := G.deleteEdges F
  have hAfree : ∀ i, (A i).IsIn G' := by
    intro i
    refine ⟨(hw.isIn_left i).vertexSet_mono, fun e x y he => ?_⟩
    refine ⟨he.mono (hw.isIn_left i), ?_⟩
    intro heF
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp heF
    exact Set.disjoint_left.mp (hw.edge_disjoint i (embJ j)) he.edge_mem hj
  have hBfree : ∀ j, j ∉ Set.range embJ → (B j).IsIn G' := by
    intro j hj
    refine ⟨(hw.isIn_right j).vertexSet_mono, fun e x y he => ?_⟩
    refine ⟨he.mono (hw.isIn_right j), ?_⟩
    intro heF
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp heF
    have hne : j ≠ embJ k := fun h => hj ⟨k, h.symm⟩
    exact Set.disjoint_left.mp
      (path_edges_disjoint (hw.isIn_right j) (hw.isIn_right (embJ k))
        (hw.disjoint_right hne)) he.edge_mem hk
  have hCfree : C ≤ simpleShadow G' := by
    apply hsupp.trans
    exact sup_le (iSup_le fun i => Path.shadow_le (hAfree i))
      (iSup₂_le fun j hj => Path.shadow_le (hBfree j hj))
  obtain ⟨K, hK, hv, hKconn, hKleaf⟩ := exists_connected_lift_with_leaves hCfree hc
  refine ⟨embI, embJ, K, hK.trans Graph.deleteEdges_le, hKconn, ?_, ?_⟩
  · intro j
    rw [Set.disjoint_left]
    intro e heK heB
    have heG' : e ∈ E(G') := hK.edgeSet_mono heK
    exact heG'.2 (Set.mem_iUnion.mpr ⟨j, heB⟩)
  · intro i
    obtain ⟨x, hx, hl⟩ := hleaf i
    exact ⟨x, by rw [hv]; exact hx, hKleaf x hl⟩

end GraphMinor.GM05.Full
