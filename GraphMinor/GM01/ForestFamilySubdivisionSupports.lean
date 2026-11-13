module

public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM09.Basic
import GraphMinor.GM01.BinarySubdivision
import GraphMinor.GM01.ForestSubdivision

/-!
# Shrinking the chosen family to its subdivision supports

Graph Minors I, page 60, takes `X_i = V(B_i)` after choosing the
subdivisions. Extract the rooted binary subdivision and its root path
inside the old root set, and the three-branch subdivisions inside the
other sets. Their smaller vertex sets remain disjoint. The retained
minor models prove (X1) and (X2) again, so the family size is unchanged.
No maximality or path-cover conclusion is built into these data.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

private theorem le_induce_own_vertices {α β : Type*} {G K : Graph α β} (hKG : K ≤ G) :
    K ≤ G.induce V(K) :=
  ⟨Subset.rfl, fun _ _ _ he ↦ ⟨he.mono hKG, he.left_mem, he.right_mem⟩⟩

/-- The support restriction asserted on page 60 of GM01. The root
support is a binary subdivision and its separate root path. Every
other support is a three-branch-tree subdivision. Both minor
conditions and the number of sets are retained. -/
theorem exists_rooted_forest_family_subdivision_supports {α β : Type*} {G : RootedGraph α β}
    {γ N : ℕ} (hγ : 0 < γ) (F : RootedForestFamily G γ N)
    (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite) :
    ∃ F' : RootedForestFamily G γ N,
      F'.rootSet ⊆ F.rootSet ∧ (∀ i, F'.otherSet i ⊆ F.otherSet i) ∧
      (∃ (B : Graph α β) (c : (binaryTree γ).verts → α)
        (P : (binaryTree γ).coe.edgeSet → Graph α β) (R : Graph α β),
        B ≤ G.graph ∧ Injective c ∧ V(B) = range c ∪ ⋃ e, V(P e) ∧ E(B) = ⋃ e, E(P e) ∧
        (∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧ (binaryTree γ).coe.Adj a b ∧
          IsGraphPathWithEnds B (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b}) ∧
        (∀ e f : (binaryTree γ).coe.edgeSet, e ≠ f →
          Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c) ∧
        IsGraphPathWithEnds G.graph R G.root.val (c (binaryRootedTree γ).root) ∧
        V(R) ∩ V(B) = {c (binaryRootedTree γ).root} ∧ F'.rootSet = V(B) ∪ V(R)) ∧
      ∀ i : Fin N, ∃ (B : Graph α β) (c : (forestTree (γ - 1)).verts → α)
        (P : (forestTree (γ - 1)).coe.edgeSet → Graph α β),
        B ≤ G.graph ∧ Injective c ∧ V(B) = range c ∪ ⋃ e, V(P e) ∧ E(B) = ⋃ e, E(P e) ∧
        (∀ e : (forestTree (γ - 1)).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
          (forestTree (γ - 1)).coe.Adj a b ∧ IsGraphPathWithEnds B (P e) (c a) (c b) ∧
          V(P e) ∩ range c = {c a,c b}) ∧
        (∀ e f : (forestTree (γ - 1)).coe.edgeSet, e ≠ f →
          Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c) ∧
        GraphConnected B ∧ F'.otherSet i = V(B) := by
  classical
  let G₀ : RootedGraph α β := ⟨G.graph.induce F.rootSet, ⟨G.root.val, F.root_mem⟩⟩
  have hG₀G : G₀.graph ≤ G.graph := G.graph.induce_le F.root_subset
  obtain ⟨MRoot⟩ := F.root_minor
  let : Nonempty β := MRoot.binaryTree_nonempty_edge_labels hγ G₀
  obtain ⟨B₀, c₀, P₀, R, hB₀, hc₀, hV₀, hE₀, hPaths₀, hInter₀, hR, hMeet, _, _,
      hroot, ⟨M₀⟩⟩ := MRoot.binaryTree_subdivision hγ G₀
  let K₀ := subgraphUnion G₀.graph B₀ R
  have hK₀G₀ : K₀ ≤ G₀.graph := subgraphUnion_le hB₀ hR.le
  have hK₀G : K₀ ≤ G.graph := hK₀G₀.trans hG₀G
  have hRootSub : V(K₀) ⊆ F.rootSet := hK₀G₀.vertexSet_mono
  have hRootModel : HasRootedMinor (binaryRootedTree γ)
      (⟨G.graph.induce V(K₀), ⟨G.root.val, hroot⟩⟩ : RootedGraph α β) :=
    ⟨M₀.mono (le_induce_own_vertices hK₀G) rfl⟩
  have hChoices : ∀ i : Fin N, ∃ (B : Graph α β) (c : (forestTree (γ - 1)).verts → α)
      (P : (forestTree (γ - 1)).coe.edgeSet → Graph α β),
      B ≤ G.graph.induce (F.otherSet i) ∧ Injective c ∧
      V(B) = range c ∪ ⋃ e, V(P e) ∧ E(B) = ⋃ e, E(P e) ∧
      (∀ e : (forestTree (γ - 1)).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
        (forestTree (γ - 1)).coe.Adj a b ∧ IsGraphPathWithEnds B (P e) (c a) (c b) ∧
        V(P e) ∩ range c = {c a,c b}) ∧
      (∀ e f : (forestTree (γ - 1)).coe.edgeSet, e ≠ f →
        Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c) ∧
      GraphConnected B ∧ IsIsoMinor (forestTreeGraph (γ - 1)) B := by
    intro i
    have hGiG := G.graph.induce_le (F.other_subset i)
    exact exists_forestTree_subdivision (hVfin.subset hGiG.vertexSet_mono)
      (hEfin.subset hGiG.edgeSet_mono) (γ - 1) (F.other_minor i)
  choose B c P hB hc hV hE hPaths hInter hConn hMinor using hChoices
  have hBG : ∀ i, B i ≤ G.graph := fun i ↦ (hB i).trans (G.graph.induce_le (F.other_subset i))
  have hOtherSub : ∀ i, V(B i) ⊆ F.otherSet i := fun i ↦ (hB i).vertexSet_mono
  have hOtherModel : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1)) (G.graph.induce V(B i)) := by
    intro i
    obtain ⟨K, hKB, edges, hEdges, hIso⟩ := hMinor i
    exact ⟨K, hKB.trans (le_induce_own_vertices (hBG i)), edges, hEdges, hIso⟩
  let F' : RootedForestFamily G γ N :=
    { rootSet := V(K₀)
      otherSet := fun i ↦ V(B i)
      root_subset := hK₀G.vertexSet_mono
      other_subset := fun i ↦ (hBG i).vertexSet_mono
      other_disjoint := fun i j hij ↦ (F.other_disjoint hij).mono (hOtherSub i) (hOtherSub j)
      root_disjoint := fun i ↦ (F.root_disjoint i).mono hRootSub (hOtherSub i)
      root_mem := hroot
      root_minor := hRootModel
      other_minor := hOtherModel }
  refine ⟨F', hRootSub, hOtherSub, ?_, ?_⟩
  · exact ⟨B₀, c₀, P₀, R, hB₀.trans hG₀G, hc₀, hV₀, hE₀, hPaths₀, hInter₀,
      hR.mono hG₀G, hMeet, rfl⟩
  · intro i
    exact ⟨B i, c i, P i, hBG i, hc i, hV i, hE i, hPaths i, hInter i, hConn i, rfl⟩

end GraphMinor.GM01
