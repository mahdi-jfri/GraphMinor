module

public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM01.PathCombs
public import GraphMinor.GM01.GraphManyPathsOrSeparator
import GraphMinor.GM01.BinarySubdivisionAttachmentContraction
import GraphMinor.GM01.CleanAttachmentIntersections
import GraphMinor.GM01.BinaryMinorModels

/-!
# The small cut for the chosen forest family

Apply (2.9) in the paragraph before (5.1), Graph Minors I, page 60,
to the actual root support and the connected other supports. In its
path alternative, reverse the paths and root each induced support at
its attachment endpoint. Clean interiors give the exact intersections.
The proved subdivision/leaf-cover contraction then gives the excluded
rooted comb. Hence the separator alternative holds with the printed
bound on the cut size plus the number of exceptional supports.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The application of (2.9) on GM01 page 60, from the actual chosen
subdivision supports. The clean-path alternative is contradicted by
the constructed rooted comb, rather than assumed to fail. -/
theorem exists_small_cut_for_rooted_forest_family {α β : Type*} {γ δ θ n : ℕ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hθ : 6 ≤ θ) (heven : Even θ)
    (G : RootedGraph α β) (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    (hGrid : ¬ IsIsoMinor (gridGraph θ) G.graph)
    (hNo : ¬ HasRootedMinor (rootedPathComb γ δ hδ) G)
    (F : RootedForestFamily G γ n)
    (hConn : ∀ i, GraphConnected (G.graph.induce (F.otherSet i)))
    {N R : Graph α β} (hNG : N ≤ G.graph)
    {c : (binaryTree γ).verts → α} (hc : Injective c)
    {P₀ : (binaryTree γ).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P₀ e))
    (hPaths : ∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P₀ e) (c a) (c b) ∧ V(P₀ e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (binaryTree γ).coe.edgeSet, e ≠ f → V(P₀ e) ∩ V(P₀ f) ⊆ range c)
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c ⟨[],binaryTree_root_mem γ⟩))
    (hMeet : V(R) ∩ V(N) = {c ⟨[],binaryTree_root_mem γ⟩})
    (hRootSet : F.rootSet = V(N) ∪ V(R)) :
    ∃ (X : Set α) (J : Set (Fin n)), X ⊆ V(G.graph) ∧
      X.ncard + J.ncard ≤ (2 ^ (θ ^ 4)) ^ (δ * 2 ^ γ) ∧
      ∀ j ∉ J, GraphSeparates G.graph X F.rootSet (F.otherSet j) := by
  classical
  rcases graph_many_paths_or_small_separator (r := δ * 2 ^ γ) hθ heven G.graph hVfin hGrid
    F.rootSet F.root_subset F.otherSet F.other_subset hConn F.other_disjoint with
    ⟨J,a,b,P,hJ,hP,hPP,hClean⟩ | hCut
  · exfalso
    obtain ⟨MRoot⟩ := F.root_minor
    let GRoot : RootedGraph α β := ⟨G.graph.induce F.rootSet,⟨G.root.val,F.root_mem⟩⟩
    let : Nonempty β := MRoot.binaryTree_nonempty_edge_labels hγ GRoot
    let : Fintype J := Fintype.ofFinite J
    let B : J → RootedGraph α β := fun j ↦
      ⟨G.graph.induce (F.otherSet j.val),⟨a j,(hP j).1⟩⟩
    have hBG : ∀ j, (B j).graph ≤ G.graph := fun j ↦ G.graph.induce_le (F.other_subset j.val)
    have hBC : ∀ j, GraphConnected (B j).graph := fun j ↦ hConn j.val
    have hMinor : ∀ j, IsIsoMinor (forestTreeGraph (γ - 1)) (B j).graph := fun j ↦ F.other_minor j.val
    have hDis : ∀ j, Disjoint F.rootSet V((B j).graph) := fun j ↦ F.root_disjoint j.val
    have hBD : Pairwise fun i j ↦ Disjoint V((B i).graph) V((B j).graph) := by
      intro i j hij
      exact F.other_disjoint (Subtype.val_injective.ne hij)
    have hPath : ∀ j, IsGraphPathWithEnds G.graph (P j) (b j) (B j).root.val :=
      fun j ↦ (hP j).2.2.symm
    have hClean' : ∀ j x, x ∈ V(P j) → x ≠ b j → x ≠ a j →
        x ∉ F.rootSet ∪ ⋃ i : J, V((B i).graph) := by
      intro j x hx hxb hxa hxTarget
      apply hClean j x hx hxa hxb
      rcases hxTarget with hxS | hxB
      · exact Or.inl hxS
      · obtain ⟨i,hxi⟩ := mem_iUnion.mp hxB
        exact Or.inr (mem_iUnion₂.mpr ⟨i.val,i.property,hxi⟩)
    obtain ⟨hPS,hSelf,hOther⟩ := attachment_intersections_of_clean_interiors
      F.rootSet (fun j ↦ (B j).graph) b a P (fun j ↦ (hP j).2.1)
      (fun j ↦ (hP j).1) hPath hDis hBD hClean'
    have hCard : Fintype.card J = δ * 2 ^ γ := by
      rw [← Nat.card_eq_fintype_card]
      change J.ncard = δ * 2 ^ γ
      exact hJ
    apply hNo
    apply rootedPathComb_of_many_binary_subdivision_attachments hγ hδ G hVfin hEfin
      hNG hc hV hPaths hInter hR hMeet B hBG hBC hMinor
      ?_ hBD b ?_ P hPath ?_ hSelf hOther hPP hCard
    · rw [← hRootSet]
      exact hDis
    · intro j
      rw [← hRootSet]
      exact (hP j).2.1
    · intro j
      rw [← hRootSet]
      exact hPS j
  · obtain ⟨X,J,hX,hSize,hSep⟩ := hCut
    refine ⟨X,J,hX,?_,hSep⟩
    rw [← Nat.pow_mul, Nat.mul_comm (θ ^ 4) (δ * 2 ^ γ)]
    exact hSize

end GraphMinor.GM01
