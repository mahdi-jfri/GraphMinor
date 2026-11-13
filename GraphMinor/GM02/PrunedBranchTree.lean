module

public import GraphMinor.GM02.BranchSpanningTree
public import GraphMinor.GM02.TreeAttachmentHull
import GraphMinor.GM05.ExpansionConnected

/-!
# Actual branch trees retaining their attachment vertices

Choose a spanning tree of a connected branch, take the hull of its
attachments, and realize that smaller tree with original edges. The result
is a connected subgraph retaining all attachments, and its only leaves are
attachments. The isomorphism fixes the original vertex names.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- A connected finite branch has a tree subgraph containing any nonempty
set of attachments, with no other leaves. The returned isomorphism fixes
vertex names, so the attachment condition refers to the original vertices. -/
theorem exists_pruned_branch_tree {α : Type u} {β : Type v}
    (G : Graph α β) (hV : V(G).Finite) (hconn : GraphConnected G)
    (A : Set α) (hA : A.Nonempty) (hAG : A ⊆ V(G)) :
    ∃ S ⊆ V(G), A ⊆ S ∧ ∃ (T : SimpleGraph S) (K : Graph α β),
      T.IsTree ∧ K ≤ G ∧ V(K) = S ∧ GraphConnected K ∧
      (∃ φ : Iso (Graph.ofSimpleGraph T) K,
        ∀ x : V(Graph.ofSimpleGraph T), (φ.vertexEquiv x).val = x.val.val) ∧
      ∀ x : S, (T.neighborSet x).ncard = 1 → x.val ∈ A := by
  let : Fintype V(G) := hV.fintype
  obtain ⟨T, hTle, hT⟩ := (toSimpleGraph_connected_of_graphConnected hconn).exists_isTree_le
  let A' : Set V(G) := {x | x.val ∈ A}
  have hA' : A'.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨⟨a, hAG ha⟩, ha⟩
  let U := treeAttachmentHull T A'
  let S : Set α := Subtype.val '' U
  let e : U ≃ S := Equiv.Set.image Subtype.val U Subtype.val_injective
  have heval : ∀ y : U, (e y).val = y.val.val := fun y =>
    congrArg Subtype.val (Equiv.Set.image_apply Subtype.val U Subtype.val_injective y)
  let T₀ := T.induce U
  let T₁ := T₀.map e.toEmbedding
  have hS : S ⊆ V(G) := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hAS : A ⊆ S := by
    intro a ha
    exact ⟨⟨a, hAG ha⟩, subset_treeAttachmentHull T A' ha, rfl⟩
  have hT₀ : T₀.IsTree := isTree_induce_treeAttachmentHull hT hA'
  have hT₁ : T₁.IsTree := (SimpleGraph.Iso.map e T₀).isTree_iff.1 hT₀
  have hle : ∀ {a b : S}, T₁.Adj a b → G.Adj a.val b.val := by
    intro a b hab
    obtain ⟨x, y, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj e.toEmbedding T₀ a b).1 hab
    have hG : G.Adj x.val.val y.val.val := (hTle hxy).2
    change G.Adj (e x).val (e y).val
    rw [heval x, heval y]
    exact hG
  obtain ⟨K, hKG, hVK, φ, hφ⟩ := exists_subgraph_iso_of_simple_graph_on G S hS T₁ hle
  refine ⟨S, hS, hAS, T₁, K, hT₁, hKG, hVK,
    GM05.graphConnected_of_iso φ (graphConnected_ofSimpleGraph hT₁.connected), ⟨φ, hφ⟩, ?_⟩
  intro x hx
  let : Fintype S := (hV.subset hS).fintype
  let y : U := e.symm x
  have hdegx : T₁.degree x = 1 := by
    simpa only [SimpleGraph.ncard_neighborSet] using hx
  have hdegmap := SimpleGraph.degree_map_apply T₀ e.toEmbedding y
  have hdegy : T₀.degree y = 1 := by
    have hex : e.toEmbedding y = x := e.apply_symm_apply x
    rw [hex] at hdegmap
    exact hdegmap.symm.trans hdegx
  have hyA : y.val.val ∈ A := mem_attachments_of_degree_one_hull hT y hdegy
  have hxval : x.val = y.val.val := by
    calc
      x.val = (e y).val := congrArg Subtype.val (e.apply_symm_apply x).symm
      _ = y.val.val := heval y
  rw [hxval]
  exact hyA

end GraphMinor.GM02
