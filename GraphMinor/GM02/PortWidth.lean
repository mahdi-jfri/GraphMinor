module

public import GraphMinor.GM02.PortGraph
import GraphMinor.GM02.IncidenceAugmentWidth
import GraphMinor.GM02.SplitWidth

/-!
# Width bound for the corrected split graph

Add an edge vertex in a leaf bag with its original ends, keeping the
old edges for this construction. The resulting augmentation has width
at most the larger of the host width and two. Delete the branch vertices
from the bags and put all split terminals in every bag. The corrected
split graph has no new adjacency between old augmentation vertices,
so these bags give width at most `max w 2 + 2k`.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The corrected split graph has width at most the host width or two, plus its number of terminals.
-/
theorem portGraph_treeWidthLE {α : Type u} {β : Type v} {k w : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hV : V(G).Finite) (hE : E(G).Finite) (hW : TreeWidthLE G w) :
    TreeWidthLE (portGraph G H choice) (max w 2 + 2 * k) := by
  let A := incidenceAugment G E(G)
  have hAV : V(A).Finite := (hV.image Sum.inl).union (hE.image Sum.inr)
  have hAW : TreeWidthLE A (max w 2) := incidenceAugment_treeWidthLE G w hW E(G) hE Set.Subset.rfl
  have hPV : V(portGraph G H choice) =
      Sum.inl '' (V(A) \ (Sum.inl '' V(H))) ∪ range Sum.inr := by
    ext a
    rcases a with (y | e) | p <;>
      simp [portGraph_vertexSet, portVertexSet, incidenceAugmentVertices, A,
        incidenceAugment, portOld, portEdge, portTerminal]
    intro _
    constructor
    · intro hy x hx hxy
      exact hy (hxy ▸ hx)
    · intro hy hym
      exact hy y hym rfl
  have hInc : ∀ e a, G.Inc e a → A.Adj (Sum.inl a) (Sum.inr e) := by
    intro e a hi
    refine ⟨s(Sum.inl a, Sum.inr e), ?_⟩
    apply (incidenceAugment_isLink_iff G E(G) _ _ _).2
    exact ⟨rfl, Or.inl ⟨a, hi.vertex_mem, rfl⟩, Or.inr ⟨e, hi.edge_mem, rfl⟩, hi.edge_mem, hi⟩
  have hOld : ∀ a b, (portGraph G H choice).Adj (Sum.inl a) (Sum.inl b) → A.Adj a b := by
    intro a b hab
    have hr := (portGraph_adj_iff G H choice _ _).1 hab |>.2.2
    rcases a with a | e <;> rcases b with b | f
    · exact hr.elim
    · exact hInc f a hr
    · exact (hInc e b hr).symm
    · exact hr.elim
  exact treeWidthLE_split_bound A (portGraph G H choice) (Sum.inl '' V(H)) hAV hPV hOld hAW

/-- The numerical width estimate used when (4.6) calls the terminated-graph algorithm. -/
theorem portGraph_treeWidth_le {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    treeWidth (portGraph G H choice) (portGraph_finite G H choice hV hE).1
      (portGraph_finite G H choice hV hE).2 ≤ max (treeWidth G hV hE) 2 + 2 * k := by
  apply (treeWidth_le_iff _ _ _ _).2
  exact portGraph_treeWidthLE G H choice hV hE ((treeWidth_le_iff G hV hE _).1 le_rfl)

end GraphMinor.GM02
