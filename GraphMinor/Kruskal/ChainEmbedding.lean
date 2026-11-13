module

public import GraphMinor.Kruskal.ChainSequence
public import GraphMinor.Kruskal.InitialChains
import GraphMinor.Minor.Basic

/-!
# From an embedded edge-chain graph to topological containment

The chain sequence starts at an isomorphic copy of the source graph. Injective
maps of the chain vertices and edges into a target, preserving links, give an
isomorphic subgraph of that target. Transporting the sequence through these
isomorphisms proves topological containment in its exact interface form.
-/

public section

namespace GraphMinor.Kruskal

open Graph Set

/-- An injective, link-preserving image of the chain graph witnesses
topological containment. Vertex membership is required even for isolated
vertices. Maps are defined only on actual vertices and edges. -/
theorem isTopologicalMinor_of_chainEmbedding {α β γ δ : Type*}
    (H : Graph α β) (G : Graph γ δ) (hV : V(H).Finite) (hE : E(H).Finite)
    (left right : E(H) → V(H))
    (hends : ∀ e : E(H), H.IsLink e.val (left e).val (right e).val)
    (n : E(H) → ℕ)
    (vertices : V(edgeChains left right n) ↪ γ)
    (edges : E(edgeChains left right n) ↪ δ)
    (hvertices : ∀ x, vertices x ∈ V(G))
    (hlinks : ∀ (d : E(edgeChains left right n)) (x y : V(edgeChains left right n)),
      (edgeChains left right n).IsLink d.val x.val y.val →
        G.IsLink (edges d) (vertices x) (vertices y)) :
    GM04.IsTopologicalMinor H G := by
  classical
  let := hV.fintype
  let := hE.fintype
  let C := edgeChains left right n
  let K := renameGraph C vertices edges
  have hKG : K ≤ G := by
    constructor
    · rintro x ⟨a, rfl⟩
      exact hvertices a
    · rintro d x y ⟨e, a, b, h, rfl, rfl, rfl⟩
      exact hlinks e a b h
  have hchain := edgeChains_isTopologicalMinor left right n
  have hHC : GM04.IsTopologicalMinor H C :=
    isTopologicalMinor_iso_source (initialChainsIso H left right hends) hchain
  have hHK : GM04.IsTopologicalMinor H K :=
    isTopologicalMinor_iso_target (renameGraphIso C vertices edges) hHC
  exact isTopologicalMinor_mono_target hKG hHK

end GraphMinor.Kruskal
