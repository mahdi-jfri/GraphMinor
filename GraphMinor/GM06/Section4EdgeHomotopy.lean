module

public import GraphMinor.GM06.Defs
public import Mathlib.Topology.Homotopy.Path
import GraphMinor.GM07.PushForest
import GraphMinor.GM11.Section4b

/-!
# Combining edge homotopies in a connected forest

The final proof of VI (4.2), page 126, says that a connected G′ would
permit Reduction 1. After taking a spanning tree, concatenate the
homotopic edge representatives along its walks. Any two curves with
the same ends in a forest are homotopic. Thus these representatives
compare every pair of path traces in the two forests, as required by
`ForestsHomotopic`.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Connected forests with matching boundary vertices are homotopic
when every edge of the first has a homotopic representative in the
second. The edge representatives are explicit paths, with their range
conditions, rather than a global homotopy assumption. -/
theorem forestsHomotopic_of_edge_representatives
    {S : Type} [TopologicalSpace S] [T2Space S] {F H : Drawing S}
    (hFp : F.IsProper) (hHp : H.IsProper)
    (hFf : IsGraphForest F.toGraph) (hHf : IsGraphForest H.toGraph)
    (hFc : IsGraphConnected F.toGraph) (hHc : IsGraphConnected H.toGraph)
    (hFVH : F.V ⊆ H.V) (hbd : F.V ∩ bd S = H.V ∩ bd S)
    (hedges : ∀ (e : Set S) (a b : S), F.toGraph.IsLink e a b →
      ∃ p q : Path a b, (∀ t, p t ∈ closure e) ∧ (∀ t, q t ∈ H.U) ∧ p.Homotopic q) :
    ForestsHomotopic F H := by
  classical
  have hone {e : Set S} {a b : S} (hl : F.toGraph.IsLink e a b) : GM07.PushJoined F H a b := by
    obtain ⟨p, q, hp, hq, hpq⟩ := hedges e a b hl
    obtain ⟨W⟩ := hHc.2 a (hFVH hl.left_mem) b (hFVH hl.right_mem)
    exact ⟨⟨.cons hl (.nil hl.right_mem)⟩, ⟨W⟩, p, q,
      fun t => F.closure_subset_U hl.1 (hp t), hq, hpq⟩
  have hjoined {a b : S} (W : GraphWalk F.toGraph a b) : GM07.PushJoined F H a b := by
    induction W with
    | nil ha => exact GM07.PushJoined.refl ha (hFVH ha)
    | cons hl r ih => exact (hone hl).trans ih
  refine ⟨hFp, hHp, hFf, hHf, hbd, ?_⟩
  intro s hs t ht hst
  have hFs : ∃ W : GraphWalk F.toGraph s t, W.IsSimple := by
    obtain ⟨W⟩ := hFc.2 s hs.1 t ht.1
    obtain ⟨W', hW', _, _⟩ := GM11.GraphWalk.exists_isSimple W
    exact ⟨W', hW'⟩
  have hHs : ∃ W : GraphWalk H.toGraph s t, W.IsSimple := by
    obtain ⟨W⟩ := hHc.2 s (hFVH hs.1) t (hFVH ht.1)
    obtain ⟨W', hW', _, _⟩ := GM11.GraphWalk.exists_isSimple W
    exact ⟨W', hW'⟩
  refine ⟨⟨fun _ => hHs, fun _ => hFs⟩, ?_⟩
  intro W₁ W₂ φ ψ _ _ hφ hψ
  obtain ⟨_, _, p, q, hp, hq, hpq⟩ := hjoined W₁
  let pφ : Path s t := ⟨φ, hφ.endpoints.1, hφ.endpoints.2⟩
  let pψ : Path s t := ⟨ψ, hψ.endpoints.1, hψ.endpoints.2⟩
  have hφp : pφ.Homotopic p := GM07.IsFlat.flat (GM07.isFlat_forest hFf) pφ p
    (fun u => hφ.range_subset_U (mem_range_self u)) hp
  have hqψ : q.Homotopic pψ := GM07.IsFlat.flat (GM07.isFlat_forest hHf) q pψ hq
    (fun u => hψ.range_subset_U (mem_range_self u))
  exact GM07.curves_of_homotopic (hφp.trans (hpq.trans hqψ))

end GraphMinor.GM06
