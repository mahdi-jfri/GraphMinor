module

public import GraphMinor.GM01.GraphSeparators
public import GraphMinor.Hypergraph.Basic
public import Mathlib.Combinatorics.Graph.Simple
import GraphMinor.GM01.SimplificationConnected

/-!
# Separators and graph simplification

For Graph Minors I, (4.2), pages 55–56, apply Menger to the underlying
simple graph. A vertex set separates in the original graph exactly when
its preimage meets every simple-graph path between the corresponding
endpoint sets. Simple paths lift to original edges after deleting the
cut. Conversely, original reachability after deletion gives a simple
path whose vertices still avoid the cut, even when loop steps were
present in the original walk.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Relation

/-- The original-graph separator predicate equals the path-hitting
predicate on its underlying simple graph. This justifies Menger's
application in the multigraph form of GM01 (4.2). -/
theorem graphSeparates_iff_simple_paths {α β : Type*} (G : Graph α β) (X A B : Set α) :
    GraphSeparates G X A B ↔
      ∀ p : PathFromTo G.toSimpleGraph (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B),
        ∃ v ∈ p.walk.support, v.val ∈ X := by
  classical
  constructor
  · intro hsep p
    by_contra hmiss
    have hAvoid : ∀ v ∈ p.walk.support, v.val ∉ X := by
      intro v hv hvX
      exact hmiss ⟨v, hv, hvX⟩
    have lift : ∀ {u v : V(G)} (w : G.toSimpleGraph.Walk u v),
        (∀ z ∈ w.support, z.val ∉ X) → ReflTransGen (G.deleteVerts X).Adj u.val v.val := by
      intro u v w
      induction w with
      | nil => intro _; exact .refl
      | @cons u u' v hadj w ih =>
        intro havoid
        obtain ⟨e, he⟩ := hadj.2
        have hu := havoid u (Walk.start_mem_support (.cons hadj w))
        have hu' := havoid u' (List.mem_cons_of_mem _ w.start_mem_support)
        have hedge : (G.deleteVerts X).Adj u.val u'.val :=
          ⟨e, (G.deleteVerts_isLink X).mpr ⟨he, hu, hu'⟩⟩
        exact (ReflTransGen.single hedge).trans
          (ih (fun z hz ↦ havoid z (List.mem_cons_of_mem _ hz)))
    have hfirst : p.first.val ∈ V(G.deleteVerts X) := by
      rw [vertexSet_deleteVerts]
      exact ⟨p.first.property, hAvoid p.first p.walk.start_mem_support⟩
    have hlast : p.last.val ∈ V(G.deleteVerts X) := by
      rw [vertexSet_deleteVerts]
      exact ⟨p.last.property, hAvoid p.last p.walk.end_mem_support⟩
    exact hsep p.first.val p.first_mem p.last.val p.last_mem hfirst hlast (lift p.walk hAvoid)
  · intro hpaths a ha b hb haDel hbDel hr
    let H := G.deleteVerts X
    have haG : a ∈ V(G) := by rw [vertexSet_deleteVerts] at haDel; exact haDel.1
    have hbG : b ∈ V(G) := by rw [vertexSet_deleteVerts] at hbDel; exact hbDel.1
    let f : V(H) ↪ V(G) :=
      ⟨fun v ↦ ⟨v.val, Graph.deleteVerts_le.vertexSet_mono v.property⟩,
        fun _ _ h ↦ Subtype.ext (congrArg (fun v : V(G) ↦ v.val) h)⟩
    let hom : H.toSimpleGraph →g G.toSimpleGraph :=
      { toFun := f
        map_rel' := by
          intro u v huv
          obtain ⟨e, he⟩ := huv.2
          exact ⟨f.injective.ne huv.1, e, he.mono Graph.deleteVerts_le⟩ }
    obtain ⟨w⟩ := toSimpleGraph_reachable hr haDel hbDel
    let w' := w.map hom
    let p : PathFromTo G.toSimpleGraph (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B) :=
      ⟨f ⟨a, haDel⟩, f ⟨b, hbDel⟩, w'.bypass, w'.bypass_isPath, ha, hb⟩
    obtain ⟨v, hv, hvX⟩ := hpaths p
    have hvw : v ∈ w'.support := w'.support_bypass_subset_support hv
    rw [Walk.support_map, List.mem_map] at hvw
    obtain ⟨u, _, huv⟩ := hvw
    have hu : u.val ∈ V(G) \ X := (G.vertexSet_deleteVerts X) ▸ u.property
    have hval : u.val = v.val := congrArg (fun z : V(G) ↦ z.val) huv
    exact hu.2 (hval.symm ▸ hvX)

end GraphMinor.GM01
