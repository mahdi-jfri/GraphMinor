module

public import GraphMinor.GM01.RootedModelSets

/-!
# Connectivity of lifted source sets

In the contraction argument for Graph Minors I, (4.1), page 55, a connected
source set is replaced by the union of its model branches. Paths inside
a branch remain in the union. Each source edge along a connecting path
has a represented target edge joining the corresponding branches. Joining
these paths and edges proves that the union induces a connected graph.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation

/-- A connected source set lifts to a connected union of branches.
The proof follows its source paths through the actual edge map. -/
theorem RootedMinorModel.liftSet_connected {α β γ δ : Type*}
    {H : RootedGraph α β} {G : RootedGraph γ δ} (M : RootedMinorModel H G)
    (S : Set α) (hS : S ⊆ V(H.graph)) (hconn : GraphConnected (H.graph.induce S)) :
    GraphConnected (G.graph.induce (M.liftSet S)) := by
  have inLift : ∀ (v : V(H.graph)), v.val ∈ S → M.branch v ⊆ M.liftSet S := by
    intro v hv x hx
    exact (M.mem_liftSet_iff S x).mpr ⟨v, hv, hx⟩
  have branch_paths : ∀ (v : V(H.graph)), v.val ∈ S → ∀ a ∈ M.branch v,
      ∀ b ∈ M.branch v, ReflTransGen (G.graph.induce (M.liftSet S)).Adj a b := by
    intro v hv a ha b hb
    apply ReflTransGen.mono ?_ a b ((M.branch_connected v).2 a ha b hb)
    intro x y hxy
    obtain ⟨e, he⟩ := hxy
    exact ⟨e, he.1, inLift v hv he.2.1, inLift v hv he.2.2⟩
  have lift : ∀ {u v : α}, ReflTransGen (H.graph.induce S).Adj u v →
      ∀ (hu : u ∈ V(H.graph)) (hv : v ∈ V(H.graph)), u ∈ S → v ∈ S →
      ∀ a ∈ M.branch ⟨u, hu⟩, ∀ b ∈ M.branch ⟨v, hv⟩,
        ReflTransGen (G.graph.induce (M.liftSet S)).Adj a b := by
    intro u v hr
    induction hr with
    | refl =>
      intro hu hv huS hvS a ha b hb
      exact branch_paths ⟨u, hu⟩ huS a ha b hb
    | @tail w v hr hstep ih =>
      intro hu hv huS hvS a ha b hb
      obtain ⟨edge, he⟩ := hstep
      let w' : V(H.graph) := ⟨w, he.1.left_mem⟩
      let v' : V(H.graph) := ⟨v, hv⟩
      let e : E(H.graph) := ⟨edge, he.1.edge_mem⟩
      obtain ⟨p, hp, q, hq, hpq⟩ := M.edge_links e w' v' he.1
      have hfirst := ih hu w'.property huS he.2.1 a ha p hp
      have hmid : (G.graph.induce (M.liftSet S)).Adj p q :=
        ⟨(M.edgeMap e).val, hpq, inLift w' he.2.1 hp, inLift v' hvS hq⟩
      exact hfirst.trans ((ReflTransGen.single hmid).trans (branch_paths v' hvS q hq b hb))
  obtain ⟨s, hs⟩ := hconn.1
  obtain ⟨a, ha⟩ := (M.branch_connected ⟨s, hS hs⟩).1
  refine ⟨⟨a, inLift ⟨s, hS hs⟩ hs ha⟩, ?_⟩
  intro x hx y hy
  obtain ⟨u, hu, hxu⟩ := (M.mem_liftSet_iff S x).mp hx
  obtain ⟨v, hv, hyv⟩ := (M.mem_liftSet_iff S y).mp hy
  exact lift (hconn.2 u.val hu v.val hv) u.property v.property hu hv x hxu y hyv

end GraphMinor.GM01
