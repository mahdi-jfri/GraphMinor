module

public import GraphMinor.GM05.EdgeTransfer
import GraphMinor.GM01.Basic

/-!
# Choosing one actual edge for each edge of a simple subgraph

Choose edges only on the edge-set subtype, so no inhabited ambient edge
type is needed. Restrict the original graph to those edges and the given
vertices. The resulting subgraph has the prescribed shadow, no loops and
no parallel edges. In particular it preserves actual valency one at leaves.
-/

public section
namespace GraphMinor.GM05.Full
open Graph Set SimpleGraph GM01
variable {α β : Type*}

/-- Lift a simple subgraph by choosing one actual edge for every edge.
The lift has the same shadow and has no loops or parallel edges. -/
theorem exists_simple_subgraph_lift {G : Graph α β} {C : (⊤ : SimpleGraph α).Subgraph}
    (hle : C ≤ simpleShadow G) :
    ∃ K : Graph α β, K ≤ G ∧ simpleShadow K = C ∧
      (∀ e x, ¬ K.IsLink e x x) ∧
      (∀ e f x y, K.IsLink e x y → K.IsLink f x y → e = f) := by
  classical
  let H := toGraph C
  have hchoice : ∀ d : E(H), ∃ e : β,
      ∀ x y, H.IsLink d x y → G.IsLink e x y := by
    intro d
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet d.property
    obtain ⟨e, he⟩ := (hle.2 hxy.2).2
    refine ⟨e, fun a b hab => ?_⟩
    rcases hxy.eq_and_eq_or_eq_and_eq hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact he
    · exact he.symm
  choose f hf using hchoice
  let K := (G.restrict (range f)).induce C.verts
  have hKG : K ≤ G :=
    (Graph.induce_le (show C.verts ⊆ V(G.restrict (range f)) from hle.1)).trans
      Graph.restrict_le
  have hlink : ∀ e x y, K.IsLink e x y ↔
      ∃ d : E(H), e = f d ∧ H.IsLink d x y := by
    intro e x y
    constructor
    · rintro ⟨⟨⟨d, hd⟩, hxy⟩, _, _⟩
      refine ⟨d, hd.symm, ?_⟩
      obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet d.property
      have hG := hf d a b hab
      have hG' : G.IsLink (f d) x y := hd.symm ▸ hxy
      rcases hG.eq_and_eq_or_eq_and_eq hG' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    · rintro ⟨d, rfl, hxy⟩
      exact ⟨⟨mem_range_self d, hf d x y hxy⟩, hxy.left_mem, hxy.right_mem⟩
  have hshadow : simpleShadow K = C := by
    ext x y
    · rfl
    · constructor
      · rintro ⟨_, e, he⟩
        obtain ⟨d, _, hd⟩ := (hlink e x y).mp he
        exact hd.2
      · intro hxy
        let d : E(H) := ⟨s(x, y), (show H.IsLink s(x, y) x y from ⟨rfl, hxy⟩).edge_mem⟩
        exact ⟨C.adj_sub hxy, f d, (hlink _ _ _).mpr ⟨d, rfl, rfl, hxy⟩⟩
  refine ⟨K, hKG, hshadow, ?_, ?_⟩
  · intro e x he
    obtain ⟨d, _, hd⟩ := (hlink e x x).mp he
    exact C.loopless.irrefl x hd.2
  · intro e e' x y he he'
    obtain ⟨d, rfl, hd⟩ := (hlink e x y).mp he
    obtain ⟨d', rfl, hd'⟩ := (hlink e' x y).mp he'
    have hdd : d = d' := Subtype.ext (hd.1.trans hd'.1.symm)
    exact congrArg f hdd

/-- In a graph without loops or parallel edges, a leaf of the shadow has
actual valency one. -/
theorem isLeafOf_of_shadow {G : Graph α β} {x : α}
    (hnoloop : ∀ e x, ¬ G.IsLink e x x)
    (hsimple : ∀ e f x y, G.IsLink e x y → G.IsLink f x y → e = f)
    (h : GM01.IsLeafOf (simpleShadow G) x) : IsLeafOf G x := by
  obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp h.2
  have hxy : x ≠ y ∧ G.Adj x y := by
    change y ∈ (simpleShadow G).neighborSet x
    rw [hy]
    exact mem_singleton y
  obtain ⟨e, he⟩ := hxy.2
  refine ⟨e, y, hxy.1, he, fun f z hf => ?_⟩
  have hxz : x ≠ z := by
    rintro rfl
    exact hnoloop f x hf
  have hz : z = y := by
    have hzmem : z ∈ (simpleShadow G).neighborSet x := ⟨hxz, f, hf⟩
    rwa [hy, mem_singleton_iff] at hzmem
  subst z
  exact ⟨hsimple f e x y hf he, rfl⟩

/-- A connected simple subgraph with leaves lifts with the same vertices
and the same leaf vertices, using only actual edges of the host. -/
theorem exists_connected_lift_with_leaves {G : Graph α β}
    {C : (⊤ : SimpleGraph α).Subgraph} (hle : C ≤ simpleShadow G) (hc : C.Connected) :
    ∃ K : Graph α β, K ≤ G ∧ V(K) = C.verts ∧ GraphConnected K ∧
      ∀ x, GM01.IsLeafOf C x → IsLeafOf K x := by
  obtain ⟨K, hK, hshadow, hnoloop, hsimple⟩ := exists_simple_subgraph_lift hle
  refine ⟨K, hK, congrArg SimpleGraph.Subgraph.verts hshadow, ?_, ?_⟩
  · exact (graphConnected_iff_simpleShadow_connected K).mpr (hshadow.symm ▸ hc)
  · intro x hx
    exact isLeafOf_of_shadow hnoloop hsimple (hshadow.symm ▸ hx)

end GraphMinor.GM05.Full
