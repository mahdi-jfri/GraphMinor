module

public import GraphMinor.GM02.ValencyTwo
public import GraphMinor.GM02.SuppressMinorModel

/-!
# Suppressing an unmarked valency-two vertex of a model source

Keep the representing-edge ends and one vertex from each branch marked.
If all other edges lie within branches, an unmarked vertex of valency two
can be suppressed inside its branch. Its connection to the marked branch
vertex rules out a loop, and neither incident edge represents a target
edge. The suppressed source therefore retains the same minor model.
-/

public section
namespace GraphMinor.GM02
open Graph Set
universe u v u' v'

/-- Under the local branch conditions used for II (4.8), an unmarked
valency-two vertex has a suppression that preserves the minor model.
The replacement reuses the first erased edge name. -/
theorem exists_model_suppression_at_unmarked_vertex
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) (hE : E(G).Finite)
    (A : Set α)
    (hcover : ∀ x ∈ V(G), ∃ u ∈ V(H), x ∈ ηv u)
    (hroot : ∀ u ∈ V(H), ∃ r ∈ ηv u, r ∈ A)
    (hattach : ∀ e ∈ E(H), ∀ x, G.Inc (ηe e) x → x ∈ A)
    (hinternal : ∀ e ∈ E(G), e ∉ ηe '' E(H) →
      ∃ u ∈ V(H), ∀ x, G.Inc e x → x ∈ ηv u)
    {x : α} (hx : x ∈ V(G) \ A) (hval : valency G x = 2) :
    ∃ d : SuppressionData G,
      d.vertex = x ∧ d.fresh = d.first ∧
      d.first ∉ ηe '' E(H) ∧ d.second ∉ ηe '' E(H) ∧
      (∀ u ∈ V(H), d.vertex ∈ ηv u → d.left ∈ ηv u) ∧
      IsMinorModel H d.result (fun u => ηv u \ {d.vertex}) ηe := by
  obtain ⟨u, hu, hxu⟩ := hcover x hx.1
  obtain ⟨r, hr, hrA⟩ := hroot u hu
  obtain ⟨K, hK, hKv, hconn⟩ := hm.connected u hu
  have hxK : x ∈ V(K) := hKv ▸ hxu
  have hrK : r ∈ V(K) := hKv ▸ hr
  have hreachK := hconn.2 x hxK r hrK
  have hKG : K ≤ G := hK.trans Graph.deleteEdges_le
  have hreach : Relation.ReflTransGen G.Adj x r :=
    Relation.ReflTransGen.mono (fun _ _ hadj => Graph.Adj.mono hKG hadj) _ _ hreachK
  have hxr : x ≠ r := fun h => hx.2 (h ▸ hrA)
  have hloop := not_loop_of_valency_two_of_reachable_ne hE hval hreach hxr
  obtain ⟨d, hdx, hdf⟩ := exists_suppressionData_of_valency_two hval hloop
  have hfirst : d.first ∉ ηe '' E(H) := by
    rintro ⟨e, he, heq⟩
    have hinc : G.Inc (ηe e) x := by
      rw [heq, ← hdx]
      exact d.first_link.inc_left
    exact hx.2 (hattach e he x hinc)
  have hsecond : d.second ∉ ηe '' E(H) := by
    rintro ⟨e, he, heq⟩
    have hinc : G.Inc (ηe e) x := by
      rw [heq, ← hdx]
      exact d.second_link.inc_left
    exact hx.2 (hattach e he x hinc)
  have hsame : ∀ w ∈ V(H), d.vertex ∈ ηv w → d.left ∈ ηv w := by
    intro w hw hxw
    obtain ⟨z, hz, hends⟩ := hinternal d.first d.first_link.edge_mem hfirst
    have hxz := hends d.vertex d.first_link.inc_left
    have hwz : w = z := by
      by_contra hn
      exact Set.disjoint_left.1 (hm.vertex_disjoint w hw z hz hn) hxw hxz
    exact hwz ▸ hends d.left d.first_link.inc_right
  have hfresh : d.fresh ∉ ηe '' E(H) := hdf ▸ hfirst
  exact ⟨d, hdx, hdf, hfirst, hsecond, hsame,
    GraphMinor.GM02.IsMinorModel.suppress_of_same_branch hm d hfirst hsecond hfresh hsame⟩

end GraphMinor.GM02
