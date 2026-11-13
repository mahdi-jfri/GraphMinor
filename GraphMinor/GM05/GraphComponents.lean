module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM05.ExpansionDefs
public import GraphMinor.Minor.Model
import GraphMinor.GM06.Section3Basic
import GraphMinor.GM05.ExpansionBasic
import GraphMinor.GM05.ExpansionConnected
import GraphMinor.Minor.Basic

/-!
# Finite component families and expansions

Use the library's connected components of multigraphs. A finite graph has
finitely many components: choosing a vertex in each gives an injection
into its vertex set. Its components can therefore be enumerated by a
finite ordinal. An expansion of the graph contains an expansion of each
component. These are the component facts used in Graph Minors V, (8.8).
-/

public section

namespace GraphMinor.GM05

open Graph Set Surface GM06

/-- The walk and adjacency-chain definitions of connectivity agree. -/
theorem graphConnected_iff_isGraphConnected {α β : Type*} (G : Graph α β) :
    GraphConnected G ↔ IsGraphConnected G := by
  have of_walk : ∀ {x y}, GraphWalk G x y → Relation.ReflTransGen G.Adj x y := by
    intro x y W
    induction W with
    | nil _ => exact .refl
    | cons h W ih => exact (Relation.ReflTransGen.single ⟨_,h⟩).trans ih
  have to_walk : ∀ {x y}, x∈V(G) → Relation.ReflTransGen G.Adj x y → Nonempty (GraphWalk G x y) := by
    intro x y hx hr
    induction hr with
    | refl => exact ⟨.nil hx⟩
    | @tail y z hr hyz ih =>
      obtain ⟨W⟩ := ih
      obtain ⟨e,he⟩ := hyz
      exact ⟨W.append (.cons he (.nil he.right_mem))⟩
  exact ⟨fun h ↦ ⟨h.1,fun x hx y hy ↦ to_walk hx (h.2 x hx y hy)⟩,
    fun h ↦ ⟨h.1,fun x hx y hy ↦ (h.2 x hx y hy).elim of_walk⟩⟩

/-- A multigraph with finitely many vertices has finitely many connected
components, even if its ambient vertex and edge types are infinite. -/
theorem graphComponents_finite {α β : Type*} {H : Graph α β} (hV : V(H).Finite) :
    (graphComponents H).Finite := by
  classical
  let : Finite V(H) := hV.to_subtype
  have hex : ∀ C : graphComponents H, ∃ x : V(H), x.1∈V(C.1) := by
    intro C
    obtain ⟨x,hx⟩ := C.2.2.1.1
    exact ⟨⟨x,C.2.1.vertexSet_mono hx⟩,hx⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro C D he
    apply Subtype.ext
    apply C.2.eq_of_mem_mem D.2 (hf C)
    rw [he]
    exact hf D
  let : Finite (graphComponents H) := Finite.of_injective f hinj
  exact toFinite _

/-- Enumerate the connected components without repetition. -/
theorem exists_component_enumeration {α β : Type*} {H : Graph α β} (hV : V(H).Finite) :
    ∃ m : ℕ, ∃ C : Fin m → Graph α β, Function.Injective C ∧
      (∀ i,IsGraphComponent (C i) H) ∧ ∀ D,IsGraphComponent D H → ∃ i,C i=D := by
  classical
  let : Fintype (graphComponents H) := (graphComponents_finite hV).fintype
  let e := (Fintype.equivFin (graphComponents H)).symm
  refine ⟨Fintype.card (graphComponents H),fun i ↦ (e i).1,?_,fun i ↦ (e i).2,?_⟩
  · intro i j he
    exact e.injective (Subtype.ext he)
  · intro D hD
    obtain ⟨i,hi⟩ := e.surjective ⟨D,hD⟩
    exact ⟨i,congrArg Subtype.val hi⟩

/-- Every graph vertex belongs to a component. -/
theorem exists_component_of_vertex {α β : Type*} {H : Graph α β} {v : α} (hv : v∈V(H)) :
    ∃ C,IsGraphComponent C H ∧ v∈V(C) :=
  ⟨compOf H v,isGraphComponent_compOf hv,self_mem_reachSet hv⟩

/-- Every graph edge belongs to a component, including a loop. -/
theorem exists_component_of_edge {α β : Type*} {H : Graph α β} {e : β} (he : e∈E(H)) :
    ∃ C,IsGraphComponent C H ∧ e∈E(C) := by
  obtain ⟨u,v,huv⟩ := exists_isLink_of_mem_edgeSet he
  let C := compOf H u
  have hC : IsGraphComponent C H := isGraphComponent_compOf huv.left_mem
  have hu : u∈V(C) := self_mem_reachSet huv.left_mem
  exact ⟨C,hC,((hC.isLink_iff_of_mem hu).mpr huv).edge_mem⟩

/-- An expansion of a graph contains an expansion of each of its connected
components. The smaller expansion is connected. -/
theorem IsHExpansion.exists_component_expansion {α β α' β' : Type*}
    {H C : Graph α' β'} {G A : Graph α β} (hA : IsHExpansion H G A)
    (hC : IsGraphComponent C H) :
    ∃ B, IsHExpansion C G B ∧ V(B)⊆V(A) ∧ GraphConnected B := by
  have hCH : IsIsoMinor C H := by
    obtain ⟨K,hK,F,hF,hIso⟩ := IsIsoMinor.refl C
    exact ⟨K,hK.trans hC.1,F,hF,hIso⟩
  have hHA : IsIsoMinor H A := ⟨A,le_rfl,hA.2⟩
  have hm : IsIsoMinor C A := hCH.trans hHA
  obtain ⟨B,hB,F,hF,hIso⟩ := hm
  have hBG : IsHExpansion C G B := ⟨hB.trans hA.1,F,hF,hIso⟩
  exact ⟨B,hBG,hB.vertexSet_mono,hBG.graphConnected
    ((graphConnected_iff_isGraphConnected C).mpr hC.2.1)⟩

end GraphMinor.GM05
