module

public import GraphMinor.GM05.ExpansionDefs
public import GraphMinor.Minor.Model
import GraphMinor.GM05.CopyContractionClasses
import GraphMinor.GM05.ShadowMinor

/-!
# Expansions of connected graphs are connected

A contraction class is connected by the edges being contracted. Lift a
walk in the contracted graph by joining its successive original ends
inside these classes. Connectivity therefore lifts through contraction.
Graph isomorphisms preserve connectivity, so every expansion of a
connected graph is connected. This justifies the subtree families in
Graph Minors V, proof of (8.8), page 111.
-/

public section

namespace GraphMinor.GM05

open Graph Set Relation SimpleGraph

private lemma class_reachable {α β : Type*} {A : Graph α β} {C : Set β} {x y : α}
    (h : y∈contractionClass A C x) : ReflTransGen A.Adj x y := by
  exact ReflTransGen.mono (r:=fun x y ↦ ∃ e∈C,A.IsLink e x y) (p:=A.Adj)
    (fun _ _ ⟨e,_,he⟩ ↦ ⟨e,he⟩) x y h

private lemma class_eq_reachable {α β : Type*} {A : Graph α β} {C : Set β} {x y : α}
    (h : contractionClass A C x=contractionClass A C y) : ReflTransGen A.Adj x y :=
  class_reachable (h.symm ▸ mem_contractionClass_self A C y)

/-- Connectivity lifts through contraction because every contracted
vertex has a connected class of original vertices. -/
theorem graphConnected_of_contract {α β : Type*} {A : Graph α β} (C : Set β)
    (hconn : GraphConnected (contract A C)) : GraphConnected A := by
  have lift {x : α} {X Y : Set α} (hX : contractionClass A C x=X)
      (hr : ReflTransGen (contract A C).Adj X Y) :
      ∀ z, contractionClass A C z=Y → ReflTransGen A.Adj x z := by
    induction hr with
    | refl => exact fun z hz ↦ class_eq_reachable (hX.trans hz.symm)
    | @tail Y Z hr hYZ ih =>
      obtain ⟨e,he⟩ := hYZ
      obtain ⟨_,u,v,huv,huY,hvZ⟩ := (contract_link_iff A C e Y Z).mp he
      intro z hz
      exact ((ih u huY).tail ⟨e,huv⟩).trans (class_eq_reachable (hvZ.trans hz.symm))
  obtain ⟨X,hX⟩ := hconn.1
  obtain ⟨x,hx,_⟩ := hX
  refine ⟨⟨x,hx⟩,?_⟩
  intro a ha b hb
  have haC : contractionClass A C a∈V(contract A C) := ⟨a,ha,rfl⟩
  have hbC : contractionClass A C b∈V(contract A C) := ⟨b,hb,rfl⟩
  exact lift rfl (hconn.2 _ haC _ hbC) b rfl

/-- A graph isomorphism preserves connectivity, including loops and
parallel edges. -/
theorem graphConnected_of_iso {α β α' β' : Type*} {H : Graph α' β'} {G : Graph α β}
    (φ : Iso H G) (hH : GraphConnected H) : GraphConnected G := by
  have hadj (x y : V(H)) : H.Adj x.1 y.1 ↔
      G.Adj (φ.vertexEquiv x).1 (φ.vertexEquiv y).1 := by
    constructor
    · rintro ⟨e,he⟩
      exact ⟨(φ.edgeEquiv ⟨e,he.edge_mem⟩).1,(φ.isLink_iff ⟨e,he.edge_mem⟩ x y).mp he⟩
    · rintro ⟨e,he⟩
      let f := φ.edgeEquiv.symm ⟨e,he.edge_mem⟩
      have hf : G.IsLink (φ.edgeEquiv f) (φ.vertexEquiv x) (φ.vertexEquiv y) := by
        simpa [f] using he
      exact ⟨f.1,(φ.isLink_iff f x y).mpr hf⟩
  let ψ : (simpleShadow H).coe ≃g (simpleShadow G).coe := {
    toEquiv := φ.vertexEquiv
    map_rel_iff' := by
      intro x y
      change ((φ.vertexEquiv x).1≠(φ.vertexEquiv y).1 ∧
        G.Adj (φ.vertexEquiv x).1 (φ.vertexEquiv y).1) ↔ (x.1≠y.1 ∧ H.Adj x.1 y.1)
      apply and_congr _ (hadj x y).symm
      constructor
      · intro h he
        exact h (congrArg Subtype.val (congrArg φ.vertexEquiv (Subtype.ext he)))
      · intro h he
        exact h (congrArg Subtype.val (φ.vertexEquiv.injective (Subtype.ext he))) }
  have hshadow := (graphConnected_iff_simpleShadow_connected H).mp hH
  exact (graphConnected_iff_simpleShadow_connected G).mpr ⟨ψ.connected_iff.mp hshadow.coe⟩

/-- Graph Minors V, proof of (8.8), page 111: an expansion of a connected
component is connected. This follows by lifting connectivity through
its contraction witness. -/
theorem IsHExpansion.graphConnected {α β α' β' : Type*} {H : Graph α' β'}
    {G A : Graph α β} (hA : IsHExpansion H G A) (hH : GraphConnected H) :
    GraphConnected A := by
  obtain ⟨_,C,hC,⟨φ⟩⟩ := hA
  exact graphConnected_of_contract C (graphConnected_of_iso φ hH)

end GraphMinor.GM05
