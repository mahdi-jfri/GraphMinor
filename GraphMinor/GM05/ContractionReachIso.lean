module

public import GraphMinor.GM05.CopyContractionClasses

/-!
# Reachability under a graph isomorphism

The geometric drawing of a graph names its vertices and edges by
points and open arcs. An isomorphism carries walks in selected edges
in both directions. This identifies their contraction classes without
extending a map to unused graph names, for GM V, (8.14).
-/

public section
namespace GraphMinor.GM05
open Set Graph Relation

/-- An isomorphism maps reachability along corresponding selected
edges to reachability in the target graph. -/
theorem contraction_reach_of_iso {α β α' β' : Type*} {G : Graph α β} {K : Graph α' β'}
    (φ : Iso G K) {C : Set β} {C' : Set β'}
    (hC : ∀ e : E(G),e.val∈C → (φ.edgeEquiv e).val∈C')
    (x y : V(G)) (h : y.val∈contractionClass G C x.val) :
    (φ.vertexEquiv y).val∈contractionClass K C' (φ.vertexEquiv x).val := by
  have hmap : ∀ (p q : α) (hp : p∈V(G)) (hq : q∈V(G)),
      ReflTransGen (fun a b ↦ ∃ e∈C,G.IsLink e a b) p q →
      ReflTransGen (fun a b ↦ ∃ e∈C',K.IsLink e a b)
        (φ.vertexEquiv ⟨p,hp⟩).val (φ.vertexEquiv ⟨q,hq⟩).val := by
    intro p q hp hq hr
    revert hq
    induction hr with
    | refl => intro _; exact .refl
    | @tail q r h hstep ih =>
      intro hrmem
      obtain ⟨e,he,hl⟩ := hstep
      have hh := (φ.isLink_iff ⟨e,hl.edge_mem⟩ ⟨q,hl.left_mem⟩ ⟨r,hrmem⟩).mp hl
      exact (ih hl.left_mem).tail ⟨(φ.edgeEquiv ⟨e,hl.edge_mem⟩).val,hC _ he,hh⟩
  exact hmap x.val y.val x.prop y.prop h

/-- Reachability in contraction classes is unchanged by a graph
isomorphism matching the contracted-edge sets. -/
theorem contraction_reach_iff_of_iso {α β α' β' : Type*} {G : Graph α β} {K : Graph α' β'}
    (φ : Iso G K) {C : Set β} {C' : Set β'}
    (hC : ∀ e : E(G),e.val∈C ↔ (φ.edgeEquiv e).val∈C') (x y : V(G)) :
    y.val∈contractionClass G C x.val ↔
      (φ.vertexEquiv y).val∈contractionClass K C' (φ.vertexEquiv x).val := by
  constructor
  · exact contraction_reach_of_iso φ (fun e ↦ (hC e).mp) x y
  · intro h
    let ψ : Iso K G := {
      vertexEquiv := φ.vertexEquiv.symm
      edgeEquiv := φ.edgeEquiv.symm
      isLink_iff := fun e x y ↦ by
        have hh := φ.isLink_iff (φ.edgeEquiv.symm e) (φ.vertexEquiv.symm x) (φ.vertexEquiv.symm y)
        simpa only [Equiv.apply_symm_apply] using hh.symm }
    have hC' : ∀ e : E(K),e.val∈C' → (ψ.edgeEquiv e).val∈C := by
      intro e he
      apply (hC (φ.edgeEquiv.symm e)).mpr
      simpa only [Equiv.apply_symm_apply] using he
    have hh := contraction_reach_of_iso ψ hC' (φ.vertexEquiv x) (φ.vertexEquiv y) h
    simpa only [ψ,Equiv.symm_apply_apply] using hh

end GraphMinor.GM05
