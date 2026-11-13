module

public import GraphMinor.GM05.GraphCopies
import GraphMinor.GM05.CopyContractionClasses

/-!
# Contraction commutes with taking disjoint copies

The vertex of a contracted copy is a singleton copy index times a
component vertex set. This gives a bijection between the vertices obtained
by copying after contraction and those obtained by contraction after
copying. The edge bijection retains every uncontracted edge label.
These bijections preserve links, including loops.
-/

public section

namespace GraphMinor.GM05

open Graph Set

/-- Contract the same edge set in every copy, or contract first and then
copy. The vertex map sends `(i,X)` to `{i} × X` and the edge map is the
identity on the surviving pairs of labels. -/
noncomputable def copiesContractIso {α β : Type*} (k : ℕ) (H : Graph α β) (C : Set β) :
    Iso (graphCopies k (contract H C)) (contract (graphCopies k H) (univ ×ˢ C)) := by
  classical
  let f : V(graphCopies k (contract H C)) → V(contract (graphCopies k H) (univ ×ˢ C)) :=
    fun X ↦ ⟨{X.1.1} ×ˢ X.1.2, by
      obtain ⟨x,hx,hc⟩ := X.2.2
      refine ⟨(X.1.1,x),⟨mem_univ _,hx⟩,?_⟩
      change contractionClass (graphCopies k H) (univ ×ˢ C) (X.1.1,x) = {X.1.1} ×ˢ X.1.2
      change contractionClass H C x=X.1.2 at hc
      rw [contractionClass_copies,hc]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro X Y h
      have hset := congrArg Subtype.val h
      change ({X.1.1} ×ˢ X.1.2 : Set (Fin k × α))={Y.1.1} ×ˢ Y.1.2 at hset
      have hNX : X.1.2.Nonempty := by
        obtain ⟨x,hx,hc⟩ := X.2.2
        exact ⟨x,hc ▸ mem_contractionClass_self H C x⟩
      have he := (singleton_prod_eq_iff hNX).mp hset
      exact Subtype.ext (Prod.ext he.1 he.2)
    · intro Y
      obtain ⟨p,hp,hpY⟩ := Y.2
      let X : V(graphCopies k (contract H C)) :=
        ⟨(p.1,contractionClass H C p.2),mem_univ _,⟨p.2,hp.2,rfl⟩⟩
      refine ⟨X,Subtype.ext ?_⟩
      change {p.1} ×ˢ contractionClass H C p.2=Y.1
      exact (contractionClass_copies k H C p).symm.trans hpY
  let edgeEquiv : E(graphCopies k (contract H C)) ≃ E(contract (graphCopies k H) (univ ×ˢ C)) := {
    toFun e := ⟨e.1,⟨mem_univ _,e.2.2.1⟩,fun h ↦ e.2.2.2 h.2⟩
    invFun e := ⟨e.1,mem_univ _,e.2.1.2,fun h ↦ e.2.2 ⟨mem_univ _,h⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  refine { vertexEquiv:=Equiv.ofBijective f hf, edgeEquiv:=edgeEquiv, isLink_iff:=?_ }
  intro e X Y
  change (e.1.1=X.1.1 ∧ e.1.1=Y.1.1 ∧ (contract H C).IsLink e.1.2 X.1.2 Y.1.2) ↔
    (contract (graphCopies k H) (univ ×ˢ C)).IsLink e.1 ({X.1.1} ×ˢ X.1.2) ({Y.1.1} ×ˢ Y.1.2)
  constructor
  · rintro ⟨heX,heY,hl⟩
    obtain ⟨heC,u,v,huv,huX,hvY⟩ := (contract_link_iff H C _ _ _).mp hl
    apply (contract_link_iff (graphCopies k H) (univ ×ˢ C) _ _ _).mpr
    refine ⟨fun h ↦ heC h.2,(e.1.1,u),(e.1.1,v),⟨rfl,rfl,huv⟩,?_,?_⟩
    · rw [contractionClass_copies,heX,huX]
    · rw [contractionClass_copies,heY,hvY]
  · intro hl
    obtain ⟨heC,p,q,hpq,hpX,hqY⟩ :=
      (contract_link_iff (graphCopies k H) (univ ×ˢ C) _ _ _).mp hl
    rw [contractionClass_copies] at hpX hqY
    have hp := (singleton_prod_eq_iff ⟨p.2,mem_contractionClass_self H C p.2⟩).mp hpX
    have hq := (singleton_prod_eq_iff ⟨q.2,mem_contractionClass_self H C q.2⟩).mp hqY
    refine ⟨hpq.1.trans hp.1,hpq.2.1.trans hq.1,?_⟩
    exact (contract_link_iff H C _ _ _).mpr
      ⟨fun h ↦ heC ⟨mem_univ _,h⟩,p.2,q.2,hpq.2.2,hp.2,hq.2⟩

end GraphMinor.GM05
