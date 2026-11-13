module

public import GraphMinor.GM05.GraphCopies

/-!
# Contraction components in disjoint copies

A walk along contracted edges cannot change its copy index. Conversely,
a walk inside `H` lifts to any fixed copy. Therefore every vertex after
contraction in a copy graph is the product of a singleton copy index and
a contraction component of `H`. This is the component calculation needed
to copy a minor witness in the proof of (8.8).
-/

@[expose] public section

namespace GraphMinor.GM05

open Graph Set Relation

/-- The component vertex set which becomes the image of `v` when edges
in `C` are contracted, as in `GraphMinor.contract`. -/
def contractionClass {α β : Type*} (H : Graph α β) (C : Set β) (v : α) : Set α :=
  {w | ReflTransGen (fun x y ↦ ∃ e∈C,H.IsLink e x y) v w}

/-- A contraction class contains its starting vertex. -/
theorem mem_contractionClass_self {α β : Type*} (H : Graph α β) (C : Set β) (v : α) :
    v∈contractionClass H C v := ReflTransGen.refl

/-- The vertices of a contraction are the component sets of its original
vertices. -/
theorem contract_vertexSet_eq {α β : Type*} (H : Graph α β) (C : Set β) :
    V(contract H C)=contractionClass H C '' V(H) := rfl

/-- The edge set of a contraction consists of the uncontracted edges. -/
theorem contract_edgeSet_eq {α β : Type*} (H : Graph α β) (C : Set β) :
    E(contract H C)=E(H)\C := rfl

/-- Ends of an uncontracted edge become the classes of their original ends. -/
theorem contract_link_iff {α β : Type*} (H : Graph α β) (C : Set β)
    (e : β) (X Y : Set α) :
    (contract H C).IsLink e X Y ↔ e∉C ∧ ∃ x y,H.IsLink e x y ∧
      contractionClass H C x=X ∧ contractionClass H C y=Y := by
  simp only [contract,Graph.deleteEdges_isLink,Graph.map_isLink,Relation.Map]
  exact and_comm

private lemma copies_reach {α β : Type*} (k : ℕ) (H : Graph α β) (C : Set β)
    (p q : Fin k × α) :
    q∈contractionClass (graphCopies k H) (univ ×ˢ C) p ↔
      p.1=q.1 ∧ q.2∈contractionClass H C p.2 := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨rfl,ReflTransGen.refl⟩
    | @tail q r h hqr ih =>
      obtain ⟨e,he,hlink⟩ := hqr
      exact ⟨ih.1.trans (hlink.1.symm.trans hlink.2.1),
        ih.2.tail ⟨e.2,he.2,hlink.2.2⟩⟩
  · rintro ⟨he,h⟩
    rcases p with ⟨i,x⟩
    rcases q with ⟨j,y⟩
    change i=j at he
    subst j
    change ReflTransGen (fun x y ↦ ∃ e∈C,H.IsLink e x y) x y at h
    induction h with
    | refl => exact ReflTransGen.refl
    | @tail y z h hyz ih =>
      obtain ⟨e,he,hl⟩ := hyz
      exact ih.tail ⟨(i,e),⟨mem_univ i,he⟩,rfl,rfl,hl⟩

/-- Contracting copied edges preserves the copy index and contracts the
same edges inside each copy. -/
theorem contractionClass_copies {α β : Type*} (k : ℕ) (H : Graph α β) (C : Set β)
    (p : Fin k × α) :
    contractionClass (graphCopies k H) (univ ×ˢ C) p = {p.1} ×ˢ contractionClass H C p.2 := by
  ext q
  rw [copies_reach]
  exact and_congr eq_comm Iff.rfl

/-- A product with a singleton determines its index and its nonempty
second factor. -/
theorem singleton_prod_eq_iff {α I : Type*} {A B : Set α} {i j : I} (hA : A.Nonempty) :
    ({i} ×ˢ A : Set (I × α))={j} ×ˢ B ↔ i=j ∧ A=B := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := hA
    have hj : (i,a)∈({j} ×ˢ B : Set (I × α)) := h ▸ ⟨rfl,ha⟩
    have hij : i=j := hj.1
    subst j
    refine ⟨rfl,?_⟩
    ext x
    have hx := congrArg (fun S : Set (I × α) ↦ (i,x)∈S) h
    simpa only [mem_prod,mem_singleton_iff,true_and] using Iff.of_eq hx
  · rintro ⟨rfl,rfl⟩; rfl

end GraphMinor.GM05
