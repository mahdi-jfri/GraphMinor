module

public import GraphMinor.GM01.CleanBypass
import GraphMinor.GM01.SubdivisionConnected

/-!
# Extending a bypass through a connected tail

The second sentence of the proof of Graph Minors I, (4.1), page 55,
extends the clean bypass to the last block. A clean bypass avoids any
set of `H` containing neither end. If its far end lies in a connected
tail disjoint from that set, follow a path through the tail and remove
repeated vertices. The result is still an avoiding path.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation GraphMinor.GM09

private theorem le_deleteVerts_of_disjoint {α β : Type*} {G K : Graph α β}
    (hKG : K ≤ G) {X : Set α} (hX : Disjoint V(K) X) : K ≤ G.deleteVerts X := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [vertexSet_deleteVerts]
    exact ⟨hKG.vertexSet_mono hx, fun hxX ↦ disjoint_left.mp hX hx hxX⟩
  · intro e x y he
    exact (G.deleteVerts_isLink X).mpr ⟨he.mono hKG,
      fun hx ↦ disjoint_left.mp hX he.left_mem hx,
      fun hy ↦ disjoint_left.mp hX he.right_mem hy⟩

/-- Extend a clean bypass to any vertex of a connected tail while
avoiding a set of the covered graph containing neither bypass end.
This is the path-extension step of GM01 (4.1), page 55. -/
theorem exists_bypass_extension {α β : Type*} {G H P K : Graph α β}
    {a b c : α} (hP : IsGraphPathWithEnds G P a b)
    (hmeet : V(P) ∩ V(H) = {a,b}) {X : Set α} (hX : X ⊆ V(H))
    (ha : a ∉ X) (hb : b ∉ X) (hKG : K ≤ G) (hconn : GraphConnected K)
    (hbK : b ∈ V(K)) (hcK : c ∈ V(K)) (hKX : Disjoint V(K) X) :
    ∃ Q : Graph α β, IsGraphPathWithEnds G Q a c ∧ Disjoint V(Q) X := by
  have hPX : Disjoint V(P) X := by
    apply disjoint_left.mpr
    intro x hx hxX
    have hends : x ∈ ({a,b} : Set α) := hmeet ▸ ⟨hx, hX hxX⟩
    rcases hends with rfl | hx
    · exact ha hxX
    · exact hb (hx ▸ hxX)
  have hPdel := le_deleteVerts_of_disjoint hP.le hPX
  have hKdel := le_deleteVerts_of_disjoint hKG hKX
  have hfirst : ReflTransGen (G.deleteVerts X).Adj a b :=
    ReflTransGen.mono
      (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hPdel⟩)
      a b ((graphConnected_of_isGraphPath hP).2 a hP.left_mem b hP.right_mem)
  have hsecond : ReflTransGen (G.deleteVerts X).Adj b c :=
    ReflTransGen.mono
      (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hKdel⟩)
      b c (hconn.2 b hbK c hcK)
  have hno : ¬ GraphSeparates G X {a} {c} := by
    intro hsep
    exact hsep a rfl c rfl (hPdel.vertexSet_mono hP.left_mem)
      (hKdel.vertexSet_mono hcK) (hfirst.trans hsecond)
  obtain ⟨a', ha', c', hc', Q, hQ, hQX⟩ := not_graphSeparates_iff.mp hno
  have hae : a' = a := ha'
  have hce : c' = c := hc'
  subst a'
  subst c'
  exact ⟨Q, hQ, hQX⟩

end GraphMinor.GM01
