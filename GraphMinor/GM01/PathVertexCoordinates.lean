module

public import GraphMinor.GM09.Basic
public import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-!
# Coordinates along an actual graph path

To order the selected attachment endpoints on page 60 of Graph
Minors I, enumerate the vertices of the covering path from its root.
Its witnessing simple walk has no repeated vertex. Its support list
therefore gives injective finite coordinates, covers the whole path,
and retains the actual edge between consecutive coordinates.
-/

public section

namespace GraphMinor.GM01

open Set Graph Function GraphMinor.GM09 GraphMinor.Surface

private theorem graphWalk_support_isChain {α β : Type*} {G : Graph α β} {a b : α}
    (W : GraphWalk G a b) : W.support.IsChain G.Adj := by
  induction W with
  | nil => exact List.isChain_singleton _
  | @cons a d b e he rest ih =>
    cases rest with
    | nil =>
      change [a,d].IsChain G.Adj
      exact List.isChain_cons_cons.mpr ⟨⟨e,he⟩,List.isChain_singleton _⟩
    | cons he' rest' =>
      exact List.isChain_cons_cons.mpr ⟨⟨e,he⟩,ih⟩

/-- Finite injective coordinates along the entire actual covering path,
starting at its root, for the GM01 page-60 attachment order. -/
theorem exists_path_vertex_coordinates {α β : Type*} {G Q : Graph α β} {a b : α}
    (hQ : IsGraphPathWithEnds G Q a b) :
    ∃ N : ℕ, ∃ hN : 0 < N, ∃ v : Fin N → α, Injective v ∧ range v = V(Q) ∧
      v ⟨0,hN⟩ = a ∧
      (∀ i j, j.val = i.val + 1 → G.Adj (v i) (v j)) := by
  obtain ⟨hQG,W,hW,hV,_⟩ := hQ
  have hN : 0 < W.support.length := by cases W <;> simp [GraphWalk.support]
  let v := W.support.get
  have hRange : range v = V(Q) := by
    ext x
    rw [hV]
    change (∃ i, W.support.get i = x) ↔ x ∈ W.support
    exact List.mem_iff_get.symm
  have hStart : v ⟨0,hN⟩ = a := by cases W <;> rfl
  refine ⟨W.support.length,hN,v,hW.injective_get,hRange,hStart,?_⟩
  intro i j hij
  have hNext : i.val + 1 < W.support.length := hij ▸ j.isLt
  have hStep := List.isChain_iff_getElem.mp (graphWalk_support_isChain W) i.val hNext
  have hStep' : Q.Adj (v i) (v j) := by
    have hj : j = (⟨i.val + 1,hNext⟩ : Fin W.support.length) := Fin.ext hij
    rw [hj]
    exact hStep
  obtain ⟨e,he⟩ := hStep'
  exact ⟨e,he.mono hQG⟩

end GraphMinor.GM01
