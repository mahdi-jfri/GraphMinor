module

public import GraphMinor.GM01.RootedBranchArms
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Root-preserving arms inside a model branch

For the rooted subdivision in the proof of Graph Minors I, (1.1), page
55, the branch of the comb root has at most two edge attachments. Choose
their ends inside that branch and add the target root as a third
attachment. The resulting arms stay in the connected branch graph
provided by the minor model, so they avoid every represented source edge.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

universe u v w

/-- Construct arms at a model vertex of degree one or two, together with a
path to a distinguished point of its branch. The latter path meets every
edge arm only at their common centre. This is the rooted refinement of
the subcubic subdivision step used on page 55. -/
theorem rooted_model_vertex_arms {α : Type u} {β : Type v} {ν : Type w} [Finite ν]
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe) (v : ν)
    (hDeg : (H.neighborSet v).ncard ≤ 2) (hNonempty : (H.neighborSet v).Nonempty)
    (root : α) (hroot : root ∈ ηv v) :
    ∃ (K : Graph α β), K ≤ G.deleteEdges (ηe '' H.edgeSet) ∧ V(K) = ηv v ∧
      ∃ (m : α) (attach : H.neighborSet v → α)
        (arm : H.neighborSet v → Graph α β) (R : Graph α β), m ∈ V(K) ∧
        (∀ i, attach i ∈ V(K) ∧ G.Inc (ηe s(v,i.val)) (attach i)) ∧
        (∀ i, IsGraphPathWithEnds K (arm i) m (attach i)) ∧
        IsGraphPathWithEnds K R m root ∧
        (∀ i j, i ≠ j → V(arm i) ∩ V(arm j) = {m}) ∧
        (∀ i, V(arm i) ∩ V(R) = {m}) := by
  classical
  obtain ⟨K, hK, hVK, hconn⟩ := h.connected v (mem_univ _)
  have hAttach (i : H.neighborSet v) : ∃ x ∈ ηv v, G.Inc (ηe s(v,i.val)) x := by
    have he : s(v,i.val) ∈ E(Graph.ofSimpleGraph H) := i.property
    have hi : (Graph.ofSimpleGraph H).Inc s(v,i.val) v := ⟨i.val, rfl, he⟩
    exact (h.inc_iff v (mem_univ _) s(v,i.val) he).mp hi
  let attach (i : H.neighborSet v) := (hAttach i).choose
  have hInK (i : H.neighborSet v) : attach i ∈ V(K) :=
    hVK.symm ▸ (hAttach i).choose_spec.1
  let : Nonempty (H.neighborSet v) := ⟨⟨hNonempty.choose, hNonempty.choose_spec⟩⟩
  have hrootK : root ∈ V(K) := hVK.symm ▸ hroot
  obtain ⟨m, arm, R, hm, hPath, hR, hInter, hRootInter⟩ :=
    exists_rooted_branch_arms hDeg K hconn attach hInK root hrootK
  exact ⟨K, hK, hVK, m, attach, arm, R, hm,
    fun i ↦ ⟨hInK i, (hAttach i).choose_spec.2⟩,
    hPath, hR, hInter, hRootInter⟩

end GraphMinor.GM01
