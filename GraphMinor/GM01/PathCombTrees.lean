module

public import GraphMinor.GM01.PathCombs
import GraphMinor.GM01.Basic

/-!
# The path of binary copies is a tree

In the rooted configuration `P(γ,δ)`, move towards the first spine vertex
by deleting a bit inside a binary copy, then moving backwards on the
spine. This gives paths to the root. A vertex has at most one neighbour
no farther from the root, which rules out a cycle by taking a farthest
vertex on it. These are properties of the configurations used in the
proof of Graph Minors I, (1.1).
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- Distance to the first spine vertex in the path-of-trees construction. -/
def pathCombDepth {δ : ℕ} : PathCombVertex δ → ℕ
  | .inl i => i.val
  | .inr (i, word) => i.val + word.length + 1

/-- Move towards the first spine vertex. Its parent is itself. -/
def pathCombParent {δ : ℕ} : PathCombVertex δ → PathCombVertex δ
  | .inl i => .inl ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩
  | .inr (i, []) => .inl i
  | .inr (i, _ :: word) => .inr (i, word)

/-- Away from the root, the parent is one step nearer to it. -/
theorem pathCombDepth_parent {δ : ℕ} (hδ : 0 < δ) {v : PathCombVertex δ}
    (hv : v ≠ Sum.inl ⟨0, hδ⟩) :
    pathCombDepth (pathCombParent v) + 1 = pathCombDepth v := by
  cases v with
  | inl i =>
    have hi : i.val ≠ 0 := fun h ↦ hv (congrArg Sum.inl (Fin.ext h))
    change i.val - 1 + 1 = i.val
    omega
  | inr p =>
    rcases p with ⟨i, word⟩
    cases word <;> rfl

/-- A nonroot comb vertex is adjacent to its parent. -/
theorem pathComb_adj_parent {γ δ : ℕ} (hδ : 0 < δ) {v : PathCombVertex δ}
    (hv : v ∈ (pathComb γ δ).verts) (hne : v ≠ Sum.inl ⟨0, hδ⟩) :
    (pathComb γ δ).Adj v (pathCombParent v) := by
  cases v with
  | inl i =>
    have hi : i.val ≠ 0 := fun h ↦ hne (congrArg Sum.inl (Fin.ext h))
    apply pathGraph_adj.mpr
    right
    change i.val - 1 + 1 = i.val
    omega
  | inr p =>
    rcases p with ⟨i, word⟩
    cases word with
    | nil => exact ⟨rfl, rfl, hv⟩
    | cons bit word =>
      refine ⟨rfl, hv, ?_, Or.inr ⟨bit, rfl⟩⟩
      change (bit :: word).length < γ at hv
      simp only [List.length_cons] at hv
      omega

/-- Every comb vertex can be reached from the first spine vertex. -/
theorem pathComb_reachable_root {γ δ : ℕ} (hδ : 0 < δ) {v : PathCombVertex δ}
    (hv : v ∈ (pathComb γ δ).verts) :
    Relation.ReflTransGen (toGraph (pathComb γ δ)).Adj (Sum.inl ⟨0, hδ⟩) v := by
  induction hd : pathCombDepth v using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hroot : v = Sum.inl ⟨0, hδ⟩
    · subst v
      exact .refl
    · have hp := pathCombDepth_parent hδ hroot
      have hlt : pathCombDepth (pathCombParent v) < n := by omega
      have ha := pathComb_adj_parent hδ hv hroot
      have hparentmem : pathCombParent v ∈ (pathComb γ δ).verts := ha.snd_mem
      exact (ih _ hlt hparentmem rfl).tail ((adj_toGraph _ _ _).2 ha.symm)

/-- The spine and its binary copies form a connected graph. -/
theorem pathComb_connected {γ δ : ℕ} (hδ : 0 < δ) : (pathComb γ δ).Connected := by
  apply (graphConnected_toGraph_iff _).mp
  refine ⟨⟨Sum.inl ⟨0, hδ⟩, pathComb_spine_mem γ δ _⟩, ?_⟩
  intro x hx y hy
  have symm {a b : PathCombVertex δ}
      (h : Relation.ReflTransGen (toGraph (pathComb γ δ)).Adj a b) :
      Relation.ReflTransGen (toGraph (pathComb γ δ)).Adj b a := by
    induction h with
    | refl => exact .refl
    | @tail c d hab hcd ih => exact (Relation.ReflTransGen.single hcd.symm).trans ih
  exact (symm (pathComb_reachable_root hδ hx)).trans (pathComb_reachable_root hδ hy)

/-- A neighbour no farther from the first spine vertex must be the parent. -/
theorem pathComb_parent_eq_of_adj {γ δ : ℕ} {v w : PathCombVertex δ}
    (h : (pathComb γ δ).Adj v w) (hd : pathCombDepth w ≤ pathCombDepth v) :
    pathCombParent v = w := by
  cases v with
  | inl i =>
    cases w with
    | inl j =>
      rcases pathGraph_adj.mp h with hij | hji
      · change j.val ≤ i.val at hd
        omega
      · apply congrArg Sum.inl
        apply Fin.ext
        change i.val - 1 = j.val
        omega
    | inr q =>
      rcases q with ⟨j, word⟩
      rcases h with ⟨rfl, rfl, hγ⟩
      change i.val + 0 + 1 ≤ i.val at hd
      omega
  | inr p =>
    rcases p with ⟨i, word⟩
    cases w with
    | inl j =>
      rcases h with ⟨rfl, rfl, hγ⟩
      rfl
    | inr q =>
      rcases q with ⟨j, word'⟩
      rcases h with ⟨rfl, hv, hw, hedge⟩
      rcases hedge with ⟨bit, rfl⟩ | ⟨bit, rfl⟩
      · change i.val + (bit :: word).length + 1 ≤ i.val + word.length + 1 at hd
        simp only [List.length_cons] at hd
        omega
      · rfl

/-- The unique-parent property rules out cycles in a path of binary copies. -/
theorem pathComb_isAcyclic (γ δ : ℕ) : (pathComb γ δ).coe.IsAcyclic := by
  classical
  intro v p hp
  obtain ⟨x, hx, hmax⟩ := p.support.toFinset.exists_max_image
    (fun x ↦ pathCombDepth x.val) ⟨v, by simp⟩
  have hxmem : x ∈ p.support := List.mem_toFinset.mp hx
  let q := p.rotate x hxmem
  have hq : q.IsCycle := hp.rotate hxmem
  have hs : pathCombDepth q.snd.val ≤ pathCombDepth x.val := hmax _
    (List.mem_toFinset.mpr ((p.mem_support_rotate_iff x hxmem).mp (q.getVert_mem_support 1)))
  have ht : pathCombDepth q.penultimate.val ≤ pathCombDepth x.val := hmax _
    (List.mem_toFinset.mpr ((p.mem_support_rotate_iff x hxmem).mp
      (q.getVert_mem_support (q.length - 1))))
  have hsparent := pathComb_parent_eq_of_adj (q.adj_snd hq.not_nil) hs
  have htparent := pathComb_parent_eq_of_adj (q.adj_penultimate hq.not_nil).symm ht
  exact hq.snd_ne_penultimate (Subtype.ext (hsparent.symm.trans htparent))

/-- The rooted configurations `P(γ,δ)` are trees for `δ ≥ 1`, as used in
Graph Minors I, Section 3, page 53. -/
theorem pathComb_isTree {γ δ : ℕ} (hδ : 0 < δ) : IsTreeSubgraph (pathComb γ δ) :=
  ⟨pathComb_connected (γ := γ) hδ, pathComb_isAcyclic γ δ⟩

end GraphMinor.GM01
