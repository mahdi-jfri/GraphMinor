module

public import GraphMinor.GM01.RootedForks
public import GraphMinor.GM01.PathCombTrees

/-!
# The rooted fork is a tree

For the `Q(γ,δ)` configuration used in the proof of Graph Minors I, (1.1),
follow the parent map in either old copy until its root, then move to the
new root. Depth strictly increases on every edge away from that parent.
A deepest vertex on a hypothetical cycle would have both cycle neighbours
equal to its parent, so the connected fork is acyclic.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- Distance from the new root in the rooted fork. -/
def rootedForkDepth {δ : ℕ} : RootedForkVertex δ → ℕ
  | none => 0
  | some (.inl p) => pathCombDepth p + 1
  | some (.inr word) => word.length + 1

/-- The parent inside either old copy, with its old root's parent changed
to the new root. -/
def rootedForkParent (δ : ℕ) (hδ : 2 ≤ δ) : RootedForkVertex δ → RootedForkVertex δ
  | none => none
  | some (.inl p) => if p = rootedForkAnchor δ hδ then none else some (.inl (pathCombParent p))
  | some (.inr []) => none
  | some (.inr (_ :: word)) => some (.inr word)

/-- A fork neighbour no farther from the new root must be the parent. -/
theorem rootedFork_parent_eq_of_adj {γ δ : ℕ} (hδ : 2 ≤ δ)
    {v w : RootedForkVertex δ} (h : (rootedFork γ δ hδ).Adj v w)
    (hd : rootedForkDepth w ≤ rootedForkDepth v) : rootedForkParent δ hδ v = w := by
  cases v with
  | none =>
    cases w with
    | none => exact False.elim h
    | some w =>
      cases w with
      | inl q => change pathCombDepth q + 1 ≤ 0 at hd; omega
      | inr word => change word.length + 1 ≤ 0 at hd; omega
  | some v =>
    cases v with
    | inl p =>
      cases w with
      | none =>
        change p = rootedForkAnchor δ hδ at h
        simp only [rootedForkParent, h, ↓reduceIte]
      | some w =>
        cases w with
        | inl q =>
          have hdepth : pathCombDepth q ≤ pathCombDepth p := Nat.le_of_succ_le_succ hd
          have hparent := pathComb_parent_eq_of_adj h hdepth
          have hpne : p ≠ rootedForkAnchor δ hδ := by
            intro hp
            subst p
            have heq : rootedForkAnchor δ hδ = q := hparent
            exact h.ne (congrArg (fun p ↦ some (Sum.inl p)) heq)
          simp only [rootedForkParent, hpne, ↓reduceIte, hparent]
        | inr word => exact False.elim h
    | inr word =>
      cases w with
      | none =>
        change word = [] at h
        subst word
        rfl
      | some w =>
        cases w with
        | inl q => exact False.elim h
        | inr word' =>
          change word'.length + 1 ≤ word.length + 1 at hd
          rcases h.2.2 with ⟨bit, rfl⟩ | ⟨bit, rfl⟩
          · simp only [List.length_cons] at hd
            omega
          · rfl

/-- The rooted fork has no cycle, by its unique parent at each depth. -/
theorem rootedFork_isAcyclic (γ δ : ℕ) (hδ : 2 ≤ δ) :
    (rootedFork γ δ hδ).coe.IsAcyclic := by
  classical
  intro v p hp
  obtain ⟨x, hx, hmax⟩ := p.support.toFinset.exists_max_image
    (fun x ↦ rootedForkDepth x.val) ⟨v, by simp⟩
  have hxmem : x ∈ p.support := List.mem_toFinset.mp hx
  let q := p.rotate x hxmem
  have hq : q.IsCycle := hp.rotate hxmem
  have hs : rootedForkDepth q.snd.val ≤ rootedForkDepth x.val := hmax _
    (List.mem_toFinset.mpr ((p.mem_support_rotate_iff x hxmem).mp (q.getVert_mem_support 1)))
  have ht : rootedForkDepth q.penultimate.val ≤ rootedForkDepth x.val := hmax _
    (List.mem_toFinset.mpr ((p.mem_support_rotate_iff x hxmem).mp
      (q.getVert_mem_support (q.length - 1))))
  have hsparent := rootedFork_parent_eq_of_adj hδ (q.adj_snd hq.not_nil) hs
  have htparent := rootedFork_parent_eq_of_adj hδ (q.adj_penultimate hq.not_nil).symm ht
  exact hq.snd_ne_penultimate (Subtype.ext (hsparent.symm.trans htparent))

/-- The finite rooted configurations `Q(γ,δ)` are trees, as used in
Graph Minors I, Section 3, page 53. -/
theorem rootedFork_isTree (γ δ : ℕ) (hδ : 2 ≤ δ) : IsTreeSubgraph (rootedFork γ δ hδ) :=
  ⟨rootedFork_connected γ δ hδ, rootedFork_isAcyclic γ δ hδ⟩

end GraphMinor.GM01
