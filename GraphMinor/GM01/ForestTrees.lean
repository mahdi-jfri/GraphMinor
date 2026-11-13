module

public import GraphMinor.GM01.Defs
public import Mathlib.Combinatorics.SimpleGraph.Star
import GraphMinor.GM01.Basic
import Mathlib.Data.Set.Finite.List

/-!
# The trees used to exclude a forest

The proof of Graph Minors I, (1.1), page 51, puts a forest inside one of the
trees `Y_ℓ`. We label the centre by `none`. A vertex on one of its three
branches is labelled by the branch number and a binary word. Removing the
first bit moves towards the centre. Bounding the word length gives the
successive trees obtained by adding two vertices at every leaf.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- Labels for the centre and the three binary branches of the trees `Y_ℓ`
from Graph Minors I, Section 3, page 51. -/
abbrev ForestTreeVertex := Option (Fin 3 × List Bool)

/-- Distance from the centre in the word labelling. -/
def forestTreeDepth : ForestTreeVertex → ℕ
  | none => 0
  | some (_, word) => word.length + 1

/-- The neighbour towards the centre. The value at the centre is the centre. -/
def forestTreeParent : ForestTreeVertex → ForestTreeVertex
  | none => none
  | some (_, []) => none
  | some (branch, _ :: word) => some (branch, word)

/-- Every vertex except the centre has a parent one level nearer the centre. -/
theorem forestTreeDepth_parent {v : ForestTreeVertex} (hv : v ≠ none) :
    forestTreeDepth (forestTreeParent v) + 1 = forestTreeDepth v := by
  cases v with
  | none => exact False.elim (hv rfl)
  | some p =>
    rcases p with ⟨branch, word⟩
    cases word <;> rfl

/-- A noncentral vertex is different from its parent. -/
theorem forestTreeParent_ne {v : ForestTreeVertex} (hv : v ≠ none) :
    forestTreeParent v ≠ v := by
  intro h
  have hd := forestTreeDepth_parent hv
  rw [h] at hd
  exact Nat.add_one_ne_self _ hd

/-- The vertices of `Y_ℓ`, namely the centre and the first `ℓ` levels of its
three binary branches (Graph Minors I, Section 3, page 51). The extension
`ℓ = 0` consists only of the centre. -/
def forestTreeVertices (ℓ : ℕ) : Set ForestTreeVertex :=
  {v | forestTreeDepth v ≤ ℓ}

/-- The finite tree `Y_ℓ` from Graph Minors I, Section 3, page 51. The paper
starts at `ℓ = 1` with `K_{1,3}` and adds two neighbours to each leaf at each
successive stage. Here each new neighbour is labelled by its added binary bit. -/
def forestTree (ℓ : ℕ) : (⊤ : SimpleGraph ForestTreeVertex).Subgraph where
  verts := forestTreeVertices ℓ
  Adj x y := x ∈ forestTreeVertices ℓ ∧ y ∈ forestTreeVertices ℓ ∧
    ((y ≠ none ∧ forestTreeParent y = x) ∨
      (x ≠ none ∧ forestTreeParent x = y))
  adj_sub := by
    intro x y h
    apply (top_adj _ _).2
    intro hxy
    subst y
    rcases h.2.2 with h | h
    · exact forestTreeParent_ne h.1 h.2
    · exact forestTreeParent_ne h.1 h.2
  edge_vert := fun h ↦ h.1
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, h.2.2.symm⟩⟩

/-- The multigraph version of the paper's `Y_ℓ`. -/
def forestTreeGraph (ℓ : ℕ) : Graph ForestTreeVertex (Sym2 ForestTreeVertex) :=
  toGraph (forestTree ℓ)

/-- Each tree has finitely many vertices even though its ambient word type
is infinite. -/
theorem forestTree_vertices_finite (ℓ : ℕ) : (forestTree ℓ).verts.Finite := by
  have hwords : {w : List Bool | w.length < ℓ}.Finite := List.finite_length_lt Bool ℓ
  have hpairs : (Set.univ : Set (Fin 3)).Finite := Set.finite_univ
  have hfin := (hpairs.prod hwords).image (fun p ↦ (some p : ForestTreeVertex))
  apply ((Set.finite_singleton none).union hfin).subset
  intro v hv
  cases v with
  | none => exact Or.inl rfl
  | some p =>
    rcases p with ⟨branch, word⟩
    exact Or.inr ⟨(branch, word), ⟨Set.mem_univ _, by
      change word.length + 1 ≤ ℓ at hv
      change word.length < ℓ
      omega⟩, rfl⟩

/-- The centre belongs to every tree. -/
theorem forestTree_centre_mem (ℓ : ℕ) : none ∈ (forestTree ℓ).verts :=
  Nat.zero_le ℓ

/-- Increasing the depth retains every vertex and edge. -/
theorem forestTree_mono {ℓ μ : ℕ} (h : ℓ ≤ μ) : forestTree ℓ ≤ forestTree μ :=
  ⟨fun _ hv ↦ hv.trans h, fun _ _ ha ↦ ⟨ha.1.trans h, ha.2.1.trans h, ha.2.2⟩⟩

/-- Moving towards the centre stays in the same finite tree. -/
theorem forestTreeParent_mem {ℓ : ℕ} {v : ForestTreeVertex}
    (hv : v ∈ (forestTree ℓ).verts) :
    forestTreeParent v ∈ (forestTree ℓ).verts := by
  by_cases h : v = none
  · subst v
    exact forestTree_centre_mem ℓ
  · have hd := forestTreeDepth_parent h
    change forestTreeDepth v ≤ ℓ at hv
    change forestTreeDepth (forestTreeParent v) ≤ ℓ
    omega

/-- Every noncentral vertex is adjacent to its parent. -/
theorem forestTree_adj_parent {ℓ : ℕ} {v : ForestTreeVertex}
    (hv : v ∈ (forestTree ℓ).verts) (h : v ≠ none) :
    (forestTree ℓ).Adj v (forestTreeParent v) :=
  ⟨hv, forestTreeParent_mem hv, Or.inr ⟨h, rfl⟩⟩

/-- A neighbour which is no farther from the centre must be the parent. -/
theorem forestTree_parent_eq_of_adj {ℓ : ℕ} {v w : ForestTreeVertex}
    (h : (forestTree ℓ).Adj v w) (hd : forestTreeDepth w ≤ forestTreeDepth v) :
    forestTreeParent v = w := by
  rcases h.2.2 with h | h
  · have hw := forestTreeDepth_parent h.1
    rw [h.2] at hw
    omega
  · exact h.2

/-- Every vertex of `Y_ℓ` can be reached from its centre by following parent
edges in reverse. -/
theorem forestTree_reachable_centre (ℓ : ℕ) {v : ForestTreeVertex}
    (hv : v ∈ (forestTree ℓ).verts) :
    Relation.ReflTransGen (forestTreeGraph ℓ).Adj none v := by
  induction hd : forestTreeDepth v using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases h : v = none
    · subst v
      exact .refl
    · have hp := forestTreeDepth_parent h
      have hlt : forestTreeDepth (forestTreeParent v) < n := by omega
      have hr := ih _ hlt (forestTreeParent_mem hv) rfl
      exact hr.tail ((adj_toGraph (forestTree ℓ) _ _).2 (forestTree_adj_parent hv h).symm)

/-- The graph `Y_ℓ` is connected, including the one-vertex extension at depth
zero. -/
theorem forestTree_connected (ℓ : ℕ) : (forestTree ℓ).Connected := by
  apply (graphConnected_toGraph_iff _).mp
  refine ⟨⟨none, forestTree_centre_mem ℓ⟩, ?_⟩
  intro x hx y hy
  have symm {x y : ForestTreeVertex}
      (h : Relation.ReflTransGen (forestTreeGraph ℓ).Adj x y) :
      Relation.ReflTransGen (forestTreeGraph ℓ).Adj y x := by
    induction h with
    | refl => exact .refl
    | @tail b c hab hbc ih => exact (Relation.ReflTransGen.single hbc.symm).trans ih
  exact (symm (forestTree_reachable_centre ℓ hx)).trans (forestTree_reachable_centre ℓ hy)

/-- A cycle would have a vertex farthest from the centre. Both its cycle
neighbours would then be its parent, contradicting their distinctness. -/
theorem forestTree_isAcyclic (ℓ : ℕ) : (forestTree ℓ).coe.IsAcyclic := by
  classical
  intro v p hp
  obtain ⟨x, hx, hmax⟩ := p.support.toFinset.exists_max_image
    (fun x ↦ forestTreeDepth x.val) ⟨v, by simp⟩
  have hxmem : x ∈ p.support := List.mem_toFinset.mp hx
  let q := p.rotate x hxmem
  have hq : q.IsCycle := hp.rotate hxmem
  have hs : forestTreeDepth q.snd.val ≤ forestTreeDepth x.val := hmax _
    (List.mem_toFinset.mpr ((p.mem_support_rotate_iff x hxmem).mp (q.getVert_mem_support 1)))
  have ht : forestTreeDepth q.penultimate.val ≤ forestTreeDepth x.val := hmax _
    (List.mem_toFinset.mpr ((p.mem_support_rotate_iff x hxmem).mp
      (q.getVert_mem_support (q.length - 1))))
  have hsparent : forestTreeParent x.val = q.snd.val :=
    forestTree_parent_eq_of_adj (q.adj_snd hq.not_nil) hs
  have htparent : forestTreeParent x.val = q.penultimate.val :=
    forestTree_parent_eq_of_adj (q.adj_penultimate hq.not_nil).symm ht
  exact hq.snd_ne_penultimate (Subtype.ext (hsparent.symm.trans htparent))

/-- The finite connected acyclic graph in the word construction is a tree. -/
theorem forestTree_isTree (ℓ : ℕ) : IsTreeSubgraph (forestTree ℓ) :=
  ⟨forestTree_connected ℓ, forestTree_isAcyclic ℓ⟩

/-- At the outer level the only neighbour is the parent. -/
theorem forestTree_neighborSet_outer {ℓ : ℕ} (hℓ : 0 < ℓ)
    {v : ForestTreeVertex} (hv : forestTreeDepth v = ℓ) :
    (forestTree ℓ).neighborSet v = {forestTreeParent v} := by
  have hvne : v ≠ none := by
    intro h
    subst v
    change 0 = ℓ at hv
    omega
  have hvmem : v ∈ (forestTree ℓ).verts := hv.le
  apply Set.ext
  intro w
  constructor
  · intro hw
    have hdw : forestTreeDepth w ≤ ℓ := hw.2.1
    have hd : forestTreeDepth w ≤ forestTreeDepth v := hdw.trans_eq hv.symm
    exact (forestTree_parent_eq_of_adj hw hd).symm
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact forestTree_adj_parent hvmem hvne

/-- In a nontrivial `Y_ℓ`, precisely the outer vertices are leaves. -/
theorem forestTree_isLeaf_iff {ℓ : ℕ} (hℓ : 0 < ℓ) {v : ForestTreeVertex} :
    IsLeafOf (forestTree ℓ) v ↔ forestTreeDepth v = ℓ := by
  constructor
  · intro hv
    by_contra hdepth
    have hlt : forestTreeDepth v < ℓ := lt_of_le_of_ne hv.1 hdepth
    obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hv.2
    have unique {a b : ForestTreeVertex} (ha : (forestTree ℓ).Adj v a)
        (hb : (forestTree ℓ).Adj v b) : a = b := by
      have ha' : a ∈ (forestTree ℓ).neighborSet v := ha
      have hb' : b ∈ (forestTree ℓ).neighborSet v := hb
      rw [hw, Set.mem_singleton_iff] at ha' hb'
      exact ha'.trans hb'.symm
    cases v with
    | none =>
      have ha : (forestTree ℓ).Adj none (some (0, [])) :=
        ⟨forestTree_centre_mem ℓ, by change 1 ≤ ℓ; omega, Or.inl ⟨by simp, rfl⟩⟩
      have hb : (forestTree ℓ).Adj none (some (1, [])) :=
        ⟨forestTree_centre_mem ℓ, by change 1 ≤ ℓ; omega, Or.inl ⟨by simp, rfl⟩⟩
      have he := unique ha hb
      cases he
    | some p =>
      rcases p with ⟨branch, word⟩
      have hc (b : Bool) :
          (forestTree ℓ).Adj (some (branch, word)) (some (branch, b :: word)) := by
        refine ⟨hv.1, ?_, Or.inl ⟨by simp, rfl⟩⟩
        change word.length + 1 < ℓ at hlt
        change (b :: word).length + 1 ≤ ℓ
        simp only [List.length_cons]
        omega
      have he := unique (hc false) (hc true)
      cases he
  · intro hv
    refine ⟨hv.le, ?_⟩
    rw [forestTree_neighborSet_outer hℓ hv, Set.ncard_singleton]

/-- Each noncentral vertex has exactly the two specified children in the
unbounded word tree. -/
theorem forestTreeParent_eq_some_iff (v : ForestTreeVertex) (branch : Fin 3)
    (word : List Bool) :
    forestTreeParent v = some (branch, word) ↔
      v = some (branch, false :: word) ∨ v = some (branch, true :: word) := by
  cases v with
  | none => simp [forestTreeParent]
  | some p =>
    rcases p with ⟨b, w⟩
    cases w with
    | nil => simp [forestTreeParent]
    | cons bit w =>
      cases bit <;> simp [forestTreeParent, and_comm]

/-- The new neighbours of a leaf at the next stage are exactly its two new
children, as required in the definition of `Y_ℓ` on page 51. -/
theorem forestTree_new_neighbors {ℓ : ℕ} (branch : Fin 3) (word : List Bool)
    (hw : word.length + 1 = ℓ) :
    (forestTree (ℓ + 1)).neighborSet (some (branch, word)) \ (forestTree ℓ).verts =
      {some (branch, false :: word), some (branch, true :: word)} := by
  apply Set.ext
  intro v
  constructor
  · intro hv
    rcases hv.1.2.2 with hp | hp
    · exact (forestTreeParent_eq_some_iff v branch word).mp hp.2
    · have hd := forestTreeDepth_parent hp.1
      rw [hp.2] at hd
      change forestTreeDepth v + 1 = word.length + 1 at hd
      rw [hw] at hd
      exact False.elim (hv.2 (by change forestTreeDepth v ≤ ℓ; omega))
  · intro hv
    have hv' : v = some (branch, false :: word) ∨ v = some (branch, true :: word) := hv
    rcases hv' with rfl | rfl <;>
      refine ⟨⟨?_, ?_, Or.inl ⟨by simp, rfl⟩⟩, ?_⟩ <;>
      simp only [forestTree, forestTreeVertices, forestTreeDepth, Set.mem_ofPred_eq,
        List.length_cons] <;> omega

/-- At depth one only the centre and the three empty-word branch vertices
are present. -/
theorem forestTree_one_mem_iff (v : ForestTreeVertex) :
    v ∈ (forestTree 1).verts ↔ v = none ∨ ∃ branch, v = some (branch, []) := by
  cases v with
  | none => simp [forestTree, forestTreeVertices, forestTreeDepth]
  | some p =>
    rcases p with ⟨branch, word⟩
    simp only [forestTree, forestTreeVertices, forestTreeDepth, Set.mem_ofPred_eq,
      Option.some_ne_none, false_or, Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro h
      have hw : word.length = 0 := by omega
      exact ⟨branch, rfl, List.eq_nil_of_length_eq_zero hw⟩
    · rintro ⟨b, hb, hw⟩
      rw [hw]
      exact Nat.le_refl 1

/-- The first tree in the construction is `K_{1,3}`, as stipulated in
Graph Minors I, Section 3, page 51. The isomorphism sends the centre to
`none` and the empty word on branch `i` to `some i`. -/
def forestTree_one_iso : (forestTree 1).coe ≃g starGraph (none : Option (Fin 3)) := by
  let e : (forestTree 1).verts ≃ Option (Fin 3) :=
    { toFun := fun v ↦ v.val.map Prod.fst
      invFun := fun v ↦ ⟨v.map (fun b ↦ (b, [])), by
        cases v <;> simp [forestTree_one_mem_iff]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        obtain ⟨v, hv⟩ := v
        rcases (forestTree_one_mem_iff v).mp hv with rfl | ⟨branch, rfl⟩ <;> rfl
      right_inv := by intro v; cases v <;> rfl }
  refine { e with map_rel_iff' := ?_ }
  intro a b
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  change (starGraph (none : Option (Fin 3))).Adj (a.map Prod.fst) (b.map Prod.fst) ↔
    (forestTree 1).Adj a b
  rcases (forestTree_one_mem_iff a).mp ha with rfl | ⟨i, rfl⟩ <;>
    rcases (forestTree_one_mem_iff b).mp hb with rfl | ⟨j, rfl⟩ <;>
    simp [starGraph_adj, forestTree, forestTreeVertices, forestTreeDepth,
      forestTreeParent]

/-- Choose two distinct children of every vertex. At the centre use branches
zero and one; on a branch prepend the chosen bit. -/
def forestTreeChild (bit : Bool) : ForestTreeVertex → ForestTreeVertex
  | none => some (if bit then 1 else 0, [])
  | some (branch, word) => some (branch, bit :: word)

/-- A chosen child has the specified parent. -/
theorem forestTreeParent_child (bit : Bool) (v : ForestTreeVertex) :
    forestTreeParent (forestTreeChild bit v) = v := by
  cases v <;> rfl

/-- Children lie one level farther from the centre. -/
theorem forestTreeDepth_child (bit : Bool) (v : ForestTreeVertex) :
    forestTreeDepth (forestTreeChild bit v) = forestTreeDepth v + 1 := by
  cases v <;> rfl

/-- The two chosen children are distinct. -/
theorem forestTreeChild_false_ne_true (v : ForestTreeVertex) :
    forestTreeChild false v ≠ forestTreeChild true v := by
  cases v with
  | none => simp [forestTreeChild]
  | some p => simp [forestTreeChild]

/-- Children of different parents are distinct. -/
theorem forestTreeChild_parent_injective {a b : Bool} {v w : ForestTreeVertex}
    (h : forestTreeChild a v = forestTreeChild b w) : v = w := by
  simpa only [forestTreeParent_child] using congrArg forestTreeParent h

/-- Each chosen child occurs in the next tree. -/
theorem forestTreeChild_mem {ℓ : ℕ} {v : ForestTreeVertex}
    (hv : v ∈ (forestTree ℓ).verts) (bit : Bool) :
    forestTreeChild bit v ∈ (forestTree (ℓ + 1)).verts := by
  change forestTreeDepth (forestTreeChild bit v) ≤ ℓ + 1
  rw [forestTreeDepth_child]
  exact Nat.add_le_add_right hv 1

/-- An outer vertex's children are absent from the current tree. -/
theorem forestTreeChild_not_mem {ℓ : ℕ} {v : ForestTreeVertex}
    (hv : forestTreeDepth v = ℓ) (bit : Bool) :
    forestTreeChild bit v ∉ (forestTree ℓ).verts := by
  change ¬ forestTreeDepth (forestTreeChild bit v) ≤ ℓ
  rw [forestTreeDepth_child, hv]
  exact Nat.not_succ_le_self ℓ

/-- The chosen children are adjacent to their parent in the next tree. -/
theorem forestTree_adj_child {ℓ : ℕ} {v : ForestTreeVertex}
    (hv : v ∈ (forestTree ℓ).verts) (bit : Bool) :
    (forestTree (ℓ + 1)).Adj v (forestTreeChild bit v) := by
  have hchild : forestTreeChild bit v ≠ none := by
    cases v <;> simp [forestTreeChild]
  exact ⟨(forestTree_mono (Nat.le_succ ℓ)).1 hv, forestTreeChild_mem hv bit,
    Or.inl ⟨hchild, forestTreeParent_child bit v⟩⟩

end GraphMinor.GM01
