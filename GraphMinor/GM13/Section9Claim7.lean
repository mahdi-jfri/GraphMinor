module

public import GraphMinor.GM13.Section9Subwalls
public import GraphMinor.GM13.Section9Forest

/-!
# Graph Minors XIII, Section 9: Hole-Pairing Infrastructure for Claim (7) of (9.2)

This file develops the infrastructure for Claim (7) in the proof of **Graph Minors XIII, (9.2)**
(page 101):
1. `SubcubicTree` and `exists_disjoint_walks_of_subcubic`: In any graph `K` with `V(K).Finite` and
   maximum degree `≤ 3`, if `S : Finset α` lies in the connected component of `v₀ ∈ V(K)` and
   `4 * m ≤ S.card`, then there exist `m` disjoint pairs of distinct vertices of `S` joined by `m`
   pairwise vertex-disjoint walks in `K`.
2. `Wall.vertexSet_finite` and `Wall.adj_finset_card_le_three`: Every wall `W : Wall α β` has
   `V(W.graph).Finite` and maximum degree `≤ 3`.
3. `DrawnWall.IsFigure1.exists_vertex_planeDist_le_two`: Every point of the plane is within
   `H'.planeDist ≤ 2` of some vertex of `H'.graph`.
4. `DrawnWall.IsFigure1.exists_walk_dist_le`: Any two vertices `u, v ∈ V(H.graph)` in a Fig. 1
   wall `H` are joined by a walk in `H.graph` all of whose vertices `w` satisfy
   `H.dist w v ≤ 3 * H.dist u v + 54`.
5. `exists_hole_paired_paths`: Combining these ingredients to pair the ends `t i` (`i ∈ I`) inside
   the punctured hole around `t i₀` and route the paths `Q i` to `V(H'.graph)`.
-/

@[expose] public noncomputable section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## Part 1: Pairing Terminals in a Subcubic Connected Component -/

/-- A rooted ternary tree over `α`, used to represent spanning trees and subtrees of graphs with
maximum degree `≤ 3`. -/
inductive SubcubicTree (α : Type u) : Type u
  | nil : SubcubicTree α
  | node (val : α) (c₁ c₂ c₃ : SubcubicTree α) : SubcubicTree α

namespace SubcubicTree

/-- The list of vertices in `T`. -/
def verts : SubcubicTree α → List α
  | nil => []
  | node v c₁ c₂ c₃ => v :: (c₁.verts ++ c₂.verts ++ c₃.verts)

/-- Whether the root of a child subtree `c` (if non-empty) is adjacent to `v` in `K`. -/
def ValidEdge (K : Graph α β) (v : α) : SubcubicTree α → Prop
  | nil => True
  | node w _ _ _ => w ∈ V(K) ∧ K.Adj v w

/-- If `ValidEdge K v c` holds and `c ≠ nil`, the root of `c` belongs to `c.verts` and is adjacent
to `v` in `K`. -/
lemma exists_root_of_ne_nil {K : Graph α β} {v : α} {c : SubcubicTree α}
    (hvalid : ValidEdge K v c) (hne : c ≠ nil) :
    ∃ w ∈ c.verts, K.Adj v w := by
  cases c with
  | nil => exact absurd rfl hne
  | node w d₁ d₂ d₃ =>
    exact ⟨w, List.mem_cons_self, hvalid.2⟩

/-- All vertices and parent-child edges of `T` lie in `K`. -/
def AdjInTree (K : Graph α β) : SubcubicTree α → Prop
  | nil => True
  | node v c₁ c₂ c₃ =>
      v ∈ V(K) ∧
      ValidEdge K v c₁ ∧ ValidEdge K v c₂ ∧ ValidEdge K v c₃ ∧
      AdjInTree K c₁ ∧ AdjInTree K c₂ ∧ AdjInTree K c₃

/-- `T` is a valid simple subtree in `K` if its vertex list is duplicate-free and all its vertices
and edges lie in `K`. -/
def ValidIn (K : Graph α β) (T : SubcubicTree α) : Prop :=
  T.verts.Nodup ∧ T.AdjInTree K

lemma mem_vertexSet_of_adjInTree {K : Graph α β} {T : SubcubicTree α}
    (hT : T.AdjInTree K) {u : α} (hu : u ∈ T.verts) : u ∈ V(K) := by
  induction T with
  | nil => simp [verts] at hu
  | node v c₁ c₂ c₃ ih₁ ih₂ ih₃ =>
    rcases hT with ⟨hv, _, _, _, h₁, h₂, h₃⟩
    simp only [verts, List.mem_cons, List.mem_append] at hu
    rcases hu with rfl | (hu₁ | hu₂) | hu₃
    · exact hv
    · exact ih₁ h₁ hu₁
    · exact ih₂ h₂ hu₂
    · exact ih₃ h₃ hu₃

/-- In any non-empty `T = node v c₁ c₂ c₃` with `T.AdjInTree K`, every `u ∈ T.verts` is reachable
from the root `v` by a walk in `K` whose support lies in `T.verts`. -/
lemma exists_walk_from_root {K : Graph α β} {v : α} {c₁ c₂ c₃ : SubcubicTree α}
    (hT : (node v c₁ c₂ c₃).AdjInTree K) {u : α} (hu : u ∈ (node v c₁ c₂ c₃).verts) :
    ∃ W : GraphWalk K v u, ∀ z ∈ W.support, z ∈ (node v c₁ c₂ c₃).verts := by
  have hind : ∀ (T : SubcubicTree α), T.AdjInTree K →
      ∀ v₀ d₁ d₂ d₃, T = node v₀ d₁ d₂ d₃ → ∀ u₀ ∈ T.verts,
      ∃ W : GraphWalk K v₀ u₀, ∀ z ∈ W.support, z ∈ T.verts := by
    intro T
    induction T with
    | nil =>
      intro _ _ _ _ _ h
      cases h
    | node v₀ d₁ d₂ d₃ ih₁ ih₂ ih₃ =>
      intro hAdj v' d₁' d₂' d₃' heq u₀ hu₀
      cases heq
      rcases hAdj with ⟨hv₀, he₁, he₂, he₃, h₁, h₂, h₃⟩
      change u₀ ∈ v₀ :: (d₁.verts ++ d₂.verts ++ d₃.verts) at hu₀
      rw [List.mem_cons, List.mem_append, List.mem_append] at hu₀
      rcases hu₀ with rfl | (hu₁ | hu₂) | hu₃
      · refine ⟨GraphWalk.nil hv₀, ?_⟩
        intro z hz
        simp only [GraphWalk.support_nil, List.mem_singleton] at hz
        subst hz
        exact List.mem_cons_self
      · cases d₁ with
        | nil => simp [verts] at hu₁
        | node w₁ e₁ e₂ e₃ =>
          obtain ⟨e, hlink⟩ := he₁.2
          obtain ⟨W₁, hW₁⟩ := ih₁ h₁ w₁ e₁ e₂ e₃ rfl u₀ hu₁
          refine ⟨GraphWalk.cons hlink W₁, ?_⟩
          intro z hz
          rw [GraphWalk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz₁
          · exact List.mem_cons_self
          · change z ∈ v₀ :: ((node w₁ e₁ e₂ e₃).verts ++ d₂.verts ++ d₃.verts)
            rw [List.mem_cons, List.mem_append, List.mem_append]
            exact Or.inr (Or.inl (Or.inl (hW₁ z hz₁)))
      · cases d₂ with
        | nil => simp [verts] at hu₂
        | node w₂ e₁ e₂ e₃ =>
          obtain ⟨e, hlink⟩ := he₂.2
          obtain ⟨W₂, hW₂⟩ := ih₂ h₂ w₂ e₁ e₂ e₃ rfl u₀ hu₂
          refine ⟨GraphWalk.cons hlink W₂, ?_⟩
          intro z hz
          rw [GraphWalk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz₂
          · exact List.mem_cons_self
          · change z ∈ v₀ :: (d₁.verts ++ (node w₂ e₁ e₂ e₃).verts ++ d₃.verts)
            rw [List.mem_cons, List.mem_append, List.mem_append]
            exact Or.inr (Or.inl (Or.inr (hW₂ z hz₂)))
      · cases d₃ with
        | nil => simp [verts] at hu₃
        | node w₃ e₁ e₂ e₃ =>
          obtain ⟨e, hlink⟩ := he₃.2
          obtain ⟨W₃, hW₃⟩ := ih₃ h₃ w₃ e₁ e₂ e₃ rfl u₀ hu₃
          refine ⟨GraphWalk.cons hlink W₃, ?_⟩
          intro z hz
          rw [GraphWalk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz₃
          · exact List.mem_cons_self
          · change z ∈ v₀ :: (d₁.verts ++ d₂.verts ++ (node w₃ e₁ e₂ e₃).verts)
            rw [List.mem_cons, List.mem_append, List.mem_append]
            exact Or.inr (Or.inr (hW₃ z hz₃))
  exact hind (node v c₁ c₂ c₃) hT v c₁ c₂ c₃ rfl u hu

/-- Any two vertices `u, w ∈ T.verts` of a tree `T` with `T.AdjInTree K` are joined by a walk in `K`
whose support lies in `T.verts`. -/
lemma exists_walk_of_mem_verts {K : Graph α β} {T : SubcubicTree α}
    (hT : T.AdjInTree K) {u w : α} (hu : u ∈ T.verts) (hw : w ∈ T.verts) :
    ∃ W : GraphWalk K u w, ∀ z ∈ W.support, z ∈ T.verts := by
  cases T with
  | nil => simp [verts] at hu
  | node v c₁ c₂ c₃ =>
    obtain ⟨W₁, hW₁⟩ := exists_walk_from_root hT hu
    obtain ⟨W₂, hW₂⟩ := exists_walk_from_root hT hw
    refine ⟨W₁.reverse.append W₂, ?_⟩
    intro z hz
    rcases GraphWalk.mem_support_append W₁.reverse W₂ hz with hz₁ | hz₂
    · rw [GraphWalk.support_reverse, List.mem_reverse] at hz₁
      exact hW₁ z hz₁
    · exact hW₂ z hz₂

/-- If `K` has maximum degree `≤ 3`, `T.ValidIn K`, `v ∈ T.verts`, `u ∈ V(K)`, `u ∉ T.verts`, and
`K.Adj v u`, we can attach `u` as a leaf of `T` to obtain `T'` with `T'.ValidIn K` and
`T'.verts ~ u :: T.verts`. -/
lemma exists_insert_of_adj {K : Graph α β}
    (hdeg : ∀ x ∈ V(K), ∀ s : Finset α, (∀ y ∈ s, K.Adj x y) → s.card ≤ 3)
    {T : SubcubicTree α} (hT : T.ValidIn K)
    {v u : α} (hv : v ∈ T.verts) (huK : u ∈ V(K)) (hu_not : u ∉ T.verts)
    (hadj : K.Adj v u) :
    ∃ T' : SubcubicTree α,
      T'.ValidIn K ∧
      List.Perm T'.verts (u :: T.verts) ∧
      (∀ p : α, ValidEdge K p T → ValidEdge K p T') := by
  induction T with
  | nil => simp [verts] at hv
  | node x c₁ c₂ c₃ ih₁ ih₂ ih₃ =>
    rcases hT with ⟨hnodup, hxK, he₁, he₂, he₃, h₁, h₂, h₃⟩
    have hnodup_full : (x :: (c₁.verts ++ c₂.verts ++ c₃.verts)).Nodup := hnodup
    rcases List.nodup_cons.mp hnodup_full with ⟨hx_not_c, hnodup_c⟩
    have hnodup₁ : c₁.verts.Nodup :=
      (List.nodup_append'.mp (List.nodup_append'.mp hnodup_c).1).1
    have hnodup₂ : c₂.verts.Nodup :=
      (List.nodup_append'.mp (List.nodup_append'.mp hnodup_c).1).2.1
    have hnodup₃ : c₃.verts.Nodup :=
      (List.nodup_append'.mp hnodup_c).2.1
    by_cases hvx : v = x
    · subst hvx
      -- At least one of `c₁, c₂, c₃` must be `nil` since `v` has degree `≤ 3` in `K`
      by_cases hc₁ : c₁ = nil
      · subst hc₁
        let T' := node v (node u nil nil nil) c₂ c₃
        have hperm : List.Perm T'.verts (u :: (node v nil c₂ c₃).verts) := by
          change List.Perm (v :: (u :: (c₂.verts ++ c₃.verts))) (u :: v :: (c₂.verts ++ c₃.verts))
          exact List.Perm.swap u v (c₂.verts ++ c₃.verts)
        refine ⟨T', ⟨?_, hxK, ⟨huK, hadj⟩, he₂, he₃,
          ⟨huK, trivial, trivial, trivial, trivial, trivial, trivial⟩, h₂, h₃⟩,
          hperm, fun _ hp => hp⟩
        exact hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hu_not, hnodup_full⟩)
      · by_cases hc₂ : c₂ = nil
        · subst hc₂
          let T' := node v c₁ (node u nil nil nil) c₃
          have hperm : List.Perm T'.verts (u :: (node v c₁ nil c₃).verts) := by
            change List.Perm (v :: (c₁.verts ++ [u] ++ c₃.verts))
              (u :: v :: (c₁.verts ++ [] ++ c₃.verts))
            rw [List.append_nil]
            have h1 : List.Perm (c₁.verts ++ [u] ++ c₃.verts) (u :: (c₁.verts ++ c₃.verts)) :=
              List.Perm.append_right c₃.verts List.perm_append_comm
            exact ((List.perm_cons v).mpr h1).trans (List.Perm.swap u v (c₁.verts ++ c₃.verts))
          refine ⟨T', ⟨?_, hxK, he₁, ⟨huK, hadj⟩, he₃, h₁,
            ⟨huK, trivial, trivial, trivial, trivial, trivial, trivial⟩, h₃⟩,
            hperm, fun _ hp => hp⟩
          exact hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hu_not, hnodup_full⟩)
        · by_cases hc₃ : c₃ = nil
          · subst hc₃
            let T' := node v c₁ c₂ (node u nil nil nil)
            have hperm : List.Perm T'.verts (u :: (node v c₁ c₂ nil).verts) := by
              change List.Perm (v :: (c₁.verts ++ c₂.verts ++ [u]))
                (u :: v :: (c₁.verts ++ c₂.verts ++ []))
              rw [List.append_nil]
              have h1 : List.Perm (c₁.verts ++ c₂.verts ++ [u]) (u :: (c₁.verts ++ c₂.verts)) :=
                List.perm_append_comm
              exact ((List.perm_cons v).mpr h1).trans (List.Perm.swap u v (c₁.verts ++ c₂.verts))
            refine ⟨T', ⟨?_, hxK, he₁, he₂, ⟨huK, hadj⟩, h₁, h₂,
              ⟨huK, trivial, trivial, trivial, trivial, trivial, trivial⟩⟩,
              hperm, fun _ hp => hp⟩
            exact hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hu_not, hnodup_full⟩)
          · -- Contradiction: `c₁, c₂, c₃` and `u` give 4 distinct neighbours of `v` in `K`
            exfalso
            obtain ⟨w₁, hw₁, hadj₁⟩ := exists_root_of_ne_nil he₁ hc₁
            obtain ⟨w₂, hw₂, hadj₂⟩ := exists_root_of_ne_nil he₂ hc₂
            obtain ⟨w₃, hw₃, hadj₃⟩ := exists_root_of_ne_nil he₃ hc₃
            have hdisj₁₂ : List.Disjoint c₁.verts c₂.verts :=
              (List.nodup_append'.mp (List.nodup_append'.mp hnodup_c).1).2.2
            have hdisj₁₂_₃ : List.Disjoint (c₁.verts ++ c₂.verts) c₃.verts :=
              (List.nodup_append'.mp hnodup_c).2.2
            have hw₁₂ : w₁ ≠ w₂ := fun h => hdisj₁₂ hw₁ (h ▸ hw₂)
            have hw₁₃ : w₁ ≠ w₃ := fun h => hdisj₁₂_₃ (List.mem_append_left _ hw₁) (h ▸ hw₃)
            have hw₂₃ : w₂ ≠ w₃ := fun h => hdisj₁₂_₃ (List.mem_append_right _ hw₂) (h ▸ hw₃)
            have huw₁ : u ≠ w₁ := fun h => hu_not (by simp [verts, h, hw₁])
            have huw₂ : u ≠ w₂ := fun h => hu_not (by simp [verts, h, hw₂])
            have huw₃ : u ≠ w₃ := fun h => hu_not (by simp [verts, h, hw₃])
            let s : Finset α := {u, w₁, w₂, w₃}
            have hs_card : s.card = 4 := by
              rw [Finset.card_insert_of_notMem (by simp [huw₁, huw₂, huw₃]),
                  Finset.card_insert_of_notMem (by simp [hw₁₂, hw₁₃]),
                  Finset.card_insert_of_notMem (by simp [hw₂₃]),
                  Finset.card_singleton]
            have hs_le : s.card ≤ 3 := by
              refine hdeg v hxK s ?_
              intro y hy
              simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl | rfl | rfl
              · exact hadj
              · exact hadj₁
              · exact hadj₂
              · exact hadj₃
            omega
    · -- `v ≠ x`, so `v` lies in `c₁`, `c₂`, or `c₃`
      have hv_c : (v ∈ c₁.verts ∨ v ∈ c₂.verts) ∨ v ∈ c₃.verts := by
        simp only [verts, List.mem_cons, List.mem_append] at hv
        exact hv.resolve_left hvx
      rcases hv_c with (hv₁ | hv₂) | hv₃
      · have hu_not₁ : u ∉ c₁.verts := fun h => hu_not (by simp [verts, h])
        obtain ⟨c₁', ⟨hnodup₁', h₁'⟩, hperm₁, hedge₁⟩ :=
          ih₁ ⟨hnodup₁, h₁⟩ hv₁ hu_not₁
        let T' := node x c₁' c₂ c₃
        have hperm : List.Perm T'.verts (u :: (node x c₁ c₂ c₃).verts) := by
          change List.Perm (x :: (c₁'.verts ++ c₂.verts ++ c₃.verts))
            (u :: x :: (c₁.verts ++ c₂.verts ++ c₃.verts))
          have h1 : List.Perm (c₁'.verts ++ c₂.verts ++ c₃.verts)
              (u :: (c₁.verts ++ c₂.verts ++ c₃.verts)) :=
            List.Perm.append_right c₃.verts (List.Perm.append_right c₂.verts hperm₁)
          exact ((List.perm_cons x).mpr h1).trans (List.Perm.swap u x _)
        refine ⟨T', ⟨?_, hxK, hedge₁ x he₁, he₂, he₃, h₁', h₂, h₃⟩, hperm, fun _ hp => hp⟩
        exact hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hu_not, hnodup_full⟩)
      · have hu_not₂ : u ∉ c₂.verts := fun h => hu_not (by simp [verts, h])
        obtain ⟨c₂', ⟨hnodup₂', h₂'⟩, hperm₂, hedge₂⟩ :=
          ih₂ ⟨hnodup₂, h₂⟩ hv₂ hu_not₂
        let T' := node x c₁ c₂' c₃
        have hperm : List.Perm T'.verts (u :: (node x c₁ c₂ c₃).verts) := by
          change List.Perm (x :: (c₁.verts ++ c₂'.verts ++ c₃.verts))
            (u :: x :: (c₁.verts ++ c₂.verts ++ c₃.verts))
          have h1 : List.Perm (c₁.verts ++ c₂'.verts ++ c₃.verts)
              (u :: (c₁.verts ++ c₂.verts ++ c₃.verts)) := by
            change List.Perm (c₁.verts ++ c₂'.verts ++ c₃.verts)
              ((u :: (c₁.verts ++ c₂.verts)) ++ c₃.verts)
            refine List.Perm.append_right c₃.verts ?_
            exact (List.Perm.append_left c₁.verts hperm₂).trans
              (List.Perm.trans List.perm_append_comm
                (List.Perm.cons u List.perm_append_comm))
          exact ((List.perm_cons x).mpr h1).trans (List.Perm.swap u x _)
        refine ⟨T', ⟨?_, hxK, he₁, hedge₂ x he₂, he₃, h₁, h₂', h₃⟩, hperm, fun _ hp => hp⟩
        exact hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hu_not, hnodup_full⟩)
      · have hu_not₃ : u ∉ c₃.verts := fun h => hu_not (by simp [verts, h])
        obtain ⟨c₃', ⟨hnodup₃', h₃'⟩, hperm₃, hedge₃⟩ :=
          ih₃ ⟨hnodup₃, h₃⟩ hv₃ hu_not₃
        let T' := node x c₁ c₂ c₃'
        have hperm : List.Perm T'.verts (u :: (node x c₁ c₂ c₃).verts) := by
          change List.Perm (x :: (c₁.verts ++ c₂.verts ++ c₃'.verts))
            (u :: x :: (c₁.verts ++ c₂.verts ++ c₃.verts))
          have h1 : List.Perm (c₁.verts ++ c₂.verts ++ c₃'.verts)
              (u :: (c₁.verts ++ c₂.verts ++ c₃.verts)) :=
            (List.Perm.append_left (c₁.verts ++ c₂.verts) hperm₃).trans
              (List.Perm.trans List.perm_append_comm
                (List.Perm.cons u List.perm_append_comm))
          exact ((List.perm_cons x).mpr h1).trans (List.Perm.swap u x _)
        refine ⟨T', ⟨?_, hxK, he₁, he₂, hedge₃ x he₃, h₁, h₂, h₃'⟩, hperm, fun _ hp => hp⟩
        exact hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hu_not, hnodup_full⟩)

/-- Along any walk `W : GraphWalk K a b` from `a ∈ X` to `b ∉ X`, there is an edge of `K` from some
`v ∈ X` to some `u ∈ V(K) \ X`. -/
lemma exists_adj_step_of_walk {K : Graph α β} {X : Set α} {a b : α}
    (W : GraphWalk K a b) (ha : a ∈ X) (hb : b ∉ X) :
    ∃ v ∈ X, ∃ u ∈ V(K), u ∉ X ∧ K.Adj v u := by
  induction W with
  | nil _ => exact False.elim (hb ha)
  | @cons x y z e hlink W' ih =>
    by_cases hy : y ∈ X
    · exact ih hy hb
    · exact ⟨x, ha, y, hlink.right_mem, hy, ⟨e, hlink⟩⟩

/-- Every finite graph `K` with maximum degree `≤ 3` and vertex `v₀ ∈ V(K)` has a `SubcubicTree`
`T` with `T.ValidIn K` whose vertex list `T.verts` contains every vertex reachable from `v₀` in `K`. -/
lemma exists_spanning_subcubicTree {K : Graph α β}
    (hfin : V(K).Finite)
    (hdeg : ∀ x ∈ V(K), ∀ s : Finset α, (∀ y ∈ s, K.Adj x y) → s.card ≤ 3)
    {v₀ : α} (hv₀ : v₀ ∈ V(K)) :
    ∃ T : SubcubicTree α,
      T.ValidIn K ∧
      ∀ z : α, Nonempty (GraphWalk K v₀ z) → z ∈ T.verts := by
  have hind : ∀ (n : ℕ) (T : SubcubicTree α),
      T.ValidIn K → v₀ ∈ T.verts → (V(K) \ {x | x ∈ T.verts}).ncard = n →
      ∃ T' : SubcubicTree α,
        T'.ValidIn K ∧ ∀ z : α, Nonempty (GraphWalk K v₀ z) → z ∈ T'.verts := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hT hv₀T hcard
      by_cases hall : ∀ z : α, Nonempty (GraphWalk K v₀ z) → z ∈ T.verts
      · exact ⟨T, hT, hall⟩
      · push Not at hall
        rcases hall with ⟨z, ⟨W⟩, hz_not⟩
        obtain ⟨v, hvT, u, huK, hu_not, hadj⟩ :=
          exists_adj_step_of_walk (X := {x | x ∈ T.verts}) W hv₀T hz_not
        obtain ⟨T₁, hT₁, hperm, _⟩ := exists_insert_of_adj hdeg hT hvT huK hu_not hadj
        have hv₀T₁ : v₀ ∈ T₁.verts := hperm.mem_iff.mpr (List.mem_cons_of_mem u hv₀T)
        have hssub : V(K) \ {x | x ∈ T₁.verts} ⊂ V(K) \ {x | x ∈ T.verts} := by
          refine ⟨?_, ?_⟩
          · intro w ⟨hwK, hw_not₁⟩
            exact ⟨hwK, fun hwT => hw_not₁ (hperm.mem_iff.mpr (List.mem_cons_of_mem u hwT))⟩
          · intro hsub
            have hu_diff : u ∈ V(K) \ {x | x ∈ T.verts} := ⟨huK, hu_not⟩
            exact (hsub hu_diff).2 (hperm.mem_iff.mpr List.mem_cons_self)
        have hlt : (V(K) \ {x | x ∈ T₁.verts}).ncard < n := by
          rw [← hcard]
          exact Set.ncard_lt_ncard hssub (hfin.subset sdiff_subset)
        exact ih _ hlt T₁ hT₁ hv₀T₁ rfl
  let T₀ : SubcubicTree α := node v₀ nil nil nil
  have hT₀ : T₀.ValidIn K :=
    ⟨List.nodup_singleton v₀, hv₀, trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact hind _ T₀ hT₀ List.mem_cons_self rfl

/-- The number of elements of `S : Finset α` that appear in `T.verts`. -/
def count (S : Finset α) (T : SubcubicTree α) : ℕ :=
  (S.filter (fun x => x ∈ T.verts)).card

@[simp]
lemma count_nil (S : Finset α) : count S nil = 0 := by
  simp [count, verts]

lemma count_node_le (S : Finset α) (v : α) (c₁ c₂ c₃ : SubcubicTree α) :
    count S (node v c₁ c₂ c₃) ≤ 1 + count S c₁ + count S c₂ + count S c₃ := by
  have hsub : S.filter (fun x => x ∈ (node v c₁ c₂ c₃).verts) ⊆
      insert v ((S.filter (fun x => x ∈ c₁.verts)) ∪
        (S.filter (fun x => x ∈ c₂.verts)) ∪
        (S.filter (fun x => x ∈ c₃.verts))) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rcases hx with ⟨hxS, hxV⟩
    simp only [verts, List.mem_cons, List.mem_append] at hxV
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    rcases hxV with rfl | (h1 | h2) | h3
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Or.inl ⟨hxS, h1⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨hxS, h2⟩))
    · exact Or.inr (Or.inr ⟨hxS, h3⟩)
  calc
    count S (node v c₁ c₂ c₃) ≤
        (insert v ((S.filter (fun x => x ∈ c₁.verts)) ∪
          (S.filter (fun x => x ∈ c₂.verts)) ∪
          (S.filter (fun x => x ∈ c₃.verts)))).card :=
      Finset.card_le_card hsub
    _ ≤ 1 + ((S.filter (fun x => x ∈ c₁.verts)) ∪
          (S.filter (fun x => x ∈ c₂.verts)) ∪
          (S.filter (fun x => x ∈ c₃.verts))).card := by
      have := Finset.card_insert_le v
        ((S.filter (fun x => x ∈ c₁.verts)) ∪
          (S.filter (fun x => x ∈ c₂.verts)) ∪
          (S.filter (fun x => x ∈ c₃.verts)))
      omega
    _ ≤ 1 + ((S.filter (fun x => x ∈ c₁.verts)).card +
          (S.filter (fun x => x ∈ c₂.verts)).card +
          (S.filter (fun x => x ∈ c₃.verts)).card) := by
      have h1 := Finset.card_union_le
        ((S.filter (fun x => x ∈ c₁.verts)) ∪ (S.filter (fun x => x ∈ c₂.verts)))
        (S.filter (fun x => x ∈ c₃.verts))
      have h2 := Finset.card_union_le
        (S.filter (fun x => x ∈ c₁.verts))
        (S.filter (fun x => x ∈ c₂.verts))
      omega
    _ = 1 + count S c₁ + count S c₂ + count S c₃ := by
      dsimp [count]; omega

lemma count_le_add_of_diff {S : Finset α} {T T' : SubcubicTree α} {k : ℕ}
    (hk : (S.filter (fun x => x ∈ T.verts ∧ x ∉ T'.verts)).card ≤ k) :
    count S T ≤ count S T' + k := by
  have hsub : S.filter (fun x => x ∈ T.verts) ⊆
      S.filter (fun x => x ∈ T'.verts) ∪
      S.filter (fun x => x ∈ T.verts ∧ x ∉ T'.verts) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hx' : x ∈ T'.verts
    · exact Or.inl ⟨hx.1, hx'⟩
    · exact Or.inr ⟨hx.1, hx.2, hx'⟩
  calc
    count S T ≤ (S.filter (fun x => x ∈ T'.verts) ∪
        S.filter (fun x => x ∈ T.verts ∧ x ∉ T'.verts)).card :=
      Finset.card_le_card hsub
    _ ≤ count S T' + (S.filter (fun x => x ∈ T.verts ∧ x ∉ T'.verts)).card :=
      Finset.card_union_le _ _
    _ ≤ count S T' + k := Nat.add_le_add_left hk _

/-- Peeling one pair of distinct terminals `s₁, s₂ ∈ S` from `T : SubcubicTree α` when
`2 ≤ count S T`, removing at most 4 elements of `S`. -/
lemma exists_peel_one {K : Graph α β} {S : Finset α} {T : SubcubicTree α}
    (hT : T.ValidIn K) (h2 : 2 ≤ count S T) :
    ∃ (T' : SubcubicTree α) (s₁ s₂ : α) (W : GraphWalk K s₁ s₂),
      T'.ValidIn K ∧
      (∀ x ∈ T'.verts, x ∈ T.verts) ∧
      (∀ p : α, ValidEdge K p T → ValidEdge K p T') ∧
      (S.filter (fun x => x ∈ T.verts ∧ x ∉ T'.verts)).card ≤ 4 ∧
      s₁ ∈ S ∧ s₂ ∈ S ∧ s₁ ≠ s₂ ∧
      s₁ ∈ T.verts ∧ s₁ ∉ T'.verts ∧
      s₂ ∈ T.verts ∧ s₂ ∉ T'.verts ∧
      (∀ z ∈ W.support, z ∈ T.verts ∧ z ∉ T'.verts) := by
  induction T with
  | nil =>
    rw [count_nil] at h2
    omega
  | node v c₁ c₂ c₃ ih₁ ih₂ ih₃ =>
    rcases hT with ⟨hnodup, hvK, he₁, he₂, he₃, h₁, h₂, h₃⟩
    simp only [verts] at hnodup
    rw [List.nodup_cons] at hnodup
    rcases hnodup with ⟨hv_not_c, hnodup_c⟩
    have hnodup₁ : c₁.verts.Nodup :=
      (List.nodup_append'.mp (List.nodup_append'.mp hnodup_c).1).1
    have hnodup₂ : c₂.verts.Nodup :=
      (List.nodup_append'.mp (List.nodup_append'.mp hnodup_c).1).2.1
    have hnodup₃ : c₃.verts.Nodup :=
      (List.nodup_append'.mp hnodup_c).2.1
    have hdisj₁₂ : List.Disjoint c₁.verts c₂.verts :=
      (List.nodup_append'.mp (List.nodup_append'.mp hnodup_c).1).2.2
    have hdisj₁₂_₃ : List.Disjoint (c₁.verts ++ c₂.verts) c₃.verts :=
      (List.nodup_append'.mp hnodup_c).2.2
    by_cases hc₁ : 2 ≤ count S c₁
    · obtain ⟨c₁', s₁, s₂, W, ⟨hnodup₁', h₁'⟩, hsub₁, hedge₁, hcard₁,
        hs₁S, hs₂S, hne, hs₁_in, hs₁_out, hs₂_in, hs₂_out, hW⟩ := ih₁ ⟨hnodup₁, h₁⟩ hc₁
      let T' := node v c₁' c₂ c₃
      have hnot_rest : ∀ {z : α}, z ∈ c₁.verts → z ≠ v ∧ z ∉ c₂.verts ∧ z ∉ c₃.verts := by
        intro z hz
        refine ⟨?_, ?_, ?_⟩
        · rintro rfl; exact hv_not_c (by simp [hz])
        · exact fun hz₂ => hdisj₁₂ hz hz₂
        · exact fun hz₃ => hdisj₁₂_₃ (List.mem_append_left _ hz) hz₃
      have hmem_diff : ∀ {z : α}, z ∈ c₁.verts ∧ z ∉ c₁'.verts ↔
          z ∈ (node v c₁ c₂ c₃).verts ∧ z ∉ T'.verts := by
        intro z
        simp only [T', verts, List.mem_cons, List.mem_append]
        constructor
        · rintro ⟨hz₁, hz₁'⟩
          obtain ⟨h1, h2, h3⟩ := hnot_rest hz₁
          exact ⟨Or.inr (Or.inl (Or.inl hz₁)), by tauto⟩
        · rintro ⟨rfl | (hz₁ | hz₂) | hz₃, hnot⟩
          · exact False.elim (hnot (Or.inl rfl))
          · exact ⟨hz₁, fun hz₁' => hnot (Or.inr (Or.inl (Or.inl hz₁')))⟩
          · exact False.elim (hnot (Or.inr (Or.inl (Or.inr hz₂))))
          · exact False.elim (hnot (Or.inr (Or.inr hz₃)))
      have hT'_valid : T'.ValidIn K := by
        refine ⟨?_, hvK, hedge₁ v he₁, he₂, he₃, h₁', h₂, h₃⟩
        simp only [T', verts]
        rw [List.nodup_cons]
        refine ⟨?_, ?_⟩
        · intro h
          simp only [List.mem_append] at h
          rcases h with (h1 | h2) | h3
          · exact hv_not_c (by simp [hsub₁ _ h1])
          · exact hv_not_c (by simp [h2])
          · exact hv_not_c (by simp [h3])
        · rw [List.nodup_append']
          refine ⟨List.nodup_append'.mpr ⟨hnodup₁', hnodup₂, fun a ha₁ ha₂ => hdisj₁₂ (hsub₁ a ha₁) ha₂⟩,
            hnodup₃, ?_⟩
          intro a ha₁₂ ha₃
          rcases List.mem_append.mp ha₁₂ with ha₁ | ha₂
          · exact hdisj₁₂_₃ (List.mem_append_left _ (hsub₁ a ha₁)) ha₃
          · exact hdisj₁₂_₃ (List.mem_append_right _ ha₂) ha₃
      refine ⟨T', s₁, s₂, W, hT'_valid, ?_, fun _ hp => hp, ?_, hs₁S, hs₂S, hne,
        (hmem_diff.mp ⟨hs₁_in, hs₁_out⟩).1, (hmem_diff.mp ⟨hs₁_in, hs₁_out⟩).2,
        (hmem_diff.mp ⟨hs₂_in, hs₂_out⟩).1, (hmem_diff.mp ⟨hs₂_in, hs₂_out⟩).2,
        fun z hz => hmem_diff.mp (hW z hz)⟩
      · intro x hx
        simp only [T', verts, List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with rfl | (h1 | h2) | h3
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inl (hsub₁ x h1)))
        · exact Or.inr (Or.inl (Or.inr h2))
        · exact Or.inr (Or.inr h3)
      · have hfilter_eq :
            S.filter (fun x => x ∈ (node v c₁ c₂ c₃).verts ∧ x ∉ T'.verts) =
            S.filter (fun x => x ∈ c₁.verts ∧ x ∉ c₁'.verts) := by
          ext x
          simp only [Finset.mem_filter, hmem_diff]
        rw [hfilter_eq]
        exact hcard₁
    · by_cases hc₂ : 2 ≤ count S c₂
      · obtain ⟨c₂', s₁, s₂, W, ⟨hnodup₂', h₂'⟩, hsub₂, hedge₂, hcard₂,
          hs₁S, hs₂S, hne, hs₁_in, hs₁_out, hs₂_in, hs₂_out, hW⟩ := ih₂ ⟨hnodup₂, h₂⟩ hc₂
        let T' := node v c₁ c₂' c₃
        have hnot_rest : ∀ {z : α}, z ∈ c₂.verts → z ≠ v ∧ z ∉ c₁.verts ∧ z ∉ c₃.verts := by
          intro z hz
          refine ⟨?_, ?_, ?_⟩
          · rintro rfl; exact hv_not_c (by simp [hz])
          · exact fun hz₁ => hdisj₁₂ hz₁ hz
          · exact fun hz₃ => hdisj₁₂_₃ (List.mem_append_right _ hz) hz₃
        have hmem_diff : ∀ {z : α}, z ∈ c₂.verts ∧ z ∉ c₂'.verts ↔
            z ∈ (node v c₁ c₂ c₃).verts ∧ z ∉ T'.verts := by
          intro z
          simp only [T', verts, List.mem_cons, List.mem_append]
          constructor
          · rintro ⟨hz₂, hz₂'⟩
            obtain ⟨h1, h2, h3⟩ := hnot_rest hz₂
            exact ⟨Or.inr (Or.inl (Or.inr hz₂)), by tauto⟩
          · rintro ⟨rfl | (hz₁ | hz₂) | hz₃, hnot⟩
            · exact False.elim (hnot (Or.inl rfl))
            · exact False.elim (hnot (Or.inr (Or.inl (Or.inl hz₁))))
            · exact ⟨hz₂, fun hz₂' => hnot (Or.inr (Or.inl (Or.inr hz₂')))⟩
            · exact False.elim (hnot (Or.inr (Or.inr hz₃)))
        have hT'_valid : T'.ValidIn K := by
          refine ⟨?_, hvK, he₁, hedge₂ v he₂, he₃, h₁, h₂', h₃⟩
          simp only [T', verts]
          rw [List.nodup_cons]
          refine ⟨?_, ?_⟩
          · intro h
            simp only [List.mem_append] at h
            rcases h with (h1 | h2) | h3
            · exact hv_not_c (by simp [h1])
            · exact hv_not_c (by simp [hsub₂ _ h2])
            · exact hv_not_c (by simp [h3])
          · rw [List.nodup_append']
            refine ⟨List.nodup_append'.mpr ⟨hnodup₁, hnodup₂', fun a ha₁ ha₂ => hdisj₁₂ ha₁ (hsub₂ a ha₂)⟩,
              hnodup₃, ?_⟩
            intro a ha₁₂ ha₃
            rcases List.mem_append.mp ha₁₂ with ha₁ | ha₂
            · exact hdisj₁₂_₃ (List.mem_append_left _ ha₁) ha₃
            · exact hdisj₁₂_₃ (List.mem_append_right _ (hsub₂ a ha₂)) ha₃
        refine ⟨T', s₁, s₂, W, hT'_valid, ?_, fun _ hp => hp, ?_, hs₁S, hs₂S, hne,
          (hmem_diff.mp ⟨hs₁_in, hs₁_out⟩).1, (hmem_diff.mp ⟨hs₁_in, hs₁_out⟩).2,
          (hmem_diff.mp ⟨hs₂_in, hs₂_out⟩).1, (hmem_diff.mp ⟨hs₂_in, hs₂_out⟩).2,
          fun z hz => hmem_diff.mp (hW z hz)⟩
        · intro x hx
          simp only [T', verts, List.mem_cons, List.mem_append] at hx ⊢
          rcases hx with rfl | (h1 | h2) | h3
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (Or.inl h1))
          · exact Or.inr (Or.inl (Or.inr (hsub₂ x h2)))
          · exact Or.inr (Or.inr h3)
        · have hfilter_eq :
              S.filter (fun x => x ∈ (node v c₁ c₂ c₃).verts ∧ x ∉ T'.verts) =
              S.filter (fun x => x ∈ c₂.verts ∧ x ∉ c₂'.verts) := by
            ext x
            simp only [Finset.mem_filter, hmem_diff]
          rw [hfilter_eq]
          exact hcard₂
      · by_cases hc₃ : 2 ≤ count S c₃
        · obtain ⟨c₃', s₁, s₂, W, ⟨hnodup₃', h₃'⟩, hsub₃, hedge₃, hcard₃,
            hs₁S, hs₂S, hne, hs₁_in, hs₁_out, hs₂_in, hs₂_out, hW⟩ := ih₃ ⟨hnodup₃, h₃⟩ hc₃
          let T' := node v c₁ c₂ c₃'
          have hnot_rest : ∀ {z : α}, z ∈ c₃.verts → z ≠ v ∧ z ∉ c₁.verts ∧ z ∉ c₂.verts := by
            intro z hz
            refine ⟨?_, ?_, ?_⟩
            · rintro rfl; exact hv_not_c (by simp [hz])
            · exact fun hz₁ => hdisj₁₂_₃ (List.mem_append_left _ hz₁) hz
            · exact fun hz₂ => hdisj₁₂_₃ (List.mem_append_right _ hz₂) hz
          have hmem_diff : ∀ {z : α}, z ∈ c₃.verts ∧ z ∉ c₃'.verts ↔
              z ∈ (node v c₁ c₂ c₃).verts ∧ z ∉ T'.verts := by
            intro z
            simp only [T', verts, List.mem_cons, List.mem_append]
            constructor
            · rintro ⟨hz₃, hz₃'⟩
              obtain ⟨h1, h2, h3⟩ := hnot_rest hz₃
              exact ⟨Or.inr (Or.inr hz₃), by tauto⟩
            · rintro ⟨rfl | (hz₁ | hz₂) | hz₃, hnot⟩
              · exact False.elim (hnot (Or.inl rfl))
              · exact False.elim (hnot (Or.inr (Or.inl (Or.inl hz₁))))
              · exact False.elim (hnot (Or.inr (Or.inl (Or.inr hz₂))))
              · exact ⟨hz₃, fun hz₃' => hnot (Or.inr (Or.inr hz₃'))⟩
          have hT'_valid : T'.ValidIn K := by
            refine ⟨?_, hvK, he₁, he₂, hedge₃ v he₃, h₁, h₂, h₃'⟩
            simp only [T', verts]
            rw [List.nodup_cons]
            refine ⟨?_, ?_⟩
            · intro h
              simp only [List.mem_append] at h
              rcases h with (h1 | h2) | h3
              · exact hv_not_c (by simp [h1])
              · exact hv_not_c (by simp [h2])
              · exact hv_not_c (by simp [hsub₃ _ h3])
            · rw [List.nodup_append']
              refine ⟨List.nodup_append'.mpr ⟨hnodup₁, hnodup₂, hdisj₁₂⟩, hnodup₃', ?_⟩
              intro a ha₁₂ ha₃
              exact hdisj₁₂_₃ ha₁₂ (hsub₃ a ha₃)
          refine ⟨T', s₁, s₂, W, hT'_valid, ?_, fun _ hp => hp, ?_, hs₁S, hs₂S, hne,
            (hmem_diff.mp ⟨hs₁_in, hs₁_out⟩).1, (hmem_diff.mp ⟨hs₁_in, hs₁_out⟩).2,
            (hmem_diff.mp ⟨hs₂_in, hs₂_out⟩).1, (hmem_diff.mp ⟨hs₂_in, hs₂_out⟩).2,
            fun z hz => hmem_diff.mp (hW z hz)⟩
          · intro x hx
            simp only [T', verts, List.mem_cons, List.mem_append] at hx ⊢
            rcases hx with rfl | (h1 | h2) | h3
            · exact Or.inl rfl
            · exact Or.inr (Or.inl (Or.inl h1))
            · exact Or.inr (Or.inl (Or.inr h2))
            · exact Or.inr (Or.inr (hsub₃ x h3))
          · have hfilter_eq :
                S.filter (fun x => x ∈ (node v c₁ c₂ c₃).verts ∧ x ∉ T'.verts) =
                S.filter (fun x => x ∈ c₃.verts ∧ x ∉ c₃'.verts) := by
              ext x
              simp only [Finset.mem_filter, hmem_diff]
            rw [hfilter_eq]
            exact hcard₃
        · -- Base case: `count S c₁ ≤ 1`, `count S c₂ ≤ 1`, `count S c₃ ≤ 1`, so `count S T ≤ 4`
          have hle4 : count S (node v c₁ c₂ c₃) ≤ 4 := by
            have := count_node_le S v c₁ c₂ c₃
            omega
          have h1_lt : 1 < (S.filter (fun x => x ∈ (node v c₁ c₂ c₃).verts)).card := by
            dsimp [count] at h2
            omega
          obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp h1_lt
          rw [Finset.mem_filter] at hs₁ hs₂
          have hAdj : (node v c₁ c₂ c₃).AdjInTree K :=
            ⟨hvK, he₁, he₂, he₃, h₁, h₂, h₃⟩
          obtain ⟨W, hW⟩ := exists_walk_of_mem_verts hAdj hs₁.2 hs₂.2
          refine ⟨nil, s₁, s₂, W, ⟨List.nodup_nil, trivial⟩, ?_, fun _ _ => trivial, ?_,
            hs₁.1, hs₂.1, hne, hs₁.2, by simp [verts], hs₂.2, by simp [verts],
            fun z hz => ⟨hW z hz, by simp [verts]⟩⟩
          · intro x hx; simp [verts] at hx
          · simpa [verts, count] using hle4

/-- Peeling `m` disjoint pairs of terminals from `T : SubcubicTree α` when `4 * m ≤ count S T`. -/
lemma exists_peel_many {K : Graph α β} {S : Finset α} :
    ∀ (m : ℕ) {T : SubcubicTree α},
      T.ValidIn K → 4 * m ≤ count S T →
      ∃ (s₁ s₂ : Fin m → α) (W : ∀ c : Fin m, GraphWalk K (s₁ c) (s₂ c)),
        (∀ c, s₁ c ∈ S ∧ s₂ c ∈ S ∧ s₁ c ≠ s₂ c) ∧
        (∀ c, s₁ c ∈ T.verts ∧ s₂ c ∈ T.verts ∧ ∀ z ∈ (W c).support, z ∈ T.verts) ∧
        (∀ c₁ c₂, c₁ ≠ c₂ →
          s₁ c₁ ≠ s₁ c₂ ∧ s₁ c₁ ≠ s₂ c₂ ∧ s₂ c₁ ≠ s₁ c₂ ∧ s₂ c₁ ≠ s₂ c₂ ∧
          Disjoint {z | z ∈ (W c₁).support} {z | z ∈ (W c₂).support}) := by
  intro m
  induction m with
  | zero =>
    intro T _ _
    exact ⟨Fin.elim0, Fin.elim0, fun c => Fin.elim0 c,
      fun c => Fin.elim0 c, fun c => Fin.elim0 c, fun c₁ => Fin.elim0 c₁⟩
  | succ m ih =>
    intro T hT hcount
    have h2 : 2 ≤ count S T := by omega
    obtain ⟨T', a₁, a₂, W₀, hT', hsub, _, hcard_diff,
      ha₁S, ha₂S, hne₀, ha₁_in, ha₁_out, ha₂_in, ha₂_out, hW₀⟩ :=
      exists_peel_one hT h2
    have hcount' : 4 * m ≤ count S T' := by
      have hle := count_le_add_of_diff hcard_diff
      omega
    obtain ⟨s₁', s₂', W', hS', hverts', hdisj'⟩ := ih hT' hcount'
    let s₁ : Fin (m + 1) → α := Fin.cons a₁ s₁'
    let s₂ : Fin (m + 1) → α := Fin.cons a₂ s₂'
    let W : ∀ c : Fin (m + 1), GraphWalk K (s₁ c) (s₂ c) :=
      Fin.cons W₀ W'
    refine ⟨s₁, s₂, W, ?_, ?_, ?_⟩
    · intro c
      refine Fin.cases ?_ ?_ c
      · exact ⟨ha₁S, ha₂S, hne₀⟩
      · intro c'
        exact hS' c'
    · intro c
      refine Fin.cases ?_ ?_ c
      · exact ⟨ha₁_in, ha₂_in, fun z hz => (hW₀ z hz).1⟩
      · intro c'
        obtain ⟨h1, h2, h3⟩ := hverts' c'
        exact ⟨hsub _ h1, hsub _ h2, fun z hz => hsub _ (h3 z hz)⟩
    · intro c₁ c₂
      refine Fin.cases ?_ (fun i₁ => ?_) c₁
      · refine Fin.cases (fun h => absurd rfl h) (fun i₂ _ => ?_) c₂
        obtain ⟨hs₁_i₂, hs₂_i₂, hW_i₂⟩ := hverts' i₂
        simp only [s₁, s₂, W, Fin.cons_zero, Fin.cons_succ]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h; exact ha₁_out (h ▸ hs₁_i₂)
        · intro h; exact ha₁_out (h ▸ hs₂_i₂)
        · intro h; exact ha₂_out (h ▸ hs₁_i₂)
        · intro h; exact ha₂_out (h ▸ hs₂_i₂)
        · rw [Set.disjoint_left]
          intro z hz₀ hz'
          exact (hW₀ z hz₀).2 (hW_i₂ z hz')
      · refine Fin.cases (fun _ => ?_) (fun i₂ hne => ?_) c₂
        · obtain ⟨hs₁_i₁, hs₂_i₁, hW_i₁⟩ := hverts' i₁
          simp only [s₁, s₂, W, Fin.cons_zero, Fin.cons_succ]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro h; exact ha₁_out (h.symm ▸ hs₁_i₁)
          · intro h; exact ha₂_out (h.symm ▸ hs₁_i₁)
          · intro h; exact ha₁_out (h.symm ▸ hs₂_i₁)
          · intro h; exact ha₂_out (h.symm ▸ hs₂_i₁)
          · rw [Set.disjoint_left]
            intro z hz' hz₀
            exact (hW₀ z hz₀).2 (hW_i₁ z hz')
        · have hi₁₂ : i₁ ≠ i₂ := fun h => hne (congrArg Fin.succ h)
          dsimp [s₁, s₂, W]
          exact hdisj' i₁ i₂ hi₁₂

end SubcubicTree

/-- In any finite graph `K` with maximum degree `≤ 3`, if every vertex in `S : Finset α` is
reachable in `K` from `v₀ ∈ V(K)` and `4 * m ≤ S.card`, then there exist `m` disjoint pairs of
distinct vertices of `S` joined by `m` pairwise vertex-disjoint walks in `K`. -/
theorem exists_disjoint_walks_of_subcubic {K : Graph α β}
    (hfin : V(K).Finite)
    (hdeg : ∀ x ∈ V(K), ∀ s : Finset α, (∀ y ∈ s, K.Adj x y) → s.card ≤ 3)
    {v₀ : α} (hv₀ : v₀ ∈ V(K))
    {S : Finset α} {m : ℕ} (hS_card : 4 * m ≤ S.card)
    (hreach : ∀ x ∈ S, Nonempty (GraphWalk K v₀ x)) :
    ∃ (s₁ s₂ : Fin m → α) (W : ∀ c : Fin m, GraphWalk K (s₁ c) (s₂ c)),
      (∀ c, s₁ c ∈ S ∧ s₂ c ∈ S ∧ s₁ c ≠ s₂ c) ∧
      (∀ c₁ c₂, c₁ ≠ c₂ →
        s₁ c₁ ≠ s₁ c₂ ∧ s₁ c₁ ≠ s₂ c₂ ∧ s₂ c₁ ≠ s₁ c₂ ∧ s₂ c₁ ≠ s₂ c₂ ∧
        Disjoint {z | z ∈ (W c₁).support} {z | z ∈ (W c₂).support}) := by
  obtain ⟨T, hT, hspan⟩ := SubcubicTree.exists_spanning_subcubicTree hfin hdeg hv₀
  have hcount_eq : SubcubicTree.count S T = S.card := by
    dsimp [SubcubicTree.count]
    rw [Finset.filter_true_of_mem (fun x hx => hspan x (hreach x hx))]
  obtain ⟨s₁, s₂, W, hS, _, hdisj⟩ :=
    SubcubicTree.exists_peel_many m hT (hcount_eq ▸ hS_card)
  exact ⟨s₁, s₂, W, hS, hdisj⟩

/-! ## Part 2: Finiteness and Subcubic Degree of a Wall -/

/-- `elementaryWallVerts h` is finite for every `h : ℕ`. -/
lemma elementaryWallVerts_finite (h : ℕ) : (elementaryWallVerts h).Finite := by
  have hsub : elementaryWallVerts h ⊆
      (↑(Finset.Iic (2 * h + 1) ×ˢ Finset.Iic h) : Set (ℕ × ℕ)) := by
    intro p hp
    simp only [Finset.coe_product, Finset.coe_Iic, mem_prod, mem_Iic]
    exact ⟨hp.1, hp.2.1⟩
  exact (Finset.finite_toSet _).subset hsub

/-- `E(elementaryWall h)` is finite for every `h : ℕ`. -/
lemma elementaryWall_edgeSet_finite (h : ℕ) : E(elementaryWall h).Finite := by
  have hfinV := elementaryWallVerts_finite h
  have hsub : E(elementaryWall h) ⊆
      (fun pq : (ℕ × ℕ) × (ℕ × ℕ) => s(pq.1, pq.2)) ''
        (elementaryWallVerts h ×ˢ elementaryWallVerts h) := by
    rintro e ⟨p, q, hadj, rfl⟩
    exact ⟨(p, q), ⟨hadj.1, hadj.2.1⟩, rfl⟩
  exact ((hfinV.prod hfinV).image _).subset hsub

/-- Every wall `W : Wall α β` has finite vertex set `V(W.graph).Finite`. -/
theorem Wall.vertexSet_finite (W : Wall α β) : V(W.graph).Finite := by
  have hfin_baseV : V(W.baseGraph).Finite := by
    have : Finite V(elementaryWall W.height) := (elementaryWallVerts_finite W.height).to_subtype
    have : Finite V(W.baseGraph) := Finite.of_equiv _ W.baseIso.vertexEquiv
    exact Set.toFinite V(W.baseGraph)
  have hfin_baseE : E(W.baseGraph).Finite := by
    have : Finite E(elementaryWall W.height) := (elementaryWall_edgeSet_finite W.height).to_subtype
    have : Finite E(W.baseGraph) := Finite.of_equiv _ W.baseIso.edgeEquiv
    exact Set.toFinite E(W.baseGraph)
  rw [W.vertexSet_eq]
  refine hfin_baseV.union (hfin_baseE.biUnion ?_)
  intro e he
  obtain ⟨u, v, _, hpath, _, _⟩ := W.path_of_edge e he
  exact hpath.vertexSet_finite

/-- Every edge `e ∈ W.edges` of a walk `W : GraphWalk P a b` has both of its endpoints in
`W.support`. -/
lemma GraphWalk.endpoints_mem_support_of_mem_edges {P : Graph α β} {a b : α}
    (W : GraphWalk P a b) {e : β} (he : e ∈ W.edges) {x y : α} (hlink : P.IsLink e x y) :
    x ∈ W.support ∧ y ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons u v c e₀ hlink₀ W_tail ih =>
    simp only [GraphWalk.edges, List.mem_cons] at he
    rw [GraphWalk.support_cons]
    rcases he with rfl | he_tail
    · rcases P.eq_or_eq_of_isLink_of_isLink hlink hlink₀ with h1 | h1
      · have hy := hlink.right_unique (h1 ▸ hlink₀)
        subst h1 hy
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ W_tail.start_mem_support⟩
      · have hy := hlink.right_unique (h1 ▸ hlink₀.symm)
        subst h1 hy
        exact ⟨List.mem_cons_of_mem _ W_tail.start_mem_support, List.mem_cons_self⟩
    · obtain ⟨hx, hy⟩ := ih he_tail
      exact ⟨List.mem_cons_of_mem u hx, List.mem_cons_of_mem u hy⟩

/-- At the start `a` of a simple walk `W : GraphWalk P a b`, all edges in `W.edges` incident to `a`
have the same other endpoint. -/
lemma GraphWalk.exists_unique_adj_start_of_isSimple {P : Graph α β} {a b : α}
    (W : GraphWalk P a b) (hW : W.IsSimple) :
    ∃ y₀ : α, ∀ {e : β} {w : α}, e ∈ W.edges → P.IsLink e a w → w = y₀ := by
  cases W with
  | nil _ =>
    refine ⟨a, ?_⟩
    intro e w he _
    simp [GraphWalk.edges] at he
  | @cons a y₀ b e₀ hlink₀ W_tail =>
    have hnd : (a :: W_tail.support).Nodup := hW
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨ha_not, _⟩
    have hay₀ : a ≠ y₀ := fun h => ha_not (h ▸ W_tail.start_mem_support)
    refine ⟨y₀, ?_⟩
    intro e w he hlink
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he_tail
    · rcases P.eq_or_eq_of_isLink_of_isLink hlink hlink₀ with h1 | h1
      · exact hlink.right_unique (h1 ▸ hlink₀)
      · exact False.elim (hay₀ h1)
    · exfalso
      exact ha_not (GraphWalk.endpoints_mem_support_of_mem_edges W_tail he_tail hlink).1

/-- At either endpoint `v ∈ {a, b}` of a path `IsGraphPathWithEnds G P a b`, `v` has at most one
neighbour in `P`. -/
lemma IsGraphPathWithEnds.exists_unique_adj_of_end {G P : Graph α β} {a b v : α}
    (hP : IsGraphPathWithEnds G P a b) (hv : v = a ∨ v = b) :
    ∃ y₀ : α, ∀ {w : α}, P.Adj v w → w = y₀ := by
  have hstart : ∀ {u₁ u₂ : α}, IsGraphPathWithEnds G P u₁ u₂ →
      ∃ y₀ : α, ∀ {w : α}, P.Adj u₁ w → w = y₀ := by
    intro u₁ u₂ hP'
    rcases hP' with ⟨_, W, hW, _, hEP⟩
    obtain ⟨y₀, hy₀⟩ := GraphWalk.exists_unique_adj_start_of_isSimple W hW
    refine ⟨y₀, ?_⟩
    rintro w ⟨e, hlink⟩
    have he : e ∈ W.edges := by
      have heP : e ∈ E(P) := hlink.edge_mem
      rwa [hEP, mem_ofPred_eq] at heP
    exact hy₀ he hlink
  rcases hv with rfl | rfl
  · exact hstart hP
  · exact hstart hP.symm

/-- Along a simple walk `W : GraphWalk P a b`, every vertex `v` is incident to edges of `W.edges`
going to at most two vertices `x₀, y₀`. -/
lemma GraphWalk.exists_two_adj_of_isSimple {P : Graph α β} {a b : α}
    (W : GraphWalk P a b) (hW : W.IsSimple) (v : α) :
    ∃ x₀ y₀ : α, ∀ {e : β} {w : α}, e ∈ W.edges → P.IsLink e v w → w = x₀ ∨ w = y₀ := by
  induction W with
  | nil _ =>
    refine ⟨v, v, ?_⟩
    intro e w he _
    simp [GraphWalk.edges] at he
  | @cons a b₀ c e₀ hlink₀ W_tail ih =>
    have hnd : (a :: W_tail.support).Nodup := hW
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨ha_not, hW_tail⟩
    by_cases hva : v = a
    · subst hva
      obtain ⟨y₀, hy₀⟩ :=
        GraphWalk.exists_unique_adj_start_of_isSimple (GraphWalk.cons hlink₀ W_tail) hW
      exact ⟨y₀, y₀, fun he hlink => Or.inl (hy₀ he hlink)⟩
    · by_cases hvb₀ : v = b₀
      · subst hvb₀
        obtain ⟨y₀, hy₀⟩ := GraphWalk.exists_unique_adj_start_of_isSimple W_tail hW_tail
        refine ⟨a, y₀, ?_⟩
        intro e w he hlink
        simp only [GraphWalk.edges, List.mem_cons] at he
        rcases he with rfl | he_tail
        · rcases P.eq_or_eq_of_isLink_of_isLink hlink hlink₀.symm with h1 | h1
          · exact Or.inl (hlink.right_unique (h1 ▸ hlink₀.symm))
          · exact False.elim (hva h1)
        · exact Or.inr (hy₀ he_tail hlink)
      · obtain ⟨x₀, y₀, hxy₀⟩ := ih hW_tail
        refine ⟨x₀, y₀, ?_⟩
        intro e w he hlink
        simp only [GraphWalk.edges, List.mem_cons] at he
        rcases he with rfl | he_tail
        · exfalso
          rcases P.eq_or_eq_of_isLink_of_isLink hlink hlink₀ with h1 | h1
          · exact hva h1
          · exact hvb₀ h1
        · exact hxy₀ he_tail hlink

/-- Every vertex `p = (x, y)` in `elementaryWall h` has at most 3 neighbours in `elementaryWall h`. -/
lemma elementaryWallAdj_eq_or_eq_or_eq (h : ℕ) (p : ℕ × ℕ) :
    let q₁ : ℕ × ℕ := (p.1 + 1, p.2)
    let q₂ : ℕ × ℕ := (p.1 - 1, p.2)
    let q₃ : ℕ × ℕ := if Odd (p.1 + p.2) then (p.1, p.2 + 1) else (p.1, p.2 - 1)
    ∀ {q : ℕ × ℕ}, elementaryWallAdj h p q → q = q₁ ∨ q = q₂ ∨ q = q₃ := by
  intro q₁ q₂ q₃ q hadj
  rcases hadj with ⟨_, _, ⟨hy, hx1 | hx2⟩ | ⟨hx, ⟨hy1, hodd⟩ | ⟨hy2, hodd⟩⟩⟩
  · exact Or.inl (Prod.ext (by dsimp [q₁]; omega) (by dsimp [q₁]; omega))
  · exact Or.inr (Or.inl (Prod.ext (by dsimp [q₂]; omega) (by dsimp [q₂]; omega)))
  · right; right
    dsimp [q₃]
    simp only [hodd, ↓reduceIte]
    exact Prod.ext (by omega) (by omega)
  · right; right
    dsimp [q₃]
    have hnot_odd : ¬ Odd (p.1 + p.2) := by
      rcases hodd with ⟨m, hm⟩
      rw [Nat.not_odd_iff_even]
      exact ⟨m + 1, by omega⟩
    simp only [hnot_odd, ↓reduceIte]
    exact Prod.ext (by omega) (by omega)

/-- In any wall `W : Wall α β`, every vertex `v ∈ V(W.graph)` is adjacent in `W.graph` to at most
3 vertices: there exist `y₁, y₂, y₃ : α` such that every `w` with `W.graph.Adj v w` belongs to
`{y₁, y₂, y₃}`. -/
theorem Wall.exists_three_adj (W : Wall α β) (v : α) :
    ∃ y₁ y₂ y₃ : α, ∀ {w : α}, W.graph.Adj v w → w = y₁ ∨ w = y₂ ∨ w = y₃ := by
  by_cases hv_base : v ∈ V(W.baseGraph)
  · -- `v` is a branch vertex corresponding to `p ∈ elementaryWallVerts W.height`
    let p_sub : V(elementaryWall W.height) := W.baseIso.vertexEquiv.symm ⟨v, hv_base⟩
    let p : ℕ × ℕ := p_sub.1
    have hp_eq : (W.baseIso.vertexEquiv p_sub).1 = v := by
      simp [p_sub]
    let q : Fin 3 → ℕ × ℕ
      | ⟨0, _⟩ => (p.1 + 1, p.2)
      | ⟨1, _⟩ => (p.1 - 1, p.2)
      | ⟨2, _⟩ => if Odd (p.1 + p.2) then (p.1, p.2 + 1) else (p.1, p.2 - 1)
    have hex_y : ∀ i : Fin 3, ∃ y_i : α,
        ∀ (hadj : elementaryWallAdj W.height p (q i)) {w : α},
          (W.subdivisionPaths (W.baseEdge hadj)).Adj v w → w = y_i := by
      intro i
      by_cases hadj : elementaryWallAdj W.height p (q i)
      · have hpath := W.isGraphPathWithEnds_baseEdge hadj
        have hv_start : v = W.branchVertex p hadj.1 := by
          dsimp [Wall.branchVertex]
          have hsub : (⟨p, hadj.1⟩ : V(elementaryWall W.height)) = p_sub := Subtype.ext rfl
          rw [hsub, hp_eq]
        obtain ⟨y_i, hy_i⟩ :=
          IsGraphPathWithEnds.exists_unique_adj_of_end hpath (Or.inl hv_start)
        exact ⟨y_i, fun _ _ h => hy_i h⟩
      · exact ⟨v, fun h => False.elim (hadj h)⟩
    choose y hy using hex_y
    refine ⟨y 0, y 1, y 2, ?_⟩
    rintro w ⟨f, hlink⟩
    have hf : f ∈ E(W.graph) := hlink.edge_mem
    rw [W.edgeSet_eq, mem_iUnion₂] at hf
    rcases hf with ⟨e, he_base, hf_e⟩
    obtain ⟨u₁, u₂, hlink_base, hpath_e, _, hinter_e⟩ := W.path_of_edge e he_base
    have hlink_e : (W.subdivisionPaths e).IsLink f v w :=
      (hpath_e.le.isLink_iff hf_e).mpr hlink
    have hv_ends : v = u₁ ∨ v = u₂ := by
      have : v ∈ V(W.subdivisionPaths e) ∩ V(W.baseGraph) := ⟨hlink_e.left_mem, hv_base⟩
      rwa [hinter_e, mem_insert_iff, mem_singleton_iff] at this
    have hlink_base' : W.baseGraph.IsLink e v (if v = u₁ then u₂ else u₁) := by
      rcases hv_ends with rfl | rfl
      · simpa using hlink_base
      · split_ifs with h12
        · subst h12; exact hlink_base
        · exact hlink_base.symm
    let u' := if v = u₁ then u₂ else u₁
    have hu'_base : u' ∈ V(W.baseGraph) := hlink_base'.right_mem
    let q_sub : V(elementaryWall W.height) := W.baseIso.vertexEquiv.symm ⟨u', hu'_base⟩
    let e_sub : E(elementaryWall W.height) := W.baseIso.edgeEquiv.symm ⟨e, he_base⟩
    have hlink_elem : (elementaryWall W.height).IsLink e_sub.1 p_sub.1 q_sub.1 := by
      refine (W.baseIso.isLink_iff e_sub p_sub q_sub).mpr ?_
      simpa [e_sub, p_sub, q_sub] using hlink_base'
    have hadj_pq : elementaryWallAdj W.height p q_sub.1 := hlink_elem.1
    have hadj_sub : (W.subdivisionPaths (W.baseEdge hadj_pq)).Adj v w := by
      have he_eq : W.baseEdge hadj_pq = e := by
        dsimp [Wall.baseEdge]
        have hsub : elementaryWallEdge hadj_pq = e_sub := by
          apply Subtype.ext
          exact hlink_elem.2.symm
        rw [hsub]
        simp [e_sub]
      rw [he_eq]
      exact ⟨f, hlink_e⟩
    have hcases := elementaryWallAdj_eq_or_eq_or_eq W.height p hadj_pq
    rcases hcases with h0 | h1 | h2
    · have hq0 : q_sub.1 = q 0 := h0
      revert hadj_pq hadj_sub
      rw [hq0]
      intro hadj_pq hadj_sub
      exact Or.inl (hy 0 hadj_pq hadj_sub)
    · have hq1 : q_sub.1 = q 1 := h1
      revert hadj_pq hadj_sub
      rw [hq1]
      intro hadj_pq hadj_sub
      exact Or.inr (Or.inl (hy 1 hadj_pq hadj_sub))
    · have hq2 : q_sub.1 = q 2 := h2
      revert hadj_pq hadj_sub
      rw [hq2]
      intro hadj_pq hadj_sub
      exact Or.inr (Or.inr (hy 2 hadj_pq hadj_sub))
  · -- `v ∉ V(W.baseGraph)` is an internal vertex of at most one subdivision path
    by_cases hex_e : ∃ e ∈ E(W.baseGraph), v ∈ V(W.subdivisionPaths e)
    · rcases hex_e with ⟨e, he_base, hv_e⟩
      obtain ⟨u₁, u₂, _, hpath_e, _, _⟩ := W.path_of_edge e he_base
      rcases hpath_e with ⟨hPe_le, W₀, hW₀, _, hEPe⟩
      obtain ⟨x₀, y₀, hxy₀⟩ := GraphWalk.exists_two_adj_of_isSimple W₀ hW₀ v
      refine ⟨x₀, y₀, y₀, ?_⟩
      rintro w ⟨f, hlink⟩
      have hf : f ∈ E(W.graph) := hlink.edge_mem
      rw [W.edgeSet_eq, mem_iUnion₂] at hf
      rcases hf with ⟨e', he'_base, hf_e'⟩
      obtain ⟨_, _, _, hpath_e', _, _⟩ := W.path_of_edge e' he'_base
      have hlink_e' : (W.subdivisionPaths e').IsLink f v w :=
        (hpath_e'.le.isLink_iff hf_e').mpr hlink
      have hee' : e = e' := by
        by_contra hne
        exact hv_base ((W.paths_disjoint e he_base e' he'_base hne).2 ⟨hv_e, hlink_e'.left_mem⟩)
      subst hee'
      have hf_W₀ : f ∈ W₀.edges := by
        rwa [hEPe, mem_ofPred_eq] at hf_e'
      rcases hxy₀ hf_W₀ hlink_e' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · refine ⟨v, v, v, ?_⟩
      rintro w ⟨f, hlink⟩
      exfalso
      have hf : f ∈ E(W.graph) := hlink.edge_mem
      rw [W.edgeSet_eq, mem_iUnion₂] at hf
      rcases hf with ⟨e, he_base, hf_e⟩
      obtain ⟨_, _, _, hpath_e, _, _⟩ := W.path_of_edge e he_base
      have hlink_e : (W.subdivisionPaths e).IsLink f v w :=
        (hpath_e.le.isLink_iff hf_e).mpr hlink
      exact hex_e ⟨e, he_base, hlink_e.left_mem⟩

/-- Every finite set `s : Finset α` of neighbours of `v` in `W.graph` (or any subgraph `K ≤ W.graph`)
has cardinality at most `3`. -/
theorem Wall.adj_finset_card_le_three (W : Wall α β) {K : Graph α β} (hKW : K ≤ W.graph)
    (v : α) (s : Finset α) (hs : ∀ w ∈ s, K.Adj v w) :
    s.card ≤ 3 := by
  obtain ⟨y₁, y₂, y₃, hy⟩ := W.exists_three_adj v
  have hsub : s ⊆ ({y₁, y₂, y₃} : Finset α) := by
    intro w hw
    obtain ⟨f, hlink⟩ := hs w hw
    have hadjW : W.graph.Adj v w := ⟨f, hlink.mono hKW⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hy hadjW
  calc
    s.card ≤ ({y₁, y₂, y₃} : Finset α).card := Finset.card_le_card hsub
    _ ≤ 3 := by
      have h1 := Finset.card_insert_le y₁ ({y₂, y₃} : Finset α)
      have h2 := Finset.card_insert_le y₂ ({y₃} : Finset α)
      have h3 : ({y₃} : Finset α).card = 1 := Finset.card_singleton y₃
      omega

/-! ## Part 3: Every Plane Point is Within `planeDist ≤ 2` of a Wall Vertex -/

/-- In any Fig. 1 drawn wall `H'`, every point `pt : EuclideanPlane` is within `H'.planeDist ≤ 2`
of `H'.vertexPoint v` for some vertex `v ∈ V(H'.graph)`. -/
theorem DrawnWall.IsFigure1.exists_vertex_planeDist_le_two
    {H' : DrawnWall α β} (hfig : H'.IsFigure1) (pt : EuclideanPlane) :
    ∃ v ∈ V(H'.graph), H'.planeDist pt (H'.vertexPoint v) ≤ 2 := by
  rcases hfig with ⟨φ, Γ, hΓ, hU, hV⟩
  have hh2 := H'.two_le_height
  have hh1 : 1 ≤ H'.height := by omega
  let s : ℝ × ℝ := fig1PlaneEquiv.symm (φ.symm pt)
  have hpt_eq : pt = φ (fig1PlaneEquiv s) := by simp [s]
  let q : ℤ × ℤ := cellUp (cellCode s)
  have hq : q ∈ squaresAbove (cellCode s) := ⟨isSquareCell_cellUp _, cellLE_cellUp _⟩
  set F : ℤ × ℤ := wallFace H'.height q
  rcases isBrick_or_eq_outFace_wallFace H'.height q with hBrick | hOut
  · -- `F` is a brick `(F.1, F.2)` with `1 ≤ F.1 ≤ 2 * H'.height` and `0 ≤ F.2 < H'.height`
    have hBrick' : 0 ≤ F.2 ∧ F.2 < (H'.height : ℤ) ∧
        1 ≤ F.1 ∧ F.1 ≤ 2 * (H'.height : ℤ) ∧ (F.1 - F.2) % 2 = 0 := hBrick
    let p₀ : ℕ × ℕ := (F.1.toNat, F.2.toNat)
    have hp₀ : p₀ ∈ elementaryWallVerts H'.height := by
      dsimp [elementaryWallVerts, p₀]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    let v : α := H'.branchVertex p₀ hp₀
    have hv : v ∈ V(H'.graph) := H'.toWall.branchVertex_mem_vertexSet p₀ hp₀
    refine ⟨v, hv, ?_⟩
    have hvp_eq : H'.vertexPoint v = φ (fig1PlaneEquiv (latticePoint p₀)) := by
      rw [hV v hv, hΓ.branchVertex_point p₀ hp₀ hv]
    have hdist_eq : H'.planeDist pt (H'.vertexPoint v) =
        planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H'.height))
          (fig1PlaneEquiv s) (fig1PlaneEquiv (latticePoint p₀)) := by
      dsimp [DrawnWall.planeDist]
      rw [hpt_eq, hU, hvp_eq, planeWallDist_image_homeomorph,
        hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
    rw [hdist_eq]
    by_cases hcode : cellCode s = cellCode (latticePoint p₀)
    · exact planeWallDist_fig1_le_two_of_cellCode_eq H'.height hcode
    · let q' : ℤ × ℤ := brickSq F
      have hq' : q' ∈ squaresAbove (cellCode (latticePoint p₀)) := by
        rw [cellCode_latticePoint, mem_squaresAbove_iff]
        dsimp [q', brickSq, p₀]
        omega
      have hq'_face : wallFace H'.height q' = F := wallFace_brickSq hBrick
      have hle := planeWallDist_fig1_le hh1 H'.even_height hcode hq hq'
      have hind₁ := cellInd_le_one (fig1WallCells H'.height) (cellCode s)
      have hind₂ := cellInd_le_one (fig1WallCells H'.height) (cellCode (latticePoint p₀))
      change _ ≤ _ + _ + faceDist H'.height F (wallFace H'.height q') at hle
      rw [hq'_face, faceDist_self (Or.inl hBrick)] at hle
      omega
  · -- `F = outFace`: pick the bottom-left branch vertex `p₀ = (1, 0)`
    let p₀ : ℕ × ℕ := (1, 0)
    have hp₀ : p₀ ∈ elementaryWallVerts H'.height := by
      dsimp [elementaryWallVerts, p₀]
      refine ⟨by omega, by omega, by decide, ?_⟩
      intro h; have := congrArg Prod.snd h; dsimp at this; omega
    let v : α := H'.branchVertex p₀ hp₀
    have hv : v ∈ V(H'.graph) := H'.toWall.branchVertex_mem_vertexSet p₀ hp₀
    refine ⟨v, hv, ?_⟩
    have hvp_eq : H'.vertexPoint v = φ (fig1PlaneEquiv (latticePoint p₀)) := by
      rw [hV v hv, hΓ.branchVertex_point p₀ hp₀ hv]
    have hdist_eq : H'.planeDist pt (H'.vertexPoint v) =
        planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H'.height))
          (fig1PlaneEquiv s) (fig1PlaneEquiv (latticePoint p₀)) := by
      dsimp [DrawnWall.planeDist]
      rw [hpt_eq, hU, hvp_eq, planeWallDist_image_homeomorph,
        hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
    rw [hdist_eq]
    by_cases hcode : cellCode s = cellCode (latticePoint p₀)
    · exact planeWallDist_fig1_le_two_of_cellCode_eq H'.height hcode
    · let q' : ℤ × ℤ := (2 * (0 : ℤ) + 1, 2 * (-1 : ℤ) + 1)
      have hq' : q' ∈ squaresAbove (cellCode (latticePoint p₀)) := by
        rw [cellCode_latticePoint, mem_squaresAbove_iff]
        dsimp [q', p₀]
        omega
      have hq'_face : wallFace H'.height q' = outFace := by
        rw [wallFace_square, ite_eq_right_iff]
        intro
        omega
      have hle := planeWallDist_fig1_le hh1 H'.even_height hcode hq hq'
      have hind₁ := cellInd_le_one (fig1WallCells H'.height) (cellCode s)
      have hind₂ := cellInd_le_one (fig1WallCells H'.height) (cellCode (latticePoint p₀))
      change _ ≤ _ + _ + faceDist H'.height F (wallFace H'.height q') at hle
      rw [show F = outFace from hOut, hq'_face, faceDist_out_out] at hle
      omega

/-! ## Part 4: Cell Distance Bounds and Bounded-Distance Walks in a Fig. 1 Wall -/

lemma cellDist_row_le (𝒰 : Set (ℤ × ℤ)) (b : ℤ) :
    ∀ (k : ℕ) (a : ℤ),
      cellDist 𝒰 (a, b) (a + k, b) ≤ k ∧ cellDist 𝒰 (a + k, b) (a, b) ≤ k
  | 0, a => by simp [cellDist_self]
  | k + 1, a => by
    obtain ⟨h1, h2⟩ := cellDist_row_le 𝒰 b k a
    have hstep1 : cellDist 𝒰 (a + k, b) (a + k + 1, b) ≤ 1 :=
      (cellDist_le_of_cellRel 𝒰 (cellRel_succ_fst (a + k) b)).trans (cellInd_le_one 𝒰 _)
    have hstep2 : cellDist 𝒰 (a + k + 1, b) (a + k, b) ≤ 1 :=
      (cellDist_le_of_cellRel 𝒰 (cellRel_succ_fst (a + k) b).symm).trans (cellInd_le_one 𝒰 _)
    have ht1 := cellDist_triangle 𝒰 (a, b) (a + k, b) (a + k + 1, b)
    have ht2 := cellDist_triangle 𝒰 (a + k + 1, b) (a + k, b) (a, b)
    have he : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rw [he]
    omega

lemma cellDist_col_le (𝒰 : Set (ℤ × ℤ)) (a : ℤ) :
    ∀ (k : ℕ) (b : ℤ),
      cellDist 𝒰 (a, b) (a, b + k) ≤ k ∧ cellDist 𝒰 (a, b + k) (a, b) ≤ k
  | 0, b => by simp [cellDist_self]
  | k + 1, b => by
    obtain ⟨h1, h2⟩ := cellDist_col_le 𝒰 a k b
    have hstep1 : cellDist 𝒰 (a, b + k) (a, b + k + 1) ≤ 1 :=
      (cellDist_le_of_cellRel 𝒰 (cellRel_succ_snd a (b + k))).trans (cellInd_le_one 𝒰 _)
    have hstep2 : cellDist 𝒰 (a, b + k + 1) (a, b + k) ≤ 1 :=
      (cellDist_le_of_cellRel 𝒰 (cellRel_succ_snd a (b + k)).symm).trans (cellInd_le_one 𝒰 _)
    have ht1 := cellDist_triangle 𝒰 (a, b) (a, b + k) (a, b + k + 1)
    have ht2 := cellDist_triangle 𝒰 (a, b + k + 1) (a, b + k) (a, b)
    have he : b + ((k + 1 : ℕ) : ℤ) = b + k + 1 := by push_cast; ring
    rw [he]
    omega

/-- For any two cells `c, d : ℤ × ℤ`, `cellDist 𝒰 c d` is at most the `L¹` distance between `c`
and `d`. -/
lemma cellDist_le_natAbs (𝒰 : Set (ℤ × ℤ)) (c d : ℤ × ℤ) :
    cellDist 𝒰 c d ≤ (c.1 - d.1).natAbs + (c.2 - d.2).natAbs := by
  rcases c with ⟨c1, c2⟩
  rcases d with ⟨d1, d2⟩
  have hrow : cellDist 𝒰 (c1, c2) (d1, c2) ≤ (c1 - d1).natAbs := by
    rcases le_total c1 d1 with h | h
    · have hk : c1 + ((d1 - c1).natAbs : ℤ) = d1 := by omega
      have h1 := (cellDist_row_le 𝒰 c2 (d1 - c1).natAbs c1).1
      rw [hk] at h1
      omega
    · have hk : d1 + ((c1 - d1).natAbs : ℤ) = c1 := by omega
      have h2 := (cellDist_row_le 𝒰 c2 (c1 - d1).natAbs d1).2
      rwa [hk] at h2
  have hcol : cellDist 𝒰 (d1, c2) (d1, d2) ≤ (c2 - d2).natAbs := by
    rcases le_total c2 d2 with h | h
    · have hk : c2 + ((d2 - c2).natAbs : ℤ) = d2 := by omega
      have h1 := (cellDist_col_le 𝒰 d1 (d2 - c2).natAbs c2).1
      rw [hk] at h1
      omega
    · have hk : d2 + ((c2 - d2).natAbs : ℤ) = c2 := by omega
      have h2 := (cellDist_col_le 𝒰 d1 (c2 - d2).natAbs d2).2
      rwa [hk] at h2
  have htri := cellDist_triangle 𝒰 (c1, c2) (d1, c2) (d1, d2)
  omega

/-- Upper bound on `planeWallDist` by the `L¹` difference of cell codes. -/
lemma planeWallDist_fig1_le_natAbs (h : ℕ) (s t : ℝ × ℝ) :
    planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h))
        (fig1PlaneEquiv s) (fig1PlaneEquiv t) ≤
      2 + ((cellCode s).1 - (cellCode t).1).natAbs + ((cellCode s).2 - (cellCode t).2).natAbs := by
  by_cases hst : cellCode s = cellCode t
  · have h2 := planeWallDist_fig1_le_two_of_cellCode_eq h hst
    omega
  · have h1 := planeWallDist_cellSet_le_cellDist (fig1WallCells_not_square h) hst
    have h2 := cellInd_le_one (fig1WallCells h) (cellCode s)
    have h3 := cellDist_le_natAbs (fig1WallCells h) (cellCode s) (cellCode t)
    omega

/-- Any cell `c` within `L¹`-margin `M` of the boundary of `[0, 4h + 2] × [0, 2h]` has
`cellDist` at most `M + 3` to and from `outBase = (-1, -1)`. -/
lemma cellDist_outBase_le_of_margin {h : ℕ} (hh : 1 ≤ h) (he : Even h)
    {c : ℤ × ℤ} {M : ℕ}
    (hc1 : 0 ≤ c.1 ∧ c.1 ≤ 4 * (h : ℤ) + 2)
    (hc2 : 0 ≤ c.2 ∧ c.2 ≤ 2 * (h : ℤ))
    (hmargin : c.2 ≤ M ∨ 2 * (h : ℤ) - M ≤ c.2 ∨ c.1 ≤ M ∨ 4 * (h : ℤ) + 2 - M ≤ c.1) :
    cellDist (fig1WallCells h) c outBase ≤ M + 3 ∧
    cellDist (fig1WallCells h) outBase c ≤ M + 3 := by
  have hsq_out : ∀ (x y : ℤ), wallFace h (2 * x + 1, 2 * y + 1) = outFace →
      cellDist (fig1WallCells h) c (2 * x + 1, 2 * y + 1) ≤ M + 3 →
      cellDist (fig1WallCells h) (2 * x + 1, 2 * y + 1) c ≤ M + 3 →
      cellDist (fig1WallCells h) c outBase ≤ M + 3 ∧
      cellDist (fig1WallCells h) outBase c ≤ M + 3 := by
    intro x y hout hd1 hd2
    have h1 := cellDist_out_base hh he hout
    have h2 : cellDist (fig1WallCells h) outBase (2 * x + 1, 2 * y + 1) = 0 := by
      rw [outBase_eq, cellDist_square_comm, ← outBase_eq]
      exact h1
    have ht1 := cellDist_triangle (fig1WallCells h) c (2 * x + 1, 2 * y + 1) outBase
    have ht2 := cellDist_triangle (fig1WallCells h) outBase (2 * x + 1, 2 * y + 1) c
    omega
  rcases hmargin with hy_lo | hy_hi | hx_lo | hx_hi
  · refine hsq_out (c.1 / 2) (-1) ?_ ?_ ?_
    · rw [wallFace_square, ite_eq_right_iff]
      intro; omega
    · have := cellDist_le_natAbs (fig1WallCells h) c (2 * (c.1 / 2) + 1, 2 * (-1 : ℤ) + 1)
      omega
    · have := cellDist_le_natAbs (fig1WallCells h) (2 * (c.1 / 2) + 1, 2 * (-1 : ℤ) + 1) c
      omega
  · refine hsq_out (c.1 / 2) h ?_ ?_ ?_
    · rw [wallFace_square, ite_eq_right_iff]
      intro; omega
    · have := cellDist_le_natAbs (fig1WallCells h) c (2 * (c.1 / 2) + 1, 2 * (h : ℤ) + 1)
      omega
    · have := cellDist_le_natAbs (fig1WallCells h) (2 * (c.1 / 2) + 1, 2 * (h : ℤ) + 1) c
      omega
  · refine hsq_out (-1) (c.2 / 2) ?_ ?_ ?_
    · rw [wallFace_square, ite_eq_right_iff]
      intro; omega
    · have := cellDist_le_natAbs (fig1WallCells h) c (2 * (-1 : ℤ) + 1, 2 * (c.2 / 2) + 1)
      omega
    · have := cellDist_le_natAbs (fig1WallCells h) (2 * (-1 : ℤ) + 1, 2 * (c.2 / 2) + 1) c
      omega
  · refine hsq_out (2 * h + 1) (c.2 / 2) ?_ ?_ ?_
    · rw [wallFace_square, ite_eq_right_iff]
      intro; omega
    · have := cellDist_le_natAbs (fig1WallCells h) c (2 * (2 * (h : ℤ) + 1) + 1, 2 * (c.2 / 2) + 1)
      omega
    · have := cellDist_le_natAbs (fig1WallCells h) (2 * (2 * (h : ℤ) + 1) + 1, 2 * (c.2 / 2) + 1) c
      omega

/-- Any two points `s, t` whose cell codes lie in `[0, 4h + 2] × [0, 2h]` within `L¹`-margin `M`
of the boundary have `planeWallDist ≤ 2 * M + 8`. -/
lemma planeWallDist_fig1_le_of_margin {h : ℕ} (hh : 1 ≤ h) (he : Even h)
    {s t : ℝ × ℝ} {M : ℕ}
    (hs1 : 0 ≤ (cellCode s).1 ∧ (cellCode s).1 ≤ 4 * (h : ℤ) + 2)
    (hs2 : 0 ≤ (cellCode s).2 ∧ (cellCode s).2 ≤ 2 * (h : ℤ))
    (hsm : (cellCode s).2 ≤ M ∨ 2 * (h : ℤ) - M ≤ (cellCode s).2 ∨
      (cellCode s).1 ≤ M ∨ 4 * (h : ℤ) + 2 - M ≤ (cellCode s).1)
    (ht1 : 0 ≤ (cellCode t).1 ∧ (cellCode t).1 ≤ 4 * (h : ℤ) + 2)
    (ht2 : 0 ≤ (cellCode t).2 ∧ (cellCode t).2 ≤ 2 * (h : ℤ))
    (htm : (cellCode t).2 ≤ M ∨ 2 * (h : ℤ) - M ≤ (cellCode t).2 ∨
      (cellCode t).1 ≤ M ∨ 4 * (h : ℤ) + 2 - M ≤ (cellCode t).1) :
    planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h))
      (fig1PlaneEquiv s) (fig1PlaneEquiv t) ≤ 2 * M + 8 := by
  by_cases hst : cellCode s = cellCode t
  · have h2 := planeWallDist_fig1_le_two_of_cellCode_eq h hst
    omega
  · have h1 := planeWallDist_cellSet_le_cellDist (fig1WallCells_not_square h) hst
    have h2 := cellInd_le_one (fig1WallCells h) (cellCode s)
    have h3 := (cellDist_outBase_le_of_margin hh he hs1 hs2 hsm).1
    have h4 := (cellDist_outBase_le_of_margin hh he ht1 ht2 htm).2
    have htri := cellDist_triangle (fig1WallCells h) (cellCode s) outBase (cellCode t)
    omega

/-- If a square `q ∈ squaresAbove (cellCode (latticePoint p))` has `wallFace h q = outFace` or
`outDepth h (wallFace h q) ≤ D`, then `p` is within margin `(2 * D + 2, D + 1)` of the boundary of
`[0, 2h] × [0, h]`. -/
lemma outDepth_margin_of_squaresAbove {h D : ℕ} {p : ℕ × ℕ} {q : ℤ × ℤ}
    (hq : q ∈ squaresAbove (cellCode (latticePoint p)))
    (hout : wallFace h q = outFace ∨ (IsBrick h (wallFace h q) ∧ outDepth h (wallFace h q) ≤ D)) :
    p.2 ≤ D + 1 ∨ h - D - 1 ≤ p.2 ∨ p.1 ≤ 2 * D + 2 ∨ 2 * h - 2 * D - 2 ≤ p.1 := by
  obtain ⟨x, y, rfl, -⟩ := exists_of_mem_squaresAbove hq
  rw [cellCode_latticePoint, mem_squaresAbove_iff] at hq
  have hwf := wallFace_square h x y
  rcases hout with ho | ⟨hb, hd⟩
  · split_ifs at hwf with hcond
    · exfalso
      have : (x + (x + y) % 2, y) = (0, -1) := hwf.symm.trans ho
      have := congrArg Prod.snd this
      dsimp at this
      omega
    · omega
  · split_ifs at hwf with hcond
    · rw [hwf] at hd
      unfold outDepth at hd
      dsimp at hd
      omega
    · exfalso
      exact not_isBrick_outFace h (hwf ▸ hb)

/-- Pure integer arithmetic helper for `hexDist_bound_of_squaresAbove`. -/
lemma hexDist_coord_bound {D : ℕ} {p₁ p₂ : ℕ × ℕ} {x₁ y₁ x₂ y₂ : ℤ}
    (hx₁ : x₁ = (p₁.1 : ℤ) ∨ x₁ = (p₁.1 : ℤ) - 1)
    (hy₁ : y₁ = (p₁.2 : ℤ) ∨ y₁ = (p₁.2 : ℤ) - 1)
    (hx₂ : x₂ = (p₂.1 : ℤ) ∨ x₂ = (p₂.1 : ℤ) - 1)
    (hy₂ : y₂ = (p₂.2 : ℤ) ∨ y₂ = (p₂.2 : ℤ) - 1)
    (hd : hexDist (x₁ + (x₁ + y₁) % 2, y₁) (x₂ + (x₂ + y₂) % 2, y₂) ≤ D) :
    ((p₁.1 : ℤ) - (p₂.1 : ℤ)).natAbs ≤ 2 * D + 3 ∧
    ((p₁.2 : ℤ) - (p₂.2 : ℤ)).natAbs ≤ D + 2 := by
  have hd' : max (max (y₁ - y₂) (y₂ - y₁))
      ((max ((x₁ + (x₁ + y₁) % 2) - (x₂ + (x₂ + y₂) % 2))
        ((x₂ + (x₂ + y₂) % 2) - (x₁ + (x₁ + y₁) % 2)) +
        max (y₁ - y₂) (y₂ - y₁)) / 2) ≤ D := hd
  clear hd
  have hdy : y₁ - y₂ ≤ D ∧ y₂ - y₁ ≤ D := by omega
  have hdX : (x₁ + (x₁ + y₁) % 2) - (x₂ + (x₂ + y₂) % 2) ≤ 2 * (D : ℤ) + 1 ∧
      (x₂ + (x₂ + y₂) % 2) - (x₁ + (x₁ + y₁) % 2) ≤ 2 * (D : ℤ) + 1 := by omega
  clear hd'
  omega

/-- If squares `q₁ ∈ squaresAbove (cellCode (latticePoint p₁))` and
`q₂ ∈ squaresAbove (cellCode (latticePoint p₂))` have brick faces `F₁, F₂` with
`hexDist F₁ F₂ ≤ D`, then `|p₁.1 - p₂.1| ≤ 2 * D + 3` and `|p₁.2 - p₂.2| ≤ D + 2`. -/
lemma hexDist_bound_of_squaresAbove {h D : ℕ} {p₁ p₂ : ℕ × ℕ} {q₁ q₂ : ℤ × ℤ}
    (hq₁ : q₁ ∈ squaresAbove (cellCode (latticePoint p₁)))
    (hq₂ : q₂ ∈ squaresAbove (cellCode (latticePoint p₂)))
    (hb₁ : IsBrick h (wallFace h q₁)) (hb₂ : IsBrick h (wallFace h q₂))
    (hd : hexDist (wallFace h q₁) (wallFace h q₂) ≤ D) :
    ((p₁.1 : ℤ) - (p₂.1 : ℤ)).natAbs ≤ 2 * D + 3 ∧
    ((p₁.2 : ℤ) - (p₂.2 : ℤ)).natAbs ≤ D + 2 := by
  obtain ⟨x₁, y₁, rfl, -⟩ := exists_of_mem_squaresAbove hq₁
  obtain ⟨x₂, y₂, rfl, -⟩ := exists_of_mem_squaresAbove hq₂
  rw [cellCode_latticePoint, mem_squaresAbove_iff] at hq₁ hq₂
  have hwf₁ := wallFace_square h x₁ y₁
  have hwf₂ := wallFace_square h x₂ y₂
  split_ifs at hwf₁ with hc₁
  · split_ifs at hwf₂ with hc₂
    · rw [hwf₁, hwf₂] at hd
      exact hexDist_coord_bound (by omega) (by omega) (by omega) (by omega) hd
    · exact False.elim (not_isBrick_outFace h (hwf₂ ▸ hb₂))
  · exact False.elim (not_isBrick_outFace h (hwf₁ ▸ hb₁))

/-- Dichotomy for two lattice points `p₁, p₂` at `planeWallDist ≤ D`: either `p₁` and `p₂`
are within `(2 * D + 3, D + 2)` of each other, or both lie within margin `(2 * D + 2, D + 1)` of
the boundary of `[0, 2h] × [0, h]`. -/
lemma latticePoint_dist_dichotomy {h D : ℕ} (hh : 1 ≤ h) (he : Even h) (p₁ p₂ : ℕ × ℕ)
    (hD : planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h))
      (fig1PlaneEquiv (latticePoint p₁)) (fig1PlaneEquiv (latticePoint p₂)) ≤ D) :
    (((p₁.1 : ℤ) - (p₂.1 : ℤ)).natAbs ≤ 2 * D + 3 ∧
      ((p₁.2 : ℤ) - (p₂.2 : ℤ)).natAbs ≤ D + 2) ∨
    ((p₁.2 ≤ D + 1 ∨ h - D - 1 ≤ p₁.2 ∨ p₁.1 ≤ 2 * D + 2 ∨ 2 * h - 2 * D - 2 ≤ p₁.1) ∧
      (p₂.2 ≤ D + 1 ∨ h - D - 1 ≤ p₂.2 ∨ p₂.1 ≤ 2 * D + 2 ∨ 2 * h - 2 * D - 2 ≤ p₂.1)) := by
  by_cases hcode : cellCode (latticePoint p₁) = cellCode (latticePoint p₂)
  · rw [cellCode_latticePoint, cellCode_latticePoint] at hcode
    have hx := congrArg Prod.fst hcode
    have hy := congrArg Prod.snd hcode
    dsimp at hx hy
    left
    omega
  · obtain ⟨q₁, hq₁, q₂, hq₂, hle₀⟩ := le_planeWallDist_fig1 hh he hcode
    have hle_toNat : (faceDist h (wallFace h q₁) (wallFace h q₂)).toNat ≤ D := by omega
    have hne : ∀ {K : ℤ × ℤ}, IsBrick h K → K ≠ outFace :=
      fun hb ho => not_isBrick_outFace h (ho ▸ hb)
    rcases isBrick_or_eq_outFace_wallFace h q₁ with hb₁ | ho₁ <;>
      rcases isBrick_or_eq_outFace_wallFace h q₂ with hb₂ | ho₂
    · rw [faceDist_of_ne (hne hb₁) (hne hb₂)] at hle_toNat
      have hpos₁ := one_le_outDepth hb₁
      have hpos₂ := one_le_outDepth hb₂
      have hnonneg := hexDist_nonneg (wallFace h q₁) (wallFace h q₂)
      by_cases hhex : hexDist (wallFace h q₁) (wallFace h q₂) ≤ D
      · exact Or.inl (hexDist_bound_of_squaresAbove hq₁ hq₂ hb₁ hb₂ hhex)
      · have hout_sum : outDepth h (wallFace h q₁) + outDepth h (wallFace h q₂) ≤ D := by omega
        exact Or.inr ⟨outDepth_margin_of_squaresAbove hq₁ (Or.inr ⟨hb₁, by omega⟩),
          outDepth_margin_of_squaresAbove hq₂ (Or.inr ⟨hb₂, by omega⟩)⟩
    · rw [ho₂, faceDist_out_right (hne hb₁)] at hle_toNat
      have hpos₁ := one_le_outDepth hb₁
      exact Or.inr ⟨outDepth_margin_of_squaresAbove hq₁ (Or.inr ⟨hb₁, by omega⟩),
        outDepth_margin_of_squaresAbove hq₂ (Or.inl ho₂)⟩
    · rw [ho₁, faceDist_out_left (hne hb₂)] at hle_toNat
      have hpos₂ := one_le_outDepth hb₂
      exact Or.inr ⟨outDepth_margin_of_squaresAbove hq₁ (Or.inl ho₁),
        outDepth_margin_of_squaresAbove hq₂ (Or.inr ⟨hb₂, by omega⟩)⟩
    · exact Or.inr ⟨outDepth_margin_of_squaresAbove hq₁ (Or.inl ho₁),
        outDepth_margin_of_squaresAbove hq₂ (Or.inl ho₂)⟩

/-- Every cell `c ∈ fig1SegmentCells p q` for `elementaryWallAdj h p q` lies in
`[0, 4h + 2] × [0, 2h]` and within `(2, 2)` of `(2 * p.1, 2 * p.2)`. -/
lemma fig1SegmentCells_bounds {h : ℕ} {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q)
    {c : ℤ × ℤ} (hc : c ∈ fig1SegmentCells p q) :
    0 ≤ c.1 ∧ c.1 ≤ 4 * (h : ℤ) + 2 ∧
    0 ≤ c.2 ∧ c.2 ≤ 2 * (h : ℤ) ∧
    (c.1 - 2 * (p.1 : ℤ)).natAbs ≤ 2 ∧
    (c.2 - 2 * (p.2 : ℤ)).natAbs ≤ 2 := by
  have hp1 : p.1 ≤ 2 * h + 1 := hadj.1.1
  have hp2 : p.2 ≤ h := hadj.1.2.1
  have hq1 : q.1 ≤ 2 * h + 1 := hadj.2.1.1
  have hq2 : q.2 ≤ h := hadj.2.1.2.1
  have hpq : (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)) ∨
      (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) := by
    rcases hadj.2.2 with ⟨h1, h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨h1, Or.inr h2⟩
  dsimp [fig1SegmentCells, horizontalCells, verticalCells] at hc
  split_ifs at hc <;>
  · simp only [mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl <;> omega

/-- The cell code of a vertex `z ∈ V(W.graph)` in a Fig. 1 coordinate drawing `Γ`. -/
noncomputable def vertexCellCode {W : Wall α β} (Γ : GraphDrawing W.graph EuclideanPlane)
    (z : α) (hz : z ∈ V(W.graph)) : ℤ × ℤ :=
  cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨z, hz⟩).1)

/-- Every vertex `z ∈ subwallRegionVerts W S` has a corresponding lattice point `p ∈ S` such that
`vertexCellCode Γ z hzW` lies in `[0, 4h + 2] × [0, 2h]` and within `(2, 2)` of `(2 * p.1, 2 * p.2)`. -/
lemma cellCode_subwallRegionVerts_bounds {W : Wall α β}
    {Γ : GraphDrawing W.graph EuclideanPlane} (hΓ : IsFigure1CoordDrawing W Γ)
    {S : Set (ℕ × ℕ)} {z : α} (hz : z ∈ subwallRegionVerts W S) :
    ∃ p ∈ S, ∃ hzW : z ∈ V(W.graph),
      let c := vertexCellCode Γ z hzW
      0 ≤ c.1 ∧ c.1 ≤ 4 * (W.height : ℤ) + 2 ∧
      0 ≤ c.2 ∧ c.2 ≤ 2 * (W.height : ℤ) ∧
      (c.1 - 2 * (p.1 : ℤ)).natAbs ≤ 2 ∧
      (c.2 - 2 * (p.2 : ℤ)).natAbs ≤ 2 := by
  have hzW : z ∈ V(W.graph) := subwallRegionVerts_subset_vertexSet W S hz
  rcases hz with ⟨p, hpS, hp, rfl⟩ | ⟨p, hpS, q, _, hadj, hzq⟩
  · refine ⟨p, hpS, hzW, ?_⟩
    have hpt := hΓ.branchVertex_point p hp hzW
    have hsymm : fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨W.branchVertex p hp, hzW⟩).1 =
        latticePoint p := by
      rw [hpt, Homeomorph.symm_apply_apply]
    dsimp only [vertexCellCode]
    rw [hsymm, cellCode_latticePoint]
    have hp1 : p.1 ≤ 2 * W.height + 1 := hp.1
    have hp2 : p.2 ≤ W.height := hp.2.1
    omega
  · have hpq_ne : W.branchVertex p hadj.1 ≠ W.branchVertex q hadj.2.1 := by
      intro h
      have h1 : W.baseIso.vertexEquiv ⟨p, hadj.1⟩ = W.baseIso.vertexEquiv ⟨q, hadj.2.1⟩ :=
        Subtype.ext h
      have h2 : p = q := congrArg Subtype.val (W.baseIso.vertexEquiv.injective h1)
      subst h2
      exact elementaryWallAdj_irrefl p hadj
    obtain ⟨f, hf, hinc⟩ :=
      IsGraphPathWithEnds.exists_inc (W.isGraphPathWithEnds_baseEdge hadj) hpq_ne hzq
    have hc_mem := hΓ.cellCode_mem_fig1SegmentCells hadj hf hinc hzW
    exact ⟨p, hpS, hzW, fig1SegmentCells_bounds hadj hc_mem⟩

/-- Every lattice point `(x, y)` with `x ≤ 2 * h + 1` and `1 ≤ y ≤ h - 1` belongs to
`elementaryWallVerts h`. -/
lemma mem_elementaryWallVerts_of_interior {h x y : ℕ}
    (hx : x ≤ 2 * h + 1) (hy1 : 1 ≤ y) (hy2 : y ≤ h - 1) :
    (x, y) ∈ elementaryWallVerts h := by
  refine ⟨hx, by omega, ?_, ?_⟩
  · intro h0; have := congrArg Prod.snd h0; dsimp at this; omega
  · intro hh; have := congrArg Prod.snd hh; dsimp at this; omega

/-- Every walk `w : GraphWalk P a b` and vertex `u ∈ w.support` has a prefix walk from `a` to `u`
whose support is contained in `w.support`. -/
lemma GraphWalk.exists_prefix_of_mem_support {P : Graph α β} {a b u : α}
    (w : GraphWalk P a b) (hu : u ∈ w.support) :
    ∃ w₁ : GraphWalk P a u, ∀ z ∈ w₁.support, z ∈ w.support := by
  induction w with
  | nil ha =>
    simp only [GraphWalk.support_nil, List.mem_singleton] at hu
    subst hu
    exact ⟨GraphWalk.nil ha, fun _ hz => hz⟩
  | @cons x y c e hlink w' ih =>
    rw [GraphWalk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu'
    · refine ⟨GraphWalk.nil hlink.left_mem, ?_⟩
      intro z hz
      simp only [GraphWalk.support_nil, List.mem_singleton] at hz
      subst hz
      exact List.mem_cons_self
    · obtain ⟨w₁', hsub'⟩ := ih hu'
      refine ⟨GraphWalk.cons hlink w₁', ?_⟩
      intro z hz
      rw [GraphWalk.support_cons, List.mem_cons] at hz ⊢
      exact hz.imp id (hsub' z)

/-- Every `p₀ ∈ elementaryWallVerts W.height` is reachable in `W.graph` from an interior lattice
point `p` with `p.1 ≤ 2 * W.height ∧ 1 ≤ p.2 ∧ p.2 ≤ W.height - 1` inside the `1`-ball around `p`. -/
lemma exists_interior_grid_reachable (W : Wall α β) {p₀ : ℕ × ℕ}
    (hp₀ : p₀ ∈ elementaryWallVerts W.height) :
    ∃ p : ℕ × ℕ,
      p.1 ≤ 2 * W.height ∧ 1 ≤ p.2 ∧ p.2 ≤ W.height - 1 ∧
      ((p₀.1 : ℤ) - (p.1 : ℤ)).natAbs ≤ 1 ∧ ((p₀.2 : ℤ) - (p.2 : ℤ)).natAbs ≤ 1 ∧
      ReachableInRegion W
        {r : ℕ × ℕ | ((r.1 : ℤ) - (p.1 : ℤ)).natAbs ≤ 1 ∧ ((r.2 : ℤ) - (p.2 : ℤ)).natAbs ≤ 1}
        p₀ p := by
  rcases p₀ with ⟨x₀, y₀⟩
  have h2 := W.two_le_height
  have hx₀_hi : x₀ ≤ 2 * W.height + 1 := hp₀.1
  have hy₀_hi : y₀ ≤ W.height := hp₀.2.1
  by_cases hy₀0 : y₀ = 0
  · subst hy₀0
    have hx₀_pos : 1 ≤ x₀ := by
      by_contra h0
      have hx0 : x₀ = 0 := by omega
      exact hp₀.2.2.1 (Prod.ext hx0 rfl)
    by_cases hodd : Odd x₀
    · by_cases hx_last : x₀ = 2 * W.height + 1
      · subst hx_last
        let p : ℕ × ℕ := (2 * W.height, 1)
        let S : Set (ℕ × ℕ) :=
          {r : ℕ × ℕ | ((r.1 : ℤ) - (p.1 : ℤ)).natAbs ≤ 1 ∧ ((r.2 : ℤ) - (p.2 : ℤ)).natAbs ≤ 1}
        have h_mid : (2 * W.height + 1, 1) ∈ elementaryWallVerts W.height :=
          mem_elementaryWallVerts_of_interior le_rfl le_rfl (by omega)
        have hp_mem : p ∈ elementaryWallVerts W.height :=
          mem_elementaryWallVerts_of_interior (by omega) le_rfl (by omega)
        have hadj₁ : elementaryWallAdj W.height (2 * W.height + 1, 0) (2 * W.height + 1, 1) :=
          ⟨hp₀, h_mid, Or.inr ⟨rfl, Or.inl ⟨rfl, by simp [hodd]⟩⟩⟩
        have hadj₂ : elementaryWallAdj W.height (2 * W.height + 1, 1) p :=
          ⟨h_mid, hp_mem, Or.inl ⟨rfl, Or.inr rfl⟩⟩
        refine ⟨p, le_rfl, le_rfl, by dsimp [p]; omega, by dsimp [p]; omega, by dsimp [p]; omega, ?_⟩
        exact (ReachableInRegion.of_adj hadj₁ (by dsimp [S, p]; omega) (by dsimp [S, p]; omega)).trans
          (ReachableInRegion.of_adj hadj₂ (by dsimp [S, p]; omega) (by dsimp [S, p]; omega))
      · let p : ℕ × ℕ := (x₀, 1)
        let S : Set (ℕ × ℕ) :=
          {r : ℕ × ℕ | ((r.1 : ℤ) - (p.1 : ℤ)).natAbs ≤ 1 ∧ ((r.2 : ℤ) - (p.2 : ℤ)).natAbs ≤ 1}
        have hp_mem : p ∈ elementaryWallVerts W.height :=
          mem_elementaryWallVerts_of_interior (by omega) le_rfl (by omega)
        have hadj₁ : elementaryWallAdj W.height (x₀, 0) p :=
          ⟨hp₀, hp_mem, Or.inr ⟨rfl, Or.inl ⟨rfl, by simp [hodd]⟩⟩⟩
        refine ⟨p, by dsimp [p]; omega, le_rfl, by dsimp [p]; omega,
          by dsimp [p]; omega, by dsimp [p]; omega, ?_⟩
        exact ReachableInRegion.of_adj hadj₁ (by dsimp [S, p]; omega) (by dsimp [S, p]; omega)
    · rw [Nat.not_odd_iff_even] at hodd
      rcases hodd with ⟨m, hm⟩
      have hx₀2 : 2 ≤ x₀ := by omega
      let p : ℕ × ℕ := (x₀ - 1, 1)
      let S : Set (ℕ × ℕ) :=
        {r : ℕ × ℕ | ((r.1 : ℤ) - (p.1 : ℤ)).natAbs ≤ 1 ∧ ((r.2 : ℤ) - (p.2 : ℤ)).natAbs ≤ 1}
      have h_mid : (x₀ - 1, 0) ∈ elementaryWallVerts W.height := by
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro h; have := congrArg Prod.fst h; dsimp at this; omega
        · intro h; have := congrArg Prod.snd h; dsimp at this; omega
      have hp_mem : p ∈ elementaryWallVerts W.height :=
        mem_elementaryWallVerts_of_interior (by omega) le_rfl (by omega)
      have hodd_m1 : Odd ((x₀ - 1) + 0) := ⟨m - 1, by omega⟩
      have hadj₁ : elementaryWallAdj W.height (x₀, 0) (x₀ - 1, 0) :=
        ⟨hp₀, h_mid, Or.inl ⟨rfl, Or.inr (by omega)⟩⟩
      have hadj₂ : elementaryWallAdj W.height (x₀ - 1, 0) p :=
        ⟨h_mid, hp_mem, Or.inr ⟨rfl, Or.inl ⟨rfl, hodd_m1⟩⟩⟩
      refine ⟨p, by dsimp [p]; omega, le_rfl, by dsimp [p]; omega,
        by dsimp [p]; omega, by dsimp [p]; omega, ?_⟩
      exact (ReachableInRegion.of_adj hadj₁ (by dsimp [S, p]; omega) (by dsimp [S, p]; omega)).trans
        (ReachableInRegion.of_adj hadj₂ (by dsimp [S, p]; omega) (by dsimp [S, p]; omega))
  · by_cases hy₀h : y₀ = W.height
    · subst hy₀h
      have hx₀_le : x₀ ≤ 2 * W.height := by
        by_contra hgt
        have hx_eq : x₀ = 2 * W.height + 1 := by omega
        exact hp₀.2.2.2 (Prod.ext hx_eq rfl)
      rcases W.even_height with ⟨kh, hkh⟩
      by_cases heven : Even x₀
      · rcases heven with ⟨kx, hkx⟩
        let p : ℕ × ℕ := (x₀, W.height - 1)
        let S : Set (ℕ × ℕ) :=
          {r : ℕ × ℕ | ((r.1 : ℤ) - (p.1 : ℤ)).natAbs ≤ 1 ∧ ((r.2 : ℤ) - (p.2 : ℤ)).natAbs ≤ 1}
        have hp_mem : p ∈ elementaryWallVerts W.height :=
          mem_elementaryWallVerts_of_interior (by omega) (by omega) le_rfl
        have hodd_p : Odd (x₀ + (W.height - 1)) := ⟨kx + kh - 1, by omega⟩
        have hadj₁ : elementaryWallAdj W.height (x₀, W.height) p :=
          ⟨hp₀, hp_mem, Or.inr ⟨rfl, Or.inr ⟨by dsimp [p]; omega, hodd_p⟩⟩⟩
        refine ⟨p, hx₀_le, by dsimp [p]; omega, le_rfl, by dsimp [p]; omega, by dsimp [p]; omega, ?_⟩
        exact ReachableInRegion.of_adj hadj₁ (by dsimp [S, p]; omega) (by dsimp [S, p]; omega)
      · rw [Nat.not_even_iff_odd] at heven
        rcases heven with ⟨kx, hkx⟩
        have hx₀1 : 1 ≤ x₀ := by omega
        let p : ℕ × ℕ := (x₀ - 1, W.height - 1)
        let S : Set (ℕ × ℕ) :=
          {r : ℕ × ℕ | ((r.1 : ℤ) - (p.1 : ℤ)).natAbs ≤ 1 ∧ ((r.2 : ℤ) - (p.2 : ℤ)).natAbs ≤ 1}
        have h_mid : (x₀ - 1, W.height) ∈ elementaryWallVerts W.height := by
          refine ⟨by omega, le_rfl, ?_, ?_⟩
          · intro h; have := congrArg Prod.snd h; dsimp at this; omega
          · intro h; have := congrArg Prod.fst h; dsimp at this; omega
        have hp_mem : p ∈ elementaryWallVerts W.height :=
          mem_elementaryWallVerts_of_interior (by omega) (by omega) le_rfl
        have hodd_p : Odd ((x₀ - 1) + (W.height - 1)) := ⟨kx + kh - 1, by omega⟩
        have hadj₁ : elementaryWallAdj W.height (x₀, W.height) (x₀ - 1, W.height) :=
          ⟨hp₀, h_mid, Or.inl ⟨rfl, Or.inr (by omega)⟩⟩
        have hadj₂ : elementaryWallAdj W.height (x₀ - 1, W.height) p :=
          ⟨h_mid, hp_mem, Or.inr ⟨rfl, Or.inr ⟨by dsimp [p]; omega, hodd_p⟩⟩⟩
        refine ⟨p, by dsimp [p]; omega, by dsimp [p]; omega, le_rfl,
          by dsimp [p]; omega, by dsimp [p]; omega, ?_⟩
        exact (ReachableInRegion.of_adj hadj₁ (by dsimp [S, p]; omega) (by dsimp [S, p]; omega)).trans
          (ReachableInRegion.of_adj hadj₂ (by dsimp [S, p]; omega) (by dsimp [S, p]; omega))
    · -- `1 ≤ y₀ ≤ W.height - 1`
      by_cases hx_last : x₀ = 2 * W.height + 1
      · subst hx_last
        let p : ℕ × ℕ := (2 * W.height, y₀)
        let S : Set (ℕ × ℕ) :=
          {r : ℕ × ℕ | ((r.1 : ℤ) - (p.1 : ℤ)).natAbs ≤ 1 ∧ ((r.2 : ℤ) - (p.2 : ℤ)).natAbs ≤ 1}
        have hp_mem : p ∈ elementaryWallVerts W.height :=
          mem_elementaryWallVerts_of_interior (by omega) (by omega) (by omega)
        have hadj₁ : elementaryWallAdj W.height (2 * W.height + 1, y₀) p :=
          ⟨hp₀, hp_mem, Or.inl ⟨rfl, Or.inr rfl⟩⟩
        refine ⟨p, le_rfl, by dsimp [p]; omega, by dsimp [p]; omega,
          by dsimp [p]; omega, by dsimp [p]; omega, ?_⟩
        exact ReachableInRegion.of_adj hadj₁ (by dsimp [S, p]; omega) (by dsimp [S, p]; omega)
      · let p : ℕ × ℕ := (x₀, y₀)
        let S : Set (ℕ × ℕ) :=
          {r : ℕ × ℕ | ((r.1 : ℤ) - (p.1 : ℤ)).natAbs ≤ 1 ∧ ((r.2 : ℤ) - (p.2 : ℤ)).natAbs ≤ 1}
        refine ⟨p, by dsimp [p]; omega, by dsimp [p]; omega, by dsimp [p]; omega,
          by dsimp [p]; omega, by dsimp [p]; omega, ?_⟩
        exact ReachableInRegion.refl hp₀ (by dsimp [S, p]; omega)

/-- Every vertex `u ∈ V(W.graph)` is connected by a short walk in `W.graph` to an interior branch
vertex `W.branchVertex p hp` (`p.1 ≤ 2h`, `1 ≤ p.2 ≤ h - 1`) such that every vertex `z` on the walk
has `vertexCellCode Γ z hzW` within `(4, 4)` of `(2 * p.1, 2 * p.2)`. -/
lemma exists_interior_branchVertex_walk {W : Wall α β}
    {Γ : GraphDrawing W.graph EuclideanPlane} (hΓ : IsFigure1CoordDrawing W Γ)
    {u : α} (hu : u ∈ V(W.graph)) :
    ∃ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height)
      (w : GraphWalk W.graph u (W.branchVertex p hp)),
      p.1 ≤ 2 * W.height ∧ 1 ≤ p.2 ∧ p.2 ≤ W.height - 1 ∧
      ∀ z ∈ w.support, ∀ hzW : z ∈ V(W.graph),
        let cz := vertexCellCode Γ z hzW
        0 ≤ cz.1 ∧ cz.1 ≤ 4 * (W.height : ℤ) + 2 ∧
        0 ≤ cz.2 ∧ cz.2 ≤ 2 * (W.height : ℤ) ∧
        (cz.1 - 2 * (p.1 : ℤ)).natAbs ≤ 4 ∧
        (cz.2 - 2 * (p.2 : ℤ)).natAbs ≤ 4 := by
  obtain ⟨p₀, q₀, hadj₀, f₀, hf₀, hinc₀⟩ := W.exists_inc_baseEdge hu
  have hu_mem : u ∈ V(W.subdivisionPaths (W.baseEdge hadj₀)) := hinc₀.vertex_mem
  have hpath₀ := W.isGraphPathWithEnds_baseEdge hadj₀
  rcases hpath₀ with ⟨hP_le, w_edge, _, hVP, _⟩
  have hu_supp : u ∈ w_edge.support := by
    change u ∈ {z | z ∈ w_edge.support}
    rw [← hVP]
    exact hu_mem
  obtain ⟨w_pref, hw_pref⟩ := GraphWalk.exists_prefix_of_mem_support w_edge hu_supp
  obtain ⟨w_up, hw_up_supp, _⟩ := exists_walk_up_of_le hP_le w_pref
  let w₀ : GraphWalk W.graph u (W.branchVertex p₀ hadj₀.1) := w_up.reverse
  obtain ⟨p, hp1_hi, hp2_lo, hp2_hi, hp₀p_1, hp₀p_2, hreach⟩ :=
    exists_interior_grid_reachable W hadj₀.1
  rcases hreach with ⟨_, hp, w₁, hw₁⟩
  refine ⟨p, hp, w₀.append w₁, hp1_hi, hp2_lo, hp2_hi, ?_⟩
  intro z hz hzW
  rcases GraphWalk.mem_support_append w₀ w₁ hz with hz₀ | hz₁
  · have hz_P : z ∈ V(W.subdivisionPaths (W.baseEdge hadj₀)) := by
      rw [hVP, mem_ofPred_eq]
      rw [GraphWalk.support_reverse, List.mem_reverse, hw_up_supp] at hz₀
      exact hw_pref z hz₀
    have hpq_ne : W.branchVertex p₀ hadj₀.1 ≠ W.branchVertex q₀ hadj₀.2.1 := by
      intro h
      have h1 : W.baseIso.vertexEquiv ⟨p₀, hadj₀.1⟩ = W.baseIso.vertexEquiv ⟨q₀, hadj₀.2.1⟩ :=
        Subtype.ext h
      have h2 : p₀ = q₀ := congrArg Subtype.val (W.baseIso.vertexEquiv.injective h1)
      subst h2
      exact elementaryWallAdj_irrefl p₀ hadj₀
    obtain ⟨f, hf, hinc⟩ :=
      IsGraphPathWithEnds.exists_inc (W.isGraphPathWithEnds_baseEdge hadj₀) hpq_ne hz_P
    have hc_mem := hΓ.cellCode_mem_fig1SegmentCells hadj₀ hf hinc hzW
    have hb := fig1SegmentCells_bounds hadj₀ hc_mem
    dsimp only [vertexCellCode]
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, by omega, by omega⟩
  · have hz_reg := hw₁ hz₁
    obtain ⟨r, ⟨hr1, hr2⟩, hzW', hb1, hb2, hb3, hb4, hb5, hb6⟩ :=
      cellCode_subwallRegionVerts_bounds hΓ hz_reg
    exact ⟨hb1, hb2, hb3, hb4, by omega, by omega⟩

/-- Upper bound on `planeWallDist` between two vertices in terms of `vertexCellCode`. -/
lemma planeWallDist_vertexCellCode_le_natAbs {W : Wall α β}
    {Γ : GraphDrawing W.graph EuclideanPlane}
    {x y : α} (hx : x ∈ V(W.graph)) (hy : y ∈ V(W.graph)) :
    planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W.height))
      (Γ.iso.vertexEquiv ⟨x, hx⟩).1 (Γ.iso.vertexEquiv ⟨y, hy⟩).1 ≤
      2 + ((vertexCellCode Γ x hx).1 - (vertexCellCode Γ y hy).1).natAbs +
      ((vertexCellCode Γ x hx).2 - (vertexCellCode Γ y hy).2).natAbs := by
  have hsx : (Γ.iso.vertexEquiv ⟨x, hx⟩).1 =
      fig1PlaneEquiv (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨x, hx⟩).1) :=
    (Homeomorph.apply_symm_apply _ _).symm
  have hsy : (Γ.iso.vertexEquiv ⟨y, hy⟩).1 =
      fig1PlaneEquiv (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨y, hy⟩).1) :=
    (Homeomorph.apply_symm_apply _ _).symm
  rw [hsx, hsy]
  exact planeWallDist_fig1_le_natAbs W.height _ _

/-- Upper bound on `planeWallDist` between a vertex and a branch vertex in terms of `vertexCellCode`. -/
lemma planeWallDist_branchVertex_le_natAbs {W : Wall α β}
    {Γ : GraphDrawing W.graph EuclideanPlane} (hΓ : IsFigure1CoordDrawing W Γ)
    {x : α} (hx : x ∈ V(W.graph)) {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts W.height)
    (hpW : W.branchVertex p hp ∈ V(W.graph)) :
    planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W.height))
      (Γ.iso.vertexEquiv ⟨x, hx⟩).1 (Γ.iso.vertexEquiv ⟨W.branchVertex p hp, hpW⟩).1 ≤
      2 + ((vertexCellCode Γ x hx).1 - 2 * (p.1 : ℤ)).natAbs +
      ((vertexCellCode Γ x hx).2 - 2 * (p.2 : ℤ)).natAbs := by
  have hsx : (Γ.iso.vertexEquiv ⟨x, hx⟩).1 =
      fig1PlaneEquiv (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨x, hx⟩).1) :=
    (Homeomorph.apply_symm_apply _ _).symm
  have hpt := hΓ.branchVertex_point p hp hpW
  rw [hsx, hpt]
  have hle := planeWallDist_fig1_le_natAbs W.height
    (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨x, hx⟩).1) (latticePoint p)
  rw [cellCode_latticePoint] at hle
  exact hle

/-- Upper bound on `planeWallDist` between two vertices in the outer `L`-margin in terms of `vertexCellCode`. -/
lemma planeWallDist_vertexCellCode_le_of_margin {W : Wall α β}
    {Γ : GraphDrawing W.graph EuclideanPlane}
    (hh1 : 1 ≤ W.height) (heven : Even W.height) {L : ℕ}
    {x y : α} (hx : x ∈ V(W.graph)) (hy : y ∈ V(W.graph))
    (hx1 : 0 ≤ (vertexCellCode Γ x hx).1 ∧ (vertexCellCode Γ x hx).1 ≤ 4 * (W.height : ℤ) + 2)
    (hx2 : 0 ≤ (vertexCellCode Γ x hx).2 ∧ (vertexCellCode Γ x hx).2 ≤ 2 * (W.height : ℤ))
    (hxm : (vertexCellCode Γ x hx).2 ≤ (L : ℤ) ∨ 2 * (W.height : ℤ) - (L : ℤ) ≤ (vertexCellCode Γ x hx).2 ∨
      (vertexCellCode Γ x hx).1 ≤ (L : ℤ) ∨ 4 * (W.height : ℤ) + 2 - (L : ℤ) ≤ (vertexCellCode Γ x hx).1)
    (hy1 : 0 ≤ (vertexCellCode Γ y hy).1 ∧ (vertexCellCode Γ y hy).1 ≤ 4 * (W.height : ℤ) + 2)
    (hy2 : 0 ≤ (vertexCellCode Γ y hy).2 ∧ (vertexCellCode Γ y hy).2 ≤ 2 * (W.height : ℤ))
    (hym : (vertexCellCode Γ y hy).2 ≤ (L : ℤ) ∨ 2 * (W.height : ℤ) - (L : ℤ) ≤ (vertexCellCode Γ y hy).2 ∨
      (vertexCellCode Γ y hy).1 ≤ (L : ℤ) ∨ 4 * (W.height : ℤ) + 2 - (L : ℤ) ≤ (vertexCellCode Γ y hy).1) :
    planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W.height))
      (Γ.iso.vertexEquiv ⟨x, hx⟩).1 (Γ.iso.vertexEquiv ⟨y, hy⟩).1 ≤ 2 * L + 8 := by
  have hsx : (Γ.iso.vertexEquiv ⟨x, hx⟩).1 =
      fig1PlaneEquiv (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨x, hx⟩).1) :=
    (Homeomorph.apply_symm_apply _ _).symm
  have hsy : (Γ.iso.vertexEquiv ⟨y, hy⟩).1 =
      fig1PlaneEquiv (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨y, hy⟩).1) :=
    (Homeomorph.apply_symm_apply _ _).symm
  rw [hsx, hsy]
  exact planeWallDist_fig1_le_of_margin hh1 heven hx1 hx2 hxm hy1 hy2 hym

attribute [irreducible] vertexCellCode

/-- The rectangular bounding box of two interior lattice points `p, q`, widened by `1` on the right
for vertical column-pair steps. -/
def interiorRectBox (p q : ℕ × ℕ) : Set (ℕ × ℕ) :=
  {r : ℕ × ℕ | min p.1 q.1 ≤ r.1 ∧ r.1 ≤ max p.1 q.1 + 1 ∧
    min p.2 q.2 ≤ r.2 ∧ r.2 ≤ max p.2 q.2}

/-- Any two interior lattice points `p, q` (`x ≤ 2h`, `1 ≤ y ≤ h - 1`) are mutually reachable in
`W.graph` inside `interiorRectBox p q`. -/
lemma reachableInRegion_interiorRectBox (W : Wall α β) {p q : ℕ × ℕ}
    (hp1 : p.1 ≤ 2 * W.height) (hp2_lo : 1 ≤ p.2) (hp2_hi : p.2 ≤ W.height - 1)
    (hq1 : q.1 ≤ 2 * W.height) (hq2_lo : 1 ≤ q.2) (hq2_hi : q.2 ≤ W.height - 1) :
    ReachableInRegion W (interiorRectBox p q) p q := by
  have hvert : ReachableInRegion W (interiorRectBox p q) p (p.1, q.2) := by
    rcases le_total p.2 q.2 with hy | hy
    · refine ReachableInRegion.vertPair p.1 p.2 q.2 hy (fun y hy1 hy2 => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩)
      · exact mem_elementaryWallVerts_of_interior (by omega) (by omega) (by omega)
      · dsimp [interiorRectBox]; omega
      · exact mem_elementaryWallVerts_of_interior (by omega) (by omega) (by omega)
      · dsimp [interiorRectBox]; omega
    · refine (ReachableInRegion.vertPair p.1 q.2 p.2 hy (fun y hy1 hy2 => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩)).symm
      · exact mem_elementaryWallVerts_of_interior (by omega) (by omega) (by omega)
      · dsimp [interiorRectBox]; omega
      · exact mem_elementaryWallVerts_of_interior (by omega) (by omega) (by omega)
      · dsimp [interiorRectBox]; omega
  have hhoriz : ReachableInRegion W (interiorRectBox p q) (p.1, q.2) q := by
    rcases le_total p.1 q.1 with hx | hx
    · refine ReachableInRegion.horiz q.2 p.1 q.1 hx (fun x hx1 hx2 => ⟨?_, ?_⟩)
      · exact mem_elementaryWallVerts_of_interior (by omega) (by omega) (by omega)
      · dsimp [interiorRectBox]; omega
    · refine (ReachableInRegion.horiz q.2 q.1 p.1 hx (fun x hx1 hx2 => ⟨?_, ?_⟩)).symm
      · exact mem_elementaryWallVerts_of_interior (by omega) (by omega) (by omega)
      · dsimp [interiorRectBox]; omega
  exact hvert.trans hhoriz

/-- The outer-margin lattice set of width `(2M + 1, M)`. -/
def marginLatticeSet (h M : ℕ) : Set (ℕ × ℕ) :=
  {r : ℕ × ℕ | r.1 ≤ 2 * M + 1 ∨ 2 * h - 2 * M ≤ r.1 ∨ r.2 ≤ M ∨ h - M ≤ r.2}

/-- Any interior lattice point `p` (`p.1 ≤ 2h`, `1 ≤ p.2 ≤ h - 1`) in the `(2M, M)` outer margin
(with `1 ≤ M`) is reachable in `W.graph` from `(0, 1)` inside `marginLatticeSet W.height M`. -/
lemma reachableInRegion_marginLatticeSet_base (W : Wall α β) {M : ℕ} (hM : 1 ≤ M) {p : ℕ × ℕ}
    (hp1 : p.1 ≤ 2 * W.height) (hp2_lo : 1 ≤ p.2) (hp2_hi : p.2 ≤ W.height - 1)
    (hmargin : p.1 ≤ 2 * M ∨ 2 * W.height - 2 * M ≤ p.1 ∨ p.2 ≤ M ∨ W.height - M ≤ p.2) :
    ReachableInRegion W (marginLatticeSet W.height M) p (0, 1) := by
  have h2 := W.two_le_height
  by_cases hright : 2 * W.height - 2 * M ≤ p.1
  · -- Go `p -> (p.1, 1) -> (0, 1)`
    have hstep1 : ReachableInRegion W (marginLatticeSet W.height M) p (p.1, 1) := by
      refine ReachableInRegion.mono ?_
        (reachableInRegion_interiorRectBox W hp1 hp2_lo hp2_hi hp1 le_rfl (by omega))
      intro r hr
      dsimp [interiorRectBox] at hr
      dsimp [marginLatticeSet]
      omega
    have hstep2 : ReachableInRegion W (marginLatticeSet W.height M) (p.1, 1) (0, 1) := by
      refine ReachableInRegion.mono ?_
        (reachableInRegion_interiorRectBox W hp1 le_rfl (by omega) (by omega) le_rfl (by omega))
      intro r hr
      dsimp [interiorRectBox] at hr
      dsimp [marginLatticeSet]
      omega
    exact hstep1.trans hstep2
  · -- Go `p -> (0, p.2) -> (0, 1)`
    have hstep1 : ReachableInRegion W (marginLatticeSet W.height M) p (0, p.2) := by
      refine ReachableInRegion.mono ?_
        (reachableInRegion_interiorRectBox W hp1 hp2_lo hp2_hi (by omega) hp2_lo hp2_hi)
      intro r hr
      dsimp [interiorRectBox] at hr
      dsimp [marginLatticeSet]
      omega
    have hstep2 : ReachableInRegion W (marginLatticeSet W.height M) (0, p.2) (0, 1) := by
      refine ReachableInRegion.mono ?_
        (reachableInRegion_interiorRectBox W (by omega) hp2_lo hp2_hi (by omega) le_rfl (by omega))
      intro r hr
      dsimp [interiorRectBox] at hr
      dsimp [marginLatticeSet]
      omega
    exact hstep1.trans hstep2

/-- Pure integer coordinate bound for Case 1 of `exists_walk_dist_le` (on `w_u`). -/
lemma natAbs_bound_case1_u {cz cv : ℤ × ℤ} {p q : ℕ × ℕ} {d : ℕ}
    (hdx : ((p.1 : ℤ) - (q.1 : ℤ)).natAbs ≤ 2 * (d + 20) + 3)
    (hdy : ((p.2 : ℤ) - (q.2 : ℤ)).natAbs ≤ d + 20 + 2)
    (hcv1 : (cv.1 - 2 * (q.1 : ℤ)).natAbs ≤ 4)
    (hcv2 : (cv.2 - 2 * (q.2 : ℤ)).natAbs ≤ 4)
    (hcz1 : (cz.1 - 2 * (p.1 : ℤ)).natAbs ≤ 4)
    (hcz2 : (cz.2 - 2 * (p.2 : ℤ)).natAbs ≤ 4) :
    2 + (cz.1 - cv.1).natAbs + (cz.2 - cv.2).natAbs ≤ 8 * d + 200 := by
  omega

/-- Pure integer coordinate bound for Case 1 of `exists_walk_dist_le` (on `w_pq`). -/
lemma natAbs_bound_case1_pq {cz cv : ℤ × ℤ} {p q r : ℕ × ℕ} {d : ℕ}
    (hdx : ((p.1 : ℤ) - (q.1 : ℤ)).natAbs ≤ 2 * (d + 20) + 3)
    (hdy : ((p.2 : ℤ) - (q.2 : ℤ)).natAbs ≤ d + 20 + 2)
    (hr : r ∈ interiorRectBox p q)
    (hcv1 : (cv.1 - 2 * (q.1 : ℤ)).natAbs ≤ 4)
    (hcv2 : (cv.2 - 2 * (q.2 : ℤ)).natAbs ≤ 4)
    (hcz1 : (cz.1 - 2 * (r.1 : ℤ)).natAbs ≤ 2)
    (hcz2 : (cz.2 - 2 * (r.2 : ℤ)).natAbs ≤ 2) :
    2 + (cz.1 - cv.1).natAbs + (cz.2 - cv.2).natAbs ≤ 8 * d + 200 := by
  dsimp [interiorRectBox] at hr
  omega

/-- Pure integer margin bound for Case 2 of `exists_walk_dist_le` (on `w_u` or `w_v`). -/
lemma margin_bound_case2_uv {c : ℤ × ℤ} {q : ℕ × ℕ} {h D : ℕ}
    (hqm : q.2 ≤ D + 1 ∨ h - D - 1 ≤ q.2 ∨ q.1 ≤ 2 * D + 2 ∨ 2 * h - 2 * D - 2 ≤ q.1)
    (hc1 : (c.1 - 2 * (q.1 : ℤ)).natAbs ≤ 4)
    (hc2 : (c.2 - 2 * (q.2 : ℤ)).natAbs ≤ 4) :
    c.2 ≤ ((4 * (D + 2) + 4 : ℕ) : ℤ) ∨
    2 * (h : ℤ) - ((4 * (D + 2) + 4 : ℕ) : ℤ) ≤ c.2 ∨
    c.1 ≤ ((4 * (D + 2) + 4 : ℕ) : ℤ) ∨
    4 * (h : ℤ) + 2 - ((4 * (D + 2) + 4 : ℕ) : ℤ) ≤ c.1 := by
  omega

/-- Pure integer margin bound for Case 2 of `exists_walk_dist_le` (on `w_pq`). -/
lemma margin_bound_case2_pq {c : ℤ × ℤ} {r : ℕ × ℕ} {h M : ℕ}
    (hr : r ∈ marginLatticeSet h M)
    (hc1 : (c.1 - 2 * (r.1 : ℤ)).natAbs ≤ 2)
    (hc2 : (c.2 - 2 * (r.2 : ℤ)).natAbs ≤ 2) :
    c.2 ≤ ((4 * M + 4 : ℕ) : ℤ) ∨
    2 * (h : ℤ) - ((4 * M + 4 : ℕ) : ℤ) ≤ c.2 ∨
    c.1 ≤ ((4 * M + 4 : ℕ) : ℤ) ∨
    4 * (h : ℤ) + 2 - ((4 * M + 4 : ℕ) : ℤ) ≤ c.1 := by
  dsimp [marginLatticeSet] at hr
  omega

/-- In any Fig. 1 drawn wall `H`, for any `u, v ∈ V(H.graph)`, there is a walk `W` in `H.graph`
from `u` to `v` such that every vertex `w ∈ W.support` satisfies
`H.dist w v ≤ 8 * H.dist u v + 200`. -/
theorem DrawnWall.IsFigure1.exists_walk_dist_le {H : DrawnWall α β} (hfig : H.IsFigure1)
    {u v : α} (hu : u ∈ V(H.graph)) (hv : v ∈ V(H.graph)) :
    ∃ W : GraphWalk H.graph u v,
      ∀ w ∈ W.support, H.dist w v ≤ 8 * H.dist u v + 200 := by
  have hthin : IsThinPlaneDrawing H.drawingU := hfig.isThin
  have hh1 : 1 ≤ H.height := by have := H.two_le_height; omega
  rcases hfig with ⟨φ, Γ, hΓ, hU, hV⟩
  have hdist_eq : ∀ {x y : α} (hx : x ∈ V(H.graph)) (hy : y ∈ V(H.graph)),
      H.dist x y = planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height))
        (Γ.iso.vertexEquiv ⟨x, hx⟩).1 (Γ.iso.vertexEquiv ⟨y, hy⟩).1 := by
    intro x y hx hy
    dsimp [DrawnWall.dist, DrawnWall.planeDist]
    rw [hU, hV x hx, hV y hy, planeWallDist_image_homeomorph, hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
  obtain ⟨p, hp, w_u, hp1, hp2_lo, hp2_hi, hw_u⟩ := exists_interior_branchVertex_walk hΓ hu
  obtain ⟨q, hq, w_v, hq1, hq2_lo, hq2_hi, hw_v⟩ := exists_interior_branchVertex_walk hΓ hv
  have hpH : H.branchVertex p hp ∈ V(H.graph) := H.toWall.branchVertex_mem_vertexSet p hp
  have hqH : H.branchVertex q hq ∈ V(H.graph) := H.toWall.branchVertex_mem_vertexSet q hq
  -- Bound `H.dist u (H.branchVertex p hp) ≤ 10` and `H.dist v (H.branchVertex q hq) ≤ 10`
  have hdist_up : H.dist u (H.branchVertex p hp) ≤ 10 := by
    obtain ⟨_, _, _, _, hu_c1, hu_c2⟩ := hw_u u w_u.start_mem_support hu
    have hle := planeWallDist_branchVertex_le_natAbs hΓ hu hp hpH
    rw [← hdist_eq hu hpH] at hle
    exact le_trans hle (by omega)
  have hdist_vq : H.dist v (H.branchVertex q hq) ≤ 10 := by
    obtain ⟨_, _, _, _, hv_c1, hv_c2⟩ := hw_v v w_v.start_mem_support hv
    have hle := planeWallDist_branchVertex_le_natAbs hΓ hv hq hqH
    rw [← hdist_eq hv hqH] at hle
    exact le_trans hle (by omega)
  -- Also every `z ∈ w_v.support` has `H.dist z v ≤ 18`
  obtain ⟨hcv1_lo, hcv1_hi, hcv2_lo, hcv2_hi, hcv_q1, hcv_q2⟩ := hw_v v w_v.start_mem_support hv
  have hw_v_dist : ∀ z ∈ w_v.support, H.dist z v ≤ 18 := by
    intro z hz
    have hzH : z ∈ V(H.graph) := w_v.mem_vertexSet_of_mem_support hz
    obtain ⟨_, _, _, _, hcz_q1, hcz_q2⟩ := hw_v z hz hzH
    have hle := planeWallDist_vertexCellCode_le_natAbs hzH hv (Γ := Γ)
    rw [← hdist_eq hzH hv] at hle
    exact le_trans hle (by omega)
  -- Bound `planeWallDist` between `latticePoint p` and `latticePoint q` by `D := H.dist u v + 20`
  have hdist_pq : H.dist (H.branchVertex p hp) (H.branchVertex q hq) ≤ H.dist u v + 20 := by
    have h1 := H.dist_triangle hthin (H.branchVertex p hp) u (H.branchVertex q hq)
    have h2 := H.dist_triangle hthin u v (H.branchVertex q hq)
    rw [H.dist_comm (H.branchVertex p hp) u] at h1
    omega
  have hplane_pq : planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height))
      (fig1PlaneEquiv (latticePoint p)) (fig1PlaneEquiv (latticePoint q)) ≤ H.dist u v + 20 := by
    have heq := hdist_eq hpH hqH
    rw [hΓ.branchVertex_point p hp hpH, hΓ.branchVertex_point q hq hqH] at heq
    rw [← heq]
    exact hdist_pq
  -- Apply `latticePoint_dist_dichotomy`
  rcases latticePoint_dist_dichotomy hh1 H.even_height p q hplane_pq with ⟨hdx, hdy⟩ | ⟨hmargin_p, hmargin_q⟩
  · -- Case 1: `p` and `q` are close in `ℕ × ℕ` coordinates
    have hreach := reachableInRegion_interiorRectBox H.toWall hp1 hp2_lo hp2_hi hq1 hq2_lo hq2_hi
    rcases hreach with ⟨_, _, w_pq, hw_pq⟩
    refine ⟨(w_u.append w_pq).append w_v.reverse, ?_⟩
    intro z hz
    rcases GraphWalk.mem_support_append (w_u.append w_pq) w_v.reverse hz with hz_upq | hz_v
    · rcases GraphWalk.mem_support_append w_u w_pq hz_upq with hz_u | hz_pq
      · have hzH : z ∈ V(H.graph) := w_u.mem_vertexSet_of_mem_support hz_u
        obtain ⟨_, _, _, _, hcz_p1, hcz_p2⟩ := hw_u z hz_u hzH
        have hle := planeWallDist_vertexCellCode_le_natAbs hzH hv (Γ := Γ)
        rw [← hdist_eq hzH hv] at hle
        exact le_trans hle (natAbs_bound_case1_u hdx hdy hcv_q1 hcv_q2 hcz_p1 hcz_p2)
      · obtain ⟨r, hr_box, hzH, _, _, _, _, hcz_r1, hcz_r2⟩ :=
          cellCode_subwallRegionVerts_bounds hΓ (hw_pq hz_pq)
        have hle := planeWallDist_vertexCellCode_le_natAbs hzH hv (Γ := Γ)
        rw [← hdist_eq hzH hv] at hle
        exact le_trans hle (natAbs_bound_case1_pq hdx hdy hr_box hcv_q1 hcv_q2 hcz_r1 hcz_r2)
    · rw [GraphWalk.support_reverse, List.mem_reverse] at hz_v
      exact le_trans (hw_v_dist z hz_v) (by omega)
  · -- Case 2: Both `p` and `q` lie in the `(2D + 2, D + 1)` outer margin
    let D : ℕ := H.dist u v + 20
    have hM : 1 ≤ D + 2 := by omega
    have hmp : p.1 ≤ 2 * (D + 2) ∨ 2 * H.height - 2 * (D + 2) ≤ p.1 ∨
        p.2 ≤ D + 2 ∨ H.height - (D + 2) ≤ p.2 := by
      dsimp [D]; omega
    have hmq : q.1 ≤ 2 * (D + 2) ∨ 2 * H.height - 2 * (D + 2) ≤ q.1 ∨
        q.2 ≤ D + 2 ∨ H.height - (D + 2) ≤ q.2 := by
      dsimp [D]; omega
    have hreach_p := reachableInRegion_marginLatticeSet_base H.toWall hM hp1 hp2_lo hp2_hi hmp
    have hreach_q := reachableInRegion_marginLatticeSet_base H.toWall hM hq1 hq2_lo hq2_hi hmq
    rcases hreach_p.trans hreach_q.symm with ⟨_, _, w_pq, hw_pq⟩
    refine ⟨(w_u.append w_pq).append w_v.reverse, ?_⟩
    have hcv_margin := margin_bound_case2_uv hmargin_q hcv_q1 hcv_q2
    have hbound_L : 2 * (4 * (D + 2) + 4) + 8 ≤ 8 * H.dist u v + 200 := by
      dsimp [D]; omega
    intro z hz
    rcases GraphWalk.mem_support_append (w_u.append w_pq) w_v.reverse hz with hz_upq | hz_v
    · rcases GraphWalk.mem_support_append w_u w_pq hz_upq with hz_u | hz_pq
      · have hzH : z ∈ V(H.graph) := w_u.mem_vertexSet_of_mem_support hz_u
        obtain ⟨hcz1_lo, hcz1_hi, hcz2_lo, hcz2_hi, hcz_p1, hcz_p2⟩ := hw_u z hz_u hzH
        have hcz_margin := margin_bound_case2_uv hmargin_p hcz_p1 hcz_p2
        have hle := planeWallDist_vertexCellCode_le_of_margin hh1 H.even_height hzH hv
          ⟨hcz1_lo, hcz1_hi⟩ ⟨hcz2_lo, hcz2_hi⟩ hcz_margin
          ⟨hcv1_lo, hcv1_hi⟩ ⟨hcv2_lo, hcv2_hi⟩ hcv_margin
        rw [← hdist_eq hzH hv] at hle
        exact le_trans hle hbound_L
      · obtain ⟨r, hr_margin, hzH, hcz1_lo, hcz1_hi, hcz2_lo, hcz2_hi, hcz_r1, hcz_r2⟩ :=
          cellCode_subwallRegionVerts_bounds hΓ (hw_pq hz_pq)
        have hcz_margin := margin_bound_case2_pq hr_margin hcz_r1 hcz_r2
        have hle := planeWallDist_vertexCellCode_le_of_margin hh1 H.even_height hzH hv
          ⟨hcz1_lo, hcz1_hi⟩ ⟨hcz2_lo, hcz2_hi⟩ hcz_margin
          ⟨hcv1_lo, hcv1_hi⟩ ⟨hcv2_lo, hcv2_hi⟩ hcv_margin
        rw [← hdist_eq hzH hv] at hle
        exact le_trans hle hbound_L
    · rw [GraphWalk.support_reverse, List.mem_reverse] at hz_v
      exact le_trans (hw_v_dist z hz_v) (by omega)

end GraphMinor.GM13
