module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.List.Chain

/-!
# Small tools on induced subgraphs and vertex lists

These lemmas are used by the proof of Wagner's theorem in `GraphMinor/Wagner/`. A *path list* is a
list of vertices whose consecutive entries are adjacent. The branch sets of the minors we build are
unions of path lists, so we need that such sets induce preconnected subgraphs, and that the union of
two preconnected sets joined by an edge is preconnected.

We also record that in a connected induced subgraph, a nonempty proper subset of the vertices has an
edge leaving it (`false_of_closed`).
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ}

theorem induce_reach_mono {X Y : Set γ} (hXY : X ⊆ Y) {u v : X}
    (hr : (K.induce X).Reachable u v) :
    (K.induce Y).Reachable ⟨u.1, hXY u.2⟩ ⟨v.1, hXY v.2⟩ := by
  let f : K.induce X →g K.induce Y := ⟨fun z => ⟨z.1, hXY z.2⟩, fun h => h⟩
  exact hr.map f

theorem pc_empty : (K.induce (∅ : Set γ)).Preconnected := by
  rintro ⟨u, hu⟩
  exact hu.elim

theorem pc_singleton (x : γ) : (K.induce ({x} : Set γ)).Preconnected := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  rw [mem_singleton_iff] at hu hv
  subst hu; subst hv
  exact Reachable.rfl

theorem pc_union_adj {X Y : Set γ} (hX : (K.induce X).Preconnected)
    (hY : (K.induce Y).Preconnected) {x y : γ} (hx : x ∈ X) (hy : y ∈ Y) (hxy : K.Adj x y) :
    (K.induce (X ∪ Y)).Preconnected := by
  have hx' : x ∈ X ∪ Y := Or.inl hx
  have hy' : y ∈ X ∪ Y := Or.inr hy
  have hlink : (K.induce (X ∪ Y)).Reachable ⟨x, hx'⟩ ⟨y, hy'⟩ :=
    Adj.reachable (G := K.induce (X ∪ Y)) (u := ⟨x, hx'⟩) (v := ⟨y, hy'⟩) hxy
  have htoX : ∀ z : ↥(X ∪ Y), z.1 ∈ X → (K.induce (X ∪ Y)).Reachable z ⟨x, hx'⟩ := fun z hz =>
    induce_reach_mono subset_union_left (hX ⟨z.1, hz⟩ ⟨x, hx⟩)
  have htoY : ∀ z : ↥(X ∪ Y), z.1 ∈ Y → (K.induce (X ∪ Y)).Reachable z ⟨x, hx'⟩ := fun z hz =>
    (induce_reach_mono subset_union_right (hY ⟨z.1, hz⟩ ⟨y, hy⟩)).trans hlink.symm
  intro u v
  have hu : (K.induce (X ∪ Y)).Reachable u ⟨x, hx'⟩ := u.2.elim (htoX u) (htoY u)
  have hv : (K.induce (X ∪ Y)).Reachable v ⟨x, hx'⟩ := v.2.elim (htoX v) (htoY v)
  exact hu.trans hv.symm

/-- Two preconnected sets with a common vertex have a preconnected union. -/
theorem pc_union_mem {X Y : Set γ} (hX : (K.induce X).Preconnected)
    (hY : (K.induce Y).Preconnected) {x : γ} (hx : x ∈ X) (hy : x ∈ Y) :
    (K.induce (X ∪ Y)).Preconnected := by
  have hx' : x ∈ X ∪ Y := Or.inl hx
  have htoX : ∀ z : ↥(X ∪ Y), z.1 ∈ X → (K.induce (X ∪ Y)).Reachable z ⟨x, hx'⟩ := fun z hz =>
    induce_reach_mono subset_union_left (hX ⟨z.1, hz⟩ ⟨x, hx⟩)
  have htoY : ∀ z : ↥(X ∪ Y), z.1 ∈ Y → (K.induce (X ∪ Y)).Reachable z ⟨x, hx'⟩ := fun z hz =>
    induce_reach_mono subset_union_right (hY ⟨z.1, hz⟩ ⟨x, hy⟩)
  intro u v
  have hu : (K.induce (X ∪ Y)).Reachable u ⟨x, hx'⟩ := u.2.elim (htoX u) (htoY u)
  have hv : (K.induce (X ∪ Y)).Reachable v ⟨x, hx'⟩ := v.2.elim (htoX v) (htoY v)
  exact hu.trans hv.symm

theorem pc_insert_adj {X : Set γ} (hX : (K.induce X).Preconnected) {x y : γ} (hy : y ∈ X)
    (hxy : K.Adj x y) : (K.induce (insert x X)).Preconnected := by
  rw [← singleton_union]
  exact pc_union_adj (pc_singleton x) hX rfl hy hxy

theorem pc_congr {X Y : Set γ} (h : X = Y) (hX : (K.induce X).Preconnected) :
    (K.induce Y).Preconnected := h ▸ hX

/-- The vertices of a path list induce a preconnected subgraph. -/
theorem pc_of_isChain : ∀ {l : List γ}, l.IsChain K.Adj → (K.induce {x | x ∈ l}).Preconnected
  | [], _ => pc_congr (by ext; simp) pc_empty
  | [a], _ => pc_congr (by ext; simp) (pc_singleton a)
  | a :: b :: t, h => by
    rw [List.isChain_cons_cons] at h
    have ih := pc_of_isChain h.2
    refine pc_congr ?_ (pc_insert_adj ih (x := a) (y := b) (by simp) h.1)
    ext z
    simp

/-- If `W` induces a preconnected subgraph, `D ⊆ W` has a vertex, `W \ D` has a vertex, then some
edge of `K` leaves `D` inside `W`. -/
theorem exists_adj_out {W D : Set γ} (hW : (K.induce W).Preconnected) (hDW : D ⊆ W) {x y : γ}
    (hx : x ∈ D) (hyW : y ∈ W) (hy : y ∉ D) : ∃ a ∈ D, ∃ b ∈ W, b ∉ D ∧ K.Adj a b := by
  obtain ⟨w⟩ := hW ⟨x, hDW hx⟩ ⟨y, hyW⟩
  have key : ∀ {u v : W} (r : (K.induce W).Walk u v), u.1 ∈ D → v.1 ∉ D →
      ∃ a ∈ D, ∃ b ∈ W, b ∉ D ∧ K.Adj a b := by
    intro u v r
    induction r with
    | nil => intro hu hv; exact (hv hu).elim
    | @cons a b c hab r' ih =>
      intro ha hc
      by_cases hb : b.1 ∈ D
      · exact ih hb hc
      · exact ⟨a.1, ha, b.1, b.2, hb, hab⟩
  exact key w hx hy

/-- A set closed under the edges of `K` inside `W` is all of `W` or misses it, when `W` induces a
preconnected subgraph. -/
theorem false_of_closed {W D : Set γ} (hW : (K.induce W).Preconnected) (hDW : D ⊆ W) {x y : γ}
    (hx : x ∈ D) (hyW : y ∈ W) (hy : y ∉ D) (hcl : ∀ a ∈ D, ∀ b ∈ W, K.Adj a b → b ∈ D) :
    False := by
  obtain ⟨a, ha, b, hbW, hb, hab⟩ := exists_adj_out hW hDW hx hyW hy
  exact hb (hcl a ha b hbW hab)

end GraphMinor.Wagner
