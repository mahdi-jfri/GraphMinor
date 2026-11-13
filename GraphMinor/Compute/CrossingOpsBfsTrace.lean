module

public import GraphMinor.Crossing.DefsForest
public import Mathlib.Data.List.Basic

/-!
# The queue history of a breadth-first forest search

Section 7.1 uses a BFS spanning forest. A new root is queued only when the queue is empty.
Scanning a queued vertex appends its unmarked neighbours and records their parent edges.
The history below records these two transitions. Its elementary invariants connect the
queue operations to the scan order and parent choice used by `IsScanFirstForest`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

universe u

variable {V : Type u}

/-- A BFS forest history: the list is the complete queue history, the natural number is its
head index, and the pairs are the discovery edges, directed from parent to child. -/
inductive BfsScanTrace (G : SimpleGraph V) (T : Set V) : List V → ℕ → List (V × V) → Prop
  | nil : BfsScanTrace G T [] 0 []
  | root {items head edges} (h : BfsScanTrace G T items head edges)
      (empty : head = items.length) (r : V) (hr : r ∈ T) (fresh : r ∉ items) :
      BfsScanTrace G T (items ++ [r]) head edges
  | scan {items head edges} (h : BfsScanTrace G T items head edges)
      (pending : head < items.length) (fresh : List V) (nodup : fresh.Nodup)
      (neighbours : ∀ v, v ∈ fresh ↔ G.Adj items[head] v ∧ v ∈ T ∧ v ∉ items) :
      BfsScanTrace G T (items ++ fresh) (head + 1)
        (edges ++ fresh.map (fun v => (items[head], v)))

/-- Each vertex enters the queue at most once. -/
theorem BfsScanTrace.nodup {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges) : items.Nodup := by
  induction h with
  | nil => simp
  | root h empty r hr fresh ih =>
    apply ih.append (by simp)
    intro x hx hxr
    have hxr' : x = r := by simpa only [List.mem_singleton] using hxr
    exact fresh (hxr' ▸ hx)
  | scan h pending fresh hnd hn ih =>
    exact ih.append hnd (fun v hv hvf => (hn v).mp hvf |>.2.2 hv)

/-- All discovered vertices belong to the input vertex set. -/
theorem BfsScanTrace.mem_set {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges) :
    ∀ v ∈ items, v ∈ T := by
  induction h with
  | nil => simp
  | root h empty r hr fresh ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih v hv
    · have : v = r := by simpa only [List.mem_singleton] using hv
      exact this ▸ hr
  | scan h pending fresh hnd hn ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih v hv
    · exact ((hn v).mp hv).2.1

/-- The head never passes the end of the queue history. -/
theorem BfsScanTrace.head_le {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges) :
    head ≤ items.length := by
  induction h with
  | nil => simp
  | root h empty r hr fresh ih => simp only [List.length_append, List.length_singleton]; omega
  | scan h pending fresh hnd hn ih => simp only [List.length_append]; omega

/-- Every neighbour in the input vertex set of a scanned vertex has been discovered. -/
theorem BfsScanTrace.closed {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges) :
    ∀ a ∈ items.take head, ∀ b ∈ T, G.Adj a b → b ∈ items := by
  classical
  induction h with
  | nil => simp
  | @root items head edges h empty r hr fresh ih =>
    have ht : (items ++ [r]).take head = items := by rw [empty]; simp
    intro a ha b hb hab
    rw [ht] at ha
    apply List.mem_append_left
    apply ih a
    · simpa only [empty, List.take_length] using ha
    · exact hb
    · exact hab
  | @scan items head edges h pending fresh hnd hn ih =>
    have ht : (items ++ fresh).take (head + 1) = items.take head ++ [items[head]] := by
      rw [List.take_append_of_le_length (by omega), List.take_succ_eq_append_getElem pending]
    intro a ha b hb hab
    rw [ht] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (ih a ha b hb hab)
    · have hau : a = items[head] := by simpa only [List.mem_singleton] using ha
      by_cases hbi : b ∈ items
      · exact List.mem_append_left _ hbi
      · exact List.mem_append_right _ ((hn b).mpr ⟨hau ▸ hab, hb, hbi⟩)

end GraphMinor.Compute.Crossing
