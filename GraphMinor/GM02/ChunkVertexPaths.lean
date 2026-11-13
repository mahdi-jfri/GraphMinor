module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Set.Disjoint

/-!
# Vertex lists obtained from consecutive edge chunks

A path's dart runs record the vertices reached after their edges. Restore
the starting vertex of each run by taking the previous run's last vertex.
This gives the full vertex list of each side piece in corrected II (2.9).
Every restored vertex belongs to the original starting vertex or to one
of the recorded chunks.
-/

@[expose] public section
namespace GraphMinor.GM02
open List Set
universe u

/-- Restore each chunk's starting vertex from the previous chunk's end. -/
def chunkVertexPaths {α : Type u} (a : α) : List (Bool × List α) → List (Bool × List α)
  | [] => []
  | (c, r) :: rs => (c, a :: r) :: chunkVertexPaths (r.getLastD a) rs

/-- Every vertex in a restored chunk comes from the starting vertex or
from the recorded reached-vertex lists. -/
theorem mem_chunkVertexPaths {α : Type u} (a : α) (chunks : List (Bool × List α))
    {q : Bool × List α} (hq : q ∈ chunkVertexPaths a chunks) {x : α} (hx : x ∈ q.2) :
    x ∈ a :: (chunks.map Prod.snd).flatten := by
  induction chunks generalizing a with
  | nil => simp [chunkVertexPaths] at hq
  | cons cr rs ih =>
    rcases cr with ⟨c, r⟩
    simp only [chunkVertexPaths, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact List.mem_cons.2 ((List.mem_cons.1 hx).imp_right (fun h =>
        List.mem_append.2 (Or.inl h)))
    · have hm := ih (r.getLastD a) hq
      rcases List.mem_cons.1 hm with hxEnd | hxRest
      · have he : r.getLastD a ∈ a :: r := List.getLastD_mem_cons
        rw [← hxEnd] at he
        rcases List.mem_cons.1 he with rfl | hxR
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem a (List.mem_append.2 (Or.inl hxR))
      · exact List.mem_cons_of_mem a (List.mem_append.2 (Or.inr hxRest))

/-- Every restored piece has its starting vertex, even before any
nonemptiness assumption is made on the reached-vertex chunks. -/
theorem chunkVertexPaths_nonempty {α : Type u} (a : α) (chunks : List (Bool × List α))
    {c : Bool × List α} (hc : c ∈ chunkVertexPaths a chunks) : c.2 ≠ [] := by
  induction chunks generalizing a with
  | nil => simp [chunkVertexPaths] at hc
  | cons cr rs ih =>
    rcases cr with ⟨color, r⟩
    rcases List.mem_cons.1 hc with rfl | htail
    · exact List.cons_ne_nil _ _
    · exact ih (r.getLastD a) htail

/-- A restored chunk keeps its color unchanged. -/
theorem chunkVertexPaths_colors {α : Type u} (a : α) (chunks : List (Bool × List α)) :
    (chunkVertexPaths a chunks).map Prod.fst = chunks.map Prod.fst := by
  induction chunks generalizing a with
  | nil => rfl
  | cons cr rs ih =>
    rcases cr with ⟨c, r⟩
    simp only [chunkVertexPaths, List.map_cons, ih]

/-- There is one restored vertex list for each chunk. -/
theorem chunkVertexPaths_length {α : Type u} (a : α) (chunks : List (Bool × List α)) :
    (chunkVertexPaths a chunks).length = chunks.length := by
  have h := congrArg List.length (chunkVertexPaths_colors a chunks)
  simpa only [List.length_map] using h

end GraphMinor.GM02
