module

public import GraphMinor.GM02.ChunkBoundaryVertices
public import Mathlib.Data.Sym.Sym2

/-!
# Edges of the contracted boundary path

Contract each nonempty path chunk to the pair of its starting and last
vertices. These pairs are exactly the consecutive edges of the boundary
vertex list. This identifies the union of side-termination pairs with the
contracted paths required in crossing-scheme condition (iv) of II (2.9).
-/

@[expose] public section
namespace GraphMinor.GM02
open List
universe u

private theorem lastD_default {α : Type u} (a b : α) {r : List α} (hr : r ≠ []) :
    r.getLastD a = r.getLastD b := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hr, Option.getD_some]

/-- The last vertices of nonempty chunks do not depend on a default. -/
theorem chunkBoundaryVertices_tail_default {α : Type u} (a b : α)
    (chunks : List (Bool × List α)) (hne : ∀ c ∈ chunks, c.2 ≠ []) :
    (chunkBoundaryVertices a chunks).tail = (chunkBoundaryVertices b chunks).tail := by
  apply List.map_congr_left
  intro c hc
  exact lastD_default a b (hne c hc)

/-- The next boundary is the last vertex of the first chunk. -/
theorem chunkBoundaryVertices_cons {α : Type u} (a : α) (color : Bool) (r : List α)
    (rs : List (Bool × List α)) (hne : ∀ c ∈ rs, c.2 ≠ []) :
    chunkBoundaryVertices a ((color, r) :: rs) =
      a :: chunkBoundaryVertices (r.getLastD a) rs := by
  have h := chunkBoundaryVertices_tail_default a (r.getLastD a) rs hne
  change a :: (r.getLastD a :: (chunkBoundaryVertices a rs).tail) = _
  rw [h]
  rfl

/-- Endpoint pairs obtained by contracting consecutive chunks. -/
def chunkEndpointPairs {α : Type u} (a : α) : List (Bool × List α) → List (Sym2 α)
  | [] => []
  | (_, r) :: rs => s(a, r.getLastD a) :: chunkEndpointPairs (r.getLastD a) rs

/-- The contracted endpoint pairs are precisely the consecutive pairs of
boundary vertices, in the same order. -/
theorem chunkEndpointPairs_eq_zip_boundaries {α : Type u} (a : α)
    (chunks : List (Bool × List α)) (hne : ∀ c ∈ chunks, c.2 ≠ []) :
    chunkEndpointPairs a chunks = List.zipWith (s(·, ·))
      (chunkBoundaryVertices a chunks) (chunkBoundaryVertices a chunks).tail := by
  induction chunks generalizing a with
  | nil => rfl
  | cons cr rs ih =>
    rcases cr with ⟨color, r⟩
    have hneTail := fun c hc => hne c (List.mem_cons_of_mem _ hc)
    rw [chunkBoundaryVertices_cons a color r rs hneTail]
    change s(a, r.getLastD a) :: chunkEndpointPairs (r.getLastD a) rs = _
    rw [ih (r.getLastD a) hneTail]
    rfl

/-- Taking endpoint pairs of full restored records agrees with the
recursive contraction. -/
theorem chunkEndpointPairs_eq_records {α : Type u} (a : α)
    (chunks : List (Bool × List α)) (hne : ∀ c ∈ chunks, c.2 ≠ []) :
    chunkEndpointPairs a chunks = (chunkVertexPaths a chunks).map
      (fun c => s(c.2.headD a, c.2.getLastD a)) := by
  induction chunks generalizing a with
  | nil => rfl
  | cons cr rs ih =>
    rcases cr with ⟨color, r⟩
    have hneTail := fun c hc => hne c (List.mem_cons_of_mem _ hc)
    have hi := ih (r.getLastD a) hneTail
    simp only [chunkEndpointPairs, chunkVertexPaths, List.map_cons, List.headD_cons]
    congr 1
    · rw [List.getLastD_cons]
    · rw [hi]
      apply List.map_congr_left
      intro c hc
      have hnonempty : c.2 ≠ [] := chunkVertexPaths_nonempty (r.getLastD a) rs hc
      have hhead : c.2.headD (r.getLastD a) = c.2.headD a := by
        cases he : c.2 with
        | nil => exact (hnonempty he).elim
        | cons x xs => rfl
      rw [hhead, lastD_default (r.getLastD a) a hnonempty]

private theorem getLastD_append {α : Type u} (a : α) (l r : List α) :
    (l ++ r).getLastD a = r.getLastD (l.getLastD a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, List.getLastD_cons, ih]

/-- The last contracted boundary is the last vertex of the original
reached-vertex list. Contraction preserves both original endpoints. -/
theorem chunkBoundaryVertices_getLastD {α : Type u} (a : α)
    (chunks : List (Bool × List α)) (hne : ∀ c ∈ chunks, c.2 ≠ []) :
    (chunkBoundaryVertices a chunks).getLastD a =
      (a :: (chunks.map Prod.snd).flatten).getLastD a := by
  induction chunks generalizing a with
  | nil => rfl
  | cons cr rs ih =>
    rcases cr with ⟨color, r⟩
    have hneTail := fun c hc => hne c (List.mem_cons_of_mem _ hc)
    let b := r.getLastD a
    have hnon : chunkBoundaryVertices b rs ≠ [] := List.cons_ne_nil _ _
    rw [chunkBoundaryVertices_cons a color r rs hneTail, List.getLastD_cons,
      lastD_default a b hnon, ih b hneTail]
    change (b :: (rs.map Prod.snd).flatten).getLastD b =
      (a :: (r ++ (rs.map Prod.snd).flatten)).getLastD a
    rw [List.getLastD_cons, List.getLastD_cons, getLastD_append]

end GraphMinor.GM02
