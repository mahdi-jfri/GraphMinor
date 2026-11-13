module

public import GraphMinor.GM02.ChunkVertexPaths
import Mathlib.Data.List.Chain

/-!
# Intersections between consecutive simple-path chunks

Distinct pieces cut from one simple path can meet only at their joining
endpoints. The first piece is disjoint from all later reached-vertex
chunks, so a shared vertex must be its last vertex. In the remaining
path this is the initial vertex and can occur only at a piece's start.
This controls opposite-side intersections and reservations in corrected
II (2.9).
-/

public section
namespace GraphMinor.GM02
open List Set
universe u

private theorem lastD_eq_last {α : Type u} (a : α) {r : List α} (hr : r ≠ []) :
    r.getLastD a = r.getLast hr := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hr, Option.getD_some]

private theorem lastD_mem {α : Type u} (a : α) {r : List α} (hr : r ≠ []) :
    r.getLastD a ∈ r := by
  rw [lastD_eq_last a hr]
  exact List.getLast_mem hr

/-- The initial vertex of a simple chunked path can occur only as the
first vertex of a piece. -/
theorem chunkVertexPaths_start_mem_head {α : Type u} (a : α)
    (chunks : List (Bool × List α)) (hne : ∀ c ∈ chunks, c.2 ≠ [])
    (hnd : (a :: (chunks.map Prod.snd).flatten).Nodup)
    {q : Bool × List α} (hq : q ∈ chunkVertexPaths a chunks) (ha : a ∈ q.2) : a ∈ q.2.head? := by
  cases chunks with
  | nil => simp [chunkVertexPaths] at hq
  | cons cr rs =>
    rcases cr with ⟨c, r⟩
    rcases List.mem_cons.1 hq with rfl | htail
    · rfl
    · have hnot : a ∉ r ++ (rs.map Prod.snd).flatten := (List.nodup_cons.1 hnd).1
      have hm := mem_chunkVertexPaths (r.getLastD a) rs htail ha
      rcases List.mem_cons.1 hm with heq | hm
      · have hr := lastD_mem a (hne (c, r) List.mem_cons_self)
        exact (hnot (List.mem_append.2 (Or.inl (heq.symm ▸ hr)))).elim
      · exact (hnot (List.mem_append.2 (Or.inr hm))).elim

/-- Shared vertices of two ordered pieces are the earlier piece's last
vertex and the later piece's first vertex. -/
theorem chunkVertexPaths_intersections {α : Type u} (a : α)
    (chunks : List (Bool × List α)) (hne : ∀ c ∈ chunks, c.2 ≠ [])
    (hnd : (a :: (chunks.map Prod.snd).flatten).Nodup) :
    (chunkVertexPaths a chunks).Pairwise (fun c d => ∀ x ∈ c.2, x ∈ d.2 →
      x ∈ c.2.getLast? ∧ x ∈ d.2.head?) := by
  induction chunks generalizing a with
  | nil => exact List.Pairwise.nil
  | cons cr rs ih =>
    rcases cr with ⟨c, r⟩
    have hr := hne (c, r) List.mem_cons_self
    have hneTail := fun d hd => hne d (List.mem_cons_of_mem _ hd)
    have hparts : ((a :: r) ++ (rs.map Prod.snd).flatten).Nodup := hnd
    have hsplit := List.nodup_append.1 hparts
    have hlast : r.getLastD a ∈ a :: r := List.mem_cons_of_mem a (lastD_mem a hr)
    have htail : (r.getLastD a :: (rs.map Prod.snd).flatten).Nodup :=
      List.nodup_cons.2 ⟨fun h => hsplit.2.2 _ hlast _ h rfl, hsplit.2.1⟩
    apply List.pairwise_cons.2
    constructor
    · intro q hq x hxFirst hxQ
      have hm := mem_chunkVertexPaths (r.getLastD a) rs hq hxQ
      have hx : x = r.getLastD a := by
        rcases List.mem_cons.1 hm with hx | hxTail
        · exact hx
        · exact (hsplit.2.2 x hxFirst x hxTail rfl).elim
      subst x
      constructor
      · have heq : (a :: r).getLast (List.cons_ne_nil a r) = r.getLastD a := by
          rw [← lastD_eq_last a (List.cons_ne_nil a r), List.getLastD_cons]
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a r), heq]
        rfl
      · exact chunkVertexPaths_start_mem_head (r.getLastD a) rs hneTail htail hq hxQ
    · exact ih (r.getLastD a) hneTail htail

end GraphMinor.GM02
