module

public import GraphMinor.GM02.ChunkVertexPaths
import Mathlib.Data.List.Chain

/-!
# Disjointness of pieces assigned to the same side

Restore the vertex lists of consecutive nonempty edge chunks of a simple
path. Successive chunks have opposite colors. The first chunk can meet the
next one at their joining vertex, but every later chunk lies in the
remaining vertex tail, disjoint from the first. Induction therefore proves
that chunks of the same color have disjoint full vertex lists. This makes
the side pieces in corrected II (2.9) feasible families.
-/

public section
namespace GraphMinor.GM02
open List Set
universe u

private theorem getLastD_mem_of_ne_nil {α : Type u} {r : List α} (a : α) (hr : r ≠ []) :
    r.getLastD a ∈ r := by
  cases r with
  | nil => exact (hr rfl).elim
  | cons b bs => simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (l := bs) (a := b))

/-- Pieces of the same color in an alternating decomposition of a simple
vertex list have disjoint vertex sets. -/
theorem chunkVertexPaths_same_color_disjoint {α : Type u} (a : α)
    (chunks : List (Bool × List α))
    (hne : ∀ c ∈ chunks, c.2 ≠ [])
    (halt : chunks.IsChain (fun c d => c.1 ≠ d.1))
    (hnd : (a :: (chunks.map Prod.snd).flatten).Nodup) :
    (chunkVertexPaths a chunks).Pairwise (fun c d => c.1 = d.1 →
      Disjoint {x | x ∈ c.2} {x | x ∈ d.2}) := by
  induction chunks generalizing a with
  | nil => exact List.Pairwise.nil
  | cons cr rs ih =>
    rcases cr with ⟨c, r⟩
    have hr : r ≠ [] := hne _ (List.mem_cons_self)
    have hparts : ((a :: r) ++ (rs.map Prod.snd).flatten).Nodup := hnd
    have hsplit := List.nodup_append.1 hparts
    have hlast : r.getLastD a ∈ a :: r := List.mem_cons_of_mem a (getLastD_mem_of_ne_nil a hr)
    have htail : (r.getLastD a :: (rs.map Prod.snd).flatten).Nodup :=
      List.nodup_cons.2 ⟨fun h => hsplit.2.2 _ hlast _ h rfl, hsplit.2.1⟩
    apply List.pairwise_cons.2
    constructor
    · intro q hq hcq
      apply Set.disjoint_left.2
      intro x hxFirst hxQ
      have hxTail : x ∈ (rs.map Prod.snd).flatten := by
        cases rs with
        | nil => simp [chunkVertexPaths] at hq
        | cons dr ds =>
          rcases dr with ⟨d, s⟩
          simp only [chunkVertexPaths, List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact (halt.rel hcq).elim
          · have hm := mem_chunkVertexPaths (s.getLastD (r.getLastD a)) ds hq hxQ
            rcases List.mem_cons.1 hm with hxEnd | hxRest
            · have hs : s ≠ [] := hne (d, s) (List.mem_cons_of_mem _ List.mem_cons_self)
              have hlastS := getLastD_mem_of_ne_nil (r.getLastD a) hs
              rw [← hxEnd] at hlastS
              exact List.mem_append.2 (Or.inl hlastS)
            · exact List.mem_append.2 (Or.inr hxRest)
      exact hsplit.2.2 x hxFirst x hxTail rfl
    · exact ih (r.getLastD a) (fun d hd => hne d (List.mem_cons_of_mem _ hd)) halt.of_cons htail

end GraphMinor.GM02
