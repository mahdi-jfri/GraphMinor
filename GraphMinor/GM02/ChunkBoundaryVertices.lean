module

public import GraphMinor.GM02.ChunkVertexPaths
import Mathlib.Data.List.Infix

/-!
# Boundary vertices of consecutive path pieces

Contract each nonempty side piece of an original path to the pair of its
ends, as in the forward construction for corrected II (2.9). Its successive
boundary vertices are the original starting vertex followed by the last
vertex of each chunk. This is a sublist of the original vertex list, so
it has no repetitions. In particular the contracted pieces form a path.
-/

@[expose] public section
namespace GraphMinor.GM02
open List
universe u

/-- The successive boundary vertices after contracting the chunks. -/
def chunkBoundaryVertices {α : Type u} (a : α) (chunks : List (Bool × List α)) : List α :=
  a :: chunks.map (fun c => c.2.getLastD a)

private theorem last_mem {α : Type u} (a : α) {r : List α} (hr : r ≠ []) : r.getLastD a ∈ r := by
  cases r with
  | nil => exact (hr rfl).elim
  | cons b bs => simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (l := bs) (a := b))

private theorem chunk_ends_sublist {α : Type u} (a : α) (chunks : List (Bool × List α))
    (hne : ∀ c ∈ chunks, c.2 ≠ []) :
    chunks.map (fun c => c.2.getLastD a) <+ (chunks.map Prod.snd).flatten := by
  induction chunks with
  | nil => exact List.Sublist.refl _
  | cons cr rs ih =>
    rcases cr with ⟨c, r⟩
    have hr : r ≠ [] := hne _ List.mem_cons_self
    have hhead : [r.getLastD a] <+ r := List.singleton_sublist.2 (last_mem a hr)
    have htail := ih (fun d hd => hne d (List.mem_cons_of_mem _ hd))
    exact hhead.append htail

/-- Contraction boundaries occur in the original order of the path. -/
theorem chunkBoundaryVertices_sublist {α : Type u} (a : α) (chunks : List (Bool × List α))
    (hne : ∀ c ∈ chunks, c.2 ≠ []) :
    chunkBoundaryVertices a chunks <+ a :: (chunks.map Prod.snd).flatten :=
  List.Sublist.cons_cons a (chunk_ends_sublist a chunks hne)

/-- Contracting nonempty chunks cannot repeat a vertex of a simple path. -/
theorem chunkBoundaryVertices_nodup {α : Type u} (a : α) (chunks : List (Bool × List α))
    (hne : ∀ c ∈ chunks, c.2 ≠ []) (hnd : (a :: (chunks.map Prod.snd).flatten).Nodup) :
    (chunkBoundaryVertices a chunks).Nodup :=
  (chunkBoundaryVertices_sublist a chunks hne).nodup hnd

end GraphMinor.GM02
