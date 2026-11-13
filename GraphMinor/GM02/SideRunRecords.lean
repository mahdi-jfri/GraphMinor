module

public import GraphMinor.GM02.SideRunWalk
public import GraphMinor.GM02.DartChunkVertices
import GraphMinor.GM02.AlternatingChunkDisjoint

/-!
# Vertex records for the side runs of a path

The reached-vertex records of all runs join to the original path's support.
They are nonempty and alternate in color. Restoring their starting vertices
therefore gives full run vertex lists, with disjoint lists on each side.
This translates the run construction in corrected II (2.9) into the data
needed for its two terminations.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph List Set Classical
universe u v

/-- Color and reached-vertex records for the maximal side runs. -/
noncomputable def sideRunRecords {α : Type u} {β : Type v} {G : Graph α β}
    (H : Graph α β) {a b : α} (p : (pathGraph G).Walk a b) :=
  (sideRuns H p).map (dartTailRecord (separationEdgeColor H))

/-- Flattening the reached vertices recovers the original path support. -/
theorem sideRunRecords_flatten {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) :
    a :: ((sideRunRecords H p).map Prod.snd).flatten = p.support := by
  simp only [sideRunRecords, List.map_map, Function.comp_def, dartTailRecord]
  rw [← List.map_flatten]
  have heq : (sideRuns H p).flatten = p.darts := flatten_coloredRuns _ _
  rw [heq]
  exact p.cons_map_snd_darts

/-- Every run record contains at least one reached vertex. -/
theorem sideRunRecords_nonempty {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) : ∀ c ∈ sideRunRecords H p, c.2 ≠ [] := by
  intro c hc
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  change r.map (fun d => d.snd) ≠ []
  intro hm
  have hl := congrArg List.length hm
  simp only [List.length_map, List.length_nil] at hl
  exact coloredRun_ne_nil hr (List.length_eq_zero_iff.1 hl)

/-- Neighboring run records have opposite colors. -/
theorem sideRunRecords_alternate {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) :
    (sideRunRecords H p).IsChain (fun c d => c.1 ≠ d.1) := by
  apply (List.isChain_map _).2
  have hc := coloredRuns_alternate (separationEdgeColor H) p.darts
  apply List.IsChain.imp_of_mem_tail_imp (p := hc)
  intro r s hr hs hdiff
  obtain ⟨hneR, hneS, hdiff⟩ := hdiff
  rw [dartTailRecord_color _ hneR, dartTailRecord_color _ hneS]
  have hlast := coloredRun_color_eq_head hr (List.getLast_mem hneR)
  exact fun heq => hdiff (hlast.trans heq)

/-- Restored records are the full vertex lists of the corresponding runs. -/
theorem sideRunRecords_restore {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) :
    chunkVertexPaths a (sideRunRecords H p) =
      (sideRuns H p).map (dartFullRecord (separationEdgeColor H) a) := by
  apply chunkVertexPaths_dart_records
  · exact fun _ hr => coloredRun_ne_nil hr
  · have heq : (sideRuns H p).flatten = p.darts := flatten_coloredRuns _ _
    rw [heq]
    exact p.isChain_dartAdj_darts
  · have heq : (sideRuns H p).flatten = p.darts := flatten_coloredRuns _ _
    rw [heq]
    cases p with
    | nil => intro d hd; simp at hd
    | cons h q => intro d hd; have hd' := Option.mem_some_iff.1 hd; exact (congrArg (fun e => e.fst) hd').symm

/-- In a path, full vertex records on the same side are disjoint. -/
theorem sideRunRecords_pairwise {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (hp : p.IsPath) :
    ((sideRuns H p).map (dartFullRecord (separationEdgeColor H) a)).Pairwise
      (fun c d => c.1 = d.1 → Disjoint {x | x ∈ c.2} {x | x ∈ d.2}) := by
  rw [← sideRunRecords_restore]
  apply chunkVertexPaths_same_color_disjoint a _ (sideRunRecords_nonempty p)
    (sideRunRecords_alternate p)
  rw [sideRunRecords_flatten]
  exact hp.support_nodup

end GraphMinor.GM02
