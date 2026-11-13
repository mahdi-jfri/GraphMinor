module

public import GraphMinor.GM02.SideRunWalk
public import GraphMinor.GM02.DartChunkVertices
import GraphMinor.GM02.SideRunRecords

/-!
# Disjoint paths among runs of the same side

The generic vertex-record argument for corrected II (2.9) now applies to
the actual run walks. Full dart records are precisely their supports.
Two distinct runs of equal color therefore have disjoint vertex sets.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph List Set Classical
universe u v

/-- Two different members of a pairwise-related list satisfy the relation
in one of their two orders. -/
theorem relation_or_reverse_of_pairwise {δ : Type*} {R : δ → δ → Prop}
    {l : List δ} (h : l.Pairwise R) {a b : δ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    R a b ∨ R b a := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    have hp := List.pairwise_cons.1 h
    rcases List.mem_cons.1 ha with rfl | haTail
    · rcases List.mem_cons.1 hb with rfl | hbTail
      · exact (hne rfl).elim
      · exact Or.inl (hp.1 _ hbTail)
    · rcases List.mem_cons.1 hb with rfl | hbTail
      · exact Or.inr (hp.1 _ haTail)
      · exact ih hp.2 haTail hbTail

/-- The full dart record of a run is its walk's support. -/
theorem sideRunWalk_fullRecord {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (r : List (pathGraph G).Dart)
    (hr : r ∈ sideRuns H p) :
    (dartFullRecord (separationEdgeColor H) a r).2 = (sideRunWalk p r hr).support := by
  have hsupport := (sideRunWalk p r hr).cons_map_snd_darts
  rw [sideRunWalk_darts] at hsupport
  rw [← hsupport]
  cases r with
  | nil => exact (coloredRun_ne_nil hr rfl).elim
  | cons d ds => rfl

/-- Distinct runs of the same color in an original simple path are
vertex-disjoint. Adjacent runs have different colors, so their common
joining vertex never belongs to two pieces assigned to the same side. -/
theorem sideRunWalk_same_color_disjoint {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (hp : p.IsPath)
    (r s : List (pathGraph G).Dart) (hr : r ∈ sideRuns H p) (hs : s ∈ sideRuns H p)
    (hrs : r ≠ s)
    (hc : separationEdgeColor H (r.head (coloredRun_ne_nil hr)) =
      separationEdgeColor H (s.head (coloredRun_ne_nil hs))) :
    Disjoint {x | x ∈ (sideRunWalk p r hr).support}
      {x | x ∈ (sideRunWalk p s hs).support} := by
  have hpair := List.pairwise_map.1 (sideRunRecords_pairwise (H := H) p hp)
  have hcolors : (dartFullRecord (separationEdgeColor H) a r).1 =
      (dartFullRecord (separationEdgeColor H) a s).1 := by
    change (dartTailRecord (separationEdgeColor H) r).1 =
      (dartTailRecord (separationEdgeColor H) s).1
    rw [dartTailRecord_color _ (coloredRun_ne_nil hr),
      dartTailRecord_color _ (coloredRun_ne_nil hs)]
    exact hc
  have hrecords : Disjoint {x | x ∈ (dartFullRecord (separationEdgeColor H) a r).2}
      {x | x ∈ (dartFullRecord (separationEdgeColor H) a s).2} := by
    rcases relation_or_reverse_of_pairwise hpair hr hs hrs with h | h
    · exact h hcolors
    · exact (h hcolors.symm).symm
  rwa [sideRunWalk_fullRecord p r hr, sideRunWalk_fullRecord p s hs] at hrecords

end GraphMinor.GM02
