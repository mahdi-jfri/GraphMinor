module

public import GraphMinor.GM02.ChunkVertexPaths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.List.Chain

/-!
# Vertex records of consecutive dart chunks

The forward construction in corrected II (2.9) groups a path's darts by
side. Each chunk records its reached vertices. The dart-chain condition
identifies its first vertex with the previous chunk's last vertex.
Consequently restoring the chunk starts recovers exactly the full vertex
list of each run, in order.
-/

@[expose] public section
namespace GraphMinor.GM02
open SimpleGraph List
universe u

/-- The color and reached vertices of a dart chunk. Empty chunks use an
arbitrary default color, and are excluded in the applications. -/
def dartTailRecord {α : Type u} {F : SimpleGraph α} (color : F.Dart → Bool)
    (r : List F.Dart) : Bool × List α :=
  ((r.head?.map color).getD true, r.map (fun d => d.snd))

/-- The full vertex record, including the first dart's initial vertex. -/
def dartFullRecord {α : Type u} {F : SimpleGraph α} (color : F.Dart → Bool)
    (a : α) (r : List F.Dart) : Bool × List α :=
  ((r.head?.map color).getD true, (r.map (fun d => d.fst)).headD a :: r.map (fun d => d.snd))

/-- The color of a nonempty dart record is its first dart's color. -/
theorem dartTailRecord_color {α : Type u} {F : SimpleGraph α} (color : F.Dart → Bool)
    {r : List F.Dart} (hr : r ≠ []) : (dartTailRecord color r).1 = color (r.head hr) := by
  cases r with
  | nil => exact (hr rfl).elim
  | cons d ds => rfl

private theorem fullRecord_default {α : Type u} {F : SimpleGraph α} (color : F.Dart → Bool)
    (a b : α) {r : List F.Dart} (hr : r ≠ []) : dartFullRecord color a r = dartFullRecord color b r := by
  cases r with
  | nil => exact (hr rfl).elim
  | cons d ds => rfl

private theorem lastD_eq_last {α : Type u} (a : α) {r : List α} (hr : r ≠ []) :
    r.getLastD a = r.getLast hr := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hr, Option.getD_some]

/-- Restoring starts of consecutive nonempty dart chunks gives their full
vertex lists. The first dart starts at `a`, and all darts form one chain. -/
theorem chunkVertexPaths_dart_records {α : Type u} {F : SimpleGraph α}
    (color : F.Dart → Bool) (a : α) (runs : List (List F.Dart))
    (hne : ∀ r ∈ runs, r ≠ [])
    (hchain : runs.flatten.IsChain (fun d e => d.snd = e.fst))
    (hstart : ∀ d ∈ runs.flatten.head?, d.fst = a) :
    chunkVertexPaths a (runs.map (dartTailRecord color)) = runs.map (dartFullRecord color a) := by
  induction runs generalizing a with
  | nil => rfl
  | cons r rs ih =>
    have hr : r ≠ [] := hne _ List.mem_cons_self
    have hrs : ∀ s ∈ rs, s ≠ [] := fun s hs => hne s (List.mem_cons_of_mem _ hs)
    have hchain' : (r ++ rs.flatten).IsChain (fun d e => d.snd = e.fst) := hchain
    have htail := hchain'.right_of_append
    let b := (r.map (fun d => d.snd)).getLastD a
    have hrMap : r.map (fun d => d.snd) ≠ [] := by
      intro hm
      have hl := congrArg List.length hm
      simp only [List.length_map, List.length_nil] at hl
      exact hr (List.length_eq_zero_iff.1 hl)
    have hb : b = (r.getLast hr).snd := by
      dsimp [b]
      rw [lastD_eq_last a hrMap, List.getLast_map]
    have htailStart : ∀ d ∈ rs.flatten.head?, d.fst = b := by
      intro d hd
      have hlastMem : r.getLast hr ∈ r.getLast? := by
        rw [List.getLast?_eq_some_getLast hr]
        rfl
      have hc := (List.isChain_append.1 hchain').2.2 (r.getLast hr) hlastMem d hd
      exact hc.symm.trans hb.symm
    have hrec := ih b hrs htail htailStart
    have hdefaults : rs.map (dartFullRecord color b) = rs.map (dartFullRecord color a) := by
      apply List.map_congr_left
      intro s hs
      exact fullRecord_default color b a (hrs s hs)
    rw [hdefaults] at hrec
    cases r with
    | nil => exact (hr rfl).elim
    | cons d ds =>
      have hd : d.fst = a := hstart d (by simp)
      change ((_, a :: (d :: ds).map (fun d => d.snd)) ::
        chunkVertexPaths b (rs.map (dartTailRecord color))) = _
      rw [hrec]
      simp only [List.map_cons, dartFullRecord, List.head?_cons, Option.map_some,
        Option.getD_some, List.map_cons, List.headD_cons]
      rw [hd]

end GraphMinor.GM02
