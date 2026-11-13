module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup

/-!
# Erasing closed subwalks without changing edge labels

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) maintains
the vertices and darts of a simple path. A new vertex extends that path.
A repeated vertex truncates it to the earlier occurrence. The list
function below is that chronological stack algorithm. Searching the
stack for its position is explicit. Distinct darts, including the two
darts of a loop or parallel edges, retain their labels.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A directed dart list traces a walk with the stated ends. The
maps give the tail and head of each dart. No simplicity is assumed. -/
inductive GM06DartWalk {D V : Type*} (tail head : D → V) : V → List D → V → Prop
  | nil (v : V) : GM06DartWalk tail head v [] v
  | cons {s t : V} {d : D} {ds : List D} (ht : tail d = s)
      (hw : GM06DartWalk tail head (head d) ds t) :
      GM06DartWalk tail head s (d :: ds) t

/-- A walk's vertex list includes its start and the head of every dart. -/
def gm06WalkVertices {D V : Type*} (head : D → V) (s : V) (ds : List D) : List V :=
  s :: ds.map head

/-- Concatenation preserves the directed walk conditions. -/
theorem GM06DartWalk.append {D V : Type*} {tail head : D → V} {s u t : V}
    {xs ys : List D} (hx : GM06DartWalk tail head s xs u)
    (hy : GM06DartWalk tail head u ys t) : GM06DartWalk tail head s (xs ++ ys) t := by
  induction hx with
  | nil => exact hy
  | cons ht hw ih => exact .cons ht (ih hy)

/-- The empty walk has equal ends. -/
theorem GM06DartWalk.nil_ends {D V : Type*} {tail head : D → V} {s t : V}
    (h : GM06DartWalk tail head s [] t) : s = t := by cases h; rfl

/-- The vertex at position `j` is the end of the first `j` darts. -/
theorem GM06DartWalk.take {D V : Type*} {tail head : D → V} {s t : V}
    {ds : List D} (h : GM06DartWalk tail head s ds t) (j : ℕ) (hj : j ≤ ds.length) :
    GM06DartWalk tail head s (ds.take j)
      ((gm06WalkVertices head s ds)[j]'(by simpa only [gm06WalkVertices, List.length_cons,
        List.length_map] using Nat.lt_succ_of_le hj)) := by
  induction h generalizing j with
  | nil => have hz : j = 0 := Nat.eq_zero_of_le_zero hj
           subst j
           exact .nil _
  | @cons s t d ds ht hw ih =>
    cases j with
    | zero => exact .nil _
    | succ j =>
      have hj' : j ≤ ds.length := Nat.le_of_succ_le_succ hj
      exact .cons ht (ih j hj')

/-- Appending one compatible dart extends a walk to that dart's head. -/
theorem GM06DartWalk.append_one {D V : Type*} {tail head : D → V} {s u : V}
    {ds : List D} (h : GM06DartWalk tail head s ds u) (d : D) (ht : tail d = u) :
    GM06DartWalk tail head s (ds ++ [d]) (head d) :=
  h.append (.cons ht (.nil _))

/-- Truncate to an old vertex, or append the newly arrived dart. -/
def gm06EraseClosedStep {D V : Type*} [DecidableEq V]
    (head : D → V) (s : V) (stack : List D) (d : D) : List D :=
  let vertices := gm06WalkVertices head s stack
  if head d ∈ vertices then stack.take (vertices.idxOf (head d)) else stack ++ [d]

/-- Chronological loop erasure, starting with the supplied dart stack. -/
def gm06EraseClosedAux {D V : Type*} [DecidableEq V]
    (head : D → V) (s : V) (stack : List D) : List D → List D
  | [] => stack
  | d :: ds => gm06EraseClosedAux head s (gm06EraseClosedStep head s stack d) ds

/-- The exact output of ERASE_CLOSED_SUBWALKS in Section 15 of our proof of VI (5.7). The source
vertex is supplied even for an empty walk. -/ def gm06EraseClosedSubwalks {D V : Type*} [DecidableEq
    V] (head : D → V) (s : V) (ds : List D) : List D :=
  gm06EraseClosedAux head s [] ds

private theorem vertices_take {D V : Type*} (head : D → V) (s : V) (ds : List D) (j : ℕ) :
    gm06WalkVertices head s (ds.take j) = (gm06WalkVertices head s ds).take (j + 1) := by
  simp [gm06WalkVertices, List.map_take]

/-- One stack update keeps a simple source path, changes its end
to the new head, and uses a sublist of the old darts plus that dart. -/
theorem gm06EraseClosedStep_spec {D V : Type*} [DecidableEq V]
    {tail head : D → V} {s u : V} {stack : List D}
    (hw : GM06DartWalk tail head s stack u)
    (hn : (gm06WalkVertices head s stack).Nodup) (d : D) (ht : tail d = u) :
    GM06DartWalk tail head s (gm06EraseClosedStep head s stack d) (head d) ∧
    (gm06WalkVertices head s (gm06EraseClosedStep head s stack d)).Nodup ∧
    (gm06EraseClosedStep head s stack d).Sublist (stack ++ [d]) := by
  unfold gm06EraseClosedStep
  dsimp only
  split_ifs with hv
  · have hj : (gm06WalkVertices head s stack).idxOf (head d) <
        (gm06WalkVertices head s stack).length := List.idxOf_lt_length_iff.mpr hv
    have hj' : (gm06WalkVertices head s stack).idxOf (head d) ≤ stack.length := by
      simpa only [gm06WalkVertices, List.length_cons, List.length_map, Nat.lt_succ_iff] using hj
    refine ⟨?_, ?_, ?_⟩
    · have hwalk := hw.take _ hj'
      simpa only [List.getElem_idxOf] using hwalk
    · rw [vertices_take]
      exact hn.take
    · exact (List.take_sublist _ _).trans (List.sublist_append_left _ _)
  · refine ⟨hw.append_one d ht, ?_, List.Sublist.refl _⟩
    have heq : gm06WalkVertices head s (stack ++ [d]) =
        gm06WalkVertices head s stack ++ [head d] := by simp [gm06WalkVertices]
    rw [heq, List.nodup_append]
    refine ⟨hn, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    have hb' : b = head d := List.mem_singleton.mp hb
    exact hv (by simpa only [hab, hb'] using ha)

/-- The stack invariant throughout loop erasure. Its end equals
the end of the processed walk and its darts are retained in order. -/
theorem gm06EraseClosedAux_spec {D V : Type*} [DecidableEq V]
    {tail head : D → V} {s u t : V} {stack ds : List D}
    (hw : GM06DartWalk tail head s stack u)
    (hn : (gm06WalkVertices head s stack).Nodup)
    (hd : GM06DartWalk tail head u ds t) :
    GM06DartWalk tail head s (gm06EraseClosedAux head s stack ds) t ∧
    (gm06WalkVertices head s (gm06EraseClosedAux head s stack ds)).Nodup ∧
    (gm06EraseClosedAux head s stack ds).Sublist (stack ++ ds) := by
  induction hd generalizing stack s with
  | nil => exact ⟨hw, hn, by simp [gm06EraseClosedAux]⟩
  | @cons u t d ds ht hd ih =>
    obtain ⟨hw', hn', hs'⟩ := gm06EraseClosedStep_spec hw hn d ht
    obtain ⟨hw'', hn'', hs''⟩ := ih hw' hn'
    refine ⟨hw'', hn'', hs''.trans ?_⟩
    simpa only [List.append_assoc, List.singleton_append] using hs'.append (List.Sublist.refl ds)

/-- Loop erasure returns a simple path with exactly the walk's
ends. Every returned dart, and hence every returned edge, was in
the input walk, in its original order. -/
theorem gm06EraseClosedSubwalks_spec {D V : Type*} [DecidableEq V]
    {tail head : D → V} {s t : V} {ds : List D}
    (hw : GM06DartWalk tail head s ds t) :
    GM06DartWalk tail head s (gm06EraseClosedSubwalks head s ds) t ∧
    (gm06WalkVertices head s (gm06EraseClosedSubwalks head s ds)).Nodup ∧
    (gm06EraseClosedSubwalks head s ds).Sublist ds := by
  simpa only [gm06EraseClosedSubwalks, List.nil_append] using
    gm06EraseClosedAux_spec (GM06DartWalk.nil s) (by simp [gm06WalkVertices]) hw

end GraphMinor.Compute
