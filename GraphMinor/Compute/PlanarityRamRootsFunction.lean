module

public import GraphMinor.Compute.PlanarityRamPostorder
import Init.Data.Range.Lemmas

/-!
# Exposing the root scan of the functional DFS

`depthFirstSearch` scans roots using a bounded `for` loop and stops at a
failed component search. The recursive list form here exposes that same
control flow for the RAM root-loop proof. The final completion reversal
is applied only after all roots succeed.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The outer root scan, with exactly the component call of `depthFirstSearch`. -/
def searchRoots (adj : Array (List ℕ)) (fuel : ℕ) : List ℕ → Search → Option Search
  | [], search => some search
  | root :: roots, search =>
    if (search.depth[root]?.join).isNone then
      let marked := { search with depth := search.depth.set! root (some 0) }
      (searchFrames adj fuel marked [⟨root, 0⟩]).bind fun next => searchRoots adj fuel roots next
    else searchRoots adj fuel roots search

/-- The accumulator and early-return tags produced by the functional `for` loop. -/
def rootFoldBody (adj : Array (List ℕ)) (fuel root : ℕ)
    (state : Option (Option Search) × Search) : Id (ForInStep (Option (Option Search) × Search)) :=
  let search := state.2
  if (search.depth[root]?.join).isNone then
    let marked := { search with depth := search.depth.set! root (some 0) }
    match searchFrames adj fuel marked [⟨root, 0⟩] with
    | none => pure (.done (some none, marked))
    | some next => pure (.yield (none, next))
  else pure (.yield (none, search))

/-- Read the root loop's early-return tag, or reverse its final completion list. -/
def rootFoldResult (adj : Array (List ℕ)) (fuel : ℕ) (roots : List ℕ) (search : Search) : Option Search :=
  let state : Option (Option Search) × Search :=
    (forIn roots (none, search) (rootFoldBody adj fuel)).run
  match state.1 with
  | some result => result
  | none => some (reversePostorder state.2)

/-- The recursive root scan is exactly the bounded-loop root scan, including failure. -/
theorem rootFoldResult_eq (adj : Array (List ℕ)) (fuel : ℕ) (roots : List ℕ) (search : Search) :
    rootFoldResult adj fuel roots search = (searchRoots adj fuel roots search).map reversePostorder := by
  induction roots generalizing search with
  | nil => rfl
  | cons root roots ih =>
    by_cases fresh : (search.depth[root]?.join).isNone = true
    · cases hc : searchFrames adj fuel { search with depth := search.depth.set! root (some 0) } [⟨root, 0⟩] with
      | none =>
        simp only [rootFoldResult, List.forIn_cons, rootFoldBody, fresh, ↓reduceIte, hc,
          searchRoots, Option.bind_none, Option.map_none]
        rfl
      | some next =>
        simp only [rootFoldResult, List.forIn_cons, rootFoldBody, fresh, ↓reduceIte, hc,
          searchRoots, Option.bind_some]
        change rootFoldResult adj fuel roots next = _
        exact ih next
    · simp only [rootFoldResult, List.forIn_cons, rootFoldBody, fresh, Bool.false_eq_true,
        ↓reduceIte, searchRoots]
      change rootFoldResult adj fuel roots search = _
      exact ih search

set_option linter.auxLemma false in
/-- The functional DFS is the recursive root scan followed by its final reversal.
The proof unfolds the matchers used by the loop's early-return elaboration. -/
theorem depthFirstSearch_eq_searchRoots (adj : Array (List ℕ)) :
    depthFirstSearch adj =
      (searchRoots adj (adj.foldl (fun total l => total + l.length) 0 + adj.size + 1)
        (List.range adj.size) (initialSearch adj.size)).map reversePostorder := by
  rw [← rootFoldResult_eq]
  simp only [depthFirstSearch, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.range_eq_range']
  unfold rootFoldResult rootFoldBody reversePostorder
  delta Break.runK.match_1 depthFirstSearch.match_1 rootFoldResult.match_1 rootFoldBody.match_1
  simp only [Id.run_bind]
  rfl

end GraphMinor.Compute.PlanarityRam
