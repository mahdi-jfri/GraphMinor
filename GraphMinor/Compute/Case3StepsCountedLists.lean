module

public import GraphMinor.Compute.Wall
public import GraphMinor.Compute.Algorithm99TransportMove

/-!
# The counted vertex lists in a wall encoding

Every subdivision path contributes its internal-vertex count followed by
those labels. Renaming the labels leaves both the count and section length
unchanged. These identities give the cursor positions for the in-place wall
renaming scan.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Serialize lists with a length word before each list of mapped labels. -/
def case3CountedLists {α : Type*} (f : α → ℕ) (lists : List (List α)) : List ℕ :=
  lists.flatMap (fun xs => xs.length :: xs.map f)

/-- A counted section is followed by the remaining counted sections. -/
theorem case3CountedLists_cons {α : Type*} (f : α → ℕ) (xs : List α) (lists : List (List α)) :
    case3CountedLists f (xs :: lists) = xs.length :: (xs.map f ++ case3CountedLists f lists) := by
  rfl

/-- Counted serialization respects concatenation of section lists. -/
theorem case3CountedLists_append {α : Type*} (f : α → ℕ) (a b : List (List α)) :
    case3CountedLists f (a ++ b) = case3CountedLists f a ++ case3CountedLists f b := by
  exact List.flatMap_append

/-- Renaming preserves all section lengths, and hence all later cursor positions. -/
theorem case3CountedLists_length_eq {α : Type*} (f g : α → ℕ) (lists : List (List α)) :
    (case3CountedLists f lists).length = (case3CountedLists g lists).length := by
  induction lists with
  | nil => rfl
  | cons xs lists ih => simp only [case3CountedLists_cons, List.length_cons, List.length_append, List.length_map, ih]

/-- Each counted section contributes at least its length word. -/
theorem case3CountedLists_numLists_le {α : Type*} (f : α → ℕ) (lists : List (List α)) :
    lists.length ≤ (case3CountedLists f lists).length := by
  induction lists with
  | nil => exact Nat.le_refl _
  | cons xs lists ih =>
    simp only [case3CountedLists_cons, List.length_cons, List.length_append, List.length_map]
    omega

/-- The next section extends the serialized prefix by exactly its count
word and its mapped vertex labels. -/
theorem case3CountedLists_take_succ {α : Type*} (f : α → ℕ) (lists : List (List α))
    (k : ℕ) (hk : k < lists.length) :
    case3CountedLists f (lists.take (k + 1)) =
      case3CountedLists f (lists.take k) ++ (lists[k]).length :: (lists[k]).map f := by
  rw [List.take_succ_eq_append_getElem hk, case3CountedLists_append]
  simp only [case3CountedLists, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- A wall encoding consists of its header, branch labels, and counted
internal-vertex lists in the fixed elementary-edge order. -/
theorem case3Wall_encList_counted {h n : ℕ} {D : MultiDigraph n} (W : WallOfHeight h D) :
    W.encList = [h, elemWallNumVerts h, (elemWallEdges h).length] ++
      (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1) ++
      case3CountedLists Fin.val ((List.finRange (elemWallEdges h).length).map W.internalVerts) := by
  simp only [WallOfHeight.encList, case3CountedLists, List.flatMap_map]

/-- The moved wall uses the same counted sections and lengths, with each
internal label mapped through its inverse vertex list. -/
theorem case3Wall_moveOrig_encList_counted {h n N : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (B : MultiDigraph N) (orig : Fin n → Fin N) :
    (W.moveOrig B orig).encList = [h, elemWallNumVerts h, (elemWallEdges h).length] ++
      (List.finRange (elemWallNumVerts h)).map (fun u => (orig (W.branchVert u)).1) ++
      case3CountedLists (fun u => (orig u).1) ((List.finRange (elemWallEdges h).length).map W.internalVerts) := by
  simp only [WallOfHeight.encList, WallOfHeight.moveOrig, List.map_map, List.length_map,
    case3CountedLists, List.flatMap_map, Function.comp_def]

end GraphMinor.Compute
