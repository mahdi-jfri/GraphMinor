module

public import GraphMinor.Compute.F92SegmentStep

/-!
# The segment arrays in input order

`fBuild` processes the subwalls from last to first. The segment at index `i` is the prefix
of path `i` cut at the segments belonging to larger indices. These identities let the program
store each segment separately while its vertex bitset records the processed suffix.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Array for segment `i`, after the marked subwalls and their input paths. -/
abbrev aSeg92 (a_base k i : ℕ) : Arr := a_base + 13 + 3 * k + i

theorem length_f92Segments {n h k : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (P : Fin k → List (Fin n)) :
    ∀ as, (f92Segments W P as).length = as.length
  | [] => rfl
  | a :: as => by simp only [f92Segments, List.length_cons, length_f92Segments W P as]

/-- The segment associated with an input index. -/
def f92SegmentAt {n h k : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (P : Fin k → List (Fin n)) (i : Fin k) : List (Fin n) :=
  f92Prefix W (f92Segments W P ((List.finRange k).drop (i.val + 1))).flatten.toFinset (P i)

theorem getElem_f92Segments {n h k : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (P : Fin k → List (Fin n)) :
    ∀ (as : List (Fin k)) (i : ℕ) (hi : i < as.length),
      (f92Segments W P as)[i]'(by rw [length_f92Segments]; exact hi) =
        f92Prefix W (f92Segments W P (as.drop (i + 1))).flatten.toFinset (P as[i])
  | [], _, hi => by simp at hi
  | a :: as, 0, _ => rfl
  | a :: as, i + 1, hi => by
    simpa only [f92Segments, List.getElem_cons_succ, List.drop_succ_cons] using
      getElem_f92Segments W P as i (by simpa using hi)

/-- The stored segment family, in increasing input order, is exactly the segment list. -/
theorem f92Segments_eq_ofFn {n h k : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (P : Fin k → List (Fin n)) :
    f92Segments W P (List.finRange k) = List.ofFn (f92SegmentAt W P) := by
  apply List.ext_getElem
  · simp [length_f92Segments]
  · intro i hi hj
    have hi' : i < k := by simpa using hj
    rw [getElem_f92Segments W P (List.finRange k) i (by simpa using hi')]
    simp [f92SegmentAt]

theorem f92Segments_suffix_cons {n h k i : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (P : Fin k → List (Fin n)) (hi : i < k) :
    f92Segments W P ((List.finRange k).drop i) =
      f92SegmentAt W P ⟨i, hi⟩ :: f92Segments W P ((List.finRange k).drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp [f92Segments, f92SegmentAt]

/-- The bitset for the processed suffix grows by precisely the new segment vertices. -/
theorem f92Segments_suffix_vertices {n h k i : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (P : Fin k → List (Fin n)) (hi : i < k) :
    (f92Segments W P ((List.finRange k).drop i)).flatten.toFinset =
      (f92Segments W P ((List.finRange k).drop (i + 1))).flatten.toFinset ∪
        (f92SegmentAt W P ⟨i, hi⟩).toFinset := by
  rw [f92Segments_suffix_cons W P hi, List.flatten_cons, List.toFinset_append, Finset.union_comm]

end GraphMinor.Compute.Alg92
