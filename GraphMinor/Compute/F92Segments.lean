module

public import GraphMinor.Compute.Algorithm92F

/-!
# Computing the segments from first intersections

The construction of `F` adds a path up to its first intersection with earlier segments
outside the wall, including that intersection. The earlier paths used to justify rerouting
need not be stored by the program: the invariant of `fBuild` proves that one contains each
such intersection. This file identifies the simple prefix operation with `fStep` and hence
with the segments of `fSegs`.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Whether a vertex meets the current segments outside the wall. -/
def f92Meets {n h : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (F : Finset (Fin n)) (v : Fin n) : Bool :=
  decide (v ∈ F ∧ v ∉ W.vertexFinset)

/-- Retain a path through its first meeting with `F` outside the wall. -/
def f92Prefix {n h : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (F : Finset (Fin n)) : List (Fin n) → List (Fin n)
  | [] => []
  | v :: vs => v :: if f92Meets W F v then [] else f92Prefix W F vs

theorem length_f92Prefix_le {n h : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (F : Finset (Fin n)) : ∀ P, (f92Prefix W F P).length ≤ P.length
  | [] => by simp [f92Prefix]
  | v :: vs => by
    simp only [f92Prefix, List.length_cons]
    split_ifs
    · simp
    · have := length_f92Prefix_le W F vs; omega

theorem f92Prefix_eq_self_of_none {n h : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (F : Finset (Fin n)) {P : List (Fin n)}
    (hf : P.find? (f92Meets W F) = none) : f92Prefix W F P = P := by
  induction P with
  | nil => rfl
  | cons v vs ih =>
    have hnot := (List.find?_eq_none.mp hf) v List.mem_cons_self
    have htail : vs.find? (f92Meets W F) = none :=
      List.find?_eq_none.mpr (fun y hy => (List.find?_eq_none.mp hf) y (List.mem_cons_of_mem _ hy))
    simp [f92Prefix, hnot, ih htail]

theorem f92Prefix_eq_take_of_some {n h : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (F : Finset (Fin n)) {P : List (Fin n)} {z : Fin n}
    (hf : P.find? (f92Meets W F) = some z) :
    f92Prefix W F P = P.take (P.idxOf z + 1) := by
  obtain ⟨hz, A, B, hsplit, hA⟩ := List.find?_eq_some_iff_append.mp hf
  have hnot : z ∉ A := fun h => by have := hA z h; simp [hz] at this
  have key : ∀ C : List (Fin n), (∀ y ∈ C, f92Meets W F y = false) →
      f92Prefix W F (C ++ z :: B) = C ++ [z] := by
    intro C
    induction C with
    | nil => intro _; simp [f92Prefix, hz]
    | cons v vs ih =>
      intro hC
      have hv := hC v List.mem_cons_self
      have htail := ih (fun y hy => hC y (List.mem_cons_of_mem _ hy))
      simp [f92Prefix, hv, htail]
  have hprefix := key A (fun y hy => by simpa using hA y hy)
  rw [hsplit]
  exact hprefix.trans ((take_idxOf_of_split rfl hnot).2.symm)

/-- The first component of `fStep` needs only the current segment vertices. Coverage by
the earlier paths proves that the second lookup in `fStep` always succeeds after a hit. -/
theorem f92Prefix_eq_fStep {n h : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (P : List (Fin n)) (segs prs : List (List (Fin n)))
    (hcover : ∀ Q ∈ segs, ∀ y ∈ Q, ∃ R ∈ prs, y ∈ R) :
    f92Prefix W segs.flatten.toFinset P = (fStep W P segs prs).1 := by
  have hpred : f92Meets W segs.flatten.toFinset =
      fun y => decide (y ∈ segs.flatten ∧ y ∉ W.vertexFinset) := by
    funext y
    simp [f92Meets]
  cases hf : P.find? (f92Meets W segs.flatten.toFinset) with
  | none =>
    rw [f92Prefix_eq_self_of_none W _ hf]
    simp only [fStep, ← hpred, hf]
  | some z =>
    have hz : z ∈ segs.flatten := by
      have hh : z ∈ segs.flatten.toFinset ∧ z ∉ W.vertexFinset := by
        simpa [f92Meets] using List.find?_some hf
      simpa using hh.1
    obtain ⟨Q, hQ, hzQ⟩ := List.mem_flatten.mp hz
    obtain ⟨R, hR, hzR⟩ := hcover Q hQ z hzQ
    have hex : prs.find? (fun L => decide (z ∈ L)) ≠ none := by
      intro hnone
      have hnot := List.find?_eq_none.mp hnone R hR
      exact hnot (by simpa using hzR)
    rw [f92Prefix_eq_take_of_some W _ hf]
    simp only [fStep, ← hpred, hf]
    cases hlookup : prs.find? (fun L => decide (z ∈ L)) with
    | none => exact (hex hlookup).elim
    | some R' => rfl

/-- A version of the segment construction that stores only segment lists. -/
def f92Segments {n h k : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (P : Fin k → List (Fin n)) : List (Fin k) → List (List (Fin n))
  | [] => []
  | a :: as =>
    let segs := f92Segments W P as
    f92Prefix W segs.flatten.toFinset (P a) :: segs

/-- The segment-only computation agrees exactly with `fBuild`. The hypotheses are the
path family and disjoint subwalls that the construction itself needs. -/
theorem f92Segments_eq_fBuild {n h k : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) {hs : Fin k → ℕ} (Wsub : ∀ a, WallOfHeight (hs a) G)
    (P : Fin k → List (Fin n))
    (hdisj : ∀ a b, a ≠ b → Disjoint (Wsub a).vertexFinset (Wsub b).vertexFinset)
    (hP : ∀ a, IsSubwallHPath W (Wsub a) (P a)) :
    ∀ as : List (Fin k), as.Nodup → f92Segments W P as = (fBuild W P as).1
  | [], _ => rfl
  | a :: as, hnd => by
    have htail := (List.nodup_cons.mp hnd).2
    have hi := fInv_fBuild hdisj hP as htail
    simp only [f92Segments, fBuild, f92Segments_eq_fBuild W Wsub P hdisj hP as htail]
    rw [f92Prefix_eq_fStep W _ _ _ hi.cover]

/-- On the input subwalls, the segment-only computation is precisely `fSegs`. -/
theorem f92Segments_eq_fSegs {l m p h k r : ℕ} (x : Alg92Input l m p h k r)
    (hr : 1 ≤ r) (P : Fin k → List (Fin x.n))
    (hP : ∀ a, IsSubwallHPath x.W (x.W_sub a) (P a)) :
    f92Segments x.W P (List.finRange k) = fSegs x P :=
  f92Segments_eq_fBuild x.W x.W_sub P (disjoint_sub x hr) hP _ (List.nodup_finRange k)

end GraphMinor.Compute.Alg92
