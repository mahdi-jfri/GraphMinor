module

public import GraphMinor.Crossing.DefsReplace
public import GraphMinor.Crossing.DefsContract

/-!
# The restoration procedure (Section 9.2 of the note)

Section 9.2 of `docs/crossing/crossing_extractor.tex`: "We process the fixed list $M$, once for
each marker. For a marker $z$:

1. If $z$ has been deleted, skip it.
2. If $z$ is on the current cycle, skip it. Its edge to $x$ keeps it out of every component that
   does not contain $x$.
3. Form $B=J-w$.
4. Run the bounded-flow computation for three internally disjoint paths from $z$ to $x$ in $B$.
5. If it succeeds, continue with the next marker.
6. Otherwise, obtain the minimum two-cut $\{p,q\}$ with maximum open source side $U$, as in
   Section 2.2.
7. Delete all vertices of $U$ from $H$, and complete the triangle $\{w,p,q\}$.
8. Record one component of $B-\{p,q\}$ inside $U$, for example the component containing $z$, as
   the connected representative for the later lifting."

The flow succeeds exactly when no two vertices of `B` other than `z` separate `z` from `x`
(vertex Menger), so step 5 is the case `IsUnseparable B _ z x 2`.

* `restoreRecord H S D w z p q`: the replacement of step 7, with the record of step 8.
* `IsRestoreStep`, `IsRestoreRun`: one step, and the run over the list of markers.
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- The vertex set of `B = J - w`, where `J = H + x` and `H` has vertex set `S`. -/
def restoreVerts (S : Set V) (w : V) : Set (Option V) :=
  apexVerts S \ {some w}

/-- **The replacement of a restoration step** (Section 9.2, steps 7 and 8), for the current graph
`H` with vertex set `S`, the cycle `D`, the merged vertex `w`, the marker `z` and the cut
`{p, q}`. The deleted set is the source side `U` of the cut in `B = J - w`; the boundary is
`{w, p, q}`; the recorded component is the component of `z` in `H[U]`. -/
def restoreRecord (H : SimpleGraph V) (S : Set V) (D : List V) (w z p q : V) : ReplRecord V :=
  let U : Set V :=
    {y | some y ∈ sourceSide (apex H D) (restoreVerts S w) none {some p, some q}}
  { graph := H, verts := S, deleted := U, boundary := {w, p, q},
    rep := {y | ReachIn H U z y} }

/-- **One restoration step** at the marker `z` (Section 9.2), from the graph `H` with vertex set
`S` to the graph `H'` with vertex set `S'`, with the record `rec` of the replacement, if any. -/
def IsRestoreStep (D : List V) (w z : V) (H : SimpleGraph V) (S : Set V)
    (H' : SimpleGraph V) (S' : Set V) (rec : Option (ReplRecord V)) : Prop :=
  ((z ∉ S ∨ z ∈ D ∨ IsUnseparable (apex H D) (restoreVerts S w) (some z) none 2) ∧
      H' = H ∧ S' = S ∧ rec = none) ∨
    (z ∈ S ∧ z ∉ D ∧ ¬ IsUnseparable (apex H D) (restoreVerts S w) (some z) none 2 ∧
      ∃ p q : V, p ≠ q ∧
        IsMaxSourceSeparator (apex H D) (restoreVerts S w) (some z) none {some p, some q} ∧
        rec = some (restoreRecord H S D w z p q) ∧
        H' = (restoreRecord H S D w z p q).newGraph ∧
        S' = (restoreRecord H S D w z p q).newVerts)

/-- **The restoration run** over a list of markers (Section 9.2: "We process the fixed list $M$,
once for each marker."), from `H` on `S` to `H'` on `S'`, with the list of the records of its
replacements. -/
def IsRestoreRun (D : List V) (w : V) :
    List V → SimpleGraph V → Set V → SimpleGraph V → Set V → List (ReplRecord V) → Prop
  | [], H, S, H', S', recs => H' = H ∧ S' = S ∧ recs = []
  | z :: M, H, S, H', S', recs => ∃ (H₁ : SimpleGraph V) (S₁ : Set V)
      (rec : Option (ReplRecord V)) (recs' : List (ReplRecord V)),
      IsRestoreStep D w z H S H₁ S₁ rec ∧ IsRestoreRun D w M H₁ S₁ H' S' recs' ∧
        recs = rec.toList ++ recs'

end GraphMinor.Crossing
