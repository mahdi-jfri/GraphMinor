module

public import GraphMinor.Compute.CrossingLiftReplacementSearchSpec
public import GraphMinor.Compute.CrossingLiftReadEnds
public import GraphMinor.Compute.CrossingLiftCutScan
public import GraphMinor.Compute.CrossingLiftBoundarySplice
public import GraphMinor.Compute.CrossingLiftPatch

/-!
# Reversing one path through a replacement

When a path uses a new boundary edge, the program computes the search bound and its first
and last boundary visits. It searches the recorded component between those visits and
splices the result into the path. These are the reverse steps of Lemma 1, Section 3.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Compute the bound and cuts, search the component, splice, and return the path in place. -/
def liftReplacementPathProg (path boundary component edges tmp R A : ℕ) : Cmd :=
  .seq (liftVertexBoundProg boundary component (R + 50) (R + 200))
    (.seq (liftCutScanProg path boundary (R + 1) (R + 2) (R + 200))
      (.seq (liftReadSearchEndsProg path (R + 1) (R + 2) (R + 84) (R + 85))
        (.seq (liftBuildSearchProg edges component (R + 10) A)
          (.seq (liftSpliceProg path (A + 66) tmp (R + 1) (R + 2) (R + 200))
            (liftCopyPathProg tmp path (R + 200))))))

private theorem splice_length_le {N : ℕ} (S : Finset (Fin N)) (L Y : List (Fin N)) :
    (spliceBetween S L Y).length ≤ 2 * L.length + Y.length := by
  have h₁ := (List.takeWhile_prefix (fun x => decide (x ∉ S)) (l := L)).length_le
  have h₂ := (List.takeWhile_prefix (fun x => decide (x ∉ S)) (l := L.reverse)).length_le
  simp only [List.length_reverse] at h₂
  simp only [spliceBetween, List.length_append, List.length_reverse]
  omega

/-- Lemma 1's affected-path program runs without assuming a search result. Replacement
validity and a new edge supply the search endpoints and reachability. The remaining
hypotheses describe the recorded lists, their memory layout and word bounds. -/
theorem liftReplacementPathProg_exec {w N : ℕ} (r : ReplRecord (Fin N))
    (D L B C : List (Fin N)) (E : List (Fin N × Fin N))
    (hvalid : r.IsValid D) (hchain : L.IsChain r.newGraph.Adj) (hnew : usesNewEdge r.graph L)
    (hBnd : B.Nodup) (hBsmall : B.length ≤ 3) (hB : ∀ x, x ∈ B ↔ x ∈ r.boundary)
    (hC : ∀ x, x ∈ C ↔ x ∈ r.rep) (hEnd : E.Nodup)
    (hE : ∀ a b, (a, b) ∈ E ↔ r.graph.Adj a b ∧
      (a ∈ r.rep ∨ a ∈ r.boundary) ∧ (b ∈ r.rep ∨ b ∈ r.boundary))
    (path boundary component edges tmp R A : ℕ)
    (hpt : path ≠ tmp) (hpA : path < A)
    (hcA : component < A) (heA : edges < A) (htA : tmp < A) (s : State)
    (hp : s.arrs path = L.map Fin.val) (hb : s.arrs boundary = B.map Fin.val)
    (hc : s.arrs component = C.map Fin.val) (he : s.arrs edges = E.flatMap encPair)
    (hw : 1024 * (N + L.length + B.length + C.length + E.length + 1) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (Y : List (Fin N)),
      Exec w (liftReplacementPathProg path boundary component edges tmp R A) s s' t ∧
      t ≤ 2000 * (N + L.length + B.length + C.length + E.length + 1) ∧
      IsReplSearchPath r L Y ∧ s'.arrs path = (spliceBetween r.boundary L Y).map Fin.val ∧
      (∀ a < A, a ≠ path → a ≠ tmp → s'.arrs a = s.arrs a) ∧
      (∀ k < R, s'.regs k = s.regs k) := by
  obtain ⟨Y₀, p, q, hfirst, hlast, _, _⟩ := liftReplacementSearch_exists hvalid hchain hnew
  obtain ⟨s1, t1, he1, ht1, hn1, ha1, hr1⟩ := liftVertexBoundProg_exec (w := w)
    boundary component (R + 50) (R + 200) (by omega) B C s hb hc (by omega)
  obtain ⟨s2, t2, he2, ht2, hlo2, hhi2, ha2, hr2⟩ := liftCutScanProg_exec (w := w)
    path boundary (R + 1) (R + 2) (R + 200) (by omega) (by omega) (by omega)
    L B hBnd hBsmall s1 ((ha1 _).trans hp) ((ha1 _).trans hb) (by omega)
  obtain ⟨s3, he3, hu3, hv3, ha3, hr3⟩ := liftReadSearchEndsProg_exec (w := w)
    path (R + 1) (R + 2) (R + 84) (R + 85) (by omega) (by omega)
    B L r.boundary hB p q hfirst hlast s2 ((ha2 _).trans ((ha1 _).trans hp)) hlo2 hhi2 (by omega)
  have hn3 : s3.regs (R + 10 + 40) = liftVertexBound (B ++ C) 0 := by
    have hh := (hr3 (R + 50) (by omega) (by omega)).trans
      ((hr2 (R + 50) (by omega) (by omega) (by omega)).trans hn1)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hh
  obtain ⟨s4, t4, Y, he4, ht4, hY, ho4, ha4, hr4⟩ := liftBuildSearchProg_exec_replacement (w := w)
    r D L B C E hvalid hB hC hEnd hE p q hfirst hlast edges component (R + 10) A heA hcA s3
    ((ha3 _).trans ((ha2 _).trans ((ha1 _).trans he)))
    ((ha3 _).trans ((ha2 _).trans ((ha1 _).trans hc))) hn3
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hu3)
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hv3) (by omega)
  have hYlen : Y.length ≤ N := by
    obtain ⟨_, _, _, _, hpath, _⟩ := hY
    simpa only [Fintype.card_fin] using hpath.2.1.length_le_card
  have hlo4 : s4.regs (R + 1) = liftFirstBoundaryIndex B L :=
    (hr4 _ (by omega)).trans ((hr3 _ (by omega) (by omega)).trans hlo2)
  have hhi4 : s4.regs (R + 2) = liftAfterLastBoundaryIndex B L :=
    (hr4 _ (by omega)).trans ((hr3 _ (by omega) (by omega)).trans hhi2)
  have hp4 : s4.arrs path = L.map Fin.val :=
    (ha4 _ hpA).trans ((ha3 _).trans ((ha2 _).trans ((ha1 _).trans hp)))
  obtain ⟨s5, t5, he5, ht5, ho5, ha5, hr5⟩ := liftSpliceProg_exec_boundary (w := w)
    path (A + 66) tmp (R + 1) (R + 2) (R + 200) hpt (by omega) (by omega) (by omega)
    B L Y r.boundary hB p q hfirst hlast s4 hp4 ho4 hlo4 hhi4 (by omega)
  have hlen := splice_length_le r.boundary L Y
  have hwords : ∀ x ∈ (spliceBetween r.boundary L Y).map Fin.val, x < 2 ^ w := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact v.isLt.trans (by omega)
  obtain ⟨s6, t6, he6, ht6, ho6, ha6, hr6⟩ := liftCopyPathProg_exec (w := w)
    tmp path (R + 200) (Ne.symm hpt) _ s5 ho5 hwords (by simp only [List.length_map]; omega)
  refine ⟨s6, t1 + (t2 + (8 + (t4 + (t5 + t6)))), Y,
    .seq he1 (.seq he2 (.seq he3 (.seq he4 (.seq he5 he6)))), ?_, hY, ho6, ?_, ?_⟩
  · simp only [List.length_map] at ht6; omega
  · intro a ha hap hat
    exact (ha6 a hap).trans ((ha5 a hat).trans ((ha4 a ha).trans
      ((ha3 a).trans ((ha2 a).trans (ha1 a)))))
  · intro k hk
    exact (hr6 k (by omega)).trans ((hr5 k (by omega)).trans ((hr4 k (by omega)).trans
      ((hr3 k (by omega) (by omega)).trans ((hr2 k (by omega) (by omega) (by omega)).trans
        (hr1 k (by omega) (by omega))))))

end GraphMinor.Compute.Crossing
