module

public import GraphMinor.Compute.CrossingLiftEdgeHeader
public import GraphMinor.Compute.CrossingLiftParse
public import GraphMinor.Compute.CrossingLiftLabels
public import GraphMinor.Compute.CrossingLiftSearch

/-!
# Preparing and running the recorded-component search

The reverse search uses only the recorded edges and component. The program orients those
edges, invokes the existing graph parser, prepares the allowed-vertex labels and invokes
the existing BFS program. Each stage is linear in the stored graph and component size.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Build the stored graph and labels, then run the existing allowed-vertex path search. -/
def liftBuildSearchProg (edges component R A : ℕ) : Cmd :=
  .seq (liftEdgeInputProg edges A (R + 40) (R + 100))
    (.seq (liftParseSearchProg R A)
      (.seq (liftSearchLabelsProg component (A + 60) (R + 40) (R + 74) (R + 75) (R + 100))
        (liftReplacementSearchProg R A)))

/-- From the stored directed edges and allowed component, construct a simple path between
stored endpoints whenever such a path exists. All hypotheses describe search input data,
reachability, word bounds or the separation of scratch memory from the input arrays. -/
theorem liftBuildSearchProg_exec {w N : ℕ} (G : SimpleGraph (Fin N))
    (E : List (Fin N × Fin N)) (C : List (Fin N)) (u v : Fin N)
    (edges component R A : ℕ) (heA : edges < A) (hcA : component < A) (s : State)
    (hE : E.Nodup) (hgraph : ∀ a b, (a, b) ∈ E ↔ G.Adj a b)
    (he : s.arrs edges = E.flatMap encPair) (hc : s.arrs component = C.map Fin.val)
    (hn : s.regs (R + 40) = N) (hu : s.regs (R + 74) = u.val)
    (hv : s.regs (R + 75) = v.val)
    (hreach : ∃ W : G.Walk u v, ∀ x ∈ W.support, x ≠ u → x ≠ v → x ∈ C)
    (hw : 32 * (N + C.length + E.length + 1) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (W : G.Walk u v), Exec w (liftBuildSearchProg edges component R A) s s' t ∧
      t ≤ 400 * (N + C.length + E.length + 1) ∧ W.IsPath ∧
      (∀ x ∈ W.support, x ≠ u → x ≠ v → x ∈ C) ∧
      s'.arrs (A + 66) = W.support.map Fin.val ∧
      (∀ a < A, s'.arrs a = s.arrs a) ∧ (∀ q < R, s'.regs q = s.regs q) := by
  let F := liftSearchEdges E
  have hF : IsSimpleEdgeList G F := liftSearchEdges_simple G E hE hgraph
  have hFl : F.length ≤ E.length := liftSearchEdges_length E
  obtain ⟨s1, t1, he1, ht1, ho1, ha1, hr1⟩ := liftEdgeInputProg_exec (w := w)
    edges A (R + 40) (R + 100) N (by omega) (by omega) E s he hn (by omega)
  have hcu1 : s1.arrs component = C.map Fin.val := (ha1 _ (by omega)).trans hc
  have hu1 : s1.regs (R + 74) = u.val := (hr1 _ (by omega)).trans hu
  have hv1 : s1.regs (R + 75) = v.val := (hr1 _ (by omega)).trans hv
  obtain ⟨s2, t2, he2, ht2, hn2, hadj2, hent2, _, hu2, hv2, ha2, hr2⟩ :=
    liftParseSearchProg_exec (w := w) G F _ R A s1 hF ho1 (by omega)
  have hc2 : s2.arrs component = C.map Fin.val := (ha2 _ hcA).trans hcu1
  obtain ⟨s3, t3, he3, ht3, hlab3, ha3, hr3⟩ := liftSearchLabelsProg_exec (w := w)
    component (A + 60) (R + 40) (R + 74) (R + 75) (R + 100)
    (by omega) (by omega) (by omega) C u v s2 hc2 hn2 (hu2.trans hu1) (hv2.trans hv1) (by omega)
  have hadj3 : IsAdjList G (A + 40) (A + 41) (A + 42) (edgeNeighbors F) s3 :=
    hadj2.of_arrs_eq (ha3 _ (by omega)) (ha3 _ (by omega)) (ha3 _ (by omega))
  have hent3 : (s3.arrs (A + 42)).length = 2 * F.length := by rw [ha3 _ (by omega), hent2]
  obtain ⟨s4, t4, W, he4, ht4, hp, hallowed, ho4, ha4, hr4⟩ := liftReplacementSearchProg_exec (w := w)
    G (edgeNeighbors F) C u v R A s3 hadj3
    ((hr3 _ (by omega)).trans hn2)
    (by simpa only [TwoPaths.rWU] using (hr3 (R + 74) (by omega)).trans (hu2.trans hu1))
    (by simpa only [TwoPaths.rWV] using (hr3 (R + 75) (by omega)).trans (hv2.trans hv1)) hlab3 hreach (by omega) (by rw [hent3]; omega)
  have htotal : totalAdjEntries (edgeNeighbors F) = 2 * F.length :=
    sum_length_edgeNeighborsUpTo F hF.1 F.length le_rfl
  refine ⟨s4, t1 + (t2 + (t3 + t4)), W, .seq he1 (.seq he2 (.seq he3 he4)),
    ?_, hp, hallowed, ho4, ?_, ?_⟩
  · rw [htotal] at ht4; omega
  · intro a ha
    exact (ha4 a ha).trans ((ha3 a (by omega)).trans ((ha2 a ha).trans (ha1 a (by omega))))
  · intro q hq
    exact (hr4 q hq).trans ((hr3 q (by omega)).trans ((hr2 q hq).trans (hr1 q (by omega))))

end GraphMinor.Compute.Crossing
