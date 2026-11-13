module

public import GraphMinor.Compute.PlanarityRamScan

/-!
# Refining one RAM frame iteration

The RAM loads the top frame, compares its next index with the input slice
length, and invokes either completion or scanning. The functional step
uses the same test. Its data/ownership invariants supply every bound used
by the local programs, and the record budget supplies free record slots.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- A represented valid nonempty frame step executes in at most 200 steps
and represents the exact `frameStep` result. All hypotheses concern the
input encoding, state invariants, record capacity, and word bounds. -/
theorem searchFrameStepProg_refines {N M w : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : State} {search : Search} {stack : List Frame} {f : Frame}
    (hadj : IsAdjList G 30 31 32 lists s)
    (h : DfsSearchAt N M s search) (hf : FramesAt N s (f :: stack))
    (hb : SearchBounded N search)
    (hs : FrameInvariant (List.ofFn lists).toArray search (f :: stack))
    (hbudget : search.edges.size + searchWork (List.ofFn lists).toArray 0 search (f :: stack) ≤ M)
    (hw : 2 * (N + M + 2) < 2 ^ w) (hentries : (s.arrs 32).length < 2 ^ w) :
    ∃ next nextStack s' t,
      frameStep (List.ofFn lists).toArray search f stack = some (next, nextStack) ∧
      Exec w searchFrameStepProg s s' t ∧ t ≤ 200 ∧
      FramesAt N s' nextStack ∧ DfsSearchAt N M s' next := by
  let adj := (List.ofFn lists).toArray
  have hadjsize : adj.size = N := by simp [adj]
  have hv : f.vertex < N := by
    have hh := hs.2.2.1 f.vertex (by simp [ownedVertices])
    simpa only [List.size_toArray, List.length_ofFn] using hh
  let vertex : Fin N := ⟨f.vertex, hv⟩
  have hlist : adj[f.vertex]! = lists vertex := by
    rw [getElem!_pos adj f.vertex (by rw [hadjsize]; exact hv)]
    simp [adj, vertex]
  have hcapacity : (f :: stack).length + search.postorder.length ≤ N := by
    simpa only [List.size_toArray, List.length_ofFn] using hs.capacity
  have hnext : f.next ≤ (lists vertex).length := by
    have hh := (hs.2.2.2.2 0 (by simp)).1
    change f.next ≤ adj[f.vertex]!.length at hh
    rwa [hlist] at hh
  have hlen : (lists vertex).length ≤ N := (hadj.2 vertex).2.2.1
  have hk : f.next < 2 ^ w := by omega
  have hn : N < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  obtain ⟨s1, hx1, hf1, h1, hrv, hrk⟩ := loadFrameProg_refines (w := w) hf h
    (by simp only [List.length_cons] at hcapacity; omega) (by omega) hk
  have hAdjArr (a : ℕ) : s1.arrs a = s.arrs a := hx1.arrs_eq_of_not_mem_writtenArrs
    (by simp [loadFrameProg, Cmd.writtenArrs])
  have hadj1 : IsAdjList G 30 31 32 lists s1 := hadj.of_arrs_eq (hAdjArr 30) (hAdjArr 31) (hAdjArr 32)
  have hent1 : (s1.arrs 32).length < 2 ^ w := by rw [hAdjArr]; exact hentries
  have eLen := adjacencyLengthExpr_eval hadj1.1 vertex hrv hn hent1
  have eK : (Expr.reg 42).eval w s1 = some f.next := by
    simpa [Expr.eval, hrk] using checkWord_of_lt hk
  by_cases hdone : (lists vertex).length ≤ f.next
  · have econd : (Expr.op .le (.op .sub (.read 31 (.reg 41)) (.read 30 (.reg 41)))
        (.reg 42)).eval w s1 = some 1 := by
      change (Expr.op .le adjacencyLengthExpr (.reg 42)).eval w s1 = some 1
      rw [Expr.eval, eLen, eK]
      simpa only [BinOp.eval, BinOp.raw, hdone, ↓reduceIte] using checkWord_of_lt hone
    have hpost : search.postorder.length < N := by
      simpa only [List.size_toArray, List.length_ofFn] using hs.completion_room
    have hEdgeCount : search.edges.size ≤ M := Nat.le_trans (Nat.le_add_right _ _) hbudget
    obtain ⟨s2, t2, hx2, ht2, hf2, h2⟩ := completeFrameProg_refines (w := w) h1 hf1 hb hv hrv hpost
      (by simp only [List.length_cons] at hcapacity; omega) (by omega) (by omega)
    refine ⟨finishIncoming { search with postorder := f.vertex :: search.postorder } f.vertex,
      stack, s2, 10 + (7 + t2), ?_, Exec.seq hx1 (Exec.ite_true econd (by decide) hx2),
      by omega, hf2, h2⟩
    change frameStep adj search f stack = _
    have hd : f.next ≥ adj[f.vertex]!.length := by rw [hlist]; exact hdone
    simp only [frameStep, hd, ↓reduceIte]
  · have hscan : f.next < (lists vertex).length := by omega
    have econd : (Expr.op .le (.op .sub (.read 31 (.reg 41)) (.read 30 (.reg 41)))
        (.reg 42)).eval w s1 = some 0 := by
      change (Expr.op .le adjacencyLengthExpr (.reg 42)).eval w s1 = some 0
      rw [Expr.eval, eLen, eK]
      simpa only [BinOp.eval, BinOp.raw, hdone, ↓reduceIte] using
        checkWord_of_lt (show 0 < 2 ^ w by omega)
    obtain ⟨next, nextStack, s2, t2, hstep, hx2, ht2, hf2, h2⟩ := scanNeighborProg_refines
      hadj1 h1 hf1 hb hs hv hscan hrv hrk hbudget hw hent1
    exact ⟨next, nextStack, s2, 10 + (7 + t2), hstep,
      Exec.seq hx1 (Exec.ite_false econd hx2), by omega, hf2, h2⟩

end GraphMinor.Compute.PlanarityRam
