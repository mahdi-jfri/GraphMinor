module

public import GraphMinor.Compute.TwoPathsBfs
public import GraphMinor.Compute.CrossingLiftSearchAppend
public import GraphMinor.Compute.Algorithm101Defs

/-!
# The existing path search for reversing a replacement

Lemma 1 asks for a path between the first and last boundary vertices through the recorded
component. This file uses `TwoPaths.bfsProg` with that component as its allowed inner vertices.
The search's existing completeness theorem supplies a path whenever one exists. The target
is appended to its output, then the whole routine is moved to caller-chosen scratch memory.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph

/-- The existing search followed by appending its target, in its canonical memory layout. -/
def liftReplacementSearchCoreProg : Cmd :=
  .seq TwoPaths.bfsProg (liftAppendSearchEndProg 64 65 66 TwoPaths.rWV 80)

/-- In canonical memory, the existing search writes a full simple path with allowed inner
vertices. Its reachability hypothesis is the ordinary input condition for this search,
not an assumption about any replacement lift. -/
theorem liftReplacementSearchCoreProg_exec {w N : ℕ} (G : SimpleGraph (Fin N))
    (lists : Fin N → List ℕ) (allowed : List (Fin N)) (u v : Fin N) (s : State)
    (hin : TwoPaths.BfsInput G lists allowed u v s)
    (hreach : ∃ W : G.Walk u v, ∀ x ∈ W.support, x ≠ u → x ≠ v → x ∈ allowed)
    (hw : 16 * (N + 1) < 2 ^ w) (hent : (s.arrs 42).length < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (W : G.Walk u v), Exec w liftReplacementSearchCoreProg s s' t ∧
      t ≤ 300 + 100 * N + 30 * totalAdjEntries lists ∧ W.IsPath ∧
      (∀ x ∈ W.support, x ≠ u → x ≠ v → x ∈ allowed) ∧
      s'.arrs 66 = W.support.map Fin.val := by
  obtain ⟨s1, t1, he1, ht1, hr1, ha1, hres⟩ := TwoPaths.bfsProg_result hin (by omega) hent
  have hv1 : s1.regs TwoPaths.rWV = v.val := (hr1 _ (by decide)).trans hin.rv
  have hresult : ∃ W : G.Walk u v, W.IsPath ∧
      (∀ x ∈ W.support, x ≠ u → x ≠ v → x ∈ allowed) ∧
      s1.arrs 64 ++ [v.val] = W.support.map Fin.val ∧
      (s1.arrs 64).length ≤ N ∧ (∀ x ∈ s1.arrs 64, x < 2 ^ w) := by
    classical
    rcases hres.vals with ⟨_, W, hvals, hp, ha⟩ | ⟨_, hfail⟩
    · have heq := (TwoPaths.walkOfVals_vals G _ hvals).symm
      have hlen := hp.support_nodup.length_le_card
      have hm : (s1.arrs 64).length + 1 ≤ N := by
        simpa only [← List.length_map Fin.val, ← heq, List.length_append,
          List.length_singleton, Fintype.card_fin] using hlen
      refine ⟨W, hp, ?_, heq, by omega, ?_⟩
      · intro x hx hxu hxv
        rcases ha x hx with h | h | h
        · exact False.elim (hxu h)
        · exact False.elim (hxv h)
        · exact h
      · intro z hz
        have hz' : z ∈ W.support.map Fin.val := by
          rw [← heq]
          exact List.mem_append_left _ hz
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hz'
        exact x.isLt.trans (by omega)
    · obtain ⟨W, hW⟩ := hreach
      exact False.elim (hfail W hW)
  obtain ⟨W, hWpath, hWallowed, hWprefix, hWlen, hWwords⟩ := hresult
  obtain ⟨s2, t2, he2, ht2, ho2, ha2, hr2⟩ := liftAppendSearchEndProg_exec
    64 65 66 TwoPaths.rWV 80 (by decide) (by decide) (by decide)
    (s1.arrs 64) v.val s1 rfl hv1 hWwords (v.isLt.trans (by omega)) (by omega)
  refine ⟨s2, t1 + t2, W, .seq he1 he2, by omega, hWpath, hWallowed, ho2.trans hWprefix⟩

/-- Move the search and target append to independent caller-chosen register and array blocks. -/
def liftReplacementSearchProg (R A : ℕ) : Cmd := liftReplacementSearchCoreProg.shiftMem R A

/-- The reverse replacement search runs in scratch blocks and preserves all lower caller
memory. Its input is the stored graph, vertex count, endpoints and allowed-vertex labels,
with the ordinary existence of a path having allowed inner vertices. -/
theorem liftReplacementSearchProg_exec {w N : ℕ} (G : SimpleGraph (Fin N))
    (lists : Fin N → List ℕ) (allowed : List (Fin N)) (u v : Fin N) (R A : ℕ) (s : State)
    (hadj : IsAdjList G (A + 40) (A + 41) (A + 42) lists s)
    (hN : s.regs (R + 40) = N) (hu : s.regs (R + TwoPaths.rWU) = u.val)
    (hv : s.regs (R + TwoPaths.rWV) = v.val)
    (hlab : s.arrs (A + TwoPaths.aLab) = List.ofFn (TwoPaths.bfsLabel allowed u v))
    (hreach : ∃ W : G.Walk u v, ∀ x ∈ W.support, x ≠ u → x ≠ v → x ∈ allowed)
    (hw : 16 * (N + 1) < 2 ^ w) (hent : (s.arrs (A + 42)).length < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (W : G.Walk u v), Exec w (liftReplacementSearchProg R A) s s' t ∧
      t ≤ 300 + 100 * N + 30 * totalAdjEntries lists ∧ W.IsPath ∧
      (∀ x ∈ W.support, x ≠ u → x ≠ v → x ∈ allowed) ∧
      s'.arrs (A + 66) = W.support.map Fin.val ∧
      (∀ a < A, s'.arrs a = s.arrs a) ∧ (∀ q < R, s'.regs q = s.regs q) := by
  have hin : TwoPaths.BfsInput G lists allowed u v (s.shiftDown R A) :=
    ⟨hN, hu, hv, hadj.of_arrs_eq rfl rfl rfl, hlab⟩
  obtain ⟨s0, t, W, he, ht, hp, hallowed, ho⟩ := liftReplacementSearchCoreProg_exec
    G lists allowed u v (s.shiftDown R A) hin hreach hw hent
  refine ⟨s.shiftUp R A s0, t, W, he.shiftMem, ht, hp, hallowed, ?_, ?_, ?_⟩
  · simpa only [State.arrs_shiftUp_add] using ho
  · intro a ha; simp [State.shiftUp, ha]
  · intro q hq; simp [State.shiftUp, hq]

end GraphMinor.Compute.Crossing
