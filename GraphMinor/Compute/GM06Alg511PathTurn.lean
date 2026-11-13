module

public import GraphMinor.Compute.GM06Alg511SelectDarts
public import GraphMinor.Compute.GM06Alg511SelectedWalk
public import GraphMinor.Compute.GM06Alg511CopyDarts
public import GraphMinor.Compute.GM06Alg511TurnBounds
import Mathlib.Tactic

/-!
# Computing the signed turn of the initial path

For VI (5.11), page 134, choose directed edges along the vertex
trace returned by maximum flow, copy their prefix, and sum their
signed edge words. The execution theorem identifies the actual
register difference with the turn of a simple labelled walk. All
choices of parallel edges are made by the verified scans.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Surface

/-- Select the path's directed edges, materialize their list and
compute its signed integer turn in registers 21 and 22. -/
def gm06Alg511PathTurnProg : Cmd :=
  .seq gm06Alg511SelectDartsProg (.seq gm06Alg511CopyDartsProg gm06Alg511TurnSumProg)

/-- The actual path-turn program returns the exact signed turn of a
simple edge-labelled path with the input vertex trace, in quadratic
time. The only extra size conditions bound ordinary machine words. -/
theorem gm06Alg511PathTurnProg_exec {w : ℕ} (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    (turns : List ℤ) (hturnlen : turns.length = rep.pairs.length)
    (a : Fin x.vertexCount) (tail : List (Fin x.vertexCount))
    (hnd : (a :: tail).Nodup)
    (hadj : ∀ i (hi : i + 1 < (a :: tail).length),
      x.flowGraph.Adj (a :: tail)[i] (a :: tail)[i + 1])
    (s : State) (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hends : x.endpoints.length < 2 ^ w)
    (hproduct : x.vertexCount * (gm06Alg511TurnWords turns).sum < 2 ^ w)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x)
    (hwords : s.arrs 11 = gm06Alg511TurnWords turns)
    (hN : s.regs 41 = x.vertexCount)
    (hvertices : IsBufPrefix s 12 42 x.vertexCount ((a :: tail).map Fin.val)) :
    ∃ s' t, Exec w gm06Alg511PathTurnProg s s' t ∧
      t ≤ 29 + x.vertexCount * (89 + 13 * x.endpoints.length) ∧
      (∀ arr, arr ≠ 12 → arr ≠ 13 → s'.arrs arr = s.arrs arr) ∧
      ∃ (b : Fin x.vertexCount) (W : GraphWalk (gm06Alg511LabelGraph rep.pairs) a b),
        W.support = a :: tail ∧ W.IsSimple ∧
        (s'.regs 21 : ℤ) - (s'.regs 22 : ℤ) = gm06Alg511LabelWalkTurn rep.pairs turns W := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, darts, hdlen, hbuf, hdends⟩ :=
    gm06Alg511SelectDartsProg_exec x rep (a :: tail) hadj s (by omega) hn hsquare
      hends hkeys hN hvertices
  have hlen : x.endpoints.length = 2 * rep.pairs.length := by
    have hend : x.endpoints = gm06EndpointWords
        (rep.pairs.map fun p => (p.1.val, p.2.val)) := rep.endpoints
    rw [hend, gm06EndpointWords_length, List.length_map]
  have hdarts : ∀ d ∈ darts, d < 2 * turns.length := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hd
    rw [hturnlen, ← hlen]
    exact (hdends j hj).1
  have hdword : ∀ d ∈ darts, d < 2 ^ w := by
    intro d hd
    exact (hdarts d hd).trans (by rw [hturnlen, ← hlen]; exact hends)
  obtain ⟨s₂, t₂, he₂, ht₂, hpath, hk₂⟩ :=
    gm06Alg511CopyDartsProg_exec x.vertexCount darts s₁ (by omega) hn hbuf hdword
  have hwords₂ : s₂.arrs 11 = gm06Alg511TurnWords turns :=
    (hk₂.2 11 (by decide)).trans ((hk₁.2 11 (by decide)).trans hwords)
  obtain ⟨hpos, hneg⟩ := gm06Alg511TurnSum_word_bounds turns darts hbuf.2.2.1 hdarts hproduct
  obtain ⟨s₃, t₃, he₃, ht₃, harr₃, hsum⟩ := gm06Alg511TurnSum_exec_signed turns darts s₂ hw
    (by rw [hturnlen, ← hlen]; exact hends) (hbuf.2.2.1.trans_lt hn)
    hwords₂ hpath hdarts hpos hneg
  have hwalk : ∃ (b : Fin x.vertexCount)
      (W : GraphWalk (gm06Alg511LabelGraph rep.pairs) a b),
      W.support = a :: tail ∧ gm06Alg511LabelWalkDarts rep.pairs W = darts := by
    have hdlen' : darts.length = tail.length := by simpa using hdlen
    apply gm06Alg511SelectedDarts_exists_walk (n := x.vertexCount)
      rep.pairs a tail darts hnd hdlen'
    intro j hj
    have hh := hdends j hj
    have hend : x.endpoints = gm06EndpointWords
        (rep.pairs.map fun p => (p.1.val, p.2.val)) := rep.endpoints
    rw [hlen, hend] at hh
    exact hh
  obtain ⟨b, W, hsupport, hdW⟩ := hwalk
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, b, W,
    hsupport, ?_, ?_⟩
  · have hdle : darts.length ≤ x.vertexCount := hbuf.2.2.1
    nlinarith [ht₁, ht₂, ht₃]
  · intro arr ha₁ ha₂
    rw [harr₃, hk₂.2 arr (by simpa using ha₁), hk₁.2 arr (by simpa using ha₂)]
  · change W.support.Nodup
    rw [hsupport]
    exact hnd
  · rw [gm06Alg511LabelWalkTurn_eq_dartSum rep.pairs turns hturnlen W, hdW]
    exact hsum

end GraphMinor.Compute
