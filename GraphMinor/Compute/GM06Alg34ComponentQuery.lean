module

public import GraphMinor.Compute.GM06Alg34ComponentCuffTest
public import GraphMinor.Compute.GM06Alg34InteriorComponent
public import GraphMinor.Compute.GM06Alg34CuffParse

/-!
# Querying whether a supplied component misses the disc cuff

Run breadth-first search from the supplied source label, then scan the
saved cuff stream against its visited bits. The result is exactly the
finite test for VI (3.3)(ii), and all input and adjacency arrays remain
available for the next query or for the deletion payload builder.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Search one component and test that it contains no supplied cuff vertex. -/
def gm06ComponentQueryProg : Cmd := .seq gm06VertexBfsProg gm06ComponentCuffTestProg

private theorem cuff_labels_stream (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) {s : State} (hinput : s.arrs 0 = x.words) :
    AtStream 0 (x.cuffOffset + 2) (L.map Fin.val ++ x.divisionWords) s := by
  refine ⟨[x.n, x.ends.length, x.regions.length] ++ x.endpointWords ++ x.regionWords ++ [1, L.length], ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, x.endpointWords_length,
      GM06DrawingData.cuffOffset] <;> omega
  · rw [hinput, x.words_layout, x.cuffWords_singleton hL]
    simp only [GM06DrawingData.listWords, List.length_map, List.append_assoc, List.cons_append,
      List.nil_append]

private theorem interior_single_cuff (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) (a : Fin x.n) :
    x.isInteriorComponent a = L.all (fun b => decide (¬ x.vertexGraph.Reachable a b)) := by
  apply Bool.eq_iff_iff.mpr
  simp [GM06DrawingData.isInteriorComponent, hL, List.all_eq_true]

/-- A prepared component query returns exactly the cuff-disjointness
bit, with a quadratic search and linear cuff scan. -/
theorem gm06ComponentQueryProg_exec {w : ℕ} (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) (a : Fin x.n) (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hsquare : x.n * x.n < 2 ^ w) (hinputSize : x.words.length < 2 ^ w)
    {s : State} (hinput : s.arrs 0 = x.words) (hsize : s.regs 4 = x.n)
    (hsource : s.regs 187 = a.val) (hcount : s.regs 105 = L.length)
    (hstart : s.regs 261 = x.cuffOffset + 2)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n) :
    ∃ s' t, Exec w gm06ComponentQueryProg s s' t ∧
      t ≤ 26 * (x.n * x.n) + 23 * x.n + 22 * L.length + 33 ∧
      s'.regs 112 = (if x.isInteriorComponent a then 1 else 0) ∧
      s'.arrs 33 = gm06VertexReachData x a ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 112 →
        s'.regs q = s.regs q) := by
  have hend : x.cuffOffset + 2 + L.length < 2 ^ w := by
    have hh := x.divisionOffset_lt_length.trans hinputSize
    rw [GM06DrawingData.divisionOffset, x.cuffWords_singleton_length hL] at hh
    omega
  have hstream := cuff_labels_stream x hL hinput
  obtain ⟨s₁, t₁, hex₁, ht₁, hmarks₁, ha₁, hg₁⟩ :=
    gm06VertexBfsProg_exec x a hw hn hsquare hsize hsource hlists hlen
  obtain ⟨s₂, t₂, hex₂, ht₂, hflag₂, _, ha₂, hg₂⟩ :=
    gm06ComponentCuffTestProg_exec x a L x.divisionWords hw hn hend hmarks₁
      (hstream.of_arr_eq (ha₁ 0 (by decide) (by decide)))
      ((hg₁ 261 (by decide)).trans hstart) ((hg₁ 105 (by decide)).trans hcount)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, ?_, (ha₂ 33).trans hmarks₁, ?_, ?_⟩
  · simpa only [interior_single_cuff x hL a] using hflag₂
  · intro A h33 h34
    exact (ha₂ A).trans (ha₁ A h33 h34)
  · intro q hq h103 h108 h109 h112
    exact (hg₂ q h103 h108 h109 h112).trans (hg₁ q hq)

end GraphMinor.Compute
