module

public import GraphMinor.Compute.GM06Alg511FlowGraph
public import GraphMinor.Compute.GM06DartMate
import Mathlib.Tactic

/-!
# Ordinary edge keys for selecting a returned path's darts

To choose an actual edge for each consecutive pair of returned vertex
labels in VI (5.11), page 134, encode its two endpoint labels as
`start * vertexCount + end`. Keep one key for each directed edge end.
Parallel edges retain separate positions. The keys are computed from
supplied endpoint labels only and contain no path or decision result.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Endpoint-pair keys, in dart order, of the supplied drawing. -/
def gm06Alg511DartKeys (x : GM06Alg511Input) : List ℕ :=
  (List.range x.endpoints.length).map fun d =>
    x.endpoints.getD d 0 * x.vertexCount + x.endpoints.getD (gm06DartMate d) 0

/-- There is exactly one key per supplied dart position. -/
theorem gm06Alg511DartKeys_length (x : GM06Alg511Input) :
    (gm06Alg511DartKeys x).length = x.endpoints.length := by simp [gm06Alg511DartKeys]

/-- The endpoint pair of an edge is read at its two consecutive positions. -/
theorem gm06Alg511EndpointWords_getD (pairs : List (ℕ × ℕ)) (i : ℕ) (hi : i < pairs.length) :
    (gm06EndpointWords pairs).getD (2 * i) 0 = pairs[i].1 ∧
    (gm06EndpointWords pairs).getD (2 * i + 1) 0 = pairs[i].2 := by
  induction pairs generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => exact ⟨rfl, rfl⟩
    | succ i =>
      have hi' : i < ps.length := by simpa using hi
      simpa [gm06EndpointWords, Nat.mul_succ, Nat.add_assoc] using ih i hi'

/-- Pair keys are below the square of the vertex bound. -/
theorem gm06Alg511PairKey_lt {n a b : ℕ} (ha : a < n) (hb : b < n) : a * n + b < n * n := by
  calc
    a * n + b < a * n + n := Nat.add_lt_add_left hb _
    _ = (a + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right n (by omega)

/-- A pair key uniquely determines its two bounded endpoint labels. -/
theorem gm06Alg511PairKey_injective {n a b c d : ℕ} (hb : b < n) (hd : d < n)
    (he : a * n + b = c * n + d) : a = c ∧ b = d := by
  have hn : 0 < n := by omega
  have hqa : (a * n + b) / n = a := by
    rw [Nat.mul_comm a n, Nat.mul_add_div hn, Nat.div_eq_of_lt hb, Nat.add_zero]
  have hqc : (c * n + d) / n = c := by
    rw [Nat.mul_comm c n, Nat.mul_add_div hn, Nat.div_eq_of_lt hd, Nat.add_zero]
  have ha : a = c := by
    have h := congrArg (fun key => key / n) he
    rw [hqa, hqc] at h
    exact h
  refine ⟨ha, ?_⟩
  rw [ha] at he
  exact Nat.add_left_cancel he

/-- Every adjacency used by the initial flow search has an ordinary
dart key in the supplied finite edge table. -/
theorem gm06Alg511DartKeys_mem_of_adj (x : GM06Alg511Input)
    {α : Type*} {β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    (a b : Fin x.vertexCount) (hadj : x.flowGraph.Adj a b) :
    a.val * x.vertexCount + b.val ∈ gm06Alg511DartKeys x := by
  let pairs := rep.pairs.map (fun p => (p.1.val, p.2.val))
  have hend : x.endpoints = gm06EndpointWords pairs := rep.endpoints
  have hlen : x.endpoints.length = 2 * pairs.length := by rw [hend, gm06EndpointWords_length]
  have hread : gm06Alg511ReadPairs x.endpoints = pairs := by
    rw [hend, gm06Alg511ReadPairs_endpointWords]
  change a ≠ b ∧ ((a.val, b.val) ∈ gm06Alg511ReadPairs x.endpoints ∨
    (b.val, a.val) ∈ gm06Alg511ReadPairs x.endpoints) at hadj
  rw [hread] at hadj
  rcases hadj.2 with h | h
  · obtain ⟨i, hi, hp⟩ := List.mem_iff_getElem.mp h
    obtain ⟨h0, h1⟩ := gm06Alg511EndpointWords_getD pairs i hi
    have hm : gm06DartMate (2 * i) = 2 * i + 1 := by simp [gm06DartMate]
    apply List.mem_map.mpr
    refine ⟨2 * i, List.mem_range.mpr (by omega), ?_⟩
    rw [hm, hend, h0, h1, hp]
  · obtain ⟨i, hi, hp⟩ := List.mem_iff_getElem.mp h
    obtain ⟨h0, h1⟩ := gm06Alg511EndpointWords_getD pairs i hi
    have hm : gm06DartMate (2 * i + 1) = 2 * i := by unfold gm06DartMate; split <;> omega
    apply List.mem_map.mpr
    refine ⟨2 * i + 1, List.mem_range.mpr (by omega), ?_⟩
    rw [hm, hend, h0, h1, hp]

/-- Reading any valid endpoint position gives a bounded vertex label. -/
theorem gm06Alg511Endpoint_getD_lt (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    (d : ℕ) (hd : d < x.endpoints.length) :
    x.endpoints.getD d 0 < x.vertexCount := by
  apply rep.endpoint_lt
  change x.endpoints.getD d 0 ∈ x.endpoints
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd,
    Option.getD_some] using List.getElem_mem hd

/-- Every generated key is smaller than the square of the vertex count. -/
theorem gm06Alg511DartKeys_lt (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G) :
    ∀ key ∈ gm06Alg511DartKeys x, key < x.vertexCount * x.vertexCount := by
  intro key hkey
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hkey
  have hd' := List.mem_range.mp hd
  have hlen : x.endpoints.length = 2 * rep.pairs.length := by
    have hend : x.endpoints = gm06EndpointWords
        (rep.pairs.map fun p => (p.1.val, p.2.val)) := rep.endpoints
    rw [hend, gm06EndpointWords_length, List.length_map]
  have hm : gm06DartMate d < x.endpoints.length := by
    rw [hlen] at hd' ⊢
    exact gm06DartMate_lt hd'
  exact gm06Alg511PairKey_lt (gm06Alg511Endpoint_getD_lt x rep d hd')
    (gm06Alg511Endpoint_getD_lt x rep _ hm)

end GraphMinor.Compute
