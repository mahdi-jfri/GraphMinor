module

public import GraphMinor.Compute.Parse
public import GraphMinor.Compute.BitSet
public import GraphMinor.Compute.Algorithm83

/-!
# Filtering the edges of recursive sides

A recursive side keeps edges whose two ends survive on that side. For
the second side, edges already assigned to the first side are omitted.
The existing edge-filter loop tests exactly this endpoint condition.
Here its canonical output is identified with the corresponding simple
graph and its linear running-time bound is retained.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Keep edges inside `B`, omitting edges with both endpoints in `A`.
This is the edge rule for a canonical recursive side of II (3.2). -/
def gm02FilteredSide {n : ℕ} (F : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    SimpleGraph (Fin n) where
  Adj u v := F.Adj u v ∧ keepCoreEdge A B (u, v) = true
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    have hk := h.2
    simp only [keepCoreEdge, decide_eq_true_eq] at hk ⊢
    exact ⟨hk.2.1, hk.1, fun hh => hk.2.2 ⟨hh.2, hh.1⟩⟩⟩
  loopless := ⟨fun u h => F.loopless.irrefl u h.1⟩

/-- The existing filter keeps the canonical edge order. -/
theorem gm02FilteredSide_edgeList {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (A B : Finset (Fin n)) :
    edgeListOf (gm02FilteredSide F A B) = (edgeListOf F).filter (keepCoreEdge A B) := by
  simp only [edgeListOf, List.filter_filter]
  apply List.filter_congr
  intro p _
  by_cases ho : p.1.val < p.2.val <;> by_cases hf : F.Adj p.1 p.2 <;>
    cases hk : keepCoreEdge A B p <;> simp [gm02FilteredSide, ho, hf, hk]

/-- Filtering a recursive side returns precisely its canonical edge words,
with spare allocation kept separate from the meaningful prefix. -/
theorem gm02FilterSide_exec {n w : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (A B : Finset (Fin n)) (hw : 3 < 2 ^ w) (hn : n < 2 ^ w)
    (hlen : 8 + 2 * (edgeListOf F).length < 2 ^ w) (s : State)
    (hin : s.arrs 0 = encGraph F) (hB : IsBitSet B 14 s) (hA : IsBitSet A 13 s)
    (hrm : s.regs 1 = (edgeListOf F).length) :
    ∃ s' t, Exec w filterEdgesProg s s' t ∧
      t ≤ 64 * (edgeListOf F).length + 22 ∧
      s'.regs 22 = (edgeListOf (gm02FilteredSide F A B)).length ∧
      s'.arrs 17 = ([0, 0] ++ flatEdges (edgeListOf (gm02FilteredSide F A B))) ++
        List.replicate (6 + 2 * ((edgeListOf F).length -
          (edgeListOf (gm02FilteredSide F A B)).length)) 0 ∧
      (∀ a, a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 →
        r ≠ 22 → s'.regs r = s.regs r) := by
  have hab : ∀ u : Fin n, u ∈ A ∩ B ↔ u ∈ B ∧ u ∈ A := by
    intro u
    simp only [Finset.mem_inter]
    exact and_comm
  simpa only [gm02FilteredSide_edgeList] using
    (filterEdgesProg_exec A B A hab (edgeListOf F) hw hn hlen hin hB hA hrm)

end GraphMinor.Compute
