module

public import GraphMinor.Compute.Case3StepsReadMappedPairProg
public import GraphMinor.Compute.Case3StepsExpandCopiesProg
public import GraphMinor.Compute.Case3StepsExpandedPairs
public import GraphMinor.Compute.Algorithm99TransportOrig

/-!
# Advancing the expanded member record by one pair

Reading and renaming one compact positive pair is followed by expanding its
whole parallel class. The edge counter advances by the full multiplicity,
and the exact completed record prefix advances to the next positive pair.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Read a compact member pair, map its endpoints, and expand all copies. -/
def case3ExpandPairProg : Cmd := .seq case3ReadMappedPairProg case3ExpandCopiesProg

/-- A pair contributes exactly its renamed directed copies to the record
and costs at most a constant plus twenty-six times its multiplicity. -/
theorem case3ExpandPairProg_exec {w n N : ℕ} (G : MultiDigraph n) (orig : Fin n → Fin N)
    (hinj : Function.Injective orig) (j : Fin G.numActivePairs)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w) (he : 3 * G.numEdges + 1 < 2 ^ w)
    {s : State} (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hrj : s.regs 103 = j.1)
    (hrq : s.regs 109 = MultiDigraph.sumEdgeMult G (G.activePairsList.take j.1))
    (hdst : s.arrs 50 =
      case3ExpandedPairs G (origVertexEmb orig hinj) (G.activePairsList.take j.1) ++
        List.replicate (3 * (G.numEdges - MultiDigraph.sumEdgeMult G (G.activePairsList.take j.1))) 0) :
    ∃ s' t, Exec w case3ExpandPairProg s s' t ∧
      t ≤ 26 * G.edgeMult (G.activePairsList[j.1]).1 (G.activePairsList[j.1]).2 + 34 ∧
      s'.arrs 50 =
        case3ExpandedPairs G (origVertexEmb orig hinj) (G.activePairsList.take (j.1 + 1)) ++
          List.replicate (3 * (G.numEdges - MultiDigraph.sumEdgeMult G (G.activePairsList.take (j.1 + 1)))) 0 ∧
      s'.regs 109 = MultiDigraph.sumEdgeMult G (G.activePairsList.take (j.1 + 1)) ∧
      (∀ a, a ≠ 50 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 104 → r ≠ 106 → r ≠ 107 → r ≠ 108 → r ≠ 109 → r ≠ 110 → r ≠ 116 →
        s'.regs r = s.regs r) := by
  let p := G.activePairsList[j.1]
  let q := MultiDigraph.sumEdgeMult G (G.activePairsList.take j.1)
  let m := G.edgeMult p.1 p.2
  let pre := case3ExpandedPairs G (origVertexEmb orig hinj) (G.activePairsList.take j.1)
  let suf := List.replicate (3 * (G.numEdges - (q + m))) 0
  have hpre : pre.length = 3 * q := case3ExpandedPairs_length G _ _
  have hnext : MultiDigraph.sumEdgeMult G (G.activePairsList.take (j.1 + 1)) = q + m :=
    case3PairPrefix_edges_succ G j.1 j.2
  have hqm : q + m ≤ G.numEdges := by
    rw [← hnext]
    exact case3PairPrefix_edges_le G _
  have hrep : List.replicate (3 * (G.numEdges - q)) 0 = List.replicate (3 * m) 0 ++ suf := by
    rw [show 3 * (G.numEdges - q) = 3 * m + 3 * (G.numEdges - (q + m)) by omega,
      List.replicate_add]
  obtain ⟨s₁, t₁, hex₁, ht₁, hru, hrv, hrm, harr₁, hreg₁⟩ :=
    case3ReadMappedPairProg_exec G orig j hw hn hN (by omega) hA hG hlabels hrj
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, hrq₂, harr₂, hreg₂⟩ :=
    case3ExpandCopiesProg_exec pre suf (orig p.1).1 (orig p.2).1 q m hpre hw
      (by rw [hpre]; omega) ((orig p.1).2.trans hN) ((orig p.2).2.trans hN)
      (s := s₁) (by
        rw [harr₁ 50]
        rw [show s.arrs 50 = pre ++ List.replicate (3 * (G.numEdges - q)) 0 from hdst, hrep, List.append_assoc])
      hru hrv hrm ((hreg₁ 109 (by decide) (by decide) (by decide) (by decide)).trans hrq)
  have ht : t₁ + t₂ ≤ 26 * G.edgeMult (G.activePairsList[j.1]).1 (G.activePairsList[j.1]).2 + 34 := by
    dsimp only [m, p] at ht₂
    omega
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ht, ?_, hrq₂.trans hnext.symm, ?_, ?_⟩
  · rw [hdst₂, case3ExpandedPairs_take_succ G _ j.1 j.2, hnext]
    simp only [origVertexEmb_apply_val, List.append_assoc]
    rfl
  · intro a ha
    exact (harr₂ a ha).trans (harr₁ a)
  · intro r h104 h106 h107 h108 h109 h110 h116
    rw [hreg₂ r h109 h110 h116, hreg₁ r h104 h106 h107 h108]

end GraphMinor.Compute
