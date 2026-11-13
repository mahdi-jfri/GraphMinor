module

public import GraphMinor.Compute.Case3StepsCompactProg

/-!
# Writing the simple compact compass graph

Step (5) of XIII (9.9), page 104, applies (8.6) to the simple graph underlying
the compass. After compact numbering we use the existing multigraph-to-simple
graph conversion. The rank array stays available for the corner list.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The compact graph and its simple encoding. The encoding for (8.6) starts
in `a_base + 8`, while the rank array remains in `a_base + 2`. -/
def case3SimpleCompassProg (a_G a_VK a_base r_base : ℕ) : Cmd :=
  .seq (case3CompactCompassProg a_G a_VK a_base r_base)
    (toSimpleGraphEdgeListProg (a_base + 3) (a_base + 4) (a_base + 8) (r_base + 2))

/-- Execution and linear time bound for the simple compact graph encoding. -/
theorem case3SimpleCompassProg_exec {w n : ℕ} (G : MultiDigraph n)
    (S : Finset (Fin n)) (a_G a_VK a_base r_base : ℕ)
    (haG : a_G < a_base) (haVK : a_VK < a_base)
    (hw3 : 3 < 2 ^ w) (hn : n < 2 ^ w)
    (hm3 : 2 + 3 * G.numActivePairs < 2 ^ w) (he : G.numEdges < 2 ^ w)
    {s : State} (hG : s.arrs a_G = G.enc) (hVK : s.arrs a_VK = bitSetList S) :
    ∃ s' t,
      Exec w (case3SimpleCompassProg a_G a_VK a_base r_base) s s' t ∧
      t ≤ 256 * G.numActivePairs + 34 * n + 209 ∧
      s'.arrs (a_base + 8) = encGraph (G.deleteVerticesCompact Sᶜ).toSimpleGraph ∧
      s'.arrs (a_base + 3) = (G.deleteVerticesCompact Sᶜ).enc ∧
      s'.arrs (a_base + 2) = List.ofFn (fun v : Fin n => compactRank Sᶜ v.1) ∧
      s'.regs (r_base + 2) = S.card ∧
      s'.regs (r_base + 3) = (edgeListOf (G.deleteVerticesCompact Sᶜ).toSimpleGraph).length ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hdst₁, hrank₁, harr₁, hreg₁⟩ :=
    case3CompactCompassProg_exec G S a_G a_VK a_base r_base haG haVK hw3 hn hm3 he hG hVK
  have hM : (G.deleteVerticesCompact Sᶜ).numActivePairs ≤ G.numActivePairs := by
    rw [G.numActivePairs_deleteVerticesCompact]
    exact G.numActivePairs_deleteVertices_le _
  have hN : Sᶜᶜ.card ≤ n := (Finset.card_le_univ _).trans (Finset.card_fin n).le
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, hrn₂, hrm₂, harr₂, hreg₂⟩ :=
    toSimpleGraphEdgeListProg_exec (G.deleteVerticesCompact Sᶜ) [] (a_base + 3) (a_base + 4)
      (a_base + 8) (r_base + 2) (by romega) (by romega) hw3 (hN.trans_lt hn)
      (by romega) (by simpa only [List.append_nil] using hdst₁)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by romega, hdst₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [harr₂ (a_base + 3) (by romega) (by romega)]
    exact hdst₁
  · rw [harr₂ (a_base + 2) (by romega) (by romega)]
    exact hrank₁
  · simpa only [compl_compl] using hrn₂
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using hrm₂
  · intro a ha
    rw [harr₂ a (by romega) (by romega)]
    exact harr₁ a ha
  · intro r hr
    rw [hreg₂ r (by romega)]
    exact hreg₁ r hr

end GraphMinor.Compute
