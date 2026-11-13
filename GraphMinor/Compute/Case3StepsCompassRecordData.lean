module

public import GraphMinor.Compute.Case3StepsExpandedEdgesProg
public import GraphMinor.Compute.Case3StepsCountedPrefixProg
public import GraphMinor.Compute.Case3StepsEncodingWords
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Preparing the compass lists in the final block

The compact compass encoding and its original inverse labels survive both
member scans. Copy the counted inverse list and expand each positive pair
into all its original directed copies. These are the vertex and edge lists
of the final case (iii) block.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Transport

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Restore the compass lists into vertex array 60 and expanded-edge array 50. -/
def case3CompassRecordDataProg : Cmd :=
  .seq (copyArrLoopProg 3 38 125 126)
    (.seq (case3CountedPrefixProg 32 47 14)
      (.seq (copyArrLoopProg 47 60 125 126)
        (.seq (sumEdgeMultProg 38 124)
          (.seq (.assign 111 (.reg 126)) case3ExpandedEdgesProg))))

/-- The complete compass lists are prepared in linear vertex and edge work.
The retained member buffer and all low scan counters survive. -/
theorem case3CompassRecordDataProg_exec {w n N : ℕ} (D : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (unused : List ℕ)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (he : 3 * D.numEdges + 1 < 2 ^ w)
    {s : State} (hG : s.arrs 3 = D.enc)
    (hlabels : s.arrs 32 = List.ofFn (fun u : Fin n => (orig u).1) ++ unused)
    (hrn : s.regs 14 = n) :
    ∃ s' t, Exec w case3CompassRecordDataProg s s' t ∧
      t ≤ 200 * (n + D.numActivePairs + D.numEdges + 1) ∧
      s'.arrs 60 = List.ofFn (fun u : Fin n => (orig u).1) ∧
      s'.arrs 50 = encEdgeTriples (D.multiEdgeTriples.map (origEdgeEmb orig hinj)) ∧
      s'.regs 111 = D.numEdges ∧
      (∀ a, a ≠ 38 → a ≠ 47 → a ≠ 50 → a ≠ 60 → s'.arrs a = s.arrs a) ∧
      (∀ r < 103, s'.regs r = s.regs r) := by
  have h1 : 1 < 2 ^ w := by omega
  have hDw : ∀ z ∈ D.enc, z < 2 ^ w :=
    case3Multigraph_enc_words_lt D hn (by omega) (by omega)
  have hDl : D.enc.length < 2 ^ w := by
    rw [D.length_enc]
    exact hA
  let labels := List.ofFn (fun u : Fin n => (orig u).1)
  have hll : labels.length = n := List.length_ofFn
  have hlw : ∀ z ∈ labels, z < 2 ^ w := by
    intro z hz
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hz
    exact (orig u).2.trans hN
  obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, harr₁, hreg₁⟩ := copyArrLoopProg_exec
    3 38 125 126 (by decide) (by decide) h1 s (by rw [hG]; exact hDl)
      (by rw [hG]; exact hDw)
  have h38 : s₁.arrs 38 = D.enc := hbuf₁.trans hG
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, harr₂, hreg₂⟩ := case3CountedPrefixProg_exec
    32 47 14 (by decide) (by decide) labels unused h1 (by rw [hll]; exact hn) hlw
    ((harr₁ 32 (by decide)).trans hlabels)
    (by rw [hreg₁ 14 (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega), hrn, hll])
  obtain ⟨s₃, t₃, hex₃, ht₃, hbuf₃, harr₃, hreg₃⟩ := copyArrLoopProg_exec
    47 60 125 126 (by decide) (by decide) h1 s₂ (by rw [hbuf₂, hll]; exact hn)
    (by rw [hbuf₂]; exact hlw)
  have h38₃ : s₃.arrs 38 = D.enc :=
    (harr₃ 38 (by decide)).trans ((harr₂ 38 (by decide)).trans h38)
  obtain ⟨s₄, t₄, hex₄, ht₄, _, _, hm₄, harr₄, hreg₄⟩ :=
    sumEdgeMultProg_exec D 38 124 hw hn hA (by omega) h38₃
  change s₄.regs 126 = D.numEdges at hm₄
  let s₅ := s₄.setReg 111 D.numEdges
  have hex₅ : Exec w (.assign 111 (.reg 126)) s₄ s₅ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hm₄,
      show D.numEdges < 2 ^ w by omega, ↓reduceIte])
  obtain ⟨s₆, t₆, hex₆, ht₆, hbuf₆, harr₆, hreg₆⟩ :=
    case3ExpandedEdgesProg_exec D orig hinj hw hn hN hA he
      (s := s₅) ((harr₄ 38).trans h38₃)
      ((harr₄ 47).trans ((harr₃ 47 (by decide)).trans hbuf₂)) (State.setReg_regs_self ..)
  have hex : Exec w case3CompassRecordDataProg s s₆
      (t₁ + (t₂ + (t₃ + (t₄ + (2 + t₆))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))
  have h111 : s₆.regs 111 = D.numEdges := by
    rw [hex₆.regs_eq_of_not_mem_writtenRegs (r := 111) (by
      simp [case3ExpandedEdgesProg, forUp, case3ExpandPairProg, case3ReadMappedPairProg,
        readTripleEndpoints, case3ExpandCopiesProg, case3WriteCopyProg, Cmd.writtenRegs])]
    exact State.setReg_regs_self ..
  refine ⟨s₆, _, hex, ?_, ?_, hbuf₆, h111, ?_, ?_⟩
  · rw [hG, D.length_enc] at ht₁
    rw [hbuf₂, hll] at ht₃
    rw [hll] at ht₂
    omega
  · exact (harr₆ 60 (by decide)).trans ((harr₄ 60).trans (hbuf₃.trans hbuf₂))
  · intro a h38' h47 h50 h60
    rw [harr₆ a h50, State.setReg_arrs, harr₄ a, harr₃ a h60,
      harr₂ a h47, harr₁ a h38']
  · intro r hr
    rw [hreg₆ r hr, State.setReg_regs_ne _ _ (by romega), hreg₄ r (by romega),
      hreg₃ r (by romega) (by romega), hreg₂ r (Or.inl (by romega)),
      hreg₁ r (by romega) (by romega)]

end GraphMinor.Compute
