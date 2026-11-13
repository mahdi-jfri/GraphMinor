module

public import GraphMinor.Compute.Case3StepsCompassRecordData
public import GraphMinor.Compute.Case3StepsMemberSectionProg
public import GraphMinor.Compute.Case3StepsBlockCornersProg
public import GraphMinor.Compute.Case3StepsBlockAssemblyProg

/-!
# Writing the block after all member scans

Restore the compass vertex and edge lists, finish the retained member
section, read the original wall corners, and assemble all sections. This
is the final encoding work of step (7) of XIII (9.9), p. 105. The graph
semantics of the records are separate from this RAM copying proof.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Transport

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Finish the block from the compact compass and the retained member buffer. -/
def case3FinishBlockProg {h : ℕ} (h2 : 2 ≤ h) : Cmd :=
  .seq case3CompassRecordDataProg
    (.seq case3MemberSectionProg
      (.seq (case3BlockCornersProg h2) case3BlockAssemblyProg))

/-- Every section is computed and the exact final block is written, with
all low counters and all arrays outside the encoding workspace retained. -/
theorem case3FinishBlockProg_exec {w h n N : ℕ} (D : MultiDigraph n)
    (D₀ : MultiDigraph N) (W : WallOfHeight h D₀) (h2 : 2 ≤ h)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig)
    (unusedLabels unusedRecords : List ℕ) (members : List Case3MemberRecord)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (he : 3 * D.numEdges + 1 < 2 ^ w)
    (hidx : 3 + elemWallNumVerts h < 2 ^ w)
    (hlen : (encCase3Block W (List.ofFn (fun u : Fin n => (orig u).1))
      (D.multiEdgeTriples.map (origEdgeEmb orig hinj))
      (List.ofFn (fun i : Fin 4 => (W.cornerVert h2 i).1)) members).length < 2 ^ w)
    (hwords : ∀ x ∈ encCase3Block W (List.ofFn (fun u : Fin n => (orig u).1))
      (D.multiEdgeTriples.map (origEdgeEmb orig hinj))
      (List.ofFn (fun i : Fin 4 => (W.cornerVert h2 i).1)) members, x < 2 ^ w)
    {s : State} (hG : s.arrs 3 = D.enc)
    (hlabels : s.arrs 32 = List.ofFn (fun u : Fin n => (orig u).1) ++ unusedLabels)
    (hrn : s.regs 14 = n) (hwall : s.arrs 59 = W.encList)
    (hbuf : s.arrs 57 = members.flatMap Case3MemberRecord.enc ++ unusedRecords)
    (hrlen : s.regs 1 = (members.flatMap Case3MemberRecord.enc).length)
    (hrcount : s.regs 2 = members.length) :
    ∃ s' t, Exec w (case3FinishBlockProg h2) s s' t ∧
      t ≤ 2000 * (n + D.numActivePairs + D.numEdges +
        (encCase3Block W (List.ofFn (fun u : Fin n => (orig u).1))
          (D.multiEdgeTriples.map (origEdgeEmb orig hinj))
          (List.ofFn (fun i : Fin 4 => (W.cornerVert h2 i).1)) members).length + 1) ∧
      s'.arrs 51 = encCase3Block W (List.ofFn (fun u : Fin n => (orig u).1))
        (D.multiEdgeTriples.map (origEdgeEmb orig hinj))
        (List.ofFn (fun i : Fin 4 => (W.cornerVert h2 i).1)) members ∧
      (∀ a, a ∉ [38, 47, 50, 51, 52, 53, 58, 60] → s'.arrs a = s.arrs a) ∧
      (∀ r < 101, s'.regs r = s.regs r) := by
  let Kv := List.ofFn (fun u : Fin n => (orig u).1)
  let Ke := D.multiEdgeTriples.map (origEdgeEmb orig hinj)
  let corners := List.ofFn (fun i : Fin 4 => (W.cornerVert h2 i).1)
  let records := members.flatMap Case3MemberRecord.enc
  have hrecwords : ∀ x ∈ records, x < 2 ^ w := by
    intro x hx
    exact hwords x (by
      simp only [encCase3Block, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr hx))
  have hcountw : members.length < 2 ^ w := hwords _ (by simp [encCase3Block])
  have hreclen : 1 + records.length < 2 ^ w := by
    have hl : 1 + records.length ≤ (encCase3Block W Kv Ke corners members).length := by
      simp only [encCase3Block, List.length_append, List.length_cons, records]
      omega
    exact hl.trans_lt hlen
  obtain ⟨s₁, t₁, hex₁, ht₁, hv₁, he₁, hm₁, harr₁, hreg₁⟩ :=
    case3CompassRecordDataProg_exec D orig hinj unusedLabels (by omega) hn hN hA he hG hlabels hrn
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, harr₂, hreg₂⟩ :=
    case3MemberSectionProg_exec records unusedRecords members.length (by omega) hreclen hcountw hrecwords
      ((harr₁ 57 (by decide) (by decide) (by decide) (by decide)).trans hbuf)
      ((hreg₁ 1 (by dsimp only [Reg]; omega)).trans hrlen)
      ((hreg₁ 2 (by dsimp only [Reg]; omega)).trans hrcount)
  obtain ⟨s₃, hex₃, hc₃, harr₃, hreg₃⟩ :=
    case3BlockCornersProg_exec W h2 hw hN hidx
      ((harr₂ 59 (by decide) (by decide)).trans
        ((harr₁ 59 (by decide) (by decide) (by decide) (by decide)).trans hwall))
  obtain ⟨s₄, t₄, hex₄, ht₄, hbuf₄, harr₄, hreg₄⟩ :=
    case3BlockAssemblyProg_exec W Kv Ke corners members (by omega) hlen hwords
      ((harr₃ 59 (by decide)).trans ((harr₂ 59 (by decide) (by decide)).trans
        ((harr₁ 59 (by decide) (by decide) (by decide) (by decide)).trans hwall)))
      ((harr₃ 60 (by decide)).trans ((harr₂ 60 (by decide) (by decide)).trans hv₁))
      ((harr₃ 50 (by decide)).trans ((harr₂ 50 (by decide) (by decide)).trans he₁)) hc₃
      ((harr₃ 51 (by decide)).trans hbuf₂)
      (by rw [hreg₃ 111, hreg₂ 111 (by dsimp only [Reg]; omega)];
          simpa only [Ke, List.length_map, D.length_multiEdgeTriples] using hm₁)
  have hex : Exec w (case3FinishBlockProg h2) s s₄ (t₁ + (t₂ + (21 + t₄))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, _, hex, ?_, hbuf₄, ?_, ?_⟩
  · have hrl : records.length ≤ (encCase3Block W Kv Ke corners members).length := by
      simp only [encCase3Block, List.length_append, List.length_cons, records]
      omega
    dsimp only [Kv, Ke, corners] at ht₄ hrl
    omega
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    rcases ha with ⟨h38, h47, h50, h51, h52, h53, h58, h60⟩
    rw [harr₄ a h51 h52 h53, harr₃ a h58, harr₂ a h51 h52,
      harr₁ a h38 h47 h50 h60]
  · intro r hr
    rw [hreg₄ r hr, hreg₃ r, hreg₂ r (by romega), hreg₁ r (by romega)]

end GraphMinor.Compute
