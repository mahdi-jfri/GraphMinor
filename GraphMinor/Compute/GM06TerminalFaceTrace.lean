module

public import GraphMinor.Compute.GM06TerminalFace
public import GraphMinor.Compute.GM06TerminalInput
public import GraphMinor.Compute.GM06TerminalTrace
public import GraphMinor.Compute.GM06CutNeighbourMarks

/-!
# The complete first-contact trace from a selected face

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) rotates the
selected face after its reverse inner-cuff dart, then follows heads
until its first boundary contact. The starting copy is the head of
that cuff dart. The program computes heads and target bits, rotates
the actual face row and runs the verified prefix scan. Its result
still contains closed subwalks, which the following stack pass erases.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The exact traced dart prefix and first-contact flag. -/
def gm06TerminalFaceTrace (n : ℕ) (origins face left upper : List ℕ) (cuff : ℕ) : List ℕ × Bool :=
  gm06TerminalTrace (gm06DartHeads origins)
    (gm06IncidenceBits n (gm06TerminalTargetLabels (gm06CutNeighbourHead origins cuff) left upper))
    (gm06TerminalFaceWalk face cuff)

/-- Compute the head/target tables and rotate the face before tracing. -/
def gm06TerminalFaceTraceProg : Cmd :=
  .seq gm06DartHeadsProg
    (.seq (.assign 606 (.read 601 (.reg 667)))
      (.seq gm06TerminalTargetsProg
        (.seq gm06TerminalFaceProg
          (.seq (gm13TabulateProg 650 (.len 614) (.read 614 (.reg 650)) 600)
            gm06TerminalTraceProg))))

/-- Full register frame for first-contact tracing from the input face. -/
def gm06TerminalFaceTraceRegs : List ℕ := [650, 606, 651, 652, 655, 610, 611, 612, 674, 600, 601, 602, 605]

/-- The trace uses only scratch tables and its returned prefix array. -/
def gm06TerminalFaceTraceArrs : List ℕ := [601, 602, 604, 605, 614, 600, 603]

/-- The whole RAM trace computes its exact pure prefix from finite
origins, face and boundary rows, with a linear input-size bound. -/
theorem gm06TerminalFaceTraceProg_exec {w n m : ℕ} (origins face left upper : List ℕ) (cuff : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (horg : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hfaceFit : face.length + 2 < 2 ^ w) (hboundaryFit : left.length + upper.length + 2 < 2 ^ w)
    (hnd : face.Nodup) (hc : cuff ∈ face) (hface : ∀ d ∈ face, d < 2 * m)
    (hleft : ∀ v ∈ left, v < n) (hupper : ∀ v ∈ upper, v < n)
    (h626 : s.arrs 626 = origins) (h600 : s.arrs 600 = face)
    (h609 : s.arrs 609 = left) (h608 : s.arrs 608 = upper)
    (h667 : s.regs 667 = cuff) (h648 : s.regs 648 = n) :
    ∃ sf t, Exec w gm06TerminalFaceTraceProg s sf t ∧
      t ≤ 130 + n + 30 * (2 * m) + 120 * face.length + 60 * (left.length + upper.length) ∧
      Keeps gm06TerminalFaceTraceRegs gm06TerminalFaceTraceArrs s sf ∧
      sf.arrs 603 = (gm06TerminalFaceTrace n origins face left upper cuff).1 ∧
      sf.regs 602 = (gm06TerminalFaceTrace n origins face left upper cuff).2.toNat ∧
      sf.arrs 601 = gm06DartHeads origins ∧
      sf.regs 606 = gm06CutNeighbourHead origins cuff := by
  have hw1 : 1 < 2 ^ w := by omega
  have hcBound : cuff < 2 * m := hface cuff hc
  have hcOrg : cuff < origins.length := horg ▸ hcBound
  let source := gm06CutNeighbourHead origins cuff
  let labels := gm06TerminalTargetLabels source left upper
  let walk := gm06TerminalFaceWalk face cuff
  have hsource : source < n := by
    have hi : gm06DartMate cuff < origins.length := horg ▸ gm06DartMate_lt hcBound
    simpa only [source, gm06CutNeighbourHead, List.getElem?_eq_getElem hi, Option.getD_some] using
      hvalues _ (List.getElem_mem hi)
  have hwalkLen : walk.length + 1 = face.length := gm06TerminalFaceWalk_length face cuff hc
  have hwalkBound : ∀ d ∈ walk, d < 2 * m := fun d hd =>
    hface d (gm06TerminalFaceWalk_mem hc hd)
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06DartHeadsProg_exec origins s hw hn hm horg hvalues h626
  let s₂ := s₁.setReg 606 source
  have heSource : (Expr.read 601 (.reg 667)).eval w s₁ = some source := by
    have hi : cuff < (s₁.arrs 601).length := by simpa only [hd₁, gm06DartHeads_length, horg] using hcBound
    have hg : (s₁.arrs 601)[cuff]'hi = source := by
      have he := gm06DartHeads_get origins hcOrg
      rw [List.getElem?_eq_getElem (by simpa only [gm06DartHeads_length] using hcOrg)] at he
      simpa only [hd₁, Option.getD_some, source, gm06CutNeighbourHead] using he
    have he := GraphMinor.Compute.Crossing.eval_read (a := 601)
      (GraphMinor.Compute.Crossing.eval_reg ((hk₁.1 667 (by decide)).trans h667) (hcBound.trans hm)) hi
      (by rw [hg]; exact hsource.trans hn)
    simpa only [hg] using he
  have he₂ : Exec w (.assign 606 (.read 601 (.reg 667))) s₁ s₂ 3 := .assign heSource
  have hk₁₂ : Keeps gm06TerminalFaceTraceRegs gm06TerminalFaceTraceArrs s s₂ :=
    (hk₁.mono (by simp [gm06TerminalFaceTraceRegs]) (by simp [gm06TerminalFaceTraceArrs])).setReg
      (by simp [gm06TerminalFaceTraceRegs]) _
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm06TerminalTargetsProg_exec left upper s₂ hw1 hn hsource hboundaryFit
    hleft hupper ((hk₁₂.2 609 (by decide)).trans h609) ((hk₁₂.2 608 (by decide)).trans h608)
    (by simp [s₂]) ((hk₁₂.1 648 (by decide)).trans h648)
  have hk₁₃ : Keeps gm06TerminalFaceTraceRegs gm06TerminalFaceTraceArrs s s₃ :=
    hk₁₂.trans hk₃ (by simp [gm06TerminalFaceTraceRegs]) (by simp [gm06TerminalFaceTraceArrs])
  have h600₃ : s₃.arrs 600 = face := (hk₃.2 600 (by decide)).trans ((hk₁.2 600 (by decide)).trans h600)
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hd₄⟩ := gm06TerminalFaceProg_exec face cuff s₃ hw1 hfaceFit hnd hc
    (fun d hd => (hface d hd).trans hm) h600₃
    ((hk₁₃.1 667 (by decide)).trans h667)
  have hk₁₄ : Keeps gm06TerminalFaceTraceRegs gm06TerminalFaceTraceArrs s s₄ :=
    hk₁₃.trans hk₄ (by simp [gm06TerminalFaceTraceRegs]) (by simp [gm06TerminalFaceTraceArrs])
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, hd₅⟩ := gm13TabulateProg_exec (w := w) 650 (.len 614) (.read 614 (.reg 650)) 600
    walk s₄ hw1 (by omega)
    (fun st hk => GraphMinor.Compute.Crossing.eval_len ((hk.2 614 (by decide)).trans hd₄) (by omega))
    (fun st i hi hk hr => by
      have ha := (hk.2 614 (by decide)).trans hd₄
      have he := GraphMinor.Compute.Crossing.eval_read (a := 614)
        (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega)) (by simpa only [ha] using hi)
        (by simpa only [ha] using (hwalkBound _ (List.getElem_mem hi)).trans hm)
      simpa only [ha] using he)
  have hk₁₅ : Keeps gm06TerminalFaceTraceRegs gm06TerminalFaceTraceArrs s s₅ :=
    hk₁₄.trans hk₅ (by simp [gm06TerminalFaceTraceRegs]) (by simp [gm06TerminalFaceTraceArrs])
  have hheads₅ : s₅.arrs 601 = gm06DartHeads origins :=
    (hk₅.2 601 (by decide)).trans ((hk₄.2 601 (by decide)).trans ((hk₃.2 601 (by decide)).trans hd₁))
  have htargets₅ : s₅.arrs 602 = gm06IncidenceBits n labels :=
    (hk₅.2 602 (by decide)).trans ((hk₄.2 602 (by decide)).trans hd₃)
  obtain ⟨sf, tf, hef, htf, hkf, hdf, _, hflag⟩ := gm06TerminalTraceProg_exec (gm06DartHeads origins)
    (gm06IncidenceBits n labels) walk s₅ hw1 (by omega)
    (by simpa only [gm06DartHeads_length, horg] using hm) (by simpa only [gm06IncidenceBits, List.length_ofFn] using hn)
    (fun d hd => by simpa only [gm06DartHeads_length, horg] using hwalkBound d hd)
    (fun v hv => by simpa only [gm06IncidenceBits, List.length_ofFn] using gm06DartHeads_bounds origins horg hvalues v hv)
    (by
      intro b hb
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hb
      split <;> omega) hd₅ hheads₅ htargets₅
  refine ⟨sf, t₁ + (3 + (t₃ + (t₄ + (t₅ + tf)))), .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ hef)))), ?_,
    hk₁₅.trans hkf (by simp [gm06TerminalFaceTraceRegs]) (by simp [gm06TerminalFaceTraceArrs]),
    hdf, hflag, (hkf.2 601 (by decide)).trans hheads₅, ?_⟩
  · simp only [Expr.cost] at ht₅
    omega
  · exact (hkf.1 606 (by decide)).trans ((hk₅.1 606 (by decide)).trans ((hk₄.1 606 (by decide)).trans
      ((hk₃.1 606 (by decide)).trans (by simp [s₂, source]))))

/-- The finite trace is a prefix of the indicated rotated face walk. -/
theorem gm06TerminalFaceTrace_prefix (n : ℕ) (origins face left upper : List ℕ) (cuff : ℕ) :
    (gm06TerminalFaceTrace n origins face left upper cuff).1 <+: gm06TerminalFaceWalk face cuff :=
  gm06FirstContact_prefix _ _

/-- Every internal head vertex of the trace is outside the exact set T_i. -/
theorem gm06TerminalFaceTrace_internal {n m : ℕ} (origins face left upper : List ℕ) (cuff : ℕ)
    (horg : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hc : cuff ∈ face) (hface : ∀ d ∈ face, d < 2 * m) :
    ∀ d ∈ (gm06TerminalFaceTrace n origins face left upper cuff).1.dropLast,
      gm06CutNeighbourHead origins d ∉ gm06TerminalTargetLabels (gm06CutNeighbourHead origins cuff) left upper := by
  let labels := gm06TerminalTargetLabels (gm06CutNeighbourHead origins cuff) left upper
  let walk := gm06TerminalFaceWalk face cuff
  intro d hd
  have hprefix := gm06TerminalFaceTrace_prefix n origins face left upper cuff
  obtain ⟨rest, heq⟩ := hprefix
  have hdTrace : d ∈ (gm06TerminalFaceTrace n origins face left upper cuff).1 :=
    (List.dropLast_sublist _).mem hd
  have hdWalk : d ∈ walk := by
    change d ∈ gm06TerminalFaceWalk face cuff
    rw [← heq]
    exact List.mem_append_left _ hdTrace
  have hdOrg : d < origins.length := horg ▸ hface d (gm06TerminalFaceWalk_mem hc hdWalk)
  have hmOrg : gm06DartMate d < origins.length := by
    rw [horg]
    exact gm06DartMate_lt (horg ▸ hdOrg)
  have hv : gm06CutNeighbourHead origins d < n := by
    simpa only [gm06CutNeighbourHead, List.getElem?_eq_getElem hmOrg, Option.getD_some] using
      hvalues _ (List.getElem_mem hmOrg)
  have hzero := (gm06TerminalTrace_spec (gm06DartHeads origins) (gm06IncidenceBits n labels) walk).2.1 d hd
  rw [gm06DartHeads_get origins hdOrg] at hzero
  change (gm06IncidenceBits n labels)[gm06CutNeighbourHead origins d]?.getD 0 = 0 at hzero
  simp only [gm06IncidenceBits, List.getElem?_ofFn, hv, ↓reduceDIte, Option.getD_some] at hzero
  change gm06CutNeighbourHead origins d ∉ labels
  by_contra hmem
  simp only [hmem, ↓reduceIte, one_ne_zero] at hzero

/-- The traced prefix starts at the head of the reverse inner cuff
and is a directed walk whenever the input face is a closed directed walk. -/
theorem gm06TerminalFaceTrace_walk {n v cuff : ℕ} (origins face left upper : List ℕ)
    (hclosed : GM06DartWalk (fun d => origins[d]?.getD 0) (gm06CutNeighbourHead origins) v face v)
    (hc : cuff ∈ face) :
    ∃ target, GM06DartWalk (fun d => origins[d]?.getD 0) (gm06CutNeighbourHead origins)
      (gm06CutNeighbourHead origins cuff) (gm06TerminalFaceTrace n origins face left upper cuff).1 target := by
  let walk := gm06TerminalFaceWalk face cuff
  let trace := (gm06TerminalFaceTrace n origins face left upper cuff).1
  have hw := gm06TerminalFaceWalk_walk hclosed hc
  have hpre := gm06TerminalFaceTrace_prefix n origins face left upper cuff
  have hlen : trace.length ≤ walk.length := hpre.length_le
  obtain ⟨rest, heq⟩ := hpre
  have htake : walk.take trace.length = trace := by
    dsimp only [walk, trace]
    rw [← heq]
    simp
  have hw' := hw.take trace.length hlen
  dsimp only [walk] at htake
  rw [htake] at hw'
  exact ⟨_, hw'⟩

end GraphMinor.Compute
