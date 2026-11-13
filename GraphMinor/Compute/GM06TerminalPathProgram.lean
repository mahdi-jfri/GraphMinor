module

public import GraphMinor.Compute.GM06TerminalFaceTrace
public import GraphMinor.Compute.GM06LoopErasureProgram

/-!
# The complete finite terminal-path program

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) traces the
selected face to its first boundary contact and erases closed subwalks. This
file composes the actual programs, including head and target-table
construction, face rotation, stack initialization and output copying.
The output function reads only the original finite rows. Its bound
is linear in those rows and the permanent vertex/dart spaces.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Exact TERMINAL_PATH output from the selected face and its two
boundary rows. The source is the reverse inner-cuff dart's head. -/
def gm06TerminalPath (n : ℕ) (origins face left upper : List ℕ) (cuff : ℕ) : List ℕ :=
  gm06EraseClosedSubwalks (fun d => (gm06DartHeads origins)[d]?.getD 0)
    (gm06CutNeighbourHead origins cuff) (gm06TerminalFaceTrace n origins face left upper cuff).1

/-- Trace the face and return the loop-erased directed dart row in 607. -/
def gm06TerminalPathProg : Cmd := .seq gm06TerminalFaceTraceProg gm06EraseClosedSubwalksProg

/-- Registers used by complete TERMINAL_PATH. -/
def gm06TerminalPathRegs : List ℕ := gm06TerminalFaceTraceRegs ++ gm06EraseClosedRegs

/-- Arrays used by complete TERMINAL_PATH. -/
def gm06TerminalPathArrs : List ℕ := gm06TerminalFaceTraceArrs ++ gm06EraseClosedArrs

/-- Full TERMINAL_PATH executes from plain origins, selected face and
boundary rows. Both the first-contact trace and the erased path are
computed, with an explicit linear time bound. -/
theorem gm06TerminalPathProg_exec {w n m : ℕ} (origins face left upper : List ℕ) (cuff : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (horg : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hfaceFit : face.length + 2 < 2 ^ w) (hboundaryFit : left.length + upper.length + 2 < 2 ^ w)
    (hnd : face.Nodup) (hc : cuff ∈ face) (hface : ∀ d ∈ face, d < 2 * m)
    (hleft : ∀ v ∈ left, v < n) (hupper : ∀ v ∈ upper, v < n)
    (h626 : s.arrs 626 = origins) (h600 : s.arrs 600 = face)
    (h609 : s.arrs 609 = left) (h608 : s.arrs 608 = upper)
    (h667 : s.regs 667 = cuff) (h648 : s.regs 648 = n) :
    ∃ sf t, Exec w gm06TerminalPathProg s sf t ∧
      t ≤ 170 + 14 * n + 30 * (2 * m) + 203 * face.length + 60 * (left.length + upper.length) ∧
      Keeps gm06TerminalPathRegs gm06TerminalPathArrs s sf ∧
      sf.arrs 607 = gm06TerminalPath n origins face left upper cuff ∧
      sf.arrs 603 = (gm06TerminalFaceTrace n origins face left upper cuff).1 ∧
      sf.regs 602 = (gm06TerminalFaceTrace n origins face left upper cuff).2.toNat := by
  let trace := (gm06TerminalFaceTrace n origins face left upper cuff).1
  have hprefix := gm06TerminalFaceTrace_prefix n origins face left upper cuff
  have hwalkLen := gm06TerminalFaceWalk_length face cuff hc
  have htraceLen : trace.length ≤ face.length := hprefix.length_le.trans (by omega)
  have htrace : ∀ d ∈ trace, d < (gm06DartHeads origins).length := by
    intro d hd
    rw [gm06DartHeads_length, horg]
    exact hface d (gm06TerminalFaceWalk_mem hc (hprefix.subset hd))
  have hsource : gm06CutNeighbourHead origins cuff < n := by
    have hmate : gm06DartMate cuff < origins.length := horg ▸ gm06DartMate_lt (hface cuff hc)
    simpa only [gm06CutNeighbourHead, List.getElem?_eq_getElem hmate, Option.getD_some] using
      hvalues _ (List.getElem_mem hmate)
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hf₁, hh₁, hs₁⟩ := gm06TerminalFaceTraceProg_exec origins face left upper cuff s
    hw hn hm horg hvalues hfaceFit hboundaryFit hnd hc hface hleft hupper h626 h600 h609 h608 h667 h648
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06EraseClosedSubwalksProg_exec (gm06DartHeads origins) trace s₁
    (by omega) hn hsource (by omega) (by simpa only [gm06DartHeads_length, horg] using hm)
    htrace (gm06DartHeads_bounds origins horg hvalues) hh₁ hd₁ hs₁
    ((hk₁.1 648 (by decide)).trans h648)
  refine ⟨sf, t₁ + tf, .seq he₁ hef, by omega,
    (hk₁.mono (fun _ hr => List.mem_append_left _ hr) (fun _ ha => List.mem_append_left _ ha)).trans hkf
      (fun _ hr => List.mem_append_right _ hr) (fun _ ha => List.mem_append_right _ ha), hdf,
    (hkf.2 603 (by decide)).trans hd₁, (hkf.1 602 (by decide)).trans hf₁⟩

private theorem walk_change_head {D V : Type*} {tail head head' : D → V} {source target : V}
    {ds : List D} (h : GM06DartWalk tail head source ds target)
    (heq : ∀ d ∈ ds, head d = head' d) : GM06DartWalk tail head' source ds target := by
  induction h with
  | nil => exact .nil _
  | @cons source target d ds ht hw ih =>
    refine .cons ht ?_
    rw [← heq d (by simp)]
    exact ih (fun e he => heq e (List.mem_cons_of_mem _ he))

/-- Terminal erasure keeps the traced walk's ends, has distinct
vertices and uses only its directed darts. This is the finite
correctness statement of Section 15, before the geometric argument
locates the first contact on the opposite boundary. -/
theorem gm06TerminalPath_spec {n m v cuff : ℕ} (origins face left upper : List ℕ)
    (horg : origins.length = 2 * m) (hc : cuff ∈ face) (hface : ∀ d ∈ face, d < 2 * m)
    (hclosed : GM06DartWalk (fun d => origins[d]?.getD 0) (gm06CutNeighbourHead origins) v face v) :
    ∃ target,
      GM06DartWalk (fun d => origins[d]?.getD 0) (gm06CutNeighbourHead origins)
        (gm06CutNeighbourHead origins cuff) (gm06TerminalFaceTrace n origins face left upper cuff).1 target ∧
      GM06DartWalk (fun d => origins[d]?.getD 0) (gm06CutNeighbourHead origins)
        (gm06CutNeighbourHead origins cuff) (gm06TerminalPath n origins face left upper cuff) target ∧
      (gm06WalkVertices (gm06CutNeighbourHead origins) (gm06CutNeighbourHead origins cuff)
        (gm06TerminalPath n origins face left upper cuff)).Nodup ∧
      (gm06TerminalPath n origins face left upper cuff).Sublist
        (gm06TerminalFaceTrace n origins face left upper cuff).1 := by
  let trace := (gm06TerminalFaceTrace n origins face left upper cuff).1
  let path := gm06TerminalPath n origins face left upper cuff
  let head : ℕ → ℕ := fun d => (gm06DartHeads origins)[d]?.getD 0
  have heq : ∀ d ∈ trace, head d = gm06CutNeighbourHead origins d := by
    intro d hd
    have hd' := (gm06TerminalFaceTrace_prefix n origins face left upper cuff).subset hd
    exact gm06DartHeads_get origins (horg ▸ hface d (gm06TerminalFaceWalk_mem hc hd'))
  obtain ⟨target, hw⟩ := gm06TerminalFaceTrace_walk (n := n) origins face left upper hclosed hc
  have hw' := walk_change_head hw (fun d hd => (heq d hd).symm)
  obtain ⟨hp, hnd, hsub⟩ := gm06EraseClosedSubwalks_spec hw'
  have heqPath : ∀ d ∈ path, head d = gm06CutNeighbourHead origins d := fun d hd => heq d (hsub.subset hd)
  refine ⟨target, hw, walk_change_head hp heqPath, ?_, hsub⟩
  have hmap : path.map head = path.map (gm06CutNeighbourHead origins) := List.map_congr_left heqPath
  change (gm06WalkVertices head (gm06CutNeighbourHead origins cuff) path).Nodup at hnd
  simpa only [gm06WalkVertices, hmap] using hnd

end GraphMinor.Compute
