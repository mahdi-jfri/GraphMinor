module

public import GraphMinor.Compute.GM06ContractRotations
public import GraphMinor.Compute.GM06DropInitialPath
public import GraphMinor.Compute.GM06ContractedMasks
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The finite updates and recovery record for an initial-edge contraction

Reduction 3 of VI (5.7), page 133, keeps the initial vertex label
and retires its neighbour. Merge their rotations, remove the first
edge from the given path, replace the neighbour's endpoint labels
and clear its edge and vertex bits. Both activity counts decrease.
The linkage masks can then be recomputed from these changed fields.

A recovery record stores the selected path index and the removed
directed edge. These are the two words needed to undo this path
shortening when lifting a successor linkage back to the old graph.
The record is written by the program from its current registers.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- Update the rotations, given path, endpoint labels and two
activity masks for the computed initial-edge contraction. -/
@[expose] def gm06ContractStateProg : Cmd :=
  .seq gm06ContractRotationsProg
    (.seq gm06DropInitialPathEdgeProg gm06ContractedMasksProg)

/-- The composed contraction command makes the exact finite
updates of Reduction 3 and decreases both live counts. It preserves
the remaining instance arrays so the linkage masks can be rebuilt. -/
theorem gm06ContractStateProg_exec {w : ℕ}
    (xs mask live : List ℕ) (rots paths : List (List ℕ)) (a b i e : ℕ)
    (ha : a < rots.length) (hb : b < rots.length) (hab : a ≠ b)
    (hi : i < paths.length) (hne : 0 < paths[i].length)
    (hnda : rots[a].Nodup) (hndb : rots[b].Nodup)
    (hd : paths[i][0] ∈ rots[a]) (he : e ∈ rots[b])
    (s : State) (hw : 2 < 2 ^ w)
    (hrotLen : 4 * (gm06EncodeRows rots).length < 2 ^ w)
    (hrotWords : ∀ x ∈ gm06EncodeRows rots, x < 2 ^ w)
    (hpathLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpathWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (hxLen : xs.length < 2 ^ w) (hl : live.length < 2 ^ w)
    (hm : 2 * mask.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (haw : a < 2 ^ w) (hbLive : b < live.length)
    (hdMask : paths[i][0] < 2 * mask.length)
    (hactive : mask[paths[i][0] / 2]'(by omega) = 1) (hlive : live[b] = 1)
    (h3 : s.arrs 3 = xs) (h4 : s.arrs 4 = gm06EncodeRows rots)
    (h8 : s.arrs 8 = gm06EncodeRows paths) (h12 : s.arrs 12 = mask) (h14 : s.arrs 14 = live)
    (h22 : s.regs 22 = a) (h301 : s.regs 301 = b) (h295 : s.regs 295 = i)
    (h23 : s.regs 23 = paths[i][0]) (h24 : s.regs 24 = e) :
    ∃ s' t, Exec w gm06ContractStateProg s s' t ∧
      t ≤ 664 + 14 * xs.length + 1000 * (gm06EncodeRows rots).length +
        17 * i + 22 * paths[i].length + 32 * (gm06EncodeRows paths).length ∧
      Keeps [31, 7, 8, 9, 11, 320, 317, 319, 313, 323, 324, 98, 311, 310, 312, 308, 307]
        [25, 26, 27, 4, 28, 24, 8, 3, 12, 14] s s' ∧
      s'.arrs 3 = xs.map (fun v => if v = b then a else v) ∧
      s'.arrs 4 = gm06EncodeRows ((rots.set a
        (gm06SplicedRotation rots[a] rots[b] (rots[a].idxOf paths[i][0]) (rots[b].idxOf e))).set b []) ∧
      s'.arrs 8 = gm06EncodeRows (paths.set i paths[i].tail) ∧
      s'.arrs 12 = mask.set (paths[i][0] / 2) 0 ∧ s'.arrs 14 = live.set b 0 ∧
      (s'.arrs 12).count 1 + 1 = mask.count 1 ∧
      (s'.arrs 14).count 1 + 1 = live.count 1 ∧
      (s'.arrs 4).length + 2 = (gm06EncodeRows rots).length ∧
      (s'.arrs 8).length + 1 = (gm06EncodeRows paths).length := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hrot, hrotDrop⟩ := gm06ContractRotationsProg_exec
    rots a b paths[i][0] e ha hb hab hnda hndb hd he s hw hrotLen hrotWords h4 h22 h301 h23 h24
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hpath, hpathDrop, _⟩ := gm06DropInitialPathEdgeProg_exec
    paths i hi hne s₁ (by omega) hpathLen hpathWords
    ((hk₁.2 8 (by decide)).trans h8) ((hk₁.1 295 (by decide)).trans h295)
  let R := [31, 7, 8, 9, 11, 320, 317, 319, 313, 323, 324, 98, 311, 310, 312, 308, 307]
  let A := [25, 26, 27, 4, 28, 24, 8, 3, 12, 14]
  have hk₁' : Keeps R A s s₁ := hk₁.mono (by simp [R]) (by simp [A])
  have hk₂' : Keeps R A s s₂ := hk₁'.trans hk₂ (by simp [R]) (by simp [A])
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hends, hmask, hverts, hmaskDrop, hvertsDrop⟩ :=
    gm06ContractedMasksProg_exec xs mask live a b paths[i][0] s₂ hw hxLen hl hm hx haw
      hbLive hdMask hactive hlive
      ((hk₂.2 3 (by decide)).trans ((hk₁.2 3 (by decide)).trans h3))
      ((hk₂.2 12 (by decide)).trans ((hk₁.2 12 (by decide)).trans h12))
      ((hk₂.2 14 (by decide)).trans ((hk₁.2 14 (by decide)).trans h14))
      ((hk₂'.1 22 (by decide)).trans h22) ((hk₂'.1 301 (by decide)).trans h301)
      ((hk₂'.1 23 (by decide)).trans h23)
  have hrot' : s₃.arrs 4 = s₁.arrs 4 :=
    (hk₃.2 4 (by decide)).trans (hk₂.2 4 (by decide))
  have hpath' : s₃.arrs 8 = s₂.arrs 8 := hk₃.2 8 (by decide)
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), by omega,
    hk₂'.trans hk₃ (by simp [R]) (by simp [A]), hends, hrot'.trans hrot,
    hpath'.trans hpath, hmask, hverts, hmaskDrop, hvertsDrop, ?_, ?_⟩
  · simpa only [hrot'] using hrotDrop
  · simpa only [hpath'] using hpathDrop

/-- Store the next pair of recovery words in array 9 and advance
the record count in register 309. The path index and first edge
are read directly from registers 295 and 23. -/
@[expose] def gm06RecordContractionProg : Cmd :=
  .seq (.write 9 (.op .mul (.const 2) (.reg 309)) (.reg 295))
    (.seq (.write 9 (.op .add (.op .mul (.const 2) (.reg 309)) (.const 1)) (.reg 23))
      (.assign 309 (.op .add (.reg 309) (.const 1))))

/-- A contraction record writes precisely its two words, preserves
all other history positions and increases the record count by one. -/
theorem gm06RecordContractionProg_exec {w : ℕ} (hist : List ℕ) (c i d : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : hist.length < 2 ^ w) (hc : 2 * c + 1 < hist.length)
    (hi : i < 2 ^ w) (hd : d < 2 ^ w) (h9 : s.arrs 9 = hist)
    (h309 : s.regs 309 = c) (h295 : s.regs 295 = i) (h23 : s.regs 23 = d) :
    Exec w gm06RecordContractionProg s
      (((s.writeArr 9 (2 * c) i).writeArr 9 (2 * c + 1) d).setReg 309 (c + 1)) 16 ∧
      Keeps [309] [9] s (((s.writeArr 9 (2 * c) i).writeArr 9 (2 * c + 1) d).setReg 309 (c + 1)) ∧
      (((s.writeArr 9 (2 * c) i).writeArr 9 (2 * c + 1) d).setReg 309 (c + 1)).arrs 9 =
        (hist.set (2 * c) i).set (2 * c + 1) d := by
  have hcW : c < 2 ^ w := by omega
  have hmul := GraphMinor.Compute.Crossing.eval_mul
    (GraphMinor.Compute.Crossing.eval_const hw) (GraphMinor.Compute.Crossing.eval_reg h309 hcW)
    (show 2 * c < 2 ^ w by omega)
  let s₁ := s.writeArr 9 (2 * c) i
  have he₁ : Exec w (.write 9 (.op .mul (.const 2) (.reg 309)) (.reg 295)) s s₁ 5 :=
    .write hmul (GraphMinor.Compute.Crossing.eval_reg h295 hi) (by rw [h9]; omega)
  let s₂ := s₁.writeArr 9 (2 * c + 1) d
  have he₂ : Exec w (.write 9 (.op .add (.op .mul (.const 2) (.reg 309)) (.const 1)) (.reg 23)) s₁ s₂ 7 :=
    .write (GraphMinor.Compute.Crossing.eval_add
      (by simpa only [s₁, Expr.eval, State.writeArr_regs] using hmul)
      (GraphMinor.Compute.Crossing.eval_const (show 1 < 2 ^ w by omega)) (hc.trans hn))
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁] using h23) hd)
      (by simpa [s₁, h9] using hc)
  have he₃ : Exec w (.assign 309 (.op .add (.reg 309) (.const 1))) s₂ (s₂.setReg 309 (c + 1)) 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₂, s₁] using h309) hcW)
      (GraphMinor.Compute.Crossing.eval_const (show 1 < 2 ^ w by omega)) (by omega))
  refine ⟨.seq he₁ (.seq he₂ he₃), ?_, ?_⟩
  · exact (((Keeps.refl [309] [9] s).writeArr (by simp) _ _).writeArr (by simp) _ _).setReg (by simp) _
  · simp only [State.setReg_arrs, State.writeArr_arrs_self, h9]

end GraphMinor.Compute
