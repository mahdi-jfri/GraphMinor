module

public import GraphMinor.Compute.GM06ContractState
public import GraphMinor.Compute.GM06RecoverContractions
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Applying the selected initial-edge contraction

The full Reduction 3 scan of VI (5.7), page 133, retains its chosen
path index in register 328. Restore that index, record the path and
first directed word for UNDO, then update the complete finite core.
The result includes the exact history write, rotation splice, path
shortening, endpoint substitution and both activity-mask changes.

The linkage masks are scratch data rebuilt at the next loop entry.
The command preserves the fixed cuff arrays and original label
positions. Its cost is linear in the endpoint and row encodings.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- Restore the selected index, save its recovery pair and perform
the finite core update for Reduction 3. -/
@[expose] def gm06ApplyReduction3Prog : Cmd :=
  .seq (.assign 295 (.reg 328))
    (.seq gm06RecordContractionProg gm06ContractStateProg)

/-- The complete selected-contraction command makes the exact
finite core and recovery writes, with strict progress in both live
counts. No array update is supplied as a conclusion hypothesis. -/
theorem gm06ApplyReduction3Prog_exec {w : ℕ}
    (xs mask live hist : List ℕ) (rots paths : List (List ℕ)) (a b i e c : ℕ)
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
    (hhist : hist.length < 2 ^ w) (hslot : 2 * c + 1 < hist.length)
    (h3 : s.arrs 3 = xs) (h4 : s.arrs 4 = gm06EncodeRows rots)
    (h8 : s.arrs 8 = gm06EncodeRows paths) (h9 : s.arrs 9 = hist)
    (h12 : s.arrs 12 = mask) (h14 : s.arrs 14 = live)
    (h22 : s.regs 22 = a) (h301 : s.regs 301 = b) (h328 : s.regs 328 = i)
    (h23 : s.regs 23 = paths[i][0]) (h24 : s.regs 24 = e) (h309 : s.regs 309 = c) :
    ∃ s' t, Exec w gm06ApplyReduction3Prog s s' t ∧
      t ≤ 682 + 14 * xs.length + 1000 * (gm06EncodeRows rots).length +
        17 * i + 22 * paths[i].length + 32 * (gm06EncodeRows paths).length ∧
      Keeps [295, 309, 31, 7, 8, 9, 11, 320, 317, 319, 313, 323, 324, 98,
        311, 310, 312, 308, 307] [9, 25, 26, 27, 4, 28, 24, 8, 3, 12, 14] s s' ∧
      s'.regs 295 = i ∧ s'.regs 309 = c + 1 ∧
      s'.arrs 9 = (hist.set (2 * c) i).set (2 * c + 1) paths[i][0] ∧
      s'.arrs 3 = xs.map (fun v => if v = b then a else v) ∧
      s'.arrs 4 = gm06EncodeRows ((rots.set a
        (gm06SplicedRotation rots[a] rots[b] (rots[a].idxOf paths[i][0]) (rots[b].idxOf e))).set b []) ∧
      s'.arrs 8 = gm06EncodeRows (paths.set i paths[i].tail) ∧
      s'.arrs 12 = mask.set (paths[i][0] / 2) 0 ∧ s'.arrs 14 = live.set b 0 ∧
      (s'.arrs 12).count 1 + 1 = mask.count 1 ∧
      (s'.arrs 14).count 1 + 1 = live.count 1 ∧
      (s'.arrs 4).length + 2 = (gm06EncodeRows rots).length ∧
      (s'.arrs 8).length + 1 = (gm06EncodeRows paths).length := by
  have hiw : i < 2 ^ w := hi.trans
    (hpathWords paths.length (by simp only [gm06EncodeRows, List.mem_cons, true_or]))
  have hdw : paths[i][0] < 2 ^ w := hdMask.trans hm
  let s₀ := s.setReg 295 i
  have he₀ : Exec w (.assign 295 (.reg 328)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h328 hiw)
  obtain ⟨he₁, hk₁, hhist₁⟩ := gm06RecordContractionProg_exec hist c i paths[i][0] s₀ hw
    hhist hslot hiw hdw (by simpa [s₀] using h9) (by simpa [s₀] using h309)
    (by simp [s₀]) (by simpa [s₀] using h23)
  let s₁ := ((s₀.writeArr 9 (2 * c) i).writeArr 9 (2 * c + 1) paths[i][0]).setReg 309 (c + 1)
  have hk₁' : Keeps [309] [9] s₀ s₁ := hk₁
  have h295₁ : s₁.regs 295 = i := (hk₁'.1 295 (by decide)).trans (by simp [s₀])
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hends, hrots, hpaths, hmask, hlive', hmaskDrop,
      hliveDrop, hrotDrop, hpathDrop⟩ := gm06ContractStateProg_exec xs mask live rots paths
    a b i e ha hb hab hi hne hnda hndb hd he s₁ hw hrotLen hrotWords hpathLen hpathWords
    hxLen hl hm hx haw hbLive hdMask hactive hlive
    ((hk₁'.2 3 (by decide)).trans (by simpa [s₀] using h3))
    ((hk₁'.2 4 (by decide)).trans (by simpa [s₀] using h4))
    ((hk₁'.2 8 (by decide)).trans (by simpa [s₀] using h8))
    ((hk₁'.2 12 (by decide)).trans (by simpa [s₀] using h12))
    ((hk₁'.2 14 (by decide)).trans (by simpa [s₀] using h14))
    ((hk₁'.1 22 (by decide)).trans (by simpa [s₀] using h22))
    ((hk₁'.1 301 (by decide)).trans (by simpa [s₀] using h301)) h295₁
    ((hk₁'.1 23 (by decide)).trans (by simpa [s₀] using h23))
    ((hk₁'.1 24 (by decide)).trans (by simpa [s₀] using h24))
  let R := [295, 309, 31, 7, 8, 9, 11, 320, 317, 319, 313, 323, 324, 98,
    311, 310, 312, 308, 307]
  let A := [9, 25, 26, 27, 4, 28, 24, 8, 3, 12, 14]
  have hk₀ : Keeps R A s s₀ := (Keeps.refl _ _ s).setReg (by simp [R]) _
  have hk : Keeps R A s s₂ :=
    (hk₀.trans hk₁' (by simp [R]) (by simp [A])).trans hk₂ (by simp [R]) (by simp [A])
  have h309₁ : s₁.regs 309 = c + 1 := by simp [s₁]
  refine ⟨s₂, 2 + (16 + t₂), .seq he₀ (.seq he₁ he₂), by omega, hk,
    (hk₂.1 295 (by decide)).trans h295₁,
    (hk₂.1 309 (by decide)).trans h309₁,
    (hk₂.2 9 (by decide)).trans hhist₁, hends, hrots, hpaths, hmask, hlive',
    hmaskDrop, hliveDrop, hrotDrop, hpathDrop⟩

/-- The allocated recovery suffix is consumed by exactly two
words when the next chronological contraction pair is recorded. -/
theorem gm06ContractionHistoryWords_record (records : List (ℕ × ℕ))
    (i d x y : ℕ) (tail : List ℕ) :
    (((gm06ContractionHistoryWords records ++ x :: y :: tail).set (2 * records.length) i).set
      (2 * records.length + 1) d) = gm06ContractionHistoryWords (records ++ [(i, d)]) ++ tail := by
  have hlen : (gm06ContractionHistoryWords records).length = 2 * records.length := by
    induction records with
    | nil => rfl
    | cons p ps ih =>
      simp only [gm06ContractionHistoryWords, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil] at *
      omega
  have happ : gm06ContractionHistoryWords (records ++ [(i, d)]) =
      gm06ContractionHistoryWords records ++ [i, d] := by
    simp only [gm06ContractionHistoryWords, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  rw [happ, ← hlen]
  rw [List.set_append_right _ _ (by omega)]
  simp only [Nat.sub_self, List.set_cons_zero]
  rw [List.set_append_right _ _ (by omega)]
  simp

end GraphMinor.Compute
