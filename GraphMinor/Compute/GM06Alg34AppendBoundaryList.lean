module

public import GraphMinor.Compute.GM06Alg34BoundaryListProg
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Appending a recomputed boundary list to the payload stream

Compute the selected new labels in exact array 11, then append their
length and words to the reserved output buffer. The old-label count
bounds both the computation and append costs. Source drawing, mask,
rank, closure, and component arrays remain available for the next list.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append one computed boundary list to payload buffer 10 at cursor 143. -/
def gm06AppendBoundaryListProg (mask ranks count : ℕ) : Cmd :=
  .seq (gm06BoundaryListProg mask ranks count) (appendLengthPrefixedProg 11 10 142 143 220)

/-- Boundary-list computation and stream emission write exactly the
length-prefixed selected words with a quadratic RAM bound. -/
theorem gm06AppendBoundaryListProg_exec {w n shift cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (mask ranks count : ℕ)
    (active : Fin n → Bool) (labels : Fin n → ℕ) (pfx : List ℕ)
    (hmask9 : mask ≠ 9) (hranks9 : ranks ≠ 9)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hfit : shift + n ≤ x.cellCount)
    (hlabel : ∀ v, active v = true → labels v < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false)
    (hout : pfx.length + 1 + n < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hmask : s.arrs mask = List.ofFn (fun u : Fin n => if active u then 1 else 0))
    (hranks : s.arrs ranks = List.ofFn labels) (hcount : s.regs count = n)
    (hshift : s.regs 208 = shift)
    (hbuf : IsPrefixBuffer 10 pfx (1 +
      (gm06BoundaryWords (gm06BoundarySelection x vs a shift hfit active) labels (List.finRange n)).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    let words := gm06BoundaryWords (gm06BoundarySelection x vs a shift hfit active)
      labels (List.finRange n)
    ∃ s' t, Exec w (gm06AppendBoundaryListProg mask ranks count) s s' t ∧
      t ≤ (18 * x.cellCount + 72) * n + 29 ∧
      IsPrefixBuffer 10 (pfx ++ GM06DrawingData.listWords words) cap s' ∧
      s'.regs 143 = (pfx ++ GM06DrawingData.listWords words).length ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 10 → j ≠ 11 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, q < 210 → q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 143 → q ≠ 204 → q ≠ 205 → q ≠ 206 →
        q ≠ 207 → q ≠ 209 → s'.regs q = s.regs q) := by
  dsimp only
  let selected := gm06BoundarySelection x vs a shift hfit active
  let words := gm06BoundaryWords selected labels (List.finRange n)
  have hlength : words.length ≤ n := by
    simpa only [List.length_finRange] using gm06BoundaryWords_length_le selected labels (List.finRange n)
  have hwords : ∀ j ∈ words, j < 2 ^ w := by
    intro j hj
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hj
    have hs := (List.mem_filter.mp hv).2
    have hav : active v = true := by
      cases hh : active v with
      | false => simp only [selected, gm06BoundarySelection, hh, Bool.false_and, Bool.false_eq_true] at hs
      | true => rfl
    exact hlabel v hav
  obtain ⟨s₁, t₁, hex₁, ht₁, harray, htotal, harr₁, hreg₁⟩ :=
    gm06BoundaryListProg_exec x vs a mask ranks count active labels hmask9 hranks9
      hw hN hsquare hfit hlabel ha hmarks hmat hc hmask hranks hcount hshift
  have hbuf₁ : IsPrefixBuffer 10 pfx (1 + words.length + cap) s₁ :=
    hbuf.of_arr_eq (harr₁ 10 (by decide) (by decide))
  have hcursor₁ : s₁.regs 143 = pfx.length :=
    (hreg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hcursor
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hcursor₂, _, harr₂, hreg₂⟩ :=
    appendLengthPrefixedProg_exec 11 10 142 143 220 (by decide) (by decide) (by decide)
      (by decide) hwords hw (by omega) harray hbuf₁ htotal hcursor₁
  refine ⟨s₂, t₁ + t₂, Exec.seq hex₁ hex₂, ?_, hbuf₂, hcursor₂, ?_, ?_⟩
  · have hcost : (18 * x.cellCount + 72) * n = (18 * x.cellCount + 55) * n + 17 * n := by
      rw [show 18 * x.cellCount + 72 = (18 * x.cellCount + 55) + 17 by omega, Nat.add_mul]
    rw [hcost]
    omega
  · intro j hj₁ hj₂ hj₃; exact (harr₂ j hj₂).trans (harr₁ j hj₁ hj₃)
  · intro q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈ hq₉
    exact (hreg₂ q (by omega) hq₄).trans (hreg₁ q hq hq₁ hq₂ hq₃ hq₅ hq₆ hq₇ hq₈ hq₉)

end GraphMinor.Compute
