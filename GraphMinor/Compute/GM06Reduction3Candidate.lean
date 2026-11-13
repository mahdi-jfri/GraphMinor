module

public import GraphMinor.Compute.GM06ActiveEndpointSum
public import GraphMinor.Compute.GM06InitialNeighbour
public import GraphMinor.Compute.GM06OuterCuffAbsent
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing the Reduction 3 eligibility flag

For VI (5.7), page 133, count the current active ends at the
initial vertex, read the given path's first-edge neighbour, and
search for it on the outer cuff. Multiply the valency-one flag
by the off-cuff flag. The resulting bit is the finite eligibility
test for contracting this initial edge. Every value is computed
from the endpoint, activity, cuff and given path arrays.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Set 306 when vertex 22 has active valency one and the first
edge of path 295 has its other endpoint off the supplied outer cuff. -/
def gm06Reduction3CandidateProg : Cmd :=
  .seq (gm06ActiveDegreeProg 3 12)
    (.seq gm06InitialNeighbourProg (.seq gm06OuterCuffAbsentProg
      (.assign 306 (.op .mul (.op .eq (.reg 21) (.const 1)) (.reg 305)))))

/-- The candidate command computes its finite eligibility predicate
with linear scans and preserves all supplied instance arrays. -/
theorem gm06Reduction3CandidateProg_exec {w : ℕ}
    (xs mask cs : List ℕ) (paths : List (List ℕ)) (i a : ℕ)
    (hi : i < paths.length) (hne : 0 < paths[i].length)
    (hfirst : paths[i][0] < 2 * mask.length) (s : State)
    (hw : 2 < 2 ^ w) (hm : 2 * mask.length < 2 ^ w) (hlen : xs.length = 2 * mask.length)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hbits : ∀ b ∈ mask, b ≤ 1) (haw : a < 2 ^ w)
    (hcLen : cs.length < 2 ^ w) (hcWords : ∀ x ∈ cs, x < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows paths, v < 2 ^ w)
    (h3 : s.arrs 3 = xs) (h12 : s.arrs 12 = mask) (h7 : s.arrs 7 = cs)
    (h8 : s.arrs 8 = gm06EncodeRows paths) (h22 : s.regs 22 = a) (h295 : s.regs 295 = i) :
    ∃ s' t, Exec w gm06Reduction3CandidateProg s s' t ∧
      t ≤ 57 + 42 * mask.length + 17 * i + 22 * paths[i].length + 13 * cs.length ∧
      Keeps [20, 21, 7, 8, 9, 11, 31, 23, 24, 301, 303, 304, 305, 306] [24] s s' ∧
      s'.regs 21 = (gm06ActiveEndpointBits xs mask a).sum ∧
      s'.regs 23 = paths[i][0] ∧ s'.regs 24 = gm06DartMate paths[i][0] ∧
      s'.regs 301 = xs[gm06DartMate paths[i][0]]'(hlen ▸ gm06DartMate_lt hfirst) ∧
      (s'.regs 306 = 1 ↔ (gm06ActiveEndpointBits xs mask a).sum = 1 ∧
        xs[gm06DartMate paths[i][0]]'(hlen ▸ gm06DartMate_lt hfirst) ∉ cs) ∧
      (s'.regs 306 = 0 ∨ s'.regs 306 = 1) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hxLen : xs.length < 2 ^ w := hlen ▸ hm
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hcount₁⟩ := gm06ActiveDegreeProg_exec
    3 12 xs mask a s hw hlen hxLen hx
      (fun b hb => (hbits b hb).trans_lt hw1) haw h3 h12 h22
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h23₂, h24₂, h301₂⟩ := gm06InitialNeighbourProg_exec
    xs paths i hi hne s₁ hw hm hlen hx hfirst hpLen hpWords
      ((hk₁.2 3 (by simp)).trans h3) ((hk₁.2 8 (by simp)).trans h8)
      ((hk₁.1 295 (by decide)).trans h295)
  have hmate : gm06DartMate paths[i][0] < xs.length := hlen ▸ gm06DartMate_lt hfirst
  have hvw : xs[gm06DartMate paths[i][0]] < 2 ^ w := hx _ (List.getElem_mem hmate)
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hoff, hbit⟩ := gm06OuterCuffAbsentProg_exec
    cs xs[gm06DartMate paths[i][0]] s₂ hw1 hcLen hcWords hvw
      ((hk₂.2 7 (by decide)).trans ((hk₁.2 7 (by simp)).trans h7)) h301₂
  have hcount : s₃.regs 21 = (gm06ActiveEndpointBits xs mask a).sum :=
    (hk₃.1 21 (by decide)).trans ((hk₂.1 21 (by decide)).trans hcount₁)
  have hsumw : (gm06ActiveEndpointBits xs mask a).sum < 2 ^ w :=
    (gm06ActiveEndpointBits_sum_le_length xs mask a).trans_lt hxLen
  have hflag : s₃.regs 305 ≤ 1 := by rcases hbit with h | h <;> omega
  let value := (if (gm06ActiveEndpointBits xs mask a).sum = 1 then 1 else 0) * s₃.regs 305
  have hvaluew : value < 2 ^ w := by dsimp only [value]; split <;> omega
  let s₄ := s₃.setReg 306 value
  have he₄ : Exec w (.assign 306 (.op .mul (.op .eq (.reg 21) (.const 1)) (.reg 305))) s₃ s₄ 6 :=
    .assign (GraphMinor.Compute.Crossing.eval_mul
      (GraphMinor.Compute.Crossing.eval_eq
        (GraphMinor.Compute.Crossing.eval_reg hcount hsumw)
        (GraphMinor.Compute.Crossing.eval_const hw1) hw1)
      (GraphMinor.Compute.Crossing.eval_reg (s := s₃) (r := 305) rfl (hflag.trans_lt hw1)) hvaluew)
  let R := [20, 21, 7, 8, 9, 11, 31, 23, 24, 301, 303, 304, 305, 306]
  have hk₁' : Keeps R [24] s s₁ := hk₁.mono (by simp [R]) (by simp)
  have hk₂' : Keeps R [24] s s₂ := hk₁'.trans hk₂ (by simp [R]) (by simp)
  have hk₃' : Keeps R [24] s s₃ := hk₂'.trans hk₃ (by simp [R]) (by simp)
  refine ⟨s₄, t₁ + (t₂ + (t₃ + 6)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_,
    hk₃'.setReg (by simp [R]) _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen] at ht₁
    omega
  · simpa [s₄] using hcount
  · simpa [s₄] using (hk₃.1 23 (by decide)).trans h23₂
  · simpa [s₄] using (hk₃.1 24 (by decide)).trans h24₂
  · simpa [s₄] using (hk₃.1 301 (by decide)).trans h301₂
  · change value = 1 ↔ _
    by_cases h : (gm06ActiveEndpointBits xs mask a).sum = 1
    · simpa [value, h] using hoff
    · simp [value, h]
  · change value = 0 ∨ value = 1
    dsimp only [value]
    split <;> simp_all

end GraphMinor.Compute
