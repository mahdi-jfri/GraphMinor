module

public import GraphMinor.Compute.GM06InitialLoopBits
public import GraphMinor.Compute.GM06FindLabel

/-!
# Finding an active loop at an initial vertex

Compute the loop flags from the current endpoint and activity
arrays, then search those flags for one. The result is an actual
active loop or the edge-count sentinel excluding every such loop.
The scan handles the attachment loops needed by Reduction 2 in VI (5.7).
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Find an active loop at vertex 135, returning its index or the edge count in 288. -/
def gm06FindInitialLoopProg : Cmd :=
  .seq gm06InitialLoopBitsProg
    (.seq (.assign 286 (.const 1)) (gm06FindLabelProg 23 286 287 288))

/-- The loop scan returns a genuine active loop or excludes all loops
at the selected initial vertex, in linear vertex and edge time. -/
theorem gm06FindInitialLoopProg_exec {w n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    (ha : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs 12 = tagged.map Prod.snd)
    (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) :
    ∃ s' t, Exec w gm06FindInitialLoopProg s s' t ∧
      t ≤ 21 + 15 * n + 41 * tagged.length ∧
      Keeps [180, 181, 286, 287, 288] [22, 23] s s' ∧
      ((s'.regs 288 = tagged.length ∧ ∀ j : Fin tagged.length,
          ¬ (tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut)) ∨
        ∃ j : Fin tagged.length, s'.regs 288 = j.val ∧
          tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hmw : tagged.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hl₁⟩ := gm06InitialLoopBitsProg_exec tagged cut s hw hn hm hbits ha hb hN hcut
  let s₂ := s₁.setReg 286 1
  have he₂ : Exec w (.assign 286 (.const 1)) s₁ s₂ 2 := .assign (eval_const hw1)
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hout₃⟩ := gm06FindLabelProg_exec
    23 286 287 288 (by decide) (by decide) (by decide) (gm06InducedEdgeBits tagged {cut}) 1 s₂ hw1
    (by simpa only [gm06InducedEdgeBits_length] using hmw)
    (fun b hb' => (gm06InducedEdgeBits_le_one tagged {cut} hbits b hb').trans_lt hw1)
    hw1 hl₁ (by simp [s₂])
  let regs := [180, 181, 286, 287, 288]
  have hk₁' : Keeps regs [22, 23] s s₁ := hk₁.mono (by simp [regs]) (by simp)
  have hk₂' : Keeps regs [22, 23] s s₂ := hk₁'.setReg (by simp [regs]) _
  have hk₃' : Keeps regs [22, 23] s₂ s₃ := hk₃.mono (by simp [regs]) (by simp)
  rw [gm06InducedEdgeBits_length] at ht₃
  refine ⟨s₃, t₁ + (2 + t₃), .seq he₁ (.seq he₂ he₃), by omega,
    hk₂'.trans hk₃' (by simp) (by simp), ?_⟩
  rcases hout₃ with ⟨hnone, hexclude⟩ | ⟨j, hj, hchosen, hloop⟩
  · left
    refine ⟨by simpa only [gm06InducedEdgeBits_length] using hnone, ?_⟩
    intro j hjloop
    exact hexclude j.val (by rw [gm06InducedEdgeBits_length]; exact j.isLt)
      ((gm06InitialLoopBits_getElem_eq_one tagged cut j.isLt).mpr hjloop)
  · right
    have hj' : j < tagged.length := by simpa only [gm06InducedEdgeBits_length] using hj
    exact ⟨⟨j, hj'⟩, hchosen, (gm06InitialLoopBits_getElem_eq_one tagged cut hj').mp hloop⟩

end GraphMinor.Compute
