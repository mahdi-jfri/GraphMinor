module

public import GraphMinor.Compute.GM02PortEdgeBodyPrefix
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning all canonical numeric split pairs

Run the proved pair body for the square of the numeric vertex count.
The loop invariant records the exact emitted edge prefix, its next free
word position, and its edge count. It also preserves original input
arrays and metadata. The completed buffer therefore contains exactly
the canonical split edge list, with its unused suffix still zero.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- The registers changed by the canonical edge scan. -/
@[expose] def gm02PortEdgeScanRegs : List ℕ := [32, 42, 43, 44, 45, 46, 60, 61, 62, 63, 64, 67, 68]

/-- Scan all pair positions, using the square bound in register 65. -/
@[expose] def gm02PortEdgeScanProg (src : Arr) : Cmd := forUp 64 (.reg 65) (gm02PortEdgeBody src)

/-- The full numeric pair scan constructs the canonical edge buffer in quadratic time in its vertex count. -/
theorem gm02PortEdgeScanProg_exec {w K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (gflags hflags : List ℕ) (hsrc24 : src ≠ 24)
    (hsrc : s.arrs src = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hslots : s.arrs 23 = List.ofFn (fun j : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code j.val))
    (hzero : s.regs 64 = 0)
    (hsquare : s.regs 65 = gm02FullPortSize x K * gm02FullPortSize x K)
    (hsize : s.regs 66 = gm02FullPortSize x K)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hbuf : s.arrs 24 = gm02PortEdgeBuffer (gm02FullPortGraph x gflags hflags code K) 0)
    (hpos : s.regs 67 = 2) (hcount : s.regs 68 = 0)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hfw : x.edges.length < 2 ^ w) (henc : x.enc.length < 2 ^ w)
    (hcap : 2 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) < 2 ^ w) :
    ∃ s' t, Exec w (gm02PortEdgeScanProg src) s s' t ∧
      t ≤ 3 + (gm02FullPortSize x K * gm02FullPortSize x K) * 102 ∧
      s'.arrs 24 = gm02PortEdgeBuffer (gm02FullPortGraph x gflags hflags code K)
        (gm02FullPortSize x K * gm02FullPortSize x K) ∧
      s'.regs 67 = 2 + 2 * (edgeListOf (gm02FullPortGraph x gflags hflags code K)).length ∧
      s'.regs 68 = (edgeListOf (gm02FullPortGraph x gflags hflags code K)).length ∧
      (∀ a, a ≠ 24 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ∉ gm02PortEdgeScanRegs → s'.regs r = s.regs r) := by
  let F := gm02FullPortGraph x gflags hflags code K
  let N := gm02FullPortSize x K
  let I : ℕ → State → Prop := fun j st => st.regs 64 = j ∧
    st.arrs 24 = gm02PortEdgeBuffer F j ∧
    st.regs 67 = (gm02PortEdgeWords F j).length ∧ st.regs 68 = (gm02EdgePrefix F j).length ∧
    (∀ a, a ≠ 24 → st.arrs a = s.arrs a) ∧
    (∀ r, r ∉ gm02PortEdgeScanRegs → st.regs r = s.regs r)
  have hI : I 0 s := by
    refine ⟨hzero, hbuf, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · simpa only [gm02PortEdgeWords_length, gm02EdgePrefix_zero, List.length_nil,
        Nat.mul_zero, Nat.add_zero] using hpos
    · exact hcount
  have hSq : N * N < 2 ^ w := by dsimp only [N]; omega
  obtain ⟨s', t, he, ht, hI'⟩ := forUp_exec' I (N * N) 95
    (r_i := 64) (hi := .reg 65) (body := gm02PortEdgeBody src) (by omega) hSq
    (fun j hj st hst => ⟨hst.1, eval_reg
      ((hst.2.2.2.2.2 65 (by decide)).trans hsquare) hSq⟩)
    (fun j hj st hst => by
      rcases hst with ⟨hindex, hbuffer, hposition, hcounter, harr, hreg⟩
      obtain ⟨st', t, he, ht, hbuf', hpos', hcount', ha', hr'⟩ :=
        gm02PortEdgeBody_prefix_exec x st src gflags hflags ⟨j, hj⟩
          ((harr src hsrc24).trans hsrc) ((harr 20 (by decide)).trans hG) hGlen hGbits
          ((harr 21 (by decide)).trans hH) hHlen hHbits
          ((harr 22 (by decide)).trans hmask) ((harr 23 (by decide)).trans hslots)
          hindex ((hreg 66 (by decide)).trans hsize)
          ((hreg 10 (by decide)).trans hn) ((hreg 11 (by decide)).trans hm)
          ((hreg 15 (by decide)).trans hf) hbuffer hposition hcounter hw hN hfw henc hcap
      refine ⟨st', t, he, ht, ?_, ?_⟩
      · refine ⟨State.setReg_regs_self .., hbuf', ?_, ?_, ?_, ?_⟩
        · exact (State.setReg_regs_ne st' (j + 1) (by decide : (67 : Reg) ≠ 64)).trans hpos'
        · exact (State.setReg_regs_ne st' (j + 1) (by decide : (68 : Reg) ≠ 64)).trans hcount'
        · intro a ha24
          exact (ha' a ha24).trans (harr a ha24)
        · intro r hrnot
          have hne (a : ℕ) (ha : a ∈ gm02PortEdgeScanRegs) : r ≠ a := fun h => hrnot (h.symm ▸ ha)
          exact (State.setReg_regs_ne st' (j + 1) (hne 64 (by decide))).trans
            ((hr' r (hne 32 (by decide)) (hne 42 (by decide)) (hne 43 (by decide))
              (hne 44 (by decide)) (hne 45 (by decide)) (hne 46 (by decide))
              (hne 60 (by decide)) (hne 61 (by decide)) (hne 62 (by decide))
              (hne 63 (by decide)) (hne 67 (by decide)) (hne 68 (by decide))).trans (hreg r hrnot))
      · exact (hr' 64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hindex) s hI
  refine ⟨s', t, he, ht, hI'.2.1, ?_, ?_, hI'.2.2.2.2.1, hI'.2.2.2.2.2⟩
  · simpa only [N, F, gm02PortEdgeWords_length, gm02EdgePrefix_full] using hI'.2.2.1
  · simpa only [N, F, gm02EdgePrefix_full] using hI'.2.2.2.1

end GraphMinor.Compute
