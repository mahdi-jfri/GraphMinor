module

public import GraphMinor.Compute.GM02PortEdgeScan
public import GraphMinor.Compute.GM02InitPortEdgeBuffer
public import GraphMinor.Compute.GM02FinalizePortGraph

/-!
# Building the plain numeric split graph encoding

Initialize the buffer and pair counters, scan all ordered pairs, and
finalize the canonical encoding. The command reads only the original
input and active flags plus the decoded candidate array. Its graph
output is exactly `encGraph` of the proved numeric split graph, with
quadratic time in that graph's vertex count.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Build the candidate split graph's canonical encoding in array 25. -/
@[expose] def gm02BuildPortGraphProg (src : Arr) (K : ℕ) : Cmd :=
  .seq (gm02InitPortEdgeBufferProg K)
    (.seq (gm02PortEdgeScanProg src) (gm02FinalizePortGraphProg 25))

private theorem builder_time_bound (q m t₁ t₂ : ℕ)
    (h₁ : t₁ ≤ 3 + q * 102) (h₂ : t₂ ≤ 16 * (2 + 2 * m) + 12) (hm : m ≤ q) :
    (28 + 2 * q) + (t₁ + t₂) ≤ 75 + 136 * q := by omega

private theorem outside_scan {r : ℕ} (h : r < 32 ∨ 72 < r) : r ∉ gm02PortEdgeScanRegs := by
  simp [gm02PortEdgeScanRegs]
  omega

private theorem outside_init {r : ℕ} (h : r < 32 ∨ 72 < r) : r ∉ [64, 65, 66, 67, 68, 69] := by
  simp
  omega

/-- The complete split graph builder computes its plain graph encoding with an explicit quadratic bound. -/
theorem gm02BuildPortGraphProg_exec {w K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (gflags hflags : List ℕ) (hsrc24 : src ≠ 24)
    (hsrc : s.arrs src = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hslots : s.arrs 23 = List.ofFn (fun j : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code j.val))
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hfw : x.edges.length < 2 ^ w) (henc : x.enc.length < 2 ^ w)
    (hcap : 2 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) < 2 ^ w) :
    ∃ s' t, Exec w (gm02BuildPortGraphProg src K) s s' t ∧
      t ≤ 75 + 136 * (gm02FullPortSize x K * gm02FullPortSize x K) ∧
      s'.arrs 25 = encGraph (gm02FullPortGraph x gflags hflags code K) ∧
      s'.regs 66 = gm02FullPortSize x K ∧
      s'.regs 68 = (edgeListOf (gm02FullPortGraph x gflags hflags code K)).length ∧
      (∀ a, a ≠ 24 → a ≠ 25 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 32 ∨ 72 < r → s'.regs r = s.regs r) := by
  let F := gm02FullPortGraph x gflags hflags code K
  let N := gm02FullPortSize x K
  obtain ⟨s₀, he₀, hbuf₀, hz₀, hsq₀, hn₀, hpos₀, hcount₀, ha₀, hr₀⟩ :=
    gm02InitPortEdgeBufferProg_exec x s gflags hflags code hn hm hw hN hcap
  obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hpos₁, hcount₁, ha₁, hr₁⟩ :=
    gm02PortEdgeScanProg_exec x s₀ src gflags hflags hsrc24
      ((ha₀ src hsrc24).trans hsrc) ((ha₀ 20 (by decide)).trans hG) hGlen hGbits
      ((ha₀ 21 (by decide)).trans hH) hHlen hHbits
      ((ha₀ 22 (by decide)).trans hmask) ((ha₀ 23 (by decide)).trans hslots)
      hz₀ hsq₀ hn₀ ((hr₀ 10 (by decide)).trans hn) ((hr₀ 11 (by decide)).trans hm)
      ((hr₀ 15 (by decide)).trans hf) hbuf₀ hpos₀ hcount₀ hw hN hfw henc hcap
  have hmle : (edgeListOf F).length ≤ N * N := by
    simpa only [N, F, gm02EdgePrefix_full] using gm02EdgePrefix_length_le F (N * N)
  have hlen : 2 + 2 * (edgeListOf F).length < 2 ^ w := by dsimp only [N] at hmle; omega
  obtain ⟨s₂, t₂, he₂, ht₂, hout, ha₂, hr₂⟩ :=
    gm02FinalizePortGraphProg_exec F s₁ 25 (by decide) hbuf₁ hpos₁ hcount₁ (by omega) hN hlen
  refine ⟨s₂, (28 + 2 * (N * N)) + (t₁ + t₂), .seq he₀ (.seq he₁ he₂), ?_, hout, ?_, ?_, ?_, ?_⟩
  · exact builder_time_bound (N * N) (edgeListOf F).length t₁ t₂ ht₁ ht₂ hmle
  · exact (hr₂ 66 (Or.inl (by decide))).trans ((hr₁ 66 (by decide)).trans hn₀)
  · exact (hr₂ 68 (Or.inl (by decide))).trans hcount₁
  · intro a ha24 ha25
    exact (ha₂ a ha24 ha25).trans ((ha₁ a ha24).trans (ha₀ a ha24))
  · intro r hrange
    dsimp only [Reg] at hrange ⊢
    have hrCopy : r < 70 ∨ 72 < r := hrange.elim (fun h => Or.inl (h.trans (by decide))) Or.inr
    have hrScan := outside_scan hrange
    have hrInit := outside_init hrange
    exact (hr₂ r hrCopy).trans ((hr₁ r hrScan).trans (hr₀ r hrInit))

end GraphMinor.Compute
