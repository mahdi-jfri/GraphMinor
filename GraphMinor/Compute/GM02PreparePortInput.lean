module

public import GraphMinor.Compute.GM02BuildPortGraph
public import GraphMinor.Compute.GM02BuildTerminalSuffix
public import GraphMinor.Compute.GM02JoinPortInput

/-!
# Preparing the complete plain split instance

Build the candidate numeric graph, construct its canonical terminal
suffix, and join both arrays. Composition preserves original input and
active flags while producing precisely the typed ordinary input used
by II (3.2). The total construction bound is quadratic in the numeric
vertex count and linear in the supplied pattern edge count.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- Construct the full plain numeric terminated input in array 28. -/
@[expose] def gm02PreparePortInputProg (src : Arr) (K : ℕ) : Cmd :=
  .seq (gm02BuildPortGraphProg src K) (.seq gm02BuildTerminalSuffixProg gm02JoinPortInputProg)

private theorem prepare_time_bound (q m tg tt tj : ℕ)
    (hg : tg ≤ 75 + 136 * q) (ht : tt ≤ 49 + 73 * m) (hj : tj ≤ 68 + 32 * q + 32 * m) :
    tg + (tt + tj) ≤ 192 + 168 * q + 105 * m := by omega

/-- Actual graph and terminal construction produces the exact plain input of the path algorithm. -/
theorem gm02PreparePortInputProg_exec {w K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (gflags hflags : List ℕ) (hsrc24 : src ≠ 24) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code))
    (hsrc : s.arrs src = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hslots : s.arrs 23 = List.ofFn (fun j : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code j.val))
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w) (henc : x.enc.length < 2 ^ w)
    (hjoin : 3 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) + 2 * x.edges.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02PreparePortInputProg src K) s s' t ∧
      t ≤ 192 + 168 * (gm02FullPortSize x K * gm02FullPortSize x K) + 105 * x.edges.length ∧
      s'.arrs 28 = (gm02NumericTerminatedInput x gflags hflags code K hK edge hvalid).enc ∧
      s'.regs 66 = gm02FullPortSize x K ∧
      (∀ a, a ≠ 24 → a ≠ 25 → a ≠ 26 → a ≠ 27 → a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ r, (r < 32 ∨ 82 < r) → r < 290 → s'.regs r = s.regs r) := by
  have hcap : 2 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) < 2 ^ w := by omega
  have htermcap : 1 + 2 * x.edges.length < 2 ^ w := by omega
  have hfw : x.edges.length < 2 ^ w := by omega
  obtain ⟨s₀, t₀, he₀, ht₀, hgraph₀, hsize₀, _, ha₀, hr₀⟩ :=
    gm02BuildPortGraphProg_exec x s src gflags hflags hsrc24 hsrc hG hGlen hGbits hH hHlen hHbits hmask hslots
      hn hm hf hw hN hfw henc hcap
  obtain ⟨s₁, t₁, he₁, ht₁, hterm₁, _, hsize₁, ha₁, hr₁⟩ :=
    gm02BuildTerminalSuffixProg_exec x hflags hK s₀ ((ha₀ 21 (by decide) (by decide)).trans hH) hHlen hHbits
      ((hr₀ 10 (Or.inl (by decide))).trans hn) ((hr₀ 11 (Or.inl (by decide))).trans hm)
      ((hr₀ 15 (Or.inl (by decide))).trans hf) hw hN htermcap
  obtain ⟨s₂, t₂, he₂, ht₂, hout, ha₂, hr₂⟩ := gm02JoinPortInputProg_exec x gflags hflags hK edge hvalid s₁
    ((ha₁ 25 (by decide) (by decide)).trans hgraph₀) hterm₁ (by omega) hN hjoin
  refine ⟨s₂, t₀ + (t₁ + t₂), .seq he₀ (.seq he₁ he₂),
    prepare_time_bound _ _ _ _ _ ht₀ ht₁ ht₂, hout, ?_, ?_, ?_⟩
  · exact (hr₂ 66 (by decide)).trans (hsize₁.trans hsize₀)
  · intro a h24 h25 h26 h27 h28
    exact (ha₂ a h28).trans ((ha₁ a h26 h27).trans (ha₀ a h24 h25))
  · intro r hrange hr290
    have hg : r < 32 ∨ 72 < r := hrange.elim Or.inl (fun h => Or.inr ((by decide : 72 < 82).trans h))
    have ht : r < 60 ∨ 82 < r := hrange.elim (fun h => Or.inl (h.trans (by decide))) Or.inr
    exact (hr₂ r hr290).trans ((hr₁ r ht).trans (hr₀ r hg))

end GraphMinor.Compute
