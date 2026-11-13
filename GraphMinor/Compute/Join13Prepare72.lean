module

public import GraphMinor.Compute.Join13Sizes72
public import GraphMinor.Compute.Join13Columns72
public import GraphMinor.Compute.Join13PackLists72

/-!
# Preparing the core arrays from the (7.2) caller

The three header reads are followed by graph-column preparation and decomposition
slicing. The empty root set is represented by a zero array. These are exactly
the arrays consumed by the core input packer.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Prepare graph columns, parent and leaf arrays, and empty-root bits. -/
def prepareArrays72Prog : Cmd :=
  .seq initializeSizes72Prog
    (.seq prepareColumns72Prog
      (.seq (prepareBD72Prog 13 62 63 28 52 90)
        (.alloc 61 (.reg 26))))

/-- All arrays prepared by the wrapper agree with the core input. -/
theorem prepareArrays72Prog_exec {w n B : ℕ} (G : MultiDigraph n)
    (bdCode : List ℕ) (hbd : IsValidBranchDecompCode B G bdCode) (s : State)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * G.numEdges < 2 ^ w)
    (henc : G.enc.length < 2 ^ w) (hcode : bdCode.length < 2 ^ w)
    (hG : s.arrs 12 = G.enc) (hBD : s.arrs 13 = bdCode) :
    let x := multiCoreInput72 G bdCode hbd
    ∃ s' t, Exec w prepareArrays72Prog s s' t ∧
      t ≤ 600 * (n + G.numEdges + 1) ∧
      s'.regs 26 = n ∧ s'.regs 28 = G.numEdges ∧ s'.regs 52 = x.t ∧
      s'.arrs 40 = endpointWords72 x.G ∧
      s'.arrs 66 = List.ofFn (fun e => (x.G.head e).1) ∧
      s'.arrs 65 = List.ofFn (fun e => (x.G.tail e).1) ∧
      s'.arrs 62 = List.ofFn (fun z : Fin x.t => x.p z.1) ∧
      s'.arrs 63 = List.ofFn (fun e => (x.τ e).1) ∧
      s'.arrs 61 = List.replicate n 0 := by
  have hlen : bdCode.length = 2 + bdNumTreeVerts bdCode + G.numEdges := by
    rw [← hbd.1]
    exact hbd.2.2.1
  have ht : bdNumTreeVerts bdCode < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hn₁, hm₁, htree₁, hk₁⟩ :=
    initializeSizes72Prog_exec G bdCode hbd s (by omega) hn (by omega) ht hG hBD
  obtain ⟨s₂, t₂, he₂, ht₂, he₂out, hh₂, htail₂, hk₂⟩ :=
    prepareColumns72Prog_exec G s₁ hw hn hm henc
      ((hk₁.2 12 (by simp)).trans hG) hm₁
  have hn₂ : s₂.regs 26 = n := (hk₂.1 26 (by decide)).trans hn₁
  have hm₂ : s₂.regs 28 = G.numEdges := (hk₂.1 28 (by decide)).trans hm₁
  have ht₂reg : s₂.regs 52 = bdNumTreeVerts bdCode := (hk₂.1 52 (by decide)).trans htree₁
  obtain ⟨s₃, t₃, he₃, ht₃, hp₃, hτ₃, ht₃reg, ha₃, hr₃⟩ :=
    prepareBD72Prog_exec G bdCode hbd 13 62 63 28 52 90
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s₂ (by omega) hcode
      ((hk₂.2 13 (by decide)).trans ((hk₁.2 13 (by simp)).trans hBD)) hm₂ ht₂reg
  have hn₃ : s₃.regs 26 = n := (hr₃ 26 (by decide) (by decide)).trans hn₂
  let s₄ := s₃.setArr 61 (List.replicate n 0)
  have he₄ : Exec w (.alloc 61 (.reg 26)) s₃ s₄ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hn₃, hn])
  refine ⟨s₄, t₁ + (t₂ + (t₃ + (1 + n))),
    .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hn₃
  · exact (hr₃ 28 (by decide) (by decide)).trans hm₂
  · exact ht₃reg
  · change s₃.arrs 40 = _
    rw [ha₃ 40 (by decide) (by decide)]
    exact he₂out
  · change s₃.arrs 66 = _
    rw [ha₃ 66 (by decide) (by decide)]
    exact hh₂
  · change s₃.arrs 65 = _
    rw [ha₃ 65 (by decide) (by decide)]
    exact htail₂
  · simpa [s₄] using hp₃
  · change s₃.arrs 63 = _
    exact hτ₃
  · simp [s₄]

end GraphMinor.Compute
