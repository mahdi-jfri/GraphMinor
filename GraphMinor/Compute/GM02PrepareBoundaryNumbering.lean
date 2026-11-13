module

public import GraphMinor.Compute.GM02TerminalSupportProg
public import GraphMinor.Compute.GM02NumberBoundary
public import GraphMinor.Compute.GM02CompressedBoundary

/-!
# Parsing and numbering a recursive boundary

Starting from the retained parent input and the separator's side arrays,
construct the original terminal support and number its union with the
separator. The original parent and side arrays remain unchanged. The
rank table, inverse names, and parsed endpoint metadata are available for
constructing the finite boundary input.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Prepare support bits, deletion bits, ranks, and inverse names in four
consecutive work arrays after the retained parent array `a`. -/
def gm02PrepareBoundaryNumberingProg (a : Arr) : Cmd :=
  .seq (gm02TerminalSupportProg a (a + 1))
    (gm02NumberBoundaryProg (a + 1) outArr 2 (a + 2) (a + 3) (a + 4))

/-- The boundary-numbering preparation reads only the parent encoding and
actual separator bits, in linear vertex-and-terminal time. -/
theorem gm02PrepareBoundaryNumberingProg_exec {w : ℕ} (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (a : Arr) (ha : 3 ≤ a) (s : State)
    (hsrc : s.arrs a = x.enc) (hleft : s.arrs outArr = bitSetList L) (hright : s.arrs 2 = bitSetList R)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    let Z := gm02BoundaryDeletedSet x L R
    ∃ s' t, Exec w (gm02PrepareBoundaryNumberingProg a) s s' t ∧
      t ≤ 63 * x.n + 28 * x.A.index + 59 ∧
      s'.arrs (a + 2) = bitSetList Z ∧
      s'.arrs (a + 3) = List.ofFn (fun v : Fin x.n => compactRank Z v.val) ∧
      s'.arrs (a + 4) = List.ofFn (fun i : Fin Zᶜ.card => (compactEmb Z i).val) ∧
      s'.regs 40 = x.n ∧ s'.regs 280 = 3 + 2 * (edgeListOf x.G).length ∧ s'.regs 281 = 2 * x.A.index ∧
      (∀ b, b ≤ a ∨ a + 4 < b → s'.arrs b = s.arrs b) := by
  let Q := (gm02TerminalVertices x.A).toFinset
  let Z := gm02BoundaryDeletedSet x L R
  have hw : 2 < 2 ^ w := by have hl := x.enc_length; omega
  obtain ⟨s₁, t₁, he₁, ht₁, hQ₁, hn₁, hstart₁, hcount₁, ha₁, _⟩ :=
    gm02TerminalSupportProg_exec x a (a + 1) (by dsimp only [Arr]; omega) s hsrc hn hlen
  have hleft₁ : s₁.arrs outArr = bitSetList L :=
    (ha₁ outArr (by dsimp only [Arr, outArr] at *; omega)).trans hleft
  have hright₁ : s₁.arrs 2 = bitSetList R :=
    (ha₁ 2 (by dsimp only [Arr] at *; omega)).trans hright
  obtain ⟨s₂, t₂, he₂, ht₂, hZ₂, hRank₂, hOrig₂, _, _, ha₂, hr₂⟩ := gm02NumberBoundaryProg_exec Q L R
    (a + 1) outArr 2 (a + 2) (a + 3) (a + 4)
    (by dsimp only [Arr]; omega) (by dsimp only [Arr, outArr] at *; omega)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr]; omega)
    (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega)
    s₁ hQ₁ hleft₁ hright₁ hn₁ hn hw
  refine ⟨s₂, _, Exec.seq he₁ he₂, by omega, hZ₂, hRank₂, hOrig₂, ?_, ?_, ?_, ?_⟩
  · exact (hr₂ 40 (by decide) (by decide) (by decide) (by decide)).trans hn₁
  · exact (hr₂ 280 (by decide) (by decide) (by decide) (by decide)).trans hstart₁
  · exact (hr₂ 281 (by decide) (by decide) (by decide) (by decide)).trans hcount₁
  · intro b hb
    rw [ha₂ b (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
      (by dsimp only [Arr] at *; omega), ha₁ b (by dsimp only [Arr] at *; omega)]

end GraphMinor.Compute
