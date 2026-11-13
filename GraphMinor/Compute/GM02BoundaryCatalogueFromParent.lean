module

public import GraphMinor.Compute.GM02PrepareBoundaryData
public import GraphMinor.Compute.GM02PackBoundaryInput
public import GraphMinor.Compute.GM02BoundaryCatalogue

import GraphMinor.Compute.GM02RecursiveWorkFrames

/-!
# Computing all boundary scheme codes from the retained parent input

Prepare and pack the finite boundary data, then run its fixed catalogue
lookup. The whole routine starts from the original terminated graph and
actual separator side arrays. It returns precisely the valid scheme
codes on the compressed boundary and keeps the inverse names for
expanding each selected pattern into the original graph.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Construct the finite boundary input and its complete scheme catalogue.
Register 330 holds the catalogue and 331 is lookup scratch. -/
noncomputable def gm02BoundaryCatalogueFromParentProg (N : ℕ) (a : Arr) : Cmd :=
  .seq (gm02PrepareBoundaryDataProg a)
    (.seq (gm02PackBoundaryInputProg a) (gm02BoundaryCatalogueProg N (a + 12) 330 331))

/-- The actual parent-to-catalogue program computes all valid scheme codes,
with linear parent-size cost plus a fixed-boundary constant. -/
theorem gm02BoundaryCatalogueFromParentProg_exec {w N : ℕ} (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (a : Arr) (ha : 3 ≤ a) (s : State)
    (hsrc : s.arrs a = x.enc) (hleft : s.arrs outArr = bitSetList L) (hright : s.arrs 2 = bitSetList R)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w)
    (hboundary : (gm02CompressedBoundaryInput x L R).n ≤ N)
    (hwords : N * N + N + 2 < 2 ^ w) (hdepth : 3 + 3 * N < 2 ^ w)
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound N ≤ 2 ^ w) :
    let Z := gm02BoundaryDeletedSet x L R
    let B := gm02CompressedBoundaryInput x L R
    ∃ s' t, Exec w (gm02BoundaryCatalogueFromParentProg N a) s s' t ∧
      t ≤ 150 * x.n + 200 * x.A.index + 350 +
        (4 + 3 * N) * (4 * (N * N + N + 1) + 10) ∧
      s'.regs 330 = gm02BoundarySchemeSetCode N B ∧ s'.arrs (a + 12) = B.enc ∧
      s'.arrs (a + 4) = List.ofFn (fun i : Fin B.n => (compactEmb Z i).val) ∧
      (∀ b, b ≤ a ∨ a + 12 < b → s'.arrs b = s.arrs b) ∧
      (∀ r : Reg, 1000 ≤ r → s'.regs r = s.regs r) := by
  let Z := gm02BoundaryDeletedSet x L R
  let B := gm02CompressedBoundaryInput x L R
  have hBlen : B.enc.length < 2 ^ w := (B.enc_length_le hboundary).trans_lt hdepth
  have hBsize : B.n ≤ x.n := gm02CompressedBoundaryInput_size_le x L R
  have hBindex : B.A.index = x.A.index := gm02CompressedBoundaryInput_index x L R
  obtain ⟨s₁, t₁, he₁, ht₁, hOrig₁, hPairs₁, hLeft₁, hRight₁, ha₁⟩ :=
    gm02PrepareBoundaryDataProg_exec x L R a ha s hsrc hleft hright hn hlen
  obtain ⟨s₂, t₂, he₂, ht₂, hEnc₂, ha₂⟩ := gm02PackBoundaryInputProg_exec B a s₁
    (by rw [hOrig₁, List.length_ofFn]) hPairs₁ hLeft₁ hRight₁ hBlen
  obtain ⟨s₃, t₃, he₃, ht₃, hCode₃, hr₃, ha₃⟩ := gm02BoundaryCatalogueProg_exec
    (N := N) (a + 12) 330 331 B hboundary [] s₂ (by simpa only [List.append_nil] using hEnc₂)
    hwords hdepth hcodes
  refine ⟨s₃, _, Exec.seq he₁ (Exec.seq he₂ he₃), ?_, hCode₃, ?_, ?_, ?_, ?_⟩
  · rw [hBindex] at ht₂
    omega
  · exact (congrFun ha₃ _).trans hEnc₂
  · exact (congrFun ha₃ _).trans
      ((ha₂ (a + 4) (Or.inl (by dsimp only [Arr]; omega))).trans hOrig₁)
  · intro b hb
    rw [congrFun ha₃ b, ha₂ b (by dsimp only [Arr] at *; omega)]
    exact ha₁ b (by dsimp only [Arr] at *; omega)
  · intro r hr
    exact (hr₃ r (by dsimp only [Reg] at *; omega) (by dsimp only [Reg] at *; omega)).trans
      ((gm02_regs_eq_of_low_writes he₂ (gm02PackBoundaryInputProg_writtenRegs_subset a) r hr).trans
        (gm02_regs_eq_of_low_writes he₁ (gm02PrepareBoundaryDataProg_writtenRegs_subset a) r hr))

end GraphMinor.Compute
