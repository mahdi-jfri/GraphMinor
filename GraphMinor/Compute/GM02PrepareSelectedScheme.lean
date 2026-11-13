module

public import GraphMinor.Compute.GM02GuardedSchemeDispatch
public import GraphMinor.Compute.GM02TerminalSupportProg
public import GraphMinor.Compute.GM02CompressedBoundary

/-!
# Preparing selected scheme data from the retained parent

Read and mark the original terminal support from the parent's plain
encoding. Then expand the selected valid boundary code through the
computed inverse numbering. The resulting seven arrays supply both
child builders, while the retained parent and side arrays stay intact.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Compute original support and the six fields of a selected valid scheme code. -/
noncomputable def gm02PrepareSelectedSchemeProg (N : ℕ) (parent a : Arr) (i : ℕ) : Cmd :=
  .seq (gm02TerminalSupportProg parent (a + 7))
    (gm02GuardedSchemeDispatchProg N (parent + 4) a i)

/-- All child template fields and original support are computed from retained parent data. -/
theorem gm02PrepareSelectedSchemeProg_exec {w N : ℕ} (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes)
    (parent a : Arr) (hpa : parent + 4 < a) (s : State)
    (hparent : s.arrs parent = x.enc) (hlen : x.enc.length < 2 ^ w)
    (hB : (gm02CompressedBoundaryInput x L R).n ≤ N) (hn : x.n < 2 ^ w) (hNW : N + 1 < 2 ^ w)
    (hCW : gm02BoundarySchemeCodeBound N + 1 < 2 ^ w)
    (horig : s.arrs (parent + 4) = List.ofFn
      (fun i : Fin (gm02CompressedBoundaryInput x L R).n =>
        (compactEmb (gm02BoundaryDeletedSet x L R) i).val))
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode N (gm02CompressedBoundaryInput x L R))
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound N ≤ 2 ^ w) :
    ∃ s' t, Exec w (gm02PrepareSelectedSchemeProg N parent a (gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C)) s s' t ∧
      t ≤ 82 + 28 * x.A.index + 42 * N + x.n * (61 + 28 * N) +
        4 * (gm02BoundarySchemeCodeBound N + 1) + 4 * (N + 1) ∧
      s'.arrs (a + 1) = (gm02TemplatePairIndices C.left.pairs).map (fun i => (compactEmb (gm02BoundaryDeletedSet x L R) i).val) ∧
      s'.arrs (a + 2) = bitSetList ((gm02TemplatePairIndices C.left.pairs).toFinset.image (compactEmb (gm02BoundaryDeletedSet x L R))) ∧
      s'.arrs (a + 3) = (gm02TemplatePairIndices C.right.pairs).map (fun i => (compactEmb (gm02BoundaryDeletedSet x L R) i).val) ∧
      s'.arrs (a + 4) = bitSetList ((gm02TemplatePairIndices C.right.pairs).toFinset.image (compactEmb (gm02BoundaryDeletedSet x L R))) ∧
      s'.arrs (a + 5) = bitSetList (C.reservedLeft.toFinset.image (compactEmb (gm02BoundaryDeletedSet x L R))) ∧
      s'.arrs (a + 6) = bitSetList (C.reservedRight.toFinset.image (compactEmb (gm02BoundaryDeletedSet x L R))) ∧
      s'.arrs (a + 7) = bitSetList x.A.support.toFinset ∧
      s'.regs 40 = x.n ∧
      s'.regs 330 = gm02BoundarySchemeSetCode N (gm02CompressedBoundaryInput x L R) ∧
      (∀ j, j < a ∨ a + 7 < j → s'.arrs j = s.arrs j) ∧
      (∀ r : Reg, 1000 ≤ r → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hQ₁, hn₁, _, _, ha₁, hr₁⟩ :=
    gm02TerminalSupportProg_exec x parent (a + 7) (by dsimp only [Arr] at *; omega)
      s hparent hn hlen
  have ho₁ := (ha₁ (parent + 4) (by dsimp only [Arr] at *; omega)).trans horig
  have hc₁ := (hr₁ 330 (by decide) (by decide) (by decide) (by decide)).trans hcat
  obtain ⟨s₂, t₂, he₂, ht₂, hL, hLS, hR, hRS, hZ, hZ', hk₂⟩ :=
    gm02GuardedSchemeDispatchProg_exec (gm02CompressedBoundaryInput x L R) C
      (compactEmb (gm02BoundaryDeletedSet x L R)) (parent + 4) a hpa s₁
      hB hn hNW hCW ho₁ hn₁ hc₁ hcodes
  refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, ?_, hL, hLS, hR, hRS, hZ, hZ', ?_, ?_, ?_, ?_, ?_⟩
  · have heq : x.n * (61 + 28 * N) = x.n + x.n * (60 + 28 * N) := by ring
    rw [heq]
    omega
  · rw [hk₂.2 (a + 7) (by simp), hQ₁,
      gm02TerminalVertices_eq_support_toFinset]
  · exact (hk₂.1 40 (by decide)).trans hn₁
  · exact (hk₂.1 330 (by decide)).trans hc₁
  · intro j hj
    rw [hk₂.2 j (by simp; dsimp only [Arr] at *; omega)]
    exact ha₁ j (by dsimp only [Arr] at *; omega)
  · intro r hr
    have hk := hk₂.1 r (by simp; dsimp only [Reg] at *; omega)
    exact hk.trans (hr₁ r (by dsimp only [Reg] at *; omega) (by dsimp only [Reg] at *; omega)
      (by dsimp only [Reg] at *; omega) (by dsimp only [Reg] at *; omega))

end GraphMinor.Compute
