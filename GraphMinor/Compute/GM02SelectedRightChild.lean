module

public import GraphMinor.Compute.GM02SelectedLeftChild

import GraphMinor.Compute.GM02RecursiveWorkFrames

/-!
# Constructing the selected right recursive call from parent data

Expand a valid catalogue code and read the original support from the
retained plain parent encoding. Interpret the emitted fields as its
canonical crossing scheme, then construct that scheme's exact right
child input. The parent input, side arrays, and catalogue are retained.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02 GraphMinor.Compute.Crossing TwoPaths

/-- A valid selected code produces its exact right recursive input with uniform overhead. -/
theorem gm02SelectedChildProg_right_exec {w N : ℕ} (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes)
    (parent a : Arr) (hp : 17 < parent) (hpa : parent + 4 < a) (s : State)
    (hparent : s.arrs parent = x.enc) (hlen : x.enc.length < 2 ^ w)
    (hL : s.arrs 1 = bitSetList L) (hR : s.arrs 2 = bitSetList R)
    (hB : (gm02CompressedBoundaryInput x L R).n ≤ N) (hn : x.n < 2 ^ w)
    (hNW : N + 1 < 2 ^ w) (hCW : gm02BoundarySchemeCodeBound N + 1 < 2 ^ w)
    (horig : s.arrs (parent + 4) = List.ofFn
      (fun i : Fin (gm02CompressedBoundaryInput x L R).n =>
        (compactEmb (gm02BoundaryDeletedSet x L R) i).val))
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode N (gm02CompressedBoundaryInput x L R))
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound N ≤ 2 ^ w)
    (hchild : 8 + 2 * (edgeListOf x.G).length + 2 * C.right.index < 2 ^ w) :
    ∃ s' t, Exec w (gm02SelectedChildProg true N parent a
        (gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C)) s s' t ∧
      t ≤ 266 + 28 * x.A.index + 73 * N + x.n * (143 + 28 * N) +
        166 * (edgeListOf x.G).length +
        4 * (gm02BoundarySchemeCodeBound N + 1) + 4 * (N + 1) ∧
      s'.arrs (a + 14) =
        (gm02CanonicalRightInput x.G L R x.A (gm02CanonicalBoundaryScheme x L R C)).enc ∧
      s'.arrs 1 = bitSetList L ∧ s'.arrs 2 = bitSetList R ∧
      s'.regs 40 = x.n ∧
      s'.regs 330 = gm02BoundarySchemeSetCode N (gm02CompressedBoundaryInput x L R) ∧
      (∀ j, 17 < j → j < a ∨ a + 14 < j → s'.arrs j = s.arrs j) ∧
      (∀ r : Reg, 1000 ≤ r → s'.regs r = s.regs r) := by
  let D := gm02CanonicalBoundaryScheme x L R C
  obtain ⟨s₁, t₁, he₁, ht₁, _, _, hW₁, hS₁, _, hZ₁, hQ₁, hn₁, hc₁, ha₁, hhigh₁⟩ :=
    gm02PrepareSelectedSchemeProg_exec x L R C parent a hpa s hparent hlen hB hn hNW hCW
      horig hcat hcodes
  have hparent₁ : s₁.arrs parent = encGraph x.G ++
      ([x.A.index] ++ flatEdges (edgeListOf x.A.pairGraph)) := by
    simpa only [GM02SimpleTerminatedInput.enc, List.append_assoc] using
      (ha₁ parent (Or.inl (by dsimp only [Arr] at *; omega))).trans hparent
  have hL₁ := (ha₁ 1 (Or.inl (by dsimp only [Arr] at *; omega))).trans hL
  have hR₁ := (ha₁ 2 (Or.inl (by dsimp only [Arr] at *; omega))).trans hR
  have hW : s₁.arrs (a + 3) = flatEdges (edgeListOf D.right.pairGraph) :=
    hW₁.trans (gm02ExpandedTemplate_right_words x L R _ _ rfl rfl C)
  have hS : s₁.arrs (a + 4) = bitSetList D.right.support.toFinset :=
    hS₁.trans (congrArg bitSetList (gm02ExpandedTemplate_right_support x L R _ _ rfl rfl C))
  have hZ : s₁.arrs (a + 6) = bitSetList D.reservedRight.toFinset :=
    hZ₁.trans (congrArg bitSetList (gm02ExpandedTemplate_reservedRight x L R _ _ rfl rfl C))
  have hchildD : 8 + 2 * (edgeListOf x.G).length + 2 * D.right.index < 2 ^ w := by
    rw [gm02CanonicalBoundaryScheme_right_index]
    exact hchild
  obtain ⟨s₂, t₂, he₂, ht₂, hout, ha₂⟩ := gm02BuildCanonicalChildProg_right_exec x.G L R x.A D
    parent a ⟨hp, by dsimp only [Arr] at *; omega⟩ _ s₁ hparent₁ hL₁ hR₁ hQ₁ hZ hS hW hn₁ hn hchildD
  have hidx : 2 * C.right.index ≤ N := by
    have h := gm02TemplatePairIndices_length_le C.right
    rw [gm02TemplatePairIndices_length] at h
    exact h.trans hB
  dsimp only [D] at ht₂
  rw [gm02CanonicalBoundaryScheme_right_index] at ht₂
  have hctrl := gm02BuildChildFromTemplateProg_control_not_written true parent
    (a + 7) (a + 6) (a + 4) (a + 3) (a + 10)
  refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, ?_, hout, ?_, ?_,
    (he₂.regs_eq_of_not_mem_writtenRegs hctrl.1).trans hn₁,
    (he₂.regs_eq_of_not_mem_writtenRegs hctrl.2.1).trans hc₁, ?_, ?_⟩
  · have heq : x.n * (143 + 28 * N) = 82 * x.n + x.n * (61 + 28 * N) := by ring
    rw [heq]
    omega
  · exact (ha₂ 1 (by simp)).trans hL₁
  · exact (ha₂ 2 (by simp)).trans hR₁
  · intro j hj hja
    rw [ha₂ j (by simp; dsimp only [Arr] at *; omega)]
    exact ha₁ j (by dsimp only [Arr] at *; omega)
  · intro r hr
    exact (gm02_regs_eq_of_low_writes he₂
      (gm02BuildChildFromTemplateProg_writtenRegs_subset true parent
        (a + 7) (a + 6) (a + 4) (a + 3) (a + 10)) r hr).trans (hhigh₁ r hr)

end GraphMinor.Compute
