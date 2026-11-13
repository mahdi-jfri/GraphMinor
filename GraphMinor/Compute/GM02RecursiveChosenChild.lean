module

public import GraphMinor.Compute.GM02SelectedRightChild
public import GraphMinor.Compute.GM02RecursiveMemory

/-!
# The selected side of a recursive crossing scheme

Use the side tag to choose the left or right canonical compact input.
The same tag selects the proved child-construction command, so both
calls share one execution statement with their exact plain encoding.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- The exact plain input selected by a recursive call's side tag. -/
noncomputable def gm02RecursiveChosenInput (right : Bool) (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes) :
    GM02SimpleTerminatedInput :=
  if right then gm02CanonicalRightInput x.G L R x.A (gm02CanonicalBoundaryScheme x L R C)
  else gm02CanonicalLeftInput x.G L R x.A (gm02CanonicalBoundaryScheme x L R C)

/-- The selected child builder writes precisely the input chosen by its side tag. -/
theorem gm02RecursiveSelectedChild_exec {w : ℕ} (right : Bool) (q : ℕ)
    (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n))
    (C : (gm02CompressedBoundaryInput x L R).schemes) (s : State)
    (hparent : s.arrs (gm02RecursiveParentArr q) = x.enc) (hlen : x.enc.length < 2 ^ w)
    (hL : s.arrs 1 = bitSetList L) (hR : s.arrs 2 = bitSetList R)
    (hB : (gm02CompressedBoundaryInput x L R).n ≤ gm02RecursiveBoundaryBound q)
    (hn : x.n < 2 ^ w) (hNW : gm02RecursiveBoundaryBound q + 1 < 2 ^ w)
    (hCW : gm02RecursiveCodeBound q + 1 < 2 ^ w)
    (horig : s.arrs (gm02RecursiveParentArr q + 4) = List.ofFn
      (fun i : Fin (gm02CompressedBoundaryInput x L R).n =>
        (compactEmb (gm02BoundaryDeletedSet x L R) i).val))
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q)
      (gm02CompressedBoundaryInput x L R))
    (hcodes : 2 ^ gm02RecursiveCodeBound q ≤ 2 ^ w)
    (hchild : 8 + 2 * (edgeListOf x.G).length +
      2 * (if right then C.right.index else C.left.index) < 2 ^ w) :
    ∃ s' t, Exec w (gm02SelectedChildProg right (gm02RecursiveBoundaryBound q)
        (gm02RecursiveParentArr q) (gm02RecursiveTemplateArr q)
        (gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C)) s s' t ∧
      t ≤ 266 + 28 * x.A.index + 73 * gm02RecursiveBoundaryBound q +
        x.n * (143 + 28 * gm02RecursiveBoundaryBound q) + 166 * (edgeListOf x.G).length +
        4 * (gm02RecursiveCodeBound q + 1) + 4 * (gm02RecursiveBoundaryBound q + 1) ∧
      s'.arrs (gm02RecursiveTemplateArr q + 14) = (gm02RecursiveChosenInput right x L R C).enc ∧
      s'.arrs 1 = bitSetList L ∧ s'.arrs 2 = bitSetList R ∧
      s'.regs 40 = x.n ∧
      s'.regs 330 = gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q)
        (gm02CompressedBoundaryInput x L R) ∧
      (∀ j, 17 < j → j < gm02RecursiveTemplateArr q ∨ gm02RecursiveTemplateArr q + 14 < j →
        s'.arrs j = s.arrs j) ∧ (∀ r : Reg, 1000 ≤ r → s'.regs r = s.regs r) := by
  have hpg := gm02RecursiveParentArr_ge q
  have hp : 17 < gm02RecursiveParentArr q := by dsimp only [Arr] at *; omega
  have hpa : gm02RecursiveParentArr q + 4 < gm02RecursiveTemplateArr q := by
    dsimp only [gm02RecursiveTemplateArr, Arr]; omega
  cases right with
  | false =>
    exact gm02SelectedChildProg_left_exec x L R C _ _ hp hpa s hparent hlen hL hR
      hB hn hNW hCW horig hcat hcodes hchild
  | true =>
    exact gm02SelectedChildProg_right_exec x L R C _ _ hp hpa s hparent hlen hL hR
      hB hn hNW hCW horig hcat hcodes hchild

end GraphMinor.Compute
