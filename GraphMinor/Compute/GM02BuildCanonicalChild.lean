module

public import GraphMinor.Compute.GM02BuildChildFromTemplate
public import GraphMinor.Compute.GM02CanonicalChildInputs

/-!
# Executable construction of both canonical recursive inputs

Use the selected template's matching, support, and reserved arrays in
the corrected child builder. The first and second fixed branches write
exactly their semantic canonical child inputs. All parent and template
arrays are preserved for subsequent recursive work.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Select the appropriate template fields and build the chosen canonical child. -/
def gm02BuildCanonicalChildProg (right : Bool) (parent b : Arr) : Cmd :=
  gm02BuildChildFromTemplateProg right parent (b + 7)
    (if right then b + 6 else b + 5) (if right then b + 4 else b + 2)
    (if right then b + 3 else b + 1) (b + 10)

variable {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
  (L R : Finset (Fin n)) (A : Termination V(Graph.ofSimpleGraph F))
  (C : CrossingScheme (Graph.ofSimpleGraph F)
    ((Graph.ofSimpleGraph F).induce (L : Set (Fin n)))
    (((Graph.ofSimpleGraph F).induce (R : Set (Fin n))).deleteEdges
      E((Graph.ofSimpleGraph F).induce (L : Set (Fin n)))) A)

/-- The left executable branch writes the exact semantic canonical child input. -/
theorem gm02BuildCanonicalChildProg_left_exec {w : ℕ} (parent b : Arr)
    (hp : 17 < parent ∧ parent < b) (rest : List ℕ) (s : State)
    (hparent : s.arrs parent = encGraph F ++ rest)
    (hL : s.arrs 1 = bitSetList L) (hR : s.arrs 2 = bitSetList R)
    (hQ : s.arrs (b + 7) = bitSetList A.support.toFinset)
    (hZ : s.arrs (b + 5) = bitSetList C.reservedLeft.toFinset)
    (hP : s.arrs (b + 2) = bitSetList C.left.support.toFinset)
    (hPairs : s.arrs (b + 1) = flatEdges (edgeListOf C.left.pairGraph))
    (hcount : s.regs 40 = n) (hn : n < 2 ^ w)
    (hlen : 8 + 2 * (edgeListOf F).length + 2 * C.left.index < 2 ^ w) :
    ∃ s' t, Exec w (gm02BuildCanonicalChildProg false parent b) s s' t ∧
      t ≤ 82 * n + 166 * (edgeListOf F).length + 62 * C.left.index + 184 ∧
      s'.arrs (b + 14) = (gm02CanonicalLeftInput F L R A C).enc ∧
      (∀ j, j ∉ [0, 13, 14, 17, b + 10, b + 11, b + 12, b + 13, b + 14] →
        s'.arrs j = s.arrs j) := by
  obtain ⟨s', t, he, ht, hout, ha⟩ := gm02BuildChildFromTemplateProg_exec F false L R
    A.support.toFinset C.reservedLeft.toFinset C.left.support.toFinset
    (C.left.rebase (gm02CanonicalChild_left_support F L R A C))
    parent (b + 7) (b + 5) (b + 2) (b + 1) (b + 10)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
    (by dsimp only [Arr] at *; omega) rest s hparent hL hR hQ hZ hP hPairs hcount hn hlen
  refine ⟨s', t, he, ht, ?_, ?_⟩
  · exact hout
  · intro j hj
    apply ha j
    simpa only [Nat.add_assoc] using hj

/-- The right executable branch writes the exact semantic canonical child input. -/
theorem gm02BuildCanonicalChildProg_right_exec {w : ℕ} (parent b : Arr)
    (hp : 17 < parent ∧ parent < b) (rest : List ℕ) (s : State)
    (hparent : s.arrs parent = encGraph F ++ rest)
    (hL : s.arrs 1 = bitSetList L) (hR : s.arrs 2 = bitSetList R)
    (hQ : s.arrs (b + 7) = bitSetList A.support.toFinset)
    (hZ : s.arrs (b + 6) = bitSetList C.reservedRight.toFinset)
    (hP : s.arrs (b + 4) = bitSetList C.right.support.toFinset)
    (hPairs : s.arrs (b + 3) = flatEdges (edgeListOf C.right.pairGraph))
    (hcount : s.regs 40 = n) (hn : n < 2 ^ w)
    (hlen : 8 + 2 * (edgeListOf F).length + 2 * C.right.index < 2 ^ w) :
    ∃ s' t, Exec w (gm02BuildCanonicalChildProg true parent b) s s' t ∧
      t ≤ 82 * n + 166 * (edgeListOf F).length + 62 * C.right.index + 184 ∧
      s'.arrs (b + 14) = (gm02CanonicalRightInput F L R A C).enc ∧
      (∀ j, j ∉ [0, 13, 14, 17, b + 10, b + 11, b + 12, b + 13, b + 14] →
        s'.arrs j = s.arrs j) := by
  obtain ⟨s', t, he, ht, hout, ha⟩ := gm02BuildChildFromTemplateProg_exec F true L R
    A.support.toFinset C.reservedRight.toFinset C.right.support.toFinset
    (C.right.rebase (gm02CanonicalChild_right_support F L R A C))
    parent (b + 7) (b + 6) (b + 4) (b + 3) (b + 10)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
    (by dsimp only [Arr] at *; omega) rest s hparent hL hR hQ hZ hP hPairs hcount hn hlen
  refine ⟨s', t, he, ht, ?_, ?_⟩
  · exact hout
  · intro j hj
    apply ha j
    simpa only [Nat.add_assoc] using hj

end GraphMinor.Compute
