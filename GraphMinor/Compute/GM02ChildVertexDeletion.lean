module

public import GraphMinor.Compute.GM02ChildVertexBits
public import GraphMinor.Compute.Algorithm94Aux

/-!
# Computing both child membership and deletion bits

First compute the corrected induced vertex set from the side and
termination arrays. Complement its bits for the compact-rank scan.
Retain both arrays: the edge filter uses membership and numbering uses
deletion. The two passes have linear total cost.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Compute corrected child membership and its deletion complement. -/
def gm02ChildVertexDeletionProg (side other support reserved fresh child deleted : Arr) : Cmd :=
  .seq (gm02ChildVertexBitsProg side other support reserved fresh child)
    (complBitSetProg child deleted 40 348)

/-- The two arrays are exactly the child set and its complement. -/
theorem gm02ChildVertexDeletionProg_exec {n w : ℕ} (S O Q Z P : Finset (Fin n))
    (side other support reserved fresh child deleted : Arr)
    (hside : side ≠ child) (hother : other ≠ child) (hsupport : support ≠ child)
    (hreserved : reserved ≠ child) (hfresh : fresh ≠ child) (hcd : child ≠ deleted) (s : State)
    (hS : s.arrs side = bitSetList S) (hO : s.arrs other = bitSetList O)
    (hQ : s.arrs support = bitSetList Q) (hZ : s.arrs reserved = bitSetList Z)
    (hP : s.arrs fresh = bitSetList P) (hn : s.regs 40 = n)
    (hnw : n < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (gm02ChildVertexDeletionProg side other support reserved fresh child deleted)
        s s' t ∧ t ≤ 12 + 46 * n ∧
      s'.arrs child = bitSetList (gm02ChildVertices S O Q Z P) ∧
      s'.arrs deleted = bitSetList (gm02ChildVertices S O Q Z P)ᶜ ∧
      s'.regs 40 = n ∧ Keeps [341, 348] [child, deleted] s s' := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hchild⟩ := gm02ChildVertexBitsProg_exec S O Q Z P
    side other support reserved fresh child hside hother hsupport hreserved hfresh s
    hS hO hQ hZ hP hn hnw hw
  have hn₁ : s₁.regs 40 = n := (hk₁.1 40 (by decide)).trans hn
  obtain ⟨s₂, t₂, he₂, ht₂, hdeleted, ha₂, hr₂⟩ :=
    complBitSetProg_exec (gm02ChildVertices S O Q Z P) child deleted 40 348 hcd (by decide)
      hw hnw (IsBitSet.of_bitSetList _ _ _ hchild) hn₁
  refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, by omega, (ha₂ child hcd).trans hchild,
    ?_, (hr₂ 40 (by decide)).trans hn₁, ?_⟩
  · simpa only [Finset.compl_eq_univ_sdiff] using hdeleted.arr_eq_bitSetList
  · constructor
    · intro r hr
      have hrs : r ≠ 341 ∧ r ≠ 348 := by simpa using hr
      exact (hr₂ r hrs.2).trans (hk₁.1 r (by simp [hrs.1]))
    · intro a ha
      have has : a ≠ child ∧ a ≠ deleted := by simpa using ha
      exact (ha₂ a has.2).trans (hk₁.2 a (by simp [has.1]))

end GraphMinor.Compute
