module

public import GraphMinor.Compute.GM02PrepareBoundaryNumbering
public import GraphMinor.Compute.GM02CompactPairWords

/-!
# Constructing all compact boundary data

Parse and number the boundary, rewrite the original terminal endpoints
by its ranks, and pull back the two side-bit arrays through its inverse
names. The resulting arrays contain exactly the pair words and side
flags of the compressed boundary instance. The retained parent graph
and original side arrays are preserved for constructing recursive children.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Prepare all finite boundary data in work arrays after `a`. -/
def gm02PrepareBoundaryDataProg (a : Arr) : Cmd :=
  .seq (gm02PrepareBoundaryNumberingProg a)
    (.seq (gm02CompactPairWordsProg a (a + 6) (a + 3) (a + 5))
      (.seq (gm02PullbackBitsProg outArr (a + 4) (a + 7)) (gm02PullbackBitsProg 2 (a + 4) (a + 8))))

/-- All compact boundary data are computed from the parent input and
separator arrays in linear vertex-and-terminal time. -/
theorem gm02PrepareBoundaryDataProg_exec {w : ℕ} (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (a : Arr) (ha : 3 ≤ a) (s : State)
    (hsrc : s.arrs a = x.enc) (hleft : s.arrs outArr = bitSetList L) (hright : s.arrs 2 = bitSetList R)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    let Z := gm02BoundaryDeletedSet x L R
    let B := gm02CompressedBoundaryInput x L R
    ∃ s' t, Exec w (gm02PrepareBoundaryDataProg a) s s' t ∧
      t ≤ 100 * x.n + 100 * x.A.index + 150 ∧
      s'.arrs (a + 4) = List.ofFn (fun i : Fin B.n => (compactEmb Z i).val) ∧
      s'.arrs (a + 5) = flatEdges (edgeListOf B.A.pairGraph) ∧
      s'.arrs (a + 7) = bitSetList B.left ∧ s'.arrs (a + 8) = bitSetList B.right ∧
      (∀ b, b ≤ a ∨ a + 8 < b → s'.arrs b = s.arrs b) := by
  let Z := gm02BoundaryDeletedSet x L R
  let B := gm02CompressedBoundaryInput x L R
  have hw : 1 < 2 ^ w := by have hl := x.enc_length; omega
  have hbsize : Zᶜ.card ≤ x.n := by simpa only [Fintype.card_fin] using Finset.card_le_univ Zᶜ
  obtain ⟨s₁, t₁, he₁, ht₁, _, hRank₁, hOrig₁, _, hstart₁, hcount₁, ha₁⟩ :=
    gm02PrepareBoundaryNumberingProg_exec x L R a ha s hsrc hleft hright hn hlen
  have hsrc₁ : s₁.arrs a = x.enc := (ha₁ a (Or.inl le_rfl)).trans hsrc
  obtain ⟨s₂, t₂, he₂, ht₂, hPairs₂, ha₂, _⟩ := gm02CompactPairWordsProg_exec x Z
    (gm02Boundary_support_survives x L R) a (a + 6) (a + 3) (a + 5)
    (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega)
    (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega)
    s₁ hsrc₁ hRank₁ hstart₁ hcount₁ hn hlen
  have hOrig₂ : s₂.arrs (a + 4) = List.ofFn (fun i : Fin Zᶜ.card => (compactEmb Z i).val) :=
    (ha₂ (a + 4) (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega)).trans hOrig₁
  have hleft₂ : s₂.arrs outArr = bitSetList L := by
    rw [ha₂ outArr (by dsimp only [Arr, outArr] at *; omega) (by dsimp only [Arr, outArr] at *; omega),
      ha₁ outArr (Or.inl (by dsimp only [Arr, outArr] at *; omega))]
    exact hleft
  have hright₂ : s₂.arrs 2 = bitSetList R := by
    rw [ha₂ 2 (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega),
      ha₁ 2 (Or.inl (by dsimp only [Arr] at *; omega))]
    exact hright
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hLeft₃⟩ := gm02PullbackBitsProg_exec (compactEmb Z) L
    outArr (a + 4) (a + 7) (by dsimp only [Arr, outArr] at *; omega) (by dsimp only [Arr]; omega)
    s₂ hleft₂ hOrig₂ hn (hbsize.trans_lt hn) hw
  have hOrig₃ : s₃.arrs (a + 4) = List.ofFn (fun i : Fin Zᶜ.card => (compactEmb Z i).val) :=
    (hk₃.2 _ (by simp only [List.mem_singleton]; dsimp only [Arr]; omega)).trans hOrig₂
  have hright₃ : s₃.arrs 2 = bitSetList R :=
    (hk₃.2 _ (by simp only [List.mem_singleton]; dsimp only [Arr] at *; omega)).trans hright₂
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hRight₄⟩ := gm02PullbackBitsProg_exec (compactEmb Z) R
    2 (a + 4) (a + 8) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr]; omega)
    s₃ hright₃ hOrig₃ hn (hbsize.trans_lt hn) hw
  refine ⟨s₄, _, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), by omega, ?_, ?_, ?_, hRight₄, ?_⟩
  · exact (hk₄.2 _ (by simp only [List.mem_singleton]; dsimp only [Arr]; omega)).trans hOrig₃
  · rw [hk₄.2 (a + 5) (by simp only [List.mem_singleton]; dsimp only [Arr]; omega),
      hk₃.2 (a + 5) (by simp only [List.mem_singleton]; dsimp only [Arr]; omega)]
    exact hPairs₂
  · exact (hk₄.2 _ (by simp only [List.mem_singleton]; dsimp only [Arr]; omega)).trans hLeft₃
  · intro b hb
    rw [hk₄.2 b (by simp only [List.mem_singleton]; dsimp only [Arr] at *; omega),
      hk₃.2 b (by simp only [List.mem_singleton]; dsimp only [Arr] at *; omega),
      ha₂ b (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)]
    exact ha₁ b (by dsimp only [Arr] at *; omega)

end GraphMinor.Compute
