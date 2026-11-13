module

public import GraphMinor.Compute.GM06Alg34BlockTest

/-!
# Reading a length-prefixed block and checking its component

The length is part of the supplied array. Read it and pass the exact
label stream to the block test. The resulting cursor points to the
next length-prefixed block, including when the current block is empty.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read a block length and test that block against graph components. -/
def gm06ReadBlockTestProg : Cmd :=
  .seq (readStreamWordProg 0 103 108) gm06BlockTestProg

/-- The complete block reader computes the split-block complement from
its length-prefixed input and preserves the adjacency arrays. -/
theorem gm06ReadBlockTestProg_exec {w off : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (tail : List ℕ) (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hsquare : x.n * x.n < 2 ^ w) (hend : off + 1 + L.length < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.n)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n)
    (hs : AtStream 0 off (GM06DrawingData.listWords (L.map Fin.val) ++ tail) s)
    (hp : s.regs 103 = off) :
    ∃ s' t, Exec w gm06ReadBlockTestProg s s' t ∧
      t ≤ 26 * (x.n * x.n) + 23 * x.n + 22 * L.length + 54 ∧
      s'.regs 112 = (if !x.isSplitBlock L then 1 else 0) ∧
      s'.regs 103 = off + 1 + L.length ∧ AtStream 0 (off + 1 + L.length) tail s' ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 112 → q ≠ 187 →
        s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hc₁, hp₁, hs₁, ha₁, hg₁⟩ :=
    readStreamWordProg_exec (x := L.length) (a_src := 0) 103 108 (by decide) hw (by omega) (by omega)
      (by simpa only [GM06DrawingData.listWords, List.length_map, List.cons_append] using hs) hp
  obtain ⟨s₂, t₂, hex₂, ht₂, hans₂, hp₂, hs₂, ha₂, hg₂⟩ :=
    gm06BlockTestProg_exec x L tail hw hn hsquare hend
      ((hg₁ 4 (by decide) (by decide)).trans hsize)
      (hlists.of_arrs_eq (ha₁ 30) (ha₁ 31) (ha₁ 32))
      (by simpa only [ha₁] using hlen) hs₁ hp₁ hc₁
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hans₂, hp₂, hs₂, ?_, ?_⟩
  · intro A h33 h34
    exact (ha₂ A h33 h34).trans (ha₁ A)
  · intro q hq h103 h108 h109 h112 h187
    exact (hg₂ q hq h103 h108 h109 h112 h187).trans (hg₁ q h103 h108)

end GraphMinor.Compute
