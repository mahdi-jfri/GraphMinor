module

public import GraphMinor.Compute.GM06Alg34VertexEdgeMark
public import GraphMinor.Compute.GM06Alg34ReadEnds

/-!
# Reading and marking one supplied vertex-graph edge

Read the next endpoint pair from the original drawing stream, then
apply its two directed adjacency marks. All source words and the vertex
count remain available, and the cursor advances by exactly two words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read one supplied endpoint pair and mark the vertex adjacency matrix. -/
def gm06VertexEdgeReadProg : Cmd := .seq gm06ReadEndsProg gm06VertexEdgeMarkProg

/-- The edge-read pass performs exactly the two marks specified by the
supplied edge, with loops skipped, in at most thirty-three steps. -/
theorem gm06VertexEdgeReadProg_exec {w off n : ℕ} (e : Fin n × Fin n) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hoff : off + 2 < 2 ^ w) {s : State}
    (hs : AtStream 0 off (e.1.val :: e.2.val :: tail) s) (hp : s.regs 103 = off)
    (hNr : s.regs 100 = n) (hcap : (s.arrs 28).length = n * n) :
    ∃ s' t, Exec w gm06VertexEdgeReadProg s s' t ∧ t ≤ 33 ∧
      s'.arrs 28 = (gm06VertexEdgeRows e).foldl (gm06MatrixMarkRow n) (s.arrs 28) ∧
      s'.regs 103 = off + 2 ∧ AtStream 0 (off + 2) tail s' ∧
      (∀ a : ℕ, a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 132 → q ≠ 133 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hA, hB, hp₁, hs₁, ha₁, hg₁⟩ :=
    gm06ReadEndsProg_exec hw hoff (e.1.isLt.trans hn) (e.2.isLt.trans hn) hs hp
  obtain ⟨s₂, t₂, hex₂, ht₂, hmat, ha₂, hg₂⟩ :=
    gm06VertexEdgeMarkProg_exec e hw hn hsquare
      ((hg₁ 100 (by decide) (by decide) (by decide)).trans hNr) hA hB
      (by rw [ha₁ 28]; exact hcap)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, ?_, (hg₂ 103).trans hp₁,
    hs₁.of_arr_eq (ha₂ 0 (by decide)), ?_, ?_⟩
  · rw [hmat, ha₁ 28]
  · intro a ha
    exact (ha₂ a ha).trans (ha₁ a)
  · intro q h103 h132 h133
    exact (hg₂ q).trans (hg₁ q h103 h132 h133)

end GraphMinor.Compute
