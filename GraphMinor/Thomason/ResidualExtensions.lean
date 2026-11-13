module

public import GraphMinor.Thomason.ResidualFamilies
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Counting extensions with a prescribed uncovered bound

Thomason's Lemma 5, page 263 (1984), counts subsets by inserting a vertex
which covers half of the vertices still uncovered. We count the possible
insertions and then count the same inclusions from their larger endpoint.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each selected set has at least `M-k` extensions when the missing-pair
budget provides at least `M` partial dominating vertices. This is the
insertion count underlying Thomason's Lemma 5, p. 263. -/
theorem card_residualBounded_extensions (M D : ℕ) (hM : M ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    {k t h : ℕ} (hcount : t * D < (Fintype.card V + 1 - M) * (h + 1))
    {Y : Finset V} (hY : Y ∈ residualBoundedSets G k t) :
    M - k ≤ ((residualBoundedSets G (k + 1) h).filter (Y ⊆ ·)).card := by
  let C := verticesLeavingAtMost G (undominatedVertices G Y) h \ Y
  have hcardY := ((mem_residualBoundedSets_iff G k t Y).mp hY).1
  have hbound := ((mem_residualBoundedSets_iff G k t Y).mp hY).2
  have hlarge := card_verticesLeavingAtMost G (undominatedVertices G Y) h D M hdegree hM
    ((Nat.mul_le_mul_right D hbound).trans_lt hcount)
  have hC : M - k ≤ C.card := by
    have hsplit := card_sdiff_add_card_inter
      (verticesLeavingAtMost G (undominatedVertices G Y) h) Y
    have hsmall := card_le_card (inter_subset_right :
      verticesLeavingAtMost G (undominatedVertices G Y) h ∩ Y ⊆ Y)
    dsimp only [C]
    omega
  have hinj : Set.InjOn (fun v => insert v Y) (↑C : Set V) := by
    intro v hv w hw heq
    dsimp only at heq
    have hvY := (mem_sdiff.mp hv).2
    have hmem : v ∈ insert w Y := by
      rw [← heq]
      exact mem_insert_self v Y
    exact (mem_insert.mp hmem).resolve_right hvY
  have hsub : C.image (fun v => insert v Y) ⊆
      (residualBoundedSets G (k + 1) h).filter (Y ⊆ ·) := by
    intro Z hZ
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hZ
    obtain ⟨hgood, hvY⟩ := mem_sdiff.mp hv
    exact mem_filter.mpr ⟨insert_mem_residualBoundedSets G hY hvY hgood,
      subset_insert v Y⟩
  calc
    M - k ≤ C.card := hC
    _ = (C.image (fun v => insert v Y)).card := (card_image_of_injOn hinj).symm
    _ ≤ _ := card_le_card hsub


end GraphMinor.Thomason
