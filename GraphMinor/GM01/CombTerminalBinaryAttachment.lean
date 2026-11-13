module

public import GraphMinor.GM01.CombSegmentModels
public import GraphMinor.GM01.BinaryCombModel
import GraphMinor.GM01.CombShiftRanges
import GraphMinor.GM01.SelectedBoundaryPath
import GraphMinor.GM01.RootedModelComposition

/-!
# The binary arm in the second end

Graph Minors I, (4.12), page 59, retains the second end as the binary
arm of the forbidden fork. Its two cells contain the required binary
tree, rooted at the first spine centre of that end. The preceding
spine edge supplies a replacing path from the other cells, and this
path meets the second end only at its root.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The actual binary arm and its boundary attachment in GM01 (4.12),
page 59. The starting vertex belongs to the complement of the second end. -/
theorem terminal_binary_arm_attachment {α β : Type*} {γ L : ℕ}
    (hL : 3 ≤ L) {D : Graph α β}
    (c : (pathComb γ L).verts → α) (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f)) :
    let B := rootedCombSegment (by omega : 0 < 2) D c P (L - 2) (by omega : L - 2 + 2 ≤ L)
    B.graph ≤ D ∧ HasRootedMinor (binaryRootedTree γ) B ∧
      ∃ a ∈ V(D) \ combSecondEndSupport (by omega) c P,
        ∃ Q : Graph α β, IsGraphPathWithEnds D Q a B.root.val ∧
          V(Q) ∩ combSecondEndSupport (by omega) c P = {B.root.val} := by
  let k := L - 2
  have hbound : k + 2 ≤ L := by dsimp [k]; omega
  have hk : 0 < k := by dsimp [k]; omega
  let f := combShiftEmbedding (γ := γ) k hbound
  let hf := fun {a b} (h : (pathComb γ 2).coe.Adj a b) ↦ combShiftEmbedding_adj k hbound h
  let r := (rootedPathComb γ 2 (by omega)).root
  let a : (pathComb γ L).verts := ⟨Sum.inl ⟨k - 1, by dsimp [k]; omega⟩, pathComb_spine_mem γ L _⟩
  have hadj : (pathComb γ L).coe.Adj a (f r) := by
    apply pathComb_spine_adj (γ := γ)
    apply pathGraph_adj.mpr
    exact Or.inl (by change k - 1 + 1 = k + 0; omega)
  let e : (pathComb γ L).coe.edgeSet := ⟨s(a,f r), hadj⟩
  obtain ⟨u, v, he, hP, _⟩ := hPaths e
  have hPair : s(a,f r) = s(u,v) := he
  have hBoundary : IsGraphPathWithEnds D (P e) (c a) (c (f r)) := by
    rcases Sym2.eq_iff.mp hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hP
    · exact hP.symm
  have haOutside : a ∉ range f := by
    intro ha
    have h := (mem_range_combShiftEmbedding_iff k hbound a).mp ha
    change k ≤ k - 1 ∧ k - 1 < k + 2 at h
    omega
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hMeet : V(P e) ∩ combSecondEndSupport (by omega) c P = {c (f r)} :=
    selected_subdivision_boundary_intersection f hf hc P hRanges
      (fun e f hne ↦ (hInter e f hne).1) r a haOutside e rfl
  have hcentres : ∀ v, c v ∈ V(D) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hSegment := combSegment_model (by omega : 0 < 2) c hc hcentres P hPaths hInter k hbound
  obtain ⟨M, _⟩ := hSegment.2.2
  have hdis := disjoint_combSegmentSupports hc P hRanges (fun e f hne ↦ (hInter e f hne).1)
    0 k (by dsimp [k]; omega : 0 + k ≤ L) hbound (by omega)
  have haFirst : c a ∈ combSegmentSupport c P 0 (by dsimp [k]; omega : 0 + k ≤ L) := by
    apply (mem_combSegmentSupport_iff c P 0 (by dsimp [k]; omega) _).mpr
    exact Or.inl ⟨a, Nat.zero_le _, by change k - 1 < 0 + k; omega, rfl⟩
  exact ⟨hSegment.1, ⟨(binaryTree_model_in_two_cell_comb γ).trans M⟩,
    c a, ⟨hcentres a, fun h ↦ Set.disjoint_left.mp hdis haFirst h⟩,
    P e, hBoundary, hMeet⟩

end GraphMinor.GM01
