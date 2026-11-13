module

public import GraphMinor.GM01.CombShiftRanges
public import GraphMinor.GM01.RootedSubgraphSubdivisionAttachment

/-!
# Keeping an attachment outside the two ends after contraction

In Graph Minors I, (4.9), page 58, contract the replacing paths of `D`
while retaining its attachment vertex. A centre outside the two ends
already has an interior source position. If the attachment is internal
to a replacing path, its ends cannot both be in the same end interval,
because the whole path would then belong to that end. The source edge
cannot jump between the two end intervals. Hence one end has an
interior position. Assign the replacing-path interior to that end's
branch and root the contracted comb there.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The controlled contraction of `D` in GM01 (4.9), page 58. Any
attachment outside its first and second ends gives a rooted copy of
the original comb at a vertex outside the first and last two cells. -/
theorem rooted_comb_at_interior_vertex_of_subdivision {α β : Type*} {γ L : ℕ}
    (hL : 5 ≤ L) {D : Graph α β} {c : (pathComb γ L).verts → α} (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (x : V(D))
    (hx : x.val ∉ combFirstEndSupport (by omega) c P ∪ combSecondEndSupport (by omega) c P) :
    ∃ v : (pathComb γ L).verts,
      2 ≤ (pathCombSpineIndex v.val).val ∧ (pathCombSpineIndex v.val).val < L - 2 ∧
      HasRootedMinor (⟨toGraph (pathComb γ L), v⟩ : RootedGraph (PathCombVertex L) (Sym2 (PathCombVertex L)))
        (⟨D, x⟩ : RootedGraph α β) := by
  classical
  let : Finite (pathComb γ L).verts := (pathComb_vertices_finite γ L).to_subtype
  have hcentres : ∀ v, c v ∈ V(D) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hmake : ∀ v : (pathComb γ L).verts,
      2 ≤ (pathCombSpineIndex v.val).val ∧ (pathCombSpineIndex v.val).val < L - 2 →
      (x.val = c v ∨ ∃ e : (pathComb γ L).coe.edgeSet,
        v ∈ e.val ∧ x.val ∈ V(P e) ∧ x.val ∉ range c) →
      ∃ v : (pathComb γ L).verts,
        2 ≤ (pathCombSpineIndex v.val).val ∧ (pathCombSpineIndex v.val).val < L - 2 ∧
        HasRootedMinor (⟨toGraph (pathComb γ L), v⟩ : RootedGraph (PathCombVertex L) (Sym2 (PathCombVertex L)))
          (⟨D, x⟩ : RootedGraph α β) := by
    intro v hv hxv
    exact ⟨v, hv.1, hv.2,
      ⟨rootedSubgraphSubdivisionAtVertex (pathComb γ L) c hc hcentres P hPaths hInter v x hxv⟩⟩
  by_cases hxC : x.val ∈ range c
  · obtain ⟨v, hv⟩ := hxC
    have hfirst : 2 ≤ (pathCombSpineIndex v.val).val := by
      by_contra hnot
      have hi : (pathCombSpineIndex v.val).val < 2 := by omega
      obtain ⟨w, hw⟩ := (mem_range_combShiftEmbedding_iff 0 (by omega : 0 + 2 ≤ L) v).mpr
        ⟨Nat.zero_le _, by omega⟩
      have hmem : c v ∈ combFirstEndSupport (by omega) c P := Or.inl ⟨w, congrArg c hw⟩
      exact hx (Or.inl (hv ▸ hmem))
    have hlast : (pathCombSpineIndex v.val).val < L - 2 := by
      by_contra hnot
      have hi := (pathCombSpineIndex v.val).isLt
      obtain ⟨w, hw⟩ := (mem_range_combShiftEmbedding_iff (L - 2) (by omega : L - 2 + 2 ≤ L) v).mpr
        ⟨by omega, by omega⟩
      have hmem : c v ∈ combSecondEndSupport (by omega) c P := Or.inl ⟨w, congrArg c hw⟩
      exact hx (Or.inr (hv ▸ hmem))
    exact hmake v ⟨hfirst, hlast⟩ (Or.inl hv.symm)
  · have hxUnion : x.val ∈ range c ∪ ⋃ e, V(P e) := by
      rw [← hV]
      exact x.property
    rcases hxUnion with hxc | hxp
    · exact False.elim (hxC hxc)
    obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hxp
    obtain ⟨a, b, he, _, _⟩ := hPaths e
    have hab : (pathComb γ L).coe.Adj a b := by
      have h := e.property
      rw [he] at h
      exact h
    have hcross : ∀ u v : (pathComb γ L).verts, (pathComb γ L).coe.Adj u v →
        (pathCombSpineIndex u.val).val < 2 → L - 2 ≤ (pathCombSpineIndex v.val).val → False := by
      intro u v huv hu hv
      have heq := pathComb_adj_crosses_spine_cut (i := ⟨2, by omega⟩) huv.symm
        (by change 2 < (pathCombSpineIndex v.val).val; omega)
        (by change (pathCombSpineIndex u.val).val ≤ 2; omega)
      have hi := congrArg (fun w : PathCombVertex L ↦ (pathCombSpineIndex w).val) heq
      change (pathCombSpineIndex u.val).val = 2 at hi
      omega
    have hcentral :
        (2 ≤ (pathCombSpineIndex a.val).val ∧ (pathCombSpineIndex a.val).val < L - 2) ∨
        (2 ≤ (pathCombSpineIndex b.val).val ∧ (pathCombSpineIndex b.val).val < L - 2) := by
      by_contra hnot
      have ha : (pathCombSpineIndex a.val).val < 2 ∨ L - 2 ≤ (pathCombSpineIndex a.val).val := by omega
      have hb : (pathCombSpineIndex b.val).val < 2 ∨ L - 2 ≤ (pathCombSpineIndex b.val).val := by omega
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · have hmem := path_subset_combSegmentSupport c P 0 (by omega : 0 + 2 ≤ L) e he
          ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ hxe
        exact hx (Or.inl hmem)
      · exact hcross a b hab ha hb
      · exact hcross b a hab.symm hb ha
      · have hai := (pathCombSpineIndex a.val).isLt
        have hbi := (pathCombSpineIndex b.val).isLt
        have hmem := path_subset_combSegmentSupport c P (L - 2) (by omega : L - 2 + 2 ≤ L) e he
          ⟨ha, by omega⟩ ⟨hb, by omega⟩ hxe
        exact hx (Or.inr hmem)
    rcases hcentral with ha | hb
    · apply hmake a ha
      refine Or.inr ⟨e, ?_, hxe, hxC⟩
      rw [he]
      exact Sym2.mem_mk_left a b
    · apply hmake b hb
      refine Or.inr ⟨e, ?_, hxe, hxC⟩
      rw [he]
      exact Sym2.mem_mk_right a b

end GraphMinor.GM01
