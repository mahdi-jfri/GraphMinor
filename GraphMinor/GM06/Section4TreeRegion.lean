module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.SurfacePull
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM07.ForestFlat
import GraphMinor.GM11.PlaneFacts
import Mathlib.Analysis.Normed.Module.Connected

/-!
# A plane forest does not separate

The region choice in Graph Minors VI (4.2), claim (2), uses that a tree
has a region reaching both cuffs. The underlying plane fact is that a
forest does not separate the plane. We remove a leaf, apply induction,
and attach its line back at its remaining end using Janiszewski's theorem.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

private theorem preconnected_compl_union_of_preconnected_compls
    {A B : Set EuclideanPlane} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : IsPreconnected (A ∩ B))
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) :
    IsPreconnected (A ∪ B)ᶜ := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  have hxA : x ∈ Aᶜ := fun h => hx (Or.inl h)
  have hyA : y ∈ Aᶜ := fun h => hy (Or.inl h)
  have hxB : x ∈ Bᶜ := fun h => hx (Or.inr h)
  have hyB : y ∈ Bᶜ := fun h => hy (Or.inr h)
  have hxy := janiszewski_plane hA hB hAB hx hy
    (hAc.subset_connectedComponentIn hxA Subset.rfl hyA)
    (hBc.subset_connectedComponentIn hxB Subset.rfl hyB)
  exact ⟨connectedComponentIn (A ∪ B)ᶜ x, connectedComponentIn_subset _ _,
    mem_connectedComponentIn hx, hxy, isPreconnected_connectedComponentIn⟩

/-- A forest carried into the plane by an embedding has preconnected
complement. This supplies the nonseparation fact behind the region choice
in Graph Minors VI (4.2), claim (2), page 126. -/
theorem isPreconnected_compl_image_forest
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    {j : S → EuclideanPlane} (hj : IsEmbedding j)
    {G : Drawing S} (hG : IsGraphForest G.toGraph) :
    IsPreconnected (j '' G.U)ᶜ := by
  classical
  induction hn : G.E.ncard generalizing G with
  | zero =>
    have hE : G.E = ∅ := (ncard_eq_zero G.finite_edges).mp hn
    have hU : G.U = G.V := by rw [G.U_eq, hE]; simp
    rw [hU]
    exact ((G.finite_V.image j).countable.isConnected_compl_of_one_lt_rank
      (by
        have hr : Module.rank ℝ EuclideanPlane = 2 :=
          (Module.rank_eq_ofNat_iff_finrank_eq_ofNat 2).mpr (by simp [EuclideanPlane])
        rw [hr]
        norm_num)).isPreconnected
  | succ n ih =>
    have hne : G.E.Nonempty := by
      exact (ncard_pos (s := G.E) G.finite_edges).mp (by rw [hn]; exact Nat.succ_pos n)
    obtain ⟨e, he, y, x, hxy, hcap, hleaf, hline⟩ := GM07.exists_forest_leaf hG hne
    let R := induceDrawing G (G.V \ {y})
    have hRV : R.V = G.V \ {y} := induceDrawing_V G sdiff_subset
    have hRE : R.E = G.E \ {e} := by
      rw [induceDrawing_E]
      ext f
      constructor
      · rintro ⟨hf, hends⟩
        refine ⟨hf, ?_⟩
        intro hfe
        have hy : y ∈ closure f ∩ G.V := by rw [hfe, hcap]; exact Or.inl rfl
        exact (hends hy).2 rfl
      · rintro ⟨hf, hfe⟩
        exact ⟨hf, fun z hz => ⟨hz.2, fun hzy => hleaf f hf hfe (hzy ▸ hz.1)⟩⟩
    have hRs : R.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
    have hcard : R.E.ncard = n := by
      rw [hRE, ncard_sdiff_singleton_of_mem he, hn]
      rfl
    have hRc := ih (GM07.IsGraphForest.of_subdrawing hG hRs) hcard
    have hyR : y ∉ R.U := by
      rw [R.U_eq, hRV, hRE]
      rintro (hy | hy)
      · exact hy.2 rfl
      · obtain ⟨f, hf, hyf⟩ := mem_iUnion₂.mp hy
        exact hleaf f hf.1 hf.2 hyf
    have hcapR : closure e ∩ R.U = {x} := by
      rw [R.U_eq, hRV, hRE]
      ext z
      constructor
      · rintro ⟨hz, hzR⟩
        by_cases hzV : z ∈ G.V
        · have hzc : z ∈ closure e ∩ G.V := ⟨hz, hzV⟩
          rw [hcap] at hzc
          rcases hzc with rfl | hzx
          · exact (hyR (by rw [R.U_eq, hRV, hRE]; exact hzR)).elim
          · exact hzx
        · rcases hzR with hzR | hzR
          · exact (hzV hzR.1).elim
          · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp hzR
            have hze : z ∈ e := by rw [← G.closure_diff_V he]; exact ⟨hz, hzV⟩
            have hzff : z ∈ f := by rw [← G.closure_diff_V hf.1]; exact ⟨hzf, hzV⟩
            exact (hf.2 (arcComponent_eq hf.1 he hzff hze)).elim
      · rintro rfl
        have hx : z ∈ closure e ∩ G.V := by rw [hcap]; exact Or.inr rfl
        exact ⟨hx.1, Or.inl ⟨hx.2, hxy⟩⟩
    have hU : G.U = R.U ∪ closure e := by
      rw [G.U_eq, R.U_eq, hRV, hRE]
      refine Subset.antisymm (union_subset ?_ (iUnion₂_subset fun f hf => ?_)) ?_
      · intro z hz
        by_cases hzy : z = y
        · right
          have hy : y ∈ closure e ∩ G.V := by rw [hcap]; exact Or.inl rfl
          exact hzy ▸ hy.1
        · exact Or.inl (Or.inl ⟨hz, hzy⟩)
      · by_cases hfe : f = e
        · exact hfe ▸ subset_union_right
        · exact fun z hz => Or.inl (Or.inr (mem_biUnion ⟨hf, hfe⟩ hz))
      · refine union_subset (union_subset (sdiff_subset.trans subset_union_left) ?_) ?_
        · exact iUnion₂_subset fun f hf z hz => Or.inr (mem_biUnion hf.1 hz)
        · exact fun z hz => Or.inr (mem_biUnion he hz)
    rw [hU, image_union]
    apply preconnected_compl_union_of_preconnected_compls
      (R.isClosed_U.isCompact.image hj.continuous)
      (hline.isCompact.image hj.continuous)
    · rw [← image_inter hj.injective, inter_comm, hcapR]
      exact isPreconnected_singleton.image j hj.continuous.continuousOn
    · exact hRc
    · obtain ⟨e, _, _⟩ := hline.map_of_embedding hj
      exact isPreconnected_compl_of_isLine ⟨e⟩

end GraphMinor.GM06
