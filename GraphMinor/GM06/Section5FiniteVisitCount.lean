module

public import GraphMinor.GM06.Defs
public import Mathlib.Topology.Subpath
import GraphMinor.GM06.Section5SubpathCount
import GraphMinor.GM06.Section5ThreeSubpaths

/-!
# Counting visits when splitting at an interior vertex

The finite-visit construction for VI (5.5), page 130, splits a
curve at its last interior vertex visit. The prefix has strictly
fewer interior visits, so induction terminates. The closed prefix
and suffix together count the joining visit twice, giving the
identity needed when their replacements are concatenated.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Restricting to a prefix ending at an interior vertex strictly
decreases the number of interior vertex visits. -/
theorem interior_vertex_hits_prefix_ncard_lt
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y : S}
    (p : Path x y) (hf : (curveVertexHits G p.toContinuousMap).Finite)
    {τ : unitInterval} (hτ : τ ∈ Ioo 0 1) (hτV : p τ ∈ G.V) :
    (curveVertexHits G (p.subpath 0 τ).toContinuousMap ∩ Ioo 0 1).ncard <
      (curveVertexHits G p.toContinuousMap ∩ Ioo 0 1).ncard := by
  classical
  have hi := convexComb_injective_of_ne (ne_of_lt hτ.1)
  have hfin := (curveL_subpath p (ne_of_lt hτ.1) hf).1
  let A := curveVertexHits G (p.subpath 0 τ).toContinuousMap ∩ Ioo 0 1
  let B := curveVertexHits G p.toContinuousMap ∩ Ioo 0 1
  have hBfin : B.Finite := hf.inter_of_left _
  have hsub : Icc.convexComb 0 τ '' A ⊆ B \ {τ} := by
    rintro z ⟨t, ht, rfl⟩
    have htime := convexComb_mem_Ioo_of_lt hτ.1 ht.2
    have hv : p (Icc.convexComb 0 τ t) ∈ G.V := ht.1
    exact ⟨⟨hv, htime.1, htime.2.trans hτ.2⟩,
      fun he => htime.2.ne (mem_singleton_iff.mp he)⟩
  have hc := ncard_le_ncard hsub (hBfin.sdiff (t := {τ}))
  rw [ncard_image_of_injective _ hi] at hc
  have hτB : τ ∈ B := ⟨hτV, hτ⟩
  have hremove := ncard_sdiff_singleton_add_one hτB hBfin
  change A.ncard < B.ncard
  omega

/-- Splitting a finite-hit curve at an interior vertex counts that
vertex twice, once at the end of each subpath. -/
theorem curveL_two_subpaths_at_vertex
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y : S}
    (p : Path x y) (hf : (curveVertexHits G p.toContinuousMap).Finite)
    {τ : unitInterval} (hτ : τ ∈ Ioo 0 1) (hτV : p τ ∈ G.V) :
    curveL G (p.subpath 0 τ).toContinuousMap + curveL G (p.subpath τ 1).toContinuousMap =
      curveL G p.toContinuousMap + 1 := by
  have hp := (curveL_subpath p (ne_of_lt hτ.1) hf).2
  have hq := (curveL_subpath p (ne_of_lt hτ.2) hf).2
  have hI : Icc (0 : unitInterval) τ = Iic τ := by
    ext t
    exact and_iff_right (show 0 ≤ t from bot_le)
  have hJ : Icc τ (1 : unitInterval) = Ici τ := by
    ext t
    exact and_iff_left (show t ≤ 1 from le_top)
  rw [uIcc_of_le (show (0 : unitInterval) ≤ τ from bot_le), hI] at hp
  rw [uIcc_of_le (show τ ≤ (1 : unitInterval) from le_top), hJ] at hq
  have hsplit := ncard_split_at (curveVertexHits G p.toContinuousMap) hf τ
  have hm : τ ∈ curveVertexHits G p.toContinuousMap := hτV
  rw [ite_eq_left hm] at hsplit
  rw [hp, hq]
  exact hsplit

end GraphMinor.GM06
