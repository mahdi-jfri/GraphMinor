module

public import GraphMinor.GM07.CutStages
public import GraphMinor.GM19.CutMap
public import GraphMinor.Surface.Dissection
import GraphMinor.GM08.Section18CountedWordCut
import GraphMinor.GM08.Section18LiftedDissection
import GraphMinor.GM08.Section18CutCardinality
import GraphMinor.GM08.Section18CutBoundary
import Lean.Elab.Tactic.Omega

/-!
# Euler change for the constructed dissection cut

Choose words for the source dissection and cut the selected edges.
The face count stays fixed and the edge count increases by the number
of cut edges. Only cut vertices change their fibre counts. Summing
these terms gives the graph Euler change plus the old boundary
contacts, as in the proof of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- The dissection Euler sum changes by the negative Euler sum of the
cutting graph plus its old boundary contacts. This proves the
triangulation calculation used in VIII (18.2), page 286. The boundary
contacts are vertices of the source dissection. -/
theorem exists_dissection_cut_euler {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {V : Set S} {E 𝓕 D : Set (Set S)}
    (hd : IsDissection V E 𝓕) (hDE : D ⊆ E) (hbd : ⋃₀ D ∩ bd S ⊆ V) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (ψ : Y → S) (E' 𝓕' : Set (Set Y)),
      IsSurface Y ∧ GM07.IsCutAlongSet (⋃₀ D) ψ ∧ GM19.IsCutMap ψ (⋃₀ D) ∧
      IsDissection (ψ ⁻¹' V) E' 𝓕' ∧
      (((ψ ⁻¹' V ∩ ⋃₀ E').ncard : ℤ) - E'.ncard + 𝓕'.ncard) -
          (((V ∩ ⋃₀ E).ncard : ℤ) - E.ncard + 𝓕.ncard) =
        (D.ncard : ℤ) - (V ∩ ⋃₀ D).ncard + (⋃₀ D ∩ bd S).ncard := by
  have : T2Space S := hS.2.1
  obtain ⟨W, f, A, lab, hw, hne⟩ := exists_word_edges hS hd
  have hmid : ∀ e ∈ D, edgeMid A e ∉ bd S := by
    intro e he hx
    have hmem : edgeMid A e ∈ ⋃₀ D ∩ bd S := ⟨⟨e, he, hw.extI_mem (hDE he) _⟩, hx⟩
    exact hw.extI_notMem (hDE he) (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num) (hbd hmem)
  obtain ⟨Y, tY, _, ψ, hY, hcm, hlift, _, hsum⟩ := exists_counted_word_cut hw hS hne hDE hmid
  let := tY
  have hcutvertices := hsum hbd
  obtain ⟨E', 𝓕', hd', hEU, hEc, hFc⟩ :=
    exists_lifted_dissection_of_word_cut hY hd hw hDE hcm hlift
  have hclosed : IsClosed (⋃₀ D) := (hw.graph.fine.subset hDE).isClosed_sUnion
    (fun e he => by obtain ⟨u, v, _, hl, _⟩ := hw.graph.edge e (hDE he); exact hl.isCompact.isClosed)
  refine ⟨Y, tY, ψ, E', 𝓕', hY, isCutAlongSet_of_cutMap hS hY hclosed hcm, hcm, hd', ?_⟩
  let T := V ∩ ⋃₀ E
  have hTfin : T.Finite := hd.graph.fin.subset inter_subset_left
  have hTF : T ∩ ⋃₀ D = V ∩ ⋃₀ D := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
      fun hx => ⟨⟨hx.1, sUnion_mono hDE hx.2⟩, hx.2⟩⟩
  have htrim : ψ ⁻¹' V ∩ ⋃₀ E' = ψ ⁻¹' T := by
    rw [hEU, ← preimage_inter]
  have hsource := ncard_inter_add_ncard_sdiff_eq_ncard T (⋃₀ D) hTfin
  rw [hTF] at hsource
  rw [htrim, hEc, hFc, cutMap_ncard_preimage_eq hcm hTfin, hTF, hcutvertices]
  change (((2 * D.ncard + (⋃₀ D ∩ bd S).ncard + (T \ ⋃₀ D).ncard : ℕ) : ℤ) -
      (E.ncard + D.ncard : ℕ) + 𝓕.ncard) - ((T.ncard : ℤ) - E.ncard + 𝓕.ncard) = _
  push_cast
  omega

end GraphMinor.GM08
