module

public import GraphMinor.GM06.Alg57FaceRegions
import GraphMinor.GM11.Section4c

/-!
# Regions after removing ordinary edges

In the local side comparison of VI (5.7), page 133, each region of
the full drawing lies in a unique region of the linkage-and-cuff
subdrawing. Removing an edge joins its two incident corners in that
larger region. This is the local reason that all corners between
two consecutive retained ends have the same side.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
  {Γ H : Drawing S}

/-- The region of a subdrawing that contains a given region of the
full drawing. The containing region is unique since regions are disjoint. -/
noncomputable def regionInSubdrawing (hH : H.IsSubdrawing Γ) (r : Γ.R) : H.R :=
  Classical.choose (show ∃ s : H.R, r.val ⊆ s.val from by
    obtain ⟨s, hs, hrs⟩ := exists_region_superset hH r.property
    exact ⟨⟨s, hs⟩, hrs⟩)

omit [LocallyConnectedSpace S] in
/-- A region lies inside its containing region of the subdrawing. -/
theorem subset_regionInSubdrawing (hH : H.IsSubdrawing Γ) (r : Γ.R) :
    r.val ⊆ (regionInSubdrawing hH r).val :=
  Classical.choose_spec (show ∃ s : H.R, r.val ⊆ s.val from by
    obtain ⟨s, hs, hrs⟩ := exists_region_superset hH r.property
    exact ⟨⟨s, hs⟩, hrs⟩)

/-- A region of the smaller drawing that meets the closure of an old
region is its containing region, provided the contact is inside it. -/
theorem regionInSubdrawing_eq_of_closure_mem (hH : H.IsSubdrawing Γ)
    (r : Γ.R) (s : H.R) {p : S} (hp : p ∈ closure r.val) (hps : p ∈ s.val) :
    regionInSubdrawing hH r = s := by
  obtain ⟨q, hqs, hqr⟩ := mem_closure_iff.mp hp s.val (region_isOpen s.property) hps
  apply Subtype.ext
  exact region_eq_of_mem (regionInSubdrawing hH r).property s.property
    (subset_regionInSubdrawing hH r hqr) hqs

omit [T2Space S] [LocallyConnectedSpace S] in
/-- A deleted open edge is disjoint from the point set of the
subdrawing, including its retained vertices. -/
theorem deleted_edge_disjoint_subdrawing (hH : H.IsSubdrawing Γ)
    {e : Set S} (he : e ∈ Γ.E) (heH : e ∉ H.E) : Disjoint e H.U := by
  apply disjoint_left.mpr
  intro p hp hpH
  have hpV : p ∉ H.V := fun h => (he.2.1 hp).2 (hH.1 h)
  obtain ⟨f, hf, hpf⟩ := H.exists_edge_of_mem hpH hpV
  have hef := Γ.edge_eq_of_mem he (hH.2 hf) hp hpf
  exact heH (hef.symm ▸ hf)

/-- Both corners beside a deleted dart lie in the same region of
the smaller drawing. Thus deleting an end merges the two adjacent
corners in the local row comparison. -/
theorem IsCornerLabel.regionInSubdrawing_rot_symm
    {γ : Set S → unitInterval → S} {R : DartRotation (DrawingDart Γ)}
    {ρ : DrawingDart Γ → Set S} (hH : H.IsSubdrawing Γ)
    (hR : IsDrawingRotation Γ γ R) (hρ : IsCornerLabel Γ γ R ρ)
    (d : DrawingDart Γ) (heH : d.val.1 ∉ H.E) :
    regionInSubdrawing hH ⟨ρ (R.rot.symm d), hρ.region _⟩ =
      regionInSubdrawing hH ⟨ρ d, hρ.region d⟩ := by
  obtain ⟨p, hp⟩ := d.property.1
  have hpH : p ∉ H.U := disjoint_left.mp (deleted_edge_disjoint_subdrawing hH d.property heH) hp
  obtain ⟨s, hs, hps⟩ := exists_region_of_notMem hpH
  have hleft := regionInSubdrawing_eq_of_closure_mem hH ⟨ρ d, hρ.region d⟩ ⟨s, hs⟩
    (hρ.edge d hp) hps
  have hprev : p ∈ closure (ρ (R.rot.symm d)) := by
    rw [hρ.rot_symm]
    apply hρ.edge (R.rev d)
    simpa only [hR.rev_eq, dartFlip_apply] using hp
  exact (regionInSubdrawing_eq_of_closure_mem hH ⟨ρ (R.rot.symm d), hρ.region _⟩
    ⟨s, hs⟩ hprev hps).trans hleft.symm

end GraphMinor.GM06
