module

public import GraphMinor.GM06.Alg34RegionGraph
public import GraphMinor.Compute.GM06Alg34RegionRoots

/-!
# Canonical region labels describe all new regions bijectively

Interpret each least inactive-cell label by the union of its finite
reachability class. This is an actual region of the induced drawing.
Different root labels give different regions, and every region arises.
Thus the canonical finite labels provide the region bijection required
when updating a supplied drawing after singleton deletion.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06 GM11

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- The subset represented by one packed complement-component label. -/
def regionClass (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) (r : Fin x.cellCount) : Set S :=
  ⋃ b ∈ {b | x.activeCell vs b = false ∧
    (x.complementGraph vs).Reachable r (x.cellNumbering b)}, h.cell b

/-- An inactive packed label represents an actual region of the induced drawing. -/
theorem regionClass_mem_regions (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (r : Fin x.cellCount) (hr : x.activeCell vs (x.cellNumbering.symm r) = false) :
    h.regionClass vs r ∈ (induceDrawing G (h.vertexImage vs)).R := by
  simpa only [regionClass, Equiv.apply_symm_apply] using
    h.regionGraph_class_mem_regions vs (x.cellNumbering.symm r) hr

/-- Interpret a canonical root as its actual induced-drawing region. -/
def regionLabel (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (r : {r : Fin x.cellCount // r ∈ x.regionRoots vs}) : (induceDrawing G (h.vertexImage vs)).R :=
  ⟨h.regionClass vs r.val, h.regionClass_mem_regions vs r.val
    ((x.mem_regionRoots_iff vs r.val).mp r.property).1⟩

/-- Every inactive cell belongs to the region class of its own packed label. -/
theorem cell_subset_regionClass (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (a : GM06CellIndex x) (ha : x.activeCell vs a = false) :
    h.cell a ⊆ h.regionClass vs (x.cellNumbering a) := by
  intro p hp
  exact mem_iUnion₂.mpr ⟨a, ⟨ha, .refl _⟩, hp⟩

/-- Canonical finite roots are in bijection with all actual regions after deletion. -/
theorem regionLabel_bijective (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) :
    Function.Bijective (h.regionLabel vs) := by
  constructor
  · intro a b hab
    have ha0 := ((x.mem_regionRoots_iff vs a.val).mp a.property).1
    obtain ⟨p, hp⟩ := (h.cell_isConnected (x.cellNumbering.symm a.val)).1
    have hpA : p ∈ h.regionClass vs a.val := by
      simpa only [Equiv.apply_symm_apply] using
        h.cell_subset_regionClass vs _ ha0 hp
    have heq : h.regionClass vs a.val = h.regionClass vs b.val := congrArg Subtype.val hab
    have hpB : p ∈ h.regionClass vs b.val := heq ▸ hpA
    obtain ⟨c, ⟨_, hbc⟩, hpc⟩ := mem_iUnion₂.mp hpB
    have hca : c = x.cellNumbering.symm a.val := h.cell_index_eq_of_mem hpc hp
    rw [hca, Equiv.apply_symm_apply] at hbc
    exact Subtype.ext ((x.regionRoots_eq_of_reachable vs b.property a.property hbc).symm)
  · intro r
    obtain ⟨p, hp⟩ := region_nonempty r.property
    have hpU := region_subset r.property hp
    rw [h.induced_complement_eq_cells vs] at hpU
    obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.mp hpU
    obtain ⟨b, hb, hab⟩ := x.exists_regionRoot vs (x.cellNumbering a)
      (by simpa only [Equiv.symm_apply_apply, mem_ofPred_eq] using ha)
    let b' : {r : Fin x.cellCount // r ∈ x.regionRoots vs} := ⟨b, hb⟩
    have hpB : p ∈ (h.regionLabel vs b').val :=
      mem_iUnion₂.mpr ⟨a, ⟨ha, hab.symm⟩, hpa⟩
    exact ⟨b', Subtype.ext (region_eq_of_mem (h.regionLabel vs b').property r.property hpB hp)⟩

end GraphMinor.Compute.GM06DrawingRep
