module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5RetainedPuncturedBarrier
import GraphMinor.GM06.Section5PuncturedLinkage
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks

/-!
# The cuff-containing punctured barrier for at least two paths

For Reduction 2 of VI (5.5), page 130, the cuffs together with
the linkage remain connected after one initial vertex is removed
when there are at least two paths. The vertex-deleted component
construction therefore gives an actual subdrawing containing both
cuffs whose puncture is connected. The initial linkage path also
shows that the punctured barrier accumulates at its attachment.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- With at least two linkage paths, the retained augmented drawing
has a cuff-containing barrier whose puncture is connected and
accumulates at the prescribed initial attachment. -/
theorem exists_multiple_path_punctured_cuff_barrier_separation
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (i : Fin k) :
    ∃ T R : Drawing ClosedCylinder, T.IsSubdrawing F ∧ bd ClosedCylinder ⊆ T.U ∧
      cylinderM1Point k i ∈ T.V ∧ IsConnected (T.U \ {cylinderM1Point k i}) ∧
      cylinderM1Point k i ∈ closure (T.U \ {cylinderM1Point k i}) ∧
      IsGraphSeparation F.toGraph R.toGraph T.toGraph ∧
      R.U ∩ T.U ⊆ {cylinderM1Point k i} := by
  let s := cylinderM1Point k i
  let X := (bd ClosedCylinder ∪ ⋃ j, (L.pathDrawing j).U) \ {s}
  have hX : IsConnected X := isConnected_punctured_linkage_and_cuffs L hk i
  have hsV : s ∈ F.V := hGF.1 ((L.isSubdrawing i).1.1
    (isPathDrawing_end_vertices (L.isPath i)).1)
  have hXG : X ⊆ F.U := by
    rintro x ⟨hx | hx, _⟩
    · exact hbdF hx
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact hGF.U_subset ((L.isSubdrawing j).2 hxj)
  have hsX : s ∉ X := fun h => h.2 rfl
  let a := L.curve i 1
  have ha2 : a ∈ cylinderCuff2 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    change L.curve i 1 ∈ cylinderCuff2
    rw [← hj]
    rfl
  have has : a ≠ s := by
    intro he
    have hs2 : s ∈ cylinderCuff2 := he ▸ ha2
    change (1 : ℝ) = 2 at hs2
    norm_num at hs2
  have haX : a ∈ X := by
    refine ⟨Or.inl ?_, has⟩
    rw [bd_closedCylinder]
    exact Or.inr ha2
  have haV : a ∈ F.V := hGF.1 ((L.isSubdrawing i).1.1
    (isPathDrawing_end_vertices (L.isPath i)).2)
  obtain ⟨T, R, hTF, hsT, hXT, hconn, hsep, hover⟩ :=
    exists_punctured_barrier_separation_containing_preconnected_set
    F hsV hX.isPreconnected hXG hsX haX haV
  have hbdT : bd ClosedCylinder ⊆ T.U := by
    intro x hxb
    by_cases hxs : x = s
    · exact hxs ▸ T.V_subset_U hsT
    · exact hXT ⟨Or.inl hxb, hxs⟩
  have hXpuncture : X ⊆ T.U \ {s} := fun x hx => ⟨hXT hx, hx.2⟩
  have h0cl : (0 : unitInterval) ∈ closure (Ioo (0 : unitInterval) 1) := by
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_ne_one)]
    exact ⟨bot_le, le_top⟩
  have hpathsub : L.curve i '' Ioo (0 : unitInterval) 1 ⊆ X := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨Or.inr (mem_iUnion.mpr ⟨i, ?_⟩), ?_⟩
    · exact (L.curve_parametrizes i).2.1 ▸ mem_range_self t
    · intro hts
      have he : L.curve i t = L.curve i 0 := hts.trans (L.curve_parametrizes i).2.2.1.symm
      exact (ne_of_gt ht.1) ((L.curve_parametrizes i).1 he)
  have hscl : s ∈ closure (T.U \ {s}) := by
    have hcl := mem_closure_image (L.curve i).continuous.continuousAt h0cl
    rw [(L.curve_parametrizes i).2.2.1] at hcl
    exact closure_mono (hpathsub.trans hXpuncture) hcl
  exact ⟨T, R, hTF, hbdT, hsT, hconn, hscl, hsep, hover⟩

/-- Retain the cuff barrier and forget its other separation side. -/
theorem exists_multiple_path_punctured_cuff_barrier
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (i : Fin k) :
    ∃ T : Drawing ClosedCylinder, T.IsSubdrawing F ∧ bd ClosedCylinder ⊆ T.U ∧
      cylinderM1Point k i ∈ T.V ∧ IsConnected (T.U \ {cylinderM1Point k i}) ∧
      cylinderM1Point k i ∈ closure (T.U \ {cylinderM1Point k i}) := by
  obtain ⟨T, _, hTF, hbdT, hsT, hconn, hscl, _, _⟩ :=
    exists_multiple_path_punctured_cuff_barrier_separation L hk hGF hbdF i
  exact ⟨T, hTF, hbdT, hsT, hconn, hscl⟩

end GraphMinor.GM06
