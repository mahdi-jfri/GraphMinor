module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM07.Matched
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks
import Mathlib.Data.List.Nodup

/-!
# A carried simple path has exactly its projected point set

Carry the simple graph walk to the target drawing. Injectivity on
the source path makes the mapped support simple. The target walk
therefore draws a path. Closedness of the map carries each edge
closure exactly, so the point set of the target path is exactly
the image of the source point set. This projects the first-contact
cut path in the proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u v

/-- A carrying map which is continuous and closed maps a path with
distinct endpoint images to a subpath with exactly the image point set. -/
theorem exists_path_image_of_isCarry
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] {f : X → Y} (hc : Continuous f) (hclosed : IsClosedMap f)
    {Q : Drawing X} {G : Drawing Y} {s t : X}
    (hcarry : GM07.IsCarry Q G f Q.V) (hQ : IsPathDrawing Q s t) (hends : f s ≠ f t) :
    ∃ P : Drawing Y, IsSubpathOf G P (f s) (f t) ∧ P.U = f '' Q.U := by
  obtain ⟨W, hW, hV, hE⟩ := hQ.1
  have hs : s ∈ Q.V := (isPathDrawing_end_vertices hQ).1
  obtain ⟨R, hRV, hRE, _, _⟩ := hcarry.walk W hs (f s) (f t) rfl rfl
  have hR : R.IsSimple := by
    change R.support.Nodup
    rw [hRV]
    apply List.Nodup.map_on _ hW
    intro x hx y hy hxy
    have hxV : x ∈ Q.V := by rw [hV]; exact hx
    have hyV : y ∈ Q.V := by rw [hV]; exact hy
    exact hcarry.inj (Q.V_subset_U hxV) (Q.V_subset_U hyV) hxy
  let P := walkDrawing G R
  have hPG : P.IsSubdrawing G := walkDrawing_isSubdrawing G R
  have hPath : IsPathDrawing P (f s) (f t) := isPathDrawing_walkDrawing_of_isSimple G hR hends
  refine ⟨P, ⟨hPG, hPG.U_subset, hPath⟩, ?_⟩
  ext z
  constructor
  · intro hz
    rcases (mem_walkDrawing_U G R).mp hz with hzV | ⟨d, hd, hzd⟩
    · rw [hRV] at hzV
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hzV
      have hxV : x ∈ Q.V := by rw [hV]; exact hx
      exact mem_image_of_mem f (Q.V_subset_U hxV)
    · rw [hRE] at hd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
      rw [hclosed.closure_image_eq_of_continuous hc] at hzd
      obtain ⟨x, hx, rfl⟩ := hzd
      have heQ : e ∈ Q.E := by rw [hE]; exact he
      exact mem_image_of_mem f (Q.closure_subset_U heQ hx)
  · rintro ⟨x, hx, rfl⟩
    apply (mem_walkDrawing_U G R).mpr
    rw [Q.U_eq] at hx
    rcases hx with hxV | hxEdge
    · left
      rw [hRV]
      rw [hV] at hxV
      exact List.mem_map.mpr ⟨x, hxV, rfl⟩
    · obtain ⟨e, heQ, hxe⟩ := mem_iUnion₂.mp hxEdge
      refine Or.inr ⟨f '' e, ?_, ?_⟩
      · rw [hRE]
        rw [hE] at heQ
        exact List.mem_map.mpr ⟨e, heQ, rfl⟩
      · exact image_closure_subset_closure_image hc (mem_image_of_mem f hxe)

end GraphMinor.GM06
