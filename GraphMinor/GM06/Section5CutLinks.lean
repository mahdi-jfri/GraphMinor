module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Walks

/-!
# Projecting links of a cut drawing

For a closed continuous quotient, an edge given by a full inverse
image projects onto the original edge. Its closure also projects
onto the original closure. If the vertex set is the full inverse
image of the original vertex set, the two ends therefore project
to the original ends. This carries links of the one-path cut drawing
back to the cylinder in the proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u v

/-- A link of a drawing with lifted vertices and a full lifted edge
projects to a link of the original drawing. The projected ends may coincide. -/
theorem isLink_of_full_preimage_edge
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hc : Continuous f) (hclosed : IsClosedMap f) (hsurj : Function.Surjective f)
    {F : Drawing X} {G : Drawing Y} (hFV : F.V = f ⁻¹' G.V)
    {ec : Set X} {e : Set Y} (he : e ∈ G.E) (heq : ec = f ⁻¹' e)
    {x y : X} (hl : F.toGraph.IsLink ec x y) : G.toGraph.IsLink e (f x) (f y) := by
  have him : f '' ec = e := by rw [heq, image_preimage_eq _ hsurj]
  have hcl : f '' closure ec = closure e := by
    rw [← hclosed.closure_image_eq_of_continuous hc, him]
  have hx : f x ∈ G.V := by
    have hxF := hl.2.1
    rw [hFV] at hxF
    exact hxF
  have hy : f y ∈ G.V := by
    have hyF := hl.2.2.1
    rw [hFV] at hyF
    exact hyF
  refine ⟨he, hx, hy, ?_⟩
  calc
    closure e ∩ G.V = (f '' closure ec) ∩ G.V := by rw [hcl]
    _ = f '' (closure ec ∩ f ⁻¹' G.V) := (image_inter_preimage f (closure ec) G.V).symm
    _ = f '' {x, y} := by rw [← hFV, hl.2.2.2]
    _ = {f x, f y} := image_pair f x y

/-- At a singleton fiber of a closed continuous surjection, incidence
with an edge closure lifts to incidence with its full preimage. -/
theorem mem_closure_preimage_of_singleton_fiber
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hc : Continuous f) (hclosed : IsClosedMap f) (hsurj : Function.Surjective f)
    {e : Set Y} {x : X} (hx : f x ∈ closure e)
    (hunique : ∀ y, f y = f x → y = x) : x ∈ closure (f ⁻¹' e) := by
  have him : f '' closure (f ⁻¹' e) = closure e := by
    rw [← hclosed.closure_image_eq_of_continuous hc, image_preimage_eq _ hsurj]
  obtain ⟨y, hy, hyx⟩ := him.symm ▸ hx
  exact hunique y hyx ▸ hy

/-- A link at a vertex with a singleton fiber lifts to a link at its
unique preimage, whenever its full edge preimage belongs to the cut drawing. -/
theorem exists_isLink_full_preimage_of_unique_fiber
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hc : Continuous f) (hclosed : IsClosedMap f) (hsurj : Function.Surjective f)
    {F : Drawing X} {G : Drawing Y} (hFV : F.V = f ⁻¹' G.V)
    {e : Set Y} (hec : f ⁻¹' e ∈ F.E) {x : X} {v : Y}
    (hxF : x ∈ F.V) (hlG : G.toGraph.IsLink e (f x) v)
    (hunique : ∀ y, f y = f x → y = x) :
    ∃ y, F.toGraph.IsLink (f ⁻¹' e) x y ∧ f y = v := by
  have hxcl : x ∈ closure (f ⁻¹' e) := mem_closure_preimage_of_singleton_fiber hc hclosed hsurj
    (show f x ∈ closure e from
      (show f x ∈ closure e ∩ G.V from hlG.2.2.2.symm ▸ mem_insert _ {v}).1) hunique
  obtain ⟨u, w, huv⟩ := F.toGraph.exists_isLink_of_mem_edgeSet hec
  have hxpair : x ∈ ({u, w} : Set X) := huv.2.2.2 ▸ (show x ∈ closure (f ⁻¹' e) ∩ F.V from ⟨hxcl, hxF⟩)
  have hxy : ∃ y, F.toGraph.IsLink (f ⁻¹' e) x y := by
    rcases hxpair with hxu | hxw
    · exact hxu.symm ▸ ⟨w, huv⟩
    · exact (mem_singleton_iff.mp hxw).symm ▸ ⟨u, huv.symm⟩
  obtain ⟨y, hxy⟩ := hxy
  have hproj := isLink_of_full_preimage_edge hc hclosed hsurj hFV hlG.1 rfl hxy
  exact ⟨y, hxy, hlG.isLink_iff_eq.mp hproj⟩

/-- Two distinct drawing vertices in an edge closure are precisely its
ends, so they form a link of that edge. -/
theorem isLink_of_distinct_vertices_in_closure
    {S : Type u} [TopologicalSpace S] {F : Drawing S} {e : Set S} (he : e ∈ F.E)
    {x y : S} (hx : x ∈ F.V) (hy : y ∈ F.V) (hxy : x ≠ y)
    (hxc : x ∈ closure e) (hyc : y ∈ closure e) : F.toGraph.IsLink e x y := by
  obtain ⟨a, b, hl⟩ := F.toGraph.exists_isLink_of_mem_edgeSet he
  have hxpair : x ∈ ({a, b} : Set S) := hl.2.2.2 ▸ (show x ∈ closure e ∩ F.V from ⟨hxc, hx⟩)
  have hypair : y ∈ ({a, b} : Set S) := hl.2.2.2 ▸ (show y ∈ closure e ∩ F.V from ⟨hyc, hy⟩)
  rcases hxpair with rfl | rfl <;> rcases hypair with rfl | rfl
  · exact False.elim (hxy rfl)
  · exact hl
  · exact hl.symm
  · exact False.elim (hxy rfl)

end GraphMinor.GM06
