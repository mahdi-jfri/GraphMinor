module

public import GraphMinor.GM05.SeparatedStarDiscs
public import GraphMinor.GM19.Section6Contract
import GraphMinor.GM07.ThickForest
import GraphMinor.GM07.SideDisc
import GraphMinor.GM19.Section6a

/-!
# The line between the vertex discs

In GM V, (8.14), the middle of each edge is separated from the
vertex neighbourhoods. The star disc lemma cuts the edge into its
two end rays and a line between the boundaries. Avoidance of
nonincident edges ensures that this middle line misses every other
vertex disc. Distinct middle lines lie in distinct open edges.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- The middle of a line edge runs between its two star discs and
misses every other vertex disc. This prepares the edge neighbourhoods
in GM V, (8.14), page 113. -/
theorem exists_edge_middle_line {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (D : Drawing S) (hD : GM19.LoopFree D)
    (R : S → Set S) (hR : ∀ v ∈ D.V, GM07.IsStarDisc D v (R v))
    (hdis : ∀ u ∈ D.V, ∀ v ∈ D.V, u ≠ v → Disjoint (R u) (R v))
    (hoff : ∀ v ∈ D.V, ∀ e ∈ D.E, v ∉ closure e → Disjoint (R v) (closure e))
    {e : Set S} (he : e ∈ D.E) :
    ∃ u v p q M, u ∈ D.V ∧ v ∈ D.V ∧ u ≠ v ∧ D.toGraph.IsLink e u v ∧
      IsLineWithEnds M p q ∧ M ⊆ e ∧
      M ∩ R u = {p} ∧ M ∩ R v = {q} ∧
      p ∈ discBd (R u) ∧ q ∈ discBd (R v) ∧
      ∀ w ∈ D.V, w ≠ u → w ≠ v → Disjoint M (R w) := by
  let : T2Space S := hS.2.1
  obtain ⟨u,v,huv,ht,hl⟩ := hD e he
  have hends : closure e ∩ D.V = {u,v} := by
    rw [← GM19.tilde_eq_inter_V D he]
    exact ht
  have hu : u ∈ D.V := (hends ▸ (mem_insert u {v}) : u ∈ closure e ∩ D.V).2
  have hv : v ∈ D.V := (hends ▸ (by simp : v ∈ ({u,v} : Set S)) : v ∈ closure e ∩ D.V).2
  obtain ⟨γ,hc,h0,h1,hi,himg⟩ := GM11.exists_edge_param D he
  have hn := GM07.isGammaNice_closure (Γ := D) subset_rfl subset_rfl he
    (show GM07.EdgeParam D e γ from ⟨hc,h0,h1,hi,himg⟩)
  obtain ⟨p,q,M,A,B,hM,hcov,-,-,hMu,hMv,hp,hq,-,-,hun,hvn⟩ :=
    GM07.exists_edge_piece hS (hR u hu) (hR v hv) (hdis u hu v hv huv)
      hl isClosed_closure hn
  have hML : M ⊆ closure e := fun x hx ↦ hcov ▸ (.inl (.inr hx) : x ∈ A ∪ M ∪ B)
  have hMe : M ⊆ e := by
    intro x hx
    apply (D.closure_diff_V he).subset
    refine ⟨hML hx,?_⟩
    intro hxV
    have hxe : x ∈ ({u,v} : Set S) := hends ▸ ⟨hML hx,hxV⟩
    rcases hxe with rfl | rfl
    · exact hun hx
    · exact hvn hx
  refine ⟨u,v,p,q,M,hu,hv,huv,⟨he,hu,hv,hends⟩,hM,hMe,hMu,hMv,hp,hq,?_⟩
  intro w hw hwu hwv
  have hwL : w ∉ closure e := by
    intro hh
    have h : w ∈ ({u,v} : Set S) := hends ▸ ⟨hh,hw⟩
    exact h.elim hwu hwv
  exact ((hoff w hw e he hwL).mono_right hML).symm

/-- Orient the middle line by prescribed original endpoints. This
keeps edge labels consistent across the copies in GM V, (8.14). -/
theorem exists_edge_middle_line_at_ends {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (D : Drawing S) (hD : GM19.LoopFree D)
    (R : S → Set S) (hR : ∀ v ∈ D.V, GM07.IsStarDisc D v (R v))
    (hdis : ∀ u ∈ D.V, ∀ v ∈ D.V, u ≠ v → Disjoint (R u) (R v))
    (hoff : ∀ v ∈ D.V, ∀ e ∈ D.E, v ∉ closure e → Disjoint (R v) (closure e))
    {e : Set S} {u v : S} (hl : D.toGraph.IsLink e u v) :
    ∃ p q M, IsLineWithEnds M p q ∧ M ⊆ e ∧
      M ∩ R u = {p} ∧ M ∩ R v = {q} ∧
      p ∈ discBd (R u) ∧ q ∈ discBd (R v) ∧
      ∀ w ∈ D.V, w ≠ u → w ≠ v → Disjoint M (R w) := by
  obtain ⟨a,b,p,q,M,ha,hb,hab,hlab,hM,hMe,hMa,hMb,hp,hq,haway⟩ :=
    exists_edge_middle_line hS D hD R hR hdis hoff hl.edge_mem
  rcases hlab.eq_and_eq_or_eq_and_eq hl with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨p,q,M,hM,hMe,hMa,hMb,hp,hq,haway⟩
  · exact ⟨q,p,M,hM.symm,hMe,hMb,hMa,hq,hp,fun w hw hwu hwv ↦ haway w hw hwv hwu⟩

end GraphMinor.GM05
