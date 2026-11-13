module

public import GraphMinor.GM05.SurfaceDescent
import GraphMinor.GM05.CircleCut
import GraphMinor.GM05.OpenDiscContainment
import GraphMinor.GM05.DrawingSupportTransport
import GraphMinor.GM11.Regions
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.Disc

/-!
# Regions of a drawing on a minimal surface

Follow GM V, (8.12): a circle in a region that bounds no disc can be
cut and capped. The drawing misses the circle, so the complement
homeomorphism carries it to the smaller surface, contrary to minimality.
The open-disc criterion then contains the region. The drawing is required
to meet every spherical component, excluding the unused-sphere error.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface GM19
universe u v

/-- Graph Minors V, (8.12), page 113:
"For any drawing of $H$ in $\Sigma$ and any region $r$ of this drawing, there is an open disc $\Delta \subseteq \Sigma$ with $r \subseteq \Delta$."
The context chooses an orientable surface minimal in the component-genus
order. We also require this drawing to meet every spherical component:
an unused sphere is a counterexample to the printed statement. -/
theorem theorem_8_12_proof {α : Type u} {β : Type v} {H : Graph α β}
    {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S)
    (hO : IsOrientableSurface S)
    (hmin : ∀ (T : Type) [TopologicalSpace T] (hT : IsClosedSurface T),
      IsOrientableSurface T → Nonempty (GraphDrawing H T) → ¬SurfaceGenusLT hT hS)
    (Γ : GraphDrawing H S)
    (hused : ∀ x : S, IsSphere (connectedComponent x) →
      (Γ.drawing.U ∩ connectedComponent x).Nonempty)
    {r : Set S} (hr : r ∈ Γ.drawing.R) :
    ∃ D : Set S, IsOpenDisc D ∧ r ⊆ D := by
  let : T2Space S := hS.2.1
  let : CompactSpace S := hS.1
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hs.locallyConnected
  have hrc : IsConnected r := ⟨GM11.region_nonempty hr,GM11.region_isPreconnected hr⟩
  let : Nonempty S := ⟨hrc.nonempty.choose⟩
  have hdiscs : ∀ C : Set S, C ⊆ r → IsOArc C → ∃ D : Set S, IsClosedDisc D ∧ C=discBd D := by
    intro C hCr hC
    rcases theorem_8_10_proof hS hO hC with hdisc|hcut
    · exact hdisc
    · obtain ⟨T,τT,hT,hTO,hgenus,D,D',hD,-,-,⟨f⟩⟩ := hcut
      let : T2Space T := hT.2.1
      let : Nonempty T := ⟨hD.isPathConnected.nonempty.choose⟩
      have hUC : Γ.drawing.U ⊆ Cᶜ := by
        intro y hy hyC
        exact GM11.region_subset hr (hCr hyC) hy
      let j₀ : Γ.drawing.U → ↥(Cᶜ) := fun y ↦ ⟨y.val,hUC y.prop⟩
      have hj₀ : IsEmbedding j₀ := IsEmbedding.subtypeVal.codRestrict _ _
      let j : Γ.drawing.U → T := fun y ↦ (f.symm (j₀ y)).val
      have hj : IsEmbedding j := IsEmbedding.subtypeVal.comp (f.symm.isEmbedding.comp hj₀)
      exact (hmin T hT hTO (graphDrawing_of_support_embedding Γ j hj) hgenus).elim
  apply theorem_8_11_proof hS hrc (GM11.region_isOpen hr) hdiscs
  intro x hx hh
  obtain ⟨y,hyU,hyC⟩ := hused x hh.1
  exact GM11.region_subset hr (hh.2.symm ▸ hyC) hyU

end GraphMinor.GM05
