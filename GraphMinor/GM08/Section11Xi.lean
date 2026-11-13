module

public import GraphMinor.GM08.Section11Forest
public import GraphMinor.GM08.Section11Iso
import GraphMinor.GM08.Section8Sleeve
import GraphMinor.GM06.DiscRegions

/-!
# The forest of a simulation inside one ring

In the proof of Graph Minors VIII, (11.2) the forest `Ξ` of the portrait simulation is moved into
`Γ_2` one ring at a time. The paper: "By (8.4) the drawing $\Xi$ of a forest involved in the
simulation relation for the portraits can be chosen to be a subdrawing of $\Gamma_2$, since each
$O$-arc in the foundation used for $\Gamma_2$ is centred, by (8.2)."

For a ring `F_j` of `Γ_2`, let `Ξ_j` be the part of `Ξ` made of its edges in `Σ_j`. By (8.2) the
ring is centred, so the form of (8.4) in `Section11Forest.lean` gives a forest `Ξ'_j` of `Γ_2`
inside `Σ_j` that joins the same vertices of `F_j` as `Ξ_j` (`exists_ring_forest`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface Graph

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- The part of a drawing `Ξ` made of its edges contained in `c`. -/
def xiPart (Ξ : Drawing S) (c : Set S) : Drawing S :=
  Ξ.span ∅ {f | f ∈ Ξ.E ∧ f ⊆ c}

theorem xiPart_isSubdrawing (Ξ : Drawing S) (c : Set S) : (xiPart Ξ c).IsSubdrawing Ξ :=
  Drawing.span_isSubdrawing Ξ _ _

theorem xiPart_E (Ξ : Drawing S) (c : Set S) : (xiPart Ξ c).E = {f | f ∈ Ξ.E ∧ f ⊆ c} := by
  rw [xiPart, Drawing.span_E]
  ext f
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

theorem xiPart_U_subset (Ξ : Drawing S) {c : Set S} : (xiPart Ξ c).U ⊆ closure c := by
  rintro x (hx | hx)
  · rcases hx with ⟨hx, -⟩ | hx
    · exact absurd hx (notMem_empty x)
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
      exact closure_mono hf.1.2 hxf.1
  · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
    exact closure_mono hf.1.2 hxf

/-- An edge of `Ξ` in `c` links the same vertices in `xiPart Ξ c`. -/
theorem xiPart_isLink {Ξ : Drawing S} {c f : Set S} {x y : S} (hl : Ξ.toGraph.IsLink f x y)
    (hfc : f ⊆ c) : (xiPart Ξ c).toGraph.IsLink f x y := by
  have hf : f ∈ (xiPart Ξ c).E := by rw [xiPart_E]; exact ⟨hl.1, hfc⟩
  exact ((xiPart_isSubdrawing Ξ c).isLink_iff hf).mpr hl

/-- **(8.4)**, via (8.2), applied to the part of `Ξ` in the disc of a ring `F_j` of a
foundation: there is a forest `Ξ'` of `Γ` in `Σ_j` with its edges inside `F_j` that joins the same
vertices of `F_j`. -/
theorem exists_ring_forest (hS : IsClosedDisc (univ : Set S)) {Γ : Drawing S} {t : ℕ}
    {F : Fin t → Set S} (hF : IsFoundation Γ univ F) (hprop : Γ.IsProper) (j : Fin t)
    {Ξ : Drawing S} (hΞV : Ξ.V ⊆ Γ.V) {c : Set S} (hc : closure c ⊆ F j ∪ insideSet (F j)) :
    ∃ Ξ' : Drawing S, Ξ'.IsSubdrawing Γ ∧ Ξ'.U ⊆ F j ∪ insideSet (F j) ∧
      (∀ e ∈ Ξ'.E, e ⊆ insideSet (F j)) ∧
      ∀ u ∈ Γ.V ∩ F j, ∀ v ∈ Γ.V ∩ F j,
        (u ∈ (xiPart Ξ c).V ∧ v ∈ (xiPart Ξ c).V ∧
          Nonempty (GraphWalk (xiPart Ξ c).toGraph u v)) ↔
        (u ∈ Ξ'.V ∧ v ∈ Ξ'.V ∧ Nonempty (GraphWalk Ξ'.toGraph u v)) := by
  have hF' := hF
  obtain ⟨C, hboss, -, -, hmin, -⟩ := hF'
  have hnorm : Γ.IsNormal (discBd univ) := by
    rw [GM06.discBd_univ]
    exact hprop
  have hcen : IsCentredOArc Γ univ (F j) :=
    theorem_8_2_proof hS (subset_univ _) hnorm (hboss j) (hmin j).1
  have hXU : (xiPart Ξ c).U ⊆ F j ∪ insideSet (F j) := (xiPart_U_subset Ξ).trans hc
  obtain ⟨Ξ', hsub, -, henc, hiff⟩ := exists_forest_subdrawing_of_vertices hS (subset_univ _)
    hcen (Ξ := xiPart Ξ c) (fun x hx => hΞV ((xiPart_isSubdrawing Ξ c).1 hx.1))
    (fun x hx => by
      rcases hXU hx.1 with h | h
      · exact absurd h hx.2
      · exact h)
  have hU : Ξ'.U ⊆ F j ∪ insideSet (F j) := by
    intro x hx
    by_cases hxF : x ∈ F j
    · exact Or.inl hxF
    · exact Or.inr (henc x ⟨hx, hxF⟩)
  refine ⟨Ξ', hsub, hU, fun e he x hx => ?_, fun u hu v hv => ?_⟩
  · have hxU : x ∈ Ξ'.U \ Ξ'.V := he.2.1 hx
    rcases hU hxU.1 with h | h
    · exact absurd h (Set.disjoint_left.mp
        (Drawing.disjoint_of_isNormal (hF.isNormal j) (hsub.2 he)) hx)
    · exact h
  · have h := hiff u hu v hv
    rw [exists_isGraphComponent_mem_mem_iff, exists_isGraphComponent_mem_mem_iff] at h
    exact h

end GM08
end GraphMinor
