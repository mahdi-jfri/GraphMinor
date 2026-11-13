module

public import GraphMinor.GM08.Section11Data
import GraphMinor.GM08.Section11

/-!
# Graph Minors VIII, (11.2)

A simulation of a portrait derived from `(G_1, τ_1)` in a portrait derived from `(G_2, τ_2)`
gives a simulation of `(G_1, τ_1)` in `(G_2, τ_2)`.

The paper's proof (page 273) moves the forest `Ξ` of the simulation of the portraits into `Γ_2`
by (8.4) and (8.2), and leaves the rest to the reader. Here (8.4) and (8.2) are used inside each
ring of `Γ_2` that is not the image of a ring of `Γ_1` (`exists_ring_forest`, in
`Section11Xi.lean`), and the rest is done as follows.

1. From the two portraits and their simulation we get the data of `ModelSetting`
   (`exists_modelSetting`, in `Section11Data.lean`).
2. These data give a simulation of the graph of `Γ_1` in the graph of `Γ_2`
   (`ModelSetting.isMinorModel`, in `Section11Model.lean`).
3. We move this simulation to `G_1` and `G_2` along the isomorphisms of the drawings
   (`Section11Transport.lean`), and check that the roots `τ_1` go to the roots `τ_2`. The roots
   are drawn at the lists `α` of the portraits, and condition (vii) of a simulation of portraits
   puts `α_2(n)` in the tree `σ(α_1(n))`.

The paper leaves this verification to the reader. The form of (8.4) used here asks for less than
the printed (8.4). The paper's proof cites condition (vii) for the insides of the rings, but the
conditions used there are (viii) and (iv). See the corrections to the proof of (11.2) in
`corrections/GM08.md`.
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface Graph

universe u u' v'

variable {S : Type u} [TopologicalSpace S]

/-- The points of `U ∩ bd S` are nodes of a portrait, since the cells miss `bd S`. -/
theorem QPortrait.alpha_mem_N {Q : Type*} (P : QPortrait Q S) {x : S} (hx : x ∈ P.α) :
    x ∈ P.painting.N := by
  have hxU : x ∈ P.painting.U ∩ bd S := by
    rw [← P.α_set]
    exact hx
  by_contra hN
  have hc : connectedComponentIn (P.painting.U \ P.painting.N) x ∈ P.painting.cells :=
    ⟨x, ⟨hxU.1, hN⟩, rfl⟩
  exact Set.disjoint_left.mp (P.painting.cell_disjoint_bd _ hc)
    (mem_connectedComponentIn ⟨hxU.1, hN⟩) hxU.2

/-- **(11.2)** (page 273): "(11.2) *Let* $(G_1, \tau_1), (G_2, \tau_2) \in \mathscr{A}(k)$, *both
with index* $k$. *Let* $P_i$ *be a* $\mathbf{Q}_{k - 1}$*-portrait derived from* $(G_i, \tau_i)$
$(i = 1, 2)$. *If* $P_1$ *is simulated in* $P_2$ *then* $(G_1, \tau_1)$ *is simulated in*
$(G_2, \tau_2)$." -/
theorem theorem_11_2_proof {α : Type u'} {β : Type v'} {k : ℕ} (hS : IsClosedDisc (univ : Set S))
    {X₁ X₂ : RootedGraph α β} (h₁ : X₁ ∈ discRootedClassA S k) (h₂ : X₂ ∈ discRootedClassA S k)
    (hk₁ : X₁.index = k) (hk₂ : X₂.index = k)
    {P₁ P₂ : QPortrait (QKElem α β S ((k : ℤ) - 1)) S} (hP₁ : IsDerivedPortrait X₁ P₁)
    (hP₂ : IsDerivedPortrait X₂ P₂)
    (hsim : IsPortraitSimulatedIn (qkLE S ((k : ℤ) - 1)) P₁ P₂) :
    IsRootedGraphSimulatedIn X₁ X₂ := by
  haveI := t2Space_of_univ hS
  haveI : Nonempty S := by
    obtain ⟨f⟩ := hS
    have h0 : (0 : EuclideanPlane) ∈ ClosedUnitDisc := by simp [ClosedUnitDisc]
    exact ⟨(f ⟨0, h0⟩).1⟩
  obtain ⟨gd₁, t₁, F₁, hP₁⟩ := hP₁
  obtain ⟨gd₂, t₂, F₂, hP₂⟩ := hP₂
  obtain ⟨Ξ, σv, σe, hsim⟩ := hsim
  obtain ⟨Ξ', π, R₁, R₂, ηR, εR, partner, hM⟩ := exists_modelSetting hS hP₁ hP₂ hsim
  have m := (isGraphSimulation_comp gd₁.iso.isGraphBij.isMinorModel hM.isMinorModel).pullHost
    gd₂.iso.isGraphBij id
  refine ⟨_, _, m, ?_⟩
  have hl₁ : X₁.τ.length = k := hk₁
  have hl₂ : X₂.τ.length = k := hk₂
  have hlen : X₂.τ.length = X₁.τ.length := by omega
  refine ⟨hlen, fun i => ?_, fun i j => ?_⟩
  · have hn₂ : i.val < X₂.τ.length := i.2
    have hn₁ : i.val < X₁.τ.length := by omega
    have hα₁ := hP₁.roots
    have hα₂ := hP₂.roots
    have ha₁ : i.val < P₁.α.length := by omega
    have ha₂ : i.val < P₂.α.length := by omega
    have hr₁ : gd₁.iso.fv X₁.τ[i.val] = P₁.α[i.val] := by
      rw [Iso.fv_of_mem (X₁.τ_subset _ (List.getElem_mem _))]
      exact hα₁.2 i.val hn₁ ha₁
    have hr₂ : gd₂.iso.fv X₂.τ[i.val] = P₂.α[i.val] := by
      rw [Iso.fv_of_mem (X₂.τ_subset _ (List.getElem_mem _))]
      exact hα₂.2 i.val hn₂ ha₂
    have hN : P₁.α[i.val] ∈ ringNodes gd₁.drawing F₁ := by
      rw [← hP₁.nodes]
      exact P₁.alpha_mem_N (List.getElem_mem _)
    have hσ : P₂.α[i.val] ∈ V(σv P₁.α[i.val]) := hsim.2.2.2.2.2.2.2.2.2.2.1.2 i.val ha₁ ha₂
    simp only [Fin.getElem_fin, Fin.val_cast]
    refine ⟨X₂.τ_subset _ (List.getElem_mem _), mem_biUnion (x := gd₁.iso.fv X₁.τ[i.val]) rfl ?_⟩
    rw [hr₁, hr₂]
    exact hM.partA_subset_mv _ ⟨hN, hσ⟩
  · simp only [Fin.getElem_fin, Fin.val_cast]
    rw [h₂.2.2.getElem_inj_iff, h₁.2.2.getElem_inj_iff]

end GM08
end GraphMinor
