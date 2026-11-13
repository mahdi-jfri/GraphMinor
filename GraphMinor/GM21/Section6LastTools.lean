module

public import GraphMinor.GM21.Section4
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.CutLift
import GraphMinor.Surface.EdgeLoop
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.DiscArcs
import GraphMinor.GM07.Reroute
import GraphMinor.GM07.Section8
import GraphMinor.GM07.FlatEdges
import GraphMinor.GM11.Section6

/-!
# Graph Minors XXI, (6.3), the last step: lines in an `O`-arc, and a disc next to a line

Two tools for the last step of the proof of (6.3).
* `IsOArc.line_compl`: if `A` is a line with ends `x ≠ u` inside an `O`-arc `X`, then the rest of
  `X` (with `x` and `u`) is also a line with ends `x, u`. Both are one of the two arcs of `X` between
  `x` and `u` (`IsOArc.lines`), since the inside of `A` is connected.
* `IsOArc.exists_line_of_mem_componentsIn`: each component of `X \ {x, u}` is the inside of a line
  of `X` with ends `x, u`.
* `exists_parallel_disc`: a line `L` in `Σ` with ends `x ≠ u` in `bd(Σ)`, which meets a closed set
  `W` and `bd(Σ)` only at its ends, has a parallel proper line `F`, and `F ∪ L` bounds a closed disc
  that meets `W ∪ bd(Σ)` only at `x, u`. The disc is half of the lens of `L`
  (`GM07.exists_line_lens`), cut along `L` (`disc_iArc`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Topology GraphMinor.Surface

section lines

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- A line without its ends is nonempty. -/
theorem IsLineWithEnds.nonempty_sdiff {L : Set T} {x u : T} (hL : IsLineWithEnds L x u) :
    (L \ {x, u}).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hcl := GM07.IsLineWithEnds.closure_sdiff hL
  rw [h, closure_empty] at hcl
  exact (hcl ▸ hL.left_mem : x ∈ (∅ : Set T))

/-- The two arcs `L₁, L₂` of an `O`-arc between `x` and `u`, without their ends, are separated. -/
theorem disjoint_closure_sdiff {L₁ L₂ : Set T} {x u : T} (h₁ : IsLineWithEnds L₁ x u)
    (hint : L₁ ∩ L₂ = {x, u}) : Disjoint (closure (L₁ \ {x, u})) (L₂ \ {x, u}) := by
  rw [GM07.IsLineWithEnds.closure_sdiff h₁]
  refine disjoint_left.2 fun z hz1 hz2 => hz2.2 ?_
  rw [← hint]
  exact ⟨hz1, hz2.1⟩

/-- If a line `A` with ends `x ≠ u` lies in the union of two lines `L₁, L₂` with ends `x, u` that
meet only in `x, u`, then `A` is one of them. -/
theorem eq_or_eq_of_subset_union {A L₁ L₂ : Set T} {x u : T} (hA : IsLineWithEnds A x u)
    (h₁ : IsLineWithEnds L₁ x u) (h₂ : IsLineWithEnds L₂ x u) (hint : L₁ ∩ L₂ = {x, u})
    (hsub : A ⊆ L₁ ∪ L₂) : A = L₁ ∨ A = L₂ := by
  have hsub' : A \ {x, u} ⊆ (L₁ \ {x, u}) ∪ (L₂ \ {x, u}) := by
    rintro z ⟨hz, hzxu⟩
    rcases hsub hz with h | h
    exacts [Or.inl ⟨h, hzxu⟩, Or.inr ⟨h, hzxu⟩]
  have hint' : L₂ ∩ L₁ = {x, u} := by rw [inter_comm, hint]
  have d₁ := disjoint_closure_sdiff h₁ hint
  have d₂ : Disjoint (L₁ \ {x, u}) (closure (L₂ \ {x, u})) :=
    (disjoint_closure_sdiff h₂ hint').symm
  have hpre := GM11.IsLineWithEnds.isPreconnected_sdiff_pair hA
  have hApre := (GM07.IsLineWithEnds.isConnected hA).isPreconnected
  rcases IsPreconnected.subset_or_of_separated hpre hsub' d₁ d₂ with h | h
  · left
    refine h₁.eq_of_subset hApre ?_ hA.left_mem hA.right_mem
    rw [← GM07.IsLineWithEnds.closure_sdiff hA, ← GM07.IsLineWithEnds.closure_sdiff h₁]
    exact closure_mono h
  · right
    refine h₂.eq_of_subset hApre ?_ hA.left_mem hA.right_mem
    rw [← GM07.IsLineWithEnds.closure_sdiff hA, ← GM07.IsLineWithEnds.closure_sdiff h₂]
    exact closure_mono h

omit [T2Space T] in
/-- The rest of two lines `L₁ ∪ L₂` that meet only in their ends, after removing the inside of
`L₁`, is `L₂`. -/
theorem union_sdiff_eq {L₁ L₂ : Set T} {x u : T} (h₂ : IsLineWithEnds L₂ x u)
    (hint : L₁ ∩ L₂ = {x, u}) : (L₁ ∪ L₂) \ (L₁ \ {x, u}) = L₂ := by
  ext z
  constructor
  · rintro ⟨hz | hz, hzn⟩
    · have hzxu : z ∈ ({x, u} : Set T) := by
        by_contra h
        exact hzn ⟨hz, h⟩
      rcases hzxu with rfl | h
      · exact h₂.left_mem
      · exact (mem_singleton_iff.mp h) ▸ h₂.right_mem
    · exact hz
  · intro hz
    refine ⟨Or.inr hz, fun hz' => hz'.2 ?_⟩
    rw [← hint]
    exact ⟨hz'.1, hz⟩

/-- **The rest of an `O`-arc after a line.** If `A` is a line with ends `x ≠ u` inside an `O`-arc
`X`, then `X` without the inside of `A` is a line with ends `x, u`, which meets `A` only in `x, u`. -/
theorem IsOArc.line_compl {X A : Set T} {x u : T} (hX : IsOArc X) (hA : IsLineWithEnds A x u)
    (hAX : A ⊆ X) (hxu : x ≠ u) :
    IsLineWithEnds (X \ (A \ {x, u})) x u ∧ A ∩ (X \ (A \ {x, u})) = {x, u} ∧
      A ∪ (X \ (A \ {x, u})) = X := by
  obtain ⟨L₁, L₂, h₁, h₂, hun, hint⟩ := hX.lines (hAX hA.left_mem) (hAX hA.right_mem) hxu
  have hint' : L₂ ∩ L₁ = {x, u} := by rw [inter_comm, hint]
  rcases eq_or_eq_of_subset_union hA h₁ h₂ hint (hun ▸ hAX) with rfl | rfl
  · rw [← hun, union_sdiff_eq h₂ hint]
    exact ⟨h₂, hint, rfl⟩
  · have key : (L₁ ∪ A) \ (A \ {x, u}) = L₁ := by
      rw [union_comm]
      exact union_sdiff_eq h₁ hint'
    rw [← hun, key]
    exact ⟨h₁, hint', union_comm _ _⟩

/-- Each component of an `O`-arc without two of its points `x ≠ u` is the inside of a line of the
`O`-arc with ends `x, u`. -/
theorem IsOArc.exists_line_of_mem_componentsIn {X A : Set T} {x u : T} (hX : IsOArc X)
    (hx : x ∈ X) (hu : u ∈ X) (hxu : x ≠ u) (hA : A ∈ componentsIn (X \ {x, u})) :
    ∃ L, IsLineWithEnds L x u ∧ L ⊆ X ∧ A = L \ {x, u} := by
  obtain ⟨L₁, L₂, h₁, h₂, hun, hint⟩ := hX.lines hx hu hxu
  have hint' : L₂ ∩ L₁ = {x, u} := by rw [inter_comm, hint]
  have hsplit : X \ {x, u} = (L₁ \ {x, u}) ∪ (L₂ \ {x, u}) := by
    rw [← hun, union_sdiff_distrib]
  have hcomp : componentsIn (X \ {x, u}) = {L₁ \ {x, u}, L₂ \ {x, u}} := by
    rw [hsplit]
    exact componentsIn_union_eq_pair (GM11.IsLineWithEnds.isPreconnected_sdiff_pair h₁)
      (GM11.IsLineWithEnds.isPreconnected_sdiff_pair h₂) (IsLineWithEnds.nonempty_sdiff h₁)
      (IsLineWithEnds.nonempty_sdiff h₂) (disjoint_closure_sdiff h₁ hint)
      (disjoint_closure_sdiff h₂ hint').symm
  rw [hcomp] at hA
  rcases hA with rfl | h
  · exact ⟨L₁, h₁, hun ▸ subset_union_left, rfl⟩
  · exact ⟨L₂, h₂, hun ▸ subset_union_right, mem_singleton_iff.mp h⟩

end lines

variable {S : Type} [TopologicalSpace S]

/-- **A disc next to a line.** Let `L` be a line with ends `x ≠ u` in `bd(Σ)`, which meets a closed
set `W` and `bd(Σ)` only at its ends. Then there are a proper line `F` with ends `x, u` and a closed
disc `P` with boundary `F ∪ L`, such that `F` meets `L` only at `x, u`, and `P` meets `W ∪ bd(Σ)` only
at `x, u`. -/
theorem exists_parallel_disc (hS : IsSurface S) {L W : Set S} {x u : S}
    (hL : IsLineWithEnds L x u) (hW : IsClosed W) (hLW : L ∩ W ⊆ {x, u})
    (hLb : L ∩ bd S ⊆ {x, u}) (hx : x ∈ bd S) (hu : u ∈ bd S) (hxu : x ≠ u) :
    ∃ F P : Set S, IsProperLineInSurface F x u ∧ F ∩ L = {x, u} ∧ IsClosedDisc P ∧
      discBd P = F ∪ L ∧ P ∩ (W ∪ bd S) ⊆ {x, u} := by
  have : T2Space S := hS.2.1
  obtain ⟨Δ, -, -, hΔ, hLΔ, hΔW, hxΔ, huΔ, hΔL, -⟩ := GM07.exists_line_lens hS hL hW hLW hLb
  have hLbd : L ∩ discBd Δ = {x, u} := by
    refine Subset.antisymm (fun z hz => hΔL ⟨hz.2, hz.1⟩) ?_
    rintro z (rfl | hz)
    · exact ⟨hL.left_mem, hxΔ⟩
    · exact (mem_singleton_iff.mp hz) ▸ ⟨hL.right_mem, huΔ⟩
  obtain ⟨A₁, A₂, P, P₂, -, hcomp, hP, -, hPun, -, hPbd, -, -⟩ :=
    disc_iArc Δ L x u hΔ hLΔ hxu hL hLbd
  have hA₁ : A₁ ∈ componentsIn (discBd Δ \ {x, u}) := hcomp ▸ Or.inl rfl
  obtain ⟨F, hF, hFbd, rfl⟩ :=
    IsOArc.exists_line_of_mem_componentsIn hΔ.isOArc_discBd hxΔ huΔ hxu hA₁
  have hPΔ : P ⊆ Δ := hPun ▸ subset_union_left
  have hFL : F ∩ L = {x, u} := by
    refine Subset.antisymm (fun z hz => hΔL ⟨hFbd hz.1, hz.2⟩) ?_
    rintro z (rfl | hz)
    · exact ⟨hF.left_mem, hL.left_mem⟩
    · exact (mem_singleton_iff.mp hz) ▸ ⟨hF.right_mem, hL.right_mem⟩
  have hFΔ : F ⊆ Δ := hFbd.trans (discBd_subset Δ)
  refine ⟨F, P, ⟨hF, hx, hu, disjoint_left.2 fun z hz hzb => hz.2 (hΔW ⟨hFΔ hz.1, Or.inr hzb⟩)⟩,
    hFL, hP, ?_, fun z hz => hΔW ⟨hPΔ hz.1, hz.2⟩⟩
  rw [hPbd]
  ext z
  constructor
  · rintro (⟨hz, -⟩ | hz)
    exacts [Or.inl hz, Or.inr hz]
  · rintro (hz | hz)
    · by_cases hzxu : z ∈ ({x, u} : Set S)
      · rcases hzxu with rfl | h
        · exact Or.inr hL.left_mem
        · rw [mem_singleton_iff.mp h]
          exact Or.inr hL.right_mem
      · exact Or.inl ⟨hz, hzxu⟩
    · exact Or.inr hz

end LastStep
end GM21
end GraphMinor
