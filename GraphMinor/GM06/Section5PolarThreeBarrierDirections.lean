module

public import GraphMinor.GM06.Section5PolarCircleDirections
public import GraphMinor.GM06.Section5PolarPathDirection
import GraphMinor.GM06.Section5SmallPolar

/-!
# Three polar directions for a path attached to a cuff

For the local side test in VI (5.7), page 133, the barrier at
an initial vertex consists of its linkage path and its cuff.
The path has one rim direction and the cuff has two. Properness
makes their only common point the initial vertex, which is not
on the rim, so the three directions are distinct. This argument
also applies when the cuff drawing is a single loop.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A path attached at one point of a circle has three distinct
polar barrier directions, with the two circle directions on its two arcs. -/
theorem exists_polar_chart_with_three_barrier_directions
    {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    {Γ P C : Drawing S} (hP : P.IsSubdrawing Γ) (hC : C.IsSubdrawing Γ)
    {v t : S} (f : Curve S) (hf : ParametrizesSet f P.U v t)
    (g h : I → S) (hgh : IsTwoArcs g h) (hg0 : g 0 = v)
    (hCU : range g ∪ range h = C.U) (hPC : P.U ∩ C.U = {v})
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    {O : Set S} (hOo : IsOpen O) (hvO : v ∈ O) :
    ∃ Ψ : C(ClosedUnitDisc, S), IsPolar Γ v Ψ ∧ range Ψ ⊆ O ∧
      (∃ a : I, (0 : ℝ) < a ∧ ∀ x, Ψ x = Φ (discScale a x)) ∧
      ∃ p q c : Circle, p ≠ q ∧ p ≠ c ∧ q ≠ c ∧
        range (polarRayMap Ψ p) ⊆ range g ∧
        range (polarRayMap Ψ c) ⊆ range h ∧
        polarRimMap Ψ q ∈ P.U ∧
        ∀ w : Circle, polarRimMap Ψ w ∈ P.U ∪ C.U ↔ w = p ∨ w = q ∨ w = c := by
  let : T2Space S := hS.2.1
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfar : g 1 ≠ v := fun hh => one_ne_zero (hgh.arc_left.2 (hh.trans hg0.symm))
  have hvN : v ∈ O ∩ ({g 1} : Set S)ᶜ :=
    ⟨hvO, fun hh => hfar (mem_singleton_iff.mp hh).symm⟩
  obtain ⟨a, ha, Ψ, hΨ, hΨN, hscale⟩ := exists_small_polar_chart_with_factor hS hp
    (hOo.inter isClosed_singleton.isOpen_compl) hvN
  have hΨfar : g 1 ∉ range Ψ := fun hh => (hΨN hh).2 rfl
  have hnC : IsGammaNice Γ C.U := isGammaNice_of_frontier hC subset_rfl
    (frontier_subset_closure.trans (by rw [C.isClosed_U.closure_eq]))
  obtain ⟨p, c, hpc, hpg, hch, hcircle⟩ := exists_two_polar_rim_directions_of_two_arcs
    hΨ g h hgh hg0 hΨfar (hCU.symm ▸ C.isClosed_U) (hCU.symm ▸ hnC)
  have hpC : polarRimMap Ψ p ∈ C.U := hCU ▸ (hcircle p).mpr (Or.inl rfl)
  have hcC : polarRimMap Ψ c ∈ C.U := hCU ▸ (hcircle c).mpr (Or.inr rfl)
  obtain ⟨q, hqP, hq⟩ := exists_unique_polar_rim_direction_of_path hP f hf hΨ
  have hsep (w : Circle) (hwP : polarRimMap Ψ w ∈ P.U) (hwC : polarRimMap Ψ w ∈ C.U) : False := by
    have hh : polarRimMap Ψ w ∈ ({v} : Set S) := hPC ▸ ⟨hwP, hwC⟩
    have hv : Ψ (polarDiscPoint 1 w) = Ψ polarCentre :=
      (mem_singleton_iff.mp hh).trans hΨ.centre.symm
    exact polarDiscPoint_one_ne_centre w (hΨ.inj hv)
  have hpq : p ≠ q := by
    intro hh
    have hpP : polarRimMap Ψ p ∈ P.U := by rw [hh]; exact hqP
    exact hsep p hpP hpC
  have hqc : q ≠ c := by
    intro hh
    have hcP : polarRimMap Ψ c ∈ P.U := by rw [← hh]; exact hqP
    exact hsep c hcP hcC
  refine ⟨Ψ, hΨ, fun y hy => (hΨN hy).1, ⟨a, ha, hscale⟩, p, q, c, hpq, hpc, hqc, hpg, hch, hqP, ?_⟩
  intro w
  constructor
  · rintro (hwP | hwC)
    · exact Or.inr (Or.inl (hq w hwP))
    · have hh : polarRimMap Ψ w ∈ range g ∪ range h := hCU.symm ▸ hwC
      rcases (hcircle w).mp hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inr hh)
  · rintro (rfl | rfl | rfl)
    · exact Or.inr hpC
    · exact Or.inl hqP
    · exact Or.inr hcC

end GraphMinor.GM06
