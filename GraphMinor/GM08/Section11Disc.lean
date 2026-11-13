module

public import GraphMinor.GM08.Section11Contract
public import GraphMinor.GM08.Section6
public import GraphMinor.GM08.Section7Grid
public import GraphMinor.GM08.Section11Inside
import GraphMinor.GM11.NiceStatements
import GraphMinor.Surface.Crossing

/-!
# The radial paths meet the circuits of a sleeve in the same cyclic order

To contract a sleeve onto the `r × s` cylinder (Graph Minors VIII, (11.1), page 273) the radial
paths must meet every circuit of the sleeve in the same cyclic order. This is a fact of the plane.
It is used in the form: if two radial paths `P_a, P_b` are consecutive on the circuit `C_j`, they
are consecutive on `C_{j + 1}` (`SleeveDraw.adj_step`, `GraphMinor/GM08/Section11Order.lean`).
This file has the facts about drawings and discs that the proof uses.

The proof is the crossing argument of Graph Minors VI. Suppose not. Going around `C_{j + 1}`
from the first vertex of `P_a` to the first vertex of `P_b`, and back, we meet radial paths `P_c`
and `P_d` other than `P_a, P_b`, one on each side. So on the boundary of the disc bounded by
`C_{j + 1}` the pairs from `{P_a, P_b}` and from `{P_c, P_d}` cross. But inside that disc,
`P_a` and `P_b` are joined by their parts before `C_{j + 1}` and the stretch of `C_j` between them,
and `P_c` and `P_d` are joined in the same way by the other side of `C_j`. These two connected sets
are disjoint, which contradicts `Surface.disc_crossing`.
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Graph Surface GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## Drawings and discs -/

/-- An edge of `D₀` that is not an edge of a subdrawing `C` misses the point set of `C`. -/
theorem disjoint_U_of_not_mem_E {D₀ C : Drawing S} (hC : C.IsSubdrawing D₀) {e : Set S}
    (he : e ∈ D₀.E) (heC : e ∉ C.E) : Disjoint e C.U := by
  refine Set.disjoint_left.mpr fun x hxe hxU => ?_
  have hxV : x ∉ D₀.V := (he.2.1 hxe).2
  rw [C.U_eq] at hxU
  rcases hxU with hx | hx
  · exact hxV (hC.1 hx)
  · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
    have hxf' : x ∈ f := by
      have h := D₀.closure_diff_V (hC.2 hf)
      have hmem : x ∈ closure f \ D₀.V := ⟨hxf, hxV⟩
      rwa [h] at hmem
    exact heC (D₀.edge_eq_of_mem he (hC.2 hf) hxe hxf' ▸ hf)

/-- A vertex of `D₀` on the point set of a subdrawing `C` is a vertex of `C`. -/
theorem mem_V_of_mem_U {D₀ C : Drawing S} (hC : C.IsSubdrawing D₀) {x : S} (hx : x ∈ C.U)
    (hxV : x ∈ D₀.V) : x ∈ C.V := by
  rw [C.U_eq] at hx
  rcases hx with hx | hx
  · exact hx
  · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
    have : x ∈ closure f ∩ C.V := by
      rw [hC.closure_inter_V hf]
      exact ⟨hxf, hxV⟩
    exact this.2

/-- Two subdrawings of `D₀` with no common edge meet only in common vertices. -/
theorem inter_U_subset_V {D₀ A B : Drawing S} (hA : A.IsSubdrawing D₀) (hB : B.IsSubdrawing D₀)
    (hE : Disjoint A.E B.E) : A.U ∩ B.U ⊆ A.V ∩ B.V := by
  rintro x ⟨hxA, hxB⟩
  by_cases hxV : x ∈ D₀.V
  · exact ⟨mem_V_of_mem_U hA hxA hxV, mem_V_of_mem_U hB hxB hxV⟩
  · exfalso
    rw [A.U_eq] at hxA
    rcases hxA with hx | hx
    · exact hxV (hA.1 hx)
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      have hxe' : x ∈ e := by
        have h := D₀.closure_diff_V (hA.2 he)
        have hmem : x ∈ closure e \ D₀.V := ⟨hxe, hxV⟩
        rwa [h] at hmem
      have hnot : e ∉ B.E := fun h => Set.disjoint_left.mp hE he h
      exact Set.disjoint_left.mp (disjoint_U_of_not_mem_E hB (hA.2 he) hnot) hxe' hxB

/-- The point set of a walk drawing lies in the point set of a subdrawing that contains its
vertices and edges. -/
theorem walkDrawing_U_subset [T1Space S] {D₀ C : Drawing S} {u w : S}
    (W : GraphWalk D₀.toGraph u w) (hV : ∀ x ∈ W.support, x ∈ C.V)
    (hE : ∀ e ∈ W.edges, e ∈ C.E) : (walkDrawing D₀ W).U ⊆ C.U := by
  intro x hx
  rcases (mem_walkDrawing_U D₀ W).mp hx with hx | ⟨e, he, hxe⟩
  · exact C.V_subset_U (hV x hx)
  · exact C.closure_subset_U (hE e he) hxe

/-- The point set of a walk drawing is path-connected. -/
theorem isPathConnected_walkDrawing [T2Space S] [ConnectedSpace S] (D₀ : Drawing S) {u w : S}
    (W : GraphWalk D₀.toGraph u w) : IsPathConnected (walkDrawing D₀ W).U := by
  have heq : (walkDrawing D₀ W).U = {x | x ∈ W.support ∨ ∃ e ∈ W.edges, x ∈ closure e} := by
    ext x
    exact mem_walkDrawing_U D₀ W
  rw [heq]
  exact isPathConnected_walk_U W

/-- The point set of a path is path-connected. -/
theorem Drawing.IsPathBetween.isPathConnected_U [T2Space S] [ConnectedSpace S] {P : Drawing S}
    {a b : S} (h : P.IsPathBetween a b) : IsPathConnected P.U := by
  obtain ⟨W, -, hV, hE⟩ := h
  have heq : P.U = {x | x ∈ W.support ∨ ∃ e ∈ W.edges, x ∈ closure e} := by
    rw [P.U_eq, hV, hE]
    ext x
    simp
  rw [heq]
  exact isPathConnected_walk_U W

/-- **A walk stays in a disc until it reaches the boundary.** Let `C` be a subdrawing of `D₀`
whose point set bounds a closed disc `Δ` of the disc `S`. A walk `d 0, …, d a` of `D₀` that starts
in `Δ` and has no vertex on `C` before `d a` lies in `Δ`. -/
theorem seq_mem_disc [T2Space S] (hS : IsClosedDisc (univ : Set S)) {D₀ C : Drawing S}
    (hC : C.IsSubdrawing D₀) {Δ : Set S} (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = C.U)
    (d : ℕ → S) (δ : ℕ → Set S) (a : ℕ)
    (hlink : ∀ k < a, D₀.toGraph.IsLink (δ k) (d k) (d (k + 1))) (h0 : d 0 ∈ Δ)
    (hnot : ∀ k < a, d k ∉ C.V) : ∀ k ≤ a, d k ∈ Δ ∧ (k < a → closure (δ k) ⊆ Δ) := by
  have hopen : IsOpen (discInt Δ) := hΔ.isOpen_discInt (isManifoldPoint_of_univ hS)
  -- One step: from a vertex of `Δ` off `C`, the edge stays in `Δ`.
  have hstep : ∀ k < a, d k ∈ Δ → closure (δ k) ⊆ Δ := by
    intro k hk hdk
    have hl := hlink k hk
    have hdkV : d k ∈ D₀.V := hl.2.1
    have hint : d k ∈ discInt Δ := ⟨hdk, fun h => hnot k hk (mem_V_of_mem_U hC (hbd ▸ h) hdkV)⟩
    have hnotE : δ k ∉ C.E := by
      intro he
      have : d k ∈ closure (δ k) ∩ C.V := by
        rw [hC.closure_inter_V he, hl.2.2.2]
        exact Or.inl rfl
      exact hnot k hk this.2
    have hdisj : Disjoint (δ k) (discBd Δ) := hbd ▸ disjoint_U_of_not_mem_E hC hl.1 hnotE
    have hdkcl : d k ∈ closure (δ k) := by
      have : d k ∈ closure (δ k) ∩ D₀.V := by rw [hl.2.2.2]; exact Or.inl rfl
      exact this.1
    rcases side_of_closedDisc hS (subset_univ Δ) (subset_univ _) hΔ
        hl.1.2.2.1.isConnected.isPreconnected hdisj with hin | hout
    · exact closure_minimal (hin.trans (discInt_subset Δ)) hΔ.isClosed
    · exfalso
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hdkcl _ hopen hint
      exact Set.disjoint_left.mp hout hz2 (discInt_subset Δ hz1)
  intro k hk
  induction k with
  | zero => exact ⟨h0, fun h => hstep 0 h h0⟩
  | succ k ih =>
    obtain ⟨hdk, hcl⟩ := ih (by omega)
    have hl := hlink k (by omega)
    have hmem : d (k + 1) ∈ closure (δ k) := by
      have : d (k + 1) ∈ closure (δ k) ∩ D₀.V := by
        rw [hl.2.2.2]
        exact Or.inr rfl
      exact this.1
    have hdk1 := hcl (by omega) hmem
    exact ⟨hdk1, fun h => hstep (k + 1) h hdk1⟩

end GM08
end GraphMinor
