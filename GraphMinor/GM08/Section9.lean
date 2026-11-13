module

public import GraphMinor.GM08.Section8Defs
import GraphMinor.GM08.Section8Sleeve

/-!
# Graph Minors VIII, Section 9: boundary paths

This file proves the Menger, boss, and ring-containment steps in the proof
of (9.1), pages 269–270. Radial paths meet every circuit by separation,
and counting their intersections with a normal ring gives a path inside it.
It also constructs one-circuit nests for the small sleeve case on page 270.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- With no boundary vertices, every nest is boundary-linked, using no paths. -/
theorem isBoundaryLinkedNest_of_boundary_card_zero {D : Drawing S} {Δ : Set S}
    {r s : ℕ} (N : DrawingNest D Δ r s)
    (hk : (D.V ∩ discBd Δ).ncard = 0) : IsBoundaryLinkedNest D Δ N := by
  refine ⟨fun i => Fin.elim0 (Fin.cast hk i), ?_, ?_⟩
  · intro i
    exact Fin.elim0 (Fin.cast hk i)
  · intro i
    exact Fin.elim0 (Fin.cast hk i)

/-- The Menger step in the proof of Graph Minors VIII (9.1), page 269:
if the first circuit has `ρ` at least the boundary size, the nest is boundary-linked.
Normality of the boundary is used in the disjoint-path theorem. -/
theorem isBoundaryLinkedNest_of_le_circuitRho {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hbd : D.IsNormal (discBd Δ))
    {r s : ℕ} (N : DrawingNest D Δ r s) (hs : 0 < s)
    (hρ : (D.V ∩ discBd Δ).ncard ≤ circuitRho (N.circuit ⟨0, hs⟩)) :
    IsBoundaryLinkedNest D Δ N := by
  obtain ⟨P, u, v, hP, hdis⟩ :=
    exists_disjoint_paths_of_circuitRho hΔ hDU hbd (N.circuit ⟨0, hs⟩) hρ
  exact ⟨P, fun i => ⟨hs, u i, v i, hP i⟩, hdis⟩

/-- The first inequality in the proof of Graph Minors VIII (9.1), page 269:
a nest which is not boundary-linked has first-circuit `ρ` below the boundary size. -/
theorem circuitRho_lt_of_not_isBoundaryLinkedNest {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hbd : D.IsNormal (discBd Δ))
    {r s : ℕ} (N : DrawingNest D Δ r s) (hs : 0 < s)
    (hnot : ¬ IsBoundaryLinkedNest D Δ N) :
    circuitRho (N.circuit ⟨0, hs⟩) < (D.V ∩ discBd Δ).ncard := by
  exact Nat.lt_of_not_ge fun hρ =>
    hnot (isBoundaryLinkedNest_of_le_circuitRho hΔ hDU hbd N hs hρ)

/-- The disc bounded by an earlier nest circuit lies strictly inside a later one.
Boundary points use strict nesting. Interior points use monotonicity of disc interiors. -/
theorem DrawingNest.insideDisc_subset_discInt_of_lt {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) {r s : ℕ} (N : DrawingNest D Δ r s)
    {i j : Fin s} (hij : i < j) : (N.circuit i).ins ⊆ discInt (N.circuit j).ins := by
  intro x hx
  by_cases hbd : x ∈ discBd (N.circuit i).ins
  · exact (insideOArc_iff_mem_discInt hΔ (N.circuit j).isInside).mp
      (N.inside_of_lt hij x ((N.circuit i).isInside.2.2.1 ▸ hbd))
  · exact (N.insideDisc_subset_of_le hΔ (le_of_lt hij)).2 ⟨hx, hbd⟩

/-- Each radial path of a nest meets each circuit: an intermediate circuit separates
its endpoints on the first and last circuits. This justifies restricting the nest in (9.1). -/
theorem DrawingNest.radialPath_meets_circuit {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) {r s : ℕ} (N : DrawingNest D Δ r s)
    (p : Fin r) (j : Fin s) : (N.radialPath p ∩ (N.circuit j).U).Nonempty := by
  have hs : 0 < s := Nat.zero_lt_of_lt j.isLt
  by_cases hj0 : j.val = 0
  · have heq : j = ⟨0, hs⟩ := Fin.ext hj0
    exact heq ▸ N.meets_inner p hs
  by_cases hjlast : j.val = s - 1
  · have heq : j = ⟨s - 1, Nat.sub_lt hs Nat.one_pos⟩ := Fin.ext hjlast
    exact heq ▸ N.meets_outer p hs
  have h0j : (⟨0, hs⟩ : Fin s) < j := Fin.lt_def.mpr (Nat.pos_of_ne_zero hj0)
  have hjl : j < ⟨s - 1, Nat.sub_lt hs Nat.one_pos⟩ := by
    apply Fin.lt_def.mpr
    have := j.isLt
    dsimp
    omega
  obtain ⟨x, hxp, hxC⟩ := N.meets_inner p hs
  obtain ⟨y, hyp, hyC⟩ := N.meets_outer p hs
  have hxint : x ∈ discInt (N.circuit j).ins :=
    (insideOArc_iff_mem_discInt hΔ (N.circuit j).isInside).mp
      (N.inside_of_lt h0j x hxC)
  have hynot : y ∉ (N.circuit j).ins := fun hy =>
    (N.insideDisc_subset_discInt_of_lt hΔ hjl hy).2
      ((N.circuit _).isInside.2.2.1 ▸ hyC)
  by_contra hnone
  have hdis : Disjoint (N.radialPath p) (discBd (N.circuit j).ins) := by
    rw [(N.circuit j).isInside.2.2.1]
    exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hnone)
  rcases side_of_closedDisc hΔ (N.circuit j).isInside.1 (N.radialPath_sub_disc p)
      (N.circuit j).isInside.2.1 (N.isPreconnected_radialPath p) hdis with hin | hout
  · exact hynot (discInt_subset _ (hin hyp))
  · exact Set.disjoint_left.mp hout hxp hxint.1

/-- Restrict a nest to fewer radial paths and an initial sequence of circuits.
The retained paths still meet the new last circuit by separation. -/
def DrawingNest.restrict {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) {r s r' s' : ℕ} (N : DrawingNest D Δ r s)
    (hr : r' ≤ r) (hs : s' ≤ s) : DrawingNest D Δ r' s' where
  circuit j := N.circuit (Fin.castLE hs j)
  inside_of_lt hij := N.inside_of_lt (Fin.lt_def.mpr (Fin.lt_def.mp hij))
  radialPath p := N.radialPath (Fin.castLE hr p)
  isPreconnected_radialPath _p := N.isPreconnected_radialPath _
  radialPath_sub_U _p := N.radialPath_sub_U _
  radialPath_sub_disc _p := N.radialPath_sub_disc _
  pairwise_disjoint_paths _ _ hpq := N.pairwise_disjoint_paths
    (fun heq => hpq (Fin.ext (Fin.mk.inj heq)))
  meets_inner _p _h := N.radialPath_meets_circuit hΔ _ _
  meets_outer _p _h := N.radialPath_meets_circuit hΔ _ _

/-- The boss step in the proof of Graph Minors VIII (9.1), page 269:
when `r, s ≥ k`, a nest that is not boundary-linked starts with a boss.
The strict bound on `ρ` leaves at least `1 + ρ` radial paths and `k` circuits. -/
theorem isBoss_of_not_isBoundaryLinkedNest {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hbd : D.IsNormal (discBd Δ))
    {r s : ℕ} (N : DrawingNest D Δ r s)
    (hr : (D.V ∩ discBd Δ).ncard ≤ r) (hs : (D.V ∩ discBd Δ).ncard ≤ s)
    (hnot : ¬ IsBoundaryLinkedNest D Δ N) :
    ∃ h : 0 < s, IsBoss D Δ (N.circuit ⟨0, h⟩) := by
  have hk : 0 < (D.V ∩ discBd Δ).ncard := Nat.pos_of_ne_zero fun hz =>
    hnot (isBoundaryLinkedNest_of_boundary_card_zero N hz)
  have hspos := lt_of_lt_of_le hk hs
  have hρ := circuitRho_lt_of_not_isBoundaryLinkedNest hΔ hDU hbd N hspos hnot
  refine ⟨hspos, hρ, ?_⟩
  have hr' : 1 + circuitRho (N.circuit ⟨0, hspos⟩) ≤ r := by omega
  refine ⟨N.restrict hΔ hr' hs, ?_⟩
  intro h
  rfl

/-- The pigeonhole step in Graph Minors VIII (9.1), pages 269–270:
if a normal arc meets fewer than `r` vertices, one of the `r` disjoint radial paths misses it. -/
theorem DrawingNest.exists_radialPath_disjoint_of_normal {D : Drawing S} {Δ F : Set S}
    {r s : ℕ} (N : DrawingNest D Δ r s) (hF : D.IsNormal F)
    (hcard : (D.V ∩ F).ncard < r) : ∃ p : Fin r, Disjoint (N.radialPath p) F := by
  classical
  by_contra! hall
  have hmeet : ∀ p : Fin r, (N.radialPath p ∩ F).Nonempty :=
    fun p => Set.not_disjoint_iff.mp (hall p)
  choose x hx using hmeet
  have hxV : ∀ p, x p ∈ D.V := fun p => hF ⟨(hx p).2, N.radialPath_sub_U p (hx p).1⟩
  have hinj : Function.Injective x := by
    intro p q heq
    by_contra hpq
    exact Set.disjoint_left.mp (N.pairwise_disjoint_paths hpq)
      ⟨(hx p).1, hxV p⟩ ⟨heq ▸ (hx q).1, hxV p⟩
  have hsub : range x ⊆ D.V ∩ F := by
    rintro _ ⟨p, rfl⟩
    exact ⟨hxV p, (hx p).2⟩
  have hle := Set.ncard_le_ncard hsub (D.finite_V.subset inter_subset_left)
  rw [Set.ncard_range_of_injective hinj, Nat.card_fin] at hle
  exact (Nat.not_le_of_lt hcard) hle

/-- In the situation of (9.1), a radial path missing the enclosing ring stays inside it.
It therefore witnesses that every circuit, including the last, meets the inside of the ring. -/
theorem DrawingNest.exists_radialPath_inside {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) {r s : ℕ} (N : DrawingNest D Δ r s) (hs : 0 < s)
    (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hFn : D.IsNormal F)
    (henc : OArcEncloses Δ F (N.circuit ⟨0, hs⟩).U)
    (hcard : (D.V ∩ F).ncard < r) :
    ∃ p : Fin r, SetInsideOArc Δ F (N.radialPath p) ∧
      ∀ j : Fin s, ∃ x ∈ (N.circuit j).U, InsideOArc Δ F x := by
  obtain ⟨p, hp⟩ := N.exists_radialPath_disjoint_of_normal hFn hcard
  obtain ⟨B, hB, -⟩ := disc_oArc Δ F hΔ hFΔ hFo
  have hdis : Disjoint (N.radialPath p) (discBd B) := hB.2.2.1 ▸ hp
  obtain ⟨x, hxp, hxC⟩ := N.meets_inner p hs
  have hxint : x ∈ discInt B :=
    (insideOArc_iff_mem_discInt hΔ hB).mp
      (henc x ⟨hxC, fun hxF => Set.disjoint_left.mp hp hxp hxF⟩)
  have hpint : N.radialPath p ⊆ discInt B := by
    rcases side_of_closedDisc hΔ hB.1 (N.radialPath_sub_disc p) hB.2.1
        (N.isPreconnected_radialPath p) hdis with hin | hout
    · exact hin
    · exact False.elim (Set.disjoint_left.mp hout hxp hxint.1)
  have hin : SetInsideOArc Δ F (N.radialPath p) := fun y hy =>
    (insideOArc_iff_mem_discInt hΔ hB).mpr (hpint hy)
  refine ⟨p, hin, fun j => ?_⟩
  obtain ⟨y, hyp, hyC⟩ := N.radialPath_meets_circuit hΔ p j
  exact ⟨y, hyC, hin y hyp⟩

/-- The containment step reused from (8.2) in the proof of (9.1), page 270.
An enclosing normal ring with few vertices misses each early circuit covered by the
stated counting inequality. The sphere calculation is transported to any closed disc. -/
theorem DrawingNest.circuit_inside_of_card_lt {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    {r s : ℕ} (N : DrawingNest D Δ r s) (hs : 0 < s)
    (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hFn : D.IsNormal F)
    (henc : OArcEncloses Δ F (N.circuit ⟨0, hs⟩).U)
    (hcard : (D.V ∩ F).ncard < r) (j : Fin s)
    (hj : (D.V ∩ F).ncard < 1 + 2 * (s - 1 - j.val)) :
    SetInsideOArc Δ F (N.circuit j).U := by
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D', -, hD'U, hD'V, -, -, -, -⟩ := sc.exists_transport_drawing hΔ D hDU
  have hΔ' := (sc.disc_f Subset.rfl hΔ).1
  let N' := sc.pushNest hΔ hDU hD'U hD'V N
  have hFn' := (sc.isNormal_f_iff hDU hD'U hD'V hFΔ).mpr hFn
  have hcard' := sc.ncard_V_inter_f hDU hD'V hFΔ
  have henc' : OArcEncloses (f '' Δ) (f '' F) (N'.circuit ⟨0, hs⟩).U :=
    (sc.oArcEncloses_f_iff hΔ hFΔ hFo (N.circuit ⟨0, hs⟩).U_sub_disc).mpr henc
  have hres := (nest_circuits_inside_oArc_sphere hΔ' sc.infty_notMem
    (image_mono hFΔ) (sc.oArc_f hFΔ hFo) hFn' hs N' henc'
    (hcard' ▸ hcard)).2 j (hcard' ▸ hj)
  exact (sc.setInsideOArc_f_iff hΔ hFΔ hFo (N.circuit j).U_sub_disc).mp hres

/-- A circuit with `r` distinct chosen points gives a one-circuit nest.
Each radial path is a singleton, so it meets both the first and last circuit.
In particular, two distinct vertices of a circuit give a `(2, 1)`-nest. -/
def DiscCircuit.oneCircuitNest {D : Drawing S} {Δ : Set S}
    (C : DiscCircuit D Δ) {r : ℕ} (p : Fin r → S)
    (hp : ∀ i, p i ∈ C.U) (hinj : Function.Injective p) : DrawingNest D Δ r 1 where
  circuit _ := C
  inside_of_lt := by
    intro i j hij
    exact False.elim ((not_lt_of_ge (Fin.le_iff_val_le_val.mpr (Nat.zero_le _)))
      (Fin.fin_one_eq_zero j ▸ hij))
  radialPath i := {p i}
  isPreconnected_radialPath _ := isPreconnected_singleton
  radialPath_sub_U i := singleton_subset_iff.mpr (C.U_sub_drawing (hp i))
  radialPath_sub_disc i := singleton_subset_iff.mpr (C.U_sub_disc (hp i))
  pairwise_disjoint_paths := by
    intro i j hne
    apply Set.disjoint_left.mpr
    rintro x ⟨hxi, _⟩ ⟨hxj, _⟩
    exact hne (hinj ((mem_singleton_iff.mp hxi).symm.trans (mem_singleton_iff.mp hxj)))
  meets_inner i _ := ⟨p i, mem_singleton _, hp i⟩
  meets_outer i _ := ⟨p i, mem_singleton _, hp i⟩

end GraphMinor.GM08
