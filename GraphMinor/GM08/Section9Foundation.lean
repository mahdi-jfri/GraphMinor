module

public import GraphMinor.GM08.Section9
import GraphMinor.GM08.Section8Sleeve
import GraphMinor.GM08.Section6
import GraphMinor.GM11.OArcCircuit

/-!
# Minimal rings used by a foundation in VIII (9.1)

The foundation step of (9.1), page 269, uses the minimum rings from
Section 6, pages 263–267. A ring exists because the normal boundary of
the ambient disc is a candidate. Among rings attaining the minimum
boundary size, minimize the number of enclosed edges.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Every circuit has a ring when the disc boundary is normal.
The boundary of the ambient disc gives a candidate for the minimum defining `ρ`. -/
theorem DiscCircuit.exists_isCRing {D : Drawing S} {Δ : Set S}
    (C : DiscCircuit D Δ) (hΔ : IsClosedDisc Δ) (hbd : D.IsNormal (discBd Δ)) :
    ∃ F, IsCRing C F := by
  obtain ⟨B, hB, huniq⟩ := disc_oArc Δ (discBd Δ) hΔ (discBd_subset Δ) hΔ.isOArc_discBd
  have hBΔ : IsInsideDisc Δ (discBd Δ) Δ := (huniq Δ Subset.rfl hΔ rfl).symm ▸ hB
  have henc : OArcEncloses Δ (discBd Δ) C.U :=
    (oArcEncloses_iff_subset hΔ hBΔ).mpr C.U_sub_disc
  have hne : {n : ℕ | ∃ F : Set S, F ⊆ Δ ∧ IsOArc F ∧ D.IsNormal F ∧
      OArcEncloses Δ F C.U ∧ (D.V ∩ F).ncard = n}.Nonempty :=
    ⟨(D.V ∩ discBd Δ).ncard, discBd Δ, discBd_subset Δ, hΔ.isOArc_discBd, hbd, henc, rfl⟩
  exact Nat.sInf_mem hne

/-- Every circuit has a minimal ring. The drawing has finitely many edges,
so a ring enclosing the fewest edges is minimal under inclusion. -/
theorem DiscCircuit.exists_isMinimalCRing {D : Drawing S} {Δ : Set S}
    (C : DiscCircuit D Δ) (hΔ : IsClosedDisc Δ) (hbd : D.IsNormal (discBd Δ)) :
    ∃ F, IsMinimalCRing C F := by
  classical
  obtain ⟨F₀, hF₀⟩ := C.exists_isCRing hΔ hbd
  have hex : ∃ n : ℕ, ∃ F, IsCRing C F ∧ (edgesInsideOArc D Δ F).ncard = n :=
    ⟨_, F₀, hF₀, rfl⟩
  obtain ⟨F, hF, hcard⟩ := Nat.find_spec hex
  refine ⟨F, hF, fun F' hF' hss => ?_⟩
  have hmin := Nat.find_min' hex ⟨F', hF', rfl⟩
  have hfin : (edgesInsideOArc D Δ F).Finite := D.finite_edges.subset fun e he => he.1
  have hlt := Set.ncard_lt_ncard hss hfin
  omega

/-- The circuits enclosed by a foundation's minimal rings are bosses,
and each ring has fewer vertices than the boundary of the ambient disc.
This is the size bound used in the sleeve reduction of (9.1). -/
theorem IsFoundation.ring_card_lt_boundary_card {D : Drawing S} {Δ : Set S}
    {t : ℕ} {F : Fin t → Set S} (h : IsFoundation D Δ F) (i : Fin t) :
    (D.V ∩ F i).ncard < (D.V ∩ discBd Δ).ncard := by
  obtain ⟨C, hboss, _, _, hmin, _⟩ := h
  rw [(hmin i).1.2.2.2.2]
  exact (hboss i).rho_lt

/-- A boss lies strictly inside each of its rings. Apply the containment
count of (8.2) to the first circuit of its defining nest. This is used
when passing from the boss edge set to a foundation ring in (9.1). -/
theorem IsBoss.inside_cRing {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) {C : DiscCircuit D Δ}
    (hboss : IsBoss D Δ C) (hF : IsCRing C F) : SetInsideOArc Δ F C.U := by
  have hk : 0 < (D.V ∩ discBd Δ).ncard := Nat.zero_lt_of_lt hboss.rho_lt
  obtain ⟨N, hN⟩ := hboss.exists_nest
  have hC : N.circuit ⟨0, hk⟩ = C := hN hk
  have henc : OArcEncloses Δ F (N.circuit ⟨0, hk⟩).U := hC.symm ▸ hF.2.2.2.1
  have hcard : (D.V ∩ F).ncard < 1 + circuitRho C := by
    rw [hF.2.2.2.2]
    omega
  have hbound : (D.V ∩ F).ncard < 1 + 2 * ((D.V ∩ discBd Δ).ncard - 1 - 0) := by
    rw [hF.2.2.2.2]
    have := hboss.rho_lt
    omega
  have hin := N.circuit_inside_of_card_lt hΔ hDU hk hF.1 hF.2.1 hF.2.2.1
    henc hcard ⟨0, hk⟩ hbound
  exact hC ▸ hin

/-- The edges of a circuit drawing of a boss belong to its foundation edge set.
A minimal ring exists and the whole circuit is strictly inside that ring. -/
theorem IsBoss.circuit_edges_subset_bossDelta {D B : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hbd : D.IsNormal (discBd Δ))
    {C : DiscCircuit D Δ} (hboss : IsBoss D Δ C)
    (hBD : B.IsSubdrawing D) (hBU : B.U = C.U) : B.E ⊆ bossDelta D Δ C := by
  obtain ⟨F, hF⟩ := C.exists_isMinimalCRing hΔ hbd
  have hin := hboss.inside_cRing hΔ hDU hF.1
  intro e he
  apply Set.mem_iUnion.mpr
  refine ⟨F, Set.mem_iUnion.mpr ⟨hF, ?_⟩⟩
  exact ⟨hBD.2 he, fun x hx => hin x (hBU ▸ (he.2.1 hx).1)⟩

/-- If every edge of a circuit subdrawing is inside a ring, the ring encloses
the whole circuit. Vertices follow by taking closures of incident edges.
This is the last geometric step in the foundation coverage argument of (9.1). -/
theorem encloses_circuit_of_edges_inside {D B : Drawing S} [T2Space S]
    {Δ F : Set S} (hΔ : IsClosedDisc Δ) (hFΔ : F ⊆ Δ) (hFo : IsOArc F)
    (hBD : B.IsSubdrawing D) (hB : B.IsCircuit)
    (hedges : B.E ⊆ edgesInsideOArc D Δ F) : OArcEncloses Δ F B.U := by
  obtain ⟨K, hK, _⟩ := disc_oArc Δ F hΔ hFΔ hFo
  have hcl : ∀ e ∈ B.E, closure e ⊆ K := by
    intro e he
    exact closure_minimal (fun x hx =>
      ((insideOArc_iff_mem_discInt hΔ hK).mp ((hedges he).2 x hx)).1) hK.2.1.isClosed
  apply (oArcEncloses_iff_subset hΔ hK).mpr
  intro x hx
  by_cases hxV : x ∈ B.V
  · rcases exists_loop_or_two_edges_of_isCircuit hBD hB hxV with hloop | htwo
    · obtain ⟨e, he, hl⟩ := hloop
      have hxcl : x ∈ closure e := by
        have hm : x ∈ closure e ∩ D.V := by rw [hl.2.2.2]; simp
        exact hm.1
      exact hcl e he hxcl
    · obtain ⟨e, he, _, _, _, hxcl, _⟩ := htwo
      exact hcl e he hxcl
  · obtain ⟨e, he, hxe⟩ := B.exists_edge_of_mem hx hxV
    exact hcl e he (subset_closure hxe)

/-- By VIII (6.6), the union defining the foundation edge set is the edge
set enclosed by any one minimal ring. This is the equality used in the
foundation step of (9.1), page 269. -/
theorem bossDelta_eq_edgesInside_of_isMinimalCRing {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) {C : DiscCircuit D Δ} (hF : IsMinimalCRing C F) :
    bossDelta D Δ C = edgesInsideOArc D Δ F := by
  ext e
  simp only [bossDelta, Set.mem_iUnion]
  constructor
  · rintro ⟨F', hF', he⟩
    rwa [theorem_6_6_proof hΔ hF hF']
  · intro he
    exact ⟨F, hF, he⟩

/-- Every boss is enclosed by a chosen foundation ring. Its circuit edges
belong to its foundation edge set, which is covered by one of the selected
bosses. Minimum-ring uniqueness turns that coverage into enclosure by the
particular ring chosen for that boss. This is the foundation step in the
proof of VIII (9.1), page 269. -/
theorem IsFoundation.encloses_boss {D : Drawing S} [T2Space S] [ConnectedSpace S]
    {Δ : Set S} (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (hbd : D.IsNormal (discBd Δ)) {t : ℕ} {F : Fin t → Set S}
    (h : IsFoundation D Δ F) {C : DiscCircuit D Δ} (hboss : IsBoss D Δ C) :
    ∃ i, OArcEncloses Δ (F i) C.U := by
  obtain ⟨Cs, _, _, hcover, hmin, _⟩ := h
  obtain ⟨i, hi⟩ := hcover C hboss
  obtain ⟨B, hB, hBD, hBU⟩ := GM11.exists_circuit_of_oArc C.isOArc_U C.U_sub_drawing
  have hCE : B.E ⊆ bossDelta D Δ C :=
    hboss.circuit_edges_subset_bossDelta hΔ hDU hbd hBD hBU
  rw [bossDelta_eq_edgesInside_of_isMinimalCRing hΔ (hmin i)] at hi
  have henc := encloses_circuit_of_edges_inside hΔ (hmin i).1.1 (hmin i).1.2.1
    hBD hB (hCE.trans hi)
  exact ⟨i, hBU ▸ henc⟩

end GraphMinor.GM08
