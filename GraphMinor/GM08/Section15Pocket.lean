module

public import GraphMinor.GM08.Section15PinchedFrame
public import GraphMinor.GM11.Walks
public import GraphMinor.GM07.CuffFinger
public import GraphMinor.GM12.Section3SolidEmbedding
public import GraphMinor.GM12.Section3OneDiscComplement
public import GraphMinor.Surface.DiscMerge
public import GraphMinor.GM11.Theorem75
public import GraphMinor.GM11.Regions
public import GraphMinor.GM11.RadialAccess
public import GraphMinor.GM11.ArcDrawings
public import GraphMinor.GM11.RadialBasics
public import GraphMinor.GM07.CylinderCap
public import GraphMinor.Surface.ArcErase
public import GraphMinor.Surface.ArcInPath

/-!
# Graph Minors VIII, printed (15.1): the largest pocket at an end

This file starts Lemma 4 of the proof of the printed (15.1) in `Section15PrintedFinal.lean`.

Let $(\Gamma, F_1, F_2)$ be a tube and $A = F_1 \cap V(\Gamma)$. An *$A$-hoop* is a
$\Gamma$-normal hoop $L \subseteq \Sigma(F_1, F_2)$ with $L \cap V(\Gamma) = A$. Its *pocket*
is the part of $\Gamma$ in $\Sigma(F_1, L)$. We choose an $A$-hoop $L$ whose pocket has the most
vertices plus edges. Then no $A$-hoop $F$ to the right of $L$ cuts off any point of $\Gamma$
from the right of $L$: all of $\Gamma$ in $\Sigma(L, F_2)$ lies in $\Sigma(F, F_2)$
(`Tube.exists_maximal_pocket`). This is Property 2 of Lemma 4.

Next, given a line in the capped sphere from a point of $L$ to a vertex $v \notin L$ that
meets $L$'s left disc, the drawing and the right disc of $F_2$ only at its two ends, a thin
finger along the line turns $L$ into a hoop $L^+$ with vertex set $(L \cap V(\Gamma)) \cup \{v\}$
that leaves all of $\Gamma$ in $\Sigma(L, F_2)$ on its right (`Tube.exists_exposure_of_line`).
This is Property 3 of Lemma 4, once the line is found.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Graph GraphMinor.Surface

universe u v w

variable {S : Type w} [TopologicalSpace S]

/-- The size of the pocket of a hoop `H`: the number of vertices plus the number of edges of
`τ.Γ` in `Σ(F₁, H)`. -/
noncomputable def Tube.pocketSize (τ : Tube S) (H : Set S) : ℕ :=
  (τ.Γ.V ∩ cylinderBetween τ.F₁ H).ncard + {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ H}.ncard

theorem Tube.pocketSize_le (τ : Tube S) (H : Set S) :
    τ.pocketSize H ≤ τ.Γ.V.ncard + τ.Γ.E.ncard :=
  Nat.add_le_add (ncard_le_ncard inter_subset_left τ.Γ.finite_V)
    (ncard_le_ncard (fun _ h => h.1) τ.Γ.finite_edges)

/-- **Lemma 4, the choice of `L'` and Property 2.** There is an `A`-hoop `L`, where
`A = F₁ ∩ V(Γ)`, such that every `A`-hoop `F` to the right of `L` leaves all of `Γ` in
`Σ(L, F₂)` on its right. We take `L` with the largest pocket. A hoop `F` to its right has a
pocket that contains the pocket of `L`, so the two pockets are equal. A point of `Γ` between `L`
and `F` is then in both bands, so it lies on `L`; it is a vertex of `A ⊆ F`, since `L` is normal. -/
theorem Tube.exists_maximal_pocket (τ : Tube S) :
    ∃ L : Set S, IsHoop L ∧ τ.Γ.IsNormal L ∧ L ⊆ cylinderBetween τ.F₁ τ.F₂ ∧
      L ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V ∧
      ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween L τ.F₂ →
        F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V →
        τ.Γ.U ∩ cylinderBetween L τ.F₂ ⊆ cylinderBetween F τ.F₂ := by
  classical
  have : T2Space S := τ.t2Space
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂
    τ.laminar
  have hS := τ.isCylinder
  set P : Set (Set S) := {H | IsHoop H ∧ τ.Γ.IsNormal H ∧ H ⊆ cylinderBetween τ.F₁ τ.F₂ ∧
    H ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V} with hP
  have hF₁P : τ.F₁ ∈ P :=
    ⟨τ.isHoop_F₁, τ.isNormal_F₁, subset_cylinderBetween_left τ.laminar, rfl⟩
  have hfin : (τ.pocketSize '' P).Finite :=
    (finite_Iic (τ.Γ.V.ncard + τ.Γ.E.ncard)).subset (by
      rintro _ ⟨H, -, rfl⟩; exact τ.pocketSize_le H)
  obtain ⟨_, ⟨L, hLP, rfl⟩, hmax⟩ :=
    Set.exists_max_image (τ.pocketSize '' P) id hfin ⟨_, τ.F₁, hF₁P, rfl⟩
  obtain ⟨hL, hNL, hLsub, hLV⟩ := hLP
  refine ⟨L, hL, hNL, hLsub, hLV, fun F hF hNF hFsub hFV => ?_⟩
  obtain ⟨h1L, hL2⟩ :=
    (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hL hle).mp hLsub
  obtain ⟨hLF, hF2⟩ :=
    (cap.hoop_subset_cylinderBetween_iff hS hL τ.isHoop_F₂ hF hL2).mp hFsub
  have hF₁F : cap.disc₁ hS.1 τ.isHoop_F₁ ⊆ cap.disc₁ hS.1 hF := h1L.trans hLF
  have hFP : F ∈ P := ⟨hF, hNF,
    (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hF hle).mpr ⟨hF₁F, hF2⟩,
    hFV⟩
  have hmono : cylinderBetween τ.F₁ L ⊆ cylinderBetween τ.F₁ F :=
    cap.cylinderBetween_mono hS τ.isHoop_F₁ τ.isHoop_F₁ hL hF Subset.rfl h1L hLF
  -- The two pockets are equal.
  have hVsub : τ.Γ.V ∩ cylinderBetween τ.F₁ L ⊆ τ.Γ.V ∩ cylinderBetween τ.F₁ F :=
    inter_subset_inter_right _ hmono
  have hEsub : {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ L} ⊆
      {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ F} := fun e he => ⟨he.1, he.2.trans hmono⟩
  have hVfin : (τ.Γ.V ∩ cylinderBetween τ.F₁ F).Finite := τ.Γ.finite_V.subset inter_subset_left
  have hEfin : {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ F}.Finite :=
    τ.Γ.finite_edges.subset fun _ h => h.1
  have hc1 := ncard_le_ncard hVsub hVfin
  have hc2 := ncard_le_ncard hEsub hEfin
  have hsize : τ.pocketSize F ≤ τ.pocketSize L := hmax _ ⟨F, hFP, rfl⟩
  have hVeq : τ.Γ.V ∩ cylinderBetween τ.F₁ L = τ.Γ.V ∩ cylinderBetween τ.F₁ F :=
    eq_of_subset_of_ncard_le hVsub (by unfold Tube.pocketSize at hsize; omega) hVfin
  have hEeq : {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ L} =
      {e ∈ τ.Γ.E | e ⊆ cylinderBetween τ.F₁ F} :=
    eq_of_subset_of_ncard_le hEsub (by unfold Tube.pocketSize at hsize; omega) hEfin
  have hinter : cylinderBetween τ.F₁ L ∩ cylinderBetween L τ.F₂ = L :=
    cap.cylinderBetween_inter hS τ.isHoop_F₁ hL τ.isHoop_F₂ h1L hL2
  have hunion : cylinderBetween τ.F₁ F ∪ cylinderBetween F τ.F₂ =
      cylinderBetween τ.F₁ τ.F₂ :=
    cap.cylinderBetween_union hS τ.isHoop_F₁ hF τ.isHoop_F₂ hF₁F hF2
  rintro x ⟨hxU, hxR⟩
  by_contra hxF
  have hxB : x ∈ cylinderBetween τ.F₁ F := by
    have := hunion ▸ τ.U_subset hxU
    exact this.resolve_right hxF
  by_cases hxV : x ∈ τ.Γ.V
  · have hxL : x ∈ cylinderBetween τ.F₁ L := (hVeq.symm.subset ⟨hxV, hxB⟩).2
    have hxLL : x ∈ L ∩ τ.Γ.V := ⟨hinter ▸ ⟨hxL, hxR⟩, hxV⟩
    rw [hLV, ← hFV] at hxLL
    exact hxF (subset_cylinderBetween_left (areLaminarHoops_of_subset_cylinderBetween
      τ.laminar hF hFP.2.2.1).2 hxLL.1)
  · obtain ⟨e, he, hxe⟩ := τ.Γ.exists_edge_of_mem hxU hxV
    have hesub : e ⊆ cylinderBetween τ.F₁ τ.F₂ := by
      have := τ.U_subset
      exact fun y hy => this (he.2.1 hy).1
    rcases edge_subset_cylinderBetween_left_or_right τ.Γ τ.laminar hF hFP.2.2.1 hNF he hesub
      with ⟨hl, -⟩ | ⟨hr, -⟩
    · have heL : e ⊆ cylinderBetween τ.F₁ L := (hEeq.symm.subset ⟨he, hl⟩).2
      exact hxV (hNL ⟨hinter ▸ ⟨heL hxe, hxR⟩, hxU⟩)
    · exact hxF (hr hxe)

/-- **Lemma 4, Property 3, from a line.** Let `L` be a normal hoop in `Σ(F₁, F₂)` and `v` a vertex
off `L`. Suppose that, in the capped sphere, a line runs from a point `p` of `L` to `v`, and meets
the left disc of `L` only at `p`, and the drawing and the right disc of `F₂` only at `v`. Then a
thin finger of the left disc of `L` along this line (`GM07.exists_finger`) is the left disc of a
normal hoop `H` with `H ∩ V(Γ) = (L ∩ V(Γ)) ∪ {v}`, between `L` and `F₂`, and every point of `Γ`
between `L` and `F₂` is also between `H` and `F₂`. The reason for the last claim: the finger
meets the drawing only in the left disc of `L` and at `v`, and all of these points lie on `H`. -/
theorem Tube.exists_exposure_of_line (τ : Tube S) (cap : CylinderSphereCap S)
    (hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    {L : Set S} (hL : IsHoop L) (hNL : τ.Γ.IsNormal L) (hLsub : L ⊆ cylinderBetween τ.F₁ τ.F₂)
    {v : S} (hv : v ∈ τ.Γ.V) (hvL : v ∉ L) {ℓ : Set cap.Z} {p : cap.Z}
    (hℓ : IsLineWithEnds ℓ p (cap.j v)) (hp : p ∈ cap.j '' L)
    (hℓΔ : ℓ ∩ cap.disc₁ τ.isCylinder.1 hL ⊆ {p})
    (hℓZ : ℓ ∩ (cap.j '' τ.Γ.U ∪ cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂) ⊆ {cap.j v}) :
    ∃ H : Set S, IsHoop H ∧ τ.Γ.IsNormal H ∧ H ⊆ cylinderBetween L τ.F₂ ∧
      H ∩ τ.Γ.V = insert v (L ∩ τ.Γ.V) ∧
      τ.Γ.U ∩ cylinderBetween L τ.F₂ ⊆ cylinderBetween H τ.F₂ := by
  classical
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have hZ := cap.isClosedSurface
  have : T2Space cap.Z := cap.t2Space_Z
  have hman : ∀ x : cap.Z, IsManifoldPoint x := cap.isManifoldPoint_Z
  have hinj := cap.inj
  set Δ := cap.disc₁ hS.1 hL with hΔdef
  set G₁ := cap.disc₁ hS.1 τ.isHoop_F₂ with hG₁def
  set D₂ := cap.disc₂ hS.1 τ.isHoop_F₂ with hD₂def
  obtain ⟨hΔ, -, hbΔ, -, -, hcapL, hD₁L, -⟩ := cap.disc₁_disc₂_spec hS.1 hL
  obtain ⟨-, hG₂, -, -, hcupG, hcapG, -, hD₂G⟩ := cap.disc₁_disc₂_spec hS.1 τ.isHoop_F₂
  obtain ⟨-, hL2⟩ :=
    (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hL hle).mp hLsub
  have hjU : ∀ x ∈ τ.Γ.U, cap.j x ∈ G₁ := fun x hx => by
    have h := τ.U_subset hx
    rw [cap.cylinderBetween_eq_of_disc₁_subset hS τ.isHoop_F₁ τ.isHoop_F₂ hle] at h
    exact h.1
  set Zc : Set cap.Z := cap.j '' τ.Γ.U ∪ D₂ with hZcdef
  have hZc : IsClosed Zc :=
    (cap.isClosedEmbedding.isClosedMap _ τ.Γ.isClosed_U).union hG₂.isClosed
  have hjvp : cap.j v ≠ p := by
    rintro h
    obtain ⟨y, hy, hyp⟩ := hp
    exact hvL (hinj (hyp.trans h.symm) ▸ hy)
  have hjvΔ : cap.j v ∉ Δ := fun h => hjvp (hℓΔ ⟨hℓ.right_mem, h⟩)
  have hpbd : p ∈ discBd Δ := hbΔ ▸ hp
  have hjvZc : cap.j v ∈ Zc := Or.inl ⟨v, τ.Γ.V_subset_U hv, rfl⟩
  obtain ⟨Δ₁, hΔ₁, hΔΔ₁, hvΔ₁, hbsub, hbΔ₁Z, -, hΔ₁Z⟩ :=
    GM07.exists_finger hZ.isSurface hΔ hℓ hjvp.symm hpbd hℓΔ hjvΔ hZc hjvZc hℓZ
      (disjoint_left.mpr fun x _ hx => hx (hZ.2.2 x))
  -- Points of the finger in `Zc` lie in `range j`.
  have hbdΔ_range : discBd Δ ⊆ range cap.j := by
    rw [hbΔ]; exact image_subset_range _ _
  have hbd_range : discBd Δ₁ ⊆ range cap.j := by
    refine cap.subset_range_of_disjoint_discInts ?_ ?_
    · refine disjoint_left.mpr fun x hx hxi => ?_
      have h1 : x ∈ discInt Δ := discInt_mono hman cap.isClosedDisc_D₁ hD₁L hxi
      have h2 : x ∈ discInt Δ₁ := discInt_mono hman hΔ hΔΔ₁ h1
      exact h2.2 hx
    · refine disjoint_left.mpr fun x hx hxi => ?_
      have hxZ : x ∈ Zc := Or.inr (hD₂G (discInt_subset _ hxi))
      have hxr : x ∈ range cap.j := by
        rcases hbΔ₁Z ⟨hx, hxZ⟩ with ⟨h, -⟩ | h
        · exact hbdΔ_range h
        · rw [mem_singleton_iff.mp h]; exact mem_range_self v
      exact disjoint_left.mp cap.disjoint_range_discInt_D₂ hxr hxi
  set H : Set S := cap.j ⁻¹' discBd Δ₁ with hHdef
  have hjH : cap.j '' H = discBd Δ₁ := image_preimage_eq_of_subset hbd_range
  have hHo : IsOArc H :=
    GM12.isOArc_preimage_isEmbedding cap.isClosedEmbedding.isEmbedding hΔ₁.isOArc_discBd
      hbd_range
  obtain ⟨hE, hbE⟩ := GM12.isClosedDisc_closure_compl_of_sphere hZ cap.isSphere hΔ₁
  set E : Set cap.Z := closure (univ \ Δ₁) with hEdef
  have hcup : Δ₁ ∪ E = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ Δ₁
    · exact Or.inl hx
    · exact Or.inr (subset_closure ⟨mem_univ x, hx⟩)
  have hbdE : discBd Δ₁ ⊆ E := hbE ▸ Surface.discBd_subset E
  have hcap : Δ₁ ∩ E = discBd Δ₁ := by
    refine Subset.antisymm (fun x ⟨hx, hxE⟩ => ?_) fun x hx => ⟨Surface.discBd_subset _ hx, hbdE hx⟩
    by_contra hxb
    have hd : Disjoint (discInt Δ₁) E :=
      Disjoint.closure_right (disjoint_left.mpr fun y hy hy' => hy'.2 hy.1)
        (hΔ₁.isOpen_discInt hman)
    exact disjoint_left.mp hd ⟨hx, hxb⟩ hxE
  have hD₂E : cap.D₂ ⊆ E := by
    refine cap.isClosedDisc_D₂.subset_closure_discInt.trans (closure_mono fun x hxi => ?_)
    refine ⟨mem_univ x, fun hxΔ₁ => ?_⟩
    have hxD₂ : x ∈ D₂ := hD₂G (discInt_subset _ hxi)
    have hxr : x ∈ range cap.j := by
      rcases hΔ₁Z ⟨hxΔ₁, Or.inr hxD₂⟩ with h | h
      · have : x ∈ G₁ ∩ D₂ := ⟨hL2 h, hxD₂⟩
        rw [hcapG] at this
        exact image_subset_range _ _ this
      · rw [mem_singleton_iff.mp h]; exact mem_range_self v
    exact disjoint_left.mp cap.disjoint_range_discInt_D₂ hxr hxi
  obtain ⟨hHh, hd1, hd2⟩ := cap.isHoop_of_discs hS.1 (Homeomorph.refl cap.Z) (ι := cap.j)
    (fun _ => rfl) (P₁ := cap.D₁) (P₂ := cap.D₂) (by simp) (by simp) hHo hΔ₁ hE
    (by rw [hjH]) (by rw [hbE, hjH]) hcup (by rw [hcap, hjH]) (hD₁L.trans hΔΔ₁) hD₂E
  simp only [Homeomorph.refl_apply, id_eq, image_id'] at hd1 hd2
  have hΔ₁G : Δ₁ ⊆ G₁ := fun x hx => by
    by_contra hxG
    have hxD₂ : x ∈ D₂ := (hcupG ▸ mem_univ x : x ∈ G₁ ∪ D₂).resolve_left hxG
    rcases hΔ₁Z ⟨hx, Or.inr hxD₂⟩ with h | h
    · exact hxG (hL2 h)
    · rw [mem_singleton_iff.mp h] at hxG
      exact hxG (hjU v (τ.Γ.V_subset_U hv))
  have hle₁ : cap.disc₁ hS.1 hL ⊆ cap.disc₁ hS.1 hHh := hd1 ▸ hΔΔ₁
  have hle₂ : cap.disc₁ hS.1 hHh ⊆ cap.disc₁ hS.1 τ.isHoop_F₂ := hd1 ▸ hΔ₁G
  -- Points of `H` on the drawing.
  have hHU : ∀ x ∈ H, x ∈ τ.Γ.U → x ∈ L ∨ x = v := fun x hxH hxU => by
    rcases hbΔ₁Z ⟨hxH, Or.inl ⟨x, hxU, rfl⟩⟩ with ⟨h, -⟩ | h
    · rw [hbΔ] at h
      obtain ⟨y, hy, hyx⟩ := h
      exact Or.inl (hinj hyx ▸ hy)
    · exact Or.inr (hinj (mem_singleton_iff.mp h))
  refine ⟨H, hHh, fun x ⟨hxH, hxU⟩ => ?_, ?_, ?_, ?_⟩
  · rcases hHU x hxH hxU with h | rfl
    · exact hNL ⟨h, hxU⟩
    · exact hv
  · exact (cap.hoop_subset_cylinderBetween_iff hS hL τ.isHoop_F₂ hHh hL2).mpr ⟨hle₁, hle₂⟩
  · ext x
    constructor
    · rintro ⟨hxH, hxV⟩
      rcases hHU x hxH (τ.Γ.V_subset_U hxV) with h | rfl
      · exact Or.inr ⟨h, hxV⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hxL, hxV⟩)
      · exact ⟨hvΔ₁, hv⟩
      · refine ⟨hbsub ⟨hbΔ ▸ mem_image_of_mem _ hxL, Or.inl ⟨x, τ.Γ.V_subset_U hxV, rfl⟩⟩, hxV⟩
  · rintro x ⟨hxU, hxB⟩
    rw [cap.cylinderBetween_eq_of_disc₁_subset hS hL τ.isHoop_F₂ hL2] at hxB
    rw [cap.cylinderBetween_eq_of_disc₁_subset hS hHh τ.isHoop_F₂ hle₂, hd2]
    refine ⟨hxB.1, ?_⟩
    by_cases hx : cap.j x ∈ Δ₁
    · rcases hΔ₁Z ⟨hx, Or.inl ⟨x, hxU, rfl⟩⟩ with h | h
      · have hb : cap.j x ∈ discBd Δ := by
          rw [hbΔ, ← hcapL]; exact ⟨h, hxB.2⟩
        exact hbdE (hbsub ⟨hb, Or.inl ⟨x, hxU, rfl⟩⟩)
      · rw [mem_singleton_iff.mp h]; exact hbdE hvΔ₁
    · exact subset_closure ⟨mem_univ _, hx⟩

/-- **Lemma 4, Property 4.** Let `L` be an `A`-hoop with the largest pocket, as in
`Tube.exists_maximal_pocket`, and let `H ⊆ Σ(L, F₂)` be a hoop through a vertex `v ∉ A`. Then no
normal hoop `F ⊆ Σ(H, F₂)` has vertex set `A`. Otherwise `v`, which is in `Γ` between `L` and
`F₂`, would lie in `Σ(F, F₂)` by the choice of `L`, and also in `Σ(L, F)`, since `H` lies between
`L` and `F`. So `v` would lie on `F`, and `v ∈ F ∩ V(Γ) = A`. -/
theorem Tube.ne_of_maximal_pocket (τ : Tube S) {L H : Set S} (hL : IsHoop L)
    (hLsub : L ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hmax : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween L τ.F₂ →
      F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V → τ.Γ.U ∩ cylinderBetween L τ.F₂ ⊆ cylinderBetween F τ.F₂)
    (hH : IsHoop H) (hHsub : H ⊆ cylinderBetween L τ.F₂) {v : S} (hvH : v ∈ H)
    (hvV : v ∈ τ.Γ.V) (hvA : v ∉ τ.F₁ ∩ τ.Γ.V) {F : Set S} (hF : IsHoop F)
    (hNF : τ.Γ.IsNormal F) (hFsub : F ⊆ cylinderBetween H τ.F₂) :
    F ∩ τ.Γ.V ≠ τ.F₁ ∩ τ.Γ.V := by
  intro hFV
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented hS τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  obtain ⟨-, hL2⟩ :=
    (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hL hle).mp hLsub
  obtain ⟨hLH, hH2⟩ := (cap.hoop_subset_cylinderBetween_iff hS hL τ.isHoop_F₂ hH hL2).mp hHsub
  obtain ⟨hHF, hF2⟩ := (cap.hoop_subset_cylinderBetween_iff hS hH τ.isHoop_F₂ hF hH2).mp hFsub
  have hFsub' : F ⊆ cylinderBetween L τ.F₂ :=
    (cap.hoop_subset_cylinderBetween_iff hS hL τ.isHoop_F₂ hF hL2).mpr ⟨hLH.trans hHF, hF2⟩
  have hvU : v ∈ τ.Γ.U := τ.Γ.V_subset_U hvV
  have hvLF₂ : v ∈ cylinderBetween L τ.F₂ := hHsub hvH
  have hvF₂ : v ∈ cylinderBetween F τ.F₂ := hmax F hF hNF hFsub' hFV ⟨hvU, hvLF₂⟩
  have hvHF : v ∈ cylinderBetween H F :=
    subset_cylinderBetween_left ((cap.areLaminarHoops_iff hS hH hF).mpr (Or.inl hHF)) hvH
  have hHF_sub : cylinderBetween H F ⊆ cylinderBetween τ.F₁ F :=
    cap.cylinderBetween_mono hS τ.isHoop_F₁ hH hF hF
      (((cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hL hle).mp hLsub).1.trans
        hLH) hHF Subset.rfl
  have hvF : v ∈ F := by
    rw [← cap.cylinderBetween_inter hS τ.isHoop_F₁ hF τ.isHoop_F₂
      ((((cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hL hle).mp
        hLsub).1.trans hLH).trans hHF) hF2]
    exact ⟨hHF_sub hvHF, hvF₂⟩
  exact hvA (hFV ▸ ⟨hvF, hvV⟩)

/-- **Lemma 4, Property 3, from a region.** Let `L` be a normal hoop in `Σ(F₁, F₂)` and `v` a
vertex between `L` and `F₂`, off `L`. Suppose that, in the capped sphere, a connected set `W`
misses the drawing and `F₂`, meets the inside of the left disc of `L`, and has `v` in its closure.
Then the exposure hoop of `Tube.exists_exposure_of_line` exists.

We draw `F₂` as a cycle and add it to the drawing. The component `r` of the rest of the sphere
that holds `W` is a region of this drawing, and it misses the right disc of `F₂`, since it meets
the left disc of `L` and does not cross `F₂`. A path runs from `v` into `r` (`GM11.exists_path_into_region`)
and then inside `r` to a point of `W` inside the left disc of `L`. An arc in this path from `v`,
stopped where it first meets the left disc of `L`, is the line that
`Tube.exists_exposure_of_line` needs. It meets that disc at a point of `L`, since the inside of the
disc is open. -/
theorem Tube.exists_exposure_of_closure (τ : Tube S) (cap : CylinderSphereCap S)
    (hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    {L : Set S} (hL : IsHoop L) (hNL : τ.Γ.IsNormal L) (hLsub : L ⊆ cylinderBetween τ.F₁ τ.F₂)
    {v : S} (hv : v ∈ τ.Γ.V) (hvL : v ∉ L) (hvR : v ∈ cylinderBetween L τ.F₂)
    {W : Set cap.Z} (hW : IsPreconnected W)
    (hWU : Disjoint W (cap.j '' τ.Γ.U ∪ cap.j '' τ.F₂))
    (hWΔ : (W ∩ discInt (cap.disc₁ τ.isCylinder.1 hL)).Nonempty) (hvW : cap.j v ∈ closure W) :
    ∃ H : Set S, IsHoop H ∧ τ.Γ.IsNormal H ∧ H ⊆ cylinderBetween L τ.F₂ ∧
      H ∩ τ.Γ.V = insert v (L ∩ τ.Γ.V) ∧
      τ.Γ.U ∩ cylinderBetween L τ.F₂ ⊆ cylinderBetween H τ.F₂ := by
  classical
  have : T2Space S := τ.t2Space
  have : Nonempty S := ⟨v⟩
  have hS := τ.isCylinder
  have : CompactSpace S := hS.1.1
  have hZ := cap.isClosedSurface
  have : T2Space cap.Z := cap.t2Space_Z
  have hman : ∀ x : cap.Z, IsManifoldPoint x := cap.isManifoldPoint_Z
  have hlc : LocallyConnectedSpace cap.Z := GM11.IsClosedSurface.locallyConnectedSpace hZ
  have hinj := cap.inj
  set Δ := cap.disc₁ hS.1 hL with hΔdef
  set D₂ := cap.disc₂ hS.1 τ.isHoop_F₂ with hD₂def
  obtain ⟨hΔ, -, hbΔ, -, -, -, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hL
  obtain ⟨-, hG₂, -, hbG₂, -, hcapG, -, -⟩ := cap.disc₁_disc₂_spec hS.1 τ.isHoop_F₂
  obtain ⟨-, hL2⟩ :=
    (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hL hle).mp hLsub
  -- The drawing `N`: the image of `Γ` together with a cycle on `F₂`.
  obtain ⟨Γz, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding τ.Γ
  have hUz : Γz.U = cap.j '' τ.Γ.U := by simpa using hm.image_U.symm
  have hVz : Γz.V = cap.j '' τ.Γ.V := by simpa using hm.image_V.symm
  obtain ⟨z₀, hz₀⟩ : (cap.j '' τ.F₂).Nonempty := by
    obtain ⟨φ⟩ := hG₂.isOArc_discBd
    have h : ((φ 1 : discBd D₂) : cap.Z) ∈ discBd D₂ := (φ 1).2
    exact ⟨_, hbG₂.subset h⟩
  obtain ⟨C, hCU, hCV⟩ := GM11.exists_drawing_on_oArc (hbG₂ ▸ hG₂.isOArc_discBd)
    (((τ.Γ.finite_V.subset inter_subset_right).image cap.j).insert z₀)
    (insert_nonempty _ _) (insert_subset hz₀ (image_mono inter_subset_left))
  have hmeet : Γz.U ∩ C.U ⊆ Γz.V ∩ C.V := by
    rintro _ ⟨hx, hxC⟩
    rw [hUz] at hx
    rw [hCU] at hxC
    obtain ⟨x, hxU, rfl⟩ := hx
    obtain ⟨y, hyF, hyx⟩ := hxC
    have hxF : x ∈ τ.F₂ := hinj hyx ▸ hyF
    have hxV : x ∈ τ.Γ.V := τ.isNormal_F₂ ⟨hxF, hxU⟩
    exact ⟨hVz ▸ mem_image_of_mem _ hxV, hCV ▸ Or.inr ⟨x, ⟨hxF, hxV⟩, rfl⟩⟩
  set N : Drawing cap.Z := Γz.glue C hmeet with hNdef
  have hNU : N.U = cap.j '' τ.Γ.U ∪ cap.j '' τ.F₂ := by
    show Γz.U ∪ C.U = _
    rw [hUz, hCU]
  -- The region `r` of `N` that holds `W`.
  obtain ⟨w₀, hw₀W, hw₀Δ⟩ := hWΔ
  have hWN : W ⊆ univ \ N.U := fun x hx =>
    ⟨mem_univ _, fun h => disjoint_left.mp hWU hx (hNU ▸ h)⟩
  set r := connectedComponentIn (univ \ N.U) w₀ with hrdef
  have hrR : r ∈ N.R := ⟨w₀, hWN hw₀W, rfl⟩
  have hWr : W ⊆ r := hW.subset_connectedComponentIn hw₀W hWN
  have hro : IsOpen r :=
    (isOpen_univ.sdiff N.isClosed_U).connectedComponentIn
  have hrc : IsPreconnected r := isPreconnected_connectedComponentIn
  have hrN : Disjoint r N.U := disjoint_left.mpr fun x hx hxN =>
    (connectedComponentIn_subset _ _ hx).2 hxN
  have hjU_N : cap.j '' τ.Γ.U ⊆ N.U := hNU ▸ subset_union_left
  have hjF_N : cap.j '' τ.F₂ ⊆ N.U := hNU ▸ subset_union_right
  -- `r` misses the right disc of `F₂`.
  have hw₀D₂ : w₀ ∉ D₂ := by
    intro h
    have h1 : w₀ ∈ cap.disc₁ hS.1 τ.isHoop_F₂ := hL2 (discInt_subset _ hw₀Δ)
    exact disjoint_left.mp hrN (hWr hw₀W) (hjF_N (hcapG ▸ ⟨h1, h⟩))
  have hrD₂ : Disjoint r D₂ := by
    have hsub : r ⊆ discInt D₂ ∪ D₂ᶜ := fun x hx => by
      by_cases h : x ∈ D₂
      · refine Or.inl ⟨h, fun hb => disjoint_left.mp hrN hx (hjF_N ?_)⟩
        rwa [hbG₂] at hb
      · exact Or.inr h
    have h2 : r ⊆ D₂ᶜ := hrc.subset_right_of_subset_union (hG₂.isOpen_discInt hman)
      hG₂.isClosed.isOpen_compl
      (disjoint_left.mpr fun x hx hx' => hx' (discInt_subset _ hx)) hsub
      ⟨w₀, mem_connectedComponentIn (hWN hw₀W), hw₀D₂⟩
    exact disjoint_left.mpr fun x hx hx' => h2 hx hx'
  -- `v` is outside the left disc of `L`.
  have hjvΔ : cap.j v ∉ Δ := by
    intro h
    have h2 : cap.j v ∈ cap.disc₂ hS.1 hL := by
      have := hvR
      rw [cap.cylinderBetween_eq_of_disc₁_subset hS hL τ.isHoop_F₂ hL2] at this
      exact this.2
    obtain ⟨-, -, -, -, -, hcapL, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hL
    have hx : cap.j v ∈ cap.j '' L := hcapL ▸ (⟨h, h2⟩ : cap.j v ∈ Δ ∩ cap.disc₂ hS.1 hL)
    obtain ⟨y, hy, hyv⟩ := hx
    exact hvL (hinj hyv ▸ hy)
  -- A path from `v` into `r`, then to `w₀`.
  have hvN : cap.j v ∈ N.V := Or.inl (hVz ▸ mem_image_of_mem _ hv)
  obtain ⟨g, hg, hg0, hgt⟩ :=
    GM11.exists_path_into_region hZ N hvN hrR (closure_mono hWr hvW)
  have hpc : IsPathConnected r :=
    GM11.isPathConnected_of_isOpen hZ hro hrc ⟨w₀, hWr hw₀W⟩
  have hg1 : g 1 ∈ r := hgt 1 (by simp)
  let P₁ : Path (cap.j v) (g 1) := ⟨⟨g, hg⟩, hg0, rfl⟩
  obtain ⟨M, hM⟩ := hpc.joinedIn _ hg1 _ (hWr hw₀W)
  let P := P₁.trans M
  have hvw : cap.j v ≠ w₀ := fun h => hjvΔ (h ▸ discInt_subset _ hw₀Δ)
  obtain ⟨e, hec, hei, he0, he1, her⟩ :=
    exists_arc_of_path (γ := P) P.continuous (by simpa [P] using hvw)
  rw [P.source] at he0
  rw [P.target] at he1
  have her' : ∀ t, 0 < t → e t ∈ r := fun t ht => by
    have hne : e t ≠ cap.j v := fun h => (ne_of_gt ht) (hei (h.trans he0.symm))
    have hy : e t ∈ range P := her ⟨t, rfl⟩
    rw [show range P = range P₁ ∪ range M by simp only [P, Path.trans_range]] at hy
    rcases hy with ⟨s, hs⟩ | ⟨s, hs⟩
    · by_cases hs0 : s = 0
      · subst hs0; exact absurd (hs.symm.trans hg0) hne
      · exact hs ▸ hgt s (unitInterval.pos_iff_ne_zero.mpr hs0)
    · exact hs ▸ hM s
  -- The first time `e` meets `Δ`.
  have hTc : IsClosed (e ⁻¹' Δ) := hΔ.isClosed.preimage hec
  obtain ⟨t₀, ht₀T, ht₀min⟩ :=
    hTc.isCompact.exists_isLeast ⟨1, by simp [he1, discInt_subset _ hw₀Δ]⟩
  have ht₀ : (0 : unitInterval) < t₀ := by
    refine unitInterval.pos_iff_ne_zero.mpr fun h => hjvΔ ?_
    rw [← he0, ← h]; exact ht₀T
  have hpbd : e t₀ ∈ discBd Δ := by
    by_contra hn
    have hint : e t₀ ∈ discInt Δ := ⟨ht₀T, hn⟩
    have hev : ∀ᶠ t in 𝓝[<] t₀, e t ∈ discInt Δ :=
      nhdsWithin_le_nhds ((hΔ.isOpen_discInt hman).preimage hec |>.mem_nhds hint)
    have : (𝓝[<] t₀).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht₀⟩
    obtain ⟨t, ht, htlt⟩ := (hev.and self_mem_nhdsWithin).exists
    exact absurd (ht₀min (discInt_subset Δ ht)) (not_le.mpr htlt)
  have hne0 : (0 : unitInterval) ≠ t₀ := ne_of_lt ht₀
  have harc : IsArcMap (subArc e 0 t₀) := IsArcMap.sub ⟨hec, hei⟩ hne0
  have hline := harc.isLineWithEnds
  rw [subArc_zero, subArc_one, he0, range_subArc e (le_of_lt ht₀)] at hline
  refine τ.exists_exposure_of_line cap hle hL hNL hLsub hv hvL hline.symm
    (hbΔ ▸ hpbd) ?_ ?_
  · rintro _ ⟨⟨t, ht, rfl⟩, hx⟩
    exact le_antisymm ht.2 (ht₀min hx) ▸ rfl
  · rintro _ ⟨⟨t, ht, rfl⟩, hx⟩
    by_cases h0 : t = 0
    · subst h0; exact he0
    have htr := her' t (unitInterval.pos_iff_ne_zero.mpr h0)
    rcases hx with hx | hx
    · exact absurd (hjU_N hx) (disjoint_left.mp hrN htr)
    · exact absurd hx (disjoint_left.mp hrD₂ htr)

/-- **A hoop from a disc.** A closed disc `Δ₁` of the capped sphere between the left disc of a
hoop `L ⊆ Σ(F₁, F₂)` and the left disc of `F₂` is the left disc of a hoop `H` between `L` and
`F₂`, with `j(H) = bd Δ₁`. The boundary of `Δ₁` misses the insides of both caps, so it is the
image of an `O`-arc `H` of the cylinder, and `H` is a hoop since it separates the caps. -/
theorem Tube.exists_hoop_of_disc (τ : Tube S) (cap : CylinderSphereCap S)
    (hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    {L : Set S} (hL : IsHoop L) (hLsub : L ⊆ cylinderBetween τ.F₁ τ.F₂)
    {Δ₁ : Set cap.Z} (hΔ₁ : IsClosedDisc Δ₁) (h1 : cap.disc₁ τ.isCylinder.1 hL ⊆ Δ₁)
    (h2 : Δ₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂) :
    ∃ H : Set S, ∃ hH : IsHoop H, cap.j '' H = discBd Δ₁ ∧
      cap.disc₁ τ.isCylinder.1 hH = Δ₁ ∧ cap.disc₂ τ.isCylinder.1 hH = closure (univ \ Δ₁) ∧
      H ⊆ cylinderBetween L τ.F₂ := by
  classical
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have hZ := cap.isClosedSurface
  have : T2Space cap.Z := cap.t2Space_Z
  have hman : ∀ x : cap.Z, IsManifoldPoint x := cap.isManifoldPoint_Z
  obtain ⟨-, -, -, -, -, -, hD₁L, -⟩ := cap.disc₁_disc₂_spec hS.1 hL
  obtain ⟨-, -, -, -, -, hcapG, -, hD₂G⟩ := cap.disc₁_disc₂_spec hS.1 τ.isHoop_F₂
  obtain ⟨-, hL2⟩ :=
    (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hL hle).mp hLsub
  have hD₂int : Disjoint Δ₁ (discInt cap.D₂) := disjoint_left.mpr fun x hx hxi => by
    have hxj : x ∈ cap.j '' τ.F₂ := hcapG ▸ ⟨h2 hx, hD₂G (discInt_subset _ hxi)⟩
    exact disjoint_left.mp cap.disjoint_range_discInt_D₂ (image_subset_range _ _ hxj) hxi
  have hbd_range : discBd Δ₁ ⊆ range cap.j := by
    refine cap.subset_range_of_disjoint_discInts ?_ ?_
    · refine disjoint_left.mpr fun x hx hxi => ?_
      have h3 : x ∈ discInt Δ₁ := discInt_mono hman cap.isClosedDisc_D₁ (hD₁L.trans h1) hxi
      exact h3.2 hx
    · exact disjoint_left.mpr fun x hx hxi =>
        disjoint_left.mp hD₂int (Surface.discBd_subset _ hx) hxi
  set H : Set S := cap.j ⁻¹' discBd Δ₁ with hHdef
  have hjH : cap.j '' H = discBd Δ₁ := image_preimage_eq_of_subset hbd_range
  have hHo : IsOArc H :=
    GM12.isOArc_preimage_isEmbedding cap.isClosedEmbedding.isEmbedding hΔ₁.isOArc_discBd
      hbd_range
  obtain ⟨hE, hbE⟩ := GM12.isClosedDisc_closure_compl_of_sphere hZ cap.isSphere hΔ₁
  set E : Set cap.Z := closure (univ \ Δ₁) with hEdef
  have hcup : Δ₁ ∪ E = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ Δ₁
    · exact Or.inl hx
    · exact Or.inr (subset_closure ⟨mem_univ x, hx⟩)
  have hbdE : discBd Δ₁ ⊆ E := hbE ▸ Surface.discBd_subset E
  have hcap : Δ₁ ∩ E = discBd Δ₁ := by
    refine Subset.antisymm (fun x ⟨hx, hxE⟩ => ?_) fun x hx => ⟨Surface.discBd_subset _ hx, hbdE hx⟩
    by_contra hxb
    have hd : Disjoint (discInt Δ₁) E :=
      Disjoint.closure_right (disjoint_left.mpr fun y hy hy' => hy'.2 hy.1)
        (hΔ₁.isOpen_discInt hman)
    exact disjoint_left.mp hd ⟨hx, hxb⟩ hxE
  have hD₂E : cap.D₂ ⊆ E := by
    refine cap.isClosedDisc_D₂.subset_closure_discInt.trans (closure_mono fun x hxi => ?_)
    exact ⟨mem_univ x, fun hxΔ₁ => disjoint_left.mp hD₂int hxΔ₁ hxi⟩
  obtain ⟨hHh, hd1, hd2⟩ := cap.isHoop_of_discs hS.1 (Homeomorph.refl cap.Z) (ι := cap.j)
    (fun _ => rfl) (P₁ := cap.D₁) (P₂ := cap.D₂) (by simp) (by simp) hHo hΔ₁ hE
    (by rw [hjH]) (by rw [hbE, hjH]) hcup (by rw [hcap, hjH]) (hD₁L.trans h1) hD₂E
  simp only [Homeomorph.refl_apply, id_eq, image_id'] at hd1 hd2
  refine ⟨H, hHh, hjH, hd1, hd2, ?_⟩
  exact (cap.hoop_subset_cylinderBetween_iff hS hL τ.isHoop_F₂ hHh hL2).mpr
    ⟨hd1 ▸ h1, hd1 ▸ h2⟩

/-- **Property 2 in the capped sphere.** Let `L` be an `A`-hoop with the largest pocket
(`Tube.exists_maximal_pocket`), where every hoop has at least `|A|` vertices. Let `Δ₁` be a closed
disc between the left disc of `L` and the left disc of `F₂` whose boundary meets the drawing only
on `L`. Then every point of the drawing inside `Δ₁` lies in the left disc of `L`.

The reason: `Δ₁` is the left disc of a hoop `H` (`Tube.exists_hoop_of_disc`). The vertices of `H`
are vertices of `L`, so they lie in `A`, and there are at least `|A|` of them, so `H` is an
`A`-hoop. By the choice of `L`, every point of the drawing between `L` and `F₂` is between `H` and
`F₂`, so it is not inside `Δ₁`. The other points of the drawing are between `F₁` and `L`. -/
theorem Tube.image_inter_discInt_subset_of_maximal (τ : Tube S) (cap : CylinderSphereCap S)
    (hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    (hmin : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (τ.F₁ ∩ τ.Γ.V).ncard ≤ (F ∩ τ.Γ.V).ncard)
    {L : Set S} (hL : IsHoop L) (hNL : τ.Γ.IsNormal L) (hLsub : L ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hLV : L ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V)
    (hmax : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween L τ.F₂ →
      F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V → τ.Γ.U ∩ cylinderBetween L τ.F₂ ⊆ cylinderBetween F τ.F₂)
    {Δ₁ : Set cap.Z} (hΔ₁ : IsClosedDisc Δ₁) (h1 : cap.disc₁ τ.isCylinder.1 hL ⊆ Δ₁)
    (h2 : Δ₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    (hbd : discBd Δ₁ ∩ cap.j '' τ.Γ.U ⊆ cap.j '' L) :
    cap.j '' τ.Γ.U ∩ discInt Δ₁ ⊆ cap.disc₁ τ.isCylinder.1 hL := by
  classical
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have : T2Space cap.Z := cap.t2Space_Z
  have hman : ∀ x : cap.Z, IsManifoldPoint x := cap.isManifoldPoint_Z
  have hinj := cap.inj
  obtain ⟨hL1, hL2⟩ :=
    (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hL hle).mp hLsub
  obtain ⟨H, hH, hjH, hd1, hd2, hHsub⟩ := τ.exists_hoop_of_disc cap hle hL hLsub hΔ₁ h1 h2
  have hHL : ∀ x ∈ H, x ∈ τ.Γ.U → x ∈ L := fun x hxH hxU => by
    obtain ⟨y, hy, hyx⟩ := hbd ⟨hjH ▸ mem_image_of_mem _ hxH, mem_image_of_mem _ hxU⟩
    exact hinj hyx ▸ hy
  have hNH : τ.Γ.IsNormal H := fun x ⟨hxH, hxU⟩ => hNL ⟨hHL x hxH hxU, hxU⟩
  have hLF : cylinderBetween L τ.F₂ ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    cap.cylinderBetween_mono hS τ.isHoop_F₁ hL τ.isHoop_F₂ τ.isHoop_F₂ hL1 hL2 Subset.rfl
  have hHV : H ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V := by
    have hsub : H ∩ τ.Γ.V ⊆ τ.F₁ ∩ τ.Γ.V := fun x ⟨hxH, hxV⟩ =>
      hLV ▸ ⟨hHL x hxH (τ.Γ.V_subset_U hxV), hxV⟩
    exact eq_of_subset_of_ncard_le hsub (hmin H hH hNH (hHsub.trans hLF))
      (τ.Γ.finite_V.subset inter_subset_right)
  have hcov := hmax H hH hNH hHsub hHV
  rintro _ ⟨⟨x, hxU, rfl⟩, hxi⟩
  have hxB : x ∈ cylinderBetween τ.F₁ τ.F₂ := τ.U_subset hxU
  rw [← cap.cylinderBetween_union hS τ.isHoop_F₁ hL τ.isHoop_F₂ hL1 hL2] at hxB
  rcases hxB with hx | hx
  · rw [cap.cylinderBetween_eq_of_disc₁_subset hS τ.isHoop_F₁ hL hL1] at hx
    exact hx.1
  · have hx2 := hcov ⟨hxU, hx⟩
    have hle₂ : cap.disc₁ hS.1 hH ⊆ cap.disc₁ hS.1 τ.isHoop_F₂ := hd1 ▸ h2
    rw [cap.cylinderBetween_eq_of_disc₁_subset hS hH τ.isHoop_F₂ hle₂, hd2] at hx2
    have hd : Disjoint (discInt Δ₁) (closure (univ \ Δ₁)) :=
      Disjoint.closure_right (disjoint_left.mpr fun y hy hy' => hy'.2 hy.1)
        (hΔ₁.isOpen_discInt hman)
    exact absurd hx2.2 (disjoint_left.mp hd hxi)

end GraphMinor.GM08
