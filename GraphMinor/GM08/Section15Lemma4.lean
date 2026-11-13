module

public import GraphMinor.GM08.Section15PushOff

/-!
# Graph Minors VIII, printed (15.1): Lemma 4, the exposure lemma

This file states and proves Lemma 4 of the proof of the printed (15.1) in
`Section15PrintedFinal.lean`.

Let $(\Gamma, F_1, F_2)$ be a tube with $A = F_1 \cap V(\Gamma)$ and $B = F_2 \cap V(\Gamma)$.
Suppose that $B \not\subseteq A$, and that every normal hoop between $F_1$ and $F_2$ has at least
$|A|$ vertices. Then there is an $A$-hoop $L$ with the largest pocket (Property 2,
`Tube.exists_maximal_pocket`), a vertex $v \notin L$ and a normal hoop $H$ between $L$ and $F_2$
with vertex set $A \cup \{v\}$ that leaves all of $\Gamma$ between $L$ and $F_2$ on its right
(Property 3), and no normal hoop to the right of $H$ has vertex set $A$ (Property 4).

The vertex $v$ and the line to it come from Claim C (`exists_exposed_region`), applied in the
capped sphere to the left disc of $L$ and the right disc of $F_2$; its pushing hypothesis is
`Tube.image_inter_discInt_subset_of_maximal`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

variable {S : Type w} [TopologicalSpace S]

/-- **Lemma 4 (minimum-end exposure).** Let `τ` be a tube with `A = F₁ ∩ V(Γ)`, such that some
vertex of `F₂` is not on `F₁` and every normal hoop between `F₁` and `F₂` has at least `|A|`
vertices. Then there are an `A`-hoop `L` with the largest pocket (no `A`-hoop to its right cuts
off any of `Γ`), a vertex `v ∉ L`, and a normal hoop `H` between `L` and `F₂` with
`H ∩ V(Γ) = A ∪ {v}` that leaves all of `Γ` between `L` and `F₂` on its right, such that no normal
hoop to the right of `H` has vertex set `A`. -/
theorem Tube.lemma4 (τ : Tube S)
    (hmin : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (τ.F₁ ∩ τ.Γ.V).ncard ≤ (F ∩ τ.Γ.V).ncard)
    (hBA : ∃ x ∈ τ.F₂ ∩ τ.Γ.V, x ∉ τ.F₁) :
    ∃ L : Set S, IsHoop L ∧ τ.Γ.IsNormal L ∧ L ⊆ cylinderBetween τ.F₁ τ.F₂ ∧
      L ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V ∧
      (∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween L τ.F₂ →
        F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V →
        τ.Γ.U ∩ cylinderBetween L τ.F₂ ⊆ cylinderBetween F τ.F₂) ∧
      ∃ v ∈ τ.Γ.V, v ∉ L ∧ ∃ H : Set S, IsHoop H ∧ τ.Γ.IsNormal H ∧
        H ⊆ cylinderBetween L τ.F₂ ∧ H ∩ τ.Γ.V = insert v (L ∩ τ.Γ.V) ∧
        τ.Γ.U ∩ cylinderBetween L τ.F₂ ⊆ cylinderBetween H τ.F₂ ∧
        ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween H τ.F₂ →
          F ∩ τ.Γ.V ≠ τ.F₁ ∩ τ.Γ.V := by
  classical
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  obtain ⟨x₀, ⟨hx₀F, hx₀V⟩, hx₀F₁⟩ := hBA
  have : Nonempty S := ⟨x₀⟩
  have : CompactSpace S := hS.1.1
  obtain ⟨L, hL, hNL, hLsub, hLV, hmax⟩ := τ.exists_maximal_pocket
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented hS τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have hZ := cap.isClosedSurface
  have : T2Space cap.Z := cap.t2Space_Z
  have hinj := cap.inj
  obtain ⟨hL1, hL2⟩ :=
    (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hL hle).mp hLsub
  obtain ⟨hD₁, -, hbD₁, -, -, -, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hL
  obtain ⟨-, hD₂, -, hbD₂, hcupG, hcapG, -, -⟩ := cap.disc₁_disc₂_spec hS.1 τ.isHoop_F₂
  set D₁ := cap.disc₁ hS.1 hL with hD₁def
  set D₂ := cap.disc₂ hS.1 τ.isHoop_F₂ with hD₂def
  set G₁ := cap.disc₁ hS.1 τ.isHoop_F₂ with hG₁def
  obtain ⟨Γz, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding τ.Γ
  have hUz : Γz.U = cap.j '' τ.Γ.U := by simpa using hm.image_U.symm
  have hVz : Γz.V = cap.j '' τ.Γ.V := by simpa using hm.image_V.symm
  -- The right disc of `F₂` meets the left disc of `F₂` only on its boundary.
  have hG₁int : Disjoint G₁ (discInt D₂) := disjoint_left.mpr fun y hy hyi =>
    hyi.2 (hbD₂ ▸ hcapG ▸ ⟨hy, hyi.1⟩)
  have hG₁of : ∀ y, y ∉ discInt D₂ → y ∈ G₁ := fun y hy => by
    rcases (hcupG.ge (mem_univ y) : y ∈ G₁ ∪ D₂) with h | h
    · exact h
    · have hb : y ∈ discBd D₂ := by_contra fun h' => hy ⟨h, h'⟩
      rw [hbD₂, ← hcapG] at hb
      exact hb.1
  have hjU : cap.j '' τ.Γ.U ⊆ G₁ := by
    rintro _ ⟨y, hy, rfl⟩
    have := τ.U_subset hy
    rw [cap.cylinderBetween_eq_of_disc₁_subset hS τ.isHoop_F₁ τ.isHoop_F₂ hle] at this
    exact this.1
  have hDD : Disjoint D₁ (discInt D₂) := hG₁int.mono_left hL2
  have hUD : Disjoint Γz.U (discInt D₂) := hUz ▸ hG₁int.mono_left hjU
  have hU₁ : Γz.U ∩ discBd D₁ ⊆ Γz.V := by
    rintro _ ⟨hy, hyb⟩
    rw [hUz] at hy
    obtain ⟨y, hyU, rfl⟩ := hy
    rw [hbD₁] at hyb
    obtain ⟨y', hy'L, hy'⟩ := hyb
    rw [hVz]
    exact ⟨y, hNL ⟨hinj hy' ▸ hy'L, hyU⟩, rfl⟩
  have hU₂ : Γz.U ∩ discBd D₂ ⊆ Γz.V := by
    rintro _ ⟨hy, hyb⟩
    rw [hUz] at hy
    obtain ⟨y, hyU, rfl⟩ := hy
    rw [hbD₂] at hyb
    obtain ⟨y', hy'F, hy'⟩ := hyb
    rw [hVz]
    exact ⟨y, τ.isNormal_F₂ ⟨hinj hy' ▸ hy'F, hyU⟩, rfl⟩
  have hpush : ∀ Δ : Set cap.Z, IsClosedDisc Δ → D₁ ⊆ Δ → Disjoint Δ (discInt D₂) →
      discBd Δ ∩ Γz.U ⊆ discBd D₁ → Γz.U ∩ discInt Δ ⊆ D₁ := by
    intro Δ hΔ h1 h2 h3
    rw [hUz] at h3 ⊢
    exact τ.image_inter_discInt_subset_of_maximal cap hle hmin hL hNL hLsub hLV hmax hΔ h1
      (fun y hy => hG₁of y (disjoint_left.mp h2 hy)) (hbD₁ ▸ h3)
  -- The vertex `x₀` of `F₂` off `F₁`.
  have hx₀L : x₀ ∉ L := fun h => by
    have : x₀ ∈ L ∩ τ.Γ.V := ⟨h, hx₀V⟩
    rw [hLV] at this
    exact hx₀F₁ this.1
  have hx₀b : cap.j x₀ ∈ discBd D₂ := hbD₂ ▸ mem_image_of_mem _ hx₀F
  have hx₀D₁ : cap.j x₀ ∉ D₁ := by
    intro h
    have hx₀B : x₀ ∈ cylinderBetween L τ.F₂ :=
      subset_cylinderBetween_right (areLaminarHoops_of_subset_cylinderBetween τ.laminar hL hLsub).2
        hx₀F
    rw [cap.cylinderBetween_eq_of_disc₁_subset hS hL τ.isHoop_F₂ hL2] at hx₀B
    obtain ⟨-, -, -, -, -, hcapL, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hL
    have : cap.j x₀ ∈ cap.j '' L := hcapL ▸ ⟨h, hx₀B.2⟩
    obtain ⟨y, hy, hyx⟩ := this
    exact hx₀L (hinj hyx ▸ hy)
  obtain ⟨W, hW, hWdis, hWint, v', hv'V, hv'D₁, hv'cl⟩ :=
    exists_exposed_region hZ cap.isSphere Γz hD₁ hD₂ hDD hUD hU₁ hU₂ hpush
      (hVz ▸ mem_image_of_mem _ hx₀V) hx₀b hx₀D₁
  rw [hVz] at hv'V
  obtain ⟨v, hvV, rfl⟩ := hv'V
  have hvL : v ∉ L := fun h => by
    have : cap.j v ∈ discBd D₁ := by rw [hbD₁]; exact mem_image_of_mem _ h
    exact hv'D₁ (discBd_subset _ this)
  have hvR : v ∈ cylinderBetween L τ.F₂ := by
    have hvB := τ.U_subset (τ.Γ.V_subset_U hvV)
    rw [← cap.cylinderBetween_union hS τ.isHoop_F₁ hL τ.isHoop_F₂ hL1 hL2] at hvB
    rcases hvB with h | h
    · rw [cap.cylinderBetween_eq_of_disc₁_subset hS τ.isHoop_F₁ hL hL1] at h
      exact absurd h.1 hv'D₁
    · exact h
  have hWdis' : Disjoint W (cap.j '' τ.Γ.U ∪ cap.j '' τ.F₂) := by
    refine disjoint_left.mpr fun y hy h => ?_
    rcases h with h | h
    · exact disjoint_left.mp hWdis hy (Or.inl (hUz ▸ h))
    · exact disjoint_left.mp hWdis hy (Or.inr (discBd_subset _ (hbD₂ ▸ h)))
  obtain ⟨H, hH, hNH, hHsub, hHV, hHcov⟩ :=
    τ.exists_exposure_of_closure cap hle hL hNL hLsub hvV hvL hvR hW hWdis' hWint hv'cl
  refine ⟨L, hL, hNL, hLsub, hLV, hmax, v, hvV, hvL, H, hH, hNH, hHsub, hHV, hHcov, ?_⟩
  intro F hF hNF hFsub
  exact τ.ne_of_maximal_pocket hL hLsub hmax hH hHsub (hHV ▸ mem_insert v _ |>.1) hvV
    (fun h => hvL (hLV ▸ h : v ∈ L ∩ τ.Γ.V).1) hF hNF hFsub

/-- The tube `τ` with its two hoops exchanged. -/
def Tube.swap (τ : Tube S) : Tube S where
  Γ := τ.Γ
  F₁ := τ.F₂
  F₂ := τ.F₁
  isCylinder := τ.isCylinder
  laminar := τ.laminar.symm
  isNormal_F₁ := τ.isNormal_F₂
  isNormal_F₂ := τ.isNormal_F₁
  U_subset := cylinderBetween_comm τ.F₁ τ.F₂ ▸ τ.U_subset

@[simp] theorem Tube.swap_Γ (τ : Tube S) : τ.swap.Γ = τ.Γ := rfl
@[simp] theorem Tube.swap_F₁ (τ : Tube S) : τ.swap.F₁ = τ.F₂ := rfl
@[simp] theorem Tube.swap_F₂ (τ : Tube S) : τ.swap.F₂ = τ.F₁ := rfl

/-- **Lemma 4, mirror image.** Lemma 4 at the second end `B = F₂ ∩ V(Γ)`: it is `Tube.lemma4`
for the tube with its hoops exchanged, written with `cylinderBetween_comm`. -/
theorem Tube.lemma4_right (τ : Tube S)
    (hmin : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (τ.F₂ ∩ τ.Γ.V).ncard ≤ (F ∩ τ.Γ.V).ncard)
    (hAB : ∃ x ∈ τ.F₁ ∩ τ.Γ.V, x ∉ τ.F₂) :
    ∃ R : Set S, IsHoop R ∧ τ.Γ.IsNormal R ∧ R ⊆ cylinderBetween τ.F₁ τ.F₂ ∧
      R ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V ∧
      (∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ R →
        F ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V →
        τ.Γ.U ∩ cylinderBetween τ.F₁ R ⊆ cylinderBetween τ.F₁ F) ∧
      ∃ w ∈ τ.Γ.V, w ∉ R ∧ ∃ H : Set S, IsHoop H ∧ τ.Γ.IsNormal H ∧
        H ⊆ cylinderBetween τ.F₁ R ∧ H ∩ τ.Γ.V = insert w (R ∩ τ.Γ.V) ∧
        τ.Γ.U ∩ cylinderBetween τ.F₁ R ⊆ cylinderBetween τ.F₁ H ∧
        ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ H →
          F ∩ τ.Γ.V ≠ τ.F₂ ∩ τ.Γ.V := by
  have hc := cylinderBetween_comm (S := S)
  obtain ⟨R, hR, hNR, hRsub, hRV, hmax, w, hwV, hwR, H, hH, hNH, hHsub, hHV, hcov, hne⟩ :=
    τ.swap.lemma4 (by simpa [hc τ.F₂ τ.F₁] using hmin) (by simpa using hAB)
  simp only [Tube.swap_Γ, Tube.swap_F₁, Tube.swap_F₂] at *
  refine ⟨R, hR, hNR, hc τ.F₂ τ.F₁ ▸ hRsub, hRV, fun F hF hNF hFsub hFV => ?_, w, hwV, hwR, H,
    hH, hNH, hc R τ.F₁ ▸ hHsub, hHV, ?_, fun F hF hNF hFsub => hne F hF hNF (hc H τ.F₁ ▸ hFsub)⟩
  · rw [hc τ.F₁ R, hc τ.F₁ F]
    exact hmax F hF hNF (hc τ.F₁ R ▸ hFsub) hFV
  · rw [hc τ.F₁ R, hc τ.F₁ H]
    exact hcov

/-- **Lemma 5 (one small exceptional end).** Let `τ` be a tube with end sets `A = F₁ ∩ V(Γ)` and
`B = F₂ ∩ V(Γ)`, where `|A| < r ≤ |B|`, and such that every normal hoop between the ends with fewer
than `r` vertices has vertex set `A`. Then `|A| = r - 1`.

Every hoop has at least `|A|` vertices, and some vertex of `B` is not in `A`, so Lemma 4 applies
at `A`. Its exposure hoop has vertex set `A ∪ {v}` with `v ∉ A`. If `|A| ≤ r - 2`, this hoop has
fewer than `r` vertices and its vertex set is not `A`. -/
theorem Tube.lemma5 (τ : Tube S) {r : ℕ} (hA : (τ.F₁ ∩ τ.Γ.V).ncard < r)
    (hB : r ≤ (τ.F₂ ∩ τ.Γ.V).ncard)
    (hsmall : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (F ∩ τ.Γ.V).ncard < r → F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V) :
    (τ.F₁ ∩ τ.Γ.V).ncard = r - 1 := by
  have hfin : ∀ X : Set S, (X ∩ τ.Γ.V).Finite := fun X => τ.Γ.finite_V.subset inter_subset_right
  have hmin : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (τ.F₁ ∩ τ.Γ.V).ncard ≤ (F ∩ τ.Γ.V).ncard := by
    intro F hF hNF hFsub
    by_contra hlt
    push Not at hlt
    have := hsmall F hF hNF hFsub (hlt.trans hA)
    rw [this] at hlt
    exact lt_irrefl _ hlt
  have hBA : ∃ x ∈ τ.F₂ ∩ τ.Γ.V, x ∉ τ.F₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : τ.F₂ ∩ τ.Γ.V ⊆ τ.F₁ ∩ τ.Γ.V := fun x hx => ⟨hcon x hx, hx.2⟩
    have := ncard_le_ncard hsub (hfin τ.F₁)
    omega
  obtain ⟨L, hL, -, hLsub, hLV, -, v, hvV, hvL, H, hH, hNH, hHsub, hHV, -, -⟩ := τ.lemma4 hmin hBA
  have hvA : v ∉ τ.F₁ ∩ τ.Γ.V := fun h => by
    rw [← hLV] at h
    exact hvL h.1
  have hHsub' : H ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    hHsub.trans (cylinderBetween_subset_cylinderBetween τ.laminar
      (areLaminarHoops_of_subset_cylinderBetween τ.laminar hL hLsub).2 hLsub
      (subset_cylinderBetween_right τ.laminar))
  have hcard : (H ∩ τ.Γ.V).ncard = (τ.F₁ ∩ τ.Γ.V).ncard + 1 := by
    rw [hHV, hLV, ncard_insert_of_notMem hvA (hfin _)]
  by_contra hne
  have := hsmall H hH hNH hHsub' (by omega)
  have hv : v ∈ H ∩ τ.Γ.V := hHV ▸ mem_insert v _
  exact hvA (this ▸ hv)

end GraphMinor.GM08
