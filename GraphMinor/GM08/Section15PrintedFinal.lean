module

public import GraphMinor.GM08.Section15PrintedCases

/-!
# Graph Minors VIII, (15.1) with the printed width

This file proves (15.1) of N. Robertson and P. D. Seymour, *Graph Minors. VIII. A Kuratowski
Theorem for General Surfaces*, J. Combin. Theory Ser. B **48** (1990), 255–288 (page 280), with
the width of a tube as printed on page 280 (`GM08.theorem_15_1_printed`).

The paper's chain argument does not work for the printed width (see the correction to the proof
of (15.1) in `corrections/GM08.md`). Our proof removes the pockets at a small end before it builds
the chain. The files of this proof name its steps as follows.
* Lemma 1 (`Tube.hasDisjointPaths_skeleton_of_forall_hoop_ncard_ge`): if every normal hoop has at
  least `q` vertices, there are `q` disjoint paths between the two ends.
* Lemma 2 (`false_of_three_attachments`): if the two ends of a tube carry the same vertex set, a
  bridge has at most two attachments.
* Lemma 3 (`Tube.exists_chain_decomposition`): the paper's chain, when every normal hoop has at
  least `r` vertices.
* Lemma 4 (`Tube.lemma4`, the exposure lemma): after the largest pocket at an end of least size is
  removed, that end can be enlarged by one vertex.
* Fact E (`le_tubularPrintedWidth_of_disc`): a graft drawn in a disc with at most two vertices on
  its boundary, padded with isolated roots, has printed width more than its number of roots.

Take a framing of printed width at least `r`, with end sets `A`, `B` and `|A| ≤ |B|`. A hoop is
*exempt* if its vertex set is `A` or `B`; every other hoop carries at least `r` vertices.
* If `|A| ≥ r`, every hoop carries at least `r` vertices (`printed_train_of_framing_sides`).
* If the framing has printed width at least `r + 1`, the graft is one piece.
* If `|B| ≥ r` (`Tube.Framing.core_big`), Lemma 4 at `A` exposes a junction `J` of `r` vertices,
  and the rest of the tube has no small hoop.
* Otherwise (`Tube.Framing.core_small`), Lemma 4 at `B` between a suitable hoop `H₀` and `F₂`
  exposes a junction `K`, and Lemma 4 at `A`, once or twice, exposes a junction `J`. Between `J`
  and `K` every hoop carries at least `r` vertices.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v}

namespace Tube.Framing

variable {S : Type w} [TopologicalSpace S] {τ : Tube S} {X : Graft α β}

/-- The vertices of the second end of a framing are roots, so there are at most as many as the
index. -/
theorem ncard_F₂_le_index (fr : τ.Framing X) : (τ.F₂ ∩ τ.Γ.V).ncard ≤ X.index := by
  rw [← fr.ncard_vertsIn]
  exact ncard_le_ncard (fr.vertsIn_F_union ▸ subset_union_right) (X.finite_G.1.subset X.T_subset)

/-- A hoop between the ends whose vertices are `A` together with a vertex `v` off `L'`, where `L'`
carries the vertices `A`, does not carry exactly `A`. -/
theorem inter_ne_of_insert {L L' : Set S} {v : S} (hvL' : v ∉ L')
    (hLV : L ∩ τ.Γ.V = insert v (L' ∩ τ.Γ.V)) : L ∩ τ.Γ.V ≠ L' ∩ τ.Γ.V := by
  intro h
  have hv : v ∈ L ∩ τ.Γ.V := hLV ▸ mem_insert _ _
  rw [h] at hv
  exact hvL' hv.1

/-- **Case IVa.** When `|A| < r ≤ |B|`, Lemma 4 at `A` gives a junction of `r` vertices after
which every hoop carries at least `r` vertices. -/
theorem core_big (fr : τ.Framing X) {r k : ℕ} (hk : X.index ≤ k)
    (hexempt : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V ∨ F ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V ∨ r ≤ (F ∩ τ.Γ.V).ncard)
    (ha : (τ.F₁ ∩ τ.Γ.V).ncard < r) (hb : r ≤ (τ.F₂ ∩ τ.Γ.V).ncard) :
    X ∈ LKGraftClass r (printedTubularClass (r + 1) (k + 2 * r)) := by
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have hfin : ∀ F : Set S, (F ∩ τ.Γ.V).Finite := fun F => τ.Γ.finite_V.subset inter_subset_right
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented hS τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have hall : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (τ.F₁ ∩ τ.Γ.V).ncard ≤ (F ∩ τ.Γ.V).ncard := by
    intro F hF hN hsub
    rcases hexempt F hF hN hsub with h | h | h
    · rw [h]
    · rw [h]; omega
    · omega
  have hBA : ∃ x ∈ τ.F₂ ∩ τ.Γ.V, x ∉ τ.F₁ := by
    by_contra hcon
    push_neg at hcon
    have : τ.F₂ ∩ τ.Γ.V ⊆ τ.F₁ ∩ τ.Γ.V := fun x hx => ⟨hcon x hx, hx.2⟩
    have := ncard_le_ncard this (hfin _)
    omega
  obtain ⟨L', hL', hNL', hL'sub, hL'V, v, hvV, hvL', L, hL, hNL, hLsub, hLV, hcov, hne⟩ :=
    τ.lemma4_sub τ.laminar τ.isNormal_F₁ τ.isNormal_F₂ hall hBA
  have hlamL' := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hL' hL'sub).2
  have hLF : L ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    hLsub.trans (cylinderBetween_subset_cylinderBetween τ.laminar hlamL' hL'sub
      (subset_cylinderBetween_right τ.laminar))
  have hlamL := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hL hLF).2
  have hLcard : (L ∩ τ.Γ.V).ncard = (τ.F₁ ∩ τ.Γ.V).ncard + 1 := by
    rw [hLV, ncard_insert_of_notMem (fun h => hvL' h.1) (hfin _), hL'V]
  have hLr : (L ∩ τ.Γ.V).ncard = r := by
    rcases hexempt L hL hNL hLF with h | h | h
    · exact absurd (h.trans hL'V.symm) (inter_ne_of_insert hvL' hLV)
    · rw [h] at hLcard ⊢; omega
    · omega
  obtain ⟨o1, o2, hleft⟩ := fr.left_part₁ cap hle τ.isHoop_F₂
    (subset_cylinderBetween_right τ.laminar) hL' hNL' hL'sub hL'V hL hNL hLsub hLV hcov (k := k) hLr
  refine fr.assemble_left cap hL hNL o1 o2 (by rw [fr.ncard_vertsIn]; exact hLr)
    (by rw [fr.ncard_vertsIn]; have := fr.ncard_F₂_le_index; omega) (fun F hF hN hsub => ?_) hleft
  have hFF : F ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    hsub.trans (cylinderBetween_subset_cylinderBetween τ.laminar hlamL hLF
      (subset_cylinderBetween_right τ.laminar))
  rcases hexempt F hF hN hFF with h | h | h
  · exact absurd h (hne F hF hN hsub)
  · rw [h]; exact hb
  · exact h

/-- **Cases II, III and IVb.** When `|A| ≤ |B| < r` and some normal hoop `H` is not exempt,
Lemma 4 at `B` and then at `A` (once or twice) give junctions `J`, `K` of `r` vertices, with no
small hoop between them. -/
theorem core_small (fr : τ.Framing X) {r k : ℕ}
    (hexempt : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V ∨ F ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V ∨ r ≤ (F ∩ τ.Γ.V).ncard)
    (hab : (τ.F₁ ∩ τ.Γ.V).ncard ≤ (τ.F₂ ∩ τ.Γ.V).ncard) (hb : (τ.F₂ ∩ τ.Γ.V).ncard < r)
    {H : Set S} (hH : IsHoop H) (hNH : τ.Γ.IsNormal H) (hHsub : H ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hHA : H ∩ τ.Γ.V ≠ τ.F₁ ∩ τ.Γ.V) (hHB : H ∩ τ.Γ.V ≠ τ.F₂ ∩ τ.Γ.V) :
    X ∈ LKGraftClass r (printedTubularClass (r + 1) (k + 2 * r)) := by
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have hfin : ∀ F : Set S, (F ∩ τ.Γ.V).Finite := fun F => τ.Γ.finite_V.subset inter_subset_right
  set A := τ.F₁ ∩ τ.Γ.V with hAdef
  set B := τ.F₂ ∩ τ.Γ.V with hBdef
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented hS τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have hall : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      A.ncard ≤ (F ∩ τ.Γ.V).ncard := by
    intro F hF hN hsub
    rcases hexempt F hF hN hsub with h | h | h
    · rw [h]
    · rw [h]; exact hab
    · omega
  have hHr : r ≤ (H ∩ τ.Γ.V).ncard :=
    ((hexempt H hH hNH hHsub).resolve_left hHA).resolve_left hHB
  have hsubF : ∀ {G₁ G₂ : Set S}, IsHoop G₁ → IsHoop G₂ → G₁ ⊆ cylinderBetween τ.F₁ τ.F₂ →
      G₂ ⊆ cylinderBetween G₁ τ.F₂ → cylinderBetween G₁ G₂ ⊆ cylinderBetween τ.F₁ τ.F₂ := by
    intro G₁ G₂ h₁ h₂ hs₁ hs₂
    have hl₁ := (areLaminarHoops_of_subset_cylinderBetween τ.laminar h₁ hs₁).2
    have hs₂' : G₂ ⊆ cylinderBetween τ.F₁ τ.F₂ := hs₂.trans
      (cylinderBetween_subset_cylinderBetween τ.laminar hl₁ hs₁
        (subset_cylinderBetween_right τ.laminar))
    exact cylinderBetween_subset_cylinderBetween τ.laminar
      (areLaminarHoops_of_subset_cylinderBetween hl₁ h₂ hs₂).1 hs₁ hs₂'
  -- Step 1: the hoop `H₀` for Lemma 4 at `B`
  have key : ∃ H₀ : Set S, ∃ hH₀ : IsHoop H₀, τ.Γ.IsNormal H₀ ∧
      H₀ ⊆ cylinderBetween τ.F₁ τ.F₂ ∧
      (∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween H₀ τ.F₂ →
        B.ncard ≤ (F ∩ τ.Γ.V).ncard) ∧
      (∃ x ∈ H₀ ∩ τ.Γ.V, x ∉ τ.F₂) ∧ (H₀ = τ.F₁ ∨ A = B ∨ A.ncard + 1 < r) := by
    have hlamH := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hHsub).2
    have hHF : cylinderBetween H τ.F₂ ⊆ cylinderBetween τ.F₁ τ.F₂ :=
      cylinderBetween_subset_cylinderBetween τ.laminar hlamH hHsub
        (subset_cylinderBetween_right τ.laminar)
    by_cases hAB : A = B
    · refine ⟨H, hH, hNH, hHsub, fun F hF hN hsub => ?_, ?_, .inr (.inl hAB)⟩
      · rw [← hAB]; exact hall F hF hN (hsub.trans hHF)
      · have hAH : A ⊆ H ∩ τ.Γ.V := fun x hx =>
          ⟨τ.inter_subset_of_hoop hH hHsub ⟨hx.1, (hAB ▸ hx : x ∈ B).1⟩, hx.2⟩
        by_contra hcon
        push_neg at hcon
        refine hHA (Subset.antisymm (fun x hx => ?_) hAH)
        rw [hAB]
        exact ⟨hcon x hx, hx.2⟩
    by_cases hab' : A.ncard = B.ncard
    · refine ⟨τ.F₁, τ.isHoop_F₁, τ.isNormal_F₁, subset_cylinderBetween_left τ.laminar,
        fun F hF hN hsub => ?_, ?_, .inl rfl⟩
      · rw [← hab']; exact hall F hF hN hsub
      · by_contra hcon
        push_neg at hcon
        have hsub : A ⊆ B := fun x hx => ⟨hcon x hx, hx.2⟩
        exact hAB (eq_of_subset_of_ncard_le hsub hab'.ge (hfin _))
    -- `|A| < |B|`: the hoop `H` carries all of `B`
    have hBH : B ⊆ H := by
      intro x hxB
      by_contra hxH
      have hlam1 := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hHsub).1
      have hF1H : cylinderBetween τ.F₁ H ⊆ cylinderBetween τ.F₁ τ.F₂ :=
        cylinderBetween_subset_cylinderBetween τ.laminar hlam1
          (subset_cylinderBetween_left τ.laminar) hHsub
      obtain ⟨L', hL', -, hL'sub, hL'V, v, -, hvL', L, hL, hNL, hLsub, hLV, -, -⟩ :=
        τ.lemma4_sub hlam1 τ.isNormal_F₁ hNH
          (fun F hF hN hsub => hall F hF hN (hsub.trans hF1H))
          (by
            by_contra hcon
            push_neg at hcon
            have : H ∩ τ.Γ.V ⊆ A := fun y hy => ⟨hcon y hy, hy.2⟩
            have := ncard_le_ncard this (hfin _)
            omega)
      have hlamL' := (areLaminarHoops_of_subset_cylinderBetween hlam1 hL' hL'sub).2
      have hLF1H : L ⊆ cylinderBetween τ.F₁ H := hLsub.trans
        (cylinderBetween_subset_cylinderBetween hlam1 hlamL' hL'sub
          (subset_cylinderBetween_right hlam1))
      have hLcard : (L ∩ τ.Γ.V).ncard = A.ncard + 1 := by
        rw [hLV, ncard_insert_of_notMem (fun h => hvL' h.1) (hfin _), hL'V]
      rcases hexempt L hL hNL (hLF1H.trans hF1H) with h | h | h
      · exact inter_ne_of_insert hvL' hLV (h.trans hL'V.symm)
      · have hxL : x ∈ cylinderBetween τ.F₁ H := hLF1H ((h ▸ hxB : x ∈ L ∩ τ.Γ.V).1)
        have hxF : x ∈ cylinderBetween H τ.F₂ := subset_cylinderBetween_right hlamH hxB.1
        obtain ⟨hHo1, hHo2⟩ :=
          (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hH hle).mp hHsub
        rw [← cap.cylinderBetween_inter hS τ.isHoop_F₁ hH τ.isHoop_F₂ hHo1 hHo2] at hxH
        exact hxH ⟨hxL, hxF⟩
      · have : A.ncard < B.ncard := lt_of_le_of_ne hab hab'
        omega
    refine ⟨H, hH, hNH, hHsub, fun F hF hN hsub => ?_, ?_, .inr (.inr ?_)⟩
    · have hσ := (τ.subTube hlamH hNH τ.isNormal_F₂).inter_subset_of_hoop hF hsub
      have : B ⊆ F ∩ τ.Γ.V := fun x hx => ⟨hσ ⟨hBH hx, hx.1⟩, hx.2⟩
      exact ncard_le_ncard this (hfin _)
    · by_contra hcon
      push_neg at hcon
      refine hHB (Subset.antisymm (fun x hx => ⟨hcon x hx, hx.2⟩) fun x hx => ⟨hBH hx, hx.2⟩)
    · have : A.ncard < B.ncard := lt_of_le_of_ne hab hab'
      omega
  obtain ⟨H₀, hH₀, hN₀, hH₀sub, hmin₀, hBA₀, hcase⟩ := key
  -- Step 2: Lemma 4 at `B`
  obtain ⟨R, hR, hNR, oR1, oR2, w, hwV, hwF₂, hRV, hneB, hright⟩ :=
    fr.right_part cap hle hH₀ hN₀ hH₀sub hmin₀ hBA₀ (r := r) (k := k)
  have hH₀o := (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hH₀ hle).mp hH₀sub
  have hRsub : R ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hR hle).mpr
      ⟨hH₀o.1.trans oR1, oR2⟩
  have hwB : w ∉ B := fun h => hwF₂ h.1
  have hRcard : (R ∩ τ.Γ.V).ncard = B.ncard + 1 := by
    rw [hRV, ncard_insert_of_notMem hwB (hfin _)]
  have hRr : (R ∩ τ.Γ.V).ncard = r := by
    rcases hexempt R hR hNR hRsub with h | h | h
    · exfalso
      have hBA : B ⊆ A := fun x hx => h ▸ (hRV ▸ mem_insert_of_mem w hx : x ∈ R ∩ τ.Γ.V)
      have hAB := eq_of_subset_of_ncard_le hBA hab (hfin _)
      have hw' : w ∈ R ∩ τ.Γ.V := hRV ▸ mem_insert _ _
      rw [h, ← hAB] at hw'
      exact hwB hw'
    · exfalso
      have hw' : w ∈ R ∩ τ.Γ.V := hRV ▸ mem_insert _ _
      rw [h] at hw'
      exact hwB hw'
    · omega
  have hlamF₁R := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hR hRsub).1
  have hF₁R : cylinderBetween τ.F₁ R ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    cylinderBetween_subset_cylinderBetween τ.laminar hlamF₁R
      (subset_cylinderBetween_left τ.laminar) hRsub
  -- Step 3: Lemma 4 at `A`, between `F₁` and `R`
  obtain ⟨L₁', hL₁', hNL₁', hL₁'sub, hL₁'V, v₁, hv₁V, hv₁L₁', L₁, hL₁, hNL₁, hL₁sub, hL₁V, hcov₁,
      hne₁⟩ :=
    τ.lemma4_sub hlamF₁R τ.isNormal_F₁ hNR (fun F hF hN hsub => hall F hF hN (hsub.trans hF₁R))
      (by
        by_contra hcon
        push_neg at hcon
        have : R ∩ τ.Γ.V ⊆ A := fun y hy => ⟨hcon y hy, hy.2⟩
        have := ncard_le_ncard this (hfin _)
        omega)
  have hlamL₁' := (areLaminarHoops_of_subset_cylinderBetween hlamF₁R hL₁' hL₁'sub).2
  have hL₁R : L₁ ⊆ cylinderBetween τ.F₁ R := hL₁sub.trans
    (cylinderBetween_subset_cylinderBetween hlamF₁R hlamL₁' hL₁'sub
      (subset_cylinderBetween_right hlamF₁R))
  have hlamL₁ := (areLaminarHoops_of_subset_cylinderBetween hlamF₁R hL₁ hL₁R).2
  have hL₁RF : cylinderBetween L₁ R ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    (cylinderBetween_subset_cylinderBetween hlamF₁R hlamL₁ hL₁R
      (subset_cylinderBetween_right hlamF₁R)).trans hF₁R
  have hL₁card : (L₁ ∩ τ.Γ.V).ncard = A.ncard + 1 := by
    rw [hL₁V, ncard_insert_of_notMem (fun h => hv₁L₁' h.1) (hfin _), hL₁'V]
  have hRb : (fr.vertsIn R).ncard = r := by rw [fr.ncard_vertsIn]; exact hRr
  by_cases ha1 : A.ncard + 1 = r
  · -- one pocket on the left
    obtain ⟨o1, o2, hleft⟩ := fr.left_part₁ cap hle hR hRsub hL₁' hNL₁' hL₁'sub hL₁'V hL₁ hNL₁
      hL₁sub hL₁V hcov₁ (r := r) (k := k) (by omega)
    refine fr.assemble cap hL₁ hR hNL₁ hNR o1 o2 oR2 (by rw [fr.ncard_vertsIn]; omega) hRb
      (fun F hF hN hsub => ?_) hleft (hright hRr)
    rcases hexempt F hF hN (hsub.trans hL₁RF) with h | h | h
    · exact absurd h (hne₁ F hF hN hsub)
    · exfalso
      rcases hcase with h0 | hAB | hlt
      · subst h0
        refine hneB F hF hN (hsub.trans ?_) h
        exact cylinderBetween_subset_cylinderBetween hlamF₁R hlamL₁ hL₁R
          (subset_cylinderBetween_right hlamF₁R)
      · exact hne₁ F hF hN hsub (h.trans hAB.symm)
      · omega
    · exact h
  · -- two pockets on the left
    have hL₁B : L₁ ∩ τ.Γ.V = B := by
      rcases hexempt L₁ hL₁ hNL₁ (hL₁R.trans hF₁R) with h | h | h
      · exact absurd (h.trans hL₁'V.symm) (inter_ne_of_insert hv₁L₁' hL₁V)
      · exact h
      · omega
    obtain ⟨L₂', hL₂', hNL₂', hL₂'sub, hL₂'V, v₂, hv₂V, hv₂L₂', L₂, hL₂, hNL₂, hL₂sub, hL₂V,
        hcov₂, hne₂⟩ :=
      τ.lemma4_sub hlamL₁ hNL₁ hNR
        (fun F hF hN hsub => by
          rw [hL₁B]
          rcases hexempt F hF hN (hsub.trans hL₁RF) with h | h | h
          · exact absurd h (hne₁ F hF hN hsub)
          · rw [h]
          · omega)
        ⟨w, ⟨(hRV ▸ mem_insert _ _ : w ∈ R ∩ τ.Γ.V).1, hwV⟩,
          fun h => hwB (hL₁B ▸ ⟨h, hwV⟩ : w ∈ B)⟩
    have hlamL₂' := (areLaminarHoops_of_subset_cylinderBetween hlamL₁ hL₂' hL₂'sub).2
    have hL₂L₁R : L₂ ⊆ cylinderBetween L₁ R := hL₂sub.trans
      (cylinderBetween_subset_cylinderBetween hlamL₁ hlamL₂' hL₂'sub
        (subset_cylinderBetween_right hlamL₁))
    have hlamL₂ := (areLaminarHoops_of_subset_cylinderBetween hlamL₁ hL₂ hL₂L₁R).2
    have hL₂R : cylinderBetween L₂ R ⊆ cylinderBetween L₁ R :=
      cylinderBetween_subset_cylinderBetween hlamL₁ hlamL₂ hL₂L₁R
        (subset_cylinderBetween_right hlamL₁)
    have hL₂card : (L₂ ∩ τ.Γ.V).ncard = r := by
      rw [hL₂V, ncard_insert_of_notMem (fun h => hv₂L₂' h.1) (hfin _), hL₂'V, hL₁B]
      omega
    obtain ⟨o1, o2, hleft⟩ := fr.left_part₂ cap hle hR hRsub hL₁' hNL₁' hL₁'sub hL₁'V hL₁ hNL₁
      hL₁sub hL₁V hcov₁ hL₂' hNL₂' hL₂'sub hL₂'V hL₂ hNL₂ hL₂sub hL₂V hcov₂ (k := k) hL₂card
    refine fr.assemble cap hL₂ hR hNL₂ hNR o1 o2 oR2 (by rw [fr.ncard_vertsIn]; exact hL₂card)
      hRb (fun F hF hN hsub => ?_) hleft (hright hRr)
    rcases hexempt F hF hN ((hsub.trans hL₂R).trans hL₁RF) with h | h | h
    · exact absurd h (hne₁ F hF hN (hsub.trans hL₂R))
    · exact absurd (h.trans hL₁B.symm) (hne₂ F hF hN hsub)
    · exact h

end Tube.Framing

/-- The printed width does not change when the two ends of a tube are exchanged. -/
theorem Tube.le_printedWidth_swap {S : Type w} [TopologicalSpace S] (τ : Tube S) {r : ℕ∞}
    (hw : r ≤ τ.printedWidth) : r ≤ τ.swap.printedWidth := by
  refine τ.swap.le_printedWidth_iff.mpr fun F hF hN hsub => ?_
  change F ⊆ cylinderBetween τ.F₂ τ.F₁ at hsub
  rw [cylinderBetween_comm] at hsub
  rcases τ.le_printedWidth_iff.mp hw F hF hN hsub with h | h | h
  exacts [.inr (.inl h), .inl h, .inr (.inr h)]

/-- The framings of printed width at least `r ≥ 1` of a graft: the printed width of the graft is
a supremum over framings, and below a natural number some framing reaches it. -/
theorem exists_framing_of_le_tubularPrintedWidth {X : Graft α β} {r : ℕ} (hr : 1 ≤ r)
    (hw : (r : ℕ∞) ≤ tubularPrintedWidth X) :
    ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S), τ.IsFraming X ∧
      (r : ℕ∞) ≤ τ.printedWidth := by
  have hlt : ((r - 1 : ℕ) : ℕ∞) < tubularPrintedWidth X :=
    lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt hr one_pos) hw
  obtain ⟨w₀, ⟨S, tS, τ, hfr, rfl⟩, hw₀⟩ := lt_sSup_iff.mp hlt
  refine ⟨S, tS, τ, hfr, ?_⟩
  have h1 := ENat.natCast_add_one_le_iff.mpr hw₀
  have h2 : (r : ℕ∞) = ((r - 1 : ℕ) : ℕ∞) + 1 := by exact_mod_cast (Nat.sub_add_cancel hr).symm
  rw [h2]
  exact h1

/-- (15.1) for one framing of printed width at least `r ≥ 1` whose first end carries at most as
many vertices as the second. -/
theorem Tube.Framing.printed_train {S : Type} [TopologicalSpace S] {τ : Tube S} {X : Graft α β}
    (fr : τ.Framing X) {r k : ℕ} (hr : 1 ≤ r) (hk : X.index ≤ k)
    (hw : (r : ℕ∞) ≤ τ.printedWidth)
    (hab : (τ.F₁ ∩ τ.Γ.V).ncard ≤ (τ.F₂ ∩ τ.Γ.V).ncard) :
    X ∈ LKGraftClass r (printedTubularClass (r + 1) (k + 2 * r)) := by
  by_cases hra : r ≤ (τ.F₁ ∩ τ.Γ.V).ncard
  · exact printed_train_of_framing_sides r k hk ⟨fr⟩ hw hra (hra.trans hab)
  by_cases hwide : ((r + 1 : ℕ) : ℕ∞) ≤ τ.printedWidth
  · refine subset_LKGraftClass r _ ⟨IsTubularGraft.of_framing ⟨fr⟩, ?_, by omega⟩
    exact hwide.trans (le_sSup ⟨S, inferInstance, τ, ⟨fr⟩, rfl⟩)
  have hexempt : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V ∨ F ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V ∨ r ≤ (F ∩ τ.Γ.V).ncard := by
    intro F hF hN hsub
    rcases τ.le_printedWidth_iff.mp hw F hF hN hsub with h | h | h
    exacts [.inl h, .inr (.inl h), .inr (.inr (by exact_mod_cast h))]
  have hH : ∃ H : Set S, IsHoop H ∧ τ.Γ.IsNormal H ∧ H ⊆ cylinderBetween τ.F₁ τ.F₂ ∧
      H ∩ τ.Γ.V ≠ τ.F₁ ∩ τ.Γ.V ∧ H ∩ τ.Γ.V ≠ τ.F₂ ∩ τ.Γ.V := by
    by_contra hcon
    push_neg at hcon
    refine hwide (τ.le_printedWidth_iff.mpr fun F hF hN hsub => ?_)
    by_cases h1 : F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V
    · exact .inl h1
    · exact .inr (.inl (hcon F hF hN hsub h1))
  obtain ⟨H, hH, hNH, hHsub, hHA, hHB⟩ := hH
  by_cases hb : (τ.F₂ ∩ τ.Γ.V).ncard < r
  · exact fr.core_small hexempt hab hb hH hNH hHsub hHA hHB
  · exact fr.core_big hk hexempt (by omega) (by omega)

/-- **Graph Minors VIII, (15.1)** with the printed width (page 280):
"*Let $r \ge 0$, $k \ge 0$ be integers, and let $(G, T)$ be a tubular graft of width $\ge r$
and index $\le k$. Then $(G, T)$ is an $r$-train over the class of all tubular grafts of width
$\ge r + 1$ and index $\le k + 2r$.*"
Here the width of a tube is the printed one of page 280 (`Tube.printedWidth`), and the width of a
tubular graft is the largest printed width of its framings (`tubularPrintedWidth`). -/
theorem theorem_15_1_printed (r k : ℕ) :
    printedTubularClass (α := α) (β := β) r k ⊆
      LKGraftClass r (printedTubularClass (r + 1) (k + 2 * r)) := by
  rintro X ⟨htub, hw, hk⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact theorem_15_1_printed_zero k ⟨htub, hw, hk⟩
  obtain ⟨S, tS, τ, ⟨fr⟩, hwτ⟩ := exists_framing_of_le_tubularPrintedWidth hr hw
  by_cases hab : (τ.F₁ ∩ τ.Γ.V).ncard ≤ (τ.F₂ ∩ τ.Γ.V).ncard
  · exact fr.printed_train hr hk hwτ hab
  · exact fr.swap.printed_train hr hk (τ.le_printedWidth_swap hwτ) (by
      change (τ.F₂ ∩ τ.Γ.V).ncard ≤ (τ.F₁ ∩ τ.Γ.V).ncard
      omega)

end GraphMinor.GM08
