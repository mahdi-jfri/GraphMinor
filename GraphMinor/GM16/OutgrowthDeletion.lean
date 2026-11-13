module

public import GraphMinor.GM16.RingDeletion
import GraphMinor.GM09.Restriction
import GraphMinor.GM09.Section7
import Mathlib.Data.Fintype.Card

/-!
# Vertex deletion in an outgrowth by rings

This file proves `IsOutgrowthByRings.deleteVertices`: if `H` is an outgrowth by at most `d`
`r`-rings of a graph drawn in a surface `S`, and `Z : Set α` is a finite set with `Z.ncard ≤ n`,
then `GM09.deleteVertices H Z` is an outgrowth by at most `d` `((n + 1) * r)`-rings of a graph
drawn in `S`.
-/

public section

namespace GraphMinor.GM16

open Set Function Graph
open GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- Adding a set `Y` of isolated vertices to a graph `G`. -/
private def addIsolatedVertices (G : Graph α β) (Y : Set α) : Graph α β where
  vertexSet := V(G) ∪ Y
  edgeSet := E(G)
  IsLink := G.IsLink
  isLink_symm := G.isLink_symm
  eq_or_eq_of_isLink_of_isLink := G.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := G.edge_mem_iff_exists_isLink
  left_mem_of_isLink _ _ _ h := Or.inl h.left_mem

@[simp]
private theorem vertexSet_addIsolatedVertices (G : Graph α β) (Y : Set α) :
    V(addIsolatedVertices G Y) = V(G) ∪ Y := rfl

@[simp]
private theorem edgeSet_addIsolatedVertices (G : Graph α β) (Y : Set α) :
    E(addIsolatedVertices G Y) = E(G) := rfl

@[simp]
private theorem isLink_addIsolatedVertices (G : Graph α β) (Y : Set α) (e : β) (u v : α) :
    (addIsolatedVertices G Y).IsLink e u v ↔ G.IsLink e u v := Iff.rfl

@[simp]
private theorem inc_addIsolatedVertices (G : Graph α β) (Y : Set α) (e : β) (v : α) :
    (addIsolatedVertices G Y).Inc e v ↔ G.Inc e v := Iff.rfl

@[simp]
private theorem isLoopAt_addIsolatedVertices (G : Graph α β) (Y : Set α) (e : β) (v : α) :
    (addIsolatedVertices G Y).IsLoopAt e v ↔ G.IsLoopAt e v := Iff.rfl

private theorem addIsolatedVertices_le {G G' : Graph α β} {Y : Set α}
    (hle : G ≤ G') (hY : Y ⊆ V(G')) : addIsolatedVertices G Y ≤ G' :=
  ⟨union_subset hle.vertexSet_mono hY, fun _ _ _ h => h.mono hle⟩

/-- If `H ≤ G`, `e ∈ E(H)`, and `G.IsLink e u v`, then `H.IsLink e u v`. -/
private theorem isLink_of_le_of_edge_mem {H G : Graph α β} (hle : H ≤ G) {e : β} (he : e ∈ E(H))
    {u v : α} (hlink : G.IsLink e u v) : H.IsLink e u v :=
  (hle.isLink_iff he).mpr hlink

/-- If `H ≤ G`, then `deleteVertices H Z ≤ deleteVertices G Z`. -/
private theorem deleteVertices_mono {H G : Graph α β} (hle : H ≤ G) (Z : Set α) :
    GM09.deleteVertices H Z ≤ GM09.deleteVertices G Z := by
  refine ⟨fun v hv => ⟨hle.vertexSet_mono hv.1, hv.2⟩, fun e u v hlink => ?_⟩
  exact ⟨hlink.1.mono hle, ⟨hle.vertexSet_mono hlink.2.1.1, hlink.2.1.2⟩,
    ⟨hle.vertexSet_mono hlink.2.2.1, hlink.2.2.2⟩⟩

/-- Transporting a vertex deletion `deleteVertices H Z` across a graph isomorphism `Iso H G'`. -/
private theorem exists_iso_deleteVertices {H G' : Graph α β} (e_iso : Iso H G')
    {Z : Set α} {n : ℕ} (hZ : Z.ncard ≤ n) (hfin : Z.Finite) :
    ∃ Z' : Set α, Z'.ncard ≤ n ∧ Z'.Finite ∧
      Nonempty (Iso (GM09.deleteVertices H Z) (GM09.deleteVertices G' Z')) := by
  classical
  let Z_H : Set α := V(H) ∩ Z
  have hZH_fin : Z_H.Finite := hfin.subset inter_subset_right
  have hZH_card : Z_H.ncard ≤ n := (Set.ncard_le_ncard inter_subset_right hfin).trans hZ
  let f_Z : α → α := fun x => if hx : x ∈ V(H) then (e_iso.vertexEquiv ⟨x, hx⟩).1 else x
  let Z' : Set α := f_Z '' Z_H
  have hZ'_fin : Z'.Finite := hZH_fin.image f_Z
  have hZ'_card : Z'.ncard ≤ n := (Set.ncard_image_le hZH_fin).trans hZH_card
  have hmem_Z' : ∀ v : V(H), (e_iso.vertexEquiv v).1 ∈ Z' ↔ v.1 ∈ Z := by
    intro v
    constructor
    · rintro ⟨x, ⟨hxH, hxZ⟩, hfx⟩
      have hfx' : (e_iso.vertexEquiv ⟨x, hxH⟩).1 = (e_iso.vertexEquiv v).1 := by
        simpa [f_Z, hxH] using hfx
      have heq : (⟨x, hxH⟩ : V(H)) = v := e_iso.vertexEquiv.injective (Subtype.ext hfx')
      exact heq ▸ hxZ
    · intro hvZ
      exact ⟨v.1, ⟨v.2, hvZ⟩, by simp [f_Z, v.2]⟩
  have hmem_Z'_symm : ∀ w : V(G'), w.1 ∈ Z' ↔ (e_iso.vertexEquiv.symm w).1 ∈ Z := by
    intro w
    have h := hmem_Z' (e_iso.vertexEquiv.symm w)
    simpa using h
  let vEquiv : V(GM09.deleteVertices H Z) ≃ V(GM09.deleteVertices G' Z') :=
    { toFun := fun v =>
        ⟨(e_iso.vertexEquiv ⟨v.1, v.2.1⟩).1,
          (e_iso.vertexEquiv ⟨v.1, v.2.1⟩).2,
          fun hz' => v.2.2 ((hmem_Z' ⟨v.1, v.2.1⟩).mp hz')⟩
      invFun := fun w =>
        ⟨(e_iso.vertexEquiv.symm ⟨w.1, w.2.1⟩).1,
          (e_iso.vertexEquiv.symm ⟨w.1, w.2.1⟩).2,
          fun hz => w.2.2 ((hmem_Z'_symm ⟨w.1, w.2.1⟩).mpr hz)⟩
      left_inv := fun v => by
        apply Subtype.ext
        dsimp only
        exact congrArg Subtype.val (e_iso.vertexEquiv.symm_apply_apply ⟨v.1, v.2.1⟩)
      right_inv := fun w => by
        apply Subtype.ext
        dsimp only
        exact congrArg Subtype.val (e_iso.vertexEquiv.apply_symm_apply ⟨w.1, w.2.1⟩) }
  have hedge_iff : ∀ e : E(H),
      e.1 ∈ E(GM09.deleteVertices H Z) ↔ (e_iso.edgeEquiv e).1 ∈ E(GM09.deleteVertices G' Z') := by
    intro e
    rw [(GM09.deleteVertices H Z).edge_mem_iff_exists_isLink,
      (GM09.deleteVertices G' Z').edge_mem_iff_exists_isLink]
    constructor
    · rintro ⟨x, y, hlink, hx, hy⟩
      refine ⟨(vEquiv ⟨x, hx⟩).1, (vEquiv ⟨y, hy⟩).1, ?_⟩
      refine ⟨?_, (vEquiv ⟨x, hx⟩).2, (vEquiv ⟨y, hy⟩).2⟩
      exact (e_iso.isLink_iff e ⟨x, hx.1⟩ ⟨y, hy.1⟩).mp hlink
    · rintro ⟨x', y', hlink', hx', hy'⟩
      let x := vEquiv.symm ⟨x', hx'⟩
      let y := vEquiv.symm ⟨y', hy'⟩
      refine ⟨x.1, y.1, ?_, x.2, y.2⟩
      refine (e_iso.isLink_iff e ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩).mpr ?_
      have hx_eq : (e_iso.vertexEquiv ⟨x.1, x.2.1⟩).1 = x' :=
        congrArg Subtype.val (vEquiv.apply_symm_apply ⟨x', hx'⟩)
      have hy_eq : (e_iso.vertexEquiv ⟨y.1, y.2.1⟩).1 = y' :=
        congrArg Subtype.val (vEquiv.apply_symm_apply ⟨y', hy'⟩)
      rwa [hx_eq, hy_eq]
  have hedge_iff_symm : ∀ e' : E(G'),
      e'.1 ∈ E(GM09.deleteVertices G' Z') ↔
        (e_iso.edgeEquiv.symm e').1 ∈ E(GM09.deleteVertices H Z) := by
    intro e'
    have h := hedge_iff (e_iso.edgeEquiv.symm e')
    simpa using h.symm
  let eEquiv : E(GM09.deleteVertices H Z) ≃ E(GM09.deleteVertices G' Z') :=
    { toFun := fun e =>
        ⟨(e_iso.edgeEquiv ⟨e.1, (H.induce_le sdiff_subset).edgeSet_mono e.2⟩).1,
          (hedge_iff ⟨e.1, (H.induce_le sdiff_subset).edgeSet_mono e.2⟩).mp e.2⟩
      invFun := fun e' =>
        ⟨(e_iso.edgeEquiv.symm ⟨e'.1, (G'.induce_le sdiff_subset).edgeSet_mono e'.2⟩).1,
          (hedge_iff_symm ⟨e'.1, (G'.induce_le sdiff_subset).edgeSet_mono e'.2⟩).mp e'.2⟩
      left_inv := fun e => by
        apply Subtype.ext
        dsimp only
        exact congrArg Subtype.val
          (e_iso.edgeEquiv.symm_apply_apply ⟨e.1, (H.induce_le sdiff_subset).edgeSet_mono e.2⟩)
      right_inv := fun e' => by
        apply Subtype.ext
        dsimp only
        exact congrArg Subtype.val
          (e_iso.edgeEquiv.apply_symm_apply ⟨e'.1, (G'.induce_le sdiff_subset).edgeSet_mono e'.2⟩) }
  refine ⟨Z', hZ'_card, hZ'_fin, ⟨⟨vEquiv, eEquiv, ?_⟩⟩⟩
  intro e x y
  constructor
  · rintro ⟨hlink, hx, hy⟩
    refine ⟨?_, (vEquiv x).2, (vEquiv y).2⟩
    exact (e_iso.isLink_iff ⟨e.1, (H.induce_le sdiff_subset).edgeSet_mono e.2⟩
      ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩).mp hlink
  · rintro ⟨hlink', _, _⟩
    refine ⟨?_, x.2, y.2⟩
    exact (e_iso.isLink_iff ⟨e.1, (H.induce_le sdiff_subset).edgeSet_mono e.2⟩
      ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩).mpr hlink'

/-- A sublist of a clockwise list is clockwise. -/
private theorem isClockwiseSeq_sublist {Ω : CyclicPerm α} {L M : List α}
    (h : Ω.IsClockwiseSeq L) (hs : M.Sublist L) : Ω.IsClockwiseSeq M := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hs
  refine CyclicPerm.IsClockwiseSeq.of_isBoundedSubseq h (lo := 0) (hi := L.length)
    ⟨Nat.zero_le _, fun i => if hi : i < M.length then (f ⟨i, hi⟩).1 else 0, ?_, ?_⟩
  · intro i hi
    simp only [hi, ↓reduceDIte]
    refine ⟨(f ⟨i, hi⟩).2, Nat.zero_le _, (f ⟨i, hi⟩).2, ?_⟩
    exact hf ⟨i, hi⟩
  · intro i j hij hj
    have hi : i < M.length := hij.trans hj
    simp only [hi, hj, ↓reduceDIte]
    exact f.strictMono (show (⟨i, hi⟩ : Fin M.length) < ⟨j, hj⟩ from hij)

/-- The cyclic permutation on a singleton set `{y}`. -/
private def singletonCyclicPerm (y : α) : CyclicPerm α where
  bar := {y}
  toFun := id
  finite_bar := finite_singleton y
  bijOn := bijOn_id {y}
  single_orbit x hx z hz := ⟨0, by rw [mem_singleton_iff.mp hx, mem_singleton_iff.mp hz]; rfl⟩

@[simp]
private theorem bar_singletonCyclicPerm (y : α) : (singletonCyclicPerm y).bar = {y} := rfl

private theorem isClockwiseSeq_singletonCyclicPerm (y : α) :
    (singletonCyclicPerm y).IsClockwiseSeq [y] := by
  refine ⟨List.nodup_singleton y, ?_, ?_⟩
  · intro v hv
    simpa using hv
  · intro i hi
    have hi0 : i = 0 := by simp at hi; exact hi
    subst hi0
    exact ⟨1, le_rfl, by simp [singletonCyclicPerm], by simp, fun j hj1 hjlt => by omega⟩

private theorem isNaturalOrderFrom_singletonCyclicPerm {ν' : α → S} {C : Set S} {y : α}
    {Ω : CyclicPerm α} {ν : α → S} (hnat : IsNaturalOrderFrom ν Ω C) (hy : ν' y ∈ C) :
    IsNaturalOrderFrom ν' (singletonCyclicPerm y) C := by
  rcases hnat with ⟨hoarc, φ, _⟩
  refine ⟨hoarc, φ, ?_, ?_⟩
  · intro v hv
    rw [bar_singletonCyclicPerm, mem_singleton_iff] at hv
    rwa [hv]
  · intro v₁ v₂ v₃ hcw3
    rcases hcw3 with ⟨hnodup, hsub, _⟩
    have hv₁ : v₁ = y := hsub v₁ (by simp)
    have hv₂ : v₂ = y := hsub v₂ (by simp)
    rw [hv₁, hv₂] at hnodup
    simp at hnodup

private theorem isNaturalOrderFrom_of_isRestriction {ν ν' : α → S} {C : Set S}
    {Ω Ω' : CyclicPerm α} {X : Set α}
    (hnat : IsNaturalOrderFrom ν Ω C) (hrest : Ω.IsRestriction X Ω')
    (hν' : ∀ v ∈ Ω'.bar, ν' v = ν v) :
    IsNaturalOrderFrom ν' Ω' C := by
  rcases hnat with ⟨hoarc, φ, hmem, hcw3⟩
  refine ⟨hoarc, φ, ?_, ?_⟩
  · intro v hv
    rw [hν' v hv]
    exact hmem v (hrest.bar_subset hv)
  · intro v₁ v₂ v₃ hcw'
    rw [hrest.isClockwise3_iff] at hcw'
    rcases hcw' with ⟨hv₁, hv₂, hv₃, hcw⟩
    rw [hν' v₁ hv₁, hν' v₂ hv₂, hν' v₃ hv₃]
    exact hcw3 v₁ v₂ v₃ hcw

/-- Deleting at most `n` vertices from an outgrowth by at most `d` `r`-rings yields an outgrowth
by at most `d` `((n + 1) * r)`-rings. -/
theorem IsOutgrowthByRings.deleteVertices {S} [TopologicalSpace S] {H : Graph α β} {d r n : ℕ}
    (h : IsOutgrowthByRings S H d r) {Z : Set α} (hZ : Z.ncard ≤ n) (hfin : Z.Finite) :
    IsOutgrowthByRings S (GM09.deleteVertices H Z) d ((n + 1) * r) := by
  classical
  rcases h with ⟨G', G₀, ⟨e_iso⟩, k, Δ, G_ring, t, ν, edgeOf,
    hk_le_d, hG₀_le, hring_le, hV_union, hE_union, hν_inj,
    hlink_line, hloop_oarc, hedge_inter, hinc_of_mem,
    hdisc, hdisc_disj, hdisc_edge, hdisc_bd, hbd_eq, hcyc, hring,
    hinter, hring_G₀_edisj, hring_disj⟩
  obtain ⟨Z', hZ'_card, hZ'_fin, ⟨e_iso'⟩⟩ := exists_iso_deleteVertices e_iso hZ hfin
  let G'₁ : Graph α β := GM09.deleteVertices G' Z'
  let R' (i : Fin k) : Graph α β := GM09.deleteVertices (G_ring i) Z'
  let p : α → Bool := fun x => decide (x ∉ Z')
  let t_filt (i : Fin k) : List α := (t i).filter p
  let isRep (i : Fin k) : Prop := t_filt i = [] ∧ V(R' i).Nonempty
  let y_rep (i : Fin k) (hi : V(R' i).Nonempty) : α := hi.some
  have hy_rep_mem (i : Fin k) (hi : V(R' i).Nonempty) : y_rep i hi ∈ V(R' i) := hi.some_mem
  have ht_ne_of_isRep (i : Fin k) (hi : isRep i) : t i ≠ [] :=
    ((hring i).deleteVertices_singleton_of_filter_eq_nil hZ'_card hZ'_fin hi.1
      (hy_rep_mem i hi.2)).1
  let x_rep (i : Fin k) (hi : isRep i) : α :=
    (t i)[0]'(List.length_pos_of_ne_nil (ht_ne_of_isRep i hi))
  have hx_rep_mem_t (i : Fin k) (hi : isRep i) : x_rep i hi ∈ t i :=
    List.getElem_mem (List.length_pos_of_ne_nil (ht_ne_of_isRep i hi))
  have ht_sub_Z'_of_eq_nil (i : Fin k) (heq : t_filt i = []) :
      ∀ x ∈ t i, x ∈ Z' := by
    intro x hx
    by_contra hxZ'
    have hmem : x ∈ t_filt i := List.mem_filter.mpr ⟨hx, decide_eq_true hxZ'⟩
    rw [heq] at hmem
    cases hmem
  have hx_rep_mem_ring (i : Fin k) (hi : isRep i) : x_rep i hi ∈ V(G_ring i) := by
    have hmem : x_rep i hi ∈ V(G_ring i) ∩ V(G₀) := by
      rw [hinter i]
      exact hx_rep_mem_t i hi
    exact hmem.1
  have hx_rep_mem_G₀ (i : Fin k) (hi : isRep i) : x_rep i hi ∈ V(G₀) := by
    have hmem : x_rep i hi ∈ V(G_ring i) ∩ V(G₀) := by
      rw [hinter i]
      exact hx_rep_mem_t i hi
    exact hmem.2
  have hx_rep_mem_Z' (i : Fin k) (hi : isRep i) : x_rep i hi ∈ Z' :=
    ht_sub_Z'_of_eq_nil i hi.1 (x_rep i hi) (hx_rep_mem_t i hi)
  have hx_rep_mem_bd (i : Fin k) (hi : isRep i) : ν (x_rep i hi) ∈ discBd (Δ i) := by
    have hmem : x_rep i hi ∈ {v ∈ V(G₀) | ν v ∈ discBd (Δ i)} := by
      rw [hbd_eq i]
      exact hx_rep_mem_t i hi
    exact hmem.2
  have hy_rep_notMem_G₀ (i : Fin k) (hi : isRep i) : y_rep i hi.2 ∉ V(G₀) := by
    intro hyG₀
    have hy_inter : y_rep i hi.2 ∈ V(G_ring i) ∩ V(G₀) := ⟨(hy_rep_mem i hi.2).1, hyG₀⟩
    rw [hinter i] at hy_inter
    exact (hy_rep_mem i hi.2).2 (ht_sub_Z'_of_eq_nil i hi.1 _ hy_inter)
  have hy_rep_inj : ∀ {i j : Fin k} (hi : V(R' i).Nonempty) (hj : V(R' j).Nonempty),
      y_rep i hi = y_rep j hj → i = j := by
    intro i j hi hj heq
    by_contra hij
    exact Set.disjoint_left.mp (hring_disj i j hij).1
      (hy_rep_mem i hi).1 (heq ▸ (hy_rep_mem j hj).1)
  have hx_rep_inj : ∀ {i j : Fin k} (hi : isRep i) (hj : isRep j),
      x_rep i hi = x_rep j hj → i = j := by
    intro i j hi hj heq
    by_contra hij
    exact Set.disjoint_left.mp (hring_disj i j hij).1
      (hx_rep_mem_ring i hi) (heq ▸ hx_rep_mem_ring j hj)
  let Y : Set α := {v | ∃ (i : Fin k) (hi : isRep i), v = y_rep i hi.2}
  have hY_sub_G'₁ : Y ⊆ V(G'₁) := by
    rintro v ⟨i, hi, rfl⟩
    exact (deleteVertices_mono (hring_le i) Z').vertexSet_mono (hy_rep_mem i hi.2)
  have hY_notMem_G₀ : ∀ v ∈ Y, v ∉ V(G₀) := by
    rintro v ⟨i, hi, rfl⟩
    exact hy_rep_notMem_G₀ i hi
  let G₀₁ : Graph α β := GM09.deleteVertices G₀ Z'
  let G₀' : Graph α β := addIsolatedVertices G₀₁ Y
  let orig (v : α) : α :=
    if hv : v ∈ Y then x_rep hv.choose hv.choose_spec.fst else v
  let ν' (v : α) : S := ν (orig v)
  have horig_of_notMem_Y {v : α} (hv : v ∉ Y) : orig v = v := by
    simp only [orig, hv, ↓reduceDIte]
  have hν'_of_notMem_Y {v : α} (hv : v ∉ Y) : ν' v = ν v := by
    simp [ν', horig_of_notMem_Y hv]
  have horig_y_rep (i : Fin k) (hi : isRep i) : orig (y_rep i hi.2) = x_rep i hi := by
    have hvY : y_rep i hi.2 ∈ Y := ⟨i, hi, rfl⟩
    have hchoose : hvY.choose = i :=
      (hy_rep_inj hi.2 hvY.choose_spec.fst.2 hvY.choose_spec.snd).symm
    have h_eq : ∀ (j : Fin k) (hj : isRep j), j = i → x_rep j hj = x_rep i hi := by
      rintro j hj rfl
      rfl
    simp only [orig, hvY, ↓reduceDIte]
    exact h_eq hvY.choose hvY.choose_spec.fst hchoose
  have hν'_y_rep (i : Fin k) (hi : isRep i) : ν' (y_rep i hi.2) = ν (x_rep i hi) := by
    simp [ν', horig_y_rep i hi]
  have horig_maps : MapsTo orig V(G₀') V(G₀) := by
    rintro v (hv | hvY)
    · rw [horig_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hv.1)]
      exact hv.1
    · rcases hvY with ⟨i, hi, rfl⟩
      rw [horig_y_rep i hi]
      exact hx_rep_mem_G₀ i hi
  have horig_inj : InjOn orig V(G₀') := by
    rintro u (hu | ⟨i, hi, rfl⟩) v (hv | ⟨j, hj, rfl⟩) heq
    · rw [horig_of_notMem_Y (fun hY => hY_notMem_G₀ u hY hu.1),
        horig_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hv.1)] at heq
      exact heq
    · rw [horig_of_notMem_Y (fun hY => hY_notMem_G₀ u hY hu.1), horig_y_rep j hj] at heq
      exfalso
      exact hu.2 (heq ▸ hx_rep_mem_Z' j hj)
    · rw [horig_y_rep i hi, horig_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hv.1)] at heq
      exfalso
      exact hv.2 (heq.symm ▸ hx_rep_mem_Z' i hi)
    · rw [horig_y_rep i hi, horig_y_rep j hj] at heq
      have hij : i = j := hx_rep_inj hi hj heq
      rcases hij with rfl
      rfl
  let Act := {i : Fin k // V(R' i).Nonempty}
  let k' : ℕ := Fintype.card Act
  have hk'_le_d : k' ≤ d :=
    (Fintype.card_subtype_le (fun i : Fin k => V(R' i).Nonempty)).trans (by simpa using hk_le_d)
  let e_act : Fin k' ≃ Act := (Fintype.equivFin Act).symm
  let idx (a : Fin k') : Fin k := (e_act a).1
  have hidx_inj : Function.Injective idx := Subtype.val_injective.comp e_act.injective
  have hidx_ne (a : Fin k') : V(R' (idx a)).Nonempty := (e_act a).2
  have hmem_idx (i : Fin k) (hi : V(R' i).Nonempty) : ∃ a : Fin k', idx a = i :=
    ⟨e_act.symm ⟨i, hi⟩, by simp [idx]⟩
  let Δ' (a : Fin k') : Set S := Δ (idx a)
  let G_ring' (a : Fin k') : Graph α β := R' (idx a)
  let t' (a : Fin k') : List α :=
    if t_filt (idx a) = [] then [y_rep (idx a) (hidx_ne a)] else t_filt (idx a)
  have hG₀'_le : G₀' ≤ G'₁ :=
    addIsolatedVertices_le (deleteVertices_mono hG₀_le Z') hY_sub_G'₁
  have hG_ring'_le (a : Fin k') : G_ring' a ≤ G'₁ :=
    deleteVertices_mono (hring_le (idx a)) Z'
  have hmem_image_of_edge : ∀ {e : β}, e ∈ E(G₀') → ∀ {s : S},
      s ∈ edgeOf e → s ∈ ν '' V(G₀) → s ∈ ν' '' V(G₀') := by
    rintro e he s hs_edge ⟨v, hvG₀, rfl⟩
    have heG₀ : e ∈ E(G₀) := (G₀.induce_le sdiff_subset).edgeSet_mono he
    obtain ⟨w, hlinkG₀⟩ := hinc_of_mem e heG₀ v hvG₀ hs_edge
    have hlinkG₀₁ : G₀₁.IsLink e v w :=
      isLink_of_le_of_edge_mem (G₀.induce_le sdiff_subset) he hlinkG₀
    have hvG₀₁ : v ∈ V(G₀₁) := hlinkG₀₁.left_mem
    refine ⟨v, Or.inl hvG₀₁, ?_⟩
    exact hν'_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hvG₀₁.1)
  have hx_rep_mem_bd_iff (j i : Fin k) (hj : isRep j) :
      ν (x_rep j hj) ∈ discBd (Δ i) ↔ j = i := by
    constructor
    · intro hbd
      have hmem : x_rep j hj ∈ {v ∈ V(G₀) | ν v ∈ discBd (Δ i)} := ⟨hx_rep_mem_G₀ j hj, hbd⟩
      rw [hbd_eq i, ← hinter i] at hmem
      by_contra hji
      exact Set.disjoint_left.mp (hring_disj j i hji).1 (hx_rep_mem_ring j hj) hmem.1
    · rintro rfl
      exact hx_rep_mem_bd j hj
  refine ⟨G'₁, G₀', ⟨e_iso'⟩, k', Δ', G_ring', t', ν', edgeOf,
    hk'_le_d, hG₀'_le, hG_ring'_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro v hv
      have hvG' : v ∈ V(G') := hv.1
      rw [hV_union] at hvG'
      rcases hvG' with hvG₀ | hv_rings
      · exact Or.inl (Or.inl ⟨hvG₀, hv.2⟩)
      · rcases mem_iUnion.mp hv_rings with ⟨i, hvi⟩
        have hvi' : v ∈ V(R' i) := ⟨hvi, hv.2⟩
        obtain ⟨a, ha⟩ := hmem_idx i ⟨v, hvi'⟩
        exact Or.inr (mem_iUnion.mpr ⟨a, by simpa [G_ring', ha] using hvi'⟩)
    · refine union_subset hG₀'_le.vertexSet_mono (iUnion_subset fun a => (hG_ring'_le a).vertexSet_mono)
  · apply Subset.antisymm
    · intro e he
      obtain ⟨u, v, hlink'⟩ := (G'₁.edge_mem_iff_exists_isLink e).mp he
      have hlinkG' : G'.IsLink e u v := hlink'.1
      have heG' : e ∈ E(G') := hlinkG'.edge_mem
      rw [hE_union] at heG'
      rcases heG' with heG₀ | he_rings
      · have hlinkG₀ : G₀.IsLink e u v := isLink_of_le_of_edge_mem hG₀_le heG₀ hlinkG'
        have hlinkG₀₁ : G₀₁.IsLink e u v :=
          ⟨hlinkG₀, ⟨hlinkG₀.left_mem, hlink'.2.1.2⟩, ⟨hlinkG₀.right_mem, hlink'.2.2.2⟩⟩
        exact Or.inl hlinkG₀₁.edge_mem
      · rcases mem_iUnion.mp he_rings with ⟨i, hei⟩
        have hlink_ring : (G_ring i).IsLink e u v :=
          isLink_of_le_of_edge_mem (hring_le i) hei hlinkG'
        have hlink_R' : (R' i).IsLink e u v :=
          ⟨hlink_ring, ⟨hlink_ring.left_mem, hlink'.2.1.2⟩, ⟨hlink_ring.right_mem, hlink'.2.2.2⟩⟩
        obtain ⟨a, ha⟩ := hmem_idx i ⟨u, hlink_R'.left_mem⟩
        exact Or.inr (mem_iUnion.mpr ⟨a, by simpa [G_ring', ha] using hlink_R'.edge_mem⟩)
    · refine union_subset hG₀'_le.edgeSet_mono (iUnion_subset fun a => (hG_ring'_le a).edgeSet_mono)
  · exact hν_inj.comp horig_inj horig_maps
  · intro e he u v hlink huv
    have heG₀ : e ∈ E(G₀) := (G₀.induce_le sdiff_subset).edgeSet_mono he
    have hlink₁ : G₀₁.IsLink e u v := hlink
    have hu : u ∈ V(G₀₁) := hlink₁.left_mem
    have hv : v ∈ V(G₀₁) := hlink₁.right_mem
    rw [hν'_of_notMem_Y (fun hY => hY_notMem_G₀ u hY hu.1),
      hν'_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hv.1)]
    exact hlink_line e heG₀ u v hlink₁.1 huv
  · intro e he v hloop
    have heG₀ : e ∈ E(G₀) := (G₀.induce_le sdiff_subset).edgeSet_mono he
    have hloop₁ : G₀₁.IsLoopAt e v := hloop
    have hv : v ∈ V(G₀₁) := hloop₁.left_mem
    rw [hν'_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hv.1)]
    exact hloop_oarc e heG₀ v hloop₁.1
  · intro e he f hf hef s hs
    have heG₀ : e ∈ E(G₀) := (G₀.induce_le sdiff_subset).edgeSet_mono he
    have hfG₀ : f ∈ E(G₀) := (G₀.induce_le sdiff_subset).edgeSet_mono hf
    exact hmem_image_of_edge he hs.1 (hedge_inter e heG₀ f hfG₀ hef hs)
  · intro e he v hv hν'
    have heG₀ : e ∈ E(G₀) := (G₀.induce_le sdiff_subset).edgeSet_mono he
    obtain ⟨w, hlinkG₀⟩ := hinc_of_mem e heG₀ (orig v) (horig_maps hv) hν'
    have hlinkG₀₁ : G₀₁.IsLink e (orig v) w :=
      isLink_of_le_of_edge_mem (G₀.induce_le sdiff_subset) he hlinkG₀
    have hv_notMem_Y : v ∉ Y := by
      rintro ⟨i, hi, rfl⟩
      rw [horig_y_rep i hi] at hlinkG₀₁
      exact hlinkG₀₁.left_mem.2 (hx_rep_mem_Z' i hi)
    rw [horig_of_notMem_Y hv_notMem_Y] at hlinkG₀₁
    exact ⟨w, hlinkG₀₁⟩
  · intro a
    exact hdisc (idx a)
  · intro a b hab
    exact hdisc_disj (idx a) (idx b) (hidx_inj.ne hab)
  · intro a e he s hs
    have heG₀ : e ∈ E(G₀) := (G₀.induce_le sdiff_subset).edgeSet_mono he
    exact hmem_image_of_edge he hs.1 (hdisc_edge (idx a) e heG₀ hs)
  · intro a v hv hΔ
    exact hdisc_bd (idx a) (orig v) (horig_maps hv) hΔ
  · intro a
    ext v
    simp only [mem_ofPred_eq, G₀', vertexSet_addIsolatedVertices, mem_union, Δ', t']
    by_cases heq : t_filt (idx a) = []
    · have hi_rep : isRep (idx a) := ⟨heq, hidx_ne a⟩
      simp only [heq, ↓reduceIte, List.mem_singleton]
      constructor
      · rintro ⟨hvG₀₁ | ⟨j, hj, rfl⟩, hbd⟩
        · rw [hν'_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hvG₀₁.1)] at hbd
          have hvt : v ∈ t (idx a) := by
            have : v ∈ {w ∈ V(G₀) | ν w ∈ discBd (Δ (idx a))} := ⟨hvG₀₁.1, hbd⟩
            rwa [hbd_eq (idx a)] at this
          exfalso
          exact hvG₀₁.2 (ht_sub_Z'_of_eq_nil (idx a) heq v hvt)
        · rw [hν'_y_rep j hj, hx_rep_mem_bd_iff j (idx a) hj] at hbd
          rcases hbd with rfl
          rfl
      · rintro rfl
        refine ⟨Or.inr ⟨idx a, hi_rep, rfl⟩, ?_⟩
        rw [hν'_y_rep (idx a) hi_rep]
        exact hx_rep_mem_bd (idx a) hi_rep
    · simp only [heq, ↓reduceIte]
      constructor
      · rintro ⟨hvG₀₁ | ⟨j, hj, rfl⟩, hbd⟩
        · rw [hν'_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hvG₀₁.1)] at hbd
          have hvt : v ∈ t (idx a) := by
            have : v ∈ {w ∈ V(G₀) | ν w ∈ discBd (Δ (idx a))} := ⟨hvG₀₁.1, hbd⟩
            rwa [hbd_eq (idx a)] at this
          exact List.mem_filter.mpr ⟨hvt, decide_eq_true hvG₀₁.2⟩
        · rw [hν'_y_rep j hj, hx_rep_mem_bd_iff j (idx a) hj] at hbd
          rcases hbd with rfl
          exact (heq hj.1).elim
      · intro hvf
        rw [List.mem_filter] at hvf
        have hvG₀ : v ∈ V(G₀) := by
          have : v ∈ {w ∈ V(G₀) | ν w ∈ discBd (Δ (idx a))} := by
            rw [hbd_eq (idx a)]
            exact hvf.1
          exact this.1
        have hvbd : ν v ∈ discBd (Δ (idx a)) := by
          have : v ∈ {w ∈ V(G₀) | ν w ∈ discBd (Δ (idx a))} := by
            rw [hbd_eq (idx a)]
            exact hvf.1
          exact this.2
        have hvZ' : v ∉ Z' := of_decide_eq_true hvf.2
        refine ⟨Or.inl ⟨hvG₀, hvZ'⟩, ?_⟩
        rwa [hν'_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hvG₀)]
  · intro a
    obtain ⟨Ω, hΩ_bar, hΩ_cw, hΩ_nat⟩ := hcyc (idx a)
    dsimp only [t', Δ']
    by_cases heq : t_filt (idx a) = []
    · have hi_rep : isRep (idx a) := ⟨heq, hidx_ne a⟩
      simp only [heq, ↓reduceIte]
      refine ⟨singletonCyclicPerm (y_rep (idx a) (hidx_ne a)), ?_,
        isClockwiseSeq_singletonCyclicPerm _, ?_⟩
      · ext v
        simp
      · refine isNaturalOrderFrom_singletonCyclicPerm hΩ_nat ?_
        rw [hν'_y_rep (idx a) hi_rep]
        exact hx_rep_mem_bd (idx a) hi_rep
    · simp only [heq, ↓reduceIte]
      let X_sub : Set α := {v | v ∈ t_filt (idx a)}
      obtain ⟨Ω', hrest⟩ := Ω.exists_isRestriction X_sub
      have hX_sub_bar : X_sub ⊆ Ω.bar := by
        intro v hv
        rw [hΩ_bar]
        exact (List.mem_filter.mp hv).1
      have hΩ'_bar : Ω'.bar = X_sub := by
        rw [hrest.1, inter_eq_self_of_subset_right hX_sub_bar]
      refine ⟨Ω', hΩ'_bar, ?_, ?_⟩
      · rw [hrest.isClockwiseSeq_iff]
        exact ⟨hΩ'_bar.symm.subset, isClockwiseSeq_sublist hΩ_cw List.filter_sublist⟩
      · refine isNaturalOrderFrom_of_isRestriction hΩ_nat hrest ?_
        intro v hv
        rw [hΩ'_bar] at hv
        have hvG₀ : v ∈ V(G₀) := by
          have : v ∈ {w ∈ V(G₀) | ν w ∈ discBd (Δ (idx a))} := by
            rw [hbd_eq (idx a)]
            exact (List.mem_filter.mp hv).1
          exact this.1
        exact hν'_of_notMem_Y (fun hY => hY_notMem_G₀ v hY hvG₀)
  · intro a
    dsimp only [G_ring', t']
    by_cases heq : t_filt (idx a) = []
    · simp only [heq, ↓reduceIte]
      exact ((hring (idx a)).deleteVertices_singleton_of_filter_eq_nil hZ'_card hZ'_fin heq
        (hy_rep_mem (idx a) (hidx_ne a))).2
    · simp only [heq, ↓reduceIte]
      exact (hring (idx a)).deleteVertices_of_filter_ne_nil hZ'_card hZ'_fin heq
  · intro a
    ext v
    simp only [G_ring', G₀', vertexSet_addIsolatedVertices, mem_inter_iff, mem_union,
      mem_ofPred_eq, t']
    by_cases heq : t_filt (idx a) = []
    · have hi_rep : isRep (idx a) := ⟨heq, hidx_ne a⟩
      simp only [heq, ↓reduceIte, List.mem_singleton]
      constructor
      · rintro ⟨hvR', hvG₀₁ | ⟨j, hj, rfl⟩⟩
        · have hvt : v ∈ t (idx a) := by
            have : v ∈ V(G_ring (idx a)) ∩ V(G₀) := ⟨hvR'.1, hvG₀₁.1⟩
            rwa [hinter (idx a)] at this
          exfalso
          exact hvR'.2 (ht_sub_Z'_of_eq_nil (idx a) heq v hvt)
        · have hij : j = idx a := by
            by_contra hne
            exact Set.disjoint_left.mp (hring_disj j (idx a) hne).1
              (hy_rep_mem j hj.2).1 hvR'.1
          rcases hij with rfl
          rfl
      · rintro rfl
        exact ⟨hy_rep_mem (idx a) (hidx_ne a), Or.inr ⟨idx a, hi_rep, rfl⟩⟩
    · simp only [heq, ↓reduceIte]
      constructor
      · rintro ⟨hvR', hvG₀₁ | ⟨j, hj, rfl⟩⟩
        · have hvt : v ∈ t (idx a) := by
            have : v ∈ V(G_ring (idx a)) ∩ V(G₀) := ⟨hvR'.1, hvG₀₁.1⟩
            rwa [hinter (idx a)] at this
          exact List.mem_filter.mpr ⟨hvt, decide_eq_true hvR'.2⟩
        · have hij : j = idx a := by
            by_contra hne
            exact Set.disjoint_left.mp (hring_disj j (idx a) hne).1
              (hy_rep_mem j hj.2).1 hvR'.1
          rcases hij with rfl
          exact (heq hj.1).elim
      · intro hvf
        rw [List.mem_filter] at hvf
        have hv_inter : v ∈ V(G_ring (idx a)) ∩ V(G₀) := by
          rw [hinter (idx a)]
          exact hvf.1
        have hvZ' : v ∉ Z' := of_decide_eq_true hvf.2
        exact ⟨⟨hv_inter.1, hvZ'⟩, Or.inl ⟨hv_inter.2, hvZ'⟩⟩
  · intro a
    exact (hring_G₀_edisj (idx a)).mono
      ((G_ring (idx a)).induce_le sdiff_subset).edgeSet_mono
      (G₀.induce_le sdiff_subset).edgeSet_mono
  · intro a b hab
    have hdisj := hring_disj (idx a) (idx b) (hidx_inj.ne hab)
    exact ⟨hdisj.1.mono sdiff_subset sdiff_subset,
      hdisj.2.mono ((G_ring (idx a)).induce_le sdiff_subset).edgeSet_mono
        ((G_ring (idx b)).induce_le sdiff_subset).edgeSet_mono⟩

end GraphMinor.GM16
