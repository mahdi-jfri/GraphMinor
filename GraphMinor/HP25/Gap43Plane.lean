module

public import GraphMinor.HP25.Prop32
public import GraphMinor.Surface.CutTree
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.Crossing
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.Fan

/-!
# The gap of Lemma 4.3: the drawing step

This is step 5 of the proof of `Lemma43Gap` (`GraphMinor/HP25/Gap43.lean`), stated for a plane
embedding in the sense of `HP25/Web.lean`. We have a plane embedding `φ` of a graph `K` drawn inside
the closed domain of an `O`-arc `F`, a path `P = x … z` of `K` whose image meets `F` only at its
ends, and a path `z L x` whose image lies on `F`. So the image of `P` cuts the closed domain of `F`
into two closed discs, and one of them is bounded by the image of the cycle `D = P L`
(`IsCut.components`, the theta curve lemma).

* `subset_side`: a connected set that misses the cut and meets one of the two arcs of `F` (away
  from the ends of the cut) lies in the closed domain on that side.
* `plane_gap`: let `𝒦` be a set of vertices off `P`, connected in `K` and containing a vertex `ℓ`
  of `L`. Two disjoint paths of `K` whose ends alternate on `D`, whose other vertices lie in `𝒦`, and
  whose edges each have an end in `𝒦`, cannot exist. Their images lie in the closed domain of the
  image of `D`: they are connected to the image of `ℓ` away from the image of `P`. In that closed
  disc, paths with alternating ends meet (`Surface.disc_crossing`), as in Proposition 3.2.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

local notation "𝕀" => unitInterval

variable {V : Type*}

/-- **The side of a cut.** Let `e` cut the closed domain of `F`, with arcs `a`, `b` of `F`. A
preconnected set in the closed domain that misses the cut, and has a point of the arc `a` other
than the ends of the cut, lies in the closed domain of `a` and the cut. -/
theorem subset_side {F : Set ℂ} {a b e : 𝕀 → ℂ} (c : IsCut F a b e) (J : IsJordanParts F)
    {X : Set ℂ} (hX : IsPreconnected X) (hXF : X ⊆ closedInner F \ range e) {p : ℂ} (hpX : p ∈ X)
    (hpa : p ∈ range a \ {e 0, e 1}) : X ⊆ closedInner (side a e) := by
  obtain ⟨-, hcomp, -, -, -⟩ := c.components J
  have hsub := hX.subset_connectedComponentIn hpX hXF
  have hmem : connectedComponentIn (closedInner F \ range e) p ∈
      componentsIn (closedInner F \ range e) := mem_image_of_mem _ (hXF hpX)
  rw [hcomp] at hmem
  rcases hmem with h | h
  · exact fun q hq => (h ▸ hsub hq).1
  · -- `p` lies on the arc `a`, outside the closed domain on the side of `b`
    exfalso
    have T := (c.isTheta J).symm
    have hout : p ∈ outer (side b e) := T.open_arc_subset_outer hpa
    have hpb : p ∈ closedInner (side b e) :=
      (h ▸ mem_connectedComponentIn (hXF hpX) : p ∈ closedInner (side b e) \ range e).1
    rcases hpb with hpb | hpb
    · exact disjoint_left.mp T.parts₁.disjoint hpb hout
    · exact T.parts₁.outer_subset_compl hout hpb

namespace PlaneEmbedding

variable {K : SimpleGraph V} {R : Set V} (φ : PlaneEmbedding K R)

/-- **The drawing step of the gap.** Let `φ` be drawn in the closed domain of the `O`-arc `F`, let
`D = x M z L` be a cycle of `K`, let the image of `z L x` lie on `F`, and let the image of
`P = x M z` meet `F` only at the points of `x` and `z`. Let `𝒦` be a set of vertices off `P`,
containing `ℓ ∈ L`, in which every vertex is joined to `ℓ` by a walk of `K` inside `𝒦`. Then there
are no two disjoint paths of `K` with alternating ends on `D` whose vertices lie in `𝒦` or on `P`
and whose edges each have an end in `𝒦`. -/
theorem plane_gap {F : Set ℂ} (hF : Nonempty (Circle ≃ₜ F)) (hU : φ.U ⊆ closedInner F)
    {x z ℓ : V} {M L : List V} (hD : IsCycleList K (x :: (M ++ z :: L)))
    (hDR : ∀ v ∈ x :: (M ++ z :: L), v ∈ R) (hA : φ.pathImage (z :: (L ++ [x])) ⊆ F)
    (hγ : φ.pathImage (x :: (M ++ [z])) ∩ F ⊆ {φ.pt x, φ.pt z}) (hℓ : ℓ ∈ L) {𝒦 : Set V}
    (h𝒦R : 𝒦 ⊆ R) (h𝒦P : ∀ v ∈ 𝒦, v ∉ x :: (M ++ [z])) (hℓ𝒦 : ℓ ∈ 𝒦)
    (h𝒦 : ∀ v ∈ 𝒦, ∃ q : K.Walk ℓ v, ∀ t ∈ q.support, t ∈ 𝒦)
    {a b c d : V} (Q : K.Walk a b) (R' : K.Walk c d) (hQ : Q.IsPath) (hR' : R'.IsPath)
    (hdisj : Q.support.Disjoint R'.support)
    (hidx : ∃ i r j s : ℕ, i < r ∧ r < j ∧ j < s ∧ (x :: (M ++ z :: L))[i]? = some a ∧
      (x :: (M ++ z :: L))[r]? = some c ∧ (x :: (M ++ z :: L))[j]? = some b ∧
      (x :: (M ++ z :: L))[s]? = some d)
    (hQv : ∀ t ∈ Q.support, t ∈ 𝒦 ∨ t ∈ x :: (M ++ [z]))
    (hQe : ∀ p ∈ Q.support.zip Q.support.tail, p.1 ∈ 𝒦 ∨ p.2 ∈ 𝒦)
    (hRv : ∀ t ∈ R'.support, t ∈ 𝒦 ∨ t ∈ x :: (M ++ [z]))
    (hRe : ∀ p ∈ R'.support.zip R'.support.tail, p.1 ∈ 𝒦 ∨ p.2 ∈ 𝒦) : False := by
  classical
  set D := x :: (M ++ z :: L) with hDdef
  set P := x :: (M ++ [z]) with hPdef
  set A := z :: (L ++ [x]) with hAdef
  have hnd := hD.2.1
  have hDne : D ≠ [] := List.cons_ne_nil _ _
  have hDlen : D.length = M.length + L.length + 2 := by simp [D]; omega
  -- the two paths of the cycle `D` cut at `x` and `z`
  obtain ⟨hPl, hAl, hDimg, -⟩ := φ.cycleImage_split hD hDR hDne (k := M.length + 1) (by omega)
    (by omega)
  have e1 : (D ++ [D.head hDne]).take (M.length + 1 + 1) = P := by simp [D, P, List.take_append]
  have e2 : (D ++ [D.head hDne]).drop (M.length + 1) = A := by simp [D, A]
  rw [e1] at hPl
  rw [e2] at hAl
  rw [e1, e2] at hDimg
  have hPR : ∀ v ∈ P, v ∈ R := hPl.2.2
  have hxz : x ≠ z := by
    intro h
    simp only [D, List.nodup_cons, List.mem_append, List.mem_cons, not_or] at hnd
    exact hnd.1.2.1 h
  have hxR : x ∈ R := hDR x (by simp [D])
  have hzR : z ∈ R := hDR z (by simp [D])
  have hptxz : φ.pt x ≠ φ.pt z := fun h => hxz (φ.injOn hxR hzR h)
  -- the image `γ` of `P`, the image of `z L x`, and the other arc of `F`
  have hγl : IsLineWithEnds (φ.pathImage P) (φ.pt x) (φ.pt z) := by
    have := φ.isLine_pathImage (x := x) (l := M ++ [z]) (by simp) hPl
    simpa using this
  have hAl' : IsLineWithEnds (φ.pathImage A) (φ.pt z) (φ.pt x) := by
    have := φ.isLine_pathImage (x := z) (l := L ++ [x]) (by simp) hAl
    simpa using this
  obtain ⟨e, he, hre, he0, he1⟩ := hγl.exists_arc
  obtain ⟨a', ha', hra, ha0, ha1⟩ := hAl'.symm.exists_arc
  obtain ⟨φF⟩ := hF
  have J := isJordanParts φF
  obtain ⟨b', hb', hb0, hb1, hun, hmeet⟩ := exists_other_arc φF ha' (hra ▸ hA)
  have hcut : IsCut F a' b' e := by
    refine ⟨ha', hb', he, by rw [ha0, he0], by rw [ha1, he1], by rw [hb0, ha0, he0],
      by rw [hb1, ha1, he1], by rw [he0, he1]; exact hptxz, hun, hmeet, fun t h0 h1 => ?_⟩
    have hmem : e t ∈ φ.pathImage P := hre ▸ mem_range_self t
    rcases hU (φ.pathImage_subset_U hPl hmem) with h | h
    · exact h
    · exfalso
      rcases hγ ⟨hmem, h⟩ with h' | h'
      · exact h0 (he.2 (h'.trans he0.symm))
      · exact h1 (he.2 ((mem_singleton_iff.mp h').trans he1.symm))
  have hside : side a' e = φ.cycleImage D := by
    rw [hDimg, side, hra, hre, union_comm]
  -- `ℓ` is on the arc `z L x`, away from `x` and `z`
  have hℓR : ℓ ∈ R := h𝒦R hℓ𝒦
  have hℓx : ℓ ≠ x := fun h => by
    simp only [D, List.nodup_cons, List.mem_append, List.mem_cons, not_or] at hnd
    exact hnd.1.2.2 (h ▸ hℓ)
  have hℓz : ℓ ≠ z := fun h => by
    simp only [D, List.nodup_cons, List.mem_append, List.mem_cons, not_or, List.nodup_append]
      at hnd
    exact hnd.2.2.1.1 (h ▸ hℓ)
  have hℓa : φ.pt ℓ ∈ range a' \ {e 0, e 1} := by
    refine ⟨hra ▸ φ.pt_mem_pathImage hAl (by simp [A]) (by simp [A, hℓ]), ?_⟩
    rintro (h | h)
    · exact hℓx (φ.injOn hℓR hxR (h.trans he0))
    · exact hℓz (φ.injOn hℓR hzR ((mem_singleton_iff.mp h).trans he1))
  have hγsub : φ.pathImage P ⊆ closedInner (side a' e) := fun w hw =>
    Or.inr (Or.inr (hre ▸ hw))
  -- every connected set through a vertex of `𝒦`, inside the closed domain and off `γ`, lies on the
  -- side of `L`
  have claim1 : ∀ v ∈ 𝒦, ∀ Y : Set ℂ, IsPreconnected Y → Y ⊆ closedInner F → Disjoint Y (φ.pathImage P) →
      φ.pt v ∈ Y → Y ⊆ closedInner (side a' e) := by
    intro v hv Y hY hYF hYγ hvY
    obtain ⟨q, hq⟩ := h𝒦 v hv
    have hqp := q.bypass_isPath
    have hq𝒦 : ∀ t ∈ q.bypass.support, t ∈ 𝒦 := fun t ht => hq t (q.support_bypass_subset_support ht)
    have hql : IsPathList K R q.bypass.support :=
      isPathList_support hqp fun t ht => h𝒦R (hq𝒦 t ht)
    by_cases hvℓ : v = ℓ
    · subst hvℓ
      exact subset_side hcut J hY (fun w hw => ⟨hYF hw, fun h => disjoint_left.mp hYγ hw (hre ▸ h)⟩)
        hvY hℓa
    have h2 : 2 ≤ q.bypass.support.length := by
      cases h : q.bypass with
      | nil => exact absurd rfl hvℓ
      | cons _ q' =>
        rw [Walk.support_cons, List.length_cons]
        exact Nat.succ_le_succ (List.length_pos_of_mem (Walk.start_mem_support q'))
    obtain ⟨-, hS₁⟩ := φ.isCompact_isConnected_pathImage hql h2
    have hS₁γ : Disjoint (φ.pathImage q.bypass.support) (φ.pathImage P) :=
      φ.disjoint_pathImage hql hPl fun t h1 h2 => h𝒦P t (hq𝒦 t h1) h2
    have hS₁F : φ.pathImage q.bypass.support ⊆ closedInner F := (φ.pathImage_subset_U hql).trans hU
    have hℓS : φ.pt ℓ ∈ φ.pathImage q.bypass.support :=
      φ.pt_mem_pathImage hql h2 q.bypass.start_mem_support
    have hvS : φ.pt v ∈ φ.pathImage q.bypass.support :=
      φ.pt_mem_pathImage hql h2 q.bypass.end_mem_support
    have hW := hS₁.isPreconnected.union (φ.pt v) hvS hvY hY
    have := subset_side hcut J hW (fun w hw => ⟨?_, fun h => ?_⟩) (Or.inl hℓS) hℓa
    · exact subset_union_right.trans this
    · rcases hw with hw | hw
      · exact hS₁F hw
      · exact hYF hw
    · rw [hre] at h
      rcases hw with hw | hw
      · exact disjoint_left.mp hS₁γ hw h
      · exact disjoint_left.mp hYγ hw h
  -- the line of an edge `u w` with `u ∈ 𝒦` lies on the side of `L`
  have claim2 : ∀ u w, u ∈ 𝒦 → (w ∈ 𝒦 ∨ w ∈ P) → K.Adj u w →
      φ.line u w ⊆ closedInner (side a' e) := by
    intro u w hu hw huw
    have huR := h𝒦R hu
    have hwR : w ∈ R := by rcases hw with hw | hw; exacts [h𝒦R hw, hPR w hw]
    have hl := φ.isLine u huR w hwR huw
    have hlF : φ.line u w ⊆ closedInner F := (φ.line_subset_U huR hwR huw).trans hU
    have hlγ : φ.line u w ∩ φ.pathImage P ⊆ {φ.pt w} := by
      refine (φ.line_inter_pathImage_sub huR hwR huw hPl fun p hp he => ?_).trans ?_
      · have h1 : p.1 ∈ P := (List.of_mem_zip hp).1
        have h2 : p.2 ∈ P := List.mem_of_mem_tail (List.of_mem_zip hp).2
        rcases Sym2.eq_iff.mp he with ⟨h, -⟩ | ⟨h, -⟩
        · exact h𝒦P u hu (h ▸ h1)
        · exact h𝒦P u hu (h ▸ h2)
      · rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
        rcases ht1 with rfl | rfl
        · exact absurd ht2 (h𝒦P t hu)
        · rfl
    intro pt hpt
    by_cases hpw : pt = φ.pt w
    · subst hpw
      rcases hw with hw | hw
      · refine claim1 w hw {φ.pt w} isPreconnected_singleton
          (singleton_subset_iff.mpr (hlF hl.right_mem)) ?_ rfl rfl
        refine disjoint_singleton_left.mpr fun h => h𝒦P w hw ?_
        exact φ.mem_of_pt_mem_pathImage hPl hwR h
      · exact hγsub (φ.pt_mem_pathImage hPl (by simp [P]) hw)
    · refine claim1 u hu (φ.line u w \ {φ.pt w}) hl.isPreconnected_diff_right
        (sdiff_subset.trans hlF) ?_ ⟨hl.left_mem, fun h => ?_⟩ ⟨hpt, hpw⟩
      · refine disjoint_left.mpr fun q hq hqγ => hq.2 (hlγ ⟨hq.1, hqγ⟩)
      · have := φ.injOn huR hwR (mem_singleton_iff.mp h)
        exact huw.ne this
  -- so the images of both paths lie in the closed domain of the image of `D`
  have claim3 : ∀ {a b : V} (W : K.Walk a b),
      (∀ t ∈ W.support, t ∈ 𝒦 ∨ t ∈ P) → (∀ p ∈ W.support.zip W.support.tail, p.1 ∈ 𝒦 ∨ p.2 ∈ 𝒦) →
      φ.pathImage W.support ⊆ closedInner (side a' e) := by
    intro a b W hv he w hw
    simp only [pathImage, mem_iUnion] at hw
    obtain ⟨p, hp, hw⟩ := hw
    have hp1 : p.1 ∈ W.support := (List.of_mem_zip hp).1
    have hp2 : p.2 ∈ W.support := List.mem_of_mem_tail (List.of_mem_zip hp).2
    have hadj : K.Adj p.1 p.2 := isChain_iff_zip.mp W.isChain_adj_support p hp
    rcases he p hp with h | h
    · exact claim2 _ _ h (hv _ hp2) hadj hw
    · rw [φ.line_comm] at hw
      exact claim2 _ _ h (hv _ hp1) hadj.symm hw
  -- the crossing lemma in the closed disc bounded by the image of `D`
  have hWR : ∀ {a b : V} (W : K.Walk a b), (∀ t ∈ W.support, t ∈ 𝒦 ∨ t ∈ P) →
      ∀ t ∈ W.support, t ∈ R := fun W hv t ht => by
    rcases hv t ht with h | h
    exacts [h𝒦R h, hPR t h]
  have hQl := isPathList_support hQ (hWR Q hQv)
  have hRl := isPathList_support hR' (hWR R' hRv)
  obtain ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩ := hidx
  have hsl : s < D.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hs
    exact absurd hs (by simp)
  obtain ⟨_, hia⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨_, hrc⟩ := List.getElem?_eq_some_iff.mp hr
  obtain ⟨_, hjb⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨_, hsd⟩ := List.getElem?_eq_some_iff.mp hs
  have hne : ∀ {m m' : ℕ} (hm : m < D.length) (hm' : m' < D.length), m ≠ m' → D[m] ≠ D[m'] :=
    fun hm hm' h he => h ((List.Nodup.getElem_inj_iff hnd).mp he)
  have hlen : ∀ {u v : V} (q : K.Walk u v), u ≠ v → 2 ≤ q.support.length := by
    intro u v q huv
    cases q with
    | nil => exact absurd rfl huv
    | cons _ q =>
      rw [Walk.support_cons, List.length_cons]
      exact Nat.succ_le_succ (List.length_pos_of_mem (Walk.start_mem_support q))
  have hl1 := hlen Q (by
    rw [← hia, ← hjb]; exact hne (by omega) (by omega) (by omega))
  have hl2 := hlen R' (by
    rw [← hrc, ← hsd]; exact hne (by omega) (by omega) (by omega))
  obtain ⟨hA1, hA2⟩ := φ.isCompact_isConnected_pathImage hQl hl1
  obtain ⟨hB1, hB2⟩ := φ.isCompact_isConnected_pathImage hRl hl2
  obtain ⟨hDd, hDb⟩ := isClosedDisc_closedInner (φ.isOArc_cycleImage hD hDR)
  have hcross := φ.pairsCrossOn_cycleImage hD hDR hir hrj hjs hsl
  rw [← hDb, hia, hjb, hrc, hsd] at hcross
  have hQsub : φ.pathImage Q.support ⊆ closedInner (φ.cycleImage D) := hside ▸ claim3 Q hQv hQe
  have hRsub : φ.pathImage R'.support ⊆ closedInner (φ.cycleImage D) := hside ▸ claim3 R' hRv hRe
  have := disc_crossing.{0} (closedInner (φ.cycleImage D)) (φ.pathImage Q.support)
    (φ.pathImage R'.support) _ _ _ _ hDd hQsub hRsub hA1 hB1 hA2 hB2
    (φ.pt_mem_pathImage hQl hl1 (Walk.start_mem_support Q))
    (φ.pt_mem_pathImage hQl hl1 (Walk.end_mem_support Q))
    (φ.pt_mem_pathImage hRl hl2 (Walk.start_mem_support R'))
    (φ.pt_mem_pathImage hRl hl2 (Walk.end_mem_support R')) hcross
  exact not_disjoint_iff_nonempty_inter.mpr this (φ.disjoint_pathImage hQl hRl hdisj)

end PlaneEmbedding

end GraphMinor.HP25
