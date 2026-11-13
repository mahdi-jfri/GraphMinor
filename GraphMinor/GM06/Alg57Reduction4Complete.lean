module

public import GraphMinor.GM06.Alg57Reduction4Witness
public import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section5Splice
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section5SidedReduction4
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks
import GraphMinor.GM11.Rotation
import Mathlib.Topology.Order.IntermediateValue

/-!
# Every Reduction 4 gives a path of the kind `FIND_4` looks for

This is the completeness half of Lemma 13 of our proof of VI (5.7) (outlined in
`Alg57Algorithm.lean`) for `k ≥ 2`, at the level of drawings (`exists_reduction4_path_of_step`).
Given a printed Reduction 4 with contact `v` and new path `Qᵢ`, we find a contact `w` on `Pᵢ` and a
path `Q'` from `sᵢ` to `w` with the properties assumed in the soundness half
`section5AnyReductionApplies_of_reduction4_path`: `Q'` lies in the closure of `Rᵢ`, misses the other
linkage paths, meets the tail of `Pᵢ` from `w` only at `w`, and the subpath of `Pᵢ` from `sᵢ` to `w`
is not in the closure of `Rᵢ`.

The other paths are missed because the new family is a linkage. For the tail we cut `Qᵢ` at its
first vertex `w` on the tail from `v` (`walk_exists_append_first_mem`). The prefix test still
fails at `w`, because the subpath from `sᵢ` to `w` contains the subpath from `sᵢ` to `v`.

This last fact is about the order along an arc: a subarc of an arc `f` from `f a` to `f b` is
exactly `f '' [a, b]` (`range_eq_image_uIcc_of_subarc`). The proof pulls the subarc back to the
unit interval, where a continuous injective map is monotone.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-! ### Subarcs of an arc -/

/-- A subarc of an injective curve `f`, from `f a` to `f b`, is the image of the interval between
`a` and `b`. -/
theorem range_eq_image_uIcc_of_subarc {S : Type*} [TopologicalSpace S] [T2Space S]
    {f g : C(I, S)} (hf : Function.Injective f) (hg : Function.Injective g)
    (hsub : range g ⊆ range f) {a b : I} (ha : g 0 = f a) (hb : g 1 = f b) :
    range g = f '' uIcc a b := by
  have hemb : IsClosedEmbedding f := f.continuous.isClosedEmbedding hf
  choose h hh using fun x => hsub (mem_range_self x)
  have hfh : (f ∘ h) = g := funext hh
  have hc : Continuous h := by
    rw [hemb.isEmbedding.continuous_iff, hfh]
    exact g.continuous
  have hi : Function.Injective h := fun x y hxy => hg (by rw [← hh x, ← hh y, hxy])
  have h0 : h 0 = a := hf (by rw [hh, ha])
  have h1 : h 1 = b := hf (by rw [hh, hb])
  have hrange : range h = uIcc a b := by
    apply subset_antisymm
    · rintro _ ⟨x, rfl⟩
      rcases hc.strictMono_of_inj_boundedOrder' hi with hm | hm
      · have l := hm.monotone (bot_le : (⊥ : I) ≤ x)
        have r := hm.monotone (le_top : x ≤ (⊤ : I))
        rw [mem_uIcc]
        left
        exact ⟨h0 ▸ l, h1 ▸ r⟩
      · have l := hm.antitone (bot_le : (⊥ : I) ≤ x)
        have r := hm.antitone (le_top : x ≤ (⊤ : I))
        rw [mem_uIcc]
        right
        exact ⟨h1 ▸ r, h0 ▸ l⟩
    · have := intermediate_value_uIcc (a := (0 : I)) (b := 1) hc.continuousOn
      rw [h0, h1] at this
      exact this.trans (image_subset_range _ _)
  rw [← hfh, range_comp, hrange]

/-! ### Walks -/

/-- A walk to a vertex of `X` splits at its first vertex in `X`. -/
theorem walk_exists_append_first_mem {α β : Type*} {Gr : Graph α β} {s v : α}
    (W : GraphWalk Gr s v) (X : Set α) (hv : v ∈ X) :
    ∃ w ∈ X, ∃ (W₁ : GraphWalk Gr s w) (W₂ : GraphWalk Gr w v), W = W₁.append W₂ ∧
      ∀ y ∈ W₁.support, y ∈ X → y = w := by
  induction W with
  | nil h =>
    refine ⟨_, hv, GraphWalk.nil h, GraphWalk.nil h, rfl, ?_⟩
    intro y hy _
    simpa using hy
  | @cons u x w' e hlink rest ih =>
    by_cases hu : u ∈ X
    · refine ⟨u, hu, GraphWalk.nil hlink.left_mem, GraphWalk.cons hlink rest, rfl, ?_⟩
      intro y hy _
      simpa using hy
    · obtain ⟨w, hw, W₁, W₂, hW, hfirst⟩ := ih hv
      refine ⟨w, hw, GraphWalk.cons hlink W₁, W₂, by rw [hW]; rfl, ?_⟩
      intro y hy hyX
      rcases List.mem_cons.mp hy with rfl | hy
      · exact absurd hyX hu
      · exact hfirst y hy hyX

/-- Every edge of a walk links two vertices of the walk. -/
theorem walk_exists_isLink_of_mem_edges {α β : Type*} {Gr : Graph α β} {s v : α}
    (W : GraphWalk Gr s v) {e : β} (he : e ∈ W.edges) :
    ∃ y y', y ∈ W.support ∧ y' ∈ W.support ∧ Gr.IsLink e y y' := by
  induction W with
  | nil h => simp [GraphWalk.edges] at he
  | @cons u x w' f hlink rest ih =>
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨u, x, List.mem_cons_self, List.mem_cons_of_mem _ rest.start_mem_support, hlink⟩
    · obtain ⟨y, y', hy, hy', hl⟩ := ih he
      exact ⟨y, y', List.mem_cons_of_mem _ hy, List.mem_cons_of_mem _ hy', hl⟩

/-- A walk without repeated vertices has no loop. -/
theorem walk_not_isLink_self_of_nodup {α β : Type*} {Gr : Graph α β} {a b : α}
    (W : GraphWalk Gr a b) (hs : W.support.Nodup) {e : β} (he : e ∈ W.edges) {z : α}
    (hz : Gr.IsLink e z z) : False := by
  induction W with
  | nil hv => simp [GraphWalk.edges] at he
  | @cons u x w f hlink rest ih =>
    simp only [GraphWalk.support, List.nodup_cons] at hs
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he
    · rcases hlink.eq_and_eq_or_eq_and_eq hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hs.1 rest.start_mem_support
      · exact hs.1 rest.start_mem_support
    · exact ih hs.2 he

/-! ### Drawings -/

/-- A vertex of a drawing that lies in a subdrawing is a vertex of the subdrawing. -/
theorem mem_V_of_mem_U_of_isSubdrawing {S : Type*} [TopologicalSpace S] {A Γ : Drawing S}
    (hA : A.IsSubdrawing Γ) {x : S} (hx : x ∈ A.U) (hxV : x ∈ Γ.V) : x ∈ A.V := by
  by_contra hxA
  obtain ⟨e, he, hxe⟩ := A.exists_edge_of_mem hx hxA
  exact edge_notMem_V (hA.2 he) hxe hxV

/-! ### Completeness -/

/-- **Lemma 13, completeness, for `k ≥ 2`.** If Reduction 4 applies, then some vertex `w` of
some `Pᵢ` is in the closure of `Rᵢ`, the subpath of `Pᵢ` from `sᵢ` to `w` is not in that closure,
and some path `Q` of `G` from `sᵢ` to `w` lies in that closure, misses the other linkage paths,
and meets the tail of `Pᵢ` from `w` only at `w`. -/
theorem exists_reduction4_path_of_step {k : ℕ} {G G' : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} {L' : CylinderLinkage k G'} (hk : 1 < k)
    (h : Section5Reduction4Step k G L G' L') :
    ∃ (i : Fin k) (w : ClosedCylinder) (P_sw T Q : Drawing ClosedCylinder),
      w ∈ (L.pathDrawing i).V ∧ w ∈ closure (cylinderRegion k G i) ∧
      IsSubpathOf (L.pathDrawing i) P_sw (cylinderM1Point k i) w ∧
      ¬ P_sw.U ⊆ closure (cylinderRegion k G i) ∧
      IsSection5Tail (L.pathDrawing i) T w (L.curve i 1) ∧
      Q.IsSubdrawing G ∧ IsPathDrawing Q (cylinderM1Point k i) w ∧
      Q.U ⊆ closure (cylinderRegion k G i) ∧ Q.U ∩ T.U ⊆ {w} ∧
      ∀ j, j ≠ i → Disjoint Q.U (L.pathDrawing j).U := by
  classical
  obtain ⟨hGG, hcond⟩ := (section5Reduction4Step_iff_of_two_le hk).mp h
  subst G'
  obtain ⟨i, v, P_sv, P_vt, Q, hv, hvR, hsv, hT, hpre, hQG, -, hQ, hQR, hL'U, hL'j⟩ := hcond
  set P := L.pathDrawing i
  set s := cylinderM1Point k i
  set t := L.curve i 1
  have hPG : P.IsSubdrawing G := (L.isSubdrawing i).1
  obtain ⟨hfi, hfr, hf0, hf1⟩ := L.curve_parametrizes i
  set f := L.curve i
  -- every subarc of `P` is an interval of `f`
  have harc : ∀ (A : Drawing ClosedCylinder) (x y : ClosedCylinder), IsPathDrawing A x y →
      A.U ⊆ P.U → ∀ a b : I, f a = x → f b = y → A.U = f '' uIcc a b := by
    intro A x y hA hAP a b ha hb
    obtain ⟨g, hgi, hgr, hg0, hg1⟩ := hA.2
    rw [← hgr]
    exact range_eq_image_uIcc_of_subarc hfi hgi (by rw [hgr, hfr]; exact hAP)
      (by rw [hg0, ha]) (by rw [hg1, hb])
  have hinP : ∀ x ∈ P.U, ∃ c : I, f c = x := fun x hx => by
    rw [← hfr] at hx; exact hx
  obtain ⟨a, ha⟩ := hinP v (P.V_subset_U hv)
  have hsv_ne : s ≠ v := isPathDrawing_start_ne_end hsv.2.2
  have hsvU : P_sv.U = f '' uIcc 0 a := harc P_sv s v hsv.2.2 hsv.2.1 0 a hf0 ha
  -- the tail from `v` is `f '' [a, 1]`
  have hvtU : P_vt.U = f '' uIcc a 1 := by
    rcases hT with ⟨hvt, hU, -⟩ | ⟨-, hTP, hTpath⟩
    · have ha1 : a = 1 := hfi (by rw [ha, hf1, hvt])
      rw [hU, ha1, uIcc_self, image_singleton, hf1, hvt]
    · exact harc P_vt v t hTpath hTP a 1 ha hf1
  have hvtP : P_vt.IsSubdrawing G := by
    rcases hT with ⟨-, hU, hV⟩ | ⟨hTP, -, -⟩
    · refine ⟨?_, ?_⟩
      · rw [hV]; exact singleton_subset_iff.mpr (hPG.1 hv)
      · intro e he
        exfalso
        have hne := (he.2.2.1 : IsPathConnected e).nonempty
        obtain ⟨x, hx⟩ := hne
        have hxU : x ∈ P_vt.U := (he.2.1 hx).1
        have hxV : x ∉ P_vt.V := (he.2.1 hx).2
        rw [hU] at hxU
        rw [hV] at hxV
        exact hxV hxU
    · exact hTP.trans hPG
  have hvX : v ∈ P_vt.V := by
    rcases hT with ⟨-, -, hV⟩ | ⟨-, -, hTpath⟩
    · rw [hV]; exact mem_singleton _
    · exact (isPathDrawing_end_vertices hTpath).1
  -- cut `Q` at its first vertex on the tail
  obtain ⟨W, hW, hVQ, hEQ⟩ := hQ.1
  obtain ⟨w, hwX, W₁, W₂, hWsplit, hfirst⟩ := walk_exists_append_first_mem W P_vt.V hvX
  have hW₁s : W₁.support.Nodup := by
    have h := hW
    change W.support.Nodup at h
    rw [hWsplit, GraphWalk.support_append] at h
    exact h.of_append_left
  have hsupp : ∀ y ∈ W₁.support, y ∈ W.support := by
    intro y hy
    rw [hWsplit, GraphWalk.support_append]
    exact List.mem_append_left _ hy
  -- `sᵢ` is not on the tail, so `w ≠ sᵢ`
  have hsT : s ∉ P_vt.U := by
    rw [hvtU]
    rintro ⟨c, hc, hcs⟩
    have hc0 : c = 0 := hfi (by rw [hcs, hf0])
    rw [hc0, mem_uIcc] at hc
    rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
    · have ha0 : a = 0 := le_antisymm h1 unitInterval.nonneg'
      exact hsv_ne (by rw [← ha, ha0, hf0])
    · exact absurd (show (1 : ℝ) ≤ 0 from h1) (by norm_num)
  have hsw : s ≠ w := fun h => hsT (h ▸ P_vt.V_subset_U hwX)
  -- the truncated path
  let Q' := walkDrawing Q W₁
  have hQ'Q : Q'.IsSubdrawing Q := walkDrawing_isSubdrawing Q W₁
  have hQ'G : Q'.IsSubdrawing G := hQ'Q.trans hQG
  have hQ' : IsPathDrawing Q' s w := isPathDrawing_walkDrawing_of_isSimple Q hW₁s hsw
  have hvtV : P_vt.V ⊆ P.V := by
    rcases hT with ⟨-, -, hV⟩ | ⟨hTP, -, -⟩
    · rw [hV]; exact singleton_subset_iff.mpr hv
    · exact hTP.1
  have hwP : w ∈ P.V := hvtV hwX
  have hwQ : w ∈ Q.U := by
    apply Q.V_subset_U
    rw [hVQ]
    exact hsupp w W₁.end_mem_support
  have hwR : w ∈ closure (cylinderRegion k G i) := hQR hwQ
  obtain ⟨c, hc⟩ := hinP w (P.V_subset_U hwP)
  have hac : a ≤ c := by
    have hw' : w ∈ P_vt.U := P_vt.V_subset_U hwX
    rw [hvtU] at hw'
    obtain ⟨c', hc', hfc'⟩ := hw'
    have : c' = c := hfi (by rw [hfc', hc])
    rw [this, uIcc_of_le unitInterval.le_one'] at hc'
    exact hc'.1
  have hsP : s ∈ P.V := (isPathDrawing_end_vertices (L.isPath i)).1
  have htP : t ∈ P.V := (isPathDrawing_end_vertices (L.isPath i)).2
  obtain ⟨P_sw, hsw'⟩ := exists_subpath_of_isPathDrawing (L.isPath i) hsP hwP hsw
  have hswU : P_sw.U = f '' uIcc 0 c := harc P_sw s w hsw'.2.2 hsw'.2.1 0 c hf0 hc
  have hpre' : ¬ P_sw.U ⊆ closure (cylinderRegion k G i) := by
    intro hsub
    apply hpre
    rw [hsvU]
    refine subset_trans (image_mono ?_) (hswU ▸ hsub)
    rw [uIcc_of_le unitInterval.nonneg', uIcc_of_le unitInterval.nonneg']
    exact Icc_subset_Icc_right hac
  -- the tail from `w`
  obtain ⟨T, hTail, hTvt⟩ : ∃ T : Drawing ClosedCylinder,
      IsSection5Tail P T w t ∧ T.U ⊆ P_vt.U := by
    by_cases hwt : w = t
    · let T := walkDrawing P (GraphWalk.nil htP)
      have hTV : T.V = {t} := by
        rw [walkDrawing_V]
        ext x
        simp [GraphWalk.support]
      have hTU : T.U = {t} := by
        ext x
        rw [mem_walkDrawing_U]
        simp [GraphWalk.support, GraphWalk.edges]
      refine ⟨T, Or.inl ⟨hwt, by rw [hTU, hwt], by rw [hTV, hwt]⟩, ?_⟩
      rw [hTU, ← hwt]
      exact singleton_subset_iff.mpr (P_vt.V_subset_U hwX)
    · obtain ⟨T, hT'⟩ := exists_subpath_of_isPathDrawing (L.isPath i) hwP htP hwt
      refine ⟨T, Or.inr hT', ?_⟩
      rw [harc T w t hT'.2.2 hT'.2.1 c 1 hc hf1, hvtU]
      apply image_mono
      rw [uIcc_of_le unitInterval.le_one', uIcc_of_le unitInterval.le_one']
      exact Icc_subset_Icc_left hac
  -- `Q'` meets the tail from `w` only at `w`
  have hinter : Q'.U ∩ T.U ⊆ {w} := by
    rintro x ⟨hxQ, hxT⟩
    have hxvt : x ∈ P_vt.U := hTvt hxT
    by_cases hxV : x ∈ G.V
    · have hx1 : x ∈ Q'.V := mem_V_of_mem_U_of_isSubdrawing hQ'G hxQ hxV
      have hx2 : x ∈ P_vt.V := mem_V_of_mem_U_of_isSubdrawing hvtP hxvt hxV
      rw [walkDrawing_V] at hx1
      exact hfirst x hx1 hx2
    · exfalso
      have hxQ'V : x ∉ Q'.V := fun h => hxV (hQ'G.1 h)
      have hxvtV : x ∉ P_vt.V := fun h => hxV (hvtP.1 h)
      obtain ⟨e, he, hxe⟩ := Q'.exists_edge_of_mem hxQ hxQ'V
      obtain ⟨e', he', hxe'⟩ := P_vt.exists_edge_of_mem hxvt hxvtV
      have hee : e = e' := G.edge_eq_of_mem (hQ'G.2 he) (hvtP.2 he') hxe hxe'
      rw [walkDrawing_E] at he
      obtain ⟨y, y', hy, hy', hl⟩ := walk_exists_isLink_of_mem_edges W₁ he
      have hends : ∀ z, z ∈ closure e ∩ Q.V → z ∈ P_vt.V := by
        rintro z ⟨hz, hzQ⟩
        have : z ∈ closure e ∩ G.V := ⟨hz, hQG.1 hzQ⟩
        rw [hee, ← hvtP.closure_inter_V he'] at this
        exact this.2
      have hyw : y = w := hfirst y hy (hends y (by rw [hl.2.2.2]; exact mem_insert _ _))
      have hy'w : y' = w := hfirst y' hy'
        (hends y' (by rw [hl.2.2.2]; exact mem_insert_of_mem _ (mem_singleton _)))
      rw [hyw, hy'w] at hl
      exact walk_not_isLink_self_of_nodup W₁ hW₁s he hl
  refine ⟨i, w, P_sw, T, Q', hwP, hwR, hsw', hpre', hTail, hQ'G, hQ', hQ'Q.U_subset.trans hQR,
    hinter, fun j hj => ?_⟩
  have hQL' : Q.U ⊆ (L'.pathDrawing i).U := by rw [hL'U]; exact subset_union_left
  have hd : Disjoint (L'.pathDrawing i).U (L'.pathDrawing j).U := L'.pairwise_disjoint (Ne.symm hj)
  rw [(hL'j j hj).1] at hd
  exact (hd.mono_left hQL').mono_left hQ'Q.U_subset

end GraphMinor.GM06
