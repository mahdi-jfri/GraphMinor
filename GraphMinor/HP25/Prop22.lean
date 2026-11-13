module

public import GraphMinor.HP25.Rib
import GraphMinor.Surface.Lunes
import GraphMinor.Surface.SurfaceGraph

/-!
# Proposition 2.2: ribs and webs with a frame of length three

Humeau and Pous, arXiv:2505.16431v2, Proposition 2.2 (page 6): "The $3$-ribs are the triangles; the
$3$-webs are the cliques of order at least $3$." The paper gives no proof.

* `isRibOn_three_iff`: `G` on `R` is a rib with frame `abc` exactly when `R = {a, b, c}` and `abc` is a
  triangle of `G`. One direction is `IsRibOn.eq_three` (`HP25/Rib.lean`). For the other we draw the
  triangle with straight sides between the points `0`, `1` and `i` of the plane
  (`triangleEmbedding`). The drawn set is then the image `F` of the triangle, an `O`-arc, so the faces
  are the inner and the outer domain of `F`, both bounded by `F`.
* `isWebOn_three_iff`: `G` is a web on `S` with frame `abc` exactly when `a, b, c` are distinct
  vertices of `S` and `G` is the complete graph on `S`. A web with a triangle as rib has one triangle,
  so all clique vertices sit on it and are adjacent to each other and to `a, b, c`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface Complex

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-- The three corners `0`, `1`, `i` of the triangle we draw. -/
noncomputable def triPt : Fin 3 → ℂ := ![0, 1, I]

theorem triPt_injective : Function.Injective triPt := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triPt, Complex.ext_iff]

/-- Two sides of the triangle `0 1 i` meet only at a common corner. -/
theorem triPt_segment_inter (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l) (hne : s(i, j) ≠ s(k, l)) :
    segment ℝ (triPt i) (triPt j) ∩ segment ℝ (triPt k) (triPt l) ⊆ triPt '' ({i, j} ∩ {k, l}) := by
  rintro z ⟨h1, h2⟩
  rw [segment_eq_image'] at h1 h2
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := h1
  obtain ⟨u, ⟨hu0, hu1⟩, hu⟩ := h2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [triPt] at hij hkl hne hu ⊢ <;>
  · have h₁ := congrArg Complex.re hu
    have h₂ := congrArg Complex.im hu
    simp at h₁ h₂
    first
    | exact ⟨0, by decide, by apply Complex.ext <;> simp <;> linarith⟩
    | exact ⟨1, by decide, by apply Complex.ext <;> simp <;> linarith⟩
    | exact ⟨2, by decide, by apply Complex.ext <;> simp <;> linarith⟩

/-- A side of the triangle `0 1 i` passes through no third corner. -/
theorem triPt_mem_segment (i j k : Fin 3) (hij : i ≠ j) (h : triPt k ∈ segment ℝ (triPt i) (triPt j)) :
    k = i ∨ k = j := by
  rw [segment_eq_image'] at h
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [triPt] at hij ht ⊢ <;>
  · have h₁ := congrArg Complex.re ht
    have h₂ := congrArg Complex.im ht
    simp at h₁ h₂ <;> linarith

/-- If `a', b', c'` are three distinct members of `{a, b, c}`, then every member of `{a, b, c}` is
one of them. -/
theorem mem_of_three {a b c a' b' c' u : V} (ha : a' ∈ ({a, b, c} : Set V))
    (hb : b' ∈ ({a, b, c} : Set V)) (hc : c' ∈ ({a, b, c} : Set V)) (hab : a' ≠ b') (hbc : b' ≠ c')
    (hac : a' ≠ c') (hu : u ∈ ({a, b, c} : Set V)) : u ∈ ({a', b', c'} : Set V) := by
  simp only [mem_insert_iff, mem_singleton_iff] at ha hb hc hu ⊢
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl <;> simp_all

section Triangle

variable [DecidableEq V] {a b c : V}

/-- The corner of the drawn triangle that the vertex `v` goes to: `a ↦ 0`, `b ↦ 1`, others `↦ 2`. -/
def triIndex (a b : V) (v : V) : Fin 3 :=
  if v = a then 0 else if v = b then 1 else 2

theorem triIndex_injOn (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    InjOn (triIndex a b) {a, b, c} := by
  intro u hu v hv h
  simp only [mem_insert_iff, mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    simp_all [triIndex, hab.symm, hbc.symm, hac.symm]

/-- The triangle `abc` drawn with straight sides between `0`, `1` and `i`. -/
noncomputable def triangleEmbedding (G : SimpleGraph V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    PlaneEmbedding G {a, b, c} where
  pt v := triPt (triIndex a b v)
  line u v := segment ℝ (triPt (triIndex a b u)) (triPt (triIndex a b v))
  finite := by simp
  injOn := triPt_injective.injOn.comp (triIndex_injOn hab hbc hac) (mapsTo_univ _ _)
  line_comm u v := segment_symm ℝ _ _
  isLine u hu v hv h := isLineWithEnds_segment fun he =>
    h.ne (triIndex_injOn hab hbc hac hu hv (triPt_injective he))
  inter u hu v hv u' hu' v' hv' h h' hne := by
    have hI := triIndex_injOn hab hbc hac
    have hne' : s(triIndex a b u, triIndex a b v) ≠ s(triIndex a b u', triIndex a b v') := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hne (by rw [hI hu hu' h1, hI hv hv' h2])
      · exact hne (by rw [hI hu hv' h1, hI hv hu' h2, Sym2.eq_swap])
    refine (triPt_segment_inter _ _ _ _ (fun he => h.ne (hI hu hv he))
      (fun he => h'.ne (hI hu' hv' he)) hne').trans ?_
    rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hm1 hm2
    rcases hm1 with rfl | rfl
    · refine ⟨u, ⟨by simp, ?_⟩, rfl⟩
      rcases hm2 with h2 | h2
      · simp [hI hu hu' h2]
      · simp [hI hu hv' h2]
    · refine ⟨v, ⟨by simp, ?_⟩, rfl⟩
      rcases hm2 with h2 | h2
      · simp [hI hv hu' h2]
      · simp [hI hv hv' h2]
  avoid u hu v hv h w hw hwl := by
    have hI := triIndex_injOn hab hbc hac
    rcases triPt_mem_segment _ _ _ (fun he => h.ne (hI hu hv he)) hwl with h1 | h1
    · exact Or.inl (hI hw hu h1)
    · exact Or.inr (hI hw hv h1)

/-- In the drawn triangle, the drawn set is the image of any triangle of `G` on `{a, b, c}`. -/
theorem triangleEmbedding_U (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {a' b' c' : V}
    (hT : IsTriangleOn G {a, b, c} a' b' c') :
    (triangleEmbedding G hab hbc hac).U = (triangleEmbedding G hab hbc hac).cycleImage [a', b', c'] := by
  set φ := triangleEmbedding G hab hbc hac
  refine Subset.antisymm ?_ (φ.cycleImage_subset_U hT.isCycleList hT.mem)
  obtain ⟨ha', hb', hc', h1, h2, h3⟩ := hT
  have hmem := fun u (hu : u ∈ ({a, b, c} : Set V)) =>
    mem_of_three ha' hb' hc' h1.ne h2.ne h3.ne hu
  rw [φ.cycleImage_three]
  rintro z (⟨u, hu, rfl⟩ | hz)
  · rcases hmem u hu with rfl | rfl | rfl
    · exact Or.inl (Or.inl ((φ.isLine _ ha' _ hb' h1).left_mem))
    · exact Or.inl (Or.inr ((φ.isLine _ hb' _ hc' h2).left_mem))
    · exact Or.inr ((φ.isLine _ hc' _ ha' h3.symm).left_mem)
  · simp only [mem_iUnion] at hz
    obtain ⟨u, hu, v, hv, huv, hz⟩ := hz
    have hl := φ.line_comm
    rcases hmem u hu with rfl | rfl | rfl <;> rcases hmem v hv with rfl | rfl | rfl
    all_goals first
      | exact absurd huv (G.loopless.irrefl _)
      | (simp only [mem_union]; rw [hl] at hz; tauto)
      | (simp only [mem_union]; tauto)

end Triangle

/-- **Proposition 2.2**, ribs: "The $3$-ribs are the triangles." `G` on `R` is a rib with frame
`abc` exactly when `R = {a, b, c}` and `abc` is a triangle of `G`. -/
theorem isRibOn_three_iff {a b c : V} :
    IsRibOn G R [a, b, c] ↔ R = {a, b, c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a := by
  classical
  constructor
  · intro h
    refine ⟨h.eq_three, h.1.2.2 (a, b) (by simp [List.rotate]), h.1.2.2 (b, c) (by simp [List.rotate]),
      h.1.2.2 (c, a) (by simp [List.rotate])⟩
  · rintro ⟨rfl, hab, hbc, hca⟩
    have hT : IsTriangleOn G {a, b, c} a b c := ⟨by simp, by simp, by simp, hab, hbc, hca.symm⟩
    refine ⟨hT.isCycleList, hT.mem, triangleEmbedding G hab.ne hbc.ne hca.ne.symm, ?_⟩
    set φ := triangleEmbedding G hab.ne hbc.ne hca.ne.symm
    have hF := triangleEmbedding_U (G := G) hab.ne hbc.ne hca.ne.symm hT
    have J := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
    -- The faces are the two domains of the image of the triangle.
    have hface : ∀ r ∈ φ.faces, (r = inner (φ.cycleImage [a, b, c]) ∧ Bornology.IsBounded r) ∨
        (r = outer (φ.cycleImage [a, b, c]) ∧ ¬ Bornology.IsBounded r) := by
      rintro r ⟨z, hz, rfl⟩
      rw [hF, ← compl_eq_univ_sdiff] at hz ⊢
      have hz' := hz
      rw [← J.union_eq] at hz'
      rcases hz' with hz' | hz'
      · left
        have he : connectedComponentIn (φ.cycleImage [a, b, c])ᶜ z = inner (φ.cycleImage [a, b, c]) := by
          refine Subset.antisymm (fun w hw => ⟨connectedComponentIn_subset _ _ hw, ?_⟩)
            (J.isConnected_inner.isPreconnected.subset_connectedComponentIn hz' J.inner_subset_compl)
          rw [← connectedComponentIn_eq hw]
          exact hz'.2
        exact ⟨he, he ▸ J.isBounded_inner⟩
      · right
        have he : connectedComponentIn (φ.cycleImage [a, b, c])ᶜ z = outer (φ.cycleImage [a, b, c]) := by
          refine Subset.antisymm (fun w hw => ⟨connectedComponentIn_subset _ _ hw, ?_⟩)
            (J.isConnected_outer.isPreconnected.subset_connectedComponentIn hz' J.outer_subset_compl)
          rw [← connectedComponentIn_eq hw]
          exact hz'.2
        exact ⟨he, he ▸ J.not_isBounded_outer⟩
    have hinner : inner (φ.cycleImage [a, b, c]) ∈ φ.faces := by
      obtain ⟨z, hz⟩ := J.isConnected_inner.nonempty
      have hzU : z ∈ univ \ φ.U := ⟨mem_univ _, by rw [hF]; exact hz.1⟩
      rcases hface _ ⟨z, hzU, rfl⟩ with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [← h1]; exact ⟨z, hzU, rfl⟩
      · exact absurd (h1 ▸ mem_connectedComponentIn hzU) fun h => disjoint_left.mp J.disjoint hz h
    refine ⟨fun r hr hb => ?_, fun r hr hb => ?_, fun a' b' c' hT' => ?_⟩
    · rcases hface r hr with ⟨-, h⟩ | ⟨rfl, -⟩
      · exact absurd h hb
      · exact J.frontier_outer
    · rcases hface r hr with ⟨rfl, -⟩ | ⟨-, h⟩
      · exact ⟨a, b, c, hT, J.frontier_inner⟩
      · exact absurd hb h
    · refine ⟨_, hinner, J.isBounded_inner, ?_⟩
      rw [J.frontier_inner, ← hF, triangleEmbedding_U (G := G) hab.ne hbc.ne hca.ne.symm hT']

/-- **Proposition 2.2**, webs: "the $3$-webs are the cliques of order at least $3$." `G` is a web on
`S` with frame `abc` exactly when `a, b, c` are distinct vertices of `S` and `G` is the complete graph
on `S`. -/
theorem isWebOn_three_iff {S : Set V} {a b c : V} :
    IsWebOn G S [a, b, c] ↔ (a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c) ∧
      ∀ x y, G.Adj x y ↔ x ∈ S ∧ y ∈ S ∧ x ≠ y := by
  constructor
  · rintro ⟨hsupp, R, tri, hRS, hrib, hcl⟩
    obtain ⟨rfl, hab, hbc, hca⟩ := isRibOn_three_iff.mp hrib
    have ha : a ∈ S := hRS (by simp)
    have hb : b ∈ S := hRS (by simp)
    have hc : c ∈ S := hRS (by simp)
    -- Every clique vertex sits on the triangle `abc`.
    have htri : ∀ x ∈ S \ {a, b, c}, tri x = {a, b, c} := by
      intro x hx
      obtain ⟨⟨a', b', c', ⟨ha', hb', hc', h1, h2, h3⟩, he⟩, -⟩ := hcl x hx
      rw [he]
      refine Subset.antisymm ?_ fun u hu => mem_of_three ha' hb' hc' h1.ne h2.ne h3.ne hu
      rintro u (rfl | rfl | rfl) <;> assumption
    refine ⟨⟨ha, hb, hc, hab.ne, hbc.ne, hca.ne.symm⟩, fun x y => ?_⟩
    have key : ∀ x y, x ∈ S \ {a, b, c} → (G.Adj x y ↔ x ∈ S ∧ y ∈ S ∧ x ≠ y) := by
      intro x y hx
      rw [(hcl x hx).2 y, htri x hx]
      constructor
      · rintro (hy | ⟨hy, hyx, -⟩)
        · exact ⟨hx.1, hRS hy, fun h => hx.2 (h ▸ hy)⟩
        · exact ⟨hx.1, hy.1, hyx.symm⟩
      · rintro ⟨-, hy, hxy⟩
        by_cases hyR : y ∈ ({a, b, c} : Set V)
        · exact Or.inl hyR
        · exact Or.inr ⟨⟨hy, hyR⟩, Ne.symm hxy, htri y ⟨hy, hyR⟩⟩
    by_cases hx : x ∈ S \ {a, b, c}
    · exact key x y hx
    by_cases hy : y ∈ S \ {a, b, c}
    · rw [G.adj_comm, key y x hy]
      tauto
    by_cases hxS : x ∈ S
    · have hxR : x ∈ ({a, b, c} : Set V) := by_contra fun h => hx ⟨hxS, h⟩
      by_cases hyS : y ∈ S
      · have hyR : y ∈ ({a, b, c} : Set V) := by_contra fun h => hy ⟨hyS, h⟩
        refine ⟨fun h => ⟨hxS, hyS, h.ne⟩, fun h => ?_⟩
        have hxy := h.2.2
        simp only [mem_insert_iff, mem_singleton_iff] at hxR hyR
        rcases hxR with rfl | rfl | rfl <;> rcases hyR with rfl | rfl | rfl
        all_goals first
          | exact absurd rfl hxy
          | exact hab | exact hab.symm | exact hbc | exact hbc.symm | exact hca | exact hca.symm
      · exact ⟨fun h => absurd (hsupp h.symm) hyS, fun h => absurd h.2.1 hyS⟩
    · exact ⟨fun h => absurd (hsupp h) hxS, fun h => absurd h.1 hxS⟩
  · rintro ⟨⟨ha, hb, hc, hab, hbc, hac⟩, hG⟩
    have hrib : IsRibOn G {a, b, c} [a, b, c] :=
      isRibOn_three_iff.mpr ⟨rfl, (hG a b).mpr ⟨ha, hb, hab⟩, (hG b c).mpr ⟨hb, hc, hbc⟩,
        (hG c a).mpr ⟨hc, ha, hac.symm⟩⟩
    refine ⟨fun x y h => ((hG x y).mp h).1, {a, b, c}, fun _ => {a, b, c}, ?_, hrib, fun x hx => ?_⟩
    · rintro u (rfl | rfl | rfl) <;> assumption
    · refine ⟨⟨a, b, c, ⟨by simp, by simp, by simp, (hG a b).mpr ⟨ha, hb, hab⟩,
        (hG b c).mpr ⟨hb, hc, hbc⟩, (hG a c).mpr ⟨ha, hc, hac⟩⟩, rfl⟩, fun y => ?_⟩
      rw [hG]
      constructor
      · rintro ⟨-, hy, hxy⟩
        by_cases hyR : y ∈ ({a, b, c} : Set V)
        · exact Or.inl hyR
        · exact Or.inr ⟨⟨hy, hyR⟩, Ne.symm hxy, rfl⟩
      · rintro (hy | ⟨hy, hyx, -⟩)
        · refine ⟨hx.1, ?_, fun h => hx.2 (h ▸ hy)⟩
          rcases hy with rfl | rfl | rfl <;> assumption
        · exact ⟨hx.1, hy.1, hyx.symm⟩

end GraphMinor.HP25
