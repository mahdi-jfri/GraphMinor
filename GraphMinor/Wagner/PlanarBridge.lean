module

public import GraphMinor.Planar.Defs
public import GraphMinor.GM16.Defs
public import GraphMinor.HP25.Web
public import GraphMinor.GM05.SeriesParallelDefs
import GraphMinor.GM01.Basic
import GraphMinor.GM03.Section4
import GraphMinor.GM05.GraphDrawingMinor
import GraphMinor.GM05.MinorTransfer
import GraphMinor.GM11.Defs
import GraphMinor.GM16.EmbeddedLineGraphDrawing
import GraphMinor.Crossing.Sparse101
import GraphMinor.LRPlanarity.ExteriorK5
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.Jordan
import GraphMinor.Surface.SurfacePull

/-!
# Planarity bridges for Wagner's theorem

This file connects `GraphMinor.IsPlanar` (topological drawings of finite multigraphs on a 2-sphere)
with `HP25.PlaneEmbedding` (embeddings of finite simple graphs in `ℂ`), proves minor-closure of
`IsPlanar`, deduces that no planar graph has a `K₅` minor, and establishes planarity of the small
building blocks needed for Wagner's theorem (simple graphs on at most four vertices, a single vertex
with one loop, and two vertices joined by up to three parallel edges).
-/

public section

namespace GraphMinor.Wagner

open Set Function Topology Graph SimpleGraph GraphMinor.Surface

universe u v u' v'

/-- A multigraph `G : Graph α β` is *simple* if it has no loops and at most one edge between any
two vertices. -/
@[expose] def IsSimpleGraphRep {α : Type u} {β : Type v} (G : Graph α β) : Prop :=
  (∀ e x, ¬ G.IsLoopAt e x) ∧
    ∀ e₁ e₂ x y, G.IsLink e₁ x y → G.IsLink e₂ x y → e₁ = e₂

theorem isSimpleGraphRep_toGraph {α : Type u} (H : (⊤ : SimpleGraph α).Subgraph) :
    IsSimpleGraphRep (GM01.toGraph H) := by
  refine ⟨GM01.not_isLoopAt_toGraph H, ?_⟩
  intro e₁ e₂ x y h₁ h₂
  exact h₁.1.trans h₂.1.symm

theorem completeGraph_eq_toGraph_top (n : ℕ) :
    GM16.completeGraph n = GM01.toGraph (⊤ : (⊤ : SimpleGraph (Fin n)).Subgraph) := by
  ext e x y
  · rfl
  · change (x ≠ y ∧ e = s(x, y)) ↔ (e = s(x, y) ∧ (⊤ : (⊤ : SimpleGraph (Fin n)).Subgraph).Adj x y)
    simp [and_comm]

theorem isSimpleGraphRep_completeGraph (n : ℕ) : IsSimpleGraphRep (GM16.completeGraph n) := by
  rw [completeGraph_eq_toGraph_top]
  exact isSimpleGraphRep_toGraph _

/-- A minor of a planar graph is planar. -/
theorem isPlanar_of_isIsoMinor {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} (hG : IsPlanar G) (hm : IsIsoMinor H G) :
    IsPlanar H := by
  obtain ⟨_, _, S, tS, hS, hSph, ⟨Γ⟩⟩ := hG
  let _ : TopologicalSpace S := tS
  have hCS : IsClosedSurface S := (GM11.IsSphere.isClosedSurface hSph).1
  obtain ⟨ΓH⟩ := GM05.graphDrawing_isIsoMinor hCS Γ hm
  exact IsPlanar.of_graphDrawing hS hSph ΓH

/-- Every simple `Graph α β` is canonically isomorphic to `GM01.toGraph (GM05.simpleShadow G)`. -/
noncomputable def isoToGraphSimpleShadow {α : Type u} {β : Type v} (G : Graph α β)
    (hS : IsSimpleGraphRep G) : Iso G (GM01.toGraph (GM05.simpleShadow G)) := by
  classical
  have hf : ∀ e : E(G), ∃ q : E(GM01.toGraph (GM05.simpleShadow G)),
      ∀ x y, G.IsLink e.1 x y ↔ (GM01.toGraph (GM05.simpleShadow G)).IsLink q.1 x y := by
    intro ⟨e, he⟩
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
    have hne : x ≠ y := fun h => hS.1 e x (h ▸ hxy)
    have hq_mem : s(x, y) ∈ E(GM01.toGraph (GM05.simpleShadow G)) :=
      (GM01.isLink_toGraph (GM05.simpleShadow G) s(x, y) x y).mpr ⟨rfl, hne, e, hxy⟩ |>.edge_mem
    refine ⟨⟨s(x, y), hq_mem⟩, fun u v => ?_⟩
    rw [GM01.isLink_toGraph]
    constructor
    · intro huv
      have heq : s(x, y) = s(u, v) := hxy.isLink_iff_sym2_eq.mp huv
      exact ⟨heq, fun h => hS.1 e u (h ▸ huv), e, huv⟩
    · rintro ⟨heq, _, e', huv'⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hS.2 e e' x y hxy huv' ▸ huv'
      · exact hS.2 e e' x y hxy huv'.symm ▸ huv'
  choose toQ htoQ using hf
  have hbij : Bijective toQ := by
    refine ⟨fun e₁ e₂ heq => ?_, fun ⟨q, hq⟩ => ?_⟩
    · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet e₁.2
      have hq₁ := (htoQ e₁ x y).mp hxy
      rw [heq] at hq₁
      have hxy₂ := (htoQ e₂ x y).mpr hq₁
      exact Subtype.ext (hS.2 e₁.1 e₂.1 x y hxy hxy₂)
    · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hq
      obtain ⟨rfl, _, e, he⟩ := (GM01.isLink_toGraph _ _ _ _).mp hxy
      refine ⟨⟨e, he.edge_mem⟩, Subtype.ext ?_⟩
      exact ((htoQ ⟨e, he.edge_mem⟩ x y).mp he).1
  exact
    { vertexEquiv := Equiv.refl V(G)
      edgeEquiv := Equiv.ofBijective toQ hbij
      isLink_iff := fun e x y => htoQ e x.1 y.1 }

/-- A plane embedding of `(GM05.simpleShadow G).spanningCoe` on `V(G)` yields `IsPlanar G` for any
finite simple graph `G`. -/
theorem isPlanar_of_planeEmbedding {α : Type u} {β : Type v} {G : Graph α β}
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hS : IsSimpleGraphRep G)
    (hemb : Nonempty (HP25.PlaneEmbedding (GM05.simpleShadow G).spanningCoe V(G))) :
    IsPlanar G := by
  classical
  obtain ⟨φ⟩ := hemb
  apply IsPlanar.of_plane_openEmbedding
  intro S _ _ j hj
  let eC : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  let f : α → ℝ × ℝ := fun v => eC (φ.pt v)
  have hf : InjOn f V(G) := eC.injective.injOn.comp φ.injOn (mapsTo_univ _ _)
  let L : β → Set (ℝ × ℝ) := fun e =>
    if he : e ∈ E(G) then
      let x := Classical.choose (exists_isLink_of_mem_edgeSet he)
      let y := Classical.choose (Classical.choose_spec (exists_isLink_of_mem_edgeSet he))
      eC '' φ.line x y
    else ∅
  have hLine_eq : ∀ e (he : e ∈ E(G)) a b, G.IsLink e a b → L e = eC '' φ.line a b := by
    intro e he a b hab
    dsimp only [L]
    simp only [he, ↓reduceDIte]
    set x := Classical.choose (exists_isLink_of_mem_edgeSet he)
    set y := Classical.choose (Classical.choose_spec (exists_isLink_of_mem_edgeSet he))
    have hxy : G.IsLink e x y :=
      Classical.choose_spec (Classical.choose_spec (exists_isLink_of_mem_edgeSet he))
    rcases Sym2.eq_iff.mp (hxy.isLink_iff_sym2_eq.mp hab) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [φ.line_comm]
  obtain ⟨Γ, -, -, -⟩ := GM16.exists_graphDrawing_of_embedded_lines G hVG hEG f hf L hS.1
    (fun e he a b hab => by
      have hne : a ≠ b := fun h => hS.1 e a (h ▸ hab)
      have hadj : (GM05.simpleShadow G).spanningCoe.Adj a b := ⟨hne, e, hab⟩
      rw [hLine_eq e he a b hab]
      exact (φ.isLine a hab.left_mem b hab.right_mem hadj).map_of_embedding eC.isEmbedding)
    (fun e he v hv hfv => by
      obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet he
      rw [hLine_eq e he a b hab] at hfv
      obtain ⟨z, hz, hzf⟩ := hfv
      have hzv : z = φ.pt v := eC.injective hzf
      have hne : a ≠ b := fun h => hS.1 e a (h ▸ hab)
      have hadj : (GM05.simpleShadow G).spanningCoe.Adj a b := ⟨hne, e, hab⟩
      rcases φ.avoid a hab.left_mem b hab.right_mem hadj v hv (hzv ▸ hz) with rfl | rfl
      · exact hab.inc_left
      · exact hab.inc_right)
    (fun e he d hd hne => by
      obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet he
      obtain ⟨a', b', hab'⟩ := exists_isLink_of_mem_edgeSet hd
      rw [hLine_eq e he a b hab, hLine_eq d hd a' b' hab']
      have hne1 : a ≠ b := fun h => hS.1 e a (h ▸ hab)
      have hne2 : a' ≠ b' := fun h => hS.1 d a' (h ▸ hab')
      have hadj1 : (GM05.simpleShadow G).spanningCoe.Adj a b := ⟨hne1, e, hab⟩
      have hadj2 : (GM05.simpleShadow G).spanningCoe.Adj a' b' := ⟨hne2, d, hab'⟩
      have hsne : s(a, b) ≠ s(a', b') := by
        intro hs
        rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hne (hS.2 e d a b hab hab')
        · exact hne (hS.2 e d a b hab hab'.symm)
      rintro w ⟨⟨z₁, hz₁, rfl⟩, ⟨z₂, hz₂, heq⟩⟩
      have hz : z₁ = z₂ := eC.injective heq.symm
      subst hz
      obtain ⟨v, ⟨hv1, hv2⟩, rfl⟩ :=
        φ.inter a hab.left_mem b hab.right_mem a' hab'.left_mem b' hab'.right_mem
          hadj1 hadj2 hsne ⟨hz₁, hz₂⟩
      refine ⟨v, ?_, rfl⟩
      rcases hv1 with rfl | rfl
      · exact hab.left_mem
      · exact hab.right_mem)
    j hj.isEmbedding
  exact ⟨Γ⟩

/-- Every planar simple graph admits a `HP25.PlaneEmbedding` in `ℂ` via stereographic puncture
away from the drawn set. -/
theorem planeEmbedding_of_isPlanar {α : Type u} {β : Type v} {G : Graph α β}
    (hS : IsSimpleGraphRep G) (hG : IsPlanar G) :
    Nonempty (HP25.PlaneEmbedding (GM05.simpleShadow G).spanningCoe V(G)) := by
  classical
  obtain ⟨hVG, _, S, tS, _, hSph, ⟨Γ⟩⟩ := hG
  let _ : TopologicalSpace S := tS
  have hCS : IsClosedSurface S := (GM11.IsSphere.isClosedSurface hSph).1
  let _ : T2Space S := hCS.2.1
  let _ : ConnectedSpace S := (GM11.IsSphere.isClosedSurface hSph).2
  obtain ⟨y₀, -, hy₀U⟩ := GM11.exists_notMem_U (Γ := Γ.drawing) hCS isOpen_univ univ_nonempty
  obtain ⟨eSph⟩ := hSph
  obtain ⟨reflH, hreflH⟩ := exists_homeomorph_onePoint (eSph y₀)
  let E : S ≃ₜ OnePoint EuclideanPlane := eSph.trans reflH
  have hEy₀ : E y₀ = OnePoint.infty := hreflH
  let j : ℂ → S := fun z => E.symm ((complexPlane z : EuclideanPlane) : OnePoint EuclideanPlane)
  have hj : IsOpenEmbedding j :=
    E.symm.isOpenEmbedding.comp
      (OnePoint.isOpenEmbedding_coe.comp complexPlane.toHomeomorph.isOpenEmbedding)
  have hU_range : Γ.drawing.U ⊆ range j := by
    intro s hs
    have hs_ne : s ≠ y₀ := fun h => hy₀U (h ▸ hs)
    have hEs_ne : E s ≠ OnePoint.infty := fun h => hs_ne (E.injective (h.trans hEy₀.symm))
    rcases hEs : E s with _ | p
    · exact (hEs_ne hEs).elim
    · refine ⟨complexPlane.symm p, ?_⟩
      dsimp only [j]
      rw [complexPlane.apply_symm_apply]
      exact E.symm_apply_eq.mpr hEs.symm
  have hpt_ex : ∀ (u : α) (hu : u ∈ V(G)), ∃ z : ℂ, j z = (Γ.iso.vertexEquiv ⟨u, hu⟩).1 := by
    intro u hu
    exact hU_range (Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨u, hu⟩).2)
  let pt : α → ℂ := fun u =>
    if hu : u ∈ V(G) then Classical.choose (hpt_ex u hu) else 0
  have hpt_spec : ∀ u (hu : u ∈ V(G)), j (pt u) = (Γ.iso.vertexEquiv ⟨u, hu⟩).1 := by
    intro u hu
    dsimp only [pt]
    simp only [hu, ↓reduceDIte]
    exact Classical.choose_spec (hpt_ex u hu)
  let edgeForSym : Sym2 α → Option E(G) := fun q =>
    if h : ∃ e : E(G), ∃ x y, q = s(x, y) ∧ G.IsLink e.1 x y then
      some (Classical.choose h)
    else none
  have hedgeForSym_eq : ∀ (e : β) (u v : α) (hab : G.IsLink e u v),
      edgeForSym s(u, v) = some ⟨e, hab.edge_mem⟩ := by
    intro e u v hab
    have hex : ∃ e' : E(G), ∃ x y, s(u, v) = s(x, y) ∧ G.IsLink e'.1 x y :=
      ⟨⟨e, hab.edge_mem⟩, u, v, rfl, hab⟩
    dsimp only [edgeForSym]
    simp only [hex, ↓reduceDIte]
    obtain ⟨x, y, hq, hlink⟩ := Classical.choose_spec hex
    congr 1
    apply Subtype.ext
    rcases Sym2.eq_iff.mp hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hS.2 _ e u v hlink hab
    · exact hS.2 _ e u v hlink.symm hab
  let line : α → α → Set ℂ := fun u v =>
    match edgeForSym s(u, v) with
    | some e => j ⁻¹' closure (Γ.iso.edgeEquiv e).1
    | none => ∅
  refine ⟨{
    pt := pt
    line := line
    finite := hVG
    injOn := fun u hu v hv huv => by
      have h1 := hpt_spec u hu
      have h2 := hpt_spec v hv
      rw [huv] at h1
      have heq := Γ.iso.vertexEquiv.injective (Subtype.ext (h1.symm.trans h2))
      exact congrArg Subtype.val heq
    line_comm := fun u v => by
      dsimp only [line]
      rw [Sym2.eq_swap]
    isLine := fun u hu v hv hadj => by
      obtain ⟨hne, e, hab⟩ := hadj
      have hline : line u v = j ⁻¹' closure (Γ.iso.edgeEquiv ⟨e, hab.edge_mem⟩).1 := by
        dsimp only [line]
        rw [hedgeForSym_eq e u v hab]
      rw [hline]
      set ed := Γ.iso.edgeEquiv ⟨e, hab.edge_mem⟩
      have hed_link : Γ.drawing.toGraph.IsLink ed.1 (j (pt u)) (j (pt v)) := by
        rw [hpt_spec u hu, hpt_spec v hv]
        exact (Γ.iso.isLink_iff ⟨e, hab.edge_mem⟩ ⟨u, hu⟩ ⟨v, hv⟩).mp hab
      have hcap : closure ed.1 ∩ Γ.drawing.V = {j (pt u), j (pt v)} := hed_link.2.2.2
      have hjne : j (pt u) ≠ j (pt v) := by
        intro hj_eq
        rw [hpt_spec u hu, hpt_spec v hv] at hj_eq
        exact hne (congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext hj_eq)))
      have hL_S : IsLineWithEnds (closure ed.1) (j (pt u)) (j (pt v)) := by
        rcases Γ.drawing.edge_cond ed.1 ed.2 with ⟨a, b, _, hcap', hL⟩ | ⟨a, hcap', -⟩
        · have hpair : ({a, b} : Set S) = {j (pt u), j (pt v)} := hcap'.symm.trans hcap
          have ha_mem : a ∈ ({j (pt u), j (pt v)} : Set S) := hpair ▸ mem_insert a {b}
          have hb_mem : b ∈ ({j (pt u), j (pt v)} : Set S) := hpair ▸ mem_insert_of_mem a rfl
          rcases ha_mem with rfl | rfl <;> rcases hb_mem with rfl | rfl
          · have hju_in : j (pt v) ∈ ({j (pt u), j (pt u)} : Set S) :=
              hpair.symm ▸ mem_insert_of_mem (j (pt u)) rfl
            simp only [mem_insert_iff, mem_singleton_iff, or_self] at hju_in
            exact (hjne hju_in.symm).elim
          · exact hL
          · exact hL.symm
          · have hju_in : j (pt u) ∈ ({j (pt v), j (pt v)} : Set S) :=
              hpair.symm ▸ mem_insert (j (pt u)) _
            simp only [mem_insert_iff, mem_singleton_iff, or_self] at hju_in
            exact (hjne hju_in).elim
        · have hpair : ({a} : Set S) = {j (pt u), j (pt v)} := hcap'.symm.trans hcap
          have h1 : j (pt u) = a := mem_singleton_iff.mp (hpair.symm ▸ mem_insert _ _)
          have h2 : j (pt v) = a := mem_singleton_iff.mp (hpair.symm ▸ mem_insert_of_mem _ rfl)
          exact (hjne (h1.trans h2.symm)).elim
      have hsub : closure ed.1 ⊆ range j :=
        (Γ.drawing.closure_subset_U ed.2).trans hU_range
      obtain ⟨u', v', hu', hv', hp⟩ := hL_S.pull hj.isEmbedding hsub
      rwa [hj.injective hu', hj.injective hv'] at hp
    inter := fun u hu v hv u' hu' v' hv' hadj hadj' hsne => by
      obtain ⟨_, e, hab⟩ := hadj
      obtain ⟨_, e', hab'⟩ := hadj'
      have hline1 : line u v = j ⁻¹' closure (Γ.iso.edgeEquiv ⟨e, hab.edge_mem⟩).1 := by
        dsimp only [line]; rw [hedgeForSym_eq e u v hab]
      have hline2 : line u' v' = j ⁻¹' closure (Γ.iso.edgeEquiv ⟨e', hab'.edge_mem⟩).1 := by
        dsimp only [line]; rw [hedgeForSym_eq e' u' v' hab']
      rw [hline1, hline2]
      set ed := Γ.iso.edgeEquiv ⟨e, hab.edge_mem⟩
      set ed' := Γ.iso.edgeEquiv ⟨e', hab'.edge_mem⟩
      have hee' : e ≠ e' := by
        rintro rfl
        exact hsne (hab.isLink_iff_sym2_eq.mp hab')
      have heded' : ed.1 ≠ ed'.1 := fun h =>
        hee' (congrArg Subtype.val (Γ.iso.edgeEquiv.injective (Subtype.ext h)))
      have hcap1 : closure ed.1 ∩ Γ.drawing.V = {j (pt u), j (pt v)} := by
        rw [hpt_spec u hu, hpt_spec v hv]
        exact ((Γ.iso.isLink_iff ⟨e, hab.edge_mem⟩ ⟨u, hu⟩ ⟨v, hv⟩).mp hab).2.2.2
      have hcap2 : closure ed'.1 ∩ Γ.drawing.V = {j (pt u'), j (pt v')} := by
        rw [hpt_spec u' hu', hpt_spec v' hv']
        exact ((Γ.iso.isLink_iff ⟨e', hab'.edge_mem⟩ ⟨u', hu'⟩ ⟨v', hv'⟩).mp hab').2.2.2
      rintro z ⟨hz1, hz2⟩
      have hjzV : j z ∈ Γ.drawing.V := by
        by_contra hnV
        have hm1 : j z ∈ ed.1 := by
          rw [← Γ.drawing.closure_diff_V ed.2]; exact ⟨hz1, hnV⟩
        have hm2 : j z ∈ ed'.1 := by
          rw [← Γ.drawing.closure_diff_V ed'.2]; exact ⟨hz2, hnV⟩
        exact heded' (Γ.drawing.edge_eq_of_mem ed.2 ed'.2 hm1 hm2)
      have hj1 : j z ∈ ({j (pt u), j (pt v)} : Set S) := hcap1 ▸ ⟨hz1, hjzV⟩
      have hj2 : j z ∈ ({j (pt u'), j (pt v')} : Set S) := hcap2 ▸ ⟨hz2, hjzV⟩
      have hinjpt : InjOn pt V(G) := fun a ha b hb hab_pt => by
        have h1 := hpt_spec a ha
        have h2 := hpt_spec b hb
        rw [hab_pt] at h1
        exact congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext (h1.symm.trans h2)))
      rcases hj1 with hj1 | hj1 <;> rcases hj2 with hj2 | hj2
      · have hzx := hj.injective hj1
        have hux : u = u' := hinjpt hu hu' (hzx.symm.trans (hj.injective hj2))
        subst hux; exact ⟨u, ⟨by simp, by simp⟩, hzx.symm⟩
      · have hzx := hj.injective hj1
        have hux : u = v' := hinjpt hu hv' (hzx.symm.trans (hj.injective hj2))
        subst hux; exact ⟨u, ⟨by simp, by simp⟩, hzx.symm⟩
      · have hzx := hj.injective hj1
        have hvx : v = u' := hinjpt hv hu' (hzx.symm.trans (hj.injective hj2))
        subst hvx; exact ⟨v, ⟨by simp, by simp⟩, hzx.symm⟩
      · have hzx := hj.injective hj1
        have hvx : v = v' := hinjpt hv hv' (hzx.symm.trans (hj.injective hj2))
        subst hvx; exact ⟨v, ⟨by simp, by simp⟩, hzx.symm⟩
    avoid := fun u hu v hv hadj w hw hzw => by
      obtain ⟨_, e, hab⟩ := hadj
      have hline : line u v = j ⁻¹' closure (Γ.iso.edgeEquiv ⟨e, hab.edge_mem⟩).1 := by
        dsimp only [line]; rw [hedgeForSym_eq e u v hab]
      rw [hline] at hzw
      set ed := Γ.iso.edgeEquiv ⟨e, hab.edge_mem⟩
      have hcap : closure ed.1 ∩ Γ.drawing.V = {j (pt u), j (pt v)} := by
        rw [hpt_spec u hu, hpt_spec v hv]
        exact ((Γ.iso.isLink_iff ⟨e, hab.edge_mem⟩ ⟨u, hu⟩ ⟨v, hv⟩).mp hab).2.2.2
      have hjwV : j (pt w) ∈ Γ.drawing.V := by
        rw [hpt_spec w hw]
        exact (Γ.iso.vertexEquiv ⟨w, hw⟩).2
      have hmem : j (pt w) ∈ ({j (pt u), j (pt v)} : Set S) := hcap ▸ ⟨hzw, hjwV⟩
      have hinjpt : InjOn pt V(G) := fun a ha b hb hab_pt => by
        have h1 := hpt_spec a ha
        have h2 := hpt_spec b hb
        rw [hab_pt] at h1
        exact congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext (h1.symm.trans h2)))
      rcases hmem with h1 | h1
      · exact Or.inl (hinjpt hw hu (hj.injective h1))
      · exact Or.inr (hinjpt hw hv (hj.injective h1)) }⟩

/-- The complete graph `K₅` is not planar. -/
theorem not_isPlanar_completeGraph_five : ¬ IsPlanar (GM16.completeGraph 5) := by
  intro hP
  obtain ⟨φ⟩ := planeEmbedding_of_isPlanar (isSimpleGraphRep_completeGraph 5) hP
  have htop : (GM05.simpleShadow (GM16.completeGraph 5)).spanningCoe = (⊤ : SimpleGraph (Fin 5)) := by
    ext x y
    change (x ≠ y ∧ (GM16.completeGraph 5).Adj x y) ↔ x ≠ y
    simp only [and_iff_left_iff_imp]
    intro hne
    exact ⟨s(x, y), hne, rfl⟩
  have hV : V(GM16.completeGraph 5) = (Set.univ : Set (Fin 5)) := rfl
  rw [htop, hV] at φ
  exact LRPlanarity.not_planeEmbedding_K5 ⟨φ⟩

/-- No planar graph has a minor isomorphic to `K₅`. -/
theorem not_isIsoMinor_completeGraph_five_of_isPlanar {α : Type u} {β : Type v}
    {G : Graph α β} (hG : IsPlanar G) : ¬ IsIsoMinor (GM16.completeGraph 5) G :=
  fun hm => not_isPlanar_completeGraph_five (isPlanar_of_isIsoMinor hG hm)

/-- Every finite simple graph on at most four vertices is planar. -/
theorem isPlanar_of_simple_ncard_le_four {α : Type u} {β : Type v} {G : Graph α β}
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hS : IsSimpleGraphRep G)
    (hcard : V(G).ncard ≤ 4) : IsPlanar G := by
  have hsupp : HP25.IsSupportedOn (GM05.simpleShadow G).spanningCoe V(G) := by
    rintro x y ⟨_, e, hxy⟩
    exact hxy.left_mem
  have hemb : Nonempty (HP25.PlaneEmbedding (GM05.simpleShadow G).spanningCoe V(G)) := by
    by_contra hnp
    have h5 := Crossing.sec101Five_proved (GM05.simpleShadow G).spanningCoe V(G) hVG hsupp hnp
    omega
  exact isPlanar_of_planeEmbedding hVG hEG hS hemb

/-- The null graph `⊥` is planar. -/
theorem isPlanar_bot (α : Type u) (β : Type v) : IsPlanar (⊥ : Graph α β) := by
  apply isPlanar_of_simple_ncard_le_four
  · simp
  · simp
  · refine ⟨fun e x h => ?_, fun e₁ e₂ x y h₁ _ => by simp at h₁⟩
    change (⊥ : Graph α β).IsLink e x x at h
    simp at h
  · simp

/-- `K_n` is planar for every `n ≤ 4`. -/
theorem isPlanar_completeGraph_of_le_four {n : ℕ} (hn : n ≤ 4) :
    IsPlanar (GM16.completeGraph n) := by
  apply isPlanar_of_simple_ncard_le_four Set.finite_univ (Set.toFinite _)
    (isSimpleGraphRep_completeGraph n)
  change (Set.univ : Set (Fin n)).ncard ≤ 4
  rw [Set.ncard_univ, Nat.card_fin]
  exact hn

/-- Every graph consisting of a single vertex and a single loop edge is planar, as a minor of `K₃`. -/
theorem isPlanar_of_single_loop {α : Type u} {β : Type v} {G : Graph α β} {v : α} {e : β}
    (hV : V(G) = {v}) (hE : E(G) = {e}) (hlink : G.IsLink e v v) : IsPlanar G := by
  classical
  let K₃ := GM16.completeGraph 3
  let ηv : α → Set (Fin 3) := fun _ => Set.univ
  let ηe : β → Sym2 (Fin 3) := fun _ => s(0, 2)
  have hVG : V(G).Finite := hV ▸ finite_singleton v
  have hEG : E(G).Finite := hE ▸ finite_singleton e
  have hm : IsIsoMinor G K₃ := by
    refine isIsoMinor_of_isMinorModel G K₃ hVG hEG finite_univ (Set.toFinite _) ηv ηe ?_
    refine
      { vertex_nonempty := fun _ _ => ⟨0, trivial⟩
        vertex_subset := fun _ _ _ _ => trivial
        edge_mem := fun _ _ => ⟨0, 2, by decide, rfl⟩
        vertex_disjoint := fun x hx y hy hxy => by
          rw [hV, mem_singleton_iff] at hx hy
          exact (hxy (hx.trans hy.symm)).elim
        edge_injOn := fun d₁ hd₁ d₂ hd₂ _ => by
          rw [hE, mem_singleton_iff] at hd₁ hd₂
          exact hd₁.trans hd₂.symm
        inc_iff := fun x hx d hd => by
          rw [hV, mem_singleton_iff] at hx
          rw [hE, mem_singleton_iff] at hd
          subst x d
          refine ⟨fun _ => ⟨0, trivial, 2, by decide, rfl⟩, fun _ => hlink.inc_left⟩
        isLoopAt_iff := fun x hx d hd => by
          rw [hV, mem_singleton_iff] at hx
          rw [hE, mem_singleton_iff] at hd
          subst x d
          exact ⟨fun _ _ _ => trivial, fun _ => hlink⟩
        connected := fun _ _ => by
          let K := K₃.deleteEdges (ηe '' E(G))
          have himg : ηe '' E(G) = {s((0 : Fin 3), 2)} := by simp [hE, ηe]
          have h01 : K.Adj 0 1 := by
            refine ⟨s(0, 1), ?_⟩
            rw [Graph.deleteEdges_isLink, himg]
            exact ⟨⟨by decide, rfl⟩, by decide⟩
          have h12 : K.Adj 1 2 := by
            refine ⟨s(1, 2), ?_⟩
            rw [Graph.deleteEdges_isLink, himg]
            exact ⟨⟨by decide, rfl⟩, by decide⟩
          have h0 : ∀ z : Fin 3, Relation.ReflTransGen K.Adj 0 z := by
            intro z
            fin_cases z
            · exact .refl
            · exact .single h01
            · exact Relation.ReflTransGen.tail (.single h01) h12
          have : Std.Symm K.Adj := ⟨fun _ _ h => h.symm⟩
          refine ⟨K, le_rfl, by simp [K, K₃, GM16.completeGraph, ηv],
            ⟨⟨0, by simp [K, K₃, GM16.completeGraph]⟩, ?_⟩⟩
          intro a _ b _
          exact (Relation.ReflTransGen.stdSymm.symm _ _ (h0 a)).trans (h0 b) }
  exact isPlanar_of_isIsoMinor (isPlanar_completeGraph_of_le_four (by decide)) hm

/-- Any graph on two distinct vertices `u ≠ v` with exactly three parallel edges between `u` and
`v` is planar, as a minor of `K₄`. -/
theorem isPlanar_of_three_parallel {α : Type u} {β : Type v} {G : Graph α β}
    {u v : α} (huv : u ≠ v) {e₁ e₂ e₃ : β}
    (he₁₂ : e₁ ≠ e₂) (he₁₃ : e₁ ≠ e₃) (he₂₃ : e₂ ≠ e₃)
    (hV : V(G) = {u, v}) (hE : E(G) = {e₁, e₂, e₃})
    (h1 : G.IsLink e₁ u v) (h2 : G.IsLink e₂ u v) (h3 : G.IsLink e₃ u v) : IsPlanar G := by
  classical
  let K₄ := GM16.completeGraph 4
  let ηv : α → Set (Fin 4) := fun x => if x = u then {0} else {1, 2, 3}
  let ηe : β → Sym2 (Fin 4) := fun d =>
    if d = e₁ then s(0, 1) else if d = e₂ then s(0, 2) else s(0, 3)
  have hVG : V(G).Finite := hV ▸ ((finite_singleton v).insert u)
  have hEG : E(G).Finite := hE ▸ (((finite_singleton e₃).insert e₂).insert e₁)
  have hV_cases : ∀ {x : α}, x ∈ V(G) → x = u ∨ x = v := fun hx => by
    simpa [hV] using hx
  have hE_cases : ∀ {d : β}, d ∈ E(G) → d = e₁ ∨ d = e₂ ∨ d = e₃ := fun hd => by
    simpa [hE] using hd
  have h_noloop : ∀ x ∈ V(G), ∀ d ∈ E(G), ¬ G.IsLoopAt d x := by
    intro x _ d hd hloop
    change G.IsLink d x x at hloop
    have hlink : G.IsLink d u v := by
      rcases hE_cases hd with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
    rcases G.eq_or_eq_of_isLink_of_isLink hloop hlink with hx | hx <;> subst x
    · exact huv (hloop.right_unique hlink)
    · exact huv (hlink.left_unique hloop)
  have hηe_link : ∀ d ∈ E(G), ∃ k : Fin 4, k ∈ ({1, 2, 3} : Set (Fin 4)) ∧ ηe d = s(0, k) := by
    intro d hd
    rcases hE_cases hd with hd | hd | hd <;> subst d
    · exact ⟨1, by simp, by simp [ηe]⟩
    · exact ⟨2, by simp, by simp [ηe, he₁₂.symm]⟩
    · exact ⟨3, by simp, by simp [ηe, he₁₃.symm, he₂₃.symm]⟩
  have hm : IsIsoMinor G K₄ := by
    refine isIsoMinor_of_isMinorModel G K₄ hVG hEG finite_univ (Set.toFinite _) ηv ηe ?_
    refine
      { vertex_nonempty := fun x _ => by
          by_cases hxu : x = u <;> simp [ηv, hxu]
        vertex_subset := fun _ _ _ _ => trivial
        edge_mem := fun d hd => by
          obtain ⟨k, hk, hdk⟩ := hηe_link d hd
          rw [hdk]
          have hk0 : (0 : Fin 4) ≠ k := by
            rcases hk with rfl | rfl | rfl <;> decide
          exact ⟨0, k, hk0, rfl⟩
        vertex_disjoint := fun x hx y hy hxy => by
          have hx' := hV_cases hx
          have hy' := hV_cases hy
          rcases hx' with hx' | hx' <;> subst x <;> rcases hy' with hy' | hy' <;> subst y
          · exact (hxy rfl).elim
          · rw [Set.disjoint_left]
            intro z hz1 hz2
            simp [ηv, huv.symm] at hz1 hz2
            rcases hz2 with rfl | rfl | rfl <;> exact absurd hz1 (by decide)
          · rw [Set.disjoint_left]
            intro z hz1 hz2
            simp [ηv, huv.symm] at hz1 hz2
            subst z
            rcases hz1 with h | h | h <;> exact absurd h (by decide)
          · exact (hxy rfl).elim
        edge_injOn := fun a ha b hb hab => by
          have ha' := hE_cases ha
          have hb' := hE_cases hb
          rcases ha' with ha' | ha' | ha' <;> subst a <;>
            rcases hb' with hb' | hb' | hb' <;> subst b
          · rfl
          · simp [ηe, he₁₂.symm] at hab
          · simp [ηe, he₁₃.symm, he₂₃.symm] at hab
          · simp [ηe, he₁₂.symm] at hab
          · rfl
          · simp [ηe, he₁₂.symm, he₁₃.symm, he₂₃.symm] at hab
          · simp [ηe, he₁₃.symm, he₂₃.symm] at hab
          · simp [ηe, he₁₂.symm, he₁₃.symm, he₂₃.symm] at hab
          · rfl
        inc_iff := fun x hx d hd => by
          have hd_link : G.IsLink d u v := by
            rcases hE_cases hd with hd' | hd' | hd' <;> subst d
            · exact h1
            · exact h2
            · exact h3
          obtain ⟨k, hk, hdk⟩ := hηe_link d hd
          have hk0 : (0 : Fin 4) ≠ k := by rcases hk with rfl | rfl | rfl <;> decide
          rcases hV_cases hx with hx' | hx' <;> subst x
          · exact ⟨fun _ => ⟨0, by simp [ηv], k, hk0, hdk⟩, fun _ => hd_link.inc_left⟩
          · exact ⟨fun _ => ⟨k, by simp [ηv, huv.symm, hk], 0, hk0.symm, hdk.trans Sym2.eq_swap⟩,
              fun _ => hd_link.inc_right⟩
        isLoopAt_iff := fun x hx d hd => by
          refine ⟨fun hl => (h_noloop x hx d hd hl).elim, fun hall => ?_⟩
          obtain ⟨k, hk, hdk⟩ := hηe_link d hd
          have hk0 : (0 : Fin 4) ≠ k := by rcases hk with rfl | rfl | rfl <;> decide
          have h0_mem : (0 : Fin 4) ∈ ηv x := hall 0 ⟨k, hk0, hdk⟩
          have hk_mem : k ∈ ηv x := hall k ⟨0, hk0.symm, hdk.trans Sym2.eq_swap⟩
          by_cases hxu : x = u
          · simp [ηv, hxu] at hk_mem
            exact (hk0 hk_mem.symm).elim
          · simp [ηv, hxu] at h0_mem
        connected := fun x hx => by
          let D := K₄.deleteEdges (ηe '' E(G))
          have himg_sub : ηe '' E(G) ⊆ {s((0 : Fin 4), 1), s(0, 2), s(0, 3)} := by
            rintro _ ⟨d, hd, rfl⟩
            rcases hE_cases hd with hd' | hd' | hd' <;> subst d
            · simp [ηe]
            · simp [ηe, he₁₂.symm]
            · simp [ηe, he₁₃.symm, he₂₃.symm]
          rcases hV_cases hx with hx' | hx' <;> subst x
          · refine ⟨D.induce {0}, ⟨by simp [D, K₄, GM16.completeGraph], fun _ _ _ h => h.1⟩,
              by simp [ηv], ⟨⟨0, rfl⟩, fun a ha b hb => ?_⟩⟩
            rw [Graph.vertexSet_induce, mem_singleton_iff] at ha hb
            subst a b; exact .refl
          · let Kv := D.induce ({1, 2, 3} : Set (Fin 4))
            have h12 : Kv.Adj 1 2 := by
              refine ⟨s(1, 2), ?_⟩
              rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
              refine ⟨⟨⟨by decide, rfl⟩, fun hm => ?_⟩, by simp, by simp⟩
              have hm' := himg_sub hm
              simp at hm'
            have h13 : Kv.Adj 1 3 := by
              refine ⟨s(1, 3), ?_⟩
              rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
              refine ⟨⟨⟨by decide, rfl⟩, fun hm => ?_⟩, by simp, by simp⟩
              have hm' := himg_sub hm
              simp at hm'
            have h1_to : ∀ z ∈ ({1, 2, 3} : Set (Fin 4)), Relation.ReflTransGen Kv.Adj 1 z := by
              rintro z (rfl | rfl | rfl)
              · exact .refl
              · exact .single h12
              · exact .single h13
            have : Std.Symm Kv.Adj := ⟨fun _ _ h => h.symm⟩
            refine ⟨Kv, ⟨by simp [K₄, GM16.completeGraph], fun _ _ _ h => h.1⟩,
              by simp [Kv, ηv, huv.symm], ⟨⟨1, by simp [Kv]⟩, fun a ha b hb => ?_⟩⟩
            exact (Relation.ReflTransGen.stdSymm.symm _ _ (h1_to a ha)).trans
              (h1_to b hb) }
  exact isPlanar_of_isIsoMinor (isPlanar_completeGraph_of_le_four (by decide)) hm

end GraphMinor.Wagner
