module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.Section2Net
import GraphMinor.GM07.Section2
import GraphMinor.GM07.Section2Disc
import GraphMinor.GM07.NetExistsLines
import GraphMinor.GM07.NetExists
import GraphMinor.GM07.Section11a
import GraphMinor.GM07.Section9MoveOff
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM19.Section6a
import GraphMinor.GM11.ArcDrawings
import GraphMinor.GM11.PerimeterExists
import GraphMinor.GM08.Section15Defs
import GraphMinor.Surface.DiscMerge
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.AddCrosscap
import GraphMinor.Surface.SphereDisc
import GraphMinor.Surface.SurfacePull
import GraphMinor.Surface.PushOff
import GraphMinor.GM11.Section4c

/-!
# Graph Minors VII, (2.1): the converse

Graph Minors VII, (2.1) (pages 215–216): "For the converse, suppose $J$ satisfies (i)-(iv). Let
$\Delta$ be the surface obtained from $\Sigma$ by cutting along $U(J - bd(\Sigma))$. Then by (iii),
$\Delta - bd(\Delta)$ is connected, and by (iv) every $O$-arc included in $\Delta - bd(\Delta)$ is
null-homotopic. Since $\Delta$ is a surface, it follows that $\Delta$ is a closed disc, as
required."

We follow these steps, for a graph `J` with `U(J)` connected (`isSeamGraph_of_conditions`).

1. Cut `Σ` along the edges of `J - bd(Σ)` (`exists_edges_cut_sum`). The cut map `ψ : Δ → Σ` maps
   `bd(Δ)` onto `U(J)`, by (i) and (ii), and it is one to one off `bd(Δ)`. So `Δ - bd(Δ)` maps
   one to one onto the region of `J`.
2. By (iii), `Δ - bd(Δ)` is connected, so `Δ` is connected.
3. Let `F` be an `O`-arc in `Δ - bd(Δ)`. By (iv) its image is null-homotopic in `Σ`, so it bounds
   a closed disc `D` of `Σ`. The paper concludes that `F` is null-homotopic in `Δ`. This needs that
   `D` misses `U(J)`, and here the connectedness of `U(J)` is used: `U(J)` lies either inside `D`
   or outside it. If it lies inside, then `bd(Σ) = ∅`; if `Σ` is a sphere we take the other disc
   bounded by the image of `F`, and otherwise some `O`-arc of `Σ` that is not null-homotopic can be
   moved off `D`, into the region, against (iv) (`exists_disc_off`). Without the connectedness of
   `U(J)` this step fails, and so does (2.1): see the correction to (2.1) in `corrections/GM07.md`.
4. So `Δ` is a closed disc (`isClosedDisc_univ_of_bounds`), and the cut gives a net whose seam graph
   is `J` (`exists_net_of_netCut`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

/-- A compact set mapped one to one onto a closed disc is a closed disc. -/
theorem isClosedDisc_of_image {A T : Type*} [TopologicalSpace A] [TopologicalSpace T] [T2Space T]
    {Δ : Set A} (hc : IsCompact Δ) {f : A → T} (hf : Continuous f) (hi : InjOn f Δ)
    (hD : IsClosedDisc (f '' Δ)) : IsClosedDisc Δ := by
  obtain ⟨φ⟩ := hD
  have : CompactSpace Δ := isCompact_iff_compactSpace.mp hc
  let h : Δ → f '' Δ := fun x => ⟨f x, x, x.2, rfl⟩
  have hcont : Continuous h := (hf.comp continuous_subtype_val).subtype_mk _
  have hb : Function.Bijective h := by
    refine ⟨fun x y hxy => Subtype.ext (hi x.2 y.2 (congrArg Subtype.val hxy)), ?_⟩
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨φ.trans (hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective h hb)).symm⟩

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- **Step 3 of the converse of (2.1).** Let `X` be a closed connected set of a connected surface
`Σ` that includes `bd(Σ)`, such that every `O`-arc off `X` is null-homotopic. Then an `O`-arc `G`
off `X` that bounds a closed disc of `Σ` bounds a closed disc that misses `X`. -/
theorem exists_disc_off (hS : IsSurface S) [ConnectedSpace S] {X : Set S} (hXc : IsPreconnected X)
    (hbX : bd S ⊆ X) (hnull : ∀ F : Set S, F ⊆ Xᶜ → IsOArc F → IsNullHomotopicOArc F)
    {G D : Set S} (hG : IsOArc G) (hGX : G ⊆ Xᶜ) (hD : IsClosedDisc D) (hDG : discBd D = G) :
    ∃ D' : Set S, IsClosedDisc D' ∧ discBd D' = G ∧ Disjoint D' X := by
  have : T2Space S := hS.2.1
  have hman := hS.2.2
  -- `X` lies inside `D` or outside it
  have hcov : X ⊆ discInt D ∪ Dᶜ := fun x hx => by
    by_cases hxD : x ∈ D
    · exact .inl ⟨hxD, fun hb => hGX (hDG ▸ hb) hx⟩
    · exact .inr hxD
  have hdis : Disjoint (discInt D) Dᶜ := disjoint_left.mpr fun x hx h => h hx.1
  rcases hXc.subset_or_subset (hD.isOpen_discInt hman) hD.isClosed.isOpen_compl hdis hcov with
    hin | hout
  swap
  · exact ⟨D, hD, hDG, disjoint_left.mpr fun x hx h => hout h hx⟩
  -- `X` lies inside `D`, so `Σ` has no boundary
  have hbd : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx =>
    hx (isInteriorPoint_of_mem_discInt hman hD (hin (hbX hx)))
  have hDb : D ∩ bd S = ∅ := by rw [hbd, inter_empty]
  by_cases hsph : IsSphere S
  · obtain ⟨Δ₁, Δ₂, hne, hΔ₁, hΔ₂, hb₁, hb₂, -, hcap, -, huniq⟩ := sphere_disc S hsph G hG
    -- the other disc bounded by `G`
    have hother : ∃ D', IsClosedDisc D' ∧ discBd D' = G ∧ D ∩ D' = G := by
      rcases huniq D hD hDG with rfl | rfl
      · exact ⟨Δ₂, hΔ₂, hb₂, hcap⟩
      · exact ⟨Δ₁, hΔ₁, hb₁, by rw [inter_comm, hcap]⟩
    obtain ⟨D', hD', hD'G, hDD'⟩ := hother
    refine ⟨D', hD', hD'G, disjoint_left.mpr fun x hx hxX => ?_⟩
    have h1 := hin hxX
    have h2 : x ∈ G := hDD' ▸ ⟨h1.1, hx⟩
    exact hGX h2 hxX
  · -- otherwise an `O`-arc that is not null-homotopic is moved off `D`
    exfalso
    obtain ⟨F, hF, hFn⟩ := GM19.exists_not_nullHomotopic hS hbd hsph
    obtain ⟨a, ha⟩ : F.Nonempty := by
      obtain ⟨φ⟩ := hF
      exact ⟨(φ 1).1, (φ 1).2⟩
    obtain ⟨H, hHU, -⟩ := GM11.exists_loop_drawing hF ha
    obtain ⟨β, -, hβ⟩ := exists_move_drawing_off_disc hS H hD hDb
    rw [hHU] at hβ
    have hβF : IsOArc (β '' F) := isOArc_image β.isEmbedding hF
    have hβX : β '' F ⊆ Xᶜ := fun y hy hyX => disjoint_left.mp hβ hy (hin hyX).1
    exact hFn ((GM08.isNullHomotopicOArc_image_homeomorph β).mp (hnull _ hβX hβF))

/-- A drawing in a surface includes no non-empty open set. We cap the cuffs and use the same fact
for surfaces without boundary (`GM11.exists_notMem_U`). -/
theorem exists_notMem_U_of_isSurface (hS : IsSurface S) (Γ : Drawing S) {O : Set S}
    (hO : IsOpen O) (hne : O.Nonempty) : ∃ y ∈ O, y ∉ Γ.U := by
  have : T2Space S := hS.2.1
  obtain ⟨x, hx⟩ := hne
  have hx' : x ∈ closure (bd S)ᶜ := mem_closure_compl_bd (hS.2.2 x)
  obtain ⟨x', hx'O, hx'b⟩ := mem_closure_iff.mp hx' O hO hx
  set O' := O ∩ (bd S)ᶜ with hO'
  have hO'o : IsOpen O' := hO.inter (isClosed_bd S).isOpen_compl
  obtain ⟨T, tT, j, K, hT, hj, hK, hu, hi, -⟩ := exists_capAll S hS
  have : T2Space T := hT.2.1
  obtain ⟨V, hV, hVj⟩ := hj.isInducing.isOpen_iff.mp hO'o
  have hW : j '' O' = V ∩ Kᶜ := by
    ext t
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(hVj ▸ hz : z ∈ j ⁻¹' V), fun hzK => hz.2 ?_⟩
      obtain ⟨z', hz', he⟩ := (hi ▸ (⟨⟨z, rfl⟩, hzK⟩ : j z ∈ range j ∩ K) : j z ∈ j '' bd S)
      exact hj.injective he ▸ hz'
    · rintro ⟨htV, htK⟩
      rcases eq_univ_iff_forall.mp hu t with ⟨z, rfl⟩ | h
      · exact ⟨z, hVj ▸ htV, rfl⟩
      · exact absurd h htK
  have hWo : IsOpen (j '' O') := hW ▸ hV.inter hK.isOpen_compl
  have hWne : (j '' O').Nonempty := ⟨j x', x', ⟨hx'O, hx'b⟩, rfl⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hzU⟩ := GM11.exists_notMem_U (Γ := embedDrawing hj Γ) hT hWo hWne
  exact ⟨z, hz.1, fun h => hzU ⟨z, h, rfl⟩⟩

/-- **The converse of Graph Minors VII, (2.1)**, for a graph `J` with `U(J)` connected, in a
connected surface: if `J` satisfies (i)–(iv), then `J` is a seam graph for some net. -/
theorem isSeamGraph_of_conditions_of_connected (hS : IsSurface S) [ConnectedSpace S] (J : Drawing S)
    (hJc : IsConnected J.U)
    (h1 : bd S ⊆ J.U ∧ ∀ e ∈ J.E, e ⊆ bd S ∨ e ∩ bd S = ∅)
    (h2 : HasNoIsolatedVertices (deleteBd J))
    (h3 : J.R.ncard = 1)
    (h4 : ∀ r ∈ J.R, ∀ F : Set S, F ⊆ r → IsOArc F → IsNullHomotopicOArc F) :
    IsSeamGraph J := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  -- the edges of `J - bd(Σ)` and their parameters
  set E := {e : Set S // e ∈ J.E ∧ e ∩ bd S = ∅} with hEdef
  have : Finite E := (J.finite_edges.subset fun e (he : e ∈ J.E ∧ _) => he.1).to_subtype
  obtain ⟨e₀, he₀, he₀b⟩ := exists_edge_disjoint_bd_of_nonempty h2 hJc.nonempty
  have hp := fun e : E => GM06.exists_edge_param_isLink J e.2.1
  choose γ hγc hγ0 hγ1 hγi hγe hγcl _ using hp
  set c : E → ℝ → S := fun e => extI (γ e) with hc'
  have hIoo : ∀ {u : ℝ}, u ∈ Ioo (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 := fun hu => ⟨hu.1.le, hu.2.le⟩
  have hval : ∀ e, ∀ u (hu : u ∈ Icc (0 : ℝ) 1), c e u = γ e ⟨u, hu⟩ := fun e u hu =>
    extI_of_mem _ hu
  have hI : ∀ {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1),
      (⟨u, hIoo hu⟩ : unitInterval) ∈ Ioo (0 : unitInterval) 1 := fun hu => ⟨hu.1, hu.2⟩
  have hmem : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∈ e.1 := fun e u hu => by
    rw [hval e u (hIoo hu), ← hγe e]
    exact mem_image_of_mem _ (hI hu)
  have hsub : ∀ e : E, e.1 ⊆ J.U \ J.V := fun e => e.2.1.2.1
  have hoff : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∉ J.V := fun e u hu => (hsub e (hmem e u hu)).2
  have h0 : ∀ e, c e 0 ∈ J.V := fun e => by
    rw [hval e 0 (by simp)]
    exact hγ0 e
  have h1' : ∀ e, c e 1 ∈ J.V := fun e => by
    rw [hval e 1 (by simp)]
    exact hγ1 e
  have hinj : ∀ e, InjOn (c e) (Ioo 0 1) := fun e u hu v hv he => by
    rw [hval e u (hIoo hu), hval e v (hIoo hv)] at he
    exact congrArg Subtype.val (hγi e (hI hu) (hI hv) he)
  have hdis : ∀ e e', e ≠ e' → ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, c e u ≠ c e' v :=
    fun e e' hne u hu v hv he => hne (Subtype.ext (arcComponentsIn_eq_of_mem e.2.1 e'.2.1
      (hmem e u hu) (he ▸ hmem e' v hv)))
  have hbd : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∉ bd S := fun e u hu hb =>
    (eq_empty_iff_forall_notMem.mp e.2.2) _ ⟨hmem e u hu, hb⟩
  have hcl : ∀ e : E, c e '' Icc 0 1 = closure e.1 := fun e => by
    rw [hγcl e]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, (hval e u hu).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, hval e t t.2⟩
  -- Step 1: the cut
  obtain ⟨Y, tY, t2Y, R, _, b, ψ, ξ, η, hY, hcut, hbR, hcovS⟩ :=
    exists_edges_cut_sum (P := J.V) hS (fun e => continuous_extI (hγc e)) hinj h0 h1' hoff hdis hbd
  set a : E ⊕ R → ℝ → S := Sum.elim c b with ha
  have : CompactSpace Y := hY.1
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  -- the paths lie in `U(J)`, and they cover it
  have haU : ∀ k, ∀ u ∈ Icc (0 : ℝ) 1, a k u ∈ J.U := by
    rintro (e | r) u hu
    · have : c e u ∈ closure e.1 := hcl e ▸ mem_image_of_mem _ hu
      exact closure_minimal (fun x hx => (hsub e hx).1) J.isClosed_U this
    · exact h1.1 (hbR r u hu)
  have hUa : ∀ x ∈ J.U, ∃ k, ∃ u ∈ Icc (0 : ℝ) 1, a k u = x := by
    intro x hx
    by_cases hxV : x ∈ J.V
    · obtain ⟨e', he', hinc⟩ := h2 x (Or.inl ⟨hxV, hxV⟩)
      rw [deleteBd, Drawing.span_E] at he'
      have hcl' : x ∈ closure e' := hinc.2.2
      rw [← hcl ⟨e', he'.1.1, he'.1.2⟩] at hcl'
      obtain ⟨u, hu, hxu⟩ := hcl'
      exact ⟨.inl ⟨e', he'.1.1, he'.1.2⟩, u, hu, hxu⟩
    · have hxe : x ∈ J.U \ J.V := ⟨hx, hxV⟩
      have he : pathComponentIn (J.U \ J.V) x ∈ J.E := pathComponentIn_mem_arcComponentsIn hxe
      have hxe' : x ∈ pathComponentIn (J.U \ J.V) x := mem_pathComponentIn_self hxe
      rcases h1.2 _ he with hb | hb
      · exact hcovS x (hb hxe')
      · have hx' : x ∈ γ ⟨_, he, hb⟩ '' Ioo 0 1 := by
          rw [hγe ⟨_, he, hb⟩]
          exact hxe'
        obtain ⟨t, ht, hxt⟩ := hx'
        exact ⟨.inl ⟨_, he, hb⟩, t, t.2, (hval _ t t.2).trans hxt⟩
  have hseamU : ψ '' bd Y = J.U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨k, u, hu, rfl | rfl⟩ := hcut.cover y hy
      · exact hcut.hξ k u hu ▸ haU k u hu
      · exact hcut.hη k u hu ▸ haU k u hu
    · intro hx
      obtain ⟨k, u, hu, rfl⟩ := hUa x hx
      exact ⟨ξ k u, hcut.bdξ k u hu, hcut.hξ k u hu⟩
  -- off `bd(Δ)` the cut map is one to one, and it misses `U(J)`
  have hiso : ∀ y : Y, y ∉ bd Y → ∀ y' : Y, ψ y = ψ y' → y = y' := by
    intro y hy y' hyy'
    refine eqvGen_eq_of_isolated (r := fun p q : Y =>
      ∃ k, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ k u ∧ q = η k u) ?_ (hcut.fib y y' hyy')
    rintro p q ⟨k, u, hu, rfl, rfl⟩
    exact ⟨fun he => hy (he ▸ hcut.bdξ k u hu), fun he => hy (he ▸ hcut.bdη k u hu)⟩
  have hpre : ∀ y : Y, ψ y ∈ J.U → y ∈ bd Y := by
    intro y hy
    by_contra hyb
    rw [← hseamU] at hy
    obtain ⟨y', hy', he⟩ := hy
    exact hyb (hiso y hyb y' he.symm ▸ hy')
  have hinjY : InjOn ψ (bd Y)ᶜ := fun x hx y _ hxy => hiso x hx y hxy
  -- the region of `J` is the complement of `U(J)`
  obtain ⟨r, hr⟩ := ncard_eq_one.mp h3
  have hrU : (J.U)ᶜ ⊆ r := fun x hx => by
    have hm : connectedComponentIn (univ \ J.U) x ∈ J.R := ⟨x, ⟨mem_univ x, hx⟩, rfl⟩
    rw [hr, mem_singleton_iff] at hm
    exact hm ▸ mem_connectedComponentIn ⟨mem_univ x, hx⟩
  have hrr : r ∈ J.R := hr ▸ mem_singleton r
  have hr' : r = (J.U)ᶜ := by
    refine Subset.antisymm ?_ hrU
    obtain ⟨x, -, hx⟩ := hrr
    rw [← hx]
    exact fun y hy => (connectedComponentIn_subset _ _ hy).2
  have h4' : ∀ F : Set S, F ⊆ (J.U)ᶜ → IsOArc F → IsNullHomotopicOArc F := fun F hF hO =>
    h4 r hrr F (hr' ▸ hF) hO
  -- Step 2: `Δ` is connected
  have hψc : Continuous ψ := hcut.cont
  have hrc : IsPreconnected (J.U)ᶜ := by
    obtain ⟨x, -, hx⟩ := hrr
    rw [← hr', ← hx]
    exact isPreconnected_connectedComponentIn
  have hbdne : (bd Y).Nonempty :=
    ⟨ξ (.inl ⟨e₀, he₀, he₀b⟩) 0, hcut.bdξ _ 0 h0I⟩
  have : Nonempty Y := ⟨hbdne.some⟩
  set g := Function.invFunOn ψ (bd Y)ᶜ with hg
  have himgY : ψ '' (bd Y)ᶜ = (J.U)ᶜ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ hx
      exact hy (hpre y hx)
    · intro hx
      obtain ⟨y, rfl⟩ := hcut.surj x
      exact ⟨y, fun hy => hx (hseamU ▸ mem_image_of_mem ψ hy), rfl⟩
  have hgψ : ∀ y ∈ (bd Y)ᶜ, g (ψ y) = y := fun y hy => hinjY.leftInvOn_invFunOn hy
  have hψg : ∀ x ∈ (J.U)ᶜ, ψ (g x) = x := fun x hx =>
    Function.invFunOn_eq (himgY ▸ hx : x ∈ ψ '' (bd Y)ᶜ)
  have hgmem : ∀ x ∈ (J.U)ᶜ, g x ∈ (bd Y)ᶜ := fun x hx =>
    Function.invFunOn_mem (himgY ▸ hx : x ∈ ψ '' (bd Y)ᶜ)
  have hgc : ContinuousOn g (J.U)ᶜ := by
    rw [continuousOn_iff_isClosed]
    intro C hC
    refine ⟨ψ '' C, (hC.isCompact.image hψc).isClosed, ?_⟩
    ext x
    constructor
    · rintro ⟨hxC, hx⟩
      exact ⟨⟨g x, hxC, hψg x hx⟩, hx⟩
    · rintro ⟨⟨y, hyC, rfl⟩, hx⟩
      have hy : y ∈ (bd Y)ᶜ := fun hy => hx (hseamU ▸ mem_image_of_mem ψ hy)
      exact ⟨show g (ψ y) ∈ C from (hgψ y hy).symm ▸ hyC, hx⟩
  have hgimg : g '' (J.U)ᶜ = (bd Y)ᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hgmem x hx
    · intro hy
      exact ⟨ψ y, fun h => hy (hpre y h), hgψ y hy⟩
  have hYc : IsPreconnected (bd Y)ᶜ := hgimg ▸ hrc.image g hgc
  have hcl' : closure (bd Y)ᶜ = univ :=
    eq_univ_iff_forall.mpr fun y => mem_closure_compl_bd (hY.2.2 y)
  have : ConnectedSpace Y :=
    { isPreconnected_univ := hcl' ▸ hYc.closure
      toNonempty := ⟨hbdne.some⟩ }
  -- Step 3: every `O`-arc off `bd(Δ)` bounds a disc off `bd(Δ)`
  have hP : ∀ F : Set Y, F ⊆ (bd Y)ᶜ → IsOArc F →
      ∃ Δ : Set Y, Δ ⊆ (bd Y)ᶜ ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
    intro F hFb hF
    have hG : IsOArc (ψ '' F) := GM11.isOArc_image hF hψc.continuousOn (hinjY.mono hFb)
    have hGJ : ψ '' F ⊆ (J.U)ᶜ := by
      rintro _ ⟨y, hy, rfl⟩ h
      exact hFb hy (hpre y h)
    obtain ⟨D, hD, hDG⟩ := nullHomotopicOArc_bounds_disc hS hG (h4' _ hGJ hG)
    obtain ⟨D', hD', hD'G, hD'J⟩ := exists_disc_off hS hJc.isPreconnected h1.1 h4' hG hGJ hD hDG
    have hΔb : ψ ⁻¹' D' ⊆ (bd Y)ᶜ := fun y hy hyb =>
      disjoint_left.mp hD'J hy (hseamU ▸ mem_image_of_mem ψ hyb)
    have hΔc : IsCompact (ψ ⁻¹' D') := (hD'.isClosed.preimage hψc).isCompact
    have himg : ψ '' (ψ ⁻¹' D') = D' := image_preimage_eq_of_subset fun x _ => hcut.surj x
    have hΔ : IsClosedDisc (ψ ⁻¹' D') :=
      isClosedDisc_of_image hΔc hψc (hinjY.mono hΔb) (himg.symm ▸ hD')
    refine ⟨_, hΔb, hΔ, ?_⟩
    have hbdΔ := (isClosedDisc_image_of_injOn hΔ hψc (hinjY.mono hΔb)).2
    rw [himg, hD'G] at hbdΔ
    exact ((hinjY.image_eq_image_iff ((discBd_subset _).trans hΔb) hFb).mp hbdΔ.symm)
  -- Step 4: `Δ` is a closed disc, and the cut is a net
  have hDisc := isClosedDisc_univ_of_bounds hY hbdne hP
  obtain ⟨N, hNr, hNU, hNV⟩ := exists_net_of_netCut hY hDisc hcut ⟨.inl ⟨e₀, he₀, he₀b⟩, trivial⟩
  refine ⟨N, hNr, hNU.trans hseamU |>.symm, ?_⟩
  rw [hNV]
  ext v
  constructor
  · intro hv
    obtain ⟨e', he', hinc⟩ := h2 v (Or.inl ⟨hv, hv⟩)
    rw [deleteBd, Drawing.span_E] at he'
    have hcl'' : v ∈ closure e' := hinc.2.2
    rw [← hcl ⟨e', he'.1.1, he'.1.2⟩] at hcl''
    obtain ⟨u, hu, hvu⟩ := hcl''
    refine ⟨.inl ⟨e', he'.1.1, he'.1.2⟩, trivial, ?_⟩
    rcases eq_or_lt_of_le hu.1 with rfl | hu0
    · exact .inl hvu
    rcases eq_or_lt_of_le hu.2 with rfl | hu1
    · exact .inr hvu
    exact absurd (hvu ▸ hv) (hoff _ u ⟨hu0, hu1⟩)
  · rintro ⟨k, hk, hv⟩
    rcases k with e | r'
    · rcases hv with rfl | rfl
      · exact h0 e
      · exact h1' e
    · exact hk.elim

/-- Under (iii), a graph `J` with `U(J)` connected lies in a connected surface: the closure of the
region meets `U(J)`, since otherwise `U(J)` would be open (`exists_notMem_U_of_isSurface`). -/
theorem connectedSpace_of_unique_region (hS : IsSurface S) {J : Drawing S} (hJc : IsConnected J.U)
    (h3 : J.R.ncard = 1) : ConnectedSpace S := by
  obtain ⟨r, hr⟩ := ncard_eq_one.mp h3
  have hrr : r ∈ J.R := hr ▸ mem_singleton r
  have hrU : (J.U)ᶜ ⊆ r := fun x hx => by
    have hm : connectedComponentIn (univ \ J.U) x ∈ J.R := ⟨x, ⟨mem_univ x, hx⟩, rfl⟩
    rw [hr, mem_singleton_iff] at hm
    exact hm ▸ mem_connectedComponentIn ⟨mem_univ x, hx⟩
  obtain ⟨x₀, -, hx₀⟩ := hrr
  have hrc : IsPreconnected r := hx₀ ▸ isPreconnected_connectedComponentIn
  have hrsub : r ⊆ (J.U)ᶜ := hx₀ ▸ fun y hy => (connectedComponentIn_subset _ _ hy).2
  have hmeet : (J.U ∩ closure r).Nonempty := by
    by_contra hno
    rw [not_nonempty_iff_eq_empty] at hno
    have hcl : closure r ⊆ (J.U)ᶜ := fun y hy hyU => (eq_empty_iff_forall_notMem.mp hno) y ⟨hyU, hy⟩
    have hJo : IsOpen J.U := by
      have : (J.U)ᶜ = closure r := Subset.antisymm (hrU.trans subset_closure) hcl
      rw [← compl_compl J.U, this]
      exact isClosed_closure.isOpen_compl
    obtain ⟨y, hy, hyU⟩ := exists_notMem_U_of_isSurface hS J hJo hJc.nonempty
    exact hyU hy
  have huniv : J.U ∪ closure r = univ := eq_univ_iff_forall.mpr fun x => by
    by_cases hx : x ∈ J.U
    · exact .inl hx
    · exact .inr (subset_closure (hrU hx))
  have hpre := hJc.isPreconnected.union' hmeet hrc.closure
  rw [huniv] at hpre
  exact { isPreconnected_univ := hpre
          toNonempty := ⟨hJc.nonempty.some⟩ }

/-- **The converse of Graph Minors VII, (2.1)**, for a graph `J` with `U(J)` connected: if `J`
satisfies (i)–(iv), then `J` is a seam graph for some net. The surface is connected by
`connectedSpace_of_unique_region`. -/
theorem isSeamGraph_of_conditions (hS : IsSurface S) (J : Drawing S) (hJc : IsConnected J.U)
    (h1 : bd S ⊆ J.U ∧ ∀ e ∈ J.E, e ⊆ bd S ∨ e ∩ bd S = ∅)
    (h2 : HasNoIsolatedVertices (deleteBd J))
    (h3 : J.R.ncard = 1)
    (h4 : ∀ r ∈ J.R, ∀ F : Set S, F ⊆ r → IsOArc F → IsNullHomotopicOArc F) :
    IsSeamGraph J := by
  have : ConnectedSpace S := connectedSpace_of_unique_region hS hJc h3
  exact isSeamGraph_of_conditions_of_connected hS J hJc h1 h2 h3 h4

/-- Graph Minors VII, (2.1) (pages 215–216), for a graph `J` with `U(J)` connected:
"Let $J$ be a graph in $\Sigma$. Then $J$ is a seam graph for some net if and only if
(i) $bd(\Sigma) \subseteq U(J)$, and for every edge $e$ of $J$, either $e \subseteq bd(\Sigma)$ or
$e \cap bd(\Sigma) = \emptyset$, (ii) $J - bd(\Sigma)$ has no isolated vertices, (iii) $J$ has a
unique region, and (iv) every $O$-arc included in that region is null-homotopic."
The hypothesis that `U(J)` is connected (and so non-empty) is added (see the correction to (2.1) in
`corrections/GM07.md`).
The forward direction is `theorem_2_1_forward`, which does not need it; the converse is
`isSeamGraph_of_conditions` (`GraphMinor/GM07/Section2Converse.lean`), by the paper's cut. -/
theorem theorem_2_1_proof (hS : IsSurface S) (J : Drawing S) (hJc : IsConnected J.U) :
    IsSeamGraph J ↔
      (bd S ⊆ J.U ∧ ∀ e ∈ J.E, e ⊆ bd S ∨ e ∩ bd S = ∅) ∧
      HasNoIsolatedVertices (deleteBd J) ∧
      J.R.ncard = 1 ∧
      (∀ r ∈ J.R, ∀ F : Set S, F ⊆ r → IsOArc F → IsNullHomotopicOArc F) :=
  ⟨theorem_2_1_forward hS J, fun ⟨h1, h2, h3, h4⟩ => isSeamGraph_of_conditions hS J hJc h1 h2 h3 h4⟩

end GraphMinor.GM07
