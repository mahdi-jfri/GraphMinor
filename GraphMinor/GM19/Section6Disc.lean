module

public import GraphMinor.GM19.Section6Region

/-!
# A path along a region inside a disc

This file proves the step in claim (1) of the proof of (6.6) of Graph Minors XIX (page 342). There, `F` is an O-arc made of a path of a drawing `G` and a line `L` through a region `r`, and `F` bounds a disc `Δ`. The paper says that `r ∩ F` is connected, and so there is a path of `G ∩ (r̄ ∩ Δ)` between the ends `a, b` of `L`.

We give the reason (`mem_of_closed_adj`). Suppose the part of `G` in `r̄ ∩ Δ` splits into two closed pieces, one with `a` and one with `b`. Cut `L` at a point `m`. Each piece with its half of `L` fails to separate the region side of `L` from the outside of `Δ`, since one can cross the other half of `L`. Two compact sets that meet in one point and do not separate two points do not separate them together, by Janiszewski's theorem. But together they contain the frontier of the part of `r` next to `L`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GM11 Metric

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- The edges in `A`, as a set of points with their ends. -/
def edgesIn (G : Drawing S) (A : Set S) (P : Set S → Prop) : Set S :=
  ⋃ e ∈ {e ∈ G.E | e ⊆ A ∧ P e}, closure e

theorem isClosed_edgesIn (G : Drawing S) (A : Set S) (P : Set S → Prop) : IsClosed (edgesIn G A P) :=
  (G.finite_edges.subset fun _ h => h.1).isClosed_biUnion fun _ _ => isClosed_closure

/-- A point of `U(G)` in `r̄ ∩ Δ` lies in a vertex or an edge of `G` in `r̄ ∩ Δ`. -/
theorem mem_edges_or_vertex (hT : IsClosedSurface S) (G : Drawing S) (hl : LoopFree G) {r Δ : Set S} (hr : r ∈ G.regions) (hΔ : IsClosedDisc Δ)
    (hedge : ∀ e ∈ G.E, (e ∩ discBd Δ).Nonempty → e ⊆ discBd Δ) {y : S} (hyU : y ∈ G.U) (hyr : y ∈ closure r) (hyΔ : y ∈ Δ) :
    y ∈ G.V ∨ ∃ e ∈ G.E, e ⊆ closure r ∩ Δ ∧ y ∈ e := by
  by_cases hyV : y ∈ G.V
  · exact .inl hyV
  right
  obtain ⟨e, he, hye⟩ := exists_edge_of_mem G hyU hyV
  refine ⟨e, he, subset_inter (edge_subset_closure hT G hl he hr ⟨y, hye, hyr⟩) ?_, hye⟩
  by_cases hb : (e ∩ discBd Δ).Nonempty
  · exact (hedge e he hb).trans (Surface.discBd_subset Δ)
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hc : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  have hO : IsOpen (discInt Δ) := hΔ.isOpen_discInt hman
  have hyI : y ∈ discInt Δ := ⟨hyΔ, fun h => hb ⟨y, hye, h⟩⟩
  have hC : IsOpen Δᶜ := hΔ.isClosed.isOpen_compl
  intro w hw
  by_contra hwΔ
  obtain ⟨z, -, hz1, hz2⟩ := hc _ _ hO hC (fun x hx => by
    by_cases h : x ∈ Δ
    · exact .inl ⟨h, fun h' => hb ⟨x, hx, h'⟩⟩
    · exact .inr h) ⟨y, hye, hyI⟩ ⟨w, hw, hwΔ⟩
  exact hz2 hz1.1

/-- The closure of a set inside the disc, seen through the chart. -/
theorem chart_mem_closure {Δ : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart Δ h g) {A : Set S} (hA : A ⊆ Δ) {y : S} (hy : y ∈ closure A) (hyΔ : y ∈ Δ) :
    h y ∈ closure (h '' A) :=
  ((c.hc y hyΔ).mono hA).mem_closure_image hy

/-- The side of the line and the outside of the disc join across a part of the line. -/
theorem isPreconnected_across {Δ : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart Δ h g) {A J : Set S} (hA : IsPreconnected A) (hAΔ : A ⊆ Δ) (hJ : J ⊆ closure A)
    (hJb : J ⊆ discBd Δ) (hne : J.Nonempty) : IsPreconnected (h '' A ∪ h '' J ∪ (closedBall (0 : ℂ) 1)ᶜ) := by
  have hbd : ∀ y ∈ J, h y ∈ sphere (0 : ℂ) 1 := fun y hy => c.bd ▸ mem_image_of_mem h (hJb hy)
  have hJΔ : J ⊆ Δ := hJb.trans (Surface.discBd_subset Δ)
  have h1 : IsPreconnected (h '' A ∪ h '' J) := (hA.image h (c.hc.mono hAΔ)).subset_closure subset_union_left
    (union_subset subset_closure (by
      rintro _ ⟨y, hy, rfl⟩
      exact chart_mem_closure c hAΔ (hJ hy) (hJΔ hy)))
  have hO : closure (closedBall (0 : ℂ) 1)ᶜ = (ball (0 : ℂ) 1)ᶜ := by
    rw [closure_compl, interior_closedBall _ one_ne_zero]
  have h2 : IsPreconnected ((closedBall (0 : ℂ) 1)ᶜ ∪ h '' J) := (isPreconnected_compl_closedBall 1 zero_le_one).subset_closure subset_union_left
    (union_subset subset_closure (by
      rintro _ ⟨y, hy, rfl⟩
      rw [hO]
      intro hb
      have := hbd y hy
      rw [mem_ball_zero_iff] at hb
      rw [mem_sphere_zero_iff_norm] at this
      linarith))
  obtain ⟨y, hy⟩ := hne
  have h3 := h1.union' (s := h '' A ∪ h '' J) (t := (closedBall (0 : ℂ) 1)ᶜ ∪ h '' J) ⟨h y, .inr ⟨y, hy, rfl⟩, .inr ⟨y, hy, rfl⟩⟩ h2
  have e : h '' A ∪ h '' J ∪ ((closedBall (0 : ℂ) 1)ᶜ ∪ h '' J) = h '' A ∪ h '' J ∪ (closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    simp only [mem_union]
    tauto
  rwa [e] at h3

/-- **Two vertices along a region are joined inside the disc.** See the module docstring. The set `Y` is closed under the edges of `G` in `r̄ ∩ Δ`. -/
theorem mem_of_closed_adj (hT : IsClosedSurface S) (G : Drawing S) (hl : LoopFree G) {r Δ L : Set S} (hr : r ∈ G.regions) (hΔ : IsClosedDisc Δ) {a b : S} (hab : a ≠ b)
    (hL : IsLineWithEnds L a b) (hLr : L \ {a, b} ⊆ r) (hLb : L ⊆ discBd Δ) (hbU : discBd Δ ⊆ G.U ∪ L) (hedge : ∀ e ∈ G.E, (e ∩ discBd Δ).Nonempty → e ⊆ discBd Δ)
    (haV : a ∈ G.V) (hbV : b ∈ G.V) {Y : Set S} (haY : a ∈ Y) (hstep : ∀ e ∈ G.E, e ⊆ closure r ∩ Δ → ∀ x ∈ tilde e, ∀ y ∈ tilde e, x ∈ Y → y ∈ Y) : b ∈ Y := by
  classical
  by_contra hbY
  have hcpt : CompactSpace S := hT.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hT
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  obtain ⟨hro, -, -, hrU, hrA, hrF⟩ := region_props G hr
  have hrU' : ∀ {y}, y ∈ r → y ∉ G.U := fun hy hyU => Set.disjoint_left.mp hrU hy hyU
  obtain ⟨c, hc, hcr, c0, c1⟩ := hL.exists_arc
  have ha : a ∈ L := hcr ▸ c0 ▸ mem_range_self _
  have hb : b ∈ L := hcr ▸ c1 ▸ mem_range_self _
  have hLU : L ∩ G.U ⊆ {a, b} := fun y hy => by
    by_contra hn
    exact hrU' (hLr ⟨hy.1, hn⟩) hy.2
  have hLc : L ⊆ closure r := by
    rw [← hcr]
    rintro _ ⟨t, rfl⟩
    have hopen : ∀ s : unitInterval, 0 < s → s < 1 → c s ∈ r := fun s h0 h1 => hLr ⟨hcr ▸ mem_range_self s, fun h => by
      rcases h with h | h
      · exact (ne_of_gt h0) (hc.2 (h.trans c0.symm))
      · exact (ne_of_lt h1) (hc.2 (h.trans c1.symm))⟩
    have hIoo : Ioo (0 : unitInterval) 1 ⊆ c ⁻¹' r := fun s hs => hopen s hs.1 hs.2
    have hcl : t ∈ closure (Ioo (0 : unitInterval) 1) := by
      rw [closure_Ioo (by simp)]
      exact ⟨unitInterval.nonneg', unitInterval.le_one'⟩
    exact closure_mono (image_subset_iff.mpr hIoo) (mem_closure_image hc.1.continuousAt hcl)
  let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have h0h : (0 : unitInterval) < half := by show (0 : ℝ) < 1 / 2; norm_num
  have hh1 : half < (1 : unitInterval) := by show (1 / 2 : ℝ) < 1; norm_num
  let m := c half
  have hmr : m ∈ r := hLr ⟨hcr ▸ mem_range_self half, fun h => by
    rcases h with h | h
    · exact (ne_of_gt h0h) (hc.2 (h.trans c0.symm))
    · exact (ne_of_lt hh1) (hc.2 (h.trans c1.symm))⟩
  have hmL : m ∈ L := hcr ▸ mem_range_self half
  let L₁ := c '' Iic half
  let L₂ := c '' Ici half
  have hL12 : L = L₁ ∪ L₂ := by
    rw [← hcr, ← image_union, Iic_union_Ici, image_univ]
  have hL₁ : L₁ ⊆ L := by rw [hL12]; exact subset_union_left
  have hL₂ : L₂ ⊆ L := by rw [hL12]; exact subset_union_right
  have hm12 : L₁ ∩ L₂ ⊆ {m} := by
    rintro _ ⟨⟨s, hs, rfl⟩, ⟨t, ht, he⟩⟩
    have := hc.2 he
    subst this
    exact congrArg c (le_antisymm hs ht)
  have hbnL₁ : b ∉ L₁ := by
    rintro ⟨s, hs, he⟩
    have : s = 1 := hc.2 (he.trans c1.symm)
    subst this
    exact not_le.mpr hh1 hs
  have hanL₂ : a ∉ L₂ := by
    rintro ⟨s, hs, he⟩
    have : s = 0 := hc.2 (he.trans c0.symm)
    subst this
    exact not_le.mpr h0h hs
  have haL₁ : a ∈ L₁ := ⟨0, unitInterval.nonneg', c0⟩
  have hbL₂ : b ∈ L₂ := ⟨1, unitInterval.le_one', c1⟩
  /- The two pieces of the part of `G` in `r̄ ∩ Δ`. -/
  let A₀ : Set S := closure r ∩ Δ
  have hA₀ : IsClosed A₀ := isClosed_closure.inter hΔ.isClosed
  let Sa : Set S := (Y ∩ (G.V ∩ A₀)) ∪ edgesIn G A₀ fun e => (tilde e ∩ Y).Nonempty
  let Sb : Set S := ((G.V ∩ A₀) \ Y) ∪ edgesIn G A₀ fun e => ¬ (tilde e ∩ Y).Nonempty
  have hVc : IsClosed G.V := G.finite_V.isClosed
  have hfin : (G.V ∩ A₀).Finite := G.finite_V.subset inter_subset_left
  have hSac : IsClosed Sa := (hfin.subset inter_subset_right).isClosed.union (isClosed_edgesIn _ _ _)
  have hSbc : IsClosed Sb := (hfin.subset diff_subset).isClosed.union (isClosed_edgesIn _ _ _)
  have hcle : ∀ {e : Set S}, e ⊆ A₀ → closure e ⊆ A₀ := fun h => closure_minimal h hA₀
  have hSasub : Sa ⊆ A₀ ∩ G.U := by
    rintro y (⟨-, hV, hy⟩ | hy)
    · exact ⟨hy, G.V_subset_U hV⟩
    · obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hy
      exact ⟨hcle he.2.1 hye, G.closure_subset_U he.1 hye⟩
  have hSbsub : Sb ⊆ A₀ ∩ G.U := by
    rintro y (⟨⟨hV, hy⟩, -⟩ | hy)
    · exact ⟨hy, G.V_subset_U hV⟩
    · obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hy
      exact ⟨hcle he.2.1 hye, G.closure_subset_U he.1 hye⟩
  have hclV : ∀ {e : Set S}, e ∈ G.E → ∀ {y}, y ∈ closure e → y ∈ G.V → y ∈ tilde e := fun he _ hy hyV => GM19.tilde_eq_inter_V G he ▸ ⟨hy, hyV⟩
  have hSaV : ∀ y ∈ Sa, y ∈ G.V → y ∈ Y := by
    rintro y (⟨hy, -⟩ | hy) hyV
    · exact hy
    · obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hy
      obtain ⟨x, hx, hxY⟩ := he.2.2
      exact hstep e he.1 he.2.1 x hx y (hclV he.1 hye hyV) hxY
  have hSbV : ∀ y ∈ Sb, y ∈ G.V → y ∉ Y := by
    rintro y (⟨-, hy⟩ | hy) hyV hyY
    · exact hy hyY
    · obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hy
      exact he.2.2 ⟨y, hclV he.1 hye hyV, hyY⟩
  have hSdis : ∀ z, z ∈ Sa → z ∈ Sb → False := fun z hza hzb => by
    by_cases hzV : z ∈ G.V
    · exact hSbV z hzb hzV (hSaV z hza hzV)
    rcases hza with hza | hza
    · exact hzV hza.2.1
    rcases hzb with hzb | hzb
    · exact hzV hzb.1.1
    obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hza
    obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp hzb
    have := edge_eq_of_mem G he.1 hf.1 hze hzf hzV
    subst this
    exact hf.2.2 he.2.2
  have hSaL : ∀ z ∈ Sa, z ∈ L → z = a := fun z hz hzL => by
    rcases hLU ⟨hzL, (hSasub hz).2⟩ with h | h
    · exact h
    · exact absurd (h ▸ hSaV z hz (h ▸ hbV)) hbY
  have hSbL : ∀ z ∈ Sb, z ∈ L → z = b := fun z hz hzL => by
    rcases hLU ⟨hzL, (hSbsub hz).2⟩ with h | h
    · exact absurd haY (h ▸ hSbV z hz (h ▸ haV))
    · exact h
  have hcover : ∀ y, y ∈ G.U → y ∈ closure r → y ∈ Δ → y ∈ Sa ∪ Sb := fun y hyU hyr hyΔ => by
    rcases mem_edges_or_vertex hT G hl hr hΔ hedge hyU hyr hyΔ with hyV | ⟨e, he, hsub, hye⟩
    · by_cases hyY : y ∈ Y
      · exact .inl (.inl ⟨hyY, hyV, hyr, hyΔ⟩)
      · exact .inr (.inl ⟨⟨hyV, hyr, hyΔ⟩, hyY⟩)
    · by_cases hP : (tilde e ∩ Y).Nonempty
      · exact .inl (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hsub, hP⟩, subset_closure hye⟩))
      · exact .inr (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hsub, hP⟩, subset_closure hye⟩))
  /- The two sides of `L`, and the side inside `Δ`. -/
  obtain ⟨D, A, B, hD, hLD, hDZ, -, -, hbL, hDe, hAc, hBc, hAn, hBn, hAL, hBL, hLA, hLB, -⟩ := exists_edge_lens hT hL hab G.isClosed_U hLU
  obtain ⟨h, g, cc⟩ := hΔ.exists_isChart
  have hmbd : m ∉ discBd D := fun hm => by
    rcases hbL ⟨hm, hmL⟩ with h' | h'
    · exact (ne_of_gt h0h) (hc.2 (h'.trans c0.symm))
    · exact (ne_of_lt hh1) (hc.2 (h'.trans c1.symm))
  have hmcl : m ∈ closure (discInt Δ) := by
    have hmΔ : m ∈ Δ := Surface.discBd_subset Δ (hLb hmL)
    have h1 : h m ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball _ one_ne_zero]
      exact cc.hm hmΔ
    have h2 := ((cc.gc (h m) (cc.hm hmΔ)).mono ball_subset_closedBall).mem_closure_image h1
    rwa [cc.gh hmΔ, ← cc.discInt_eq] at h2
  have hIo : IsOpen (discInt Δ) := hΔ.isOpen_discInt hman
  obtain ⟨y, hyD, hyI⟩ := mem_closure_iff.mp hmcl _ (hD.isOpen_discInt hman) ⟨hLD hmL, hmbd⟩
  have hyL : y ∉ L := fun h' => hyI.2 (hLb h')
  have hmem : ∀ {C : Set S}, C ⊆ D → IsPreconnected C → Disjoint C L → L ⊆ closure C → (y ∈ C) →
      C ⊆ discInt Δ ∧ C ⊆ r ∧ Disjoint C G.U := fun {C} hCD hCc hCL hLC hyC => by
    have hCU : Disjoint C G.U := Set.disjoint_left.mpr fun z hz hzU => by
      rcases hDZ ⟨hCD hz, hzU⟩ with h' | h'
      · exact Set.disjoint_left.mp hCL hz (h' ▸ ha)
      · exact Set.disjoint_left.mp hCL hz (h' ▸ hb)
    have hCr : C ⊆ r := hrA C hCc hCU (by
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp (hLC hmL) r hro hmr
      exact ⟨w, hw2, hw1⟩)
    refine ⟨fun z hz => ?_, hCr, hCU⟩
    have hbdC : ∀ w ∈ C, w ∉ discBd Δ := fun w hw hwb => by
      rcases hbU hwb with h' | h'
      · exact Set.disjoint_left.mp hCU hw h'
      · exact Set.disjoint_left.mp hCL hw h'
    by_contra hzI
    have hzΔ : z ∉ Δ := fun h' => hzI ⟨h', hbdC z hz⟩
    obtain ⟨w, -, hw1, hw2⟩ := hCc _ _ hIo hΔ.isClosed.isOpen_compl (fun w hw => by
      by_cases h' : w ∈ Δ
      · exact .inl ⟨h', hbdC w hw⟩
      · exact .inr h') ⟨y, hyC, hyI⟩ ⟨z, hz, hzΔ⟩
    exact hw2 hw1.1
  obtain ⟨Sd, hSdc, hSdL, hLSd, hSdI, hSdr, hSdU, hSdne⟩ : ∃ Sd, IsPreconnected Sd ∧ Disjoint Sd L ∧ L ⊆ closure Sd ∧ Sd ⊆ discInt Δ ∧ Sd ⊆ r ∧ Disjoint Sd G.U ∧ Sd.Nonempty := by
    have hy' : y ∈ A ∪ B ∪ L := hDe ▸ hyD.1
    rcases hy' with (hyA | hyB) | h'
    · have hAD : A ⊆ D := by rw [hDe]; exact fun z hz => .inl (.inl hz)
      obtain ⟨h1, h2, h3⟩ := hmem hAD hAc hAL hLA hyA
      exact ⟨A, hAc, hAL, hLA, h1, h2, h3, hAn⟩
    · have hBD : B ⊆ D := by rw [hDe]; exact fun z hz => .inl (.inr hz)
      obtain ⟨h1, h2, h3⟩ := hmem hBD hBc hBL hLB hyB
      exact ⟨B, hBc, hBL, hLB, h1, h2, h3, hBn⟩
    · exact absurd h' hyL
  /- Now we are in the plane. -/
  have hSdΔ : Sd ⊆ Δ := fun z hz => (hSdI hz).1
  have hhi : InjOn h Δ := fun x hx y hy he => by
    have := congrArg g he
    rwa [cc.gh hx, cc.gh hy] at this
  obtain ⟨x₀, hx₀⟩ := hSdne
  have hnorm : ∀ z ∈ Δ, ‖h z‖ ≤ 1 := fun z hz => by simpa using cc.hm hz
  let O : Set ℂ := (closedBall (0 : ℂ) 1)ᶜ
  have hp : (2 : ℂ) ∈ O := by simp [O]
  have hpK : ∀ K : Set S, K ⊆ Δ → (2 : ℂ) ∉ h '' K := by
    rintro K hK ⟨z, hz, he⟩
    have := hnorm z (hK hz)
    rw [he] at this
    norm_num at this
  have hsep : ∀ K J : Set S, K ⊆ Δ → J ⊆ L → J.Nonempty → Disjoint J K → Disjoint Sd K → (2 : ℂ) ∈ connectedComponentIn (h '' K)ᶜ (h x₀) := fun K J hK hJ hJn hJK hSK => by
    have hc' := isPreconnected_across cc hSdc hSdΔ (hJ.trans hLSd) (hJ.trans hLb) hJn
    refine hc'.subset_connectedComponentIn (x := h x₀) (.inl (.inl ⟨x₀, hx₀, rfl⟩)) ?_ (.inr hp)
    rintro z (( ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩) | hz) ⟨w', hw', he⟩
    · exact Set.disjoint_left.mp hSK hw (hhi (hK hw') (hSdΔ hw) he ▸ hw')
    · exact Set.disjoint_left.mp hJK hw (hhi (hK hw') ((hJ.trans hLb).trans (Surface.discBd_subset Δ) hw) he ▸ hw')
    · exact hz (by rw [← he]; simpa using hnorm w' (hK hw'))
  let K₁ : Set S := Sa ∪ L₁
  let K₂ : Set S := Sb ∪ L₂
  have hLΔ : L ⊆ Δ := hLb.trans (Surface.discBd_subset Δ)
  have hK₁ : K₁ ⊆ Δ := union_subset (fun z hz => (hSasub hz).1.2) (hL₁.trans hLΔ)
  have hK₂ : K₂ ⊆ Δ := union_subset (fun z hz => (hSbsub hz).1.2) (hL₂.trans hLΔ)
  have hcompK : ∀ {K : Set S}, IsClosed K → K ⊆ Δ → IsCompact (h '' K) := fun hK hsub => hK.isCompact.image_of_continuousOn (cc.hc.mono hsub)
  have hclL₁ : IsClosed L₁ := (isClosed_Iic.isCompact.image hc.1).isClosed
  have hclL₂ : IsClosed L₂ := (isClosed_Ici.isCompact.image hc.1).isClosed
  have hx₀S : ∀ {T : Set S}, T ⊆ G.U ∪ L → x₀ ∉ T := fun hT' hin => by
    rcases hT' hin with h' | h'
    · exact Set.disjoint_left.mp hSdU hx₀ h'
    · exact Set.disjoint_left.mp hSdL hx₀ h'
  have hK₁U : K₁ ⊆ G.U ∪ L := union_subset (fun z hz => .inl (hSasub hz).2) (hL₁.trans subset_union_right)
  have hK₂U : K₂ ⊆ G.U ∪ L := union_subset (fun z hz => .inl (hSbsub hz).2) (hL₂.trans subset_union_right)
  have hSdK : ∀ {K : Set S}, K ⊆ G.U ∪ L → Disjoint Sd K := fun hK => Set.disjoint_left.mpr fun z hz hzK => by
    rcases hK hzK with h' | h'
    · exact Set.disjoint_left.mp hSdU hz h'
    · exact Set.disjoint_left.mp hSdL hz h'
  have hJ₂ : (2 : ℂ) ∈ connectedComponentIn (h '' K₁)ᶜ (h x₀) := hsep K₁ (L₂ \ {m}) hK₁ (diff_subset.trans hL₂) ⟨b, hbL₂, fun h' => by
      exact hbnL₁ (by rw [mem_singleton_iff.mp h']; exact ⟨half, le_rfl, rfl⟩)⟩ (Set.disjoint_left.mpr fun z hz hzK => by
      rcases hzK with h' | h'
      · have hz1 := hSaL z h' (hL₂ hz.1)
        exact hanL₂ (hz1 ▸ hz.1)
      · exact hz.2 (hm12 ⟨h', hz.1⟩)) (hSdK hK₁U)
  have hJ₁ : (2 : ℂ) ∈ connectedComponentIn (h '' K₂)ᶜ (h x₀) := hsep K₂ (L₁ \ {m}) hK₂ (diff_subset.trans hL₁) ⟨a, haL₁, fun h' => by
      exact hanL₂ (by rw [mem_singleton_iff.mp h']; exact ⟨half, le_rfl, rfl⟩)⟩ (Set.disjoint_left.mpr fun z hz hzK => by
      rcases hzK with h' | h'
      · have hz1 := hSbL z h' (hL₁ hz.1)
        exact hbnL₁ (hz1 ▸ hz.1)
      · exact hz.2 (hm12 ⟨hz.1, h'⟩)) (hSdK hK₂U)
  have hinter : h '' K₁ ∩ h '' K₂ = {h m} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨w, hw, rfl⟩, ⟨w', hw', he⟩⟩
      have := hhi (hK₂ hw') (hK₁ hw) he
      subst this
      have hwm : w' = m := by
        rcases hw with hw | hw <;> rcases hw' with hw' | hw'
        · exact (hSdis _ hw hw').elim
        · exact absurd (hSaL _ hw (hL₂ hw') ▸ hw') hanL₂
        · exact absurd (hSbL _ hw' (hL₁ hw) ▸ hw) hbnL₁
        · exact hm12 ⟨hw, hw'⟩
      rw [hwm]
      rfl
    · rintro _ rfl
      exact ⟨⟨m, .inr ⟨half, le_rfl, rfl⟩, rfl⟩, ⟨m, .inr ⟨half, le_rfl, rfl⟩, rfl⟩⟩
  have hq₁ : h x₀ ∉ h '' K₁ ∪ h '' K₂ := by
    rintro (⟨w, hw, he⟩ | ⟨w, hw, he⟩)
    · exact hx₀S hK₁U (hhi (hK₁ hw) (hSdΔ hx₀) he ▸ hw)
    · exact hx₀S hK₂U (hhi (hK₂ hw) (hSdΔ hx₀) he ▸ hw)
  have hp₁ : (2 : ℂ) ∉ h '' K₁ ∪ h '' K₂ := by
    rintro (h' | h')
    · exact hpK _ hK₁ h'
    · exact hpK _ hK₂ h'
  have hjan := janiszewski (hcompK (hSac.union hclL₁) hK₁) (hcompK (hSbc.union hclL₂) hK₂) (by rw [hinter]; exact isPreconnected_singleton) hq₁ hp₁ hJ₂ hJ₁
  /- The part of `r` next to `L` in the plane. -/
  let Ω : Set ℂ := ball 0 1 ∩ g ⁻¹' r
  have hΩ : IsOpen Ω := (cc.gc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball hro
  let R := connectedComponentIn Ω (h x₀)
  have hROpen : IsOpen R := hΩ.connectedComponentIn
  have hqΩ : h x₀ ∈ Ω := by
    refine ⟨?_, ?_⟩
    · have h1 : x₀ ∈ g '' ball 0 1 := cc.discInt_eq ▸ hSdI hx₀
      obtain ⟨w, hw, rfl⟩ := h1
      rw [cc.hg (ball_subset_closedBall hw)]
      exact hw
    · show g (h x₀) ∈ r
      rw [cc.gh (hSdΔ hx₀)]
      exact hSdr hx₀
  have hqR : h x₀ ∈ R := mem_connectedComponentIn hqΩ
  have hRΩ : R ⊆ Ω := connectedComponentIn_subset _ _
  have hconn : IsPreconnected (connectedComponentIn (h '' K₁ ∪ h '' K₂)ᶜ (h x₀)) := isPreconnected_connectedComponentIn
  have hpR : (2 : ℂ) ∉ R := fun h' => by
    have := (hRΩ h').1
    rw [mem_ball_zero_iff] at this
    norm_num at this
  obtain ⟨z, hzK, hzR, hzcl⟩ : ∃ z, z ∈ connectedComponentIn (h '' K₁ ∪ h '' K₂)ᶜ (h x₀) ∧ z ∉ R ∧ z ∈ closure R := by
    by_contra hno
    push Not at hno
    obtain ⟨w, -, hw1, hw2⟩ := hconn R (closure R)ᶜ hROpen isClosed_closure.isOpen_compl (fun w hw => by
      by_cases hwR : w ∈ R
      · exact .inl hwR
      · exact .inr (hno w hw hwR)) ⟨h x₀, mem_connectedComponentIn hq₁, hqR⟩ ⟨2, hjan, hno 2 hjan hpR⟩
    exact hw2 (subset_closure hw1)
  have hzn : z ∉ h '' K₁ ∪ h '' K₂ := connectedComponentIn_subset _ _ hzK
  have hzb : z ∈ closedBall (0 : ℂ) 1 := by
    have : closure R ⊆ closure (ball (0 : ℂ) 1) := closure_mono fun w hw => (hRΩ hw).1
    rw [closure_ball _ one_ne_zero] at this
    exact this hzcl
  have hyΔ : g z ∈ Δ := cc.gm hzb
  have hhg : h (g z) = z := cc.hg hzb
  have hyr : g z ∈ closure r := by
    have h1 := ((cc.gc z hzb).mono fun w hw => ball_subset_closedBall (hRΩ hw).1).mem_closure_image hzcl
    exact closure_mono (image_subset_iff.mpr fun w hw => (hRΩ hw).2) h1
  by_cases hyU : g z ∈ G.U
  · rcases hcover _ hyU hyr hyΔ with h' | h'
    · exact hzn (.inl ⟨g z, .inl h', hhg⟩)
    · exact hzn (.inr ⟨g z, .inl h', hhg⟩)
  have hyrr : g z ∈ r := by
    by_contra hn
    exact hyU (hrF ⟨hyr, hn⟩)
  have hzball : z ∈ ball (0 : ℂ) 1 := by
    by_contra hn
    have hzs : z ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]
      rw [mem_ball_zero_iff, not_lt] at hn
      rw [mem_closedBall_zero_iff] at hzb
      linarith
    rw [← cc.bd] at hzs
    obtain ⟨w, hw, he⟩ := hzs
    have hgw : g z = w := by rw [← he, cc.gh (Surface.discBd_subset Δ hw)]
    rw [← hgw] at hw
    rcases hbU hw with h' | h'
    · exact hyU h'
    · rw [hL12] at h'
      rcases h' with h' | h'
      · exact hzn (.inl ⟨g z, .inr h', hhg⟩)
      · exact hzn (.inr ⟨g z, .inr h', hhg⟩)
  have hzΩ : z ∈ Ω := ⟨hzball, hyrr⟩
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hzcl _ hΩ.connectedComponentIn (mem_connectedComponentIn hzΩ)
  have e : connectedComponentIn Ω (h x₀) = connectedComponentIn Ω z := (connectedComponentIn_eq hw2).trans (connectedComponentIn_eq hw1).symm
  exact hzR (by
    show z ∈ connectedComponentIn Ω (h x₀)
    rw [e]
    exact mem_connectedComponentIn hzΩ)

end GraphMinor.GM19
