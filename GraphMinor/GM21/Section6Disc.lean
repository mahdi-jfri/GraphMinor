module

public import GraphMinor.GM21.Section6Jumps
public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section3Dual
import GraphMinor.GM17.CuffOrder
import GraphMinor.GM21.Section6Supports

/-!
# Graph Minors XXI, proof of (6.4): jumps in a disc do not cross

In the proof of (6.4) (page 25 of the preprint) the jumps of `Γ` in the disc `Σ` are nested:
"if $r_1, r_2$ touch then $\bar{r}_1 \cap \bar{r}_2 = U(J)$ for some $\Sigma$-jump $J$". This rests
on the fact that two different jumps cannot cross: if the ends `a, c` of one jump and the ends
`b, d` of another occur in the order `a, b, c, d` around `bd(Σ)`, the two jumps meet
(`jumps_not_cross`). Here the jumps are subgraphs of `Γ`, and we draw each as a compact
connected set of `Σ` made of the closures of its edges (`exists_points_of_walk`). Two such sets
of different jumps meet only in common vertices (`mem_of_mem_points_of_mem_points`), and two
different jumps have no common vertex but an end (Section 6, page 24 of the preprint).

`pairsCrossOn_of_angles` gives the crossing on a cuff from the angles of the four points.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Topology Hypergraph GraphMinor.GM10 GraphMinor.Surface

universe u v w

section points

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}

/-- An edge `e` of a drawing whose closure has two vertices: the points of `ē` that are not
vertices are the points of `e`. -/
theorem closure_sdiff_subset_of_two {e : Set S} (he : e ∈ Γ.E) {u v : S} (huv : u ≠ v)
    (hu : u ∈ closure e ∩ Γ.V) (hv : v ∈ closure e ∩ Γ.V) : closure e \ Γ.V ⊆ e := by
  rcases Γ.edge_cond e he with ⟨u₀, v₀, hne, hcap, -⟩ | ⟨u₀, hcap, -⟩
  · have hlink : Γ.toGraph.IsLink e u₀ v₀ := by
      refine ⟨he, ?_, ?_, hcap⟩
      · exact (show u₀ ∈ closure e ∩ Γ.V from hcap ▸ Or.inl rfl).2
      · exact (show v₀ ∈ closure e ∩ Γ.V from hcap ▸ Or.inr rfl).2
    rw [GM06.closure_edge_eq_union_ends Γ hlink hne]
    rintro p ⟨hp | hp, hpV⟩
    · exact hp
    · rcases hp with rfl | rfl
      · exact absurd (show p ∈ closure e ∩ Γ.V from hcap ▸ Or.inl rfl).2 hpV
      · exact absurd (show p ∈ closure e ∩ Γ.V from hcap ▸ Or.inr rfl).2 hpV
  · rw [hcap] at hu hv
    exact absurd (hu.trans hv.symm) huv

/-- The closure of an edge `e` of `Γ` whose image is an edge of a linkage `Γ_sub` has two vertices,
so its points outside `V(Γ)` are those of `e`. -/
theorem closure_sdiff_subset_of_isDrawingIso (hiso : IsDrawingIso Γ Γ_sub ιV ιE)
    (h2 : ∀ e ∈ Γ_sub.edgeSet, (Γ_sub.ends e).ncard = 2) {e : Set S} (he : e ∈ Γ.E) :
    closure e \ Γ.V ⊆ e := by
  have heE : ιE e ∈ Γ_sub.edgeSet := hiso.ιE_image ▸ mem_image_of_mem ιE he
  obtain ⟨u', v', huv', hends⟩ := ncard_eq_two.1 (h2 _ heE)
  have hu' : Γ_sub.Inc (ιE e) u' := show u' ∈ Γ_sub.ends (ιE e) from hends ▸ Or.inl rfl
  have hv' : Γ_sub.Inc (ιE e) v' := show v' ∈ Γ_sub.ends (ιE e) from hends ▸ Or.inr rfl
  obtain ⟨u, hu, rfl⟩ : u' ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc hu'
  obtain ⟨v, hv, rfl⟩ : v' ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc hv'
  exact closure_sdiff_subset_of_two he (fun h => huv' (congrArg ιV h))
    ⟨(hiso.inc_iff e he u hu).1 hu', hu⟩ ⟨(hiso.inc_iff e he v hv).1 hv', hv⟩

/-- A walk in a subgraph `J` of `Γ` is drawn as a compact connected set of `Σ`, which contains the
two ends of the walk, and whose points are points of edges of `J` or vertices of `J`. -/
theorem exists_points_of_walk (hiso : IsDrawingIso Γ Γ_sub ιV ιE)
    (h2 : ∀ e ∈ Γ_sub.edgeSet, (Γ_sub.ends e).ncard = 2) {J : Hypergraph α β} (hJ : J ≤ Γ_sub) :
    ∀ {x y : α} (_ : J.skeleton.Walk x y), x ∈ J.vertexSet → ∀ x₀ ∈ Γ.V, ιV x₀ = x →
      ∀ y₀ ∈ Γ.V, ιV y₀ = y →
      ∃ K : Set S, IsCompact K ∧ IsConnected K ∧ x₀ ∈ K ∧ y₀ ∈ K ∧
        ∀ p ∈ K, (∃ e ∈ Γ.E, ιE e ∈ J.edgeSet ∧ p ∈ e) ∨ (p ∈ Γ.V ∧ ιV p ∈ J.vertexSet) := by
  intro x y w
  induction w with
  | nil =>
    intro hx x₀ hx₀ hx₀x y₀ hy₀ hy₀x
    have : x₀ = y₀ := hiso.ιV_injOn hx₀ hy₀ (hx₀x.trans hy₀x.symm)
    subst this
    refine ⟨{x₀}, isCompact_singleton, isConnected_singleton, rfl, rfl, ?_⟩
    rintro p rfl
    exact Or.inr ⟨hx₀, hx₀x ▸ hx⟩
  | @cons x z y hadj w' ih =>
    intro hx x₀ hx₀ hx₀x y₀ hy₀ hy₀y
    obtain ⟨-, e', hxe, hze⟩ := hadj
    have he'J : e' ∈ J.edgeSet := J.edge_mem_of_inc hxe
    have hzJ : z ∈ J.vertexSet := J.vertex_mem_of_inc hze
    obtain ⟨z₀, hz₀, rfl⟩ : z ∈ ιV '' Γ.V := hiso.ιV_image ▸ hJ.vertexSet_subset hzJ
    obtain ⟨K', hK'c, hK'conn, hz₀K', hy₀K', hK'pts⟩ := ih hzJ z₀ hz₀ rfl y₀ hy₀ hy₀y
    obtain ⟨e, he, rfl⟩ : e' ∈ ιE '' Γ.E := hiso.ιE_image ▸ hJ.edgeSet_subset he'J
    have hx₀e : x₀ ∈ closure e :=
      (hiso.inc_iff e he x₀ hx₀).1 (hx₀x ▸ GM10.inc_of_le hJ hxe)
    have hz₀e : z₀ ∈ closure e := (hiso.inc_iff e he z₀ hz₀).1 (GM10.inc_of_le hJ hze)
    refine ⟨closure e ∪ K', (GM06.isCompact_closure_edge Γ he).union hK'c,
      IsConnected.union ⟨z₀, hz₀e, hz₀K'⟩ (GM06.isConnected_closure_edge Γ he) hK'conn,
      Or.inl hx₀e, Or.inr hy₀K', ?_⟩
    rintro p (hp | hp)
    · by_cases hpV : p ∈ Γ.V
      · right
        refine ⟨hpV, J.vertex_mem_of_inc ((GM10.inc_iff_of_le hJ he'J).2 ?_)⟩
        exact (hiso.inc_iff e he p hpV).2 hp
      · left
        exact ⟨e, he, he'J, closure_sdiff_subset_of_isDrawingIso hiso h2 he ⟨hp, hpV⟩⟩
    · exact hK'pts p hp

/-- A point drawn both for `J` and for `J'`, where `J` and `J'` have no common edge, is a vertex
of `Γ` that is a vertex of both. -/
theorem mem_of_mem_points_of_mem_points {J J' : Hypergraph α β}
    (hE : Disjoint J.edgeSet J'.edgeSet) {p : S}
    (hp : (∃ e ∈ Γ.E, ιE e ∈ J.edgeSet ∧ p ∈ e) ∨ (p ∈ Γ.V ∧ ιV p ∈ J.vertexSet))
    (hp' : (∃ e ∈ Γ.E, ιE e ∈ J'.edgeSet ∧ p ∈ e) ∨ (p ∈ Γ.V ∧ ιV p ∈ J'.vertexSet)) :
    p ∈ Γ.V ∧ ιV p ∈ J.vertexSet ∧ ιV p ∈ J'.vertexSet := by
  have hnotV : ∀ e ∈ Γ.E, p ∈ e → p ∉ Γ.V := fun e he hpe => (he.2.1 hpe).2
  rcases hp with ⟨e, he, heJ, hpe⟩ | ⟨hpV, hpJ⟩
  · rcases hp' with ⟨e', he', he'J, hpe'⟩ | ⟨hpV, -⟩
    · have hee : e = e' := by
        by_contra hne
        exact Set.disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he he' hne) hpe hpe'
      subst hee
      exact absurd he'J (Set.disjoint_left.mp hE heJ)
    · exact absurd hpV (hnotV e he hpe)
  · rcases hp' with ⟨e', he', -, hpe'⟩ | ⟨-, hpJ'⟩
    · exact absurd hpV (hnotV e' he' hpe')
    · exact ⟨hpV, hpJ, hpJ'⟩

end points

section angles

variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Two points on opposite lines of a circle cross the ends of the lines (as
`GM17.pairsCross_of_lines`, for a space in any universe). -/
private theorem pairsCross_of_lines' {C J₁ J₂ : Set S} {x y b d : S}
    (hJ₁ : IsLineWithEnds J₁ x y) (hJ₂ : IsLineWithEnds J₂ x y) (hu : J₁ ∪ J₂ = C)
    (hi : J₁ ∩ J₂ = {x, y}) (hb : b ∈ J₁) (hd : d ∈ J₂) (hbx : b ≠ x) (hby : b ≠ y)
    (hdx : d ≠ x) (hdy : d ≠ y) : PairsCrossOn C x y b d := by
  have hbC : b ∈ C := hu ▸ .inl hb
  have hdC : d ∈ C := hu ▸ .inr hd
  have hne : b ≠ d := by
    rintro rfl
    have h3 : b ∈ J₁ ∩ J₂ := ⟨hb, hd⟩
    rw [hi] at h3
    rcases h3 with h3 | h3
    · exact hbx h3
    · exact hby h3
  refine ⟨hu ▸ .inl hJ₁.left_mem, hbC, hu ▸ .inl hJ₁.right_mem, hdC, hJ₁.ne', hne, hbx.symm,
    hdx.symm, hby.symm, hdy.symm, fun he => ?_⟩
  have hbm : b ∈ C \ {x, y} := ⟨hbC, by rintro (h | h); exacts [hbx h, hby h]⟩
  have hdm : d ∈ C \ {x, y} := ⟨hdC, by rintro (h | h); exacts [hdx h, hdy h]⟩
  have hd' : d ∈ connectedComponentIn (C \ {x, y}) b := he ▸ mem_connectedComponentIn hdm
  have hsub := connectedComponentIn_subset (C \ {x, y}) b
  obtain ⟨z, hz, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn J₁ J₂
    hJ₁.isCompact.isClosed hJ₂.isCompact.isClosed (fun z hz => hu ▸ (hsub hz).1)
    ⟨b, mem_connectedComponentIn hbm, hb⟩ ⟨d, hd', hd⟩
  exact (hsub hz).2 (hi ▸ ⟨hz₁, hz₂⟩)

/-- Four points of an `O`-arc `C` with angles `ta < tb < tc < td < ta + 2π` cross:
`{cuffPoint ta, cuffPoint tc}` separates `cuffPoint tb` from `cuffPoint td` on `C`. -/
theorem pairsCrossOn_of_angles {C : Set S} (f : Circle ≃ₜ C) {ta tb tc td : ℝ} (h1 : ta < tb)
    (h2 : tb < tc) (h3 : tc < td) (h4 : td < ta + 2 * Real.pi) :
    PairsCrossOn C (GM19.cuffPoint f ta) (GM19.cuffPoint f tc) (GM19.cuffPoint f tb)
      (GM19.cuffPoint f td) := by
  have hpi := Real.pi_pos
  have hJ₁ : IsLineWithEnds (GM19.cuffPoint f '' Icc ta tc) (GM19.cuffPoint f ta) (GM19.cuffPoint f tc) :=
    Supports.isLineWithEnds_cuffPoint_Icc f (h1.trans h2) (by linarith)
  have hJ₂' : IsLineWithEnds (GM19.cuffPoint f '' Icc tc (ta + 2 * Real.pi)) (GM19.cuffPoint f tc) (GM19.cuffPoint f (ta + 2 * Real.pi)) :=
    Supports.isLineWithEnds_cuffPoint_Icc f (by linarith) (by linarith)
  rw [GM17.cuffPoint_add_two_pi] at hJ₂'
  have hJ₂ := hJ₂'.symm
  have hinj := GM17.cuffPoint_injOn_Ico f ta
  have hu : GM19.cuffPoint f '' Icc ta tc ∪ GM19.cuffPoint f '' Icc tc (ta + 2 * Real.pi) = C := by
    rw [← image_union, Icc_union_Icc_eq_Icc (h1.trans h2).le (by linarith)]
    apply Subset.antisymm
    · rintro _ ⟨t, -, rfl⟩
      exact GM17.cuffPoint_mem f t
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := GM17.exists_cuffPoint_mem_Ico f ta hx
      exact ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩
  have hi : GM19.cuffPoint f '' Icc ta tc ∩ GM19.cuffPoint f '' Icc tc (ta + 2 * Real.pi) = {GM19.cuffPoint f ta, GM19.cuffPoint f tc} := by
    apply Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, hst⟩⟩
      rcases eq_or_lt_of_le ht.2 with hteq | htlt
      · left
        rw [hteq, GM17.cuffPoint_add_two_pi] at hst
        have := hinj ⟨le_rfl, by linarith⟩ ⟨hs.1, by linarith [hs.2]⟩ hst
        rw [← this]
      · have := hinj ⟨by linarith [ht.1], htlt⟩ ⟨hs.1, by linarith [hs.2]⟩ hst
        right
        rw [← this]
        congr 1
        linarith [hs.2, ht.1]
    · rintro x (rfl | rfl)
      · exact ⟨⟨ta, ⟨le_rfl, (h1.trans h2).le⟩, rfl⟩,
          ⟨ta + 2 * Real.pi, ⟨by linarith, le_rfl⟩, GM17.cuffPoint_add_two_pi f ta⟩⟩
      · exact ⟨⟨tc, ⟨(h1.trans h2).le, le_rfl⟩, rfl⟩, ⟨tc, ⟨le_rfl, by linarith⟩, rfl⟩⟩
  have hne : ∀ {s t : ℝ}, s ∈ Ico ta (ta + 2 * Real.pi) → t ∈ Ico ta (ta + 2 * Real.pi) → s ≠ t →
      GM19.cuffPoint f s ≠ GM19.cuffPoint f t := fun hs ht hst h => hst (hinj hs ht h)
  have mem : ∀ {t : ℝ}, ta ≤ t → t < ta + 2 * Real.pi → t ∈ Ico ta (ta + 2 * Real.pi) :=
    fun h h' => ⟨h, h'⟩
  refine pairsCross_of_lines' hJ₁ hJ₂ hu hi ⟨tb, ⟨h1.le, h2.le⟩, rfl⟩
    ⟨td, ⟨h3.le, h4.le⟩, rfl⟩ ?_ ?_ ?_ ?_
  · exact hne (mem h1.le (by linarith)) (mem le_rfl (by linarith)) h1.ne'
  · exact hne (mem h1.le (by linarith)) (mem (by linarith) (by linarith)) h2.ne
  · exact hne (mem (by linarith) h4) (mem le_rfl (by linarith)) (by linarith)
  · exact hne (mem (by linarith) h4) (mem (by linarith) (by linarith)) h3.ne'

end angles

section disc

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}

/-- Two different jumps of `Γ` in a disc do not cross: if the ends `a, c` of `J` and the ends
`b, d` of `J'` cross on `bd(Σ)`, then `J = J'`. -/
theorem jumps_not_cross (hS : GM06.IsClosedDiscSpace S) (hiso : IsDrawingIso Γ Γ_sub ιV ιE)
    (hK : IsLinkage G Γ_sub)
    (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)
    {J J' : Hypergraph α β} (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)))
    (hJ' : J' ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) {a b c d : S}
    (ha : a ∈ Γ.V) (hb : b ∈ Γ.V) (hc : c ∈ Γ.V) (hd : d ∈ Γ.V)
    (haJ : ιV a ∈ terminals J) (hcJ : ιV c ∈ terminals J) (hbJ : ιV b ∈ terminals J')
    (hdJ : ιV d ∈ terminals J') (hcross : PairsCrossOn (bd S) a c b d) : J = J' := by
  by_contra hne
  have h2 : ∀ e ∈ Γ_sub.edgeSet, (Γ_sub.ends e).ncard = 2 := fun e he => hK.ends_ncard_eq_two he
  obtain ⟨-, -, -, -, hac, hbd, hab, had, hcb, hcd, -⟩ := id hcross
  -- Draw `J` from `a` to `c` and `J'` from `b` to `d`.
  obtain ⟨w⟩ := hJ.2.1.2.2.1 (ιV a) haJ.1 (ιV c) hcJ.1
  obtain ⟨w'⟩ := hJ'.2.1.2.2.1 (ιV b) hbJ.1 (ιV d) hdJ.1
  obtain ⟨K, hKc, hKconn, haK, hcK, hKpts⟩ :=
    exists_points_of_walk hiso h2 hJ.1 w haJ.1 a ha rfl c hc rfl
  obtain ⟨K', hK'c, hK'conn, hbK', hdK', hK'pts⟩ :=
    exists_points_of_walk hiso h2 hJ'.1 w' hbJ.1 b hb rfl d hd rfl
  obtain ⟨p, hpK, hpK'⟩ := GM06.discCrossing_of_isClosedDiscSpace hS hKc hK'c hKconn hK'conn
    haK hcK hbK' hdK' hcross
  have hEdisj : Disjoint J.edgeSet J'.edgeSet := by
    rw [Set.disjoint_left]
    intro f hf hf'
    exact hne (jump_eq_of_edge hdeg hJ hJ' hf hf')
  obtain ⟨hpV, hpJ, hpJ'⟩ :=
    mem_of_mem_points_of_mem_points hEdisj (hKpts p hpK) (hK'pts p hpK')
  have hpB : ιV p ∈ ιV '' (Γ.V ∩ bd S) := by
    by_contra h
    exact hne (jump_eq_of_vertex hdeg hJ hJ' hpJ hpJ' h)
  have hpT := mem_terminals_of_mem_jumpSet hJ hpJ hpB
  have hpT' := mem_terminals_of_mem_jumpSet hJ' hpJ' hpB
  have hinj := hiso.ιV_injOn
  -- A third member of a two-element set of terminals equals one of the other two.
  have key : ∀ {J₁ : Hypergraph α β}, J₁ ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)) →
      ∀ {x y z : α}, x ∈ terminals J₁ → y ∈ terminals J₁ → z ∈ terminals J₁ → x ≠ y →
        z = x ∨ z = y := by
    intro J₁ h₁ x y z hx hy hz hxy
    obtain ⟨x', -, y', -, -, hterm, -, -⟩ := terminals_eq_of_mem_jumpSet h₁
    rw [hterm] at hx hy hz
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> simp_all
  have hac' : ιV a ≠ ιV c := fun h => hac (hinj ha hc h)
  have hbd' : ιV b ≠ ιV d := fun h => hbd (hinj hb hd h)
  rcases key hJ haJ hcJ hpT hac' with h1 | h1 <;> rcases key hJ' hbJ hdJ hpT' hbd' with h2 | h2
  · exact hab (hinj ha hb (h1.symm.trans h2))
  · exact had (hinj ha hd (h1.symm.trans h2))
  · exact hcb (hinj hc hb (h1.symm.trans h2))
  · exact hcd (hinj hc hd (h1.symm.trans h2))

end disc

end GM21
end GraphMinor
