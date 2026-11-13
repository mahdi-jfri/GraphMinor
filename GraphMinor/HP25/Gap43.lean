module

public import GraphMinor.HP25.Lemma43Case2
public import GraphMinor.HP25.Gap43Core
public import GraphMinor.HP25.Gap43Rural
public import GraphMinor.HP25.Society
public import GraphMinor.GM13.Defs
import GraphMinor.HP25.Gap43Plane
import GraphMinor.Compute.Bridge13
import GraphMinor.HP25.Embedding
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Path
import GraphMinor.GM13.Section8a

/-!
# The gap of Lemma 4.3

In the second case of the proof of Lemma 4.3, which starts on page 14, Humeau and Pous apply
induction to the graph `H = G[𝒞 ∪ P]` with the cycle `P L` (page 15: "It is easily proved that
$PzCx$ is crossed in any edge extension of $H$, hence $H$ is a web with frame $PzCx$ by
induction."), and for this they need `P L` to be crossless in `H`. The paper does not prove this
(see the correction to Lemma 4.3 in `corrections/HP25.md`). Here we prove it (`Case2.gap`) in five
steps.

1. View `G` with the cycle `C = x y z L` as a society (`cycleSociety`). Since `C` is crossless in
   `G`, the society has no cross (`isCrossed_of_hasCross`).
2. By Graph Minors XIII, (8.3) and (8.5), the society has a core `Z` whose society is rural. We only
   use that `Z` is trisecting and that the edges of the core are the paths of `G` with no inner
   vertex in `Z`.
3. The vertices of `P` lie in `Z`, and two of them adjacent in the core are consecutive on `P`
   (`Case2.mem_core`, `Case2.core_adj_P`).
4. The rural drawing of the core gives a plane embedding inside a disc, with the frame `C` on the
   boundary (`exists_planeEmbedding`).
5. A crossing of `P L` in `H` gives two disjoint paths of the core with alternating ends on `P L`,
   through vertices of `𝒞` and `P`, with each edge having an end in `𝒞`. In the drawing this is
   impossible (`PlaneEmbedding.plane_gap`).

Main result: `Case2.gap`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- An edge of `G` between two vertices of `Z` is an edge of the core graph. -/
theorem coreGraph_adj_of_adj {Z : Set V} {u w : V} (h : G.Adj u w) (hu : u ∈ Z) (hw : w ∈ Z) :
    (coreGraph G Z).Adj u w :=
  ⟨h.ne, hu, hw, h.toWalk, fun t ht h1 h2 => by
    simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    exact (ht.elim h1 h2).elim⟩

/-- A path of `G` gives a path of `Graph.ofSimpleGraph G` with the same vertices. -/
theorem exists_graphPath {u w : V} (p : G.Walk u w) (hp : p.IsPath) :
    ∃ Pg : Graph V (Sym2 V), GM09.IsGraphPathWithEnds (Graph.ofSimpleGraph G) Pg u w ∧
      Pg.vertexSet = {t | t ∈ p.support} :=
  ⟨GM09.walkSubgraph p.toGraphWalk,
    GM09.isGraphPathWithEnds_walkSubgraph (Walk.isSimple_toGraphWalk hp), by
      rw [GM09.vertexSet_walkSubgraph, Walk.support_toGraphWalk]⟩

/-- The vertices of `Z` reached from `v` with no other vertex in `Z` are the attachments of `v` in
the sense of Graph Minors XIII, Section 8 (page 93). -/
theorem reachOut_subset {Z : Set V} {v : V} :
    {w | ReachOut G Z v w} ⊆ {w ∈ Z | ∃ Pg : Graph V (Sym2 V),
      GM09.IsGraphPathWithEnds (Graph.ofSimpleGraph G) Pg v w ∧ Pg.vertexSet ∩ Z = {w}} := by
  classical
  rintro w ⟨hw, p, hp⟩
  obtain ⟨Pg, hPg, hV⟩ := exists_graphPath p.bypass p.bypass_isPath
  refine ⟨hw, Pg, hPg, ?_⟩
  ext t
  rw [hV]
  constructor
  · rintro ⟨ht, htZ⟩
    by_contra hne
    exact hp t (p.support_bypass_subset_support ht) hne htZ
  · intro ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact ⟨p.bypass.end_mem_support, hw⟩

/-- Two vertices adjacent in `coreGraph G Z`, for `Z` the vertex set of a core `Kc` of the society
of `G` and a cycle, are adjacent in `Kc`. -/
theorem core_adj_of_coreGraph_adj [Finite V] {C : List V} {hnd : C.Nodup} {hne : C ≠ []}
    {Kc : Graph V (Sym2 V)} (hK : GM13.IsCoreOf (cycleSociety G C hnd hne) Kc) {u w : V}
    (h : (coreGraph G Kc.vertexSet).Adj u w) : Kc.Adj u w := by
  classical
  obtain ⟨hne', hu, hw, p, hp⟩ := h
  refine (hK.adj_iff u hu w hw hne').mpr ?_
  obtain ⟨Pg, hPg, hV⟩ := exists_graphPath p.bypass p.bypass_isPath
  refine ⟨Pg, hPg, ?_⟩
  ext t
  rw [hV]
  constructor
  · rintro ⟨ht, htZ⟩
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact hp t (p.support_bypass_subset_support ht) hne.1 hne.2 htZ
  · intro ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht <;> rw [ht]
    · exact ⟨p.bypass.start_mem_support, hu⟩
    · exact ⟨p.bypass.end_mem_support, hw⟩

/-- A list without repetition of length at least three has at least three entries. -/
theorem three_le_ncard {C : List V} (hnd : C.Nodup) (h3 : 3 ≤ C.length) :
    3 ≤ {v | v ∈ C}.ncard := by
  classical
  have e : {v | v ∈ C} = (C.toFinset : Set V) := by ext; simp
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  exact h3

/-- Two entries next to each other in `T` are consecutive in the cyclic order of `T`. -/
theorem isConsec_succ {T : List V} (hnd : T.Nodup) (hne : T ≠ []) {k : ℕ}
    (hk : k + 1 < T.length) :
    IsConsec (GM09.CyclicPerm.ofNodupList T hnd hne) T[k] T[k + 1] := by
  refine ⟨by simp, by simp, fun h => by have := hnd.getElem_inj_iff.mp h; omega, ?_⟩
  refine Set.eq_empty_of_forall_notMem fun v hv => ?_
  have hvT : v ∈ T := by
    simpa using (GM09.CyclicPerm.ofNodupList T hnd hne).interval_subset_bar _ _ hv
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvT
  have := (GM09.CyclicPerm.ofNodupList_mem_interval_iff T hnd hne (Nat.lt_succ_self k) hk hj).mp hv
  omega

/-- The last and the first entry of `T` are consecutive in the cyclic order of `T`. -/
theorem isConsec_last {T : List V} (hnd : T.Nodup) (hne : T ≠ []) (h2 : 2 ≤ T.length) :
    IsConsec (GM09.CyclicPerm.ofNodupList T hnd hne) (T[T.length - 1]'(by omega))
      (T[0]'(by omega)) := by
  refine ⟨by simp, by simp, fun h => by have := hnd.getElem_inj_iff.mp h; omega, ?_⟩
  refine Set.eq_empty_of_forall_notMem fun v hv => ?_
  have hvT : v ∈ T := by
    simpa using (GM09.CyclicPerm.ofNodupList T hnd hne).interval_subset_bar _ _ hv
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvT
  have := (GM09.CyclicPerm.ofNodupList_mem_interval_swap_iff T hnd hne (i := 0)
    (k := T.length - 1) (by omega) (by omega) hj).mp hv
  omega

/-- Two vertices next to each other on `z L x` are consecutive in the cyclic order of
`x y z L`. -/
theorem isConsec_of_mem_zip_tail {x y z : V} {L : List V} (hnd : (x :: y :: z :: L).Nodup)
    (hne : x :: y :: z :: L ≠ []) {p : V × V}
    (h : p ∈ (z :: (L ++ [x])).zip (z :: (L ++ [x])).tail) :
    IsConsec (GM09.CyclicPerm.ofNodupList (x :: y :: z :: L) hnd hne) p.1 p.2 := by
  obtain ⟨u, w⟩ := p
  obtain ⟨i, hi, rfl, rfl⟩ := mem_zip_tail_iff.mp h
  simp only [List.length_cons, List.length_append, List.length_nil] at hi
  by_cases hiL : i < L.length
  · have e1 : (z :: (L ++ [x]))[i] = (x :: y :: z :: L)[i + 2]'(by simp; omega) := by
      rcases i with _ | i
      · rfl
      · simp [List.getElem_append_left (by omega : i < L.length)]
    have e2 : (z :: (L ++ [x]))[i + 1] = (x :: y :: z :: L)[i + 2 + 1]'(by simp; omega) := by
      simp [List.getElem_append_left hiL]
    rw [e1, e2]
    exact isConsec_succ hnd hne (by simp; omega)
  · have hi' : i = L.length := by omega
    subst hi'
    have e1 : (z :: (L ++ [x]))[L.length] =
        (x :: y :: z :: L)[(x :: y :: z :: L).length - 1]'(by simp) := by
      rcases L.eq_nil_or_concat with hL | ⟨L', l, rfl⟩
      · subst hL; rfl
      · simp
    have e2 : (z :: (L ++ [x]))[L.length + 1] = (x :: y :: z :: L)[0] := by simp
    rw [e1, e2]
    exact isConsec_last hnd hne (by simp)

/-- **Core edges of `P` with both ends at the ends of a crossing path.** Let `P ++ L` have no
repetition, let two vertices of `P` adjacent in `K` be consecutive on `P`, and let `a`, `b` sit at
positions `i₀`, `j₀` of `P ++ L` with `i₀ + 2 ≤ j₀`. Then `a` and `b` are not two adjacent vertices
of `P`. -/
theorem not_adj_ends_aux {K : SimpleGraph V} {P L : List V} (hnd : (P ++ L).Nodup)
    (hcore : ∀ (i j : ℕ) (hij : i < j) (hj : j < P.length), K.Adj (P[i]'(hij.trans hj)) P[j] →
      j = i + 1)
    {i₀ j₀ : ℕ} {a b : V} (ha : (P ++ L)[i₀]? = some a) (hb : (P ++ L)[j₀]? = some b)
    (hij : i₀ + 2 ≤ j₀) (haP : a ∈ P) (hbP : b ∈ P) (hab : K.Adj a b) : False := by
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp haP
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hbP
  rw [List.getElem?_eq_some_iff] at ha hb
  obtain ⟨hi₀, ha⟩ := ha
  obtain ⟨hj₀, hb⟩ := hb
  have ha' : (P ++ L)[i₀] = (P ++ L)[p]'(by simp; omega) := by
    rw [ha, List.getElem_append_left]
  have hb' : (P ++ L)[j₀] = (P ++ L)[q]'(by simp; omega) := by
    rw [hb, List.getElem_append_left]
  have e1 := hnd.getElem_inj_iff.mp ha'
  have e2 := hnd.getElem_inj_iff.mp hb'
  subst e1 e2
  have := hcore i₀ j₀ (by omega) hq hab
  omega

/-- The same with the two vertices given in either order. -/
theorem not_adj_ends {K : SimpleGraph V} {P L : List V} (hnd : (P ++ L).Nodup)
    (hcore : ∀ (i j : ℕ) (hij : i < j) (hj : j < P.length), K.Adj (P[i]'(hij.trans hj)) P[j] →
      j = i + 1)
    {i₀ j₀ : ℕ} {a b : V} (ha : (P ++ L)[i₀]? = some a) (hb : (P ++ L)[j₀]? = some b)
    (hij : i₀ + 2 ≤ j₀) {u w : V} (hu : u ∈ P) (hw : w ∈ P) (huw : K.Adj u w)
    (hu' : u = a ∨ u = b) (hw' : w = a ∨ w = b) : False := by
  rcases hu' with rfl | rfl <;> rcases hw' with rfl | rfl
  · exact huw.ne rfl
  · exact not_adj_ends_aux hnd hcore ha hb hij hu hw huw
  · exact not_adj_ends_aux hnd hcore ha hb hij hw hu huw.symm
  · exact huw.ne rfl

/-- A walk of `restrict G X` with both ends in `Z` gives a path of the core graph with the same
ends, on vertices of the walk that lie in `Z`. -/
theorem exists_corePath {Z X : Set V} {a b : V} (Q : (restrict G X).Walk a b) (ha : a ∈ Z)
    (hb : b ∈ Z) :
    ∃ q : (coreGraph G Z).Walk a b, q.IsPath ∧ ∀ t ∈ q.support, t ∈ Q.support ∧ t ∈ Z := by
  classical
  have hle : restrict G X ≤ G := fun _ _ h => h.1
  obtain ⟨q, hq⟩ := exists_coreWalk _ (Q.mapLe hle) le_rfl ha hb
  refine ⟨q.bypass, q.bypass_isPath, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hq t (q.support_bypass_subset_support ht)
  refine ⟨?_, h2⟩
  simpa [Walk.mapLe, Walk.support_map] using h1

namespace Case2

variable {S : Set V} {x y z ℓ : V} {L P : List V}

/-- **The gap of Lemma 4.3.** In the second case of the proof of Lemma 4.3, the cycle `P L` is
crossless in `G[𝒞 ∪ P]`. -/
theorem gap [Finite V] (hc : Case2 G S x y z ℓ L P) :
    ¬ IsCrossed (restrict G (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P})) (P ++ L) := by
  classical
  intro hcr
  set 𝒞 := compOf G S {v | v ∈ P} ℓ with h𝒞
  -- the society of the frame, its core `Z`, and the rural drawing of the core
  have hnd : (x :: y :: z :: L).Nodup := hc.cyc.2.1
  have hne : x :: y :: z :: L ≠ [] := List.cons_ne_nil _ _
  set Ω := GM09.CyclicPerm.ofNodupList (x :: y :: z :: L) hnd hne with hΩ
  have hbar : ∀ v, v ∈ Ω.bar → v ∈ x :: y :: z :: L := fun v h => by simpa [hΩ] using h
  have hnc : ¬ GM13.HasCross (cycleSociety G _ hnd hne) := fun h =>
    hc.max.2.1 (isCrossed_of_hasCross hnd hne h)
  obtain ⟨Kc, hK4⟩ := GM13.theorem_8_3_proof (cycleSociety G _ hnd hne)
  obtain ⟨Ω₀, h₀, -, hrur⟩ := (GM13.theorem_8_5_proof hK4).mp hnc
  set Z := Kc.vertexSet with hZ
  have hCZ : ∀ v ∈ x :: y :: z :: L, v ∈ Z := fun v hv =>
    hK4.isCore.isTrisecting.bar_subset hv
  have hatt : ∀ v, v ∉ Z → {w | ReachOut G Z v w}.ncard ≤ 3 := fun v hv =>
    (Set.ncard_le_ncard reachOut_subset (Set.toFinite _)).trans
      (hK4.isCore.isTrisecting.attach_ncard_le_three v ⟨Set.mem_univ v, hv⟩)
  have hPZ : ∀ v ∈ P, v ∈ Z := hc.mem_core hCZ hatt
  have hDZ : ∀ v ∈ P ++ L, v ∈ Z := fun v hv =>
    (List.mem_append.mp hv).elim (hPZ v) fun h => hCZ v (by simp [h])
  have h3 : 3 ≤ Ω.bar.ncard := by
    rw [hΩ, GM09.CyclicPerm.ofNodupList_bar]
    exact three_le_ncard hnd (by simp)
  obtain ⟨φ, F, hF, hU, hptF, hcons, hnon⟩ := exists_planeEmbedding hrur hK4.isCore.isSimple h3
    (coreGraph G Z) (fun u w h => core_adj_of_coreGraph_adj hK4.isCore h)
  -- the cycle `D = P L = x M z L`
  obtain ⟨M, hM⟩ := hc.mu.1.exists_middle (hc.mu.1.two_le_length hc.cyc)
  have eP : x :: (M ++ [z]) = P := by rw [hM]; rfl
  have eD : x :: (M ++ z :: L) = P ++ L := by rw [hM]; simp
  have hndD : (P ++ L).Nodup := hc.isCycleList_H.2.1
  have hD : IsCycleList (coreGraph G Z) (x :: (M ++ z :: L)) := by
    rw [eD]
    have h := hc.isCycleList_H
    exact ⟨h.1, h.2.1, fun p hp => coreGraph_adj_of_adj (h.2.2 p hp).1
      (hDZ _ (List.of_mem_zip hp).1) (hDZ _ (List.mem_rotate.mp (List.of_mem_zip hp).2))⟩
  -- the path `z L x` is drawn on `F`
  have hA : φ.pathImage (z :: (L ++ [x])) ⊆ F :=
    Set.iUnion₂_subset fun p hp => hcons p.1 p.2 (isConsec_of_mem_zip_tail hnd hne hp)
  -- the path `P` meets `F` only at `x` and `z`
  have hxz : ∀ u w, IsConsec Ω u w → u ∈ P → w ∈ P → False := by
    intro u w h hu hw
    obtain ⟨hub, hwb, hne', hint⟩ := h
    have hy : y ∈ Ω.interval x z :=
      GM09.CyclicPerm.ofNodupList_mem_interval_of_lt (x :: y :: z :: L) hnd hne (i := 0)
        (j := 1) (k := 2) (by omega) (by omega) (by simp)
    obtain ⟨m, hm, hℓm⟩ := List.mem_iff_getElem.mp hc.mem
    have hl : ℓ ∈ Ω.interval z x := by
      rw [← hℓm]
      exact GM09.CyclicPerm.ofNodupList_mem_interval_swap_of_lt_or_gt (x :: y :: z :: L) hnd
        hne (i := 0) (k := 2) (j := m + 3) (by omega) (by simp) (by simp; omega) (Or.inr (by omega))
    rcases hc.mu.1.2.2.2.2 u hu (hbar u hub) with hu' | hu' <;>
      rcases hc.mu.1.2.2.2.2 w hw (hbar w hwb) with hw' | hw' <;>
      rw [hu', hw'] at hne' hint
    · exact hne' rfl
    · rw [hint] at hy; exact hy
    · rw [hint] at hl; exact hl
    · exact hne' rfl
  have hγ : φ.pathImage (x :: (M ++ [z])) ∩ F ⊆ {φ.pt x, φ.pt z} := by
    rw [eP]
    rintro q ⟨hq, hqF⟩
    simp only [PlaneEmbedding.pathImage, Set.mem_iUnion] at hq
    obtain ⟨⟨u, w⟩, hp, hqL⟩ := hq
    have hadj : G.Adj u w := isChain_iff_zip.mp hc.mu.1.1 _ hp
    obtain ⟨i, hi, hu, hw⟩ := mem_zip_tail_iff.mp hp
    have huP : u ∈ P := hu ▸ List.getElem_mem _
    have hwP : w ∈ P := hw ▸ List.getElem_mem _
    have hK : (coreGraph G Z).Adj u w := coreGraph_adj_of_adj hadj (hPZ u huP) (hPZ w hwP)
    obtain ⟨v, hv, rfl⟩ := hnon u w hK (fun h => hxz u w h huP hwP)
      (fun h => hxz w u h hwP huP) ⟨hqL, hqF⟩
    have hvP : v ∈ P := by
      rcases hv with hv | hv <;> rw [hv]
      · exact huP
      · exact hwP
    rcases hc.mu.1.2.2.2.2 v hvP (hbar v (hptF v (hPZ v hvP) hqF)) with h | h <;> simp [h]
  -- the set `𝒦` of vertices of the component `𝒞` that lie in the core
  have hL𝒞 : ∀ v ∈ L, v ∈ 𝒞 := hc.mu.1.L_mem hc.cyc hc.sub hc.mem
  set 𝒦 : Set V := {v | v ∈ 𝒞 ∧ v ∈ Z} with h𝒦def
  have h𝒦P : ∀ v ∈ 𝒦, v ∉ x :: (M ++ [z]) := fun v hv => by rw [eP]; exact hc.K_not_mem hv.1
  have hℓ𝒦 : ℓ ∈ 𝒦 := ⟨Reachable.refl _, hCZ ℓ (by simp [hc.mem])⟩
  have h𝒦 : ∀ v ∈ 𝒦, ∃ q : (coreGraph G Z).Walk ℓ v, ∀ t ∈ q.support, t ∈ 𝒦 := by
    rintro v ⟨⟨W⟩, hvZ⟩
    obtain ⟨q, -, hq⟩ := exists_corePath W hℓ𝒦.2 hvZ
    exact ⟨q, fun t ht => ⟨⟨W.takeUntil t (hq t ht).1⟩, (hq t ht).2⟩⟩
  -- the crossing gives two paths of the core
  have hverts : ∀ {u w : V} (W : (restrict G (𝒞 ∪ {v | v ∈ P})).Walk u w), u ∈ P ++ L →
      ∀ t ∈ W.support, t ∈ Z → t ∈ 𝒦 ∨ t ∈ P := by
    intro u w W hu t ht htZ
    by_cases htu : t = u
    · rw [htu] at htZ ⊢
      rcases List.mem_append.mp hu with h | h
      · exact Or.inr h
      · exact Or.inl ⟨hL𝒞 u h, htZ⟩
    · rcases mem_of_mem_support_restrict W ht htu with h | h
      · exact Or.inl ⟨h, htZ⟩
      · exact Or.inr h
  have hcore : ∀ (i j : ℕ) (hij : i < j) (hj : j < P.length),
      (coreGraph G Z).Adj (P[i]'(hij.trans hj)) P[j] → j = i + 1 := fun i j hij hj h =>
    hc.core_adj_P hCZ hatt hij hj h
  have hedge : ∀ {u w : V} (W : (restrict G (𝒞 ∪ {v | v ∈ P})).Walk u w)
      (W' : (coreGraph G Z).Walk u w), IsTPath _ (P ++ L) W →
      (∀ t ∈ W'.support, t ∈ W.support ∧ t ∈ Z) → ∀ {i j : ℕ}, (P ++ L)[i]? = some u →
      (P ++ L)[j]? = some w → i + 2 ≤ j →
      ∀ p ∈ W'.support.zip W'.support.tail, p.1 ∈ 𝒦 ∨ p.2 ∈ 𝒦 := by
    intro u w W W' hW hW' i j hu hw hij p hp
    have hadj := isChain_iff_zip.mp W'.isChain_adj_support p hp
    have hp1 : p.1 ∈ W'.support := (List.of_mem_zip hp).1
    have hp2 : p.2 ∈ W'.support := List.mem_of_mem_tail (List.of_mem_zip hp).2
    by_contra hno
    rw [not_or] at hno
    have hp1P : p.1 ∈ P :=
      (hverts W hW.2.1 p.1 (hW' _ hp1).1 (hW' _ hp1).2).resolve_left hno.1
    have hp2P : p.2 ∈ P :=
      (hverts W hW.2.1 p.2 (hW' _ hp2).1 (hW' _ hp2).2).resolve_left hno.2
    have hend : ∀ t ∈ W'.support, t ∈ P → t = u ∨ t = w := fun t ht htP => by
      by_contra h
      rw [not_or] at h
      exact (hW.2.2.2 t (hW' t ht).1 h.1 h.2).1 (List.mem_append_left _ htP)
    exact not_adj_ends hndD hcore hu hw hij hp1P hp2P hadj (hend _ hp1 hp1P) (hend _ hp2 hp2P)
  obtain ⟨a, b, c, d, Q, R, ⟨i₀, r₀, j₀, s₀, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisj⟩ := hcr
  have hmem : ∀ {k : ℕ} {v : V}, (P ++ L)[k]? = some v → v ∈ Z := fun h =>
    hDZ _ (List.mem_of_getElem? h)
  obtain ⟨Q', hQ', hQs⟩ := exists_corePath Q (hmem hi) (hmem hj)
  obtain ⟨R', hR', hRs⟩ := exists_corePath R (hmem hr) (hmem hs)
  have hdisj' : Q'.support.Disjoint R'.support := fun t h1 h2 =>
    hdisj (hQs t h1).1 (hRs t h2).1
  have hidx : ∃ i r j s : ℕ, i < r ∧ r < j ∧ j < s ∧ (x :: (M ++ z :: L))[i]? = some a ∧
      (x :: (M ++ z :: L))[r]? = some c ∧ (x :: (M ++ z :: L))[j]? = some b ∧
      (x :: (M ++ z :: L))[s]? = some d := by
    rw [eD]
    exact ⟨i₀, r₀, j₀, s₀, hir, hrj, hjs, hi, hr, hj, hs⟩
  refine φ.plane_gap hF hU hD (fun v hv => hDZ v (eD ▸ hv)) hA hγ hc.mem (fun v hv => hv.2)
    h𝒦P hℓ𝒦 h𝒦 Q' R' hQ' hR' hdisj' hidx ?_ (hedge Q Q' hQ hQs hi hj (by omega)) ?_
    (hedge R R' hR hRs hr hs (by omega))
  · intro t ht
    rw [eP]
    exact hverts Q hQ.2.1 t (hQs t ht).1 (hQs t ht).2
  · intro t ht
    rw [eP]
    exact hverts R hR.2.1 t (hRs t ht).1 (hRs t ht).2

end Case2

end GraphMinor.HP25
