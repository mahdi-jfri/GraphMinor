module

public import GraphMinor.Crossing.BridgeLemma3
public import GraphMinor.Crossing.BridgeSweep
public import GraphMinor.HP25.Sec5Search

/-!
# `BridgeCross`: finding crossings in distinct cycle bridges (Section 5.2 of the note)

This file formalizes the procedure $\operatorname{BridgeCross}(K, D)$ of
`docs/crossing/crossing_extractor.tex`, Section 5.2:

"When an alternating pair of candidates of different colors is found, we make two searches. For a
component bridge with component \(A\) and selected endpoints \(p,q\), we search in
\(K[A\cup\{p,q\}]\). For a chord, we use its edge. The two searches may return arbitrary paths:
their inner vertices belong to different bridges, and the four selected endpoints are distinct.

We call this whole procedure \(\operatorname{BridgeCross}(K,D)\). It takes time \(O(n+m)\) and,
when it succeeds, two path searches."

## Main definitions and results

* `BridgeData V`: computable representation of a `D`-bridge (`.comp A` for an off-cycle component
  vertex list `A : List V`, or `.chord u v` for a chord with endpoints `u, v ∈ D`).
* `allBridgeData G verts D`: computes the deduplicated list of all `D`-bridges of `G` on `verts`.
* `BridgeData.findPath G bd p q`: constructs a `D`-path in `G` between `p` and `q` using `bd`
  (searching in `(G \ edge p q)` with allowed interior `A` for a component bridge `.comp A`, and
  using the single edge for a chord bridge `.chord u v`).
* `bridgeCross G verts D`: the full procedure $\operatorname{BridgeCross}(K, D)$.
* `bridgeCross_valid`, `bridgeCross_usesDistinctBridges`: soundness of `bridgeCross`.
* `bridgeCross_isSome_of_usesDistinctBridges`, `bridgeCross_isSome_iff`: completeness of
  `bridgeCross` for crossings using distinct cycle bridges.
* `bridgeCross_isSome_iff_isCrossed_of_planar`: completeness on planar inputs (given Lemma 4).
* `bridgeCrossSearches_le_two`, `length_allBridgeCandidates_le`, `bridgeCrossSteps_le`: step count
  and search count bounds.
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph GraphMinor.HP25

variable {V : Type*}

instance instDecidableIsCycleEdge [DecidableEq V] (C : List V) (x y : V) :
    Decidable (PlaneEmbedding.IsCycleEdge C x y) := by
  unfold PlaneEmbedding.IsCycleEdge
  infer_instance

/-! ### 1. Computable bridge data and attachment indices -/

/-- Computable representation of a `D`-bridge:
- `comp A`: an off-cycle component represented by its vertex list `A : List V`;
- `chord u v`: a chord with endpoints `u, v ∈ D`. -/
inductive BridgeData (V : Type*) where
  | comp (A : List V) : BridgeData V
  | chord (u v : V) : BridgeData V
  deriving DecidableEq, Repr

/-- Convert `BridgeData V` to its mathematical `Bridge V`. -/
def BridgeData.toBridge : BridgeData V → Bridge V
  | .comp A => .comp {x | x ∈ A}
  | .chord u v => .chord s(u, v)

/-- Boolean test for whether two `BridgeData V` represent the same `Bridge V`. -/
def BridgeData.sameBridge [DecidableEq V] : BridgeData V → BridgeData V → Bool
  | .comp A₁, .comp A₂ => A₁.all (fun x => decide (x ∈ A₂)) && A₂.all (fun x => decide (x ∈ A₁))
  | .chord u₁ v₁, .chord u₂ v₂ => decide (s(u₁, v₁) = s(u₂, v₂))
  | _, _ => false

theorem BridgeData.sameBridge_iff [DecidableEq V] (bd₁ bd₂ : BridgeData V) :
    bd₁.sameBridge bd₂ = true ↔ bd₁.toBridge = bd₂.toBridge := by
  cases bd₁ with
  | comp A₁ =>
    cases bd₂ with
    | comp A₂ =>
      simp only [sameBridge, toBridge, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
        Bridge.comp.injEq, Set.ext_iff]
      exact ⟨fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩, fun h => ⟨fun x => (h x).mp, fun x => (h x).mpr⟩⟩
    | chord u₂ v₂ =>
      simp [sameBridge, toBridge]
  | chord u₁ v₁ =>
    cases bd₂ with
    | comp A₂ =>
      simp [sameBridge, toBridge]
    | chord u₂ v₂ =>
      simp [sameBridge, toBridge]

/-- Boolean attachment test: whether vertex `v` is attached to bridge `bd` in `G`. -/
def BridgeData.attaches [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (bd : BridgeData V) (v : V) : Bool :=
  match bd with
  | .comp A => A.any (fun a => decide (G.Adj a v))
  | .chord u w => decide (v = u ∨ v = w)

theorem BridgeData.attaches_iff [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : List V} (bd : BridgeData V) {v : V} (hvD : v ∈ D) :
    bd.attaches G v = true ↔ IsBridgeAttachment G D bd.toBridge v := by
  cases bd with
  | comp A =>
    simp [attaches, toBridge, IsBridgeAttachment, hvD]
  | chord u w =>
    simp [attaches, toBridge, IsBridgeAttachment, hvD]

/-- Cyclic attachment index list in `0, ..., D.length - 1` of a bridge `bd`. -/
def BridgeData.attachmentIndices [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : List V) (bd : BridgeData V) : List ℕ :=
  (List.range D.length).filter (fun i =>
    match D[i]? with
    | some v => bd.attaches G v
    | none => false)

theorem BridgeData.pairwise_attachmentIndices [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : List V) (bd : BridgeData V) :
    (bd.attachmentIndices G D).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem BridgeData.mem_attachmentIndices_lt [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {D : List V} {bd : BridgeData V} {i : ℕ}
    (hi : i ∈ bd.attachmentIndices G D) : i < D.length :=
  List.mem_range.mp (List.mem_filter.mp hi).1

theorem BridgeData.attaches_of_mem_attachmentIndices [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {D : List V} {bd : BridgeData V} {i : ℕ}
    (hi : i ∈ bd.attachmentIndices G D) :
    bd.attaches G (D[i]'(bd.mem_attachmentIndices_lt G hi)) = true := by
  have hlt := bd.mem_attachmentIndices_lt G hi
  have hfilt := (List.mem_filter.mp hi).2
  rw [List.getElem?_eq_getElem hlt] at hfilt
  exact hfilt

theorem BridgeData.attachmentIndices_eq_map_idxOf [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {D : List V} (hnd : D.Nodup) (bd : BridgeData V) :
    bd.attachmentIndices G D = (D.filter (bd.attaches G)).map D.idxOf :=
  (map_idxOf_filter_eq_filter_range hnd (bd.attaches G)).symm

theorem BridgeData.attaches_congr [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {bd₁ bd₂ : BridgeData V} (heq : bd₁.toBridge = bd₂.toBridge) (v : V) :
    bd₁.attaches G v = bd₂.attaches G v := by
  have hiff : bd₁.attaches G v = true ↔ bd₂.attaches G v = true := by
    have hD : v ∈ ([v] : List V) := List.mem_singleton.mpr rfl
    rw [bd₁.attaches_iff G hD, bd₂.attaches_iff G hD, heq]
  exact Bool.eq_iff_iff.mpr hiff

/-! ### 2. Enumerating off-cycle components and chord bridges -/

instance [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (D : List V) :
    DecidableRel (offCycleGraph G D).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u ∉ D ∧ v ∉ D))

theorem walk_support_mem_offCycleComp {G : SimpleGraph V} {D : List V} {v₀ y z : V}
    (w : (offCycleGraph G D).Walk y z) (hy : y ∈ offCycleComp G D v₀) :
    ∀ x ∈ w.support, x ∈ offCycleComp G D v₀ := by
  induction w with
  | nil =>
    intro x hx
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ hy
  | @cons y' m z' h w' ih =>
    have hm : m ∈ offCycleComp G D v₀ :=
      ⟨h.2.2, hy.2.trans (Adj.reachable h)⟩
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hy
    · exact ih hm x hx

/-- Vertex list of the connected component of `v` in `G - V(D)` within `verts`. -/
def offCycleCompList [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) (v : V) : List V :=
  let off := verts.filter (fun x => decide (x ∉ D))
  off.filter (fun u => (findWalkIn (offCycleGraph G D) off v u).isSome)

theorem mem_offCycleCompList_iff [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts})
    {v : V} (hv : v ∈ verts) (hvD : v ∉ D) (u : V) :
    u ∈ offCycleCompList G verts D v ↔ u ∈ offCycleComp G D v := by
  unfold offCycleCompList
  set off := verts.filter (fun x => decide (x ∉ D))
  rw [List.mem_filter, mem_offCycleComp_iff]
  constructor
  · rintro ⟨hu_off, his⟩
    have huD : u ∉ D := of_decide_eq_true (List.mem_filter.mp hu_off).2
    obtain ⟨w, _⟩ := Option.isSome_iff_exists.mp his
    exact ⟨huD, ⟨w⟩⟩
  · rintro ⟨huD, ⟨w⟩⟩
    have hv_comp : v ∈ offCycleComp G D v := mem_offCycleComp_self hvD
    have hw_comp := walk_support_mem_offCycleComp w hv_comp
    have hsub_verts : offCycleComp G D v ⊆ {x | x ∈ verts} := offCycleComp_subset_supp hG hv
    have hw_off : ∀ x ∈ w.support, x ∈ off := by
      intro x hx
      have hx_comp := hw_comp x hx
      exact List.mem_filter.mpr ⟨hsub_verts hx_comp, decide_eq_true hx_comp.1⟩
    refine ⟨hw_off u w.end_mem_support, ?_⟩
    exact findWalkIn_isSome_of_walk (offCycleGraph G D) w (fun x hx _ _ => hw_off x hx)

theorem set_offCycleCompList_eq [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts})
    {v : V} (hv : v ∈ verts) (hvD : v ∉ D) :
    {u | u ∈ offCycleCompList G verts D v} = offCycleComp G D v := by
  ext u
  exact mem_offCycleCompList_iff G hG hv hvD u

/-- Raw list of component bridges of `G` on `verts` outside `D`. -/
def rawCompBridgeData [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) : List (BridgeData V) :=
  (verts.filter (fun v => decide (v ∉ D))).map (fun v =>
    BridgeData.comp (offCycleCompList G verts D v))

/-- Raw list of chord bridges of `D` in `G`. -/
def rawChordBridgeData [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : List V) : List (BridgeData V) :=
  (List.range D.length).flatMap (fun i =>
    (List.range D.length).filterMap (fun j =>
      if hi : i < D.length then
        if hj : j < D.length then
          if i < j ∧ G.Adj D[i] D[j] ∧ ¬ PlaneEmbedding.IsCycleEdge D D[i] D[j] then
            some (BridgeData.chord D[i] D[j])
          else none
        else none
      else none))

/-- Deduplicated list of all `D`-bridges of `G` on `verts`. -/
def allBridgeData [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) : List (BridgeData V) :=
  (rawCompBridgeData G verts D ++ rawChordBridgeData G D).pwFilter
    (fun b₁ b₂ => !b₁.sameBridge b₂)

theorem allBridgeData_sublist [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) :
    (allBridgeData G verts D).Sublist (rawCompBridgeData G verts D ++ rawChordBridgeData G D) :=
  List.pwFilter_sublist _

/-- Distinct entries in `allBridgeData G verts D` represent distinct bridges. -/
theorem allBridgeData_pairwise_ne [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) :
    (allBridgeData G verts D).Pairwise (fun b₁ b₂ => b₁.toBridge ≠ b₂.toBridge) := by
  have hpw := List.pairwise_pwFilter (R := fun b₁ b₂ : BridgeData V => !b₁.sameBridge b₂ = true)
    (rawCompBridgeData G verts D ++ rawChordBridgeData G D)
  refine hpw.imp ?_
  intro b₁ b₂ hne heq
  rw [← BridgeData.sameBridge_iff] at heq
  simp [heq] at hne

theorem allBridgeData_toBridge_ne_of_ne [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) {γ₁ γ₂ : ℕ}
    (h₁ : γ₁ < (allBridgeData G verts D).length)
    (h₂ : γ₂ < (allBridgeData G verts D).length) (hne : γ₁ ≠ γ₂) :
    ((allBridgeData G verts D)[γ₁]'h₁).toBridge ≠
      ((allBridgeData G verts D)[γ₂]'h₂).toBridge := by
  have hpw := List.pairwise_iff_getElem.mp (allBridgeData_pairwise_ne G verts D)
  rcases lt_trichotomy γ₁ γ₂ with hlt | rfl | hgt
  · exact hpw γ₁ γ₂ h₁ h₂ hlt
  · exact absurd rfl hne
  · exact (hpw γ₂ γ₁ h₂ h₁ hgt).symm

/-- Every entry `bd ∈ allBridgeData G verts D` represents a valid `D`-bridge, and if `bd = .comp A`,
every vertex of `A` avoids `D`. -/
theorem isBridge_of_mem_allBridgeData [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts})
    {bd : BridgeData V} (hbd : bd ∈ allBridgeData G verts D) :
    IsBridge G {x | x ∈ verts} D bd.toBridge ∧
      (∀ A, bd = BridgeData.comp A → ∀ x ∈ A, x ∉ D) := by
  have hmem := (allBridgeData_sublist G verts D).subset hbd
  rcases List.mem_append.mp hmem with hcomp | hchord
  · rw [rawCompBridgeData, List.mem_map] at hcomp
    obtain ⟨v, hv_filt, rfl⟩ := hcomp
    have hv_verts : v ∈ verts := (List.mem_filter.mp hv_filt).1
    have hv_not_D : v ∉ D := of_decide_eq_true (List.mem_filter.mp hv_filt).2
    refine ⟨?_, ?_⟩
    · simp only [BridgeData.toBridge, IsBridge, IsOffCycleComp]
      exact ⟨v, hv_verts, hv_not_D, set_offCycleCompList_eq G hG hv_verts hv_not_D⟩
    · intro A hA x hx
      cases hA
      have hx_off : x ∈ verts.filter (fun y => decide (y ∉ D)) := (List.mem_filter.mp hx).1
      exact of_decide_eq_true (List.mem_filter.mp hx_off).2
  · simp only [rawChordBridgeData, List.mem_flatMap, List.mem_range, List.mem_filterMap] at hchord
    obtain ⟨i, hi, j, hj, hsome⟩ := hchord
    simp only [hi, hj, ↓reduceDIte] at hsome
    split_ifs at hsome with hcond
    simp only [Option.some.injEq] at hsome
    subst hsome
    refine ⟨?_, fun A hA => by cases hA⟩
    simp only [BridgeData.toBridge, IsBridge, IsChordBridge]
    exact ⟨D[i], D[j], rfl, List.getElem_mem hi, List.getElem_mem hj, hcond.2.1, hcond.2.2⟩

/-- Helper for `pwFilter`: for every `x ∈ L`, there is some `y ∈ L.pwFilter R` with `¬ R y x` or
`y = x`. -/
theorem exists_mem_pwFilter_sameBridge [DecidableEq V] (L : List (BridgeData V))
    {bd : BridgeData V} (hbd : bd ∈ L) :
    ∃ bd' ∈ L.pwFilter (fun b₁ b₂ => !b₁.sameBridge b₂), bd'.toBridge = bd.toBridge := by
  induction L with
  | nil => cases hbd
  | cons hd tl ih =>
    rw [List.pwFilter, List.foldr_cons, ← List.pwFilter]
    rcases List.mem_cons.mp hbd with rfl | htl
    · split_ifs with hall
      · exact ⟨bd, List.mem_cons_self, rfl⟩
      · simp only [not_forall] at hall
        obtain ⟨bd', hbd'_mem, hnot⟩ := hall
        have hsame : bd.sameBridge bd' = true := by simpa using hnot
        exact ⟨bd', hbd'_mem, ((BridgeData.sameBridge_iff bd bd').mp hsame).symm⟩
    · obtain ⟨bd', hbd'_mem, heq⟩ := ih htl
      split_ifs
      · exact ⟨bd', List.mem_cons_of_mem hd hbd'_mem, heq⟩
      · exact ⟨bd', hbd'_mem, heq⟩

/-- Completeness of `allBridgeData`: every valid `D`-bridge `B` of `G` on `verts` appears in
`allBridgeData G verts D` at some index `γ`. -/
theorem exists_index_allBridgeData_of_isBridge [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts})
    {B : Bridge V} (hB : IsBridge G {x | x ∈ verts} D B) :
    ∃ (γ : ℕ) (hγ : γ < (allBridgeData G verts D).length),
      ((allBridgeData G verts D)[γ]'hγ).toBridge = B := by
  suffices hraw : ∃ bd ∈ rawCompBridgeData G verts D ++ rawChordBridgeData G D,
      bd.toBridge = B by
    obtain ⟨bd, hbd_mem, hbd_eq⟩ := hraw
    obtain ⟨bd', hbd'_mem, hbd'_eq⟩ := exists_mem_pwFilter_sameBridge _ hbd_mem
    obtain ⟨γ, hγ, rfl⟩ := List.getElem_of_mem hbd'_mem
    exact ⟨γ, hγ, hbd'_eq.trans hbd_eq⟩
  cases B with
  | comp A =>
    obtain ⟨v, hv_verts, hv_not_D, rfl⟩ := hB
    refine ⟨BridgeData.comp (offCycleCompList G verts D v), ?_, ?_⟩
    · apply List.mem_append_left
      rw [rawCompBridgeData, List.mem_map]
      exact ⟨v, List.mem_filter.mpr ⟨hv_verts, decide_eq_true hv_not_D⟩, rfl⟩
    · simp only [BridgeData.toBridge, Bridge.comp.injEq]
      exact set_offCycleCompList_eq G hG hv_verts hv_not_D
  | chord e =>
    obtain ⟨u, v, rfl, huD, hvD, hadj, hnot_cyc⟩ := hB
    have huv : u ≠ v := G.ne_of_adj hadj
    obtain ⟨i₀, hi₀, rfl⟩ := List.getElem_of_mem huD
    obtain ⟨j₀, hj₀, rfl⟩ := List.getElem_of_mem hvD
    have hij_ne : i₀ ≠ j₀ := fun h => huv (by subst h; rfl)
    rcases lt_trichotomy i₀ j₀ with hlt | rfl | hgt
    · refine ⟨BridgeData.chord D[i₀] D[j₀], ?_, rfl⟩
      apply List.mem_append_right
      simp only [rawChordBridgeData, List.mem_flatMap, List.mem_range, List.mem_filterMap]
      refine ⟨i₀, hi₀, j₀, hj₀, ?_⟩
      have hcond : i₀ < j₀ ∧ G.Adj D[i₀] D[j₀] ∧ ¬ PlaneEmbedding.IsCycleEdge D D[i₀] D[j₀] :=
        ⟨hlt, hadj, hnot_cyc⟩
      simp [hi₀, hj₀, hcond]
    · exact absurd rfl hij_ne
    · refine ⟨BridgeData.chord D[j₀] D[i₀], ?_, ?_⟩
      · apply List.mem_append_right
        simp only [rawChordBridgeData, List.mem_flatMap, List.mem_range, List.mem_filterMap]
        refine ⟨j₀, hj₀, i₀, hi₀, ?_⟩
        have hnot_cyc' : ¬ PlaneEmbedding.IsCycleEdge D D[j₀] D[i₀] := by
          unfold PlaneEmbedding.IsCycleEdge
          rw [Sym2.eq_swap]
          exact hnot_cyc
        have hcond : j₀ < i₀ ∧ G.Adj D[j₀] D[i₀] ∧ ¬ PlaneEmbedding.IsCycleEdge D D[j₀] D[i₀] :=
          ⟨hgt, hadj.symm, hnot_cyc'⟩
        simp [hj₀, hi₀, hcond]
      · simp [BridgeData.toBridge, Sym2.eq_swap]

/-! ### 3. Path construction in a single bridge (`BridgeData.findPath`) -/

/-- Construct a `D`-path in `G` from `p` to `q` using the bridge `bd`
(`docs/crossing/crossing_extractor.tex`, Section 5.2):
"For a component bridge with component \(A\) and selected endpoints \(p,q\), we search in
\(K[A\cup\{p,q\}]\). For a chord, we use its edge." -/
def BridgeData.findPath [DecidableEq V] [WalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (bd : BridgeData V) (p q : V) : Option (G.Walk p q) :=
  match bd with
  | .comp A =>
    match WalkSearch.find (G \ edge p q) A p q with
    | some w => some (w.mapLe sdiff_le)
    | none => none
  | .chord _ _ =>
    if h : G.Adj p q then
      some (Walk.cons h Walk.nil)
    else
      none

/-- Number of calls to `WalkSearch.find` made by `BridgeData.findPath`. -/
def BridgeData.findPathSearches : BridgeData V → ℕ
  | .comp _ => 1
  | .chord _ _ => 0

theorem BridgeData.findPathSearches_le_one (bd : BridgeData V) :
    bd.findPathSearches ≤ 1 := by
  cases bd <;> simp [findPathSearches]

theorem offCycleGraph_le_sdiff_edge (G : SimpleGraph V) {D : List V} {p q : V} (hp : p ∈ D) :
    offCycleGraph G D ≤ G \ edge p q := by
  intro x y ⟨hadj, hxD, hyD⟩
  rw [sdiff_adj, edge_adj]
  refine ⟨hadj, ?_⟩
  rintro ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
  · exact hxD hp
  · exact hyD hp

@[simp]
theorem walk_support_mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} (w : G.Walk u v) :
    (w.mapLe h).support = w.support := by
  simp [Walk.mapLe]

/-- Soundness of `BridgeData.findPath`: any walk `P` returned by `bd.findPath G p q` for distinct
attachments `p, q ∈ D` of `bd ∈ allBridgeData G verts D` is a `D`-path using `bd.toBridge`. -/
theorem BridgeData.findPath_sound [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts})
    {bd : BridgeData V} (hbd : bd ∈ allBridgeData G verts D)
    {p q : V} (hpD : p ∈ D) (hqD : q ∈ D) (hpq : p ≠ q)
    (hp_att : bd.attaches G p = true) (hq_att : bd.attaches G q = true)
    {P : G.Walk p q} (hfind : bd.findPath G p q = some P) :
    IsTPath G D P ∧ UsesBridge G P bd.toBridge := by
  have hbd_info := isBridge_of_mem_allBridgeData G hG hbd
  cases bd with
  | comp A =>
    simp only [findPath] at hfind
    cases hw : WalkSearch.find (G \ edge p q) A p q with
    | none => simp [hw] at hfind
    | some w =>
      rw [hw] at hfind
      simp only [Option.some.injEq] at hfind
      subst hfind
      have hws := LawfulWalkSearch.isWalkSearch (G \ edge p q)
      have hw_path : w.IsPath := hws.isPath hw
      have hw_supp := hws.support_subset hw
      have hP_path : (w.mapLe sdiff_le).IsPath := hw_path.mapLe sdiff_le
      have hA_not_D : ∀ x ∈ A, x ∉ D := hbd_info.2 A rfl
      have hinner_A : ∀ x ∈ (w.mapLe sdiff_le).support, x ≠ p → x ≠ q → x ∈ A := by
        intro x hx hxp hxq
        rw [walk_support_mapLe] at hx
        exact (hw_supp x hx).resolve_left hxp |>.resolve_left hxq
      have hTPath : IsTPath G D (w.mapLe sdiff_le) := by
        refine ⟨hP_path, hpD, hqD, fun x hx hxp hxq => ?_⟩
        have hxA := hinner_A x hx hxp hxq
        exact ⟨hA_not_D x hxA, hA_not_D x hxA⟩
      have hex_inner : ∃ x ∈ (w.mapLe sdiff_le).support, x ≠ p ∧ x ≠ q := by
        rw [walk_support_mapLe]
        cases hw_eq : w with
        | nil => exact absurd rfl hpq
        | @cons _ mid _ hadj₁ w' =>
          cases hw'_eq : w' with
          | nil =>
            exfalso
            rw [sdiff_adj, edge_adj] at hadj₁
            exact hadj₁.2 ⟨Or.inl ⟨rfl, rfl⟩, hpq⟩
          | @cons _ mid₂ _ hadj₂ w'' =>
            have hmid_ne_p : mid ≠ p := ((G \ edge p q).ne_of_adj hadj₁).symm
            have hmid_ne_q : mid ≠ q := by
              intro hmq
              subst hmq
              rw [hw_eq, hw'_eq] at hw_path
              have hnd := hw_path.support_nodup
              simp only [Walk.support_cons, List.nodup_cons] at hnd
              exact hnd.2.1 w''.end_mem_support
            exact ⟨mid, by simp, hmid_ne_p, hmid_ne_q⟩
      exact ⟨hTPath, hex_inner, fun x hx hxp hxq => hinner_A x hx hxp hxq⟩
  | chord u v =>
    simp only [findPath] at hfind
    split_ifs at hfind with hadj
    simp only [Option.some.injEq] at hfind
    subst hfind
    have hp_uv : p = u ∨ p = v := of_decide_eq_true hp_att
    have hq_uv : q = u ∨ q = v := of_decide_eq_true hq_att
    have hsym : s(u, v) = s(p, q) := by
      rcases hp_uv with rfl | rfl <;> rcases hq_uv with rfl | rfl
      · exact absurd rfl hpq
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hpq
    have hpath : (Walk.cons hadj Walk.nil).IsPath :=
      Walk.IsPath.nil.cons (by simp [hpq])
    refine ⟨⟨hpath, hpD, hqD, ?_⟩, ?_, hsym⟩
    · intro x hx hxp hxq
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl
      · exact absurd rfl hxp
      · exact absurd rfl hxq
    · intro x hx
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      exact hx

/-- Completeness of `BridgeData.findPath`: for distinct attachments `p, q ∈ D` of
`bd ∈ allBridgeData G verts D`, `bd.findPath G p q` returns `some` walk. -/
theorem BridgeData.findPath_isSome [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts})
    {bd : BridgeData V} (hbd : bd ∈ allBridgeData G verts D)
    {p q : V} (hpD : p ∈ D) (hqD : q ∈ D) (hpq : p ≠ q)
    (hp_att : bd.attaches G p = true) (hq_att : bd.attaches G q = true) :
    (bd.findPath G p q).isSome = true := by
  have hbd_info := isBridge_of_mem_allBridgeData G hG hbd
  cases bd with
  | comp A =>
    simp only [findPath]
    have hA_not_D : ∀ x ∈ A, x ∉ D := hbd_info.2 A rfl
    obtain ⟨v₀, hv₀_verts, hv₀_not_D, hA_eq⟩ := hbd_info.1
    have hmem_A_iff : ∀ x, x ∈ A ↔ x ∈ offCycleComp G D v₀ := by
      intro x
      change x ∈ {y | y ∈ A} ↔ x ∈ offCycleComp G D v₀
      rw [hA_eq]
    simp only [attaches, List.any_eq_true, decide_eq_true_eq] at hp_att hq_att
    obtain ⟨a, haA, hadj_ap⟩ := hp_att
    obtain ⟨b, hbA, hadj_bq⟩ := hq_att
    have ha_comp : a ∈ offCycleComp G D v₀ := (hmem_A_iff a).mp haA
    have hb_comp : b ∈ offCycleComp G D v₀ := (hmem_A_iff b).mp hbA
    obtain ⟨w₀⟩ : (offCycleGraph G D).Reachable a b := ha_comp.2.symm.trans hb_comp.2
    have hw₀_in_A : ∀ x ∈ w₀.support, x ∈ A :=
      fun x hx => (hmem_A_iff x).mpr (walk_support_mem_offCycleComp w₀ ha_comp x hx)
    set w₁ : (G \ edge p q).Walk a b := w₀.mapLe (offCycleGraph_le_sdiff_edge G hpD)
    have hp_a : (G \ edge p q).Adj p a := by
      rw [sdiff_adj, edge_adj]
      refine ⟨hadj_ap.symm, ?_⟩
      rintro ⟨⟨_, rfl⟩ | ⟨_, rfl⟩, _⟩
      · exact hA_not_D a haA hqD
      · exact hA_not_D a haA hpD
    have hq_b : (G \ edge p q).Adj b q := by
      rw [sdiff_adj, edge_adj]
      refine ⟨hadj_bq, ?_⟩
      rintro ⟨⟨rfl, _⟩ | ⟨rfl, _⟩, _⟩
      · exact hA_not_D b hbA hpD
      · exact hA_not_D b hbA hqD
    set W : (G \ edge p q).Walk p q := Walk.cons hp_a (w₁.concat hq_b)
    have hW_inner : ∀ x ∈ W.support, x ≠ p → x ≠ q → x ∈ A := by
      intro x hx hxp hxq
      simp only [W, w₁, Walk.support_cons, Walk.support_concat, walk_support_mapLe,
        List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx_w₀ | rfl
      · exact absurd rfl hxp
      · exact hw₀_in_A x hx_w₀
      · exact absurd rfl hxq
    have hisSome :=
      (LawfulWalkSearch.isWalkSearch (G \ edge p q)).isSome_of_walk W hW_inner
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hisSome
    simp [hw]
  | chord u v =>
    obtain ⟨u', v', heq, _, _, hadj_u'v', _⟩ := hbd_info.1
    have hp_uv : p = u ∨ p = v := of_decide_eq_true hp_att
    have hq_uv : q = u ∨ q = v := of_decide_eq_true hq_att
    have hsym : s(p, q) = s(u, v) := by
      rcases hp_uv with rfl | rfl <;> rcases hq_uv with rfl | rfl
      · exact absurd rfl hpq
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hpq
    have hadj_pq : G.Adj p q := by
      have hsym' : s(p, q) = s(u', v') := hsym.trans heq
      rcases Sym2.eq_iff.mp hsym' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj_u'v'
      · exact hadj_u'v'.symm
    simp [findPath, hadj_pq]

/-! ### 4. The `bridgeCross` procedure and its correctness -/

/-- All candidates across all bridges in `bridges : List (BridgeData V)`, indexed by bridge color
`γ < bridges.length`. -/
def allBridgeCandidates [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : List V) (bridges : List (BridgeData V)) : List Candidate :=
  (List.range bridges.length).flatMap (fun γ =>
    match bridges[γ]? with
    | some bd => candidatesOfIndices γ (bd.attachmentIndices G D)
    | none => [])

theorem mem_allBridgeCandidates_iff [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : List V} {bridges : List (BridgeData V)} {I : Candidate} :
    I ∈ allBridgeCandidates G D bridges ↔
      ∃ (γ : ℕ) (hγ : γ < bridges.length),
        I ∈ candidatesOfIndices γ ((bridges[γ]'hγ).attachmentIndices G D) := by
  unfold allBridgeCandidates
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨γ, hγ, hmem⟩
    rw [List.getElem?_eq_getElem hγ] at hmem
    exact ⟨γ, hγ, hmem⟩
  · rintro ⟨γ, hγ, hmem⟩
    refine ⟨γ, hγ, ?_⟩
    rw [List.getElem?_eq_getElem hγ]
    exact hmem

theorem mem_allBridgeCandidates_spec [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : List V} {bridges : List (BridgeData V)} {I : Candidate}
    (hI : I ∈ allBridgeCandidates G D bridges) :
    ∃ (hγ : I.γ < bridges.length),
      I.l < I.r ∧ I.r < D.length ∧
      I.l ∈ (bridges[I.γ]'hγ).attachmentIndices G D ∧
      I.r ∈ (bridges[I.γ]'hγ).attachmentIndices G D := by
  obtain ⟨γ, hγ, hmem⟩ := (mem_allBridgeCandidates_iff G).mp hI
  obtain ⟨hlr, hγ_eq, hl_mem, hr_mem⟩ := mem_candidatesOfIndices_lt hmem
  rcases I with ⟨l, r, γ'⟩
  dsimp only at hlr hγ_eq hl_mem hr_mem ⊢
  subst hγ_eq
  exact ⟨hγ, hlr, (bridges[γ']'hγ).mem_attachmentIndices_lt G hr_mem, hl_mem, hr_mem⟩

/-- The procedure `BridgeCross(K, D)` of `docs/crossing/crossing_extractor.tex`, Section 5.2:
"We call this whole procedure \(\operatorname{BridgeCross}(K,D)\). It takes time \(O(n+m)\) and,
when it succeeds, two path searches." -/
def bridgeCross [DecidableEq V] [WalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) : Option (CrossingWalks G D) :=
  let bridges := allBridgeData G verts D
  let cs := allBridgeCandidates G D bridges
  let sorted := sortCandidates D.length cs
  match sweepCandidates sorted with
  | none => none
  | some (I₁, I₂) =>
    if h₁ : I₁.l < D.length ∧ I₁.r < D.length then
      if h₂ : I₂.l < D.length ∧ I₂.r < D.length then
        match bridges[I₁.γ]?, bridges[I₂.γ]? with
        | some bd₁, some bd₂ =>
          let u₁ := D[I₁.l]'h₁.1
          let v₁ := D[I₁.r]'h₁.2
          let u₂ := D[I₂.l]'h₂.1
          let v₂ := D[I₂.r]'h₂.2
          match bd₁.findPath G u₁ v₁, bd₂.findPath G u₂ v₂ with
          | some Q, some R => some ⟨u₁, v₁, u₂, v₂, Q, R⟩
          | _, _ => none
        | _, _ => none
      else none
    else none

/-- Soundness of `bridgeCross`: if `bridgeCross G verts D = some cr`, then `cr` is a valid crossing
of `D` in `G` and its two paths use distinct `D`-bridges. -/
theorem bridgeCross_valid_and_usesDistinctBridges [DecidableEq V] [WalkSearch V]
    [LawfulWalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts}) (hD : D.Nodup)
    {cr : CrossingWalks G D} (heq : bridgeCross G verts D = some cr) :
    cr.Valid ∧ UsesDistinctBridges G {x | x ∈ verts} D cr.Q cr.R := by
  unfold bridgeCross at heq
  dsimp only at heq
  set bridges := allBridgeData G verts D
  set cs := allBridgeCandidates G D bridges
  set sorted := sortCandidates D.length cs
  have hcs_lt : ∀ I ∈ cs, I.l < D.length ∧ I.r < D.length := by
    intro I hI
    obtain ⟨_, hl_r, hr_lt, _, _⟩ := mem_allBridgeCandidates_spec G hI
    exact ⟨lt_trans hl_r hr_lt, hr_lt⟩
  have hperm : sorted.Perm cs := sortCandidates_perm hcs_lt
  have hpw : sorted.Pairwise CandidateOrder := sortCandidates_pairwise hcs_lt
  cases hsweep : sweepCandidates sorted with
  | none =>
    rw [hsweep] at heq
    simp at heq
  | some pair =>
    rcases pair with ⟨I₁, I₂⟩
    rw [hsweep] at heq
    obtain ⟨hI₁_sorted, hI₂_sorted, hinter⟩ := sweepCandidates_sound hpw hsweep
    have hI₁_cs : I₁ ∈ cs := hperm.subset hI₁_sorted
    have hI₂_cs : I₂ ∈ cs := hperm.subset hI₂_sorted
    obtain ⟨hγ₁, hI₁_lr, hI₁_r, hI₁_l_att, hI₁_r_att⟩ := mem_allBridgeCandidates_spec G hI₁_cs
    obtain ⟨hγ₂, hI₂_lr, hI₂_r, hI₂_l_att, hI₂_r_att⟩ := mem_allBridgeCandidates_spec G hI₂_cs
    have h₁ : I₁.l < D.length ∧ I₁.r < D.length := ⟨lt_trans hI₁_lr hI₁_r, hI₁_r⟩
    have h₂ : I₂.l < D.length ∧ I₂.r < D.length := ⟨lt_trans hI₂_lr hI₂_r, hI₂_r⟩
    simp only [h₁, h₂, and_self, ↓reduceDIte] at heq
    have hget₁ : bridges[I₁.γ]? = some (bridges[I₁.γ]'hγ₁) := List.getElem?_eq_getElem hγ₁
    have hget₂ : bridges[I₂.γ]? = some (bridges[I₂.γ]'hγ₂) := List.getElem?_eq_getElem hγ₂
    rw [hget₁, hget₂] at heq
    dsimp only at heq
    set bd₁ := bridges[I₁.γ]'hγ₁
    set bd₂ := bridges[I₂.γ]'hγ₂
    set u₁ := D[I₁.l]'h₁.1
    set v₁ := D[I₁.r]'h₁.2
    set u₂ := D[I₂.l]'h₂.1
    set v₂ := D[I₂.r]'h₂.2
    cases hfind₁ : bd₁.findPath G u₁ v₁ with
    | none =>
      rw [hfind₁] at heq
      simp at heq
    | some Q =>
      cases hfind₂ : bd₂.findPath G u₂ v₂ with
      | none =>
        rw [hfind₁, hfind₂] at heq
        simp at heq
      | some R =>
        rw [hfind₁, hfind₂] at heq
        simp only [Option.some.injEq] at heq
        subst heq
        rcases hinter with ⟨hγ_ne, hl₁_l₂, hl₂_r₁, hr₁_r₂⟩
        have hne_idx : ∀ {i j : ℕ} (hi : i < D.length) (hj : j < D.length),
            i ≠ j → D[i]'hi ≠ D[j]'hj :=
          fun _ _ hne h => hne (hD.getElem_inj_iff.mp h)
        have hu₁v₁ : u₁ ≠ v₁ := hne_idx h₁.1 h₁.2 (by omega)
        have hu₂v₂ : u₂ ≠ v₂ := hne_idx h₂.1 h₂.2 (by omega)
        have hu₁_att : bd₁.attaches G u₁ = true :=
          bd₁.attaches_of_mem_attachmentIndices G hI₁_l_att
        have hv₁_att : bd₁.attaches G v₁ = true :=
          bd₁.attaches_of_mem_attachmentIndices G hI₁_r_att
        have hu₂_att : bd₂.attaches G u₂ = true :=
          bd₂.attaches_of_mem_attachmentIndices G hI₂_l_att
        have hv₂_att : bd₂.attaches G v₂ = true :=
          bd₂.attaches_of_mem_attachmentIndices G hI₂_r_att
        have hQ_sound := bd₁.findPath_sound G hG (List.getElem_mem hγ₁)
          (List.getElem_mem h₁.1) (List.getElem_mem h₁.2) hu₁v₁ hu₁_att hv₁_att hfind₁
        have hR_sound := bd₂.findPath_sound G hG (List.getElem_mem hγ₂)
          (List.getElem_mem h₂.1) (List.getElem_mem h₂.2) hu₂v₂ hu₂_att hv₂_att hfind₂
        have hB₁ : IsBridge G {x | x ∈ verts} D bd₁.toBridge :=
          (isBridge_of_mem_allBridgeData G hG (List.getElem_mem hγ₁)).1
        have hB₂ : IsBridge G {x | x ∈ verts} D bd₂.toBridge :=
          (isBridge_of_mem_allBridgeData G hG (List.getElem_mem hγ₂)).1
        have hB_ne : bd₁.toBridge ≠ bd₂.toBridge :=
          allBridgeData_toBridge_ne_of_ne G verts D hγ₁ hγ₂ hγ_ne
        have hdist : UsesDistinctBridges G {x | x ∈ verts} D Q R :=
          ⟨bd₁.toBridge, bd₂.toBridge, hB₁, hB₂, hB_ne, hQ_sound.2, hR_sound.2⟩
        have hdisj : Q.support.Disjoint R.support := by
          refine disjoint_support_of_usesDistinctBridges hB₁ hB₂ hB_ne hQ_sound.2 hR_sound.2
            (List.getElem_mem h₁.1) (List.getElem_mem h₁.2)
            (List.getElem_mem h₂.1) (List.getElem_mem h₂.2) ?_
          intro x hx₁ hx₂
          rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h
          · exact hne_idx h₁.1 h₂.1 (by omega) h
          · exact hne_idx h₁.1 h₂.2 (by omega) h
          · exact hne_idx h₁.2 h₂.1 (by omega) h
          · exact hne_idx h₁.2 h₂.2 (by omega) h
        have hvalid : IsCrossing G D Q R := by
          refine ⟨⟨I₁.l, I₂.l, I₁.r, I₂.r, hl₁_l₂, hl₂_r₁, hr₁_r₂,
            List.getElem?_eq_getElem h₁.1, List.getElem?_eq_getElem h₂.1,
            List.getElem?_eq_getElem h₁.2, List.getElem?_eq_getElem h₂.2⟩,
            hQ_sound.1, hR_sound.1, hdisj⟩
        exact ⟨hvalid, hdist⟩

/-- Soundness of `bridgeCross` (validity of the returned crossing). -/
theorem bridgeCross_valid [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts}) (hD : D.Nodup)
    {cr : CrossingWalks G D} (heq : bridgeCross G verts D = some cr) :
    cr.Valid :=
  (bridgeCross_valid_and_usesDistinctBridges G hG hD heq).1

/-- Soundness of `bridgeCross` (the two paths of the returned crossing use distinct bridges). -/
theorem bridgeCross_usesDistinctBridges [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts}) (hD : D.Nodup)
    {cr : CrossingWalks G D} (heq : bridgeCross G verts D = some cr) :
    UsesDistinctBridges G {x | x ∈ verts} D cr.Q cr.R :=
  (bridgeCross_valid_and_usesDistinctBridges G hG hD heq).2

/-- Completeness of `bridgeCross`: if there exists a crossing `(Q, R)` of `D` in `G` whose two paths
use distinct `D`-bridges, then `bridgeCross G verts D` returns `some` crossing. -/
theorem bridgeCross_isSome_of_usesDistinctBridges [DecidableEq V] [WalkSearch V]
    [LawfulWalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts}) (hD : D.Nodup)
    {u₁ v₁ u₂ v₂ : V} {Q : G.Walk u₁ v₁} {R : G.Walk u₂ v₂}
    (hcr : IsCrossing G D Q R)
    (hdist : UsesDistinctBridges G {x | x ∈ verts} D Q R) :
    (bridgeCross G verts D).isSome = true := by
  unfold bridgeCross
  dsimp only
  set bridges := allBridgeData G verts D
  set cs := allBridgeCandidates G D bridges
  set sorted := sortCandidates D.length cs
  have hcs_lt : ∀ I ∈ cs, I.l < D.length ∧ I.r < D.length := by
    intro I hI
    obtain ⟨_, hl_r, hr_lt, _, _⟩ := mem_allBridgeCandidates_spec G hI
    exact ⟨lt_trans hl_r hr_lt, hr_lt⟩
  have hperm : sorted.Perm cs := sortCandidates_perm hcs_lt
  have hpw : sorted.Pairwise CandidateOrder := sortCandidates_pairwise hcs_lt
  obtain ⟨B₁, B₂, hB₁, hB₂, hB_ne, hQ_B₁, hR_B₂⟩ := hdist
  obtain ⟨γ₁, hγ₁, hB₁_eq⟩ := exists_index_allBridgeData_of_isBridge G hG hB₁
  obtain ⟨γ₂, hγ₂, hB₂_eq⟩ := exists_index_allBridgeData_of_isBridge G hG hB₂
  have hγ_ne : γ₁ ≠ γ₂ := fun h => hB_ne (by subst h; exact hB₁_eq.symm.trans hB₂_eq)
  set bd₁ := bridges[γ₁]'hγ₁
  set bd₂ := bridges[γ₂]'hγ₂
  have hQ_path : IsTPath G D Q := hcr.2.1
  have hR_path : IsTPath G D R := hcr.2.2.1
  obtain ⟨hu₁v₁, hu₂v₂, hnot₁, hnot₂⟩ := IsCrossing.not_isCycleEdge_ends hD hcr
  obtain ⟨B₁', hB₁', hQ_B₁', hu₁_att', hv₁_att'⟩ := IsTPath.exists_bridge hG hQ_path hu₁v₁ hnot₁
  obtain ⟨B₂', hB₂', hR_B₂', hu₂_att', hv₂_att'⟩ := IsTPath.exists_bridge hG hR_path hu₂v₂ hnot₂
  have hB₁'_eq : B₁' = B₁ := UsesBridge.unique hB₁' hB₁ hQ_B₁' hQ_B₁
  have hB₂'_eq : B₂' = B₂ := UsesBridge.unique hB₂' hB₂ hR_B₂' hR_B₂
  have hu₁_att : bd₁.attaches G u₁ = true := by
    rw [bd₁.attaches_iff G hQ_path.2.1, hB₁_eq, ← hB₁'_eq]
    exact hu₁_att'
  have hv₁_att : bd₁.attaches G v₁ = true := by
    rw [bd₁.attaches_iff G hQ_path.2.2.1, hB₁_eq, ← hB₁'_eq]
    exact hv₁_att'
  have hu₂_att : bd₂.attaches G u₂ = true := by
    rw [bd₂.attaches_iff G hR_path.2.1, hB₂_eq, ← hB₂'_eq]
    exact hu₂_att'
  have hv₂_att : bd₂.attaches G v₂ = true := by
    rw [bd₂.attaches_iff G hR_path.2.2.1, hB₂_eq, ← hB₂'_eq]
    exact hv₂_att'
  have halt : Alternate D u₁ v₁ u₂ v₂ := hcr.alternate
  obtain ⟨I₁, hI₁_cand, I₂, hI₂_cand, hinter⟩ :=
    lemma_3_candidatesOfIndices hD (bd₁.attaches G) (bd₂.attaches G) γ₁ γ₂
      hu₁_att hv₁_att hu₂_att hv₂_att halt
  rw [← bd₁.attachmentIndices_eq_map_idxOf G hD] at hI₁_cand
  rw [← bd₂.attachmentIndices_eq_map_idxOf G hD] at hI₂_cand
  have hI₁_cs : I₁ ∈ cs := (mem_allBridgeCandidates_iff G).mpr ⟨γ₁, hγ₁, hI₁_cand⟩
  have hI₂_cs : I₂ ∈ cs := (mem_allBridgeCandidates_iff G).mpr ⟨γ₂, hγ₂, hI₂_cand⟩
  have hI₁_sorted : I₁ ∈ sorted := hperm.symm.subset hI₁_cs
  have hI₂_sorted : I₂ ∈ sorted := hperm.symm.subset hI₂_cs
  have hI₁_γ : I₁.γ = γ₁ := by
    unfold candidatesOfIndices at hI₁_cand
    rw [List.mem_map] at hI₁_cand
    obtain ⟨_, _, rfl⟩ := hI₁_cand
    rfl
  have hI₂_γ : I₂.γ = γ₂ := by
    unfold candidatesOfIndices at hI₂_cand
    rw [List.mem_map] at hI₂_cand
    obtain ⟨_, _, rfl⟩ := hI₂_cand
    rfl
  have hsweep_some : (sweepCandidates sorted).isSome := by
    rcases hinter with h12 | h21
    · exact sweepCandidates_complete hpw hI₁_sorted hI₂_sorted
        ⟨by rw [hI₁_γ, hI₂_γ]; exact hγ_ne, h12⟩
    · exact sweepCandidates_complete hpw hI₂_sorted hI₁_sorted
        ⟨by rw [hI₁_γ, hI₂_γ]; exact hγ_ne.symm, h21⟩
  obtain ⟨⟨J, I⟩, hsweep_eq⟩ := Option.isSome_iff_exists.mp hsweep_some
  rw [hsweep_eq]
  obtain ⟨hJ_sorted, hI_sorted, hinter_JI⟩ := sweepCandidates_sound hpw hsweep_eq
  have hJ_cs : J ∈ cs := hperm.subset hJ_sorted
  have hI_cs : I ∈ cs := hperm.subset hI_sorted
  obtain ⟨hγJ, hJ_lr, hJ_r, hJ_l_att, hJ_r_att⟩ := mem_allBridgeCandidates_spec G hJ_cs
  obtain ⟨hγI, hI_lr, hI_r, hI_l_att, hI_r_att⟩ := mem_allBridgeCandidates_spec G hI_cs
  have h₁ : J.l < D.length ∧ J.r < D.length := ⟨lt_trans hJ_lr hJ_r, hJ_r⟩
  have h₂ : I.l < D.length ∧ I.r < D.length := ⟨lt_trans hI_lr hI_r, hI_r⟩
  simp only [h₁, h₂]
  rw [List.getElem?_eq_getElem hγJ, List.getElem?_eq_getElem hγI]
  dsimp only
  have hne_J : D[J.l]'h₁.1 ≠ D[J.r]'h₁.2 :=
    fun h => (ne_of_lt hJ_lr) (hD.getElem_inj_iff.mp h)
  have hne_I : D[I.l]'h₂.1 ≠ D[I.r]'h₂.2 :=
    fun h => (ne_of_lt hI_lr) (hD.getElem_inj_iff.mp h)
  have hfindJ := (bridges[J.γ]'hγJ).findPath_isSome G hG (List.getElem_mem hγJ)
    (List.getElem_mem h₁.1) (List.getElem_mem h₁.2) hne_J
    ((bridges[J.γ]'hγJ).attaches_of_mem_attachmentIndices G hJ_l_att)
    ((bridges[J.γ]'hγJ).attaches_of_mem_attachmentIndices G hJ_r_att)
  have hfindI := (bridges[I.γ]'hγI).findPath_isSome G hG (List.getElem_mem hγI)
    (List.getElem_mem h₂.1) (List.getElem_mem h₂.2) hne_I
    ((bridges[I.γ]'hγI).attaches_of_mem_attachmentIndices G hI_l_att)
    ((bridges[I.γ]'hγI).attaches_of_mem_attachmentIndices G hI_r_att)
  obtain ⟨QJ, hQJ⟩ := Option.isSome_iff_exists.mp hfindJ
  obtain ⟨RI, hRI⟩ := Option.isSome_iff_exists.mp hfindI
  simp [hQJ, hRI]

/-- Exact characterization of `bridgeCross`: `bridgeCross G verts D` returns `some` crossing if and
only if `D` has a crossing in `G` whose two paths use distinct `D`-bridges. -/
theorem bridgeCross_isSome_iff [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts}) (hD : D.Nodup) :
    (bridgeCross G verts D).isSome = true ↔
      ∃ (u₁ v₁ u₂ v₂ : V) (Q : G.Walk u₁ v₁) (R : G.Walk u₂ v₂),
        IsCrossing G D Q R ∧ UsesDistinctBridges G {x | x ∈ verts} D Q R := by
  constructor
  · intro his
    obtain ⟨cr, hcr⟩ := Option.isSome_iff_exists.mp his
    obtain ⟨hvalid, hdist⟩ := bridgeCross_valid_and_usesDistinctBridges G hG hD hcr
    exact ⟨cr.u₁, cr.v₁, cr.u₂, cr.v₂, cr.Q, cr.R, hvalid, hdist⟩
  · rintro ⟨u₁, v₁, u₂, v₂, Q, R, hcr, hdist⟩
    exact bridgeCross_isSome_of_usesDistinctBridges G hG hD hcr hdist

/-- "Every crossing in a planar graph uses distinct cycle bridges. Therefore \(\operatorname{BridgeCross}\)
is complete on planar inputs." (`docs/crossing/crossing_extractor.tex`, Lemma 4, Section 5.3). -/
theorem bridgeCross_isSome_iff_isCrossed_of_planar [DecidableEq V] [WalkSearch V]
    [LawfulWalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts}) (hD : D.Nodup)
    (h_lemma4 : ∀ {u₁ v₁ u₂ v₂ : V} (Q : G.Walk u₁ v₁) (R : G.Walk u₂ v₂),
      IsCrossing G D Q R → UsesDistinctBridges G {x | x ∈ verts} D Q R) :
    (bridgeCross G verts D).isSome = true ↔ IsCrossed G D := by
  rw [bridgeCross_isSome_iff G hG hD]
  constructor
  · rintro ⟨u₁, v₁, u₂, v₂, Q, R, hcr, _⟩
    exact ⟨u₁, v₁, u₂, v₂, Q, R, hcr⟩
  · rintro ⟨u₁, v₁, u₂, v₂, Q, R, hcr⟩
    exact ⟨u₁, v₁, u₂, v₂, Q, R, hcr, h_lemma4 Q R hcr⟩

/-! ### 5. Step count and search count bounds for `bridgeCross` -/

/-- Number of path searches performed by `bridgeCross G verts D`. -/
def bridgeCrossSearches [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) : ℕ :=
  let bridges := allBridgeData G verts D
  let cs := allBridgeCandidates G D bridges
  let sorted := sortCandidates D.length cs
  match sweepCandidates sorted with
  | none => 0
  | some (I₁, I₂) =>
    if I₁.l < D.length ∧ I₁.r < D.length then
      if I₂.l < D.length ∧ I₂.r < D.length then
        match bridges[I₁.γ]?, bridges[I₂.γ]? with
        | some bd₁, some bd₂ => bd₁.findPathSearches + bd₂.findPathSearches
        | _, _ => 0
      else 0
    else 0

/-- `bridgeCross` makes at most two path searches (`docs/crossing/crossing_extractor.tex`,
Section 5.2: "When an alternating pair of candidates of different colors is found, we make two
searches."). -/
theorem bridgeCrossSearches_le_two [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) :
    bridgeCrossSearches G verts D ≤ 2 := by
  unfold bridgeCrossSearches
  dsimp only
  cases sweepCandidates _ with
  | none => simp
  | some pair =>
    rcases pair with ⟨I₁, I₂⟩
    dsimp only
    split_ifs
    · cases (allBridgeData G verts D)[I₁.γ]? with
      | none => simp
      | some bd₁ =>
        cases (allBridgeData G verts D)[I₂.γ]? with
        | none => simp
        | some bd₂ =>
          dsimp only
          have h1 := bd₁.findPathSearches_le_one
          have h2 := bd₂.findPathSearches_le_one
          omega
    · omega
    · omega

/-- Total number of bridge-attachment incidences across a list of bridges. -/
def totalAttachments [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : List V) (bridges : List (BridgeData V)) : ℕ :=
  (bridges.map (fun bd => (bd.attachmentIndices G D).length)).sum

theorem length_flatMap_range_le {α β : Type*} (L : List α) (f : ℕ → List β)
    (g : α → ℕ) (hfg : ∀ (i : ℕ) (hi : i < L.length), (f i).length ≤ g (L[i]'hi)) :
    ((List.range L.length).flatMap f).length ≤ (L.map g).sum := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ,
      List.flatMap_append, List.length_append, List.map_append, List.sum_append]
    simp only [List.flatMap_singleton, List.map_singleton, List.sum_singleton]
    have ih' : ((List.range xs.length).flatMap f).length ≤ (xs.map g).sum := by
      apply ih
      intro i hi
      have hi' : i < (xs ++ [x]).length := by simp; omega
      have hget : (xs ++ [x])[i]'hi' = xs[i]'hi := List.getElem_append_left hi
      simpa [hget] using hfg i hi'
    have hlast_lt : xs.length < (xs ++ [x]).length := by simp
    have hlast_get : (xs ++ [x])[xs.length]'hlast_lt = x := by simp
    have hlast : (f xs.length).length ≤ g x := by
      simpa [hlast_get] using hfg xs.length hlast_lt
    exact Nat.add_le_add ih' hlast

/-- "There are at most twice as many candidates as attachments."
(`docs/crossing/crossing_extractor.tex`, Section 5.1), summed over all bridges. -/
theorem length_allBridgeCandidates_le [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : List V) (bridges : List (BridgeData V)) :
    (allBridgeCandidates G D bridges).length ≤ 2 * totalAttachments G D bridges := by
  unfold allBridgeCandidates totalAttachments
  have hmul : (bridges.map (fun bd => 2 * (bd.attachmentIndices G D).length)).sum =
      2 * (bridges.map (fun bd => (bd.attachmentIndices G D).length)).sum := by
    induction bridges with
    | nil => simp
    | cons bd tl ih => simp [List.sum_cons, ih, Nat.mul_add]
  rw [← hmul]
  apply length_flatMap_range_le bridges
    (fun γ => match bridges[γ]? with
      | some bd => candidatesOfIndices γ (bd.attachmentIndices G D)
      | none => [])
    (fun bd => 2 * (bd.attachmentIndices G D).length)
  intro γ hγ
  rw [List.getElem?_eq_getElem hγ]
  exact length_candidatesOfIndices_le γ ((bridges[γ]'hγ).attachmentIndices G D)

/-- For any bridge `bd` at index `γ`, at most six of its candidates are active at any sweep
position `l₀` (`docs/crossing/crossing_extractor.tex`, Section 5.2). -/
theorem BridgeData.length_active_candidates_le_six [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : List V) (bd : BridgeData V) (γ l₀ : ℕ) :
    ((candidatesOfIndices γ (bd.attachmentIndices G D)).filter
      (fun I => decide (I.l ≤ l₀ ∧ l₀ < I.r))).length ≤ 6 :=
  length_active_candidatesOfIndices_le γ (bd.pairwise_attachmentIndices G D) l₀

/-- Every block `B` in the sweep stack `st` whose stored candidates of color `B.γ` are bounded by
the active candidates of `bd` at sweep position `l₀` has size at most six
(`docs/crossing/crossing_extractor.tex`, Section 5.2). -/
theorem BridgeData.block_length_items_le_six [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : List V) (bd : BridgeData V) {st : List Block} (hst : StackInv st)
    {B : Block} (hB : B ∈ st) (l₀ : ℕ)
    (hle : ((storedCandidates st).filter (fun J => J.γ == B.γ)).length ≤
      ((candidatesOfIndices B.γ (bd.attachmentIndices G D)).filter
        (fun I => decide (I.l ≤ l₀ ∧ l₀ < I.r))).length) :
    B.items.length ≤ 6 :=
  Block.length_items_le_six hst hB (bd.pairwise_attachmentIndices G D) l₀ hle

/-- List of directed edges `(u, v)` of `G` on `verts.dedup`. Its length is `2 * |E(G)|`. -/
def directedEdges [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts : List V) : List (V × V) :=
  verts.dedup.flatMap (fun u =>
    verts.dedup.filterMap (fun v => if G.Adj u v then some (u, v) else none))

theorem mem_directedEdges_iff [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts : List V} {u v : V} :
    (u, v) ∈ directedEdges G verts ↔ u ∈ verts ∧ v ∈ verts ∧ G.Adj u v := by
  simp only [directedEdges, List.mem_flatMap, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨u', hu', v', hv', hif⟩
    split_ifs at hif with hadj
    simp only [Option.some.injEq, Prod.mk.injEq] at hif
    rcases hif with ⟨rfl, rfl⟩
    exact ⟨hu', hv', hadj⟩
  · rintro ⟨hu, hv, hadj⟩
    exact ⟨u, hu, v, hv, by simp [hadj]⟩

theorem exists_directedEdge_of_isBridgeAttachment [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts})
    {B : Bridge V} (hB : IsBridge G {x | x ∈ verts} D B)
    {v : V} (hatt : IsBridgeAttachment G D B v) :
    ∃ u, (u, v) ∈ directedEdges G verts ∧
      (if u ∈ D then Bridge.chord s(u, v) else Bridge.comp (offCycleComp G D u)) = B := by
  cases B with
  | comp A =>
    obtain ⟨r, hr_verts, hr_not_D, rfl⟩ := hB
    obtain ⟨_, u, hu_comp, hadj⟩ := hatt
    have hu_verts : u ∈ verts := offCycleComp_subset_supp hG hr_verts hu_comp
    have hv_verts : v ∈ verts := hG hadj.symm
    have hu_not_D : u ∉ D := hu_comp.1
    refine ⟨u, (mem_directedEdges_iff G).mpr ⟨hu_verts, hv_verts, hadj⟩, ?_⟩
    simp only [hu_not_D, ↓reduceIte, offCycleComp_eq_of_mem hu_comp]
  | chord e =>
    obtain ⟨p, q, rfl, hpD, hqD, hadj_pq, _⟩ := hB
    obtain ⟨_, hv_e⟩ := hatt
    rcases Sym2.mem_iff.mp hv_e with rfl | rfl
    · refine ⟨q, (mem_directedEdges_iff G).mpr ⟨hG hadj_pq.symm, hG hadj_pq, hadj_pq.symm⟩, ?_⟩
      simp only [hqD, ↓reduceIte, Sym2.eq_swap]
    · refine ⟨p, (mem_directedEdges_iff G).mpr ⟨hG hadj_pq, hG hadj_pq.symm, hadj_pq⟩, ?_⟩
      simp only [hpD, ↓reduceIte]

/-- List of all `(bridgeIndex, attachmentIndex)` pairs for a list of bridges. -/
def attachmentPairs [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : List V) : List (BridgeData V) → List (ℕ × ℕ)
  | [] => []
  | bd :: tl =>
    (bd.attachmentIndices G D).map (fun i => (0, i)) ++
      (attachmentPairs G D tl).map (fun p => (p.1 + 1, p.2))

theorem length_attachmentPairs [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : List V) (bridges : List (BridgeData V)) :
    (attachmentPairs G D bridges).length = totalAttachments G D bridges := by
  induction bridges with
  | nil => simp [attachmentPairs, totalAttachments]
  | cons bd tl ih => simp [attachmentPairs, totalAttachments, ih]

theorem nodup_attachmentPairs [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : List V) (bridges : List (BridgeData V)) :
    (attachmentPairs G D bridges).Nodup := by
  induction bridges with
  | nil => simp [attachmentPairs]
  | cons bd tl ih =>
    simp only [attachmentPairs]
    apply List.Nodup.append
    · refine ((List.nodup_range).filter _).map ?_
      intro a b h
      exact (Prod.mk.injEq 0 a 0 b).mp h |>.2
    · refine ih.map ?_
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      omega
    · intro x hx₁ hx₂
      rw [List.mem_map] at hx₁ hx₂
      obtain ⟨i, _, rfl⟩ := hx₁
      obtain ⟨⟨γ, j⟩, _, heq⟩ := hx₂
      simp only [Prod.mk.injEq] at heq
      omega

theorem mem_attachmentPairs_spec [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : List V} {bridges : List (BridgeData V)} {p : ℕ × ℕ}
    (hp : p ∈ attachmentPairs G D bridges) :
    ∃ (hγ : p.1 < bridges.length), p.2 ∈ (bridges[p.1]'hγ).attachmentIndices G D := by
  induction bridges generalizing p with
  | nil => cases hp
  | cons bd tl ih =>
    simp only [attachmentPairs, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨i, hi, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨Nat.zero_lt_succ tl.length, hi⟩
    · obtain ⟨hγ, hq2⟩ := ih hq
      exact ⟨Nat.succ_lt_succ hγ, hq2⟩

theorem nodup_length_le_of_forall_exists_map {α β : Type*} [DecidableEq β]
    {L₁ : List β} (L₂ : List α) (f : α → β)
    (hnd : L₁.Nodup) (hsub : ∀ x ∈ L₁, ∃ y ∈ L₂, f y = x) :
    L₁.length ≤ L₂.length := by
  have h1 : L₁.length ≤ (L₂.map f).length := by
    apply nodup_length_le_of_subset hnd
    intro x hx
    rw [List.mem_map]
    exact hsub x hx
  rwa [List.length_map] at h1

/-- Every bridge-attachment incidence corresponds to a distinct directed edge `(u, v)` of `G` with
`v ∈ D`, so the total number of bridge-attachment incidences across all bridges is at most
`(directedEdges G verts).length = 2 * |E(G)|`
(`docs/crossing/crossing_extractor.tex`, Section 5.1). -/
theorem totalAttachments_le_directedEdges [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts})
    (hD : D.Nodup) :
    totalAttachments G D (allBridgeData G verts D) ≤ (directedEdges G verts).length := by
  classical
  set bridges := allBridgeData G verts D
  rw [← length_attachmentPairs G D bridges]
  let f : V × V → ℕ × ℕ := fun ⟨u, v⟩ =>
    let B : Bridge V := if u ∈ D then Bridge.chord s(u, v) else Bridge.comp (offCycleComp G D u)
    let γ : ℕ := if h : ∃ (γ : ℕ) (hγ : γ < bridges.length), (bridges[γ]'hγ).toBridge = B
      then Classical.choose h else 0
    (γ, D.idxOf v)
  apply nodup_length_le_of_forall_exists_map (directedEdges G verts) f
    (nodup_attachmentPairs G D bridges)
  rintro ⟨γ₀, i₀⟩ hp
  obtain ⟨hγ₀, hi₀⟩ := mem_attachmentPairs_spec G hp
  have hi₀_lt : i₀ < D.length := (bridges[γ₀]'hγ₀).mem_attachmentIndices_lt G hi₀
  set bd₀ := bridges[γ₀]'hγ₀
  set v₀ := D[i₀]'hi₀_lt
  have hv₀_D : v₀ ∈ D := List.getElem_mem hi₀_lt
  have hatt₀ : IsBridgeAttachment G D bd₀.toBridge v₀ :=
    (bd₀.attaches_iff G hv₀_D).mp (bd₀.attaches_of_mem_attachmentIndices G hi₀)
  have hB₀ : IsBridge G {x | x ∈ verts} D bd₀.toBridge :=
    (isBridge_of_mem_allBridgeData G hG (List.getElem_mem hγ₀)).1
  obtain ⟨u₀, hdir, hB_eq⟩ := exists_directedEdge_of_isBridgeAttachment G hG hB₀ hatt₀
  refine ⟨(u₀, v₀), hdir, ?_⟩
  dsimp only [f]
  rw [hB_eq]
  have hex : ∃ (γ : ℕ) (hγ : γ < bridges.length), (bridges[γ]'hγ).toBridge = bd₀.toBridge :=
    ⟨γ₀, hγ₀, rfl⟩
  simp only [hex, ↓reduceDIte]
  have hchoose_spec := Classical.choose_spec hex
  obtain ⟨hγ_ch, hch_eq⟩ := hchoose_spec
  have hγ_eq : Classical.choose hex = γ₀ := by
    by_contra hne
    exact allBridgeData_toBridge_ne_of_ne G verts D hγ_ch hγ₀ hne hch_eq
  rw [hγ_eq, hD.idxOf_getElem i₀ hi₀_lt]

/-- Total combinatorial step count of `bridgeCross` outside the at most two path searches:
1. `verts.length + totalAttachments G D bridges` for bridge and attachment collection;
2. `cs.length` for candidate generation;
3. `sortCandidatesSteps D.length cs` for the two stable counting-sort passes;
4. `sweepInsertions [] sorted + sweepRemovals [] sorted` for the block-stack sweep. -/
def bridgeCrossSteps [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) : ℕ :=
  let bridges := allBridgeData G verts D
  let cs := allBridgeCandidates G D bridges
  let sorted := sortCandidates D.length cs
  (verts.length + totalAttachments G D bridges) +
    cs.length +
    sortCandidatesSteps D.length cs +
    (sweepInsertions [] sorted + sweepRemovals [] sorted)

/-- Linear bound on `bridgeCrossSteps`: the non-search work of `bridgeCross` is bounded by
`verts.length + 2 * D.length + 11 * totalAttachments G D (allBridgeData G verts D)`. -/
theorem bridgeCrossSteps_le [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) :
    let bridges := allBridgeData G verts D
    bridgeCrossSteps G verts D ≤
      verts.length + 2 * D.length + 11 * totalAttachments G D bridges := by
  dsimp only [bridgeCrossSteps]
  set bridges := allBridgeData G verts D
  set cs := allBridgeCandidates G D bridges
  set sorted := sortCandidates D.length cs
  have hcs_le : cs.length ≤ 2 * totalAttachments G D bridges :=
    length_allBridgeCandidates_le G D bridges
  have hsort_steps : sortCandidatesSteps D.length cs ≤ 2 * (D.length + cs.length) :=
    sortCandidatesSteps_le D.length cs
  have hsorted_len : sorted.length ≤ cs.length := by
    unfold sorted sortCandidates
    exact le_trans (length_countingSort_le _ _ _) (length_countingSort_le _ _ _)
  have hins : sweepInsertions [] sorted ≤ sorted.length := sweepInsertions_le [] sorted
  have hrem : sweepRemovals [] sorted ≤ sorted.length := by
    simpa [storedCandidates] using sweepRemovals_le [] sorted
  omega

/-- Linear bound on `bridgeCrossSteps` in terms of `|S|` (`verts.length`, `D.length`) and `2|E|`
(`(directedEdges G verts).length`), matching Section 5.2 of `docs/crossing/crossing_extractor.tex`
("We call this whole procedure \(\operatorname{BridgeCross}(K,D)\). It takes time \(O(n+m)\) and,
when it succeeds, two path searches."). -/
theorem bridgeCrossSteps_le_linear [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : IsSupportedOn G {x | x ∈ verts}) (hD : D.Nodup) :
    bridgeCrossSteps G verts D ≤
      verts.length + 2 * D.length + 11 * (directedEdges G verts).length := by
  have h1 := bridgeCrossSteps_le G verts D
  have h2 := totalAttachments_le_directedEdges G hG hD
  omega

end GraphMinor.Crossing
