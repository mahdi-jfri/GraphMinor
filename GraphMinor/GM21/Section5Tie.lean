module

public import GraphMinor.GM21.Section5Lift
import GraphMinor.GM11.Section6
import GraphMinor.GM11.Section85
import GraphMinor.GM11.Section91
import GraphMinor.GM11.Section92
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM11.RadialRegions
import GraphMinor.GM12.Section4WalkMetric
import GraphMinor.GM12.Section6Regions
import GraphMinor.GM12.Section72Circuit
import GraphMinor.GM12.Section73CircuitPath
import GraphMinor.GM12.Section78
import GraphMinor.GM19.Section15c
import GraphMinor.GM19.Section15i
import GraphMinor.Surface.PushOff

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Graph Minors XXI, Section 5: Proof of Claim (10) of `(5.2)`

Formalizes Claim (10) (`claim_5_2_10`, pages 20–21 of the preprint) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616:

- "(10) *If* $r_1, r_2$ *are the cuff regions corresponding to distinct cuffs* $C_1, C_2$ *then*
  $d_1(r_1, r_2) \ge \theta_4$."

Following the paper's subproof, we:
1. Show from Claim (7) (`claim_5_2_7`) that no path-connected `H₀`-normal subset `M ⊆ S₀` with
   `(M ∩ H₀.V).ncard ≤ θ₄` meets `closure (cap.cuffDisc C₁)` and `closure (cap.cuffDisc C₂)` for
   distinct cuffs `C₁ ≠ C₂` (`no_cuff_conn_of_claim_5_2_7`), so distinct cuffs have distinct cuff
   regions (`cuffRegion_ne_of_cuff_ne`) and any closed walk `W` of the radial drawing `K` of length
   `< 2 * θ₄` meets `r_c ∪ closure (cap.cuffDisc c)` for at most one cuff `c ∈ cuffs S`
   (`unique_cuff_of_closed_walk`).
2. Prove a unified two-disc and line-cutting contradiction lemma
   (`contradiction_of_two_discs_and_line`) that removes two disjoint closed discs `Δ₁, Δ₂` and at
   most `(cuffs S).ncard - 2` cuff discs from `S₀`, cuts the resulting surface `W` along a normal
   proper line `L₀` between `discBd Δ₁` and `discBd Δ₂`, lifts the subdrawing `B` across the cut,
   and contradicts Claim (6) (`apply_claim_5_2_6_of_drawing`).
3. Show that no circuit `G₁` of `K` of length `< 2 * θ₄` with
   `r₁ ∪ closure (cap.cuffDisc C₁) ⊆ discInt (ins G₁)` can pass through the hub vertex `z_c` of any
   cuff region `r_c` (`no_other_cuff_hub_on_circuit`), using `Surface.push_disc` and
   `contradiction_of_two_discs_and_line`.
4. Show Case (10)(i) (`no_walk_meets_other_cuff_of_cuff_in_discInt`): if `W` is a closed walk of
   `K` of length `< 2 * θ₄` and `G₁` is a circuit of `walkDrawing K W` with
   `r₁ ∪ closure (cap.cuffDisc C₁) ⊆ discInt (ins G₁)`, then `walkDrawing K W` cannot meet
   `r_c ∪ closure (cap.cuffDisc c)` for any cuff `c ≠ C₁`, by extracting the normal line `F₀` from
   `F₁` to `c` (or radial line across `cap.cuffDisc c` when `D₁` touches `c`) and applying
   `contradiction_of_two_discs_and_line`.
5. Deduce that `(walkDrawing K W).U ⊆ cap.emb '' (S \ bd S)`, extract the two circuit pieces
   `(D₁, G₁)` and `(D₂, G₂)` of the restraint `Y = insWalk ins K W` around `z₁ ∈ r₁` and
   `z₂ ∈ r₂` via `GM11.exists_piece` and `GM11.piece_of_two_points`, and rule out both
   Case (10)(ii) (`(D₁ ∩ D₂).Subsingleton` with `D₁ ∩ D₂ = {p}`) and Case (10)(iii)
   (`Disjoint D₁ D₂` with connecting normal line `F₀`) via `contradiction_of_two_discs_and_line`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph unitInterval
open GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM19

local notation "𝕀" => unitInterval

universe u v w

/-! ## 1. Crossing lines in path-connected sets and two-disc cutting contradiction -/

/-- If `Z ⊆ S` is path-connected and meets two closed sets `X, Y ⊆ S` that are disjoint on `Z`
(`Disjoint (Z ∩ X) (Z ∩ Y)`), then `Z` contains a line `L` with ends `a ∈ Z ∩ frontier X` (`a ∈ X`)
and `b ∈ Z ∩ frontier Y` (`b ∈ Y`) whose interior `L \ {a, b}` lies in `Z \ (X ∪ Y)`. -/
theorem exists_line_crossing_of_isPathConnected {S : Type*} [TopologicalSpace S] [T2Space S]
    {Z X Y : Set S} (hZ : IsPathConnected Z) (hX : IsClosed X) (hY : IsClosed Y)
    (hdisj : Disjoint (Z ∩ X) (Z ∩ Y))
    {p q : S} (hpZ : p ∈ Z) (hpX : p ∈ X) (hqZ : q ∈ Z) (hqY : q ∈ Y) :
    ∃ (L : Set S) (a b : S),
      IsLineWithEnds L a b ∧
      L ⊆ Z ∧
      a ∈ Z ∩ X ∧ a ∈ frontier X ∧
      b ∈ Z ∩ Y ∧ b ∈ frontier Y ∧
      L \ {a, b} ⊆ Z \ (X ∪ Y) := by
  have hXYZ : ∀ {x : S}, x ∈ Z → x ∈ X → x ∈ Y → False := fun hz hx hy =>
    Set.disjoint_left.mp hdisj ⟨hz, hx⟩ ⟨hz, hy⟩
  obtain ⟨c, hc⟩ := hZ.joinedIn p hpZ q hqZ
  have hcc : Continuous c := c.continuous
  obtain ⟨s, s', hss, hsT, hsT', hgap⟩ :=
    GM12.exists_crossing (hX.preimage hcc) (hY.preimage hcc)
      (Set.disjoint_left.mpr fun t h1 h2 => hXYZ (hc t) h1 h2)
      (by change c 0 ∈ X; rw [c.source]; exact hpX)
      (by change c 1 ∈ Y; rw [c.target]; exact hqY)
  have hsn : s.1 < s'.1 := hss
  let u : 𝕀 → 𝕀 := fun t => ⟨s.1 + t.1 * (s'.1 - s.1), by
    have h1 := s.2.1
    have h2 := t.2.1
    have := mul_nonneg h2 (sub_nonneg.mpr hsn.le)
    linarith, by
    have h1 := t.2.2
    have h2 := s'.2.2
    have := mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hsn.le)
    linarith⟩
  have huc : Continuous u := Continuous.subtype_mk (by fun_prop) _
  let δ : 𝕀 → S := fun t => c (u t)
  have hδ : Continuous δ := hcc.comp huc
  have hu0 : u 0 = s := Subtype.ext (by simp [u])
  have hu1 : u 1 = s' := Subtype.ext (by simp [u])
  set a := c s with ha_def
  set b := c s' with hb_def
  have hδ0 : δ 0 = a := by simp only [δ, hu0, ha_def]
  have hδ1 : δ 1 = b := by simp only [δ, hu1, hb_def]
  have haZ : a ∈ Z := hc s
  have hbZ : b ∈ Z := hc s'
  have hab : a ≠ b := fun he => hXYZ haZ hsT (he ▸ hsT')
  obtain ⟨e, he, hei, he0, he1, hrng⟩ := exists_arc_of_path hδ (by rw [hδ0, hδ1]; exact hab)
  rw [hδ0] at he0
  rw [hδ1] at he1
  have harc : IsArcMap e := ⟨he, hei⟩
  have hL : IsLineWithEnds (range e) a b := he0 ▸ he1 ▸ harc.isLineWithEnds
  have hLZ : range e ⊆ Z := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t', ht'⟩ := hrng ⟨t, rfl⟩
    rw [← ht']
    exact hc _
  have hLint : range e \ {a, b} ⊆ Z \ (X ∪ Y) := by
    rintro z ⟨hz, hzab⟩
    refine ⟨hLZ hz, ?_⟩
    rintro (hzX | hzY)
    · obtain ⟨t, rfl⟩ := hrng hz
      have h0 : t ≠ 0 := fun h => hzab (Or.inl (by simp [h, hδ0]))
      have h1 : t ≠ 1 := fun h => hzab (Or.inr (by simp [h, hδ1]))
      have ht0 : 0 < t.1 := lt_of_le_of_ne t.2.1 fun he => h0 (Subtype.ext he.symm)
      have ht1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun he => h1 (Subtype.ext he)
      have h3 : s < u t := by change s.1 < s.1 + t.1 * (s'.1 - s.1); nlinarith
      have h4 : u t < s' := by change s.1 + t.1 * (s'.1 - s.1) < s'.1; nlinarith
      exact (hgap _ h3 h4).1 hzX
    · obtain ⟨t, rfl⟩ := hrng hz
      have h0 : t ≠ 0 := fun h => hzab (Or.inl (by simp [h, hδ0]))
      have h1 : t ≠ 1 := fun h => hzab (Or.inr (by simp [h, hδ1]))
      have ht0 : 0 < t.1 := lt_of_le_of_ne t.2.1 fun he => h0 (Subtype.ext he.symm)
      have ht1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun he => h1 (Subtype.ext he)
      have h3 : s < u t := by change s.1 < s.1 + t.1 * (s'.1 - s.1); nlinarith
      have h4 : u t < s' := by change s.1 + t.1 * (s'.1 - s.1) < s'.1; nlinarith
      exact (hgap _ h3 h4).2 hzY
  have hLcl : closure (range e \ {a, b}) = range e := GM11.closure_sdiff_pair hL
  have haL : a ∈ range e := hL.left_mem
  have hbL : b ∈ range e := hL.right_mem
  have ha_fr : a ∈ frontier X := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hsT, ?_⟩
    have hcomp : range e \ {a, b} ⊆ Xᶜ := fun z hz hzX => (hLint hz).2 (Or.inl hzX)
    exact closure_mono hcomp (hLcl.symm ▸ haL)
  have hb_fr : b ∈ frontier Y := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hsT', ?_⟩
    have hcomp : range e \ {a, b} ⊆ Yᶜ := fun z hz hzY => (hLint hz).2 (Or.inr hzY)
    exact closure_mono hcomp (hLcl.symm ▸ hbL)
  exact ⟨range e, a, b, hL, hLZ, ⟨haZ, hsT⟩, ha_fr, ⟨hbZ, hsT'⟩, hb_fr, hLint⟩

/-- Subspace drawing restriction for a closed set `K_B ⊆ Shat` inside a subspace `W ⊆ Shat`
when `(capDrawing hS cap Γ).U ∩ K_B ⊆ W`: restricting `(capDrawing hS cap Γ).interSet K_B` to `W`
via `GM12.drawingInSubspace` produces a drawing `Γ' : Drawing W` and injective maps `(π, fE)` on
`Γ'.V` and `Γ'.E` such that
`mapHypergraph π fE Γ'.toHypergraph = (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)`. -/
theorem exists_subspace_drawing_of_closed_subset {S Shat : Type}
    [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : GM19.IsCappedSurface S Shat)
    (Γ : Surface.Drawing S) {K_B W : Set Shat}
    (hKB : IsClosed K_B) (hKB_W : (capDrawing hS cap Γ).U ∩ K_B ⊆ W) :
    ∃ (Γ' : Surface.Drawing W) (π : W → S) (fE : Set W → Set S),
      InjOn π Γ'.V ∧
      InjOn fE Γ'.E ∧
      mapHypergraph π fE Γ'.toHypergraph =
        (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B) ∧
      (∀ y ∈ Γ'.V, cap.emb (π y) = y.1 ∧ π y ∈ Γ.V ∧ y.1 ∈ K_B) ∧
      (∀ y ∈ Γ'.U, y.1 ∈ cap.emb '' Γ.U ∧ y.1 ∈ K_B ∧ (y.1 ∈ cap.emb '' Γ.V → y ∈ Γ'.V)) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : T2Space Shat := cap.isSurface.2.1
  let Γ_hat := capDrawing hS cap Γ
  let B_hat := Γ_hat.interSet K_B
  have hUC : B_hat.U ⊆ W := fun x hx =>
    hKB_W ⟨interSet_U_subset_self Γ_hat K_B hx, interSet_U_subset Γ_hat hKB hx⟩
  let Γ' : Surface.Drawing W := GM12.drawingInSubspace B_hat W hUC
  have hU_spec : ∀ y ∈ Γ'.U,
      y.1 ∈ cap.emb '' Γ.U ∧ y.1 ∈ K_B ∧ (y.1 ∈ cap.emb '' Γ.V → y ∈ Γ'.V) := by
    intro y hyU
    have hyB : y.1 ∈ B_hat.U := by rwa [GM12.drawingInSubspace_U] at hyU
    have hy_hatU : y.1 ∈ Γ_hat.U := interSet_U_subset_self Γ_hat K_B hyB
    have hy_KB : y.1 ∈ K_B := interSet_U_subset Γ_hat hKB hyB
    rw [capDrawing_U] at hy_hatU
    refine ⟨hy_hatU, hy_KB, fun hy_hatV => ?_⟩
    rw [GM12.drawingInSubspace_V]
    have hV_eq : B_hat.V = Γ_hat.V ∩ K_B :=
      congrArg Hypergraph.vertexSet (interSet_toHypergraph_eq_inter Γ_hat hKB)
    change y.1 ∈ B_hat.V
    rw [hV_eq, capDrawing_V]
    exact ⟨hy_hatV, hy_KB⟩
  have h_sub_map :
      mapHypergraph (Subtype.val : W → Shat) (image (Subtype.val : W → Shat)) Γ'.toHypergraph =
        (PaintingOrDrawing.drawing Γ_hat).inter K_B :=
    (mapHypergraph_drawingInSubspace_eq B_hat W hUC).trans (interSet_toHypergraph_eq_inter Γ_hat hKB)
  have h_cap_map := mapHypergraph_cap_inter_eq hS cap Γ K_B
  have hinj := cap.isEmbedding.injective
  have hV_range : ∀ y ∈ Γ'.V, y.1 ∈ cap.emb '' Γ.V ∧ y.1 ∈ K_B := by
    intro y hy
    have hyB : y.1 ∈ B_hat.V := by rwa [GM12.drawingInSubspace_V] at hy
    have hV_eq : B_hat.V = Γ_hat.V ∩ K_B :=
      congrArg Hypergraph.vertexSet (interSet_toHypergraph_eq_inter Γ_hat hKB)
    rw [hV_eq, capDrawing_V] at hyB
    exact hyB
  have hE_range : ∀ e' ∈ Γ'.E, (Subtype.val : W → Shat) '' e' ∈ (image cap.emb) '' Γ.E := by
    intro e' he'
    have he'B : (Subtype.val : W → Shat) '' e' ∈ B_hat.E := by
      change (Subtype.val : W → Shat) '' e' ∈ B_hat.toHypergraph.edgeSet
      rw [← mapHypergraph_drawingInSubspace_eq B_hat W hUC]
      exact mem_image_of_mem _ he'
    have hE_eq : B_hat.E = {e ∈ Γ_hat.E | e ⊆ K_B} :=
      congrArg Hypergraph.edgeSet (interSet_toHypergraph_eq_inter Γ_hat hKB)
    rw [hE_eq, capDrawing_E] at he'B
    exact he'B.1
  let fE : Set W → Set S := fun e' => cap.emb ⁻¹' ((Subtype.val : W → Shat) '' e')
  by_cases hS_ne : Nonempty S
  · haveI := hS_ne
    let π₀ : W → S := fun y => Function.invFun cap.emb y.1
    have hπ₀_spec : ∀ y ∈ Γ'.V, cap.emb (π₀ y) = y.1 ∧ π₀ y ∈ Γ.V ∧ y.1 ∈ K_B := by
      intro y hy
      rcases hV_range y hy with ⟨⟨v, hv, hvy⟩, hyKB⟩
      have hinv : π₀ y = v := by
        dsimp [π₀]
        rw [← hvy]
        exact Function.leftInverse_invFun hinj v
      exact ⟨hinv ▸ hvy, hinv ▸ hv, hyKB⟩
    have hπ₀_inj : InjOn π₀ Γ'.V := by
      intro y₁ hy₁ y₂ hy₂ h_eq
      apply Subtype.ext
      rw [← (hπ₀_spec y₁ hy₁).1, ← (hπ₀_spec y₂ hy₂).1, h_eq]
    have hfE_spec : ∀ e' ∈ Γ'.E,
        cap.emb '' (fE e') = (Subtype.val : W → Shat) '' e' ∧ fE e' ∈ Γ.E := by
      intro e' he'
      rcases hE_range e' he' with ⟨e₀, he₀, he₀_eq⟩
      have hfE_eq : fE e' = e₀ := by
        dsimp [fE]
        rw [← he₀_eq, preimage_image_eq _ hinj]
      exact ⟨hfE_eq ▸ he₀_eq, hfE_eq ▸ he₀⟩
    have hfE_inj : InjOn fE Γ'.E := by
      intro e₁ he₁ e₂ he₂ h_eq
      have himg : (Subtype.val : W → Shat) '' e₁ = (Subtype.val : W → Shat) '' e₂ := by
        rw [← (hfE_spec e₁ he₁).1, ← (hfE_spec e₂ he₂).1, h_eq]
      exact Set.image_injective.mpr Subtype.val_injective himg
    refine ⟨Γ', π₀, fE, hπ₀_inj, hfE_inj, ?_, hπ₀_spec, hU_spec⟩
    have h_comp : mapHypergraph cap.emb (image cap.emb)
        (mapHypergraph π₀ fE Γ'.toHypergraph) =
        mapHypergraph cap.emb (image cap.emb)
          ((PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)) := by
      rw [h_cap_map, ← h_sub_map]
      refine Hypergraph.ext (Set.ext fun x => ?_) (Set.ext fun e => ?_)
        (funext fun e => funext fun x => propext ?_)
      · change x ∈ cap.emb '' (π₀ '' Γ'.V) ↔ x ∈ (Subtype.val : W → Shat) '' Γ'.V
        simp only [mem_image]
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨y, hy, (hπ₀_spec y hy).1.symm⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨π₀ y, ⟨y, hy, rfl⟩, (hπ₀_spec y hy).1⟩
      · change e ∈ (image cap.emb) '' (fE '' Γ'.E) ↔
          e ∈ (image (Subtype.val : W → Shat)) '' Γ'.E
        simp only [mem_image]
        constructor
        · rintro ⟨_, ⟨e', he', rfl⟩, rfl⟩
          exact ⟨e', he', (hfE_spec e' he').1.symm⟩
        · rintro ⟨e', he', rfl⟩
          exact ⟨fE e', ⟨e', he', rfl⟩, (hfE_spec e' he').1⟩
      · change (∃ e₁ v₁, (∃ e' y, (e' ∈ Γ'.E ∧ y ∈ Γ'.V ∧ y ∈ closure e') ∧ fE e' = e₁ ∧ π₀ y = v₁) ∧
            cap.emb '' e₁ = e ∧ cap.emb v₁ = x) ↔
          ∃ e' y, (e' ∈ Γ'.E ∧ y ∈ Γ'.V ∧ y ∈ closure e') ∧
            (Subtype.val : W → Shat) '' e' = e ∧ y.1 = x
        constructor
        · rintro ⟨_, _, ⟨e', y, ⟨he', hy, hycl⟩, rfl, rfl⟩, rfl, rfl⟩
          exact ⟨e', y, ⟨he', hy, hycl⟩, (hfE_spec e' he').1.symm, (hπ₀_spec y hy).1.symm⟩
        · rintro ⟨e', y, ⟨he', hy, hycl⟩, rfl, rfl⟩
          exact ⟨fE e', π₀ y, ⟨e', y, ⟨he', hy, hycl⟩, rfl, rfl⟩,
            (hfE_spec e' he').1, (hπ₀_spec y hy).1⟩
    refine Hypergraph.ext (Set.ext fun v => ?_) (Set.ext fun e => ?_)
      (funext fun e => funext fun v => propext ?_)
    · have hv := congrArg (fun H => cap.emb v ∈ H.vertexSet) h_comp
      dsimp [mapHypergraph] at hv
      rw [hinj.mem_set_image, hinj.mem_set_image] at hv
      exact Eq.to_iff hv
    · have he := congrArg (fun H => cap.emb '' e ∈ H.edgeSet) h_comp
      dsimp [mapHypergraph] at he
      rw [(Set.image_injective.mpr hinj).mem_set_image,
        (Set.image_injective.mpr hinj).mem_set_image] at he
      exact Eq.to_iff he
    · have hinc := congrArg (fun H => H.Inc (cap.emb '' e) (cap.emb v)) h_comp
      change (∃ e₀ v₀, (mapHypergraph π₀ fE Γ'.toHypergraph).Inc e₀ v₀ ∧
          cap.emb '' e₀ = cap.emb '' e ∧ cap.emb v₀ = cap.emb v) =
        (∃ e₀ v₀, ((PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)).Inc e₀ v₀ ∧
          cap.emb '' e₀ = cap.emb '' e ∧ cap.emb v₀ = cap.emb v) at hinc
      constructor
      · intro h
        have h' : ∃ e₀ v₀, (mapHypergraph π₀ fE Γ'.toHypergraph).Inc e₀ v₀ ∧
            cap.emb '' e₀ = cap.emb '' e ∧ cap.emb v₀ = cap.emb v := ⟨e, v, h, rfl, rfl⟩
        rw [hinc] at h'
        rcases h' with ⟨e₀, v₀, h₀, he₀, hv₀⟩
        rwa [Set.image_injective.mpr hinj he₀, hinj hv₀] at h₀
      · intro h
        have h' : ∃ e₀ v₀, ((PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)).Inc e₀ v₀ ∧
            cap.emb '' e₀ = cap.emb '' e ∧ cap.emb v₀ = cap.emb v := ⟨e, v, h, rfl, rfl⟩
        rw [← hinc] at h'
        rcases h' with ⟨e₀, v₀, h₀, he₀, hv₀⟩
        rwa [Set.image_injective.mpr hinj he₀, hinj hv₀] at h₀
  · haveI : IsEmpty S := not_nonempty_iff.mp hS_ne
    have hV_emp : Γ.V = ∅ := eq_empty_of_forall_notMem fun x => isEmptyElim x
    have hE_emp : Γ.E = ∅ := by
      refine eq_empty_of_forall_notMem fun e he => ?_
      rcases he.1 with ⟨x, _⟩
      exact isEmptyElim x
    have hV'_emp : Γ'.V = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => ?_
      rcases (hV_range y hy).1 with ⟨v, _, _⟩
      exact isEmptyElim v
    have hE'_emp : Γ'.E = ∅ := by
      refine eq_empty_of_forall_notMem fun e' he' => ?_
      rcases hE_range e' he' with ⟨e₀, he₀, _⟩
      rw [hE_emp] at he₀
      exact he₀
    have h_univ : (range cap.emb)ᶜ = ∅ := by
      rw [cap.compl_eq]
      ext z
      simp only [mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      rintro C ⟨x, _⟩
      exact isEmptyElim x
    have h_range : range cap.emb = univ := compl_empty_iff.mp h_univ
    haveI : IsEmpty W := ⟨fun y => by
      have hy : y.1 ∈ range cap.emb := h_range.symm ▸ mem_univ y.1
      rcases hy with ⟨x, _⟩
      exact isEmptyElim x⟩
    refine ⟨Γ', isEmptyElim, fE, ?_, ?_, ?_, fun y => isEmptyElim y, fun y => isEmptyElim y⟩
    · intro y; exact isEmptyElim y
    · intro e' he'; rw [hE'_emp] at he'; exact False.elim he'
    · refine Hypergraph.ext (Set.ext fun x => isEmptyElim x) (Set.ext fun e => ?_)
        (funext fun e => funext fun x => propext (isEmptyElim x))
      change e ∈ fE '' Γ'.E ↔ e ∈ {e₀ ∈ Γ.E | e₀ ⊆ cap.emb ⁻¹' K_B}
      rw [hE'_emp, hE_emp]
      simp

/-- An injective vertex/edge map preserves `IsVertexSplit`. -/
theorem isVertexSplit_mapHypergraph {α : Type u} {β : Type v} {α' : Type w} {β' : Type*}
    {G G₁ : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G₁ v v₁ v₂ δ₁ δ₂)
    {fV : α → α'} {fE : β → β'}
    (hfV : InjOn fV (G.vertexSet ∪ {v₁, v₂}))
    (hfE : InjOn fE G.edgeSet) :
    IsVertexSplit (mapHypergraph fV fE G) (mapHypergraph fV fE G₁)
      (fV v) (fV v₁) (fV v₂) (fE '' δ₁) (fE '' δ₂) := by
  have hv_mem : v ∈ G.vertexSet ∪ {v₁, v₂} := Or.inl hs.v_mem
  have hv₁_mem : v₁ ∈ G.vertexSet ∪ {v₁, v₂} := Or.inr (Or.inl rfl)
  have hv₂_mem : v₂ ∈ G.vertexSet ∪ {v₁, v₂} := Or.inr (Or.inr rfl)
  have hG₁_V_sub : G₁.vertexSet ⊆ G.vertexSet ∪ {v₁, v₂} := by
    rw [hs.vertexSet_eq]
    exact union_subset_union sdiff_subset Subset.rfl
  have hδ_sub : δ₁ ∪ δ₂ ⊆ G.edgeSet := by
    rw [hs.δ_union]
    intro e he
    exact he.1
  have hδ₁_sub : δ₁ ⊆ G.edgeSet := subset_union_left.trans hδ_sub
  have hδ₂_sub : δ₂ ⊆ G.edgeSet := subset_union_right.trans hδ_sub
  refine
    { v_mem := mem_image_of_mem fV hs.v_mem
      v₁_not_mem := by
        rintro ⟨u, huG, h_eq⟩
        have huv₁ : u = v₁ := hfV (Or.inl huG) hv₁_mem h_eq
        exact hs.v₁_not_mem (huv₁ ▸ huG)
      v₂_not_mem := by
        rintro ⟨u, huG, h_eq⟩
        have huv₂ : u = v₂ := hfV (Or.inl huG) hv₂_mem h_eq
        exact hs.v₂_not_mem (huv₂ ▸ huG)
      v₁_ne_v₂ := fun h => hs.v₁_ne_v₂ (hfV hv₁_mem hv₂_mem h)
      δ_disjoint := by
        refine disjoint_left.mpr fun _ ⟨e₁, he₁, h_eq₁⟩ ⟨e₂, he₂, h_eq₂⟩ => ?_
        have he₁₂ : e₁ = e₂ := hfE (hδ₁_sub he₁) (hδ₂_sub he₂) (h_eq₁.trans h_eq₂.symm)
        exact disjoint_left.mp hs.δ_disjoint he₁ (he₁₂ ▸ he₂)
      δ_union := by
        rw [← image_union, hs.δ_union]
        ext e'
        simp only [mem_image, incidentEdges, mem_ofPred_eq]
        constructor
        · rintro ⟨e, ⟨heG, hev⟩, rfl⟩
          exact ⟨⟨e, heG, rfl⟩, e, v, hev, rfl, rfl⟩
        · rintro ⟨_, e, w, hew, rfl, h_eq⟩
          have hwv : w = v := hfV (Or.inl (G.vertex_mem_of_inc hew)) hv_mem h_eq
          exact ⟨e, ⟨G.edge_mem_of_inc hew, hwv ▸ hew⟩, rfl⟩
      vertexSet_eq := by
        change fV '' G₁.vertexSet = (fV '' G.vertexSet \ {fV v}) ∪ {fV v₁, fV v₂}
        rw [hs.vertexSet_eq, image_union]
        congr 1
        · ext x
          simp only [mem_image, mem_sdiff, mem_singleton_iff]
          constructor
          · rintro ⟨u, ⟨huG, huv⟩, rfl⟩
            exact ⟨⟨u, huG, rfl⟩, fun h => huv (hfV (Or.inl huG) hv_mem h)⟩
          · rintro ⟨⟨u, huG, rfl⟩, h_ne⟩
            exact ⟨u, ⟨huG, fun huv => h_ne (congrArg fV huv)⟩, rfl⟩
        · ext x
          simp
      edgeSet_eq := by
        change fE '' G₁.edgeSet = fE '' G.edgeSet
        rw [hs.edgeSet_eq]
      inc_iff := by
        rintro _ ⟨e, heG₁, rfl⟩ _ ⟨u, huG₁, rfl⟩
        have heG : e ∈ G.edgeSet := hs.edgeSet_eq ▸ heG₁
        have hu_mem : u ∈ G.vertexSet ∪ {v₁, v₂} := hG₁_V_sub huG₁
        have h_inc1 : (mapHypergraph fV fE G₁).Inc (fE e) (fV u) ↔ G₁.Inc e u := by
          constructor
          · rintro ⟨e', u', h', he', hu'⟩
            have he_eq : e' = e := hfE (hs.edgeSet_eq ▸ G₁.edge_mem_of_inc h') heG he'
            have hu_eq : u' = u := hfV (hG₁_V_sub (G₁.vertex_mem_of_inc h')) hu_mem hu'
            rwa [← he_eq, ← hu_eq]
          · intro h
            exact ⟨e, u, h, rfl, rfl⟩
        have h_inc0 : (mapHypergraph fV fE G).Inc (fE e) (fV u) ↔ G.Inc e u := by
          constructor
          · rintro ⟨e', u', h', he', hu'⟩
            have he_eq : e' = e := hfE (G.edge_mem_of_inc h') heG he'
            have hu_eq : u' = u := hfV (Or.inl (G.vertex_mem_of_inc h')) hu_mem hu'
            rwa [← he_eq, ← hu_eq]
          · intro h
            exact ⟨e, u, h, rfl, rfl⟩
        have h_ne1 : fV u = fV v₁ ↔ u = v₁ :=
          ⟨fun h => hfV hu_mem hv₁_mem h, congrArg fV⟩
        have h_ne2 : fV u = fV v₂ ↔ u = v₂ :=
          ⟨fun h => hfV hu_mem hv₂_mem h, congrArg fV⟩
        have h_ne1' : fV u ≠ fV v₁ ↔ u ≠ v₁ := not_iff_not.mpr h_ne1
        have h_ne2' : fV u ≠ fV v₂ ↔ u ≠ v₂ := not_iff_not.mpr h_ne2
        have h_δ₁ : fE e ∈ fE '' δ₁ ↔ e ∈ δ₁ :=
          ⟨fun ⟨e', he', h⟩ => hfE (hδ₁_sub he') heG h ▸ he', mem_image_of_mem fE⟩
        have h_δ₂ : fE e ∈ fE '' δ₂ ↔ e ∈ δ₂ :=
          ⟨fun ⟨e', he', h⟩ => hfE (hδ₂_sub he') heG h ▸ he', mem_image_of_mem fE⟩
        rw [h_inc1, h_inc0, h_ne1', h_ne2', h_ne1, h_ne2, h_δ₁, h_δ₂]
        exact hs.inc_iff e heG₁ u huG₁ }

/-- Every splitting chain `ObtainedBySplittingOutsideLe U k G G'` is supported on a finite vertex
set `V_all` such that any vertex/edge map `(fV, fE)` injective on `V_all` and `G.edgeSet` that sends
`V_all \ U` outside `U'` transports the chain to `ObtainedBySplittingOutsideLe U' k`. -/
theorem exists_vertexSet_of_splittingOutsideLe {α : Type u} {β : Type v} {α' : Type w} {β' : Type*}
    {U : Set α} {k : ℕ} {G G' : Hypergraph α β}
    (h : ObtainedBySplittingOutsideLe U k G G') :
    G'.edgeSet = G.edgeSet ∧
    ∃ V_all : Set α,
      V_all.Finite ∧
      G.vertexSet ⊆ V_all ∧
      G'.vertexSet ⊆ V_all ∧
      ∀ (U' : Set α') (fV : α → α') (fE : β → β'),
        InjOn fV V_all →
        InjOn fE G.edgeSet →
        (∀ x ∈ V_all, x ∉ U → fV x ∉ U') →
        ObtainedBySplittingOutsideLe U' k (mapHypergraph fV fE G) (mapHypergraph fV fE G') := by
  induction h with
  | refl k G =>
    refine ⟨rfl, G.vertexSet, G.vertexSet_finite, Subset.rfl, Subset.rfl, fun U' fV fE _ _ _ => ?_⟩
    exact ObtainedBySplittingOutsideLe.refl k (mapHypergraph fV fE G)
  | @step k G G₁ G' v v₁ v₂ δ₁ δ₂ hs hv₁ hv₂ _ ih =>
    obtain ⟨hE_rest, V_rest, hV_rest_fin, hG₁_sub, hG'_sub, h_ih⟩ := ih
    let V_all : Set α := G.vertexSet ∪ {v₁, v₂} ∪ V_rest
    refine ⟨hE_rest.trans hs.edgeSet_eq, V_all,
      (G.vertexSet_finite.union (by simp)).union hV_rest_fin,
      subset_union_left.trans subset_union_left,
      hG'_sub.trans subset_union_right,
      fun U' fV fE hfV hfE h_out => ?_⟩
    have hfV_step : InjOn fV (G.vertexSet ∪ {v₁, v₂}) := hfV.mono subset_union_left
    have hs_map : IsVertexSplit (mapHypergraph fV fE G) (mapHypergraph fV fE G₁)
        (fV v) (fV v₁) (fV v₂) (fE '' δ₁) (fE '' δ₂) :=
      isVertexSplit_mapHypergraph hs hfV_step hfE
    have hfv₁ : fV v₁ ∉ U' := h_out v₁ (Or.inl (Or.inr (Or.inl rfl))) hv₁
    have hfv₂ : fV v₂ ∉ U' := h_out v₂ (Or.inl (Or.inr (Or.inr rfl))) hv₂
    have hfE_G₁ : InjOn fE G₁.edgeSet := hs.edgeSet_eq ▸ hfE
    have h_rest_map := h_ih U' fV fE (hfV.mono subset_union_right) hfE_G₁
      (fun x hx => h_out x (Or.inr hx))
    exact ObtainedBySplittingOutsideLe.step hs_map hfv₁ hfv₂ h_rest_map

/-- Given a finite set `K : Set α` and a finite forbidden set `U' : Set α'` in an infinite type
`α'`, there is a map `g : α → α'` that is injective on `K` and maps `K` outside `U'`. -/
theorem exists_injOn_compl_of_finite {α : Type u} {α' : Type w} [Infinite α']
    {K : Set α} (hK : K.Finite) {U' : Set α'} (hU' : U'.Finite) :
    ∃ g : α → α', InjOn g K ∧ ∀ x ∈ K, g x ∉ U' := by
  classical
  have h_finset : ∀ S : Finset α, ∃ g : α → α', InjOn g (S : Set α) ∧ ∀ x ∈ S, g x ∉ U' := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => Classical.arbitrary α', by simp, by simp⟩
    | @insert a S haS ih =>
      obtain ⟨g, hg_inj, hg_out⟩ := ih
      have hAvoid_fin : (U' ∪ g '' (S : Set α)).Finite := hU'.union (S.finite_toSet.image g)
      obtain ⟨y, hy_not⟩ := Infinite.exists_notMem_finset hAvoid_fin.toFinset
      have hy : y ∉ U' ∪ g '' (S : Set α) := by rwa [Set.Finite.mem_toFinset] at hy_not
      let g' : α → α' := fun x => if x = a then y else g x
      refine ⟨g', ?_, ?_⟩
      · intro x₁ hx₁ x₂ hx₂ h_eq
        rw [Finset.coe_insert, mem_insert_iff] at hx₁ hx₂
        by_cases h1 : x₁ = a <;> by_cases h2 : x₂ = a
        · exact h1.trans h2.symm
        · exfalso
          rcases hx₂ with hx₂_eq | hx₂_mem
          · exact h2 hx₂_eq
          · simp only [g', h1, h2, ↓reduceIte] at h_eq
            exact hy (Or.inr ⟨x₂, hx₂_mem, h_eq.symm⟩)
        · exfalso
          rcases hx₁ with hx₁_eq | hx₁_mem
          · exact h1 hx₁_eq
          · simp only [g', h1, h2, ↓reduceIte] at h_eq
            exact hy (Or.inr ⟨x₁, hx₁_mem, h_eq⟩)
        · rcases hx₁ with hx₁_eq | hx₁_mem
          · exact (h1 hx₁_eq).elim
          · rcases hx₂ with hx₂_eq | hx₂_mem
            · exact (h2 hx₂_eq).elim
            · simp only [g', h1, h2, ↓reduceIte] at h_eq
              exact hg_inj hx₁_mem hx₂_mem h_eq
      · intro x hx
        rw [Finset.mem_insert] at hx
        by_cases hx_eq : x = a
        · simp only [g', hx_eq, ↓reduceIte]
          exact fun h => hy (Or.inl h)
        · rcases hx with hx_a | hx_mem
          · exact (hx_eq hx_a).elim
          · simp only [g', hx_eq, ↓reduceIte]
            exact hg_out x hx_mem
  obtain ⟨g, hg_inj, hg_out⟩ := h_finset hK.toFinset
  rw [Set.Finite.coe_toFinset] at hg_inj
  refine ⟨g, hg_inj, fun x hx => hg_out x (hK.mem_toFinset.mpr hx)⟩

/-- Given `ObtainedBySplittingOutsideLe H₀.vertexSet k H₀ (mapHypergraph π' fE' G)` and an
embedding `(π_W, fE_W)` of `H₀` with `π_W '' H₀.vertexSet ⊆ U_S` where `U_S` is finite in an
infinite type `S`, we can relabel the split vertices outside `H₀.vertexSet` into `S \ U_S` so as
to obtain `π_tot : γ → S` with `InjOn π_tot G.vertexSet` and
`ObtainedBySplittingOutsideLe U_S k (mapHypergraph π_W fE_W H₀) (mapHypergraph π_tot (fE_W ∘ fE') G)`. -/
theorem exists_relabeled_splittingOutsideLe {α : Type u} {β : Type v} {γ : Type*} {δ : Type*}
    {S : Type w} {β' : Type*} [Infinite S]
    {k : ℕ} {H₀ : Hypergraph α β} {G : Hypergraph γ δ}
    {π' : γ → α} {fE' : δ → β}
    {π_W : α → S} {fE_W : β → β'} {U_S : Set S}
    (hπ'_inj : InjOn π' G.vertexSet)
    (hfE'_inj : InjOn fE' G.edgeSet)
    (hsplit : ObtainedBySplittingOutsideLe H₀.vertexSet k H₀ (mapHypergraph π' fE' G))
    (hπW_inj : InjOn π_W H₀.vertexSet)
    (hfEW_inj : InjOn fE_W H₀.edgeSet)
    (hH₀_sub : ∀ y ∈ H₀.vertexSet, π_W y ∈ U_S)
    (hUS_fin : U_S.Finite) :
    ∃ π_tot : γ → S,
      InjOn π_tot G.vertexSet ∧
      InjOn (fE_W ∘ fE') G.edgeSet ∧
      ObtainedBySplittingOutsideLe U_S k
        (mapHypergraph π_W fE_W H₀)
        (mapHypergraph π_tot (fE_W ∘ fE') G) ∧
      (∀ x ∈ G.vertexSet, π' x ∈ H₀.vertexSet → π_tot x = π_W (π' x)) ∧
      (∀ x ∈ G.vertexSet, π' x ∉ H₀.vertexSet → π_tot x ∉ U_S) := by
  classical
  obtain ⟨hE_eq, V_all, hV_all_fin, hH₀_V_sub, hG'_V_sub, h_map_split⟩ :=
    exists_vertexSet_of_splittingOutsideLe hsplit
  obtain ⟨g, hg_inj, hg_out⟩ :=
    exists_injOn_compl_of_finite (hV_all_fin.sdiff) hUS_fin
  let fV : α → S := fun y => if y ∈ H₀.vertexSet then π_W y else g y
  have hfV_inj : InjOn fV V_all := by
    intro y₁ hy₁ y₂ hy₂ h_eq
    by_cases h₁ : y₁ ∈ H₀.vertexSet <;> by_cases h₂ : y₂ ∈ H₀.vertexSet
    · simp only [fV, h₁, h₂, ↓reduceIte] at h_eq
      exact hπW_inj h₁ h₂ h_eq
    · simp only [fV, h₁, h₂, ↓reduceIte] at h_eq
      exfalso
      exact hg_out y₂ ⟨hy₂, h₂⟩ (h_eq ▸ hH₀_sub y₁ h₁)
    · simp only [fV, h₁, h₂, ↓reduceIte] at h_eq
      exfalso
      exact hg_out y₁ ⟨hy₁, h₁⟩ (h_eq.symm ▸ hH₀_sub y₂ h₂)
    · simp only [fV, h₁, h₂, ↓reduceIte] at h_eq
      exact hg_inj ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩ h_eq
  have hfV_out : ∀ y ∈ V_all, y ∉ H₀.vertexSet → fV y ∉ U_S := by
    intro y hy hy_not
    simp only [fV, hy_not, ↓reduceIte]
    exact hg_out y ⟨hy, hy_not⟩
  have h_map_H₀ : mapHypergraph fV fE_W H₀ = mapHypergraph π_W fE_W H₀ := by
    refine Hypergraph.ext (Set.ext fun s => ?_) (Set.ext fun _ => Iff.rfl)
      (funext fun e => funext fun s => propext ?_)
    · change s ∈ fV '' H₀.vertexSet ↔ s ∈ π_W '' H₀.vertexSet
      simp only [mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [fV, hy, ↓reduceIte]
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        simp only [fV, hy, ↓reduceIte]
    · change (∃ e' y, H₀.Inc e' y ∧ fE_W e' = e ∧ fV y = s) ↔
        ∃ e' y, H₀.Inc e' y ∧ fE_W e' = e ∧ π_W y = s
      constructor
      · rintro ⟨e', y, hinc, rfl, rfl⟩
        have hy : y ∈ H₀.vertexSet := H₀.vertex_mem_of_inc hinc
        simp only [fV, hy, ↓reduceIte]
        exact ⟨e', y, hinc, rfl, rfl⟩
      · rintro ⟨e', y, hinc, rfl, rfl⟩
        have hy : y ∈ H₀.vertexSet := H₀.vertex_mem_of_inc hinc
        refine ⟨e', y, hinc, rfl, ?_⟩
        simp only [fV, hy, ↓reduceIte]
  have h_map_G : mapHypergraph fV fE_W (mapHypergraph π' fE' G) =
      mapHypergraph (fV ∘ π') (fE_W ∘ fE') G := by
    refine Hypergraph.ext (Set.ext fun s => ?_) (Set.ext fun e => ?_)
      (funext fun e => funext fun s => propext ?_)
    · change s ∈ fV '' (π' '' G.vertexSet) ↔ s ∈ (fV ∘ π') '' G.vertexSet
      rw [image_image]
      rfl
    · change e ∈ fE_W '' (fE' '' G.edgeSet) ↔ e ∈ (fE_W ∘ fE') '' G.edgeSet
      rw [image_image]
      rfl
    · change (∃ e₁ y₁, (∃ e₀ x₀, G.Inc e₀ x₀ ∧ fE' e₀ = e₁ ∧ π' x₀ = y₁) ∧
          fE_W e₁ = e ∧ fV y₁ = s) ↔
        ∃ e₀ x₀, G.Inc e₀ x₀ ∧ (fE_W ∘ fE') e₀ = e ∧ (fV ∘ π') x₀ = s
      constructor
      · rintro ⟨_, _, ⟨e₀, x₀, hinc, rfl, rfl⟩, rfl, rfl⟩
        exact ⟨e₀, x₀, hinc, rfl, rfl⟩
      · rintro ⟨e₀, x₀, hinc, rfl, rfl⟩
        exact ⟨fE' e₀, π' x₀, ⟨e₀, x₀, hinc, rfl, rfl⟩, rfl, rfl⟩
  have h_split_S := h_map_split U_S fV fE_W hfV_inj hfEW_inj hfV_out
  rw [h_map_H₀, h_map_G] at h_split_S
  have hπ_tot_inj : InjOn (fV ∘ π') G.vertexSet := by
    intro x₁ hx₁ x₂ hx₂ h_eq
    have hx₁_all : π' x₁ ∈ V_all := hG'_V_sub (mem_image_of_mem π' hx₁)
    have hx₂_all : π' x₂ ∈ V_all := hG'_V_sub (mem_image_of_mem π' hx₂)
    exact hπ'_inj hx₁ hx₂ (hfV_inj hx₁_all hx₂_all h_eq)
  have hfE_tot_inj : InjOn (fE_W ∘ fE') G.edgeSet := by
    have hfE'_E : ∀ e ∈ G.edgeSet, fE' e ∈ H₀.edgeSet := by
      intro e he
      have h_mem : fE' e ∈ (mapHypergraph π' fE' G).edgeSet := mem_image_of_mem fE' he
      rwa [hE_eq] at h_mem
    intro e₁ he₁ e₂ he₂ h_eq
    exact hfE'_inj he₁ he₂ (hfEW_inj (hfE'_E e₁ he₁) (hfE'_E e₂ he₂) h_eq)
  refine ⟨fV ∘ π', hπ_tot_inj, hfE_tot_inj, h_split_S, ?_, ?_⟩
  · intro x _ hx
    simp only [Function.comp_apply, fV, hx, ↓reduceIte]
  · intro x hx hx_not
    simp only [Function.comp_apply]
    exact hfV_out (π' x) (hG'_V_sub (mem_image_of_mem π' hx)) hx_not

/-- Unified two-disc and line-cutting contradiction lemma for Claim (10):
Suppose `(A, B) ∈ 𝒯` has `separationOrder A B ≤ θ₄` with
`B = (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)` for a closed set `K_B ⊆ S₀`, and we
have two disjoint closed discs `Δ₁, Δ₂ ⊆ S₀`, a set of remaining cuffs `CuffsRest ⊆ cuffs S` with
`CuffsRest.ncard + 2 ≤ (cuffs S).ncard` whose open cuff discs are disjoint from `Δ₁` and `Δ₂`,
and a line `L₀ ⊆ S₀` with ends `a₀ ∈ discBd Δ₁` and `b₀ ∈ discBd Δ₂` such that:
- `(capDrawing hS cap Γ).U ∩ K_B ⊆ (discInt Δ₁ ∪ discInt Δ₂)ᶜ`,
- `(discBd Δ₁ ∪ discBd Δ₂) ∩ ((capDrawing hS cap Γ).U ∩ K_B) ⊆ (capDrawing hS cap Γ).V`,
- `L₀ \ {a₀, b₀} ⊆ (Δ₁ ∪ Δ₂ ∪ ⋃ c ∈ CuffsRest, cap.cuffDisc c)ᶜ`,
- `L₀ ∩ ((capDrawing hS cap Γ).U ∩ K_B) ⊆ (capDrawing hS cap Γ).V`, and
- `(L₀ ∩ ((capDrawing hS cap Γ).V ∩ K_B)).ncard ≤ θ₄`,
- for every `v ∈ B.vertexSet` with `cap.emb v ∉ L₀`,
  `cap.emb v ∈ discBd Δ₁ ∪ discBd Δ₂ ∪ (⋃ c ∈ CuffsRest, cap.emb '' c) ↔
    v ∈ (A ∩ B).vertexSet ∨ v ∈ Γ.V ∩ bd S`.
Then Claim (6) (`apply_claim_5_2_6_of_drawing`) yields `False`. -/
theorem contradiction_of_two_discs_and_line {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L A B : Hypergraph S (Set S)}
    {K_B Δ₁ Δ₂ L₀ : Set S₀} {a₀ b₀ : S₀}
    {CuffsRest : Set (Set S)}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ_loopless : ∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard)
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (h_ind2 : ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
      IsSurface S' → [ConnectedSpace S'] →
      GM19.IsCappedSurface S' Shat' →
      Nonempty (Shat' ≃ₜ S₀) →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₂ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → [ConnectedSpace S'] →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₃ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (hKB : IsClosed K_B)
    (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B ≤ θ₄)
    (hB_eq : B = (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B))
    (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂) (hdisj_12 : Disjoint Δ₁ Δ₂)
    (hCuffsRest_sub : CuffsRest ⊆ cuffs S)
    (hCuffsRest_card : CuffsRest.ncard + 2 ≤ (cuffs S).ncard)
    (hdisj_c1 : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) Δ₁)
    (hdisj_c2 : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) Δ₂)
    (hKB_W : (capDrawing hS cap Γ).U ∩ K_B ⊆ (discInt Δ₁ ∪ discInt Δ₂)ᶜ)
    (hW_bd_norm :
      (discBd Δ₁ ∪ discBd Δ₂) ∩
        ((capDrawing hS cap Γ).U ∩ K_B) ⊆ (capDrawing hS cap Γ).V)
    (hL₀ : IsLineWithEnds L₀ a₀ b₀)
    (ha₀ : a₀ ∈ discBd Δ₁) (hb₀ : b₀ ∈ discBd Δ₂)
    (hL₀_int : L₀ \ {a₀, b₀} ⊆ (Δ₁ ∪ Δ₂ ∪ ⋃ c ∈ CuffsRest, cap.cuffDisc c)ᶜ)
    (hL₀_norm : L₀ ∩ ((capDrawing hS cap Γ).U ∩ K_B) ⊆ (capDrawing hS cap Γ).V)
    (hL₀_card : (L₀ ∩ ((capDrawing hS cap Γ).V ∩ K_B)).ncard ≤ θ₄)
    (hbd_V : ∀ v ∈ B.vertexSet, cap.emb v ∉ L₀ →
      (cap.emb v ∈ discBd Δ₁ ∪ discBd Δ₂ ∪ (⋃ c ∈ CuffsRest, cap.emb '' c) ↔
        v ∈ (A ∩ B).vertexSet ∨ v ∈ Γ.V ∩ bd S)) :
    False := by
  classical
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : CompactSpace S₀ := hS₀.1
  haveI : T2Space S₀ := hS₀.2.1
  haveI : ConnectedSpace S₀ := cap.connected
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hcuffs_ne : (cuffs S).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨C₀_S, hC₀_S⟩ := hcuffs_ne
  haveI : Infinite S := infinite_of_isOArc ((cuff_statement S hS).2.2 C₀_S hC₀_S)
  have hCuffsRest_fin : CuffsRest.Finite := hcuffs_fin.subset hCuffsRest_sub
  haveI : Finite CuffsRest := hCuffsRest_fin.to_subtype
  -- Shrink each cuff disc `closure (cap.cuffDisc c)` so its boundary only meets `range cap.emb`
  -- at vertices of `Γ.V` on `c` outside `Δ₁ ∪ Δ₂ ∪ L₀`.
  let Avoid : Set S := cap.emb ⁻¹' (Δ₁ ∪ Δ₂ ∪ L₀)
  have h_shrunk : ∀ c : CuffsRest, ∃ P_c : Set S₀,
      P_c ⊆ closure (cap.cuffDisc c.1) ∧
      IsClosedDisc P_c ∧
      P_c ⊆ cap.cuffDisc c.1 ∪ cap.emb '' ((c.1 ∩ Γ.V) \ Avoid) ∧
      discInt P_c ⊆ cap.cuffDisc c.1 ∧
      cap.emb '' ((c.1 ∩ Γ.V) \ Avoid) ⊆ discBd P_c := by
    intro c
    have hE_disc : IsClosedDisc (closure (cap.cuffDisc c.1)) :=
      cap.cuffDisc_closedDisc c.1 (hCuffsRest_sub c.2)
    have hE_bd : discBd (closure (cap.cuffDisc c.1)) = cap.emb '' c.1 :=
      cap.cuffDisc_bd c.1 (hCuffsRest_sub c.2)
    have hE_int : discInt (closure (cap.cuffDisc c.1)) = cap.cuffDisc c.1 :=
      (cap.cuffDisc_eq_discInt hS (hCuffsRest_sub c.2)).symm
    have hA_fin : (cap.emb '' ((c.1 ∩ Γ.V) \ Avoid)).Finite :=
      ((Γ.finite_V.subset inter_subset_right).sdiff).image cap.emb
    have hA_sub : cap.emb '' ((c.1 ∩ Γ.V) \ Avoid) ⊆ discBd (closure (cap.cuffDisc c.1)) := by
      rw [hE_bd]
      exact image_mono (sdiff_subset.trans inter_subset_left)
    obtain ⟨P_c, hP_sub, hP_disc, hP_int_A, hP_int, hP_bd⟩ :=
      exists_subdisc_fixing_bd_subset hE_disc hA_fin hA_sub
    rw [hE_int] at hP_int_A hP_int
    exact ⟨P_c, hP_sub, hP_disc, hP_int_A, hP_int, hP_bd⟩
  choose P_c hP_c_sub_cl hP_c_disc hP_c_sub_union hP_c_int hP_c_bd using h_shrunk
  -- Index the family of removed closed discs by `Bool ⊕ CuffsRest`.
  let P : Bool ⊕ CuffsRest → Set S₀ := fun i =>
    match i with
    | Sum.inl true => Δ₁
    | Sum.inl false => Δ₂
    | Sum.inr c => P_c c
  have hP_disc : ∀ i : Bool ⊕ CuffsRest, IsClosedDisc (P i) := by
    rintro ((_ | _) | c)
    · exact hΔ₂
    · exact hΔ₁
    · exact hP_c_disc c
  have hP_disj_1 : ∀ c : CuffsRest, Disjoint (P_c c) Δ₁ := by
    intro c
    refine disjoint_left.mpr fun x hxP hx1 => ?_
    rcases hP_c_sub_union c hxP with hx_open | ⟨u, ⟨_, hu_not⟩, rfl⟩
    · exact disjoint_left.mp (hdisj_c1 c.1 c.2) hx_open hx1
    · exact hu_not (Or.inl (Or.inl hx1))
  have hP_disj_2 : ∀ c : CuffsRest, Disjoint (P_c c) Δ₂ := by
    intro c
    refine disjoint_left.mpr fun x hxP hx2 => ?_
    rcases hP_c_sub_union c hxP with hx_open | ⟨u, ⟨_, hu_not⟩, rfl⟩
    · exact disjoint_left.mp (hdisj_c2 c.1 c.2) hx_open hx2
    · exact hu_not (Or.inl (Or.inr hx2))
  have hP_disj : Pairwise fun i j : Bool ⊕ CuffsRest => Disjoint (P i) (P j) := by
    rintro ((_ | _) | c₁) ((_ | _) | c₂) hij
    · exact (hij rfl).elim
    · exact hdisj_12.symm
    · exact (hP_disj_2 c₂).symm
    · exact hdisj_12
    · exact (hij rfl).elim
    · exact (hP_disj_1 c₂).symm
    · exact hP_disj_2 c₁
    · exact hP_disj_1 c₁
    · have hne : c₁.1 ≠ c₂.1 := fun h => hij (congrArg Sum.inr (Subtype.ext h))
      exact (cap.cuffDisc_disjoint c₁.1 (hCuffsRest_sub c₁.2) c₂.1 (hCuffsRest_sub c₂.2) hne).mono
        (hP_c_sub_cl c₁) (hP_c_sub_cl c₂)
  obtain ⟨_, hW_surf, hW_bd, hW_conn, hW_cuffs⟩ :=
    Surface.remove_discs hS₀ hcl₀.2.2 hP_disc hP_disj
  obtain ⟨capW⟩ := GM19.nonempty_capped_of_removal hcl₀ hP_disc hP_disj
  let W : Set S₀ := (⋃ i : Bool ⊕ CuffsRest, discInt (P i))ᶜ
  haveI : ConnectedSpace ↥W := hW_conn
  haveI : T2Space ↥W := hW_surf.2.1
  have hKB_sub_W : (capDrawing hS cap Γ).U ∩ K_B ⊆ W := by
    rintro x ⟨hxU, hxKB⟩ hx_bad
    have hx_not12 : x ∉ discInt Δ₁ ∪ discInt Δ₂ := hKB_W ⟨hxU, hxKB⟩
    rcases mem_iUnion.mp hx_bad with ⟨(_ | _) | c, hxc⟩
    · exact hx_not12 (Or.inr hxc)
    · exact hx_not12 (Or.inl hxc)
    · have hx_open : x ∈ cap.cuffDisc c.1 := hP_c_int c hxc
      have hx_compl : x ∈ (range cap.emb)ᶜ := by
        rw [cap.compl_eq]
        exact mem_iUnion₂.mpr ⟨c.1, hCuffsRest_sub c.2, hx_open⟩
      rcases hxU with ⟨s, _, rfl⟩
      exact hx_compl (mem_range_self s)
  have hbd_union_sub :
      (⋃ i : Bool ⊕ CuffsRest, discBd (P i)) ⊆
        discBd Δ₁ ∪ discBd Δ₂ ∪
          ⋃ c : CuffsRest, (cap.cuffDisc c.1 ∪ cap.emb '' ((c.1 ∩ Γ.V) \ Avoid)) := by
    rintro x hx
    rcases mem_iUnion.mp hx with ⟨(_ | _) | c, hxc⟩
    · exact Or.inl (Or.inr hxc)
    · exact Or.inl (Or.inl hxc)
    · exact Or.inr (mem_iUnion.mpr ⟨c, hP_c_sub_union c (Surface.discBd_subset _ hxc)⟩)
  have hbW : ∀ i : Bool ⊕ CuffsRest, ∀ x ∈ discBd (P i), x ∈ W := fun i x hx hu => by
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    by_cases hij : i = j
    · subst hij
      exact hj.2 hx
    · exact Set.disjoint_left.mp (hP_disj hij) (Surface.discBd_subset _ hx) hj.1
  have hinj_cuff : Function.Injective
      (fun i : Bool ⊕ CuffsRest => (Subtype.val ⁻¹' discBd (P i) : Set ↥W)) := by
    intro i j he
    by_contra hij
    obtain ⟨y, hy⟩ := (IsOArc.isConnected' (hP_disc i).isOArc_discBd).nonempty
    have h1 : (⟨y, hbW i y hy⟩ : ↥W) ∈ (Subtype.val ⁻¹' discBd (P j) : Set ↥W) := by
      dsimp only at he
      have hmem : (⟨y, hbW i y hy⟩ : ↥W) ∈ (Subtype.val ⁻¹' discBd (P i) : Set ↥W) := hy
      rwa [he] at hmem
    exact Set.disjoint_left.mp (hP_disj hij)
      (Surface.discBd_subset _ hy) (Surface.discBd_subset _ h1)
  have hcuffs_W : (cuffs ↥W).ncard = CuffsRest.ncard + 2 := by
    haveI : Fintype CuffsRest := hCuffsRest_fin.fintype
    rw [hW_cuffs, ← image_univ, Set.ncard_image_of_injective univ hinj_cuff,
      ncard_univ, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_bool,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, add_comm]
  -- Obtain the subspace drawing `Γ_W : Drawing ↥W` of `B`.
  obtain ⟨Γ_W, π_W, fE_W, hπW_inj, hfEW_inj, h_mapW, hπW_spec, hUW_spec⟩ :=
    exists_subspace_drawing_of_closed_subset hS cap Γ hKB hKB_sub_W
  have hΓW_prop : Γ_W.IsProper := by
    rintro y ⟨hy_bd, hy_U⟩
    obtain ⟨hy_embU, hy_KB, h_to_V⟩ := hUW_spec y hy_U
    apply h_to_V
    rw [hW_bd, mem_preimage] at hy_bd
    rcases hbd_union_sub hy_bd with hy12 | hy_c
    · exact hW_bd_norm ⟨hy12, hy_embU, hy_KB⟩
    · rcases mem_iUnion.mp hy_c with ⟨c, hy_open | ⟨u, ⟨⟨_, hu_V⟩, _⟩, h_eq⟩⟩
      · exfalso
        have hy_compl : (y : S₀) ∈ (range cap.emb)ᶜ := by
          rw [cap.compl_eq]
          exact mem_iUnion₂.mpr ⟨c.1, hCuffsRest_sub c.2, hy_open⟩
        rcases hy_embU with ⟨s, _, hs_eq⟩
        exact hy_compl ⟨s, hs_eq⟩
      · exact ⟨u, hu_V, h_eq⟩
  have hΓW_loopless : ∀ e' ∈ Γ_W.E, 2 ≤ (Γ_W.toHypergraph.ends e').ncard := by
    intro e' he'
    have h_card : ((mapHypergraph π_W fE_W Γ_W.toHypergraph).ends (fE_W e')).ncard =
        (Γ_W.toHypergraph.ends e').ncard :=
      ends_mapHypergraph_ncard (le_refl Γ_W.toHypergraph) hπW_inj hfEW_inj he'
    rw [← h_card, h_mapW, ← hB_eq]
    have hB_le : B ≤ Γ.toHypergraph :=
      hB_eq ▸ GM11.inter_le (Γ := PaintingOrDrawing.drawing Γ)
        (hKB.preimage cap.isEmbedding.continuous)
    have hfE_B : fE_W e' ∈ B.edgeSet := by
      rw [hB_eq, ← h_mapW]
      exact mem_image_of_mem fE_W he'
    rw [← hB_le.ends_eq (fE_W e') hfE_B]
    exact hΓ_loopless (fE_W e') (hB_le.edgeSet_subset hfE_B)
  -- Pull back `L₀` to a proper line `F_W` in `↥W` between the two distinct cuffs `discBd Δ₁` and `discBd Δ₂`.
  have hL₀_sub_W : L₀ ⊆ W := by
    intro x hxL₀
    by_cases hxa : x = a₀
    · subst hxa; exact hbW (Sum.inl true) x ha₀
    · by_cases hxb : x = b₀
      · subst hxb; exact hbW (Sum.inl false) x hb₀
      · have hx_int := hL₀_int ⟨hxL₀, fun h => h.elim hxa hxb⟩
        intro hx_bad
        apply hx_int
        rcases mem_iUnion.mp hx_bad with ⟨(_ | _) | c, hxc⟩
        · exact Or.inl (Or.inr (Surface.discInt_subset Δ₂ hxc))
        · exact Or.inl (Or.inl (Surface.discInt_subset Δ₁ hxc))
        · exact Or.inr (mem_iUnion₂.mpr ⟨c.1, c.2, hP_c_int c hxc⟩)
  let F_W : Set ↥W := Subtype.val ⁻¹' L₀
  let a_W : ↥W := ⟨a₀, hbW (Sum.inl true) a₀ ha₀⟩
  let b_W : ↥W := ⟨b₀, hbW (Sum.inl false) b₀ hb₀⟩
  have hFW_line : IsLineWithEnds F_W a_W b_W := by
    rcases id hL₀ with ⟨φ, hφ0, hφ1⟩
    let ψ_line : 𝕀 ≃ₜ F_W :=
      { toFun := fun t => ⟨⟨(φ t).1, hL₀_sub_W (φ t).2⟩, (φ t).2⟩
        invFun := fun y => φ.symm ⟨y.1.1, y.2⟩
        left_inv := fun t => by simp
        right_inv := fun y => by ext; simp
        continuous_toFun := Continuous.subtype_mk
          (Continuous.subtype_mk (continuous_subtype_val.comp φ.continuous) _) _
        continuous_invFun := φ.symm.continuous.comp
          (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) }
    exact ⟨ψ_line, Subtype.ext hφ0, Subtype.ext hφ1⟩
  have hFW_bd : F_W ∩ bd ↥W = {a_W, b_W} := by
    apply Subset.antisymm
    · rintro ⟨x, hxW⟩ ⟨hxL₀, hx_bd⟩
      by_contra hx_ne
      have hx_ab : x ∉ ({a₀, b₀} : Set S₀) := by
        rintro (rfl | rfl)
        · exact hx_ne (Or.inl rfl)
        · exact hx_ne (Or.inr rfl)
      have hx_out := hL₀_int ⟨hxL₀, hx_ab⟩
      rw [hW_bd, mem_preimage] at hx_bd
      rcases hbd_union_sub hx_bd with (hx1 | hx2) | hx_c
      · exact hx_out (Or.inl (Or.inl (Surface.discBd_subset Δ₁ hx1)))
      · exact hx_out (Or.inl (Or.inr (Surface.discBd_subset Δ₂ hx2)))
      · rcases mem_iUnion.mp hx_c with ⟨c, hx_open | ⟨u, ⟨_, hu_not⟩, rfl⟩⟩
        · exact hx_out (Or.inr (mem_iUnion₂.mpr ⟨c.1, c.2, hx_open⟩))
        · exact hu_not (Or.inr hxL₀)
    · rintro y (rfl | rfl)
      · refine ⟨hL₀.left_mem, ?_⟩
        rw [hW_bd, mem_preimage]
        exact mem_iUnion.mpr ⟨Sum.inl true, ha₀⟩
      · refine ⟨hL₀.right_mem, ?_⟩
        rw [hW_bd, mem_preimage]
        exact mem_iUnion.mpr ⟨Sum.inl false, hb₀⟩
  have hFW_norm : (PaintingOrDrawing.drawing Γ_W).IsNormal F_W := by
    rintro y ⟨hyF, hyU⟩
    obtain ⟨hy_embU, hy_KB, h_to_V⟩ := hUW_spec y hyU
    exact h_to_V (hL₀_norm ⟨hyF, hy_embU, hy_KB⟩)
  have hFW_card : (F_W ∩ Γ_W.V).ncard ≤ θ₄ := by
    have h_sub : (Subtype.val : ↥W → S₀) '' (F_W ∩ Γ_W.V) ⊆
        L₀ ∩ ((capDrawing hS cap Γ).V ∩ K_B) := by
      rintro _ ⟨y, ⟨hyF, hyV⟩, rfl⟩
      obtain ⟨h_emb_π, hπ_V, hy_KB⟩ := hπW_spec y hyV
      exact ⟨hyF, ⟨⟨π_W y, hπ_V, h_emb_π⟩, hy_KB⟩⟩
    have h_fin : (L₀ ∩ ((capDrawing hS cap Γ).V ∩ K_B)).Finite :=
      ((capDrawing hS cap Γ).finite_V.subset inter_subset_left).subset inter_subset_right
    rw [← (Subtype.val_injective.injOn).ncard_image]
    exact (ncard_le_ncard h_sub h_fin).trans hL₀_card
  let C₁_W : Set ↥W := Subtype.val ⁻¹' discBd Δ₁
  let C₂_W : Set ↥W := Subtype.val ⁻¹' discBd Δ₂
  have hC₁_W : C₁_W ∈ cuffs ↥W := by
    rw [hW_cuffs]
    exact ⟨Sum.inl true, rfl⟩
  have hC₂_W : C₂_W ∈ cuffs ↥W := by
    rw [hW_cuffs]
    exact ⟨Sum.inl false, rfl⟩
  have hC12_ne : C₁_W ≠ C₂_W := by
    intro h
    have h_eq : Sum.inl true = (Sum.inl false : Bool ⊕ CuffsRest) := hinj_cuff h
    exact nomatch h_eq
  -- Cut `↥W` along `F_W` using `cutIArc` and `theorem_4_1_proof`.
  obtain ⟨f_line, _, _⟩ := id hFW_line
  haveI : Infinite ↥W := infinite_of_isLine ⟨f_line⟩
  have ha_C₁ : a_W ∈ C₁_W := ha₀
  have hb_C₂ : b_W ∈ C₂_W := hb₀
  have hcomp_a : connectedComponentIn (bd ↥W) a_W = C₁_W := by
    rcases hC₁_W with ⟨z, _, hz⟩
    rw [← hz]
    refine (connectedComponentIn_eq ?_).symm
    rwa [hz]
  have hcomp_b : connectedComponentIn (bd ↥W) b_W = C₂_W := by
    rcases hC₂_W with ⟨z, _, hz⟩
    rw [← hz]
    refine (connectedComponentIn_eq ?_).symm
    rwa [hz]
  have hdiff : connectedComponentIn (bd ↥W) a_W ≠ connectedComponentIn (bd ↥W) b_W := by
    rw [hcomp_a, hcomp_b]
    exact hC12_ne
  have h_proper_FW : IsProperLineInSurface F_W a_W b_W := by
    refine ⟨hFW_line, ((Set.ext_iff.mp hFW_bd a_W).mpr (Or.inl rfl)).2,
      ((Set.ext_iff.mp hFW_bd b_W).mpr (Or.inr rfl)).2,
      disjoint_left.mpr fun y ⟨hyF, hy_ab⟩ hy_bd => ?_⟩
    exact hy_ab ((Set.ext_iff.mp hFW_bd y).mp ⟨hyF, hy_bd⟩)
  obtain ⟨W', tW', ψ, hW'_surf, hcut_W, h_iarc, -, -⟩ :=
    cutIArc ↥W F_W a_W b_W hW_surf inferInstance h_proper_FW.ne h_proper_FW.inter_bd_eq h_proper_FW.1
  letI := tW'
  obtain ⟨hW'_conn, -⟩ := h_iarc hdiff
  letI := hW'_conn
  haveI : T2Space W' := hW'_surf.2.1
  obtain ⟨W'hat, tW'hat, ⟨capW'⟩⟩ := exists_cappedSurface _ W' hW'_surf inferInstance rfl
  letI := tW'hat
  obtain ⟨hhat, hcuffs_W'⟩ :=
    (theorem_4_1_proof hW_surf hW'_surf hcut_W capW capW').1 a_W b_W C₁_W C₂_W
      hC₁_W hC₂_W hC12_ne ha_C₁ hb_C₂ h_proper_FW
  have hFW_closed : IsClosed F_W := hFW_line.isCompact.isClosed
  -- Lift `Γ_W` across `hcut_W` using `exists_lifted_drawing_of_isCutting`.
  obtain ⟨Γ', π', fE', hΓ'_eq, hπ'_inj, hfE'_inj, hsplit_W, hπ'_out, hπ'_in⟩ :=
    exists_lifted_drawing_of_isCutting hW'_surf hW_surf hcut_W hFW_closed
      Γ_W hΓW_loopless hFW_norm Γ_W.finite_V
  subst hΓ'_eq
  have hΓ'_prop : (liftDrawing hW'_surf hW_surf hcut_W hFW_closed Γ_W hΓW_loopless hFW_norm).IsProper :=
    liftDrawing_isProper hW'_surf hW_surf hcut_W hFW_closed Γ_W hΓW_loopless hFW_norm hΓW_prop
  have hsplit_W_θ₄ :
      ObtainedBySplittingOutsideLe Γ_W.V θ₄ Γ_W.toHypergraph
        (mapHypergraph π' fE'
          (liftDrawing hW'_surf hW_surf hcut_W hFW_closed Γ_W hΓW_loopless hFW_norm).toHypergraph) :=
    hsplit_W.mono hFW_card
  obtain ⟨π_tot, hπ_tot_inj, hfE_tot_inj, hsplit_S, hπ_tot_in, hπ_tot_out⟩ :=
    exists_relabeled_splittingOutsideLe (H₀ := Γ_W.toHypergraph)
      hπ'_inj hfE'_inj hsplit_W_θ₄
      hπW_inj hfEW_inj (fun y hy => (hπW_spec y hy).2.1) Γ.finite_V
  rw [h_mapW, ← hB_eq] at hsplit_S
  have h6b : ∀ x ∈ (liftDrawing hW'_surf hW_surf hcut_W hFW_closed Γ_W hΓW_loopless hFW_norm).V,
      x ∈ bd W' ↔
        π_tot x ∈ (A ∩ B).vertexSet ∨ π_tot x ∈ Γ.V ∩ bd S ∨ π_tot x ∉ Γ.V := by
    intro x hxV
    have hbd_W := bd_iff_of_lifted_drawing hW'_surf hW_surf hcut_W hFW_closed
      Subset.rfl rfl hπ'_out hπ'_in x hxV
    change x ∈ bd W' ↔ π' x ∈ Γ_W.V ∩ bd ↥W ∨ π' x ∉ Γ_W.V at hbd_W
    have hψx_V : ψ x ∈ Γ_W.V := hxV
    by_cases hψx_F : ψ x ∈ F_W
    · have hx_bd : x ∈ bd W' := hcut_W.2.2.2.2 hψx_F
      have hπ'_not : π' x ∉ Γ_W.V := fun h => hπ'_in x hxV hψx_F (Or.inl h)
      have hπ_tot_not : π_tot x ∉ Γ.V := hπ_tot_out x hxV hπ'_not
      exact ⟨fun _ => Or.inr (Or.inr hπ_tot_not), fun _ => hx_bd⟩
    · have hπ'_eq : π' x = ψ x := hπ'_out x hxV hψx_F
      have hπ'_mem : π' x ∈ Γ_W.V := hπ'_eq ▸ hψx_V
      have hπ_tot_eq : π_tot x = π_W (ψ x) := by
        rw [hπ_tot_in x hxV hπ'_mem, hπ'_eq]
      obtain ⟨h_emb_π, hπ_V, hy_KB⟩ := hπW_spec (ψ x) hψx_V
      have hπ_B : π_W (ψ x) ∈ B.vertexSet := by
        rw [hB_eq, ← h_mapW]
        exact mem_image_of_mem π_W hψx_V
      have h_not_L₀ : cap.emb (π_W (ψ x)) ∉ L₀ := by
        rw [h_emb_π]
        exact hψx_F
      have h_not_int12 : cap.emb (π_W (ψ x)) ∉ discInt Δ₁ ∪ discInt Δ₂ := by
        apply hKB_W
        rw [h_emb_π]
        exact ⟨⟨π_W (ψ x), Γ.V_subset_U hπ_V, h_emb_π⟩, hy_KB⟩
      have h_bd_ψ : ψ x ∈ bd ↥W ↔
          cap.emb (π_W (ψ x)) ∈ discBd Δ₁ ∪ discBd Δ₂ ∪ ⋃ c ∈ CuffsRest, cap.emb '' c := by
        rw [hW_bd, mem_preimage, ← h_emb_π]
        constructor
        · intro hx_u
          rcases hbd_union_sub hx_u with hx12 | hx_c
          · exact Or.inl hx12
          · rcases mem_iUnion.mp hx_c with ⟨c, hx_open | ⟨u, ⟨⟨hu_c, _⟩, _⟩, h_eq⟩⟩
            · exfalso
              have hx_compl : cap.emb (π_W (ψ x)) ∈ (range cap.emb)ᶜ := by
                rw [cap.compl_eq]
                exact mem_iUnion₂.mpr ⟨c.1, hCuffsRest_sub c.2, hx_open⟩
              exact hx_compl (mem_range_self _)
            · exact Or.inr (mem_iUnion₂.mpr ⟨c.1, c.2, u, hu_c, h_eq⟩)
        · rintro ((hx1 | hx2) | hx_c)
          · exact mem_iUnion.mpr ⟨Sum.inl true, hx1⟩
          · exact mem_iUnion.mpr ⟨Sum.inl false, hx2⟩
          · rcases mem_iUnion₂.mp hx_c with ⟨c, hc, u, hu_c, h_eq⟩
            have hu_eq : u = π_W (ψ x) := cap.isEmbedding.injective h_eq
            by_cases h_in12 : cap.emb (π_W (ψ x)) ∈ Δ₁ ∪ Δ₂
            · rcases h_in12 with h1 | h2
              · refine mem_iUnion.mpr ⟨Sum.inl true, ?_⟩
                by_contra h_not_bd1
                exact h_not_int12 (Or.inl ⟨h1, h_not_bd1⟩)
              · refine mem_iUnion.mpr ⟨Sum.inl false, ?_⟩
                by_contra h_not_bd2
                exact h_not_int12 (Or.inr ⟨h2, h_not_bd2⟩)
            · refine mem_iUnion.mpr ⟨Sum.inr ⟨c, hc⟩, hP_c_bd ⟨c, hc⟩ ?_⟩
              refine ⟨π_W (ψ x), ⟨⟨hu_eq ▸ hu_c, hπ_V⟩, ?_⟩, rfl⟩
              rintro (h12 | hL)
              · exact h_in12 h12
              · exact h_not_L₀ hL
      rw [hbd_W, mem_inter_iff, hπ'_eq, hπ_tot_eq]
      simp only [hψx_V, true_and, not_true_eq_false, or_false]
      rw [h_bd_ψ, hbd_V (π_W (ψ x)) hπ_B h_not_L₀]
      simp only [hπ_V, not_true_eq_false, or_false]
  have h6 := apply_claim_5_2_6_of_drawing hS hW'_surf cap capW' hΓ_bd h𝒯 hL hL_bd hAB hord
    hπ_tot_inj hfE_tot_inj hsplit_S hhat h6b hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos
    (fun hlt_c hle_bd T' L' hT' hL' =>
      h_ind2 W' W'hat hW'_surf capW' hhat hlt_c _ hΓ'_prop hle_bd T' L' hT' hL')
    (fun hhomeo hlt_bd T' L' hT' hL' =>
      h_ind3 W' hW'_surf hhomeo _ hΓ'_prop hlt_bd T' L' hT' hL')
  have h_le := h6.1
  change (cuffs W').ncard + 1 = (cuffs ↥W).ncard at hcuffs_W'
  omega

/-- Single-disc counterpart of `contradiction_of_two_discs_and_line`: if a single closed disc `Δ`
and a family `CuffsRest ⊆ cuffs S` of cardinality `CuffsRest.ncard + 2 ≤ (cuffs S).ncard` absorb all
boundary vertices of `B = Γ.inter (cap.emb ⁻¹' K_B)`, then removing `discInt Δ` and the shrunk cuff
discs for `CuffsRest` produces a surface `W` with `(cuffs W).ncard = CuffsRest.ncard + 1 < (cuffs S).ncard`
in which `B` embeds with `0` vertex splits, contradicting Claim (6). -/
theorem contradiction_of_single_disc {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L A B : Hypergraph S (Set S)}
    {K_B Δ : Set S₀}
    {CuffsRest : Set (Set S)}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (h_ind2 : ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
      IsSurface S' → [ConnectedSpace S'] →
      GM19.IsCappedSurface S' Shat' →
      Nonempty (Shat' ≃ₜ S₀) →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₂ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → [ConnectedSpace S'] →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₃ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (hKB : IsClosed K_B)
    (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B ≤ θ₄)
    (hB_eq : B = (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B))
    (hΔ : IsClosedDisc Δ)
    (hCuffsRest_sub : CuffsRest ⊆ cuffs S)
    (hCuffsRest_card : CuffsRest.ncard + 2 ≤ (cuffs S).ncard)
    (hdisj_c : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) Δ)
    (hKB_W : (capDrawing hS cap Γ).U ∩ K_B ⊆ (discInt Δ)ᶜ)
    (hW_bd_norm :
      discBd Δ ∩ ((capDrawing hS cap Γ).U ∩ K_B) ⊆ (capDrawing hS cap Γ).V)
    (hbd_V : ∀ v ∈ B.vertexSet,
      (cap.emb v ∈ discBd Δ ∪ (⋃ c ∈ CuffsRest, cap.emb '' c) ↔
        v ∈ (A ∩ B).vertexSet ∨ v ∈ Γ.V ∩ bd S)) :
    False := by
  classical
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : CompactSpace S₀ := hS₀.1
  haveI : T2Space S₀ := hS₀.2.1
  haveI : ConnectedSpace S₀ := cap.connected
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hCuffsRest_fin : CuffsRest.Finite := hcuffs_fin.subset hCuffsRest_sub
  haveI : Finite CuffsRest := hCuffsRest_fin.to_subtype
  have hinj_emb : Function.Injective cap.emb := cap.isEmbedding.injective
  let Avoid : Set S := cap.emb ⁻¹' Δ
  have h_shrunk : ∀ c : CuffsRest, ∃ P_c : Set S₀,
      P_c ⊆ closure (cap.cuffDisc c.1) ∧
      IsClosedDisc P_c ∧
      P_c ⊆ cap.cuffDisc c.1 ∪ cap.emb '' ((c.1 ∩ Γ.V) \ Avoid) ∧
      discInt P_c ⊆ cap.cuffDisc c.1 ∧
      cap.emb '' ((c.1 ∩ Γ.V) \ Avoid) ⊆ discBd P_c := by
    intro c
    have hc_cuff : c.1 ∈ cuffs S := hCuffsRest_sub c.2
    have hE_disc : IsClosedDisc (closure (cap.cuffDisc c.1)) :=
      cap.cuffDisc_closedDisc c.1 hc_cuff
    have hE_bd : discBd (closure (cap.cuffDisc c.1)) = cap.emb '' c.1 :=
      cap.cuffDisc_bd c.1 hc_cuff
    have hE_int : discInt (closure (cap.cuffDisc c.1)) = cap.cuffDisc c.1 :=
      (cap.cuffDisc_eq_discInt hS hc_cuff).symm
    have hA_fin : (cap.emb '' ((c.1 ∩ Γ.V) \ Avoid)).Finite :=
      ((Γ.finite_V.subset inter_subset_right).sdiff).image cap.emb
    have hA_sub : cap.emb '' ((c.1 ∩ Γ.V) \ Avoid) ⊆ discBd (closure (cap.cuffDisc c.1)) := by
      rw [hE_bd]
      exact image_mono (sdiff_subset.trans inter_subset_left)
    obtain ⟨P_c, hP_sub, hP_disc, hP_int_A, hP_int, hP_bd⟩ :=
      exists_subdisc_fixing_bd_subset hE_disc hA_fin hA_sub
    rw [hE_int] at hP_int_A hP_int
    exact ⟨P_c, hP_sub, hP_disc, hP_int_A, hP_int, hP_bd⟩
  choose P_c hP_c_sub_cl hP_c_disc hP_c_sub_union hP_c_int hP_c_bd using h_shrunk
  let P : Option CuffsRest → Set S₀ := fun i =>
    match i with
    | none => Δ
    | some c => P_c c
  have hP_disc : ∀ i : Option CuffsRest, IsClosedDisc (P i) := by
    rintro (_ | c)
    · exact hΔ
    · exact hP_c_disc c
  have hP_disj_none : ∀ c : CuffsRest, Disjoint (P_c c) Δ := by
    intro c
    refine disjoint_left.mpr fun x hxP hxΔ => ?_
    rcases hP_c_sub_union c hxP with hx_open | ⟨u, ⟨_, hu_not⟩, rfl⟩
    · exact disjoint_left.mp (hdisj_c c.1 c.2) hx_open hxΔ
    · exact hu_not hxΔ
  have hP_disj : Pairwise fun i j : Option CuffsRest => Disjoint (P i) (P j) := by
    rintro (_ | c₁) (_ | c₂) hij
    · exact (hij rfl).elim
    · exact (hP_disj_none c₂).symm
    · exact hP_disj_none c₁
    · have hne : c₁.1 ≠ c₂.1 := fun h => hij (congrArg some (Subtype.ext h))
      exact (cap.cuffDisc_disjoint c₁.1 (hCuffsRest_sub c₁.2) c₂.1 (hCuffsRest_sub c₂.2) hne).mono
        (hP_c_sub_cl c₁) (hP_c_sub_cl c₂)
  obtain ⟨_, hW_surf, hW_bd, hW_conn, hW_cuffs⟩ :=
    Surface.remove_discs hS₀ hcl₀.2.2 hP_disc hP_disj
  obtain ⟨capW⟩ := GM19.nonempty_capped_of_removal hcl₀ hP_disc hP_disj
  let W : Set S₀ := (⋃ i : Option CuffsRest, discInt (P i))ᶜ
  haveI : ConnectedSpace ↥W := hW_conn
  have hKB_sub_W : (capDrawing hS cap Γ).U ∩ K_B ⊆ W := by
    rintro x ⟨hxU, hxKB⟩ hx_bad
    rcases mem_iUnion.mp hx_bad with ⟨_ | c, hxc⟩
    · exact hKB_W ⟨hxU, hxKB⟩ hxc
    · have hx_open : x ∈ cap.cuffDisc c.1 := hP_c_int c hxc
      have hx_compl : x ∈ (range cap.emb)ᶜ := by
        rw [cap.compl_eq]
        exact mem_iUnion₂.mpr ⟨c.1, hCuffsRest_sub c.2, hx_open⟩
      rcases hxU with ⟨s, _, rfl⟩
      exact hx_compl (mem_range_self s)
  have hbd_union_sub :
      (⋃ i : Option CuffsRest, discBd (P i)) ⊆
        discBd Δ ∪ ⋃ c : CuffsRest, (cap.cuffDisc c.1 ∪ cap.emb '' ((c.1 ∩ Γ.V) \ Avoid)) := by
    rintro x hx
    rcases mem_iUnion.mp hx with ⟨_ | c, hxc⟩
    · exact Or.inl hxc
    · exact Or.inr (mem_iUnion.mpr ⟨c, hP_c_sub_union c (Surface.discBd_subset _ hxc)⟩)
  have hbW : ∀ i : Option CuffsRest, ∀ x ∈ discBd (P i), x ∈ W := fun i x hx hu => by
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    by_cases hij : i = j
    · subst hij
      exact hj.2 hx
    · exact Set.disjoint_left.mp (hP_disj hij) (Surface.discBd_subset _ hx) hj.1
  have hinj_cuff : Function.Injective
      (fun i : Option CuffsRest => (Subtype.val ⁻¹' discBd (P i) : Set ↥W)) := by
    intro i j he
    by_contra hij
    obtain ⟨y, hy⟩ := (IsOArc.isConnected' (hP_disc i).isOArc_discBd).nonempty
    have h1 : (⟨y, hbW i y hy⟩ : ↥W) ∈ (Subtype.val ⁻¹' discBd (P j) : Set ↥W) := by
      dsimp only at he
      have hmem : (⟨y, hbW i y hy⟩ : ↥W) ∈ (Subtype.val ⁻¹' discBd (P i) : Set ↥W) := hy
      rwa [he] at hmem
    exact Set.disjoint_left.mp (hP_disj hij)
      (Surface.discBd_subset _ hy) (Surface.discBd_subset _ h1)
  have hcuffs_W : (cuffs ↥W).ncard = CuffsRest.ncard + 1 := by
    haveI : Fintype CuffsRest := hCuffsRest_fin.fintype
    rw [hW_cuffs, ← image_univ, Set.ncard_image_of_injective univ hinj_cuff,
      ncard_univ, Nat.card_eq_fintype_card, Fintype.card_option,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  obtain ⟨Γ_W, π_W, fE_W, hπW_inj, hfEW_inj, h_mapW, hπW_spec, hUW_spec⟩ :=
    exists_subspace_drawing_of_closed_subset hS cap Γ hKB hKB_sub_W
  have hΓW_prop : Γ_W.IsProper := by
    rintro y ⟨hy_bd, hy_U⟩
    obtain ⟨hy_embU, hy_KB, h_to_V⟩ := hUW_spec y hy_U
    apply h_to_V
    rw [hW_bd, mem_preimage] at hy_bd
    rcases hbd_union_sub hy_bd with hy1 | hy_c
    · exact hW_bd_norm ⟨hy1, hy_embU, hy_KB⟩
    · rcases mem_iUnion.mp hy_c with ⟨c, hy_open | ⟨u, ⟨⟨_, huV⟩, _⟩, hu_eq⟩⟩
      · exfalso
        have hy_compl : y.1 ∈ (range cap.emb)ᶜ := by
          rw [cap.compl_eq]
          exact mem_iUnion₂.mpr ⟨c.1, hCuffsRest_sub c.2, hy_open⟩
        rcases hy_embU with ⟨s, _, hs_eq⟩
        exact hy_compl ⟨s, hs_eq⟩
      · rw [← hu_eq]
        exact mem_image_of_mem cap.emb huV
  have hsplit_S : ObtainedBySplittingOutsideLe Γ.V θ₄ B
      (mapHypergraph π_W fE_W Γ_W.toHypergraph) := by
    rw [h_mapW, ← hB_eq]
    exact ObtainedBySplittingOutsideLe.refl θ₄ B
  have h6b : ∀ y ∈ Γ_W.V,
      y ∈ bd ↥W ↔
        π_W y ∈ (A ∩ B).vertexSet ∨ π_W y ∈ Γ.V ∩ bd S ∨ π_W y ∉ Γ.V := by
    intro y hyV
    obtain ⟨h_emb_π, hπ_V, hy_KB⟩ := hπW_spec y hyV
    have hπ_B : π_W y ∈ B.vertexSet := by
      rw [hB_eq, ← h_mapW]
      exact mem_image_of_mem π_W hyV
    have h_not_int : cap.emb (π_W y) ∉ discInt Δ := by
      apply hKB_W
      rw [h_emb_π]
      exact ⟨⟨π_W y, Γ.V_subset_U hπ_V, h_emb_π⟩, hy_KB⟩
    have h_bd_y : y ∈ bd ↥W ↔
        cap.emb (π_W y) ∈ discBd Δ ∪ ⋃ c ∈ CuffsRest, cap.emb '' c := by
      rw [hW_bd, mem_preimage, ← h_emb_π]
      constructor
      · intro hy_u
        rcases hbd_union_sub hy_u with hy1 | hy_c
        · exact Or.inl hy1
        · rcases mem_iUnion.mp hy_c with ⟨c, hy_open | ⟨u, ⟨⟨hu_c, _⟩, _⟩, h_eq⟩⟩
          · exfalso
            have hy_compl : cap.emb (π_W y) ∈ (range cap.emb)ᶜ := by
              rw [cap.compl_eq]
              exact mem_iUnion₂.mpr ⟨c.1, hCuffsRest_sub c.2, hy_open⟩
            exact hy_compl (mem_range_self _)
          · exact Or.inr (mem_iUnion₂.mpr ⟨c.1, c.2, u, hu_c, h_eq⟩)
      · rintro (hy1 | hy_c)
        · exact mem_iUnion.mpr ⟨none, hy1⟩
        · rcases mem_iUnion₂.mp hy_c with ⟨c, hc, u, hu_c, h_eq⟩
          have hu_eq : u = π_W y := hinj_emb h_eq
          by_cases h_in : cap.emb (π_W y) ∈ Δ
          · refine mem_iUnion.mpr ⟨none, ?_⟩
            by_contra h_not_bd
            exact h_not_int ⟨h_in, h_not_bd⟩
          · refine mem_iUnion.mpr ⟨some ⟨c, hc⟩, hP_c_bd ⟨c, hc⟩ ?_⟩
            exact ⟨π_W y, ⟨⟨hu_eq ▸ hu_c, hπ_V⟩, h_in⟩, rfl⟩
    rw [h_bd_y, hbd_V (π_W y) hπ_B]
    simp only [hπ_V, not_true_eq_false, or_false]
  have h6 := apply_claim_5_2_6_of_drawing hS hW_surf cap capW hΓ_bd h𝒯 hL hL_bd hAB hord
    hπW_inj hfEW_inj hsplit_S ⟨Homeomorph.refl S₀⟩ h6b hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos
    (fun hlt_c hle_bd T' L' hT' hL' =>
      h_ind2 ↥W S₀ hW_surf capW ⟨Homeomorph.refl S₀⟩ hlt_c _ hΓW_prop hle_bd T' L' hT' hL')
    (fun hhomeo hlt_bd T' L' hT' hL' =>
      h_ind3 ↥W hW_surf hhomeo _ hΓW_prop hlt_bd T' L' hT' hL')
  have h_le := h6.1
  change (cuffs S).ncard ≤ (cuffs ↥W).ncard at h_le
  omega

/-- Given a closed disc `E` in a T2 space `Z`, a boundary point `p ∈ discBd E`, and a closed set
`K_bad ⊆ Z` with `p ∉ K_bad`, there exists a closed subdisc `D ⊆ (discInt E \ K_bad) ∪ {p}` such
that `p ∈ discBd D`, `D ∩ discBd E = {p}`, and `Disjoint D K_bad`. -/
theorem exists_tangent_subdisc_at_bd_point {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    {E K_bad : Set Z} (hE : IsClosedDisc E) {p : Z} (hp : p ∈ discBd E)
    (hK_closed : IsClosed K_bad) (hp_not_K : p ∉ K_bad) :
    ∃ D : Set Z,
      D ⊆ E ∧
      IsClosedDisc D ∧
      D ⊆ (discInt E \ K_bad) ∪ {p} ∧
      discInt D ⊆ discInt E \ K_bad ∧
      p ∈ discBd D ∧
      D ∩ discBd E = {p} ∧
      Disjoint D K_bad := by
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  have hp_E : p ∈ E := Surface.discBd_subset E hp
  let w₁ : ℂ := h p
  have hw₁_sph : w₁ ∈ Metric.sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hp
  have hw₁_norm : ‖w₁‖ = 1 := by simpa using hw₁_sph
  have hw₁_nsq : Complex.normSq w₁ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hw₁_norm, one_pow]
  have hw₁_cb : w₁ ∈ Metric.closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hw₁_sph
  have hgw₁ : g w₁ = p := c.gh hp_E
  have h_nhds : g ⁻¹' K_badᶜ ∈ nhdsWithin w₁ (Metric.closedBall (0 : ℂ) 1) :=
    c.gc w₁ hw₁_cb (hK_closed.isOpen_compl.mem_nhds (hgw₁.symm ▸ hp_not_K))
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhdsWithin_iff.mp h_nhds
  let ε : ℝ := min (1 / 2) (δ / 3)
  have hε_pos : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε_lt1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have h2ε_lt : 2 * ε < δ := by
    have : ε ≤ δ / 3 := min_le_right _ _
    linarith
  let Φ : ℂ → ℂ := fun z => (1 - ε : ℝ) • w₁ + (ε : ℝ) • z
  let Φinv : ℂ → ℂ := fun w => (ε⁻¹ : ℝ) • (w - (1 - ε : ℝ) • w₁)
  have hΦ_cont : Continuous Φ := by fun_prop
  have hΦinv_cont : Continuous Φinv := by fun_prop
  have hΦ_left : ∀ z : ℂ, Φinv (Φ z) = z := fun z => by
    dsimp [Φ, Φinv, Complex.real_smul]
    rw [add_sub_cancel_left, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hε_pos.ne', Complex.ofReal_one, one_mul]
  have hΦw₁ : Φ w₁ = w₁ := by
    dsimp [Φ, Complex.real_smul]
    push_cast
    ring
  have hΦ_dist : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Φ z ∈ Metric.ball w₁ δ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    have hz_norm : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have h_diff : Φ z - w₁ = (ε : ℝ) • (z - w₁) := by
      dsimp [Φ, Complex.real_smul]
      push_cast
      ring
    rw [h_diff, norm_smul, Real.norm_eq_abs, abs_of_pos hε_pos]
    have h_zw : ‖z - w₁‖ ≤ 2 := by
      calc ‖z - w₁‖ ≤ ‖z‖ + ‖w₁‖ := norm_sub_le z w₁
        _ ≤ 1 + 1 := add_le_add hz_norm hw₁_norm.le
        _ = 2 := by norm_num
    nlinarith
  have hΦ_ball : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, z ≠ w₁ → Φ z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz hne
    rw [Metric.mem_ball, dist_zero_right, ← sq_lt_one_iff₀ (norm_nonneg _),
      ← Complex.normSq_eq_norm_sq]
    have hz_norm : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hz_nsq : Complex.normSq z ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg z]
    have hdiff_pos : 0 < Complex.normSq (w₁ - z) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr hne.symm)
    have h_pol : Complex.normSq (Φ z) =
        (1 - ε) * Complex.normSq w₁ + ε * Complex.normSq z -
          (1 - ε) * ε * Complex.normSq (w₁ - z) := by
      dsimp [Φ, Complex.normSq_apply, Complex.real_smul]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h_pol, hw₁_nsq]
    have h_prod_pos : 0 < (1 - ε) * ε * Complex.normSq (w₁ - z) :=
      mul_pos (mul_pos (by linarith) hε_pos) hdiff_pos
    nlinarith
  let K : Set ℂ := Φ '' Metric.closedBall (0 : ℂ) 1
  obtain ⟨hK_disc, hK_bd⟩ :=
    Surface.isClosedDisc_closedBall.1.image hΦ_cont.continuousOn
      hΦinv_cont.continuousOn (fun z _ => hΦ_left z)
  rw [Surface.isClosedDisc_closedBall.2] at hK_bd
  have hK_sub_ball_w₁ : K ⊆ Metric.ball (0 : ℂ) 1 ∪ {w₁} := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzw : z = w₁
    · subst hzw
      rw [hΦw₁]
      exact Or.inr rfl
    · exact Or.inl (hΦ_ball z hz hzw)
  have hK_sub_cb : K ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro w hw
    rcases hK_sub_ball_w₁ hw with hw_ball | rfl
    · exact Metric.ball_subset_closedBall hw_ball
    · exact hw₁_cb
  have hK_disj_bad : ∀ w ∈ K, g w ∉ K_bad := by
    rintro _ ⟨z, hz, rfl⟩
    exact hδ_sub ⟨hΦ_dist z hz, hK_sub_cb ⟨z, hz, rfl⟩⟩
  obtain ⟨hD_disc, hD_bd⟩ := c.disc_g hK_sub_cb hK_disc
  have hp_mem_bd : p ∈ discBd (g '' K) := by
    rw [hD_bd, hK_bd, ← hgw₁]
    exact mem_image_of_mem g ⟨w₁, hw₁_sph, hΦw₁⟩
  have hD_sub_int_p : g '' K ⊆ (discInt E \ K_bad) ∪ {p} := by
    rintro _ ⟨w, hwK, rfl⟩
    rcases hK_sub_ball_w₁ hwK with hw_ball | rfl
    · refine Or.inl ⟨?_, hK_disj_bad w hwK⟩
      rw [c.discInt_eq]
      exact mem_image_of_mem g hw_ball
    · rw [hgw₁]
      exact Or.inr rfl
  have hD_int_sub : discInt (g '' K) ⊆ discInt E \ K_bad := by
    intro x hx
    rcases hD_sub_int_p hx.1 with hx_int | rfl
    · exact hx_int
    · exact (hx.2 hp_mem_bd).elim
  have hD_inter_bd : g '' K ∩ discBd E = {p} := by
    apply Subset.antisymm
    · rintro x ⟨hxD, hx_bdE⟩
      rcases hD_sub_int_p hxD with ⟨hx_intE, _⟩ | rfl
      · exact (hx_intE.2 hx_bdE).elim
      · rfl
    · rintro x rfl
      exact ⟨Surface.discBd_subset (g '' K) hp_mem_bd, hp⟩
  have hD_disj : Disjoint (g '' K) K_bad := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨w, hwK, rfl⟩
    exact hK_disj_bad w hwK
  exact ⟨g '' K, c.g_subset hK_sub_cb, hD_disc, hD_sub_int_p, hD_int_sub,
    hp_mem_bd, hD_inter_bd, hD_disj⟩

/-- For any cuff `C ∈ cuffs S` and cuff region `r` (`IsCuffRegion hS cap Γ C r`),
`cap.cuffDisc C ⊆ r` and `closure (cap.cuffDisc C) \ (capDrawing hS cap Γ).V ⊆ r`. -/
theorem cuffDisc_closure_sdiff_subset_cuffRegion {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S) (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S} (hΓ : Γ.IsProper) {C : Set S} {r : Set S₀}
    (hr : IsCuffRegion hS cap Γ C r) :
    cap.cuffDisc C ⊆ r ∧
    closure (cap.cuffDisc C) \ (capDrawing hS cap Γ).V ⊆ r ∧
    IsPathConnected r := by
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : CompactSpace S₀ := hS₀.1
  haveI : T2Space S₀ := hS₀.2.1
  haveI : LocallyConnectedSpace S₀ := GM11.IsClosedSurface.locallyConnectedSpace hcl₀
  have hC : C ∈ cuffs S := hr.1
  have hr_reg : r ∈ (capDrawing hS cap Γ).R := hr.2.1
  obtain ⟨r₀, _, hdisc_r₀, _, _, huniq⟩ := exists_unique_cuffRegion hS cap hΓ hC
  have hrr₀ : r = r₀ := (huniq r hr_reg).1.mp hr
  have hdisc_sub_r : cap.cuffDisc C ⊆ r := hrr₀ ▸ hdisc_r₀
  have h_sdiff_sub_r : closure (cap.cuffDisc C) \ (capDrawing hS cap Γ).V ⊆ r := by
    rintro x ⟨hx_cl, hx_notV⟩
    rw [cap.closure_cuffDisc hS hC] at hx_cl
    rcases hx_cl with hx_open | ⟨u, huC, rfl⟩
    · exact hdisc_sub_r hx_open
    · have hu_notV : u ∉ Γ.V := fun huV => hx_notV (mem_image_of_mem cap.emb huV)
      exact hr.2.2 ⟨u, ⟨huC, hu_notV⟩, rfl⟩
  have hr_pc : IsPathConnected r :=
    GM11.isPathConnected_of_isOpen hcl₀
      (GM11.region_isOpen hr_reg) (GM11.region_isPreconnected hr_reg) (GM11.region_nonempty hr_reg)
  exact ⟨hdisc_sub_r, h_sdiff_sub_r, hr_pc⟩

/-- Consequence of Claim (7) (`claim_5_2_7`): no path-connected set `P ⊆ S₀` with
`P ∩ H₀.U ⊆ H₀.V` and `(P ∩ H₀.V).ncard ≤ θ₄` can meet both `r₁ ∪ closure (cap.cuffDisc C₁)` and
`r₂ ∪ closure (cap.cuffDisc C₂)` for two distinct cuffs `C₁ ≠ C₂`. -/
theorem no_cuff_conn_of_claim_5_2_7 {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ : Γ.IsProper)
    (hΓ_loopless : ∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard)
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (h_ind2 : ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
      IsSurface S' → [ConnectedSpace S'] →
      GM19.IsCappedSurface S' Shat' →
      Nonempty (Shat' ≃ₜ S₀) →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₂ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → [ConnectedSpace S'] →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₃ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    {C₁ C₂ : Set S} {r₁ r₂ P : Set S₀}
    (hne : C₁ ≠ C₂)
    (hr₁ : IsCuffRegion hS cap Γ C₁ r₁)
    (hr₂ : IsCuffRegion hS cap Γ C₂ r₂)
    (hP_pc : IsPathConnected P)
    (hP_norm : P ∩ (capDrawing hS cap Γ).U ⊆ (capDrawing hS cap Γ).V)
    (hP_card : (P ∩ (capDrawing hS cap Γ).V).ncard ≤ θ₄)
    (hP₁ : (P ∩ (r₁ ∪ closure (cap.cuffDisc C₁))).Nonempty)
    (hP₂ : (P ∩ (r₂ ∪ closure (cap.cuffDisc C₂))).Nonempty) :
    False := by
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : CompactSpace S₀ := hS₀.1
  haveI : T2Space S₀ := hS₀.2.1
  have hinj_emb : Function.Injective cap.emb := cap.isEmbedding.injective
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hC₁ : C₁ ∈ cuffs S := hr₁.1
  have hC₂ : C₂ ∈ cuffs S := hr₂.1
  obtain ⟨hdisc_r₁, _, hr₁_pc⟩ := cuffDisc_closure_sdiff_subset_cuffRegion hS cap hΓ hr₁
  obtain ⟨hdisc_r₂, _, hr₂_pc⟩ := cuffDisc_closure_sdiff_subset_cuffRegion hS cap hΓ hr₂
  let X : Set S₀ := closure (cap.cuffDisc C₁)
  let Y : Set S₀ := ⋃ c ∈ cuffs S \ {C₁}, closure (cap.cuffDisc c)
  have hX_closed : IsClosed X := isClosed_closure
  have hY_closed : IsClosed Y :=
    (hcuffs_fin.sdiff).isClosed_biUnion fun _ _ => isClosed_closure
  have hXY_disj : Disjoint X Y := by
    refine disjoint_left.mpr fun x hxX hxY => ?_
    rcases mem_iUnion₂.mp hxY with ⟨c, ⟨hc, hc_ne⟩, hxc⟩
    exact disjoint_left.mp (cap.cuffDisc_disjoint C₁ hC₁ c hc (Ne.symm hc_ne)) hxX hxc
  have hdisc₁_ne : (cap.cuffDisc C₁).Nonempty := by
    rw [cap.cuffDisc_eq_discInt hS hC₁]
    exact (cap.cuffDisc_closedDisc C₁ hC₁).nonempty_discInt
  have hdisc₂_ne : (cap.cuffDisc C₂).Nonempty := by
    rw [cap.cuffDisc_eq_discInt hS hC₂]
    exact (cap.cuffDisc_closedDisc C₂ hC₂).nonempty_discInt
  obtain ⟨x₁, hx₁⟩ := hdisc₁_ne
  obtain ⟨x₂, hx₂⟩ := hdisc₂_ne
  classical
  let P₁ : Set S₀ := if (P ∩ r₁).Nonempty then P ∪ r₁ else P
  have hP_sub_P₁ : P ⊆ P₁ := by
    dsimp [P₁]
    split_ifs <;> [exact subset_union_left; exact Subset.rfl]
  have hP₁_sub : P₁ ⊆ P ∪ r₁ := by
    dsimp [P₁]
    split_ifs <;> [exact Subset.rfl; exact subset_union_left]
  have hP₁_pc : IsPathConnected P₁ := by
    dsimp [P₁]
    split_ifs with h1
    · exact hP_pc.union hr₁_pc h1
    · exact hP_pc
  have hP₁X : (P₁ ∩ X).Nonempty := by
    dsimp [P₁]
    split_ifs with h1
    · exact ⟨x₁, Or.inr (hdisc_r₁ hx₁), subset_closure hx₁⟩
    · rcases hP₁ with ⟨z, hzP, hzr₁ | hzX⟩
      · exact (h1 ⟨z, hzP, hzr₁⟩).elim
      · exact ⟨z, hzP, hzX⟩
  let P' : Set S₀ := if (P₁ ∩ r₂).Nonempty then P₁ ∪ r₂ else P₁
  have hP₁_sub_P' : P₁ ⊆ P' := by
    dsimp [P']
    split_ifs <;> [exact subset_union_left; exact Subset.rfl]
  have hP'_sub : P' ⊆ (P ∪ r₁) ∪ r₂ := by
    dsimp [P']
    split_ifs <;> [exact union_subset_union_left _ hP₁_sub; exact hP₁_sub.trans subset_union_left]
  have hP'_pc : IsPathConnected P' := by
    dsimp [P']
    split_ifs with h2
    · exact hP₁_pc.union hr₂_pc h2
    · exact hP₁_pc
  have hP'X : (P' ∩ X).Nonempty := hP₁X.mono (inter_subset_inter_left X hP₁_sub_P')
  have hP'Y : (P' ∩ Y).Nonempty := by
    dsimp [P']
    split_ifs with h2
    · exact ⟨x₂, Or.inr (hdisc_r₂ hx₂),
        mem_iUnion₂.mpr ⟨C₂, ⟨hC₂, hne.symm⟩, subset_closure hx₂⟩⟩
    · rcases hP₂ with ⟨z, hzP, hzr₂ | hzX₂⟩
      · exact (h2 ⟨z, hP_sub_P₁ hzP, hzr₂⟩).elim
      · exact ⟨z, hP_sub_P₁ hzP, mem_iUnion₂.mpr ⟨C₂, ⟨hC₂, hne.symm⟩, hzX₂⟩⟩
  obtain ⟨p₀, hp₀P', hp₀X⟩ := hP'X
  obtain ⟨q₀, hq₀P', hq₀Y⟩ := hP'Y
  obtain ⟨L₀, a₀, b₀, hL₀, hL₀_P', _, ha₀_fr, ⟨_, hb₀_Y⟩, hb₀_fr, hL₀_int⟩ :=
    exists_line_crossing_of_isPathConnected hP'_pc hX_closed hY_closed
      (hXY_disj.mono inter_subset_right inter_subset_right)
      hp₀P' hp₀X hq₀P' hq₀Y
  have ha₀_bd : a₀ ∈ cap.emb '' C₁ := by
    rw [← cap.cuffDisc_bd C₁ hC₁,
      ← GM11.IsClosedDisc.frontier_eq_discBd hcl₀ (cap.cuffDisc_closedDisc C₁ hC₁)]
    exact ha₀_fr
  rcases mem_iUnion₂.mp hb₀_Y with ⟨C₂', ⟨hC₂', hC₂'_ne⟩, hb₀_cl⟩
  have hb₀_not_open : b₀ ∉ cap.cuffDisc C₂' := by
    intro hb₀_open
    have h_open_c₂' : IsOpen (cap.cuffDisc C₂') := by
      rw [cap.cuffDisc_eq_discInt hS hC₂']
      exact (cap.cuffDisc_closedDisc C₂' hC₂').isOpen_discInt hS₀.2.2
    have h_open_sub : cap.cuffDisc C₂' ⊆ interior Y :=
      interior_maximal (fun z hz =>
        mem_iUnion₂.mpr ⟨C₂', ⟨hC₂', hC₂'_ne⟩, subset_closure hz⟩) h_open_c₂'
    exact hb₀_fr.2 (h_open_sub hb₀_open)
  have hb₀_bd : b₀ ∈ cap.emb '' C₂' := by
    rw [cap.closure_cuffDisc hS hC₂'] at hb₀_cl
    exact hb₀_cl.resolve_left hb₀_not_open
  rcases ha₀_bd with ⟨s, hs_C₁, rfl⟩
  rcases hb₀_bd with ⟨t, ht_C₂', rfl⟩
  have hL₀_int_no_cl : ∀ x ∈ L₀ \ {cap.emb s, cap.emb t},
      ∀ c ∈ cuffs S, x ∉ closure (cap.cuffDisc c) := by
    intro x hx c hc hxc
    have hx_out := (hL₀_int hx).2
    by_cases hc1 : c = C₁
    · subst hc1
      exact hx_out (Or.inl hxc)
    · exact hx_out (Or.inr (mem_iUnion₂.mpr ⟨c, ⟨hc, hc1⟩, hxc⟩))
  have hL₀_range : L₀ ⊆ range cap.emb := by
    intro x hx
    by_cases h_end : x ∈ ({cap.emb s, cap.emb t} : Set S₀)
    · rcases h_end with rfl | rfl <;> exact mem_range_self _
    · by_contra hx_not_range
      have hx_compl : x ∈ (range cap.emb)ᶜ := hx_not_range
      rw [cap.compl_eq] at hx_compl
      rcases mem_iUnion₂.mp hx_compl with ⟨c, hc, hx_open⟩
      exact hL₀_int_no_cl x ⟨hx, h_end⟩ c hc (subset_closure hx_open)
  let F : Set S := cap.emb ⁻¹' L₀
  have hF_img : cap.emb '' F = L₀ := image_preimage_eq_of_subset hL₀_range
  have hF_line : IsLineWithEnds F s t := by
    rcases id hL₀ with ⟨φ, hφ0, hφ1⟩
    have hφ_in : ∀ u : 𝕀, ∃ x : S, cap.emb x = (φ u).1 := fun u => hL₀_range (φ u).2
    let ψ_fun : 𝕀 → F := fun u =>
      ⟨Classical.choose (hφ_in u), by
        change cap.emb _ ∈ L₀
        rw [Classical.choose_spec (hφ_in u)]
        exact (φ u).2⟩
    have hψ_emb : ∀ u : 𝕀, cap.emb (ψ_fun u).1 = (φ u).1 :=
      fun u => Classical.choose_spec (hφ_in u)
    have hψ_cont : Continuous ψ_fun := by
      refine Continuous.subtype_mk ?_ _
      rw [cap.isEmbedding.continuous_iff]
      have h_eq : cap.emb ∘ (fun u => (ψ_fun u).1) = Subtype.val ∘ φ := by
        ext u; exact hψ_emb u
      rw [h_eq]
      exact continuous_subtype_val.comp φ.continuous
    let ψ_homeo : 𝕀 ≃ₜ F :=
      { toFun := ψ_fun
        invFun := fun y => φ.symm ⟨cap.emb y.1, y.2⟩
        left_inv := fun u => by
          apply φ.injective
          ext
          simp [hψ_emb u]
        right_inv := fun y => by
          ext
          apply hinj_emb
          rw [hψ_emb]
          simp
        continuous_toFun := hψ_cont
        continuous_invFun := φ.symm.continuous.comp
          (Continuous.subtype_mk (cap.isEmbedding.continuous.comp continuous_subtype_val) _) }
    refine ⟨ψ_homeo, ?_, ?_⟩
    · apply hinj_emb
      change cap.emb (ψ_fun 0).1 = cap.emb s
      rw [hψ_emb, hφ0]
    · apply hinj_emb
      change cap.emb (ψ_fun 1).1 = cap.emb t
      rw [hψ_emb, hφ1]
  have hF_bd : F ∩ bd S = {s, t} := by
    apply Subset.antisymm
    · intro x ⟨hxF, hx_bd⟩
      by_contra hx_ne
      have hx_emb_ne : cap.emb x ∉ ({cap.emb s, cap.emb t} : Set S₀) := by
        rintro (h1 | h2)
        · exact hx_ne (Or.inl (hinj_emb h1))
        · exact hx_ne (Or.inr (hinj_emb h2))
      rw [← sUnion_cuffs] at hx_bd
      rcases hx_bd with ⟨c, hc, hxc⟩
      have hx_cl : cap.emb x ∈ closure (cap.cuffDisc c) := by
        rw [cap.closure_cuffDisc hS hc]
        exact Or.inr (mem_image_of_mem cap.emb hxc)
      exact hL₀_int_no_cl (cap.emb x) ⟨hxF, hx_emb_ne⟩ c hc hx_cl
    · rintro x (rfl | rfl)
      · exact ⟨hL₀.left_mem, sUnion_cuffs (S := S) ▸ subset_sUnion_of_mem hC₁ hs_C₁⟩
      · exact ⟨hL₀.right_mem, sUnion_cuffs (S := S) ▸ subset_sUnion_of_mem hC₂' ht_C₂'⟩
  have hF_proper : IsProperLineInSurface F s t := by
    refine ⟨hF_line, ((Set.ext_iff.mp hF_bd s).mpr (Or.inl rfl)).2,
      ((Set.ext_iff.mp hF_bd t).mpr (Or.inr rfl)).2,
      disjoint_left.mpr fun y ⟨hyF, hy_st⟩ hy_bd => ?_⟩
    exact hy_st ((Set.ext_iff.mp hF_bd y).mp ⟨hyF, hy_bd⟩)
  have hL₀_U_sub_P : L₀ ∩ (capDrawing hS cap Γ).U ⊆ P ∩ (capDrawing hS cap Γ).V := by
    rintro x ⟨hxL₀, hxU⟩
    rcases hP'_sub (hL₀_P' hxL₀) with (hxP | hxr₁) | hxr₂
    · exact ⟨hxP, hP_norm ⟨hxP, hxU⟩⟩
    · exact (GM11.region_subset hr₁.2.1 hxr₁ hxU).elim
    · exact (GM11.region_subset hr₂.2.1 hxr₂ hxU).elim
  have hF_norm : (PaintingOrDrawing.drawing Γ).IsNormal F := by
    intro u ⟨huF, huU⟩
    have hu_emb : cap.emb u ∈ (capDrawing hS cap Γ).V :=
      (hL₀_U_sub_P ⟨huF, mem_image_of_mem cap.emb huU⟩).2
    rcases hu_emb with ⟨v, hvV, hv_eq⟩
    exact hinj_emb hv_eq ▸ hvV
  have hF_card : (F ∩ Γ.V).ncard ≤ θ₄ := by
    have h_img_sub : cap.emb '' (F ∩ Γ.V) ⊆ P ∩ (capDrawing hS cap Γ).V := by
      rintro _ ⟨u, ⟨huF, huV⟩, rfl⟩
      exact hL₀_U_sub_P ⟨huF, mem_image_of_mem cap.emb (Γ.V_subset_U huV)⟩
    have h_fin : (P ∩ (capDrawing hS cap Γ).V).Finite :=
      (capDrawing hS cap Γ).finite_V.subset inter_subset_right
    rw [← Set.ncard_image_of_injective (F ∩ Γ.V) hinj_emb]
    exact (ncard_le_ncard h_img_sub h_fin).trans hP_card
  have h_gt := claim_5_2_7 hS cap hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd
    hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3
    hC₁ hC₂' (Ne.symm hC₂'_ne) hs_C₁ ht_C₂' hF_proper hF_norm
  omega

/-- For any subdrawing `D` of a pre-radial drawing `K` of `H₀`, `D.U` meets `H₀.U` and `H₀.V`
exclusively at `D.V ∩ H₀.V`. -/
theorem subdrawing_radial_inter_U {S₀ : Type} [TopologicalSpace S₀]
    {H₀ K D : Surface.Drawing S₀}
    (hP : (PaintingOrDrawing.drawing H₀).IsPreRadialDrawing K)
    (hD : D.IsSubdrawing K) :
    D.U ∩ H₀.U = D.V ∩ H₀.V ∧ D.U ∩ H₀.V = D.V ∩ H₀.V := by
  have h1 : D.U ∩ H₀.U = D.V ∩ H₀.V := by
    apply Subset.antisymm
    · rintro x ⟨hxD, hxH⟩
      have hx_inter : x ∈ (PaintingOrDrawing.drawing H₀).U ∩ K.U := ⟨hxH, hD.U_subset hxD⟩
      have hx_HV : x ∈ H₀.V := by
        change x ∈ (PaintingOrDrawing.drawing H₀).V
        rwa [← hP.1]
      exact ⟨GM19.mem_V_of_mem_U_sub hD hxD (hP.2.1 hx_HV), hx_HV⟩
    · exact inter_subset_inter D.V_subset_U H₀.V_subset_U
  refine ⟨h1, Subset.antisymm ?_ (inter_subset_inter_left H₀.V D.V_subset_U)⟩
  rintro x ⟨hxD, hxHV⟩
  exact h1 ▸ ⟨hxD, H₀.V_subset_U hxHV⟩

/-- For any closed walk `W` of length `< 2 * θ₄` in a pre-radial drawing `K` of `H₀` (with `1 ≤ θ₄`),
the walk drawing `walkDrawing K W` contains at most `θ₄` vertices of `H₀.V`. -/
theorem walkDrawing_inter_V_ncard_le {S₀ : Type} [TopologicalSpace S₀] [T2Space S₀]
    {H₀ K : Surface.Drawing S₀}
    (hP : (PaintingOrDrawing.drawing H₀).IsPreRadialDrawing K)
    {u₀ : S₀} {θ₄ : ℕ} (W : GraphWalk K.toGraph u₀ u₀) (hW : W.length < 2 * θ₄)
    (hθ₄ : 1 ≤ θ₄) :
    ((walkDrawing K W).V ∩ H₀.V).ncard ≤ θ₄ := by
  classical
  obtain ⟨k, hk⟩ := GM11.even_length_of_closed hP W
  obtain ⟨_, hcnt⟩ := GM12.walk_bipartite_parity_and_count hP W
  have hcnt_le : W.support.countP (· ∈ H₀.V) ≤ θ₄ := by
    split_ifs at hcnt <;> omega
  have hsub : (walkDrawing K W).V ∩ H₀.V ⊆
      ((W.support.filter (· ∈ H₀.V)).toFinset : Set S₀) := by
    rintro x ⟨hxV, hxH⟩
    rw [GM11.walkDrawing_V] at hxV
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨hxV, hxH⟩
  have hfin : ((W.support.filter (· ∈ H₀.V)).toFinset : Set S₀).Finite :=
    Finset.finite_toSet _
  calc ((walkDrawing K W).V ∩ H₀.V).ncard
      ≤ ((W.support.filter (· ∈ H₀.V)).toFinset : Set S₀).ncard :=
        ncard_le_ncard hsub hfin
    _ = (W.support.filter (· ∈ H₀.V)).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (W.support.filter (· ∈ H₀.V)).length := List.toFinset_card_le _
    _ = W.support.countP (· ∈ H₀.V) := List.countP_eq_length_filter.symm
    _ ≤ θ₄ := hcnt_le

/-- Intersection of two subspace hypergraphs `(PaintingOrDrawing.drawing Γ).inter Δ₁` and
`(PaintingOrDrawing.drawing Γ).inter Δ₂` is `(PaintingOrDrawing.drawing Γ).inter (Δ₁ ∩ Δ₂)`. -/
theorem inter_painting_inter_eq {S : Type} [TopologicalSpace S]
    (Γ : Surface.Drawing S) (Δ₁ Δ₂ : Set S) :
    (PaintingOrDrawing.drawing Γ).inter Δ₁ ∩ (PaintingOrDrawing.drawing Γ).inter Δ₂ =
      (PaintingOrDrawing.drawing Γ).inter (Δ₁ ∩ Δ₂) := by
  refine Hypergraph.ext (Set.ext fun v => ?_) (Set.ext fun e => ?_)
    (funext fun e => funext fun v => propext ?_)
  · change (v ∈ Γ.V ∧ v ∈ Δ₁) ∧ (v ∈ Γ.V ∧ v ∈ Δ₂) ↔ v ∈ Γ.V ∧ v ∈ Δ₁ ∧ v ∈ Δ₂
    tauto
  · change (e ∈ Γ.E ∧ e ⊆ Δ₁) ∧ (e ∈ Γ.E ∧ e ⊆ Δ₂) ↔ e ∈ Γ.E ∧ e ⊆ Δ₁ ∩ Δ₂
    rw [subset_inter_iff]
    tauto
  · change (Γ.toHypergraph.Inc e v ∧ e ⊆ Δ₁ ∧ v ∈ Δ₁) ∧
        (Γ.toHypergraph.Inc e v ∧ e ⊆ Δ₂ ∧ v ∈ Δ₂) ↔
      Γ.toHypergraph.Inc e v ∧ e ⊆ Δ₁ ∩ Δ₂ ∧ v ∈ Δ₁ ∧ v ∈ Δ₂
    rw [subset_inter_iff]
    tauto

/-- Pullback of the separation of a short circuit `C` of `K` under `cap.emb`. -/
theorem pullback_circuit_separation {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S)
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {K : Surface.Drawing S₀}
    {ins : Surface.Drawing S₀ → Set S₀}
    {θ θ₄ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hP : (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).IsPreRadialDrawing K)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing (capDrawing hS cap Γ)) K θ₄
      (mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)) ins)
    {C : Surface.Drawing S₀} (hC : C.IsCircuit) (hCK : C.IsSubdrawing K)
    (hClen : C.length < 2 * θ₄) :
    let H₀ := capDrawing hS cap Γ
    let E := ins C
    let K_B := closure (univ \ E)
    let A := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E)
    let B := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)
    IsClosedDisc E ∧
    discBd E = C.U ∧
    subBd E = C.U ∧
    K_B = (discInt E)ᶜ ∧
    IsClosed K_B ∧
    (A, B) ∈ 𝒯 ∧
    separationOrder A B < θ₄ ∧
    (∀ v : S, v ∈ (A ∩ B).vertexSet ↔ v ∈ Γ.V ∧ cap.emb v ∈ C.V ∩ H₀.V) ∧
    (C.V ∩ H₀.V).ncard < θ₄ ∧
    (C.V ∩ H₀.V).Nonempty := by
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : T2Space S₀ := hS₀.2.1
  have hinj_emb : Function.Injective cap.emb := cap.isEmbedding.injective
  let H₀ := capDrawing hS cap Γ
  let E := ins C
  let K_B := closure (univ \ E)
  let A := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E)
  let B := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)
  obtain ⟨hE_disc, hE_subBd, hm⟩ := hins C hC hCK hClen
  have hfrE : frontier E = C.U := (GM11.subBd_eq_frontier E).symm.trans hE_subBd
  have hE_bd : discBd E = C.U :=
    (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hE_disc).symm.trans hfrE
  have hdiscInt_eq : discInt E = interior E := by
    rw [Surface.discInt, hE_bd, ← hfrE, frontier, hE_disc.isClosed.closure_eq,
      sdiff_sdiff_right_self, inter_eq_right.mpr interior_subset]
  have hKB_eq : K_B = (discInt E)ᶜ := by
    dsimp [K_B]
    rw [hdiscInt_eq, ← closure_compl, compl_eq_univ_sdiff]
  have hKB_closed : IsClosed K_B := isClosed_closure
  have hinj_V : InjOn cap.emb Γ.toHypergraph.vertexSet := hinj_emb.injOn
  have hinj_E : InjOn (image cap.emb) Γ.toHypergraph.edgeSet :=
    (Set.image_injective.mpr hinj_emb).injOn
  have h_mapA : mapHypergraph cap.emb (image cap.emb) A =
      (PaintingOrDrawing.drawing H₀).inter E :=
    mapHypergraph_cap_inter_eq hS cap Γ E
  have h_mapB : mapHypergraph cap.emb (image cap.emb) B =
      (PaintingOrDrawing.drawing H₀).interOutside E :=
    mapHypergraph_cap_inter_eq hS cap Γ K_B
  have hA_le : A ≤ Γ.toHypergraph :=
    GM11.inter_le (Γ := PaintingOrDrawing.drawing Γ)
      (hE_disc.isClosed.preimage cap.isEmbedding.continuous)
  have hB_le : B ≤ Γ.toHypergraph :=
    GM11.inter_le (Γ := PaintingOrDrawing.drawing Γ)
      (hKB_closed.preimage cap.isEmbedding.continuous)
  have hm_orig : (A, B) ∈ truncation 𝒯 θ₄ := by
    rcases hm with ⟨⟨A₀, B₀⟩, hm₀, heq⟩
    obtain ⟨hA₀, hB₀⟩ := Prod.ext_iff.mp heq
    dsimp only at hm₀ hA₀ hB₀
    have hsep₀ := h𝒯.isSeparation hm₀.1
    have hA_eq : A₀ = A := by
      rw [← comapHypergraph_mapHypergraph hsep₀.left_le hinj_V hinj_E,
        ← comapHypergraph_mapHypergraph hA_le hinj_V hinj_E, hA₀, h_mapA]
    have hB_eq : B₀ = B := by
      rw [← comapHypergraph_mapHypergraph hsep₀.right_le hinj_V hinj_E,
        ← comapHypergraph_mapHypergraph hB_le hinj_V hinj_E, hB₀, h_mapB]
    rwa [← hA_eq, ← hB_eq]
  have hAB_V : ∀ v : S, v ∈ (A ∩ B).vertexSet ↔ v ∈ Γ.V ∧ cap.emb v ∈ C.V ∩ H₀.V := by
    intro v
    change (v ∈ Γ.V ∧ cap.emb v ∈ E) ∧ (v ∈ Γ.V ∧ cap.emb v ∈ K_B) ↔
      v ∈ Γ.V ∧ cap.emb v ∈ C.V ∩ H₀.V
    have h_inter_E : E ∩ K_B = C.U := by
      dsimp [K_B, E]
      rw [← compl_eq_univ_sdiff]
      nth_rw 1 [← hE_disc.isClosed.closure_eq]
      rw [← frontier_eq_closure_inter_closure, hfrE]
    have hCU_HV := (subdrawing_radial_inter_U hP hCK).2
    constructor
    · rintro ⟨⟨hvΓ, hvE⟩, ⟨_, hvKB⟩⟩
      have hvCU : cap.emb v ∈ C.U := h_inter_E ▸ ⟨hvE, hvKB⟩
      have hvHV : cap.emb v ∈ H₀.V := mem_image_of_mem cap.emb hvΓ
      exact ⟨hvΓ, hCU_HV ▸ ⟨hvCU, hvHV⟩⟩
    · rintro ⟨hvΓ, hvCV⟩
      have hv_in : cap.emb v ∈ E ∩ K_B := h_inter_E.symm ▸ (hCU_HV.symm ▸ hvCV).1
      exact ⟨⟨hvΓ, hv_in.1⟩, ⟨hvΓ, hv_in.2⟩⟩
  obtain ⟨hlen_eq, hCV_ne⟩ := GM12.circuit_length_eq_two_mul_ncard hP hC hCK
  exact ⟨hE_disc, hE_bd, hE_subBd, hKB_eq, hKB_closed, hm_orig.1, hm_orig.2,
    hAB_V, by omega, hCV_ne⟩

/-- Pullback of the combined separation of two circuits `C₁, C₂` of `walkDrawing K W` whose
insides meet in at most one point (`(ins C₁ ∩ ins C₂).Subsingleton`). -/
theorem pullback_two_circuits_separation {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀] [T2Space S₀]
    (hS : IsSurface S)
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {K : Surface.Drawing S₀}
    {ins : Surface.Drawing S₀ → Set S₀}
    {u₀ : S₀} {θ θ₄ θ₂ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ₄_pos : 1 ≤ θ₄)
    (hP : (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).IsPreRadialDrawing K)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing (capDrawing hS cap Γ)) K θ₄
      (mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)) ins)
    {W : GraphWalk K.toGraph u₀ u₀} (hW : W.length < 2 * θ₄)
    {C₁ C₂ : Surface.Drawing S₀}
    (hC₁ : C₁.IsCircuit) (hC₁W : C₁.IsSubdrawing (walkDrawing K W))
    (hC₂ : C₂.IsCircuit) (hC₂W : C₂.IsSubdrawing (walkDrawing K W))
    (hsub_inter : (ins C₁ ∩ ins C₂).Subsingleton) :
    let H₀ := capDrawing hS cap Γ
    let E₁ := ins C₁
    let E₂ := ins C₂
    let K_B := closure (univ \ E₁) ∩ closure (univ \ E₂)
    let A := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E₁) ∪
             (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E₂)
    let B := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)
    IsClosedDisc E₁ ∧ IsClosedDisc E₂ ∧
    discBd E₁ = C₁.U ∧ discBd E₂ = C₂.U ∧
    Disjoint (discInt E₁) E₂ ∧ Disjoint (discInt E₂) E₁ ∧
    K_B = (discInt E₁ ∪ discInt E₂)ᶜ ∧
    IsClosed K_B ∧
    (A, B) ∈ 𝒯 ∧
    separationOrder A B ≤ θ₄ ∧
    (∀ v : S, v ∈ (A ∩ B).vertexSet ↔ v ∈ Γ.V ∧ cap.emb v ∈ (C₁.V ∪ C₂.V) ∩ H₀.V) := by
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  have hinj_emb : Function.Injective cap.emb := cap.isEmbedding.injective
  have hWK : (walkDrawing K W).IsSubdrawing K := GM11.walkDrawing_isSubdrawing K W
  have hC₁K : C₁.IsSubdrawing K := hC₁W.trans hWK
  have hC₂K : C₂.IsSubdrawing K := hC₂W.trans hWK
  have hconf : IsConfined (2 * θ₄) (walkDrawing K W) := GM11.isConfined_walk W hW
  have hC₁_len : C₁.length < 2 * θ₄ := hconf C₁ hC₁ hC₁W
  have hC₂_len : C₂.length < 2 * θ₄ := hconf C₂ hC₂ hC₂W
  obtain ⟨hE₁_disc, hE₁_bd, _, hKB₁_eq, hKB₁_closed, hAB₁, _, hAB₁_V, _, hC₁V_ne⟩ :=
    pullback_circuit_separation hS cap h𝒯 hP hins hC₁ hC₁K hC₁_len
  obtain ⟨hE₂_disc, hE₂_bd, _, hKB₂_eq, hKB₂_closed, hAB₂, _, hAB₂_V, _, hC₂V_ne⟩ :=
    pullback_circuit_separation hS cap h𝒯 hP hins hC₂ hC₂K hC₂_len
  let H₀ := capDrawing hS cap Γ
  let E₁ := ins C₁
  let E₂ := ins C₂
  have h_disj_int : ∀ {D₁ D₂ : Set S₀},
      IsClosedDisc D₁ → IsClosedDisc D₂ →
      (D₁ ∩ D₂).Subsingleton →
      Disjoint (discInt D₁) D₂ := by
    intro D₁ D₂ hD₁ hD₂ hsub
    have hfr₁ : frontier D₁ = discBd D₁ := GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hD₁
    have hint₁ : discInt D₁ = interior D₁ := by
      rw [Surface.discInt, ← hfr₁, frontier, hD₁.isClosed.closure_eq,
        Set.sdiff_sdiff_right_self, inter_eq_right.mpr interior_subset]
    refine disjoint_left.mpr fun x hx_int₁ hx_D₂ => ?_
    obtain ⟨y₁, hy₁⟩ := hD₂.nonempty_discInt
    obtain ⟨y₂, hy₂⟩ := (IsOArc.isConnected' hD₂.isOArc_discBd).nonempty
    have hy12_ne : y₁ ≠ y₂ := fun h => hy₁.2 (h ▸ hy₂)
    have h_not_sub : ¬ (D₂ ⊆ D₁) := fun h =>
      hy12_ne (hsub ⟨h hy₁.1, hy₁.1⟩ ⟨h (Surface.discBd_subset D₂ hy₂), Surface.discBd_subset D₂ hy₂⟩)
    obtain ⟨z, hz_D₂, hz_not_D₁⟩ := not_subset.mp h_not_sub
    have h_conn : IsPreconnected D₂ := hD₂.isPathConnected.isConnected.isPreconnected
    have h_not_sub_union : ¬ (D₂ ⊆ interior D₁ ∪ D₁ᶜ) := by
      intro h_cov
      rcases h_conn (interior D₁) (D₁ᶜ) isOpen_interior hD₁.isClosed.isOpen_compl h_cov
        ⟨x, hx_D₂, hint₁ ▸ hx_int₁⟩ ⟨z, hz_D₂, hz_not_D₁⟩ with ⟨w, _, hw_int, hw_compl⟩
      exact hw_compl (interior_subset hw_int)
    obtain ⟨y, hy_D₂, hy_not⟩ := not_subset.mp h_not_sub_union
    rw [mem_union, not_or, notMem_compl_iff] at hy_not
    have hy_bd₁ : y ∈ discBd D₁ := by
      rw [← hfr₁, hD₁.isClosed.frontier_eq]
      exact ⟨hy_not.2, hy_not.1⟩
    have hxy : x = y := hsub ⟨hx_int₁.1, hx_D₂⟩ ⟨hy_not.2, hy_D₂⟩
    exact hx_int₁.2 (hxy ▸ hy_bd₁)
  have hdisj₁₂ : Disjoint (discInt E₁) E₂ := h_disj_int hE₁_disc hE₂_disc hsub_inter
  have hdisj₂₁ : Disjoint (discInt E₂) E₁ :=
    h_disj_int hE₂_disc hE₁_disc (inter_comm E₁ E₂ ▸ hsub_inter)
  let K_B₁ := closure (univ \ E₁)
  let K_B₂ := closure (univ \ E₂)
  let K_B := K_B₁ ∩ K_B₂
  have hKB_eq : K_B = (discInt E₁ ∪ discInt E₂)ᶜ := by
    dsimp [K_B, K_B₁, K_B₂]
    rw [hKB₁_eq, hKB₂_eq, compl_union]
  have hKB_closed : IsClosed K_B := hKB₁_closed.inter hKB₂_closed
  let A₁ := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E₁)
  let B₁ := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B₁)
  let A₂ := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E₂)
  let B₂ := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B₂)
  let A := A₁ ∪ A₂
  let B := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)
  have hB_inter : B₁ ∩ B₂ = B := by
    dsimp [B₁, B₂, B, K_B]
    rw [inter_painting_inter_eq]
  have hE₁_sub_KB₂ : E₁ ⊆ K_B₂ := by
    dsimp [K_B₂]
    rw [hKB₂_eq]
    exact disjoint_left.mp hdisj₂₁.symm
  have hE₂_sub_KB₁ : E₂ ⊆ K_B₁ := by
    dsimp [K_B₁]
    rw [hKB₁_eq]
    exact disjoint_left.mp hdisj₁₂.symm
  have hAB_V : ∀ v : S, v ∈ (A ∩ B).vertexSet ↔ v ∈ Γ.V ∧ cap.emb v ∈ (C₁.V ∪ C₂.V) ∩ H₀.V := by
    intro v
    change (v ∈ A₁.vertexSet ∨ v ∈ A₂.vertexSet) ∧ v ∈ B.vertexSet ↔
      v ∈ Γ.V ∧ cap.emb v ∈ (C₁.V ∪ C₂.V) ∩ H₀.V
    rw [← hB_inter]
    change ((v ∈ Γ.V ∧ cap.emb v ∈ E₁) ∨ (v ∈ Γ.V ∧ cap.emb v ∈ E₂)) ∧
      ((v ∈ Γ.V ∧ cap.emb v ∈ K_B₁) ∧ (v ∈ Γ.V ∧ cap.emb v ∈ K_B₂)) ↔ _
    have h₁ := hAB₁_V v
    change (v ∈ Γ.V ∧ cap.emb v ∈ E₁) ∧ (v ∈ Γ.V ∧ cap.emb v ∈ K_B₁) ↔
      v ∈ Γ.V ∧ cap.emb v ∈ C₁.V ∩ H₀.V at h₁
    have h₂ := hAB₂_V v
    change (v ∈ Γ.V ∧ cap.emb v ∈ E₂) ∧ (v ∈ Γ.V ∧ cap.emb v ∈ K_B₂) ↔
      v ∈ Γ.V ∧ cap.emb v ∈ C₂.V ∩ H₀.V at h₂
    constructor
    · rintro ⟨(⟨hvΓ, hvE₁⟩ | ⟨hvΓ, hvE₂⟩), ⟨_, hvKB₁⟩, ⟨_, hvKB₂⟩⟩
      · obtain ⟨_, hvC₁, hvH₀⟩ := h₁.mp ⟨⟨hvΓ, hvE₁⟩, ⟨hvΓ, hvKB₁⟩⟩
        exact ⟨hvΓ, Or.inl hvC₁, hvH₀⟩
      · obtain ⟨_, hvC₂, hvH₀⟩ := h₂.mp ⟨⟨hvΓ, hvE₂⟩, ⟨hvΓ, hvKB₂⟩⟩
        exact ⟨hvΓ, Or.inr hvC₂, hvH₀⟩
    · rintro ⟨hvΓ, (hvC₁ | hvC₂), hvH₀⟩
      · obtain ⟨⟨_, hvE₁⟩, ⟨_, hvKB₁⟩⟩ := h₁.mpr ⟨hvΓ, hvC₁, hvH₀⟩
        exact ⟨Or.inl ⟨hvΓ, hvE₁⟩, ⟨hvΓ, hvKB₁⟩, ⟨hvΓ, hE₁_sub_KB₂ hvE₁⟩⟩
      · obtain ⟨⟨_, hvE₂⟩, ⟨_, hvKB₂⟩⟩ := h₂.mpr ⟨hvΓ, hvC₂, hvH₀⟩
        exact ⟨Or.inr ⟨hvΓ, hvE₂⟩, ⟨hvΓ, hE₂_sub_KB₁ hvE₂⟩, ⟨hvΓ, hvKB₂⟩⟩
  have hord_le : separationOrder A B ≤ θ₄ := by
    unfold separationOrder
    have h_img_sub : cap.emb '' (A ∩ B).vertexSet ⊆ (walkDrawing K W).V ∩ H₀.V := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨_, hv12, hvH₀⟩ := (hAB_V v).mp hv
      rcases hv12 with hv1 | hv2
      · exact ⟨hC₁W.1 hv1, hvH₀⟩
      · exact ⟨hC₂W.1 hv2, hvH₀⟩
    have h_fin : ((walkDrawing K W).V ∩ H₀.V).Finite :=
      ((walkDrawing K W).finite_V).subset inter_subset_left
    rw [← Set.ncard_image_of_injective (A ∩ B).vertexSet hinj_emb]
    exact (ncard_le_ncard h_img_sub h_fin).trans (walkDrawing_inter_V_ncard_le hP W hW hθ₄_pos)
  have hsep := (h𝒯.isSeparation hAB₁).union_inter (h𝒯.isSeparation hAB₂)
  rw [hB_inter] at hsep
  have hAB : (A, B) ∈ 𝒯 := by
    rcases h𝒯.axiom1 hsep (by omega : separationOrder A B < θ) with hm | hm
    · exact hm
    · exact (h𝒯.axiom2 hAB₁ hAB₂ hm hsep.union_eq).elim
  exact ⟨hE₁_disc, hE₂_disc, hE₁_bd, hE₂_bd, hdisj₁₂, hdisj₂₁, hKB_eq, hKB_closed,
    hAB, hord_le, hAB_V⟩

/-- Splitting a circuit `C` of a pre-radial drawing `K` of `H₀` at a hub vertex `z ∈ C.V \ H₀.V`:
produces the two neighbours `u₁, u₂ ∈ C.V ∩ H₀.V` of `z` in `C`, the spoke `e₂ ∈ C.E` between
`u₂` and `z`, and the subdrawing `D_P` of `C` obtained by removing `z` and its two incident edges,
which contains all of `C.V ∩ H₀.V` and avoids `z`. -/
theorem circuit_split_at_hub {S₀ : Type} [TopologicalSpace S₀] [T2Space S₀]
    {H₀ K C : Surface.Drawing S₀}
    (hP : (PaintingOrDrawing.drawing H₀).IsPreRadialDrawing K)
    (hC : C.IsCircuit) (hCK : C.IsSubdrawing K)
    {z : S₀} (hz_CV : z ∈ C.V) (hz_not_HV : z ∉ H₀.V) :
    ∃ (u₁ u₂ : S₀) (e₂ : Set S₀) (D_P : Surface.Drawing S₀),
      u₁ ∈ C.V ∩ H₀.V ∧
      u₂ ∈ C.V ∩ H₀.V ∧
      e₂ ∈ C.E ∧
      closure e₂ ∩ K.V = {u₂, z} ∧
      D_P.IsSubdrawing C ∧
      z ∉ D_P.V ∧
      C.V ∩ H₀.V ⊆ D_P.V ∧
      ((u₁ = u₂ ∧ D_P.U = {u₁}) ∨ (u₁ ≠ u₂ ∧ IsLineWithEnds D_P.U u₁ u₂)) := by
  have hbip := GM11.bipartite_of_preRadial hP
  obtain ⟨u₀, W₀, ⟨hnd, hed⟩, hpos, hCV, hCE⟩ := hC
  have hz_W₀ : z ∈ W₀.support := by rwa [hCV, mem_ofPred_eq] at hz_CV
  obtain ⟨W₁, W₂, rfl⟩ := W₀.exists_append_of_mem hz_W₀
  let Rot : GraphWalk C.toGraph z z := W₂.append W₁
  have hmemRot : ∀ x, x ∈ Rot.support ↔ x ∈ C.V := by
    intro x
    rw [hCV, mem_ofPred_eq, GraphWalk.mem_support_append, GraphWalk.mem_support_append, or_comm]
  have hmemE : ∀ e, e ∈ Rot.edges ↔ e ∈ C.E := by
    intro e
    rw [hCE, mem_ofPred_eq, GraphWalk.edges_append, GraphWalk.edges_append,
      List.mem_append, List.mem_append, or_comm]
  have htail : Rot.support.tail.Nodup := by
    have h1 : (W₁.append W₂).support.tail = W₁.support.tail ++ W₂.support.tail := by
      rw [GraphWalk.support_append, W₁.support_eq_cons]; simp
    have h2 : Rot.support.tail = W₂.support.tail ++ W₁.support.tail := by
      rw [ GraphWalk.support_append, W₂.support_eq_cons]; simp
    rw [h2]
    rw [h1] at hnd
    exact (List.perm_append_comm.nodup_iff).mp hnd
  have hRot_pos : 0 < Rot.length := by
    rw [GraphWalk.length_append]
    rw [GraphWalk.length_append] at hpos
    omega
  cases hRot_eq : Rot with
  | nil _ =>
    rw [hRot_eq] at hRot_pos
    exact (Nat.lt_irrefl 0 hRot_pos).elim
  | @cons _ u₁ _ e₁ hl₁ R =>
    have hl₁_K : K.toGraph.IsLink e₁ z u₁ :=
      ⟨hCK.2 hl₁.1, hCK.1 hl₁.2.1, hCK.1 hl₁.2.2.1,
        (hCK.closure_inter_V hl₁.1).symm.trans hl₁.2.2.2⟩
    have hu₁_HV : u₁ ∈ H₀.V := by
      have := hbip e₁ z u₁ hl₁_K
      tauto
    have hu₁_CV : u₁ ∈ C.V := hl₁.2.2.1
    have hR_nd : R.support.Nodup := by
      rw [hRot_eq, GraphWalk.support_cons, List.tail_cons] at htail
      exact htail
    have hR_supp_CV : ∀ x ∈ C.V, x ∈ R.support := by
      intro x hx
      have hx_rot := (hmemRot x).mpr hx
      rw [hRot_eq, GraphWalk.support_cons, List.mem_cons] at hx_rot
      rcases hx_rot with rfl | hx_R
      · exact R.end_mem_support
      · exact hx_R
    have hzu₁ : z ≠ u₁ := fun h => hz_not_HV (h ▸ hu₁_HV)
    cases hRrev_eq : R.reverse with
    | nil _ =>
      exact (hzu₁ rfl).elim
    | @cons _ u₂ _ e₂ hl₂ Q =>
      have hl₂_K : K.toGraph.IsLink e₂ z u₂ :=
        ⟨hCK.2 hl₂.1, hCK.1 hl₂.2.1, hCK.1 hl₂.2.2.1,
          (hCK.closure_inter_V hl₂.1).symm.trans hl₂.2.2.2⟩
      have hu₂_HV : u₂ ∈ H₀.V := by
        have := hbip e₂ z u₂ hl₂_K
        tauto
      have hu₂_CV : u₂ ∈ C.V := hl₂.2.2.1
      have hcap_e₂ : closure e₂ ∩ K.V = {u₂, z} := by
        rw [Set.pair_comm]
        exact hl₂_K.2.2.2
      have hRrev_nd : R.reverse.support.Nodup := by
        rw [GraphWalk.support_reverse]
        exact List.nodup_reverse.mpr hR_nd
      rw [hRrev_eq, GraphWalk.support_cons] at hRrev_nd
      obtain ⟨hz_not_Q, hQ_nd⟩ := List.nodup_cons.mp hRrev_nd
      let W_P : GraphWalk C.toGraph u₁ u₂ := Q.reverse
      let D_P : Surface.Drawing S₀ := walkDrawing C W_P
      have hWP_sim : W_P.IsSimple := by
        unfold GraphWalk.IsSimple
        dsimp [W_P]
        rw [GraphWalk.support_reverse]
        exact List.nodup_reverse.mpr hQ_nd
      have hDP_sub : D_P.IsSubdrawing C := GM11.walkDrawing_isSubdrawing C W_P
      have hDP_V : ∀ x, x ∈ D_P.V ↔ x ∈ Q.support := by
        intro x
        dsimp [D_P, W_P]
        rw [GM11.walkDrawing_V, mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse]
      have hz_not_DP : z ∉ D_P.V := by
        rw [hDP_V]
        exact hz_not_Q
      have hCV_sub_DP : C.V ∩ H₀.V ⊆ D_P.V := by
        rintro x ⟨hxC, hxH⟩
        rw [hDP_V]
        have hx_R : x ∈ R.reverse.support := by
          rw [GraphWalk.support_reverse, List.mem_reverse]
          exact hR_supp_CV x hxC
        rw [hRrev_eq, GraphWalk.support_cons, List.mem_cons] at hx_R
        rcases hx_R with rfl | hx_Q
        · exact (hz_not_HV hxH).elim
        · exact hx_Q
      refine ⟨u₁, u₂, e₂, D_P, ⟨hu₁_CV, hu₁_HV⟩, ⟨hu₂_CV, hu₂_HV⟩,
        hl₂.1, hcap_e₂, hDP_sub, hz_not_DP, hCV_sub_DP, ?_⟩
      by_cases hu12 : u₁ = u₂
      · left
        refine ⟨hu12, ?_⟩
        subst hu12
        have hWP_nil : W_P.edges = [] ∧ W_P.support = [u₁] := by
          cases hWP : W_P with
          | nil _ =>
            exact ⟨rfl, rfl⟩
          | @cons _ v _ f hlf rest =>
            exfalso
            have hnd' := hWP_sim
            unfold GraphWalk.IsSimple at hnd'
            rw [hWP, GraphWalk.support_cons] at hnd'
            exact (List.nodup_cons.mp hnd').1 rest.end_mem_support
        have hDP_V_eq : D_P.V = {u₁} := by
          ext x
          dsimp [D_P]
          rw [GM11.walkDrawing_V, mem_ofPred_eq, hWP_nil.2, List.mem_singleton]
          rfl
        have hDP_E_eq : D_P.E = ∅ := by
          ext f
          dsimp [D_P]
          rw [GM11.walkDrawing_E, mem_ofPred_eq, hWP_nil.1]
          simp
        rw [Surface.Drawing.U_eq, hDP_V_eq, hDP_E_eq]
        simp
      · right
        exact ⟨hu12, GM11.isLine_of_isPathBetween (GM11.walkDrawing_isPathBetween C hWP_sim) hu12⟩

/-- Extraction of a circuit `G₁` of `walkDrawing K W` with maximal inside `ins G₁` around a cuff
`C ∈ cuffs S` and its cuff region `r` when `Disjoint (walkDrawing K W).U (r ∪ closure (cap.cuffDisc C))`. -/
theorem exists_maximal_circuit_around_cuff {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀] [T2Space S₀]
    (hS : IsSurface S)
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    (hΓ : Γ.IsProper)
    {K : Surface.Drawing S₀}
    {ins : Surface.Drawing S₀ → Set S₀}
    {u₀ : S₀} {θ₄ : ℕ}
    (hP : (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).IsPreRadialDrawing K)
    (hsl : IsSlope K (2 * θ₄) ins)
    {W : GraphWalk K.toGraph u₀ u₀} (hW : W.length < 2 * θ₄)
    {C : Set S} {r : Set S₀} (hr : IsCuffRegion hS cap Γ C r)
    {z : S₀} (hz_KV : z ∈ K.V) (hz_r : z ∈ r)
    (hz_walk : z ∈ insWalk ins K W)
    (hdisj_W : Disjoint (walkDrawing K W).U (r ∪ closure (cap.cuffDisc C))) :
    ∃ G₁ : Surface.Drawing S₀,
      G₁.IsCircuit ∧
      G₁.IsSubdrawing (walkDrawing K W) ∧
      G₁.length < 2 * θ₄ ∧
      (∀ D : Surface.Drawing S₀,
        D.IsCircuit → D.IsSubdrawing (walkDrawing K W) → ins G₁ ⊆ ins D → ins D ⊆ ins G₁) ∧
      r ∪ closure (cap.cuffDisc C) ⊆ discInt (ins G₁) := by
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : ConnectedSpace S₀ := cap.connected
  let G_W := walkDrawing K W
  have hGW_K : G_W.IsSubdrawing K := GM11.walkDrawing_isSubdrawing K W
  have hconf : IsConfined (2 * θ₄) G_W := GM11.isConfined_walk W hW
  have hz_not_W : z ∉ G_W.U :=
    fun hzU => disjoint_left.mp hdisj_W hzU (Or.inl hz_r)
  rcases hz_walk with hzU | hzC
  · exact (hz_not_W hzU).elim
  obtain ⟨C₀, ⟨hC₀_cir, hC₀_sub⟩, hz_C₀⟩ := mem_iUnion₂.mp hzC
  let 𝒞 : Set (Surface.Drawing S₀) := {D | D.IsCircuit ∧ D.IsSubdrawing G_W}
  have h𝒞_fin : 𝒞.Finite := GM11.finite_circuits G_W
  obtain ⟨m, hle_m, hm_max⟩ :=
    (h𝒞_fin.image ins).exists_le_maximal (mem_image_of_mem ins ⟨hC₀_cir, hC₀_sub⟩)
  obtain ⟨G₁, ⟨hG₁_cir, hG₁_sub⟩, rfl⟩ := hm_max.1
  have hG₁_len : G₁.length < 2 * θ₄ := hconf G₁ hG₁_cir hG₁_sub
  have hG₁_K : G₁.IsSubdrawing K := hG₁_sub.trans hGW_K
  have hz_G₁ : z ∈ ins G₁ := hle_m hz_C₀
  have hz_not_G₁U : z ∉ G₁.U := fun h => hz_not_W (hG₁_sub.U_subset h)
  have hdisj_r : Disjoint r G₁.U :=
    GM19.disjoint_region_U hcl₀ hP hr.2.1 hz_r hz_KV hG₁_K hz_not_G₁U
  have hcl_r_sub : closure r ⊆ ins G₁ :=
    GM19.closure_subset_ins hsl hG₁_cir hG₁_K hG₁_len
      (GM11.region_isPreconnected hr.2.1) hz_r hz_G₁ hdisj_r
  obtain ⟨hdisc_r, _, _⟩ := cuffDisc_closure_sdiff_subset_cuffRegion hS cap hΓ hr
  have hcl_cuff_sub : closure (cap.cuffDisc C) ⊆ closure r := closure_mono hdisc_r
  have h_sub_ins : r ∪ closure (cap.cuffDisc C) ⊆ ins G₁ :=
    union_subset (subset_closure.trans hcl_r_sub) (hcl_cuff_sub.trans hcl_r_sub)
  have hE₁_disc : IsClosedDisc (ins G₁) := hsl.isClosedDisc G₁ hG₁_cir hG₁_K hG₁_len
  have hE₁_bd : discBd (ins G₁) = G₁.U := by
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hE₁_disc, ← GM11.subBd_eq_frontier,
      hsl.subBd_eq G₁ hG₁_cir hG₁_K hG₁_len]
  have h_sub_int : r ∪ closure (cap.cuffDisc C) ⊆ discInt (ins G₁) := by
    intro x hx
    refine ⟨h_sub_ins hx, ?_⟩
    rw [hE₁_bd]
    intro hxU
    exact disjoint_left.mp hdisj_W (hG₁_sub.U_subset hxU) hx
  exact ⟨G₁, hG₁_cir, hG₁_sub, hG₁_len,
    fun D hD hDs hsub => hm_max.2 (mem_image_of_mem ins ⟨hD, hDs⟩) hsub,
    h_sub_int⟩

/-- Every line `L` (`IsLineWithEnds L u v`) is path-connected. -/
theorem isPathConnected_of_isLineWithEnds {Z : Type*} [TopologicalSpace Z]
    {L : Set Z} {u v : Z} (h : IsLineWithEnds L u v) : IsPathConnected L := by
  rcases id h with ⟨φ, _, _⟩
  have h_eq : range (Subtype.val ∘ φ) = L := by
    rw [range_comp, φ.surjective.range_eq, image_univ, Subtype.range_coe]
  rw [← h_eq]
  exact isPathConnected_range (continuous_subtype_val.comp φ.continuous)

/-- Every `O`-arc `F` (`IsOArc F`) is path-connected. -/
theorem isPathConnected_of_isOArc {Z : Type*} [TopologicalSpace Z]
    {F : Set Z} (h : IsOArc F) : IsPathConnected F := by
  rcases id h with ⟨φ⟩
  have h_eq : range (Subtype.val ∘ φ) = F := by
    rw [range_comp, φ.surjective.range_eq, image_univ, Subtype.range_coe]
  rw [← h_eq]
  exact isPathConnected_range (continuous_subtype_val.comp φ.continuous)

/-- For any walk `W : GraphWalk Γ.toGraph u v` in a drawing `Γ`, `(walkDrawing Γ W).U` is
path-connected. -/
theorem walkDrawing_isPathConnected {S₀ : Type} [TopologicalSpace S₀] [T1Space S₀]
    (Γ : Surface.Drawing S₀) {u v : S₀} (W : GraphWalk Γ.toGraph u v) :
    IsPathConnected (walkDrawing Γ W).U := by
  induction W with
  | @nil u hu =>
    have hU : (walkDrawing Γ (GraphWalk.nil hu)).U = {u} := by
      ext x
      rw [GM11.mem_walkDrawing_U]
      simp [GraphWalk.support, GraphWalk.edges]
    rw [hU]
    exact isPathConnected_singleton u
  | @cons u w v e hl rest ih =>
    have hU : (walkDrawing Γ (GraphWalk.cons hl rest)).U =
        closure e ∪ (walkDrawing Γ rest).U := by
      ext x
      rw [GM11.mem_walkDrawing_U, mem_union, GM11.mem_walkDrawing_U]
      simp only [GraphWalk.support_cons, List.mem_cons, GraphWalk.edges_cons]
      constructor
      · rintro ((rfl | h_supp) | ⟨f, rfl | hf, hxf⟩)
        · left
          have hu_ends : x ∈ ({x, w} : Set S₀) := Or.inl rfl
          rw [← hl.2.2.2] at hu_ends
          exact hu_ends.1
        · exact Or.inr (Or.inl h_supp)
        · exact Or.inl hxf
        · exact Or.inr (Or.inr ⟨f, hf, hxf⟩)
      · rintro (hxe | (h_supp | ⟨f, hf, hxf⟩))
        · exact Or.inr ⟨e, Or.inl rfl, hxe⟩
        · exact Or.inl (Or.inr h_supp)
        · exact Or.inr ⟨f, Or.inr hf, hxf⟩
    have he_pc : IsPathConnected (closure e) := by
      rcases Γ.edge_cond e hl.1 with ⟨a, b, _, _, hL⟩ | ⟨a, _, hO⟩
      · exact isPathConnected_of_isLineWithEnds hL
      · exact isPathConnected_of_isOArc hO
    have hw_cl : w ∈ closure e := by
      have hw_ends : w ∈ ({u, w} : Set S₀) := Or.inr rfl
      rw [← hl.2.2.2] at hw_ends
      exact hw_ends.1
    have hw_rest : w ∈ (walkDrawing Γ rest).U :=
      (GM11.mem_walkDrawing_U Γ rest).mpr (Or.inl rest.start_mem_support)
    rw [hU]
    exact he_pc.union ih ⟨w, hw_cl, hw_rest⟩

/-- No circuit `G₁` of `walkDrawing K W` (with `W.length < 2 * θ₄`) satisfying
`r₁ ∪ closure (cap.cuffDisc C₁) ⊆ discInt (ins G₁)` can pass through the hub vertex `z_star ∈ K.V ∩ r_star`
of any cuff region `r_star` of `S`. Consequently, `Disjoint r_star G₁.U` and
`Disjoint (cap.cuffDisc c_star) (discBd (ins G₁))`. -/
theorem no_other_cuff_hub_on_circuit {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀] [T2Space S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {K : Surface.Drawing S₀}
    {ins : Surface.Drawing S₀ → Set S₀}
    {u₀ : S₀} {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ : Γ.IsProper)
    (hΓ_loopless : ∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard)
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (hθ₄_pos : 1 ≤ θ₄)
    (h_ind2 : ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
      IsSurface S' → [ConnectedSpace S'] →
      GM19.IsCappedSurface S' Shat' →
      Nonempty (Shat' ≃ₜ S₀) →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₂ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → [ConnectedSpace S'] →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₃ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (hP : (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).IsPreRadialDrawing K)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing (capDrawing hS cap Γ)) K θ₄
      (mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)) ins)
    {W : GraphWalk K.toGraph u₀ u₀} (hW : W.length < 2 * θ₄)
    {C₁ : Set S} {r₁ : Set S₀} (hr₁ : IsCuffRegion hS cap Γ C₁ r₁)
    {G₁ : Surface.Drawing S₀} (hG₁_cir : G₁.IsCircuit)
    (hG₁_sub : G₁.IsSubdrawing (walkDrawing K W))
    (hG₁_int : r₁ ∪ closure (cap.cuffDisc C₁) ⊆ discInt (ins G₁))
    {c_star : Set S} {r_star : Set S₀} (hr_star : IsCuffRegion hS cap Γ c_star r_star)
    {z_star : S₀} (hz_KV : z_star ∈ K.V) (hz_r : z_star ∈ r_star) :
    z_star ∉ G₁.V ∧
    Disjoint r_star G₁.U ∧
    Disjoint (cap.cuffDisc c_star) (discBd (ins G₁)) := by
  classical
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : CompactSpace S₀ := hS₀.1
  haveI : ConnectedSpace S₀ := cap.connected
  have hinj_emb : Function.Injective cap.emb := cap.isEmbedding.injective
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  let H₀ := capDrawing hS cap Γ
  let G_W := walkDrawing K W
  have hGW_K : G_W.IsSubdrawing K := GM11.walkDrawing_isSubdrawing K W
  have hG₁_K : G₁.IsSubdrawing K := hG₁_sub.trans hGW_K
  have hG₁_len : G₁.length < 2 * θ₄ := GM11.isConfined_walk W hW G₁ hG₁_cir hG₁_sub
  obtain ⟨hE₁_disc, hE₁_bd, _, hKB_eq, hKB_closed, hAB, hord_lt, hAB_V, hA₁_lt, _⟩ :=
    pullback_circuit_separation hS cap h𝒯 hP hins hG₁_cir hG₁_K hG₁_len
  let E₁ := ins G₁
  let K_B := closure (univ \ E₁)
  let A := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E₁)
  let B := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)
  obtain ⟨hdisc_r_star, _, hr_star_pc⟩ := cuffDisc_closure_sdiff_subset_cuffRegion hS cap hΓ hr_star
  have hz_not_G₁V : z_star ∉ G₁.V := by
    intro hz_G₁V
    have hz_G₁U : z_star ∈ G₁.U := G₁.V_subset_U hz_G₁V
    have hz_GWU : z_star ∈ G_W.U := hG₁_sub.U_subset hz_G₁U
    have hz_not_HU : z_star ∉ H₀.U := GM11.region_subset hr_star.2.1 hz_r
    have hz_not_HV : z_star ∉ H₀.V := fun h => hz_not_HU (H₀.V_subset_U h)
    have hGW_pc : IsPathConnected G_W.U := walkDrawing_isPathConnected K W
    have hGW_norm : G_W.U ∩ H₀.U ⊆ H₀.V := by
      rw [(subdrawing_radial_inter_U hP hGW_K).1]
      exact inter_subset_right
    have hGW_card : (G_W.U ∩ H₀.V).ncard ≤ θ₄ := by
      rw [(subdrawing_radial_inter_U hP hGW_K).2]
      exact walkDrawing_inter_V_ncard_le hP W hW hθ₄_pos
    have h_no_other_conn : ∀ c ∈ cuffs S, c ≠ c_star →
        ∀ r_c : Set S₀, IsCuffRegion hS cap Γ c r_c →
          Disjoint G_W.U (r_c ∪ closure (cap.cuffDisc c)) := by
      intro c _ hc_ne r_c hr_c
      rw [Set.disjoint_iff_inter_eq_empty]
      by_contra h_ne
      exact no_cuff_conn_of_claim_5_2_7 hS cap hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd
        hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3 (Ne.symm hc_ne) hr_star hr_c
        hGW_pc hGW_norm hGW_card ⟨z_star, hz_GWU, Or.inl hz_r⟩
        (Set.nonempty_iff_ne_empty.mpr h_ne)
    have hc_star_ne_C₁ : c_star ≠ C₁ := by
      rintro rfl
      obtain ⟨x, hx_int⟩ := (cap.cuffDisc_closedDisc c_star hr_star.1).nonempty_discInt
      rw [← cap.cuffDisc_eq_discInt hS hr_star.1] at hx_int
      have hx_r₁ : x ∈ r₁ := (cuffDisc_closure_sdiff_subset_cuffRegion hS cap hΓ hr₁).1 hx_int
      have hx_r_star : x ∈ r_star := hdisc_r_star hx_int
      have hr_eq : r₁ = r_star :=
        GM11.region_eq_of_mem hr₁.2.1 hr_star.2.1 hx_r₁ hx_r_star
      have hz_int : z_star ∈ discInt E₁ := hG₁_int (Or.inl (hr_eq.symm ▸ hz_r))
      exact hz_int.2 (hE₁_bd.symm ▸ hz_G₁U)
    let CuffsRest : Set (Set S) :=
      {c ∈ (cuffs S \ {C₁}) \ {c_star} | Disjoint (cap.cuffDisc c) E₁}
    have hCuffsRest_sub : CuffsRest ⊆ cuffs S := fun c hc => hc.1.1.1
    have hCuffsRest_card : CuffsRest.ncard + 2 ≤ (cuffs S).ncard := by
      have h_sub : CuffsRest ⊆ (cuffs S \ {C₁}) \ {c_star} := fun _ hc => hc.1
      have h1 : CuffsRest.ncard ≤ ((cuffs S \ {C₁}) \ {c_star}).ncard :=
        ncard_le_ncard h_sub (hcuffs_fin.sdiff.sdiff)
      have h2 : ((cuffs S \ {C₁}) \ {c_star}).ncard + 1 = (cuffs S \ {C₁}).ncard :=
        ncard_sdiff_singleton_add_one ⟨hr_star.1, hc_star_ne_C₁⟩ hcuffs_fin.sdiff
      have h3 : (cuffs S \ {C₁}).ncard + 1 = (cuffs S).ncard :=
        ncard_sdiff_singleton_add_one hr₁.1 hcuffs_fin
      omega
    have h_not_rest_in_int : ∀ c ∈ (cuffs S \ {C₁}) \ {c_star},
        c ∉ CuffsRest → closure (cap.cuffDisc c) ⊆ discInt E₁ := by
      intro c hc hc_not
      have h_not_disj : ¬ Disjoint (cap.cuffDisc c) E₁ := fun hd => hc_not ⟨hc, hd⟩
      obtain ⟨r_c, hr_c, _, _, _, _⟩ := exists_unique_cuffRegion hS cap hΓ hc.1.1
      have hdisj_GW_c : Disjoint G_W.U (r_c ∪ closure (cap.cuffDisc c)) :=
        h_no_other_conn c hc.1.1 hc.2 r_c hr_c
      have hdisj_cl_bd : Disjoint (closure (cap.cuffDisc c)) (discBd E₁) := by
        rw [hE₁_bd]
        exact (hdisj_GW_c.mono_right subset_union_right).symm.mono_right hG₁_sub.U_subset
      have h_pre_c : IsPreconnected (cap.cuffDisc c) := by
        rw [cap.cuffDisc_eq_discInt hS hc.1.1]
        exact (cap.cuffDisc_closedDisc c hc.1.1).isPreconnected_discInt
      have h_side := hE₁_disc.side hS₀.2.2 h_pre_c
        (hdisj_cl_bd.mono_left subset_closure)
      rcases h_side with h_sub_int | h_disj
      · have hcl_sub_E₁ : closure (cap.cuffDisc c) ⊆ E₁ :=
          hE₁_disc.isClosed.closure_subset_iff.mpr
            (h_sub_int.trans (Surface.discInt_subset E₁))
        intro x hx
        exact ⟨hcl_sub_E₁ hx, disjoint_left.mp hdisj_cl_bd hx⟩
      · exact (h_not_disj h_disj).elim
    -- Shrink `closure (cap.cuffDisc c_star)` fixing `V_out = (cap.emb '' (c_star ∩ Γ.V)) \ E₁`.
    let V_out : Set S₀ := (cap.emb '' (c_star ∩ Γ.V)) \ E₁
    have hE_star_disc : IsClosedDisc (closure (cap.cuffDisc c_star)) :=
      cap.cuffDisc_closedDisc c_star hr_star.1
    have hE_star_bd : discBd (closure (cap.cuffDisc c_star)) = cap.emb '' c_star :=
      cap.cuffDisc_bd c_star hr_star.1
    have hE_star_int : discInt (closure (cap.cuffDisc c_star)) = cap.cuffDisc c_star :=
      (cap.cuffDisc_eq_discInt hS hr_star.1).symm
    have hVout_fin : V_out.Finite :=
      (((Γ.finite_V.subset inter_subset_right).image cap.emb).sdiff)
    have hVout_sub_bd : V_out ⊆ discBd (closure (cap.cuffDisc c_star)) := by
      rw [hE_star_bd]
      exact sdiff_subset.trans (image_mono inter_subset_left)
    obtain ⟨Δ₂, hΔ₂_sub_cl, hΔ₂_disc, hΔ₂_sub, hΔ₂_int, hΔ₂_bd_Vout⟩ :=
      exists_subdisc_fixing_bd_subset hE_star_disc hVout_fin hVout_sub_bd
    rw [hE_star_int] at hΔ₂_sub hΔ₂_int
    obtain ⟨q₀, hq₀_int⟩ := hΔ₂_disc.nonempty_discInt
    have hq₀_r : q₀ ∈ r_star := hdisc_r_star (hΔ₂_int hq₀_int)
    have hq₀_Δ₂ : q₀ ∈ Δ₂ := Surface.discInt_subset Δ₂ hq₀_int
    obtain ⟨γ, hγ_in⟩ := hr_star_pc.joinedIn z_star hz_r q₀ hq₀_r
    have hrange_γ : range γ ⊆ r_star := by
      rintro _ ⟨t, rfl⟩
      exact hγ_in t
    have hγ_closed : IsClosed (range γ) := (isCompact_range γ.continuous).isClosed
    have hγ_pc : IsPathConnected (range γ) := isPathConnected_range γ.continuous
    have hz_γ : z_star ∈ range γ := ⟨0, γ.source⟩
    have hq₀_γ : q₀ ∈ range γ := ⟨1, γ.target⟩
    -- Split `G₁` at `z_star` using `circuit_split_at_hub`.
    obtain ⟨u₁, u₂, e₂, D_P, hu₁, hu₂, he₂, he₂_ends, hDP_sub, hz_not_DP, hA₁_sub_DP, hDP_cases⟩ :=
      circuit_split_at_hub hP hG₁_cir hG₁_K hz_G₁V hz_not_HV
    have hDP_K : D_P.IsSubdrawing K := hDP_sub.trans hG₁_K
    have hz_not_DPU : z_star ∉ D_P.U :=
      fun h => hz_not_DP (GM19.mem_V_of_mem_U_sub hDP_K h hz_KV)
    have hdisj_r_DP : Disjoint r_star D_P.U :=
      GM19.disjoint_region_U hcl₀ hP hr_star.2.1 hz_r hz_KV hDP_K hz_not_DPU
    have hdisj_DP_Δ₂ : Disjoint D_P.U Δ₂ := by
      refine disjoint_left.mpr fun x hxDP hxΔ₂ => ?_
      rcases hΔ₂_sub hxΔ₂ with hx_open | ⟨_, hx_not_E₁⟩
      · exact disjoint_left.mp hdisj_r_DP (hdisc_r_star hx_open) hxDP
      · exact hx_not_E₁ (Surface.discBd_subset E₁ (hE₁_bd.symm ▸ hDP_sub.U_subset hxDP))
    have hu₁_DPU : u₁ ∈ D_P.U := D_P.V_subset_U (hA₁_sub_DP hu₁)
    have hu₂_DPU : u₂ ∈ D_P.U := D_P.V_subset_U (hA₁_sub_DP hu₂)
    have hu₁_bdE₁ : u₁ ∈ discBd E₁ := hE₁_bd.symm ▸ G₁.V_subset_U hu₁.1
    -- Construct `Δ₁` tangent to `E₁` at `u₁` avoiding `K_bad = Δ₂ ∪ range γ`.
    let K_bad : Set S₀ := Δ₂ ∪ range γ
    have hK_closed : IsClosed K_bad := hΔ₂_disc.isClosed.union hγ_closed
    have hu₁_not_K : u₁ ∉ K_bad := by
      rintro (hu₁_Δ₂ | hu₁_γ)
      · exact disjoint_left.mp hdisj_DP_Δ₂ hu₁_DPU hu₁_Δ₂
      · exact disjoint_left.mp hdisj_r_DP (hrange_γ hu₁_γ) hu₁_DPU
    obtain ⟨Δ₁, hΔ₁_sub_E₁, hΔ₁_disc, hΔ₁_sub, hΔ₁_int, hu₁_bd₁, hΔ₁_inter_bdE₁, hΔ₁_disj_K⟩ :=
      exists_tangent_subdisc_at_bd_point hE₁_disc hu₁_bdE₁ hK_closed hu₁_not_K
    have hdisj_12 : Disjoint Δ₁ Δ₂ := hΔ₁_disj_K.mono_right subset_union_left
    have hdisj_1_γ : Disjoint Δ₁ (range γ) := hΔ₁_disj_K.mono_right subset_union_right
    -- Analyze `P₂ = closure e₂ ∪ range γ`.
    have hu₂_ne_z : u₂ ≠ z_star := fun h => hz_not_HV (h ▸ hu₂.2)
    have he₂_K : e₂ ∈ K.E := hG₁_K.2 he₂
    have he₂_line : IsLineWithEnds (closure e₂) u₂ z_star :=
      GM11.isLine_closure he₂_K hu₂_ne_z he₂_ends
    have he₂_not_DPE : e₂ ∉ D_P.E := by
      intro he₂_DP
      exact hz_not_DPU (D_P.closure_subset_U he₂_DP he₂_line.right_mem)
    have hdisj_e₂_DP : Disjoint e₂ D_P.U :=
      GM11.edge_disjoint_U hDP_K he₂_K he₂_not_DPE
    have hcl_e₂_inter_DP : closure e₂ ∩ D_P.U = {u₂} := by
      apply Subset.antisymm
      · rintro x ⟨hx_cl, hx_DP⟩
        by_cases hx_KV : x ∈ K.V
        · have hx_ends : x ∈ ({u₂, z_star} : Set S₀) := he₂_ends ▸ ⟨hx_cl, hx_KV⟩
          rcases hx_ends with rfl | rfl
          · rfl
          · exact (hz_not_DPU hx_DP).elim
        · have hx_e₂ : x ∈ e₂ := (K.closure_diff_V he₂_K).subset ⟨hx_cl, hx_KV⟩
          exact (disjoint_left.mp hdisj_e₂_DP hx_e₂ hx_DP).elim
      · rintro x rfl
        exact ⟨he₂_line.left_mem, hu₂_DPU⟩
    let P₂ : Set S₀ := closure e₂ ∪ range γ
    have hP₂_pc : IsPathConnected P₂ :=
      (isPathConnected_of_isLineWithEnds he₂_line).union hγ_pc
        ⟨z_star, he₂_line.right_mem, hz_γ⟩
    have hP₂_inter_DP : P₂ ∩ D_P.U = {u₂} := by
      apply Subset.antisymm
      · rintro x ⟨hx_e₂ | hx_γ, hx_DP⟩
        · exact hcl_e₂_inter_DP.subset ⟨hx_e₂, hx_DP⟩
        · exact (disjoint_left.mp hdisj_r_DP (hrange_γ hx_γ) hx_DP).elim
      · rintro x rfl
        exact ⟨Or.inl he₂_line.left_mem, hu₂_DPU⟩
    have hP₂_inter_Δ₁ : P₂ ∩ Δ₁ ⊆ {u₁} := by
      rintro x ⟨hx_e₂ | hx_γ, hx_Δ₁⟩
      · have hx_bdE₁ : x ∈ discBd E₁ := hE₁_bd.symm ▸ G₁.closure_subset_U he₂ hx_e₂
        exact hΔ₁_inter_bdE₁.subset ⟨hx_Δ₁, hx_bdE₁⟩
      · exact (disjoint_left.mp hdisj_1_γ hx_Δ₁ hx_γ).elim
    have hP₂_inter_HU : P₂ ∩ H₀.U = {u₂} := by
      apply Subset.antisymm
      · rintro x ⟨hx_e₂ | hx_γ, hx_HU⟩
        · have hx_G₁U : x ∈ G₁.U := G₁.closure_subset_U he₂ hx_e₂
          have hx_A₁ : x ∈ G₁.V ∩ H₀.V :=
            (subdrawing_radial_inter_U hP hG₁_K).1 ▸ ⟨hx_G₁U, hx_HU⟩
          exact hcl_e₂_inter_DP.subset ⟨hx_e₂, D_P.V_subset_U (hA₁_sub_DP hx_A₁)⟩
        · exact (GM11.region_subset hr_star.2.1 (hrange_γ hx_γ) hx_HU).elim
      · rintro x rfl
        exact ⟨Or.inl he₂_line.left_mem, H₀.V_subset_U hu₂.2⟩
    -- Extract crossing line `L₂ ⊆ P₂` from `{u₂}` to `Δ₂`.
    have hu₂_not_Δ₂ : u₂ ∉ Δ₂ := disjoint_left.mp hdisj_DP_Δ₂ hu₂_DPU
    have hdisj_u₂_Δ₂ : Disjoint (P₂ ∩ {u₂}) (P₂ ∩ Δ₂) := by
      refine disjoint_left.mpr ?_
      rintro x ⟨_, rfl⟩ ⟨_, hx_Δ₂⟩
      exact hu₂_not_Δ₂ hx_Δ₂
    obtain ⟨L₂, a₂, b₀, hL₂_line, hL₂_sub_P₂, ha₂_mem, _, hb₀_mem, hb₀_fr, hL₂_int⟩ :=
      exists_line_crossing_of_isPathConnected hP₂_pc isClosed_singleton hΔ₂_disc.isClosed
        hdisj_u₂_Δ₂ (Or.inl he₂_line.left_mem) rfl (Or.inr hq₀_γ) hq₀_Δ₂
    have ha₂_eq : a₂ = u₂ := ha₂_mem.2
    subst ha₂_eq
    have hb₀_bd₂ : b₀ ∈ discBd Δ₂ :=
      (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hΔ₂_disc) ▸ hb₀_fr
    -- Form `L₀ = D_P.U ∪ L₂`.
    let L₀ : Set S₀ := D_P.U ∪ L₂
    have hL₀_line : IsLineWithEnds L₀ u₁ b₀ := by
      rcases hDP_cases with ⟨rfl, hDP_eq⟩ | ⟨_, hDP_line⟩
      · dsimp [L₀]
        rw [hDP_eq, singleton_union, insert_eq_of_mem hL₂_line.left_mem]
        exact hL₂_line
      · refine GM11.IsLineWithEnds.union (GM11.IsLineWithEnds.symm hDP_line) hL₂_line ?_
        apply Subset.antisymm
        · intro x ⟨hxDP, hxL₂⟩
          exact hP₂_inter_DP.subset ⟨hL₂_sub_P₂ hxL₂, hxDP⟩
        · rintro x rfl
          exact ⟨hu₂_DPU, hL₂_line.left_mem⟩
    have hdisj_c1 : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) Δ₁ :=
      fun c hc => hc.2.mono_right hΔ₁_sub_E₁
    have hdisj_c2 : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) Δ₂ := by
      intro c hc
      exact (cap.cuffDisc_disjoint c hc.1.1.1 c_star hr_star.1 hc.1.2).mono
        subset_closure hΔ₂_sub_cl
    have hKB_W : H₀.U ∩ K_B ⊆ (discInt Δ₁ ∪ discInt Δ₂)ᶜ := by
      rintro x ⟨hxU, hxKB⟩ (hx1 | hx2)
      · dsimp [K_B, E₁] at hxKB
        rw [hKB_eq] at hxKB
        exact hxKB (hΔ₁_int hx1).1
      · have hx_open : x ∈ cap.cuffDisc c_star := hΔ₂_int hx2
        exact GM11.region_subset hr_star.2.1 (hdisc_r_star hx_open) hxU
    have hW_bd_norm : (discBd Δ₁ ∪ discBd Δ₂) ∩ (H₀.U ∩ K_B) ⊆ H₀.V := by
      rintro x ⟨hx_bd1 | hx_bd2, hxU, hxKB⟩
      · rcases hΔ₁_sub (Surface.discBd_subset Δ₁ hx_bd1) with ⟨hx_intE₁, _⟩ | rfl
        · dsimp [K_B, E₁] at hxKB
          rw [hKB_eq] at hxKB
          exact (hxKB hx_intE₁).elim
        · exact hu₁.2
      · rcases hΔ₂_sub (Surface.discBd_subset Δ₂ hx_bd2) with hx_open | ⟨⟨v, ⟨_, hvV⟩, rfl⟩, _⟩
        · exact (GM11.region_subset hr_star.2.1 (hdisc_r_star hx_open) hxU).elim
        · exact mem_image_of_mem cap.emb hvV
    have hL₀_int : L₀ \ {u₁, b₀} ⊆ (Δ₁ ∪ Δ₂ ∪ ⋃ c ∈ CuffsRest, cap.cuffDisc c)ᶜ := by
      rintro x ⟨hx_DP | hx_L₂, hx_not_ends⟩ ((hx1 | hx2) | hx_c)
      · have hx_bdE₁ : x ∈ discBd E₁ := hE₁_bd.symm ▸ hDP_sub.U_subset hx_DP
        have hxu₁ : x = u₁ := hΔ₁_inter_bdE₁.subset ⟨hx1, hx_bdE₁⟩
        exact hx_not_ends (Or.inl hxu₁)
      · exact disjoint_left.mp hdisj_DP_Δ₂ hx_DP hx2
      · rcases mem_iUnion₂.mp hx_c with ⟨c, hc, hxc⟩
        obtain ⟨r_c, hr_c, _, _, _, _⟩ := exists_unique_cuffRegion hS cap hΓ hc.1.1.1
        have hdisj_GW_c := h_no_other_conn c hc.1.1.1 hc.1.2 r_c hr_c
        exact disjoint_left.mp hdisj_GW_c (hG₁_sub.U_subset (hDP_sub.U_subset hx_DP))
          (Or.inr (subset_closure hxc))
      · have hxu₁ : x = u₁ := hP₂_inter_Δ₁ ⟨hL₂_sub_P₂ hx_L₂, hx1⟩
        exact hx_not_ends (Or.inl hxu₁)
      · by_cases hxa₂ : x = a₂
        · subst hxa₂
          exact hu₂_not_Δ₂ hx2
        · have hx_out := hL₂_int ⟨hx_L₂, fun h => h.elim hxa₂ (fun hb => hx_not_ends (Or.inr hb))⟩
          exact hx_out.2 (Or.inr hx2)
      · rcases mem_iUnion₂.mp hx_c with ⟨c, hc, hxc⟩
        obtain ⟨r_c, hr_c, hdisc_rc, _, _, _⟩ := exists_unique_cuffRegion hS cap hΓ hc.1.1.1
        have hdisj_GW_c := h_no_other_conn c hc.1.1.1 hc.1.2 r_c hr_c
        rcases hL₂_sub_P₂ hx_L₂ with hx_e₂ | hx_γ
        · exact disjoint_left.mp hdisj_GW_c (hG₁_sub.U_subset (G₁.closure_subset_U he₂ hx_e₂))
            (Or.inr (subset_closure hxc))
        · have hr_eq : r_star = r_c :=
            GM11.region_eq_of_mem hr_star.2.1 hr_c.2.1 (hrange_γ hx_γ) (hdisc_rc hxc)
          exact disjoint_left.mp hdisj_GW_c hz_GWU (Or.inl (hr_eq ▸ hz_r))
    have hL₀_sub_A₁ : L₀ ∩ H₀.U ⊆ G₁.V ∩ H₀.V := by
      rintro x ⟨hx_DP | hx_L₂, hx_HU⟩
      · exact (subdrawing_radial_inter_U hP hG₁_K).1 ▸ ⟨hDP_sub.U_subset hx_DP, hx_HU⟩
      · have hxa₂ : x = a₂ := hP₂_inter_HU.subset ⟨hL₂_sub_P₂ hx_L₂, hx_HU⟩
        exact hxa₂ ▸ hu₂
    have hL₀_norm : L₀ ∩ (H₀.U ∩ K_B) ⊆ H₀.V :=
      fun x ⟨hxL₀, hxHU, _⟩ => (hL₀_sub_A₁ ⟨hxL₀, hxHU⟩).2
    have hL₀_card : (L₀ ∩ (H₀.V ∩ K_B)).ncard ≤ θ₄ := by
      have h_sub : L₀ ∩ (H₀.V ∩ K_B) ⊆ G₁.V ∩ H₀.V :=
        fun x ⟨hxL₀, hxHV, _⟩ => hL₀_sub_A₁ ⟨hxL₀, H₀.V_subset_U hxHV⟩
      exact (ncard_le_ncard h_sub (H₀.finite_V.subset inter_subset_right)).trans (le_of_lt hA₁_lt)
    have hbd_V : ∀ v ∈ B.vertexSet, cap.emb v ∉ L₀ →
        (cap.emb v ∈ discBd Δ₁ ∪ discBd Δ₂ ∪ (⋃ c ∈ CuffsRest, cap.emb '' c) ↔
          v ∈ (A ∩ B).vertexSet ∨ v ∈ Γ.V ∩ bd S) := by
      intro v hvB hv_not_L₀
      obtain ⟨hvΓ, hvKB⟩ : v ∈ Γ.V ∧ cap.emb v ∈ K_B := hvB
      have hv_not_AB : v ∉ (A ∩ B).vertexSet := by
        intro hvAB
        have hv_A₁ : cap.emb v ∈ G₁.V ∩ H₀.V := (hAB_V v).mp hvAB |>.2
        exact hv_not_L₀ (Or.inl (D_P.V_subset_U (hA₁_sub_DP hv_A₁)))
      have hv_not_E₁ : cap.emb v ∉ E₁ := by
        intro hvE₁
        exact hv_not_AB ⟨⟨hvΓ, hvE₁⟩, ⟨hvΓ, hvKB⟩⟩
      constructor
      · rintro ((hv_bd1 | hv_bd2) | hv_c)
        · exact (hv_not_E₁ (hΔ₁_sub_E₁ (Surface.discBd_subset Δ₁ hv_bd1))).elim
        · rcases hΔ₂_sub (Surface.discBd_subset Δ₂ hv_bd2) with hv_open | ⟨⟨u, ⟨hu_c, _⟩, h_eq⟩, _⟩
          · exfalso
            exact GM11.region_subset hr_star.2.1 (hdisc_r_star hv_open)
              (H₀.V_subset_U (mem_image_of_mem cap.emb hvΓ))
          · obtain rfl : u = v := hinj_emb h_eq
            refine Or.inr ⟨hvΓ, ?_⟩
            rw [← sUnion_cuffs]
            exact ⟨c_star, hr_star.1, hu_c⟩
        · rcases mem_iUnion₂.mp hv_c with ⟨c, hc, u, hu_c, h_eq⟩
          obtain rfl : u = v := hinj_emb h_eq
          refine Or.inr ⟨hvΓ, ?_⟩
          rw [← sUnion_cuffs]
          exact ⟨c, hc.1.1.1, hu_c⟩
      · rintro (hvAB | ⟨_, hv_bd⟩)
        · exact (hv_not_AB hvAB).elim
        · rw [← sUnion_cuffs] at hv_bd
          rcases hv_bd with ⟨c, hc, hvc⟩
          have hv_cl_c : cap.emb v ∈ closure (cap.cuffDisc c) :=
            Surface.discBd_subset _ ((cap.cuffDisc_bd c hc).symm ▸ mem_image_of_mem cap.emb hvc)
          have hv_not_intE₁ : cap.emb v ∉ discInt E₁ := by
            dsimp [K_B, E₁] at hvKB
            rwa [hKB_eq] at hvKB
          by_cases hc1 : c = C₁
          · subst hc1
            exact (hv_not_intE₁ (hG₁_int (Or.inr hv_cl_c))).elim
          · by_cases hc_star : c = c_star
            · subst hc_star
              have hv_Vout : cap.emb v ∈ V_out := ⟨⟨v, ⟨hvc, hvΓ⟩, rfl⟩, hv_not_E₁⟩
              exact Or.inl (Or.inr (hΔ₂_bd_Vout hv_Vout))
            · have hc_rest : c ∈ CuffsRest := by
                by_contra hc_not_rest
                exact hv_not_intE₁ (h_not_rest_in_int c ⟨⟨hc, hc1⟩, hc_star⟩ hc_not_rest hv_cl_c)
              exact Or.inr (mem_iUnion₂.mpr ⟨c, hc_rest, mem_image_of_mem cap.emb hvc⟩)
    exact contradiction_of_two_discs_and_line hS cap hΓ_loopless hΓ_bd h𝒯 hL hL_bd
      hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3 hKB_closed hAB (le_of_lt hord_lt) rfl
      hΔ₁_disc hΔ₂_disc hdisj_12 hCuffsRest_sub hCuffsRest_card hdisj_c1 hdisj_c2
      hKB_W hW_bd_norm hL₀_line hu₁_bd₁ hb₀_bd₂ hL₀_int hL₀_norm hL₀_card hbd_V
  have hz_not_G₁U : z_star ∉ G₁.U :=
    fun h => hz_not_G₁V (GM19.mem_V_of_mem_U_sub hG₁_K h hz_KV)
  have hdisj_r_G₁ : Disjoint r_star G₁.U :=
    GM19.disjoint_region_U hcl₀ hP hr_star.2.1 hz_r hz_KV hG₁_K hz_not_G₁U
  have hdisj_c_bd : Disjoint (cap.cuffDisc c_star) (discBd (ins G₁)) := by
    rw [hE₁_bd]
    exact hdisj_r_G₁.mono_left hdisc_r_star
  exact ⟨hz_not_G₁V, hdisj_r_G₁, hdisj_c_bd⟩

/-- Consequence of `no_other_cuff_hub_on_circuit` and `claim_5_2_9_and_11_core`: for any circuit
`G₁` of `walkDrawing K W` (with `W.length < 2 * θ₄`) satisfying
`r₁ ∪ closure (cap.cuffDisc C₁) ⊆ discInt (ins G₁)`, `G₁.U ⊆ range cap.emb`, `cap.emb ⁻¹' G₁.U` is a
`Γ`-normal `O`-arc in `S`, and for every cuff `c ∈ cuffs S \ {C₁}`, `Disjoint (cap.cuffDisc c) (ins G₁)`. -/
theorem circuit_around_cuff_disjoint_other_cuffDisc {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀] [T2Space S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {K : Surface.Drawing S₀}
    {ins : Surface.Drawing S₀ → Set S₀}
    {u₀ : S₀} {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ : Γ.IsProper)
    (hΓ_loopless : ∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard)
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (hθ₄_pos : 1 ≤ θ₄)
    (h_ind2 : ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
      IsSurface S' → [ConnectedSpace S'] →
      GM19.IsCappedSurface S' Shat' →
      Nonempty (Shat' ≃ₜ S₀) →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₂ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → [ConnectedSpace S'] →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₃ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (hP : (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).IsPreRadialDrawing K)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing (capDrawing hS cap Γ)) K θ₄
      (mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)) ins)
    {W : GraphWalk K.toGraph u₀ u₀} (hW : W.length < 2 * θ₄)
    {C₁ : Set S} {r₁ : Set S₀} (hr₁ : IsCuffRegion hS cap Γ C₁ r₁)
    {G₁ : Surface.Drawing S₀} (hG₁_cir : G₁.IsCircuit)
    (hG₁_sub : G₁.IsSubdrawing (walkDrawing K W))
    (hG₁_int : r₁ ∪ closure (cap.cuffDisc C₁) ⊆ discInt (ins G₁)) :
    G₁.U ⊆ range cap.emb ∧
    (∀ c ∈ cuffs S, c ≠ C₁ → Disjoint (cap.cuffDisc c) (ins G₁)) := by
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  haveI : CompactSpace S₀ := hS₀.1
  haveI : ConnectedSpace S₀ := cap.connected
  have hinj_emb : Function.Injective cap.emb := cap.isEmbedding.injective
  let H₀ := capDrawing hS cap Γ
  have hGW_K : (walkDrawing K W).IsSubdrawing K := GM11.walkDrawing_isSubdrawing K W
  have hG₁_K : G₁.IsSubdrawing K := hG₁_sub.trans hGW_K
  have hG₁_len : G₁.length < 2 * θ₄ := GM11.isConfined_walk W hW G₁ hG₁_cir hG₁_sub
  obtain ⟨hE₁_disc, hE₁_bd, hm⟩ := hins G₁ hG₁_cir hG₁_K hG₁_len
  have h_disj_bd : ∀ c ∈ cuffs S, Disjoint (cap.cuffDisc c) G₁.U := by
    intro c hc
    obtain ⟨r_c, hr_c, _, _, _, _⟩ := exists_unique_cuffRegion hS cap hΓ hc
    obtain ⟨z_c, ⟨hz_r, hz_KV⟩, _⟩ := hP.2.2.1 r_c hr_c.2.1
    obtain ⟨_, _, hdisj⟩ := no_other_cuff_hub_on_circuit hS cap hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd
      hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos hθ₄_pos h_ind2 h_ind3 hP hins hW hr₁ hG₁_cir hG₁_sub hG₁_int
      hr_c hz_KV hz_r
    obtain ⟨_, hbd_eq, _, _, _, _, _, _, _, _⟩ :=
      pullback_circuit_separation hS cap h𝒯 hP hins hG₁_cir hG₁_K hG₁_len
    rwa [hbd_eq] at hdisj
  have hG₁_range : G₁.U ⊆ range cap.emb := by
    intro x hx
    by_contra hx_not
    have hx_compl : x ∈ (range cap.emb)ᶜ := hx_not
    rw [cap.compl_eq] at hx_compl
    rcases mem_iUnion₂.mp hx_compl with ⟨c, hc, hxc⟩
    exact disjoint_left.mp (h_disj_bd c hc) hxc hx
  let F₁ : Set S := cap.emb ⁻¹' G₁.U
  have hF₁_img : cap.emb '' F₁ = G₁.U := image_preimage_eq_of_subset hG₁_range
  have hF₁_oarc : IsOArc F₁ :=
    IsOArc.pull_of_embedding cap.isEmbedding (GM11.IsCircuit.isOArc_U hG₁_cir) hG₁_range
  have hF₁_norm : (PaintingOrDrawing.drawing Γ).IsNormal F₁ := by
    rintro s ⟨hsF, hsU⟩
    have hs_G₁U : cap.emb s ∈ G₁.U := hsF
    have hs_HU : cap.emb s ∈ H₀.U := mem_image_of_mem cap.emb hsU
    have hs_HV : cap.emb s ∈ H₀.V :=
      ((subdrawing_radial_inter_U hP hG₁_K).1.subset ⟨hs_G₁U, hs_HU⟩).2
    exact (hinj_emb.mem_set_image).mp hs_HV
  have h9_core := (claim_5_2_9_and_11_core hS cap hΓ_bd h𝒯 hL hL_bd
    hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos
    (fun S' _ hS' hconn' cap' hlt_c Γ' T' L' hprop' hbd' hT' hL' =>
      @h_ind2 S' S₀ _ _ hS' hconn' cap' ⟨Homeomorph.refl S₀⟩ hlt_c Γ' hprop' hbd' T' L' hT' hL')
    (fun S' _ hS' hconn' hhomeo Γ' T' L' hprop' hbd' hT' hL' =>
      @h_ind3 S' _ hS' hconn' hhomeo Γ' hprop' hbd' T' L' hT' hL')
    hF₁_norm hF₁_oarc hE₁_disc (hE₁_bd.trans hF₁_img.symm) hm).1
  refine ⟨hG₁_range, fun c hc hc_ne => ?_⟩
  by_contra h_not_disj
  have h_not_disj₁ : ¬ Disjoint (cap.cuffDisc C₁) (ins G₁) := by
    obtain ⟨x₁, hx₁⟩ := (cap.cuffDisc_closedDisc C₁ hr₁.1).nonempty_discInt
    rw [← cap.cuffDisc_eq_discInt hS hr₁.1] at hx₁
    intro hd
    exact disjoint_left.mp hd hx₁
      (Surface.discInt_subset (ins G₁) (hG₁_int (Or.inr (subset_closure hx₁))))
  exact hc_ne (h9_core c hc C₁ hr₁.1 h_not_disj h_not_disj₁)

/-- Case (10)(i): if `G₁` is a circuit of `walkDrawing K W` (with `W.length < 2 * θ₄`) satisfying
`r₁ ∪ closure (cap.cuffDisc C₁) ⊆ discInt (ins G₁)`, then `(walkDrawing K W).U` cannot meet
`r₂ ∪ closure (cap.cuffDisc C₂)` for any cuff `C₂ ≠ C₁` and its cuff region `r₂`. -/
theorem no_walk_meets_other_cuff_of_cuff_in_discInt {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀] [T2Space S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {K : Surface.Drawing S₀}
    {ins : Surface.Drawing S₀ → Set S₀}
    {u₀ : S₀} {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ : Γ.IsProper)
    (hΓ_loopless : ∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard)
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (hθ₄_pos : 1 ≤ θ₄)
    (h_ind2 : ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
      IsSurface S' → [ConnectedSpace S'] →
      GM19.IsCappedSurface S' Shat' →
      Nonempty (Shat' ≃ₜ S₀) →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₂ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → [ConnectedSpace S'] →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₃ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (hP : (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).IsPreRadialDrawing K)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing (capDrawing hS cap Γ)) K θ₄
      (mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)) ins)
    {W : GraphWalk K.toGraph u₀ u₀} (hW : W.length < 2 * θ₄)
    {C₁ C₂ : Set S} (hne : C₁ ≠ C₂)
    {r₁ r₂ : Set S₀} (hr₁ : IsCuffRegion hS cap Γ C₁ r₁) (hr₂ : IsCuffRegion hS cap Γ C₂ r₂)
    {G₁ : Surface.Drawing S₀} (hG₁_cir : G₁.IsCircuit)
    (hG₁_sub : G₁.IsSubdrawing (walkDrawing K W))
    (hG₁_int : r₁ ∪ closure (cap.cuffDisc C₁) ⊆ discInt (ins G₁)) :
    Disjoint (walkDrawing K W).U (r₂ ∪ closure (cap.cuffDisc C₂)) := by
  classical
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : CompactSpace S₀ := hS₀.1
  haveI : ConnectedSpace S₀ := cap.connected
  have hinj_emb : Function.Injective cap.emb := cap.isEmbedding.injective
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra h_ne
  obtain ⟨z₀, hz₀_W, hz₀_r₂⟩ := Set.nonempty_iff_ne_empty.mpr h_ne
  let H₀ := capDrawing hS cap Γ
  let G_W := walkDrawing K W
  have hGW_K : G_W.IsSubdrawing K := GM11.walkDrawing_isSubdrawing K W
  have hG₁_K : G₁.IsSubdrawing K := hG₁_sub.trans hGW_K
  have hG₁_len : G₁.length < 2 * θ₄ := GM11.isConfined_walk W hW G₁ hG₁_cir hG₁_sub
  obtain ⟨hE₁_disc, hE₁_bd, _, hKB_eq, hKB_closed, hAB, hord_lt, hAB_V, _, hA₁_ne⟩ :=
    pullback_circuit_separation hS cap h𝒯 hP hins hG₁_cir hG₁_K hG₁_len
  let E₁ := ins G₁
  let K_B := closure (univ \ E₁)
  let A := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E₁)
  let B := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)
  obtain ⟨_, h_disj_other⟩ := circuit_around_cuff_disjoint_other_cuffDisc hS cap
    hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos hθ₄_pos h_ind2 h_ind3
    hP hins hW hr₁ hG₁_cir hG₁_sub hG₁_int
  obtain ⟨hdisc_r₂, _, hr₂_pc⟩ := cuffDisc_closure_sdiff_subset_cuffRegion hS cap hΓ hr₂
  have hGW_pc : IsPathConnected G_W.U := walkDrawing_isPathConnected K W
  have hGW_norm : G_W.U ∩ H₀.U ⊆ H₀.V := by
    rw [(subdrawing_radial_inter_U hP hGW_K).1]
    exact inter_subset_right
  have hGW_card : (G_W.U ∩ H₀.V).ncard ≤ θ₄ := by
    rw [(subdrawing_radial_inter_U hP hGW_K).2]
    exact walkDrawing_inter_V_ncard_le hP W hW hθ₄_pos
  have h_no_other_conn : ∀ c ∈ cuffs S, c ≠ C₂ →
      ∀ r_c : Set S₀, IsCuffRegion hS cap Γ c r_c →
        Disjoint G_W.U (r_c ∪ closure (cap.cuffDisc c)) := by
    intro c _ hc_ne r_c hr_c
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra h_ne'
    exact no_cuff_conn_of_claim_5_2_7 hS cap hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd
      hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3 (Ne.symm hc_ne) hr₂ hr_c
      hGW_pc hGW_norm hGW_card ⟨z₀, hz₀_W, hz₀_r₂⟩
      (Set.nonempty_iff_ne_empty.mpr h_ne')
  -- Shrink `closure (cap.cuffDisc C₂)` fixing `V_out₂ = (cap.emb '' (C₂ ∩ Γ.V)) \ E₁`.
  let V_out₂ : Set S₀ := (cap.emb '' (C₂ ∩ Γ.V)) \ E₁
  have hE₂_disc : IsClosedDisc (closure (cap.cuffDisc C₂)) :=
    cap.cuffDisc_closedDisc C₂ hr₂.1
  have hE₂_bd : discBd (closure (cap.cuffDisc C₂)) = cap.emb '' C₂ :=
    cap.cuffDisc_bd C₂ hr₂.1
  have hE₂_int : discInt (closure (cap.cuffDisc C₂)) = cap.cuffDisc C₂ :=
    (cap.cuffDisc_eq_discInt hS hr₂.1).symm
  have hVout₂_fin : V_out₂.Finite :=
    (((Γ.finite_V.subset inter_subset_right).image cap.emb).sdiff)
  have hVout₂_sub_bd : V_out₂ ⊆ discBd (closure (cap.cuffDisc C₂)) := by
    rw [hE₂_bd]
    exact sdiff_subset.trans (image_mono inter_subset_left)
  obtain ⟨Δ₂, hΔ₂_sub_cl, hΔ₂_disc, hΔ₂_sub, hΔ₂_int, hΔ₂_bd_Vout⟩ :=
    exists_subdisc_fixing_bd_subset hE₂_disc hVout₂_fin hVout₂_sub_bd
  rw [hE₂_int] at hΔ₂_sub hΔ₂_int
  have hdisj_12 : Disjoint E₁ Δ₂ := by
    refine disjoint_left.mpr fun x hxE₁ hxΔ₂ => ?_
    rcases hΔ₂_sub hxΔ₂ with hx_open | ⟨_, hx_not_E₁⟩
    · exact disjoint_left.mp (h_disj_other C₂ hr₂.1 hne.symm) hx_open hxE₁
    · exact hx_not_E₁ hxE₁
  -- Form the path-connected set `Z = G_W.U ∪ r₂` meeting both `E₁` and `Δ₂`.
  obtain ⟨q₀, hq₀_int⟩ := hΔ₂_disc.nonempty_discInt
  have hq₀_r₂ : q₀ ∈ r₂ := hdisc_r₂ (hΔ₂_int hq₀_int)
  have hq₀_Δ₂ : q₀ ∈ Δ₂ := Surface.discInt_subset Δ₂ hq₀_int
  have hZ_pc : IsPathConnected (G_W.U ∪ r₂) := by
    rcases hz₀_r₂ with hz₀_in_r₂ | hz₀_cl
    · exact hGW_pc.union hr₂_pc ⟨z₀, hz₀_W, hz₀_in_r₂⟩
    · by_cases hz₀_in_r₂ : z₀ ∈ r₂
      · exact hGW_pc.union hr₂_pc ⟨z₀, hz₀_W, hz₀_in_r₂⟩
      · have hz₀_bd : z₀ ∈ discBd (closure (cap.cuffDisc C₂)) := by
          by_contra hz₀_not_bd
          have hz₀_open : z₀ ∈ cap.cuffDisc C₂ := hE₂_int ▸ ⟨hz₀_cl, hz₀_not_bd⟩
          exact hz₀_in_r₂ (hdisc_r₂ hz₀_open)
        let T : Set S₀ := discBd (closure (cap.cuffDisc C₂)) \ {z₀}
        have hD_sdiff_pc : IsPathConnected (closure (cap.cuffDisc C₂) \ T) :=
          GM19.isPathConnected_disc_sdiff hE₂_disc sdiff_subset
        have h_sdiff_sub : closure (cap.cuffDisc C₂) \ T ⊆ r₂ ∪ {z₀} := by
          rintro x ⟨hx_cl, hx_not_T⟩
          by_cases hxz₀ : x = z₀
          · exact Or.inr hxz₀
          · have hx_not_bd : x ∉ discBd (closure (cap.cuffDisc C₂)) :=
              fun hx_bd => hx_not_T ⟨hx_bd, hxz₀⟩
            exact Or.inl (hdisc_r₂ (hE₂_int ▸ ⟨hx_cl, hx_not_bd⟩))
        have hq₀_sdiff : q₀ ∈ closure (cap.cuffDisc C₂) \ T :=
          ⟨hΔ₂_sub_cl hq₀_Δ₂, fun h => (hE₂_int.symm ▸ hΔ₂_int hq₀_int).2 h.1⟩
        have hz₀_sdiff : z₀ ∈ closure (cap.cuffDisc C₂) \ T :=
          ⟨hz₀_cl, fun h => h.2 rfl⟩
        have hr₂_z₀_pc : IsPathConnected (r₂ ∪ {z₀}) := by
          have h_eq : r₂ ∪ (closure (cap.cuffDisc C₂) \ T) = r₂ ∪ {z₀} :=
            Subset.antisymm (union_subset subset_union_left h_sdiff_sub)
              (union_subset subset_union_left (singleton_subset_iff.mpr (Or.inr hz₀_sdiff)))
          rw [← h_eq]
          exact hr₂_pc.union hD_sdiff_pc ⟨q₀, hq₀_r₂, hq₀_sdiff⟩
        have h_union_eq : G_W.U ∪ (r₂ ∪ {z₀}) = G_W.U ∪ r₂ := by
          rw [← Set.union_assoc, Set.union_comm G_W.U r₂, Set.union_assoc,
            Set.union_eq_self_of_subset_right (singleton_subset_iff.mpr hz₀_W), Set.union_comm]
        rw [← h_union_eq]
        exact hGW_pc.union hr₂_z₀_pc ⟨z₀, hz₀_W, Or.inr rfl⟩
  obtain ⟨p₀, hp₀_G₁V, _⟩ := hA₁_ne
  have hp₀_Z : p₀ ∈ G_W.U ∪ r₂ := Or.inl (hG₁_sub.U_subset (G₁.V_subset_U hp₀_G₁V))
  have hp₀_E₁ : p₀ ∈ E₁ := Surface.discBd_subset E₁ (hE₁_bd.symm ▸ G₁.V_subset_U hp₀_G₁V)
  obtain ⟨L₀, a₀, b₀, hL₀_line, hL₀_sub_Z, _, ha₀_fr, _, hb₀_fr, hL₀_int_Z⟩ :=
    exists_line_crossing_of_isPathConnected hZ_pc hE₁_disc.isClosed hΔ₂_disc.isClosed
      (hdisj_12.mono inter_subset_right inter_subset_right)
      hp₀_Z hp₀_E₁ (Or.inr hq₀_r₂) hq₀_Δ₂
  have ha₀_bd₁ : a₀ ∈ discBd E₁ :=
    (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hE₁_disc) ▸ ha₀_fr
  have hb₀_bd₂ : b₀ ∈ discBd Δ₂ :=
    (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hΔ₂_disc) ▸ hb₀_fr
  let CuffsRest : Set (Set S) := (cuffs S \ {C₁}) \ {C₂}
  have hCuffsRest_sub : CuffsRest ⊆ cuffs S := fun _ hc => hc.1.1
  have hCuffsRest_card : CuffsRest.ncard + 2 ≤ (cuffs S).ncard := by
    have h1 : ((cuffs S \ {C₁}) \ {C₂}).ncard + 1 = (cuffs S \ {C₁}).ncard :=
      ncard_sdiff_singleton_add_one ⟨hr₂.1, hne.symm⟩ hcuffs_fin.sdiff
    have h2 : (cuffs S \ {C₁}).ncard + 1 = (cuffs S).ncard :=
      ncard_sdiff_singleton_add_one hr₁.1 hcuffs_fin
    dsimp only [CuffsRest]
    omega
  have hdisj_c1 : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) E₁ :=
    fun c hc => h_disj_other c hc.1.1 hc.1.2
  have hdisj_c2 : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) Δ₂ := by
    intro c hc
    exact (cap.cuffDisc_disjoint c hc.1.1 C₂ hr₂.1 hc.2).mono subset_closure hΔ₂_sub_cl
  have hKB_W : H₀.U ∩ K_B ⊆ (discInt E₁ ∪ discInt Δ₂)ᶜ := by
    rintro x ⟨hxU, hxKB⟩ (hx1 | hx2)
    · dsimp [K_B, E₁] at hxKB
      rw [hKB_eq] at hxKB
      exact hxKB hx1
    · exact GM11.region_subset hr₂.2.1 (hdisc_r₂ (hΔ₂_int hx2)) hxU
  have hW_bd_norm : (discBd E₁ ∪ discBd Δ₂) ∩ (H₀.U ∩ K_B) ⊆ H₀.V := by
    rintro x ⟨hx_bd1 | hx_bd2, hxU, _⟩
    · rw [hE₁_bd] at hx_bd1
      exact ((subdrawing_radial_inter_U hP hG₁_K).1.subset ⟨hx_bd1, hxU⟩).2
    · rcases hΔ₂_sub (Surface.discBd_subset Δ₂ hx_bd2) with hx_open | ⟨⟨v, ⟨_, hvV⟩, rfl⟩, _⟩
      · exact (GM11.region_subset hr₂.2.1 (hdisc_r₂ hx_open) hxU).elim
      · exact mem_image_of_mem cap.emb hvV
  have hL₀_int : L₀ \ {a₀, b₀} ⊆ (E₁ ∪ Δ₂ ∪ ⋃ c ∈ CuffsRest, cap.cuffDisc c)ᶜ := by
    rintro x hx (hx12 | hx_c)
    · exact (hL₀_int_Z hx).2 hx12
    · rcases mem_iUnion₂.mp hx_c with ⟨c, hc, hxc⟩
      obtain ⟨r_c, hr_c, hdisc_rc, _, _, _⟩ := exists_unique_cuffRegion hS cap hΓ hc.1.1
      have hdisj_GW_c := h_no_other_conn c hc.1.1 hc.2 r_c hr_c
      rcases (hL₀_int_Z hx).1 with hx_GW | hx_r₂
      · exact disjoint_left.mp hdisj_GW_c hx_GW (Or.inr (subset_closure hxc))
      · have hr_eq : r₂ = r_c :=
          GM11.region_eq_of_mem hr₂.2.1 hr_c.2.1 hx_r₂ (hdisc_rc hxc)
        rcases hz₀_r₂ with hz₀_in_r₂ | hz₀_cl
        · exact disjoint_left.mp hdisj_GW_c hz₀_W (Or.inl (hr_eq ▸ hz₀_in_r₂))
        · exact disjoint_left.mp (h_disj_other c hc.1.1 hc.1.2) hxc
            (by
              exfalso
              exact no_cuff_conn_of_claim_5_2_7 hS cap hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd
                hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3 (Ne.symm hc.2) hr₂ hr_c
                hr₂_pc (fun y ⟨hyr₂, hyU⟩ => (GM11.region_subset hr₂.2.1 hyr₂ hyU).elim)
                (by
                  have h_empty : r₂ ∩ H₀.V = ∅ :=
                    eq_empty_iff_forall_notMem.mpr fun y ⟨hyr₂, hyV⟩ =>
                      GM11.region_subset hr₂.2.1 hyr₂ (H₀.V_subset_U hyV)
                  rw [h_empty, ncard_empty]
                  exact Nat.zero_le _)
                ⟨q₀, hq₀_r₂, Or.inl hq₀_r₂⟩ ⟨x, hx_r₂, Or.inl (hdisc_rc hxc)⟩)
  have hL₀_sub_GW : L₀ ∩ H₀.U ⊆ G_W.U ∩ H₀.U := by
    rintro x ⟨hxL₀, hxHU⟩
    rcases hL₀_sub_Z hxL₀ with hxGW | hxr₂
    · exact ⟨hxGW, hxHU⟩
    · exact (GM11.region_subset hr₂.2.1 hxr₂ hxHU).elim
  have hL₀_norm : L₀ ∩ (H₀.U ∩ K_B) ⊆ H₀.V :=
    fun x ⟨hxL₀, hxHU, _⟩ => hGW_norm (hL₀_sub_GW ⟨hxL₀, hxHU⟩)
  have hL₀_card : (L₀ ∩ (H₀.V ∩ K_B)).ncard ≤ θ₄ := by
    have h_sub : L₀ ∩ (H₀.V ∩ K_B) ⊆ G_W.U ∩ H₀.V :=
      fun x ⟨hxL₀, hxHV, _⟩ => ⟨(hL₀_sub_GW ⟨hxL₀, H₀.V_subset_U hxHV⟩).1, hxHV⟩
    exact (ncard_le_ncard h_sub (H₀.finite_V.subset inter_subset_right)).trans hGW_card
  have hbd_V : ∀ v ∈ B.vertexSet, cap.emb v ∉ L₀ →
      (cap.emb v ∈ discBd E₁ ∪ discBd Δ₂ ∪ (⋃ c ∈ CuffsRest, cap.emb '' c) ↔
        v ∈ (A ∩ B).vertexSet ∨ v ∈ Γ.V ∩ bd S) := by
    intro v hvB _
    obtain ⟨hvΓ, hvKB⟩ : v ∈ Γ.V ∧ cap.emb v ∈ K_B := hvB
    constructor
    · rintro ((hv_bd1 | hv_bd2) | hv_c)
      · rw [hE₁_bd] at hv_bd1
        have hv_A₁ : cap.emb v ∈ G₁.V ∩ H₀.V :=
          (subdrawing_radial_inter_U hP hG₁_K).2.subset ⟨hv_bd1, mem_image_of_mem cap.emb hvΓ⟩
        exact Or.inl ((hAB_V v).mpr ⟨hvΓ, hv_A₁⟩)
      · rcases hΔ₂_sub (Surface.discBd_subset Δ₂ hv_bd2) with hv_open | ⟨⟨u, ⟨hu_c, _⟩, h_eq⟩, _⟩
        · exfalso
          exact GM11.region_subset hr₂.2.1 (hdisc_r₂ hv_open)
            (H₀.V_subset_U (mem_image_of_mem cap.emb hvΓ))
        · obtain rfl : u = v := hinj_emb h_eq
          refine Or.inr ⟨hvΓ, ?_⟩
          rw [← sUnion_cuffs]
          exact ⟨C₂, hr₂.1, hu_c⟩
      · rcases mem_iUnion₂.mp hv_c with ⟨c, hc, u, hu_c, h_eq⟩
        obtain rfl : u = v := hinj_emb h_eq
        refine Or.inr ⟨hvΓ, ?_⟩
        rw [← sUnion_cuffs]
        exact ⟨c, hc.1.1, hu_c⟩
    · rintro (hvAB | ⟨_, hv_bd⟩)
      · have hv_A₁ : cap.emb v ∈ G₁.V ∩ H₀.V := ((hAB_V v).mp hvAB).2
        exact Or.inl (Or.inl (hE₁_bd.symm ▸ G₁.V_subset_U hv_A₁.1))
      · rw [← sUnion_cuffs] at hv_bd
        rcases hv_bd with ⟨c, hc, hvc⟩
        have hv_cl_c : cap.emb v ∈ closure (cap.cuffDisc c) :=
          Surface.discBd_subset _ ((cap.cuffDisc_bd c hc).symm ▸ mem_image_of_mem cap.emb hvc)
        have hv_not_intE₁ : cap.emb v ∉ discInt E₁ := by
          dsimp [K_B, E₁] at hvKB
          rwa [hKB_eq] at hvKB
        by_cases hc1 : c = C₁
        · subst hc1
          exact (hv_not_intE₁ (hG₁_int (Or.inr hv_cl_c))).elim
        · by_cases hc2 : c = C₂
          · subst hc2
            by_cases hvE₁ : cap.emb v ∈ E₁
            · refine Or.inl (Or.inl ?_)
              by_contra hv_not_bd
              exact hv_not_intE₁ ⟨hvE₁, hv_not_bd⟩
            · exact Or.inl (Or.inr (hΔ₂_bd_Vout ⟨⟨v, ⟨hvc, hvΓ⟩, rfl⟩, hvE₁⟩))
          · exact Or.inr (mem_iUnion₂.mpr ⟨c, ⟨⟨hc, hc1⟩, hc2⟩, mem_image_of_mem cap.emb hvc⟩)
  exact contradiction_of_two_discs_and_line hS cap hΓ_loopless hΓ_bd h𝒯 hL hL_bd
    hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3 hKB_closed hAB (le_of_lt hord_lt) rfl
    hE₁_disc hΔ₂_disc hdisj_12 hCuffsRest_sub hCuffsRest_card hdisj_c1 hdisj_c2
    hKB_W hW_bd_norm hL₀_line ha₀_bd₁ hb₀_bd₂ hL₀_int hL₀_norm hL₀_card hbd_V

/-- **Graph Minors XXI, (5.2), Claim (10)** (pages 20–21 of the preprint):
"(10) *If* $r_1, r_2$ *are the cuff regions corresponding to distinct cuffs* $C_1, C_2$ *then*
$d_1(r_1, r_2) \ge \theta_4$." -/
theorem claim_5_2_10 {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀] [T2Space S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d₁ : Set S₀ → Set S₀ → ℕ}
    (hΓ : Γ.IsProper)
    (hΓ_loopless : ∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard)
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (hθ₄_pos : 1 ≤ θ₄)
    (h_ind2 : ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
      IsSurface S' → [ConnectedSpace S'] →
      GM19.IsCappedSurface S' Shat' →
      Nonempty (Shat' ≃ₜ S₀) →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₂ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → [ConnectedSpace S'] →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₃ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (hd₁ : GM14.HasTangleMetric (capDrawing hS cap Γ) θ₄
      (mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)) d₁) :
    ∀ (C₁ C₂ : Set S) (r₁ r₂ : Set S₀),
      C₁ ≠ C₂ → IsCuffRegion hS cap Γ C₁ r₁ → IsCuffRegion hS cap Γ C₂ r₂ →
      θ₄ ≤ d₁ r₁ r₂ := by
  classical
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : CompactSpace S₀ := hS₀.1
  haveI : ConnectedSpace S₀ := cap.connected
  have hinj_emb : Function.Injective cap.emb := cap.isEmbedding.injective
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  let H₀ := capDrawing hS cap Γ
  obtain ⟨hResp, K, ins, hRad, hins, hd₁_eq⟩ := hd₁
  have hP : (PaintingOrDrawing.drawing H₀).IsPreRadialDrawing K := hRad.2.1
  have hsl : IsSlope K (2 * θ₄) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H₀) hcl₀ hResp.2.1.isPretangle hP.1 hins
  intro C₁ C₂ r₁ r₂ hne hr₁ hr₂
  by_contra! hlt
  have hr₁_A : r₁ ∈ H₀.A := Or.inr hr₁.2.1
  have hr₂_A : r₂ ∈ H₀.A := Or.inr hr₂.2.1
  rw [hd₁_eq r₁ hr₁_A r₂ hr₂_A] at hlt
  change GM14.tangleMetric H₀ K ins θ₄ r₁ r₂ < θ₄ at hlt
  obtain ⟨hdisc_r₁, _, hr₁_pc⟩ := cuffDisc_closure_sdiff_subset_cuffRegion hS cap hΓ hr₁
  obtain ⟨hdisc_r₂, _, hr₂_pc⟩ := cuffDisc_closure_sdiff_subset_cuffRegion hS cap hΓ hr₂
  obtain ⟨x₁, hx₁_int⟩ := (cap.cuffDisc_closedDisc C₁ hr₁.1).nonempty_discInt
  have hx₁_open : x₁ ∈ cap.cuffDisc C₁ := (cap.cuffDisc_eq_discInt hS hr₁.1).symm ▸ hx₁_int
  obtain ⟨x₂, hx₂_int⟩ := (cap.cuffDisc_closedDisc C₂ hr₂.1).nonempty_discInt
  have hx₂_open : x₂ ∈ cap.cuffDisc C₂ := (cap.cuffDisc_eq_discInt hS hr₂.1).symm ▸ hx₂_int
  have hr_ne : r₁ ≠ r₂ := by
    rintro rfl
    exact no_cuff_conn_of_claim_5_2_7 hS cap hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd
      hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3 hne hr₁ hr₂
      hr₁_pc (fun y ⟨hyr₁, hyU⟩ => (GM11.region_subset hr₁.2.1 hyr₁ hyU).elim)
      (by
        have h_empty : r₁ ∩ H₀.V = ∅ :=
          eq_empty_iff_forall_notMem.mpr fun y ⟨hyr₁, hyV⟩ =>
            GM11.region_subset hr₁.2.1 hyr₁ (H₀.V_subset_U hyV)
        rw [h_empty, ncard_empty]
        exact Nat.zero_le _)
      ⟨x₁, hdisc_r₁ hx₁_open, Or.inl (hdisc_r₁ hx₁_open)⟩
      ⟨x₁, hdisc_r₁ hx₁_open, Or.inl (hdisc_r₁ hx₁_open)⟩
  rcases GM11.tangleMetric_cases (ins := ins) (θ := θ₄) hP hr_ne with h_eq_θ | ⟨_, hwit⟩
  · omega
  obtain ⟨u₀, W, r₁', r₂', ha₁, ha₂, hW, _, hs₁, hs₂⟩ := hwit
  obtain ⟨z₁, hz₁_K, hz₁_r₁, hz₁_ins⟩ : ∃ z₁ ∈ K.V, z₁ ∈ r₁ ∧ z₁ ∈ insWalk ins K W := by
    obtain ⟨-, -, ⟨v, hv, h_eq, rfl⟩ | ⟨he, -, -⟩ | ⟨_, z₁, ⟨hz₁_K, hz₁_r₁⟩, rfl⟩⟩ := ha₁
    · exact (GM11.region_subset hr₁.2.1 (h_eq ▸ rfl) (H₀.V_subset_U hv)).elim
    · obtain ⟨z, hz⟩ := he.1
      exact (GM11.region_subset hr₁.2.1 hz (he.2.1 hz).1).elim
    · exact ⟨z₁, hz₁_K, hz₁_r₁, hs₁ rfl⟩
  obtain ⟨z₂, hz₂_K, hz₂_r₂, hz₂_ins⟩ : ∃ z₂ ∈ K.V, z₂ ∈ r₂ ∧ z₂ ∈ insWalk ins K W := by
    obtain ⟨-, -, ⟨v, hv, h_eq, rfl⟩ | ⟨he, -, -⟩ | ⟨_, z₂, ⟨hz₂_K, hz₂_r₂⟩, rfl⟩⟩ := ha₂
    · exact (GM11.region_subset hr₂.2.1 (h_eq ▸ rfl) (H₀.V_subset_U hv)).elim
    · obtain ⟨z, hz⟩ := he.1
      exact (GM11.region_subset hr₂.2.1 hz (he.2.1 hz).1).elim
    · exact ⟨z₂, hz₂_K, hz₂_r₂, hs₂ rfl⟩
  let G_W := walkDrawing K W
  have hGW_K : G_W.IsSubdrawing K := GM11.walkDrawing_isSubdrawing K W
  have hGW_pc : IsPathConnected G_W.U := walkDrawing_isPathConnected K W
  have hGW_norm : G_W.U ∩ H₀.U ⊆ H₀.V := by
    rw [(subdrawing_radial_inter_U hP hGW_K).1]
    exact inter_subset_right
  have hGW_card : (G_W.U ∩ H₀.V).ncard ≤ θ₄ := by
    rw [(subdrawing_radial_inter_U hP hGW_K).2]
    exact walkDrawing_inter_V_ncard_le hP W hW hθ₄_pos
  -- Show `G_W.U` is disjoint from `r₁ ∪ closure (cap.cuffDisc C₁)`.
  have hdisj_GW_1 : Disjoint G_W.U (r₁ ∪ closure (cap.cuffDisc C₁)) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra h_ne1
    have hdisj_GW_2 : Disjoint G_W.U (r₂ ∪ closure (cap.cuffDisc C₂)) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      by_contra h_ne2
      exact no_cuff_conn_of_claim_5_2_7 hS cap hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd
        hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3 hne hr₁ hr₂
        hGW_pc hGW_norm hGW_card
        (Set.nonempty_iff_ne_empty.mpr h_ne1) (Set.nonempty_iff_ne_empty.mpr h_ne2)
    obtain ⟨G₂, hG₂_cir, hG₂_sub, _, _, hG₂_int⟩ :=
      exists_maximal_circuit_around_cuff hS cap hΓ hP hsl hW hr₂ hz₂_K hz₂_r₂ hz₂_ins hdisj_GW_2
    have hdisj1 := no_walk_meets_other_cuff_of_cuff_in_discInt hS cap hΓ hΓ_loopless hΓ_bd
      h𝒯 hL hL_bd hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos hθ₄_pos h_ind2 h_ind3 hP hins hW
      hne.symm hr₂ hr₁ hG₂_cir hG₂_sub hG₂_int
    exact h_ne1 (Set.disjoint_iff_inter_eq_empty.mp hdisj1)
  obtain ⟨G₁, hG₁_cir, hG₁_sub, _, hG₁_max, hG₁_int⟩ :=
    exists_maximal_circuit_around_cuff hS cap hΓ hP hsl hW hr₁ hz₁_K hz₁_r₁ hz₁_ins hdisj_GW_1
  have hdisj_GW_other : ∀ c ∈ cuffs S, c ≠ C₁ →
      ∀ r_c : Set S₀, IsCuffRegion hS cap Γ c r_c →
        Disjoint G_W.U (r_c ∪ closure (cap.cuffDisc c)) := by
    intro c _ hc_ne r_c hr_c
    exact no_walk_meets_other_cuff_of_cuff_in_discInt hS cap hΓ hΓ_loopless hΓ_bd
      h𝒯 hL hL_bd hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos hθ₄_pos h_ind2 h_ind3 hP hins hW
      hc_ne.symm hr₁ hr_c hG₁_cir hG₁_sub hG₁_int
  have hdisj_GW_2 : Disjoint G_W.U (r₂ ∪ closure (cap.cuffDisc C₂)) :=
    hdisj_GW_other C₂ hr₂.1 hne.symm r₂ hr₂
  obtain ⟨G₂, hG₂_cir, hG₂_sub, _, _, hG₂_int⟩ :=
    exists_maximal_circuit_around_cuff hS cap hΓ hP hsl hW hr₂ hz₂_K hz₂_r₂ hz₂_ins hdisj_GW_2
  obtain ⟨_, hG₁_other⟩ := circuit_around_cuff_disjoint_other_cuffDisc hS cap
    hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos hθ₄_pos h_ind2 h_ind3
    hP hins hW hr₁ hG₁_cir hG₁_sub hG₁_int
  obtain ⟨_, hG₂_other⟩ := circuit_around_cuff_disjoint_other_cuffDisc hS cap
    hΓ hΓ_loopless hΓ_bd h𝒯 hL hL_bd hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos hθ₄_pos h_ind2 h_ind3
    hP hins hW hr₂ hG₂_cir hG₂_sub hG₂_int
  let E₁ := ins G₁
  let E₂ := ins G₂
  have hG₁_K : G₁.IsSubdrawing K := hG₁_sub.trans hGW_K
  have hG₂_K : G₂.IsSubdrawing K := hG₂_sub.trans hGW_K
  have hconf : IsConfined (2 * θ₄) G_W := GM11.isConfined_walk W hW
  have hG₁_len : G₁.length < 2 * θ₄ := hconf G₁ hG₁_cir hG₁_sub
  have hG₂_len : G₂.length < 2 * θ₄ := hconf G₂ hG₂_cir hG₂_sub
  obtain ⟨hE₁_disc₀, hE₁_subBd, _⟩ := hins G₁ hG₁_cir hG₁_K hG₁_len
  obtain ⟨hE₂_disc₀, hE₂_subBd, _⟩ := hins G₂ hG₂_cir hG₂_K hG₂_len
  have hE₁_bd₀ : discBd E₁ = G₁.U :=
    (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hE₁_disc₀).symm.trans
      ((GM11.subBd_eq_frontier E₁).symm.trans hE₁_subBd)
  have hE₂_bd₀ : discBd E₂ = G₂.U :=
    (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hE₂_disc₀).symm.trans
      ((GM11.subBd_eq_frontier E₂).symm.trans hE₂_subBd)
  have hx₁_E₁ : x₁ ∈ discInt E₁ := hG₁_int (Or.inr (subset_closure hx₁_open))
  have hx₁_not_E₂ : x₁ ∉ E₂ := disjoint_left.mp (hG₂_other C₁ hr₁.1 hne) hx₁_open
  have hx₂_E₂ : x₂ ∈ discInt E₂ := hG₂_int (Or.inr (subset_closure hx₂_open))
  have hx₂_not_E₁ : x₂ ∉ E₁ := disjoint_left.mp (hG₁_other C₂ hr₂.1 hne.symm) hx₂_open
  have h_not_sub₂₁ : ¬ (E₂ ⊆ E₁) :=
    fun h => hx₂_not_E₁ (h (Surface.discInt_subset E₂ hx₂_E₂))
  -- Prove `(E₁ ∩ E₂).Subsingleton`.
  have hV12_sub : (G₁.V ∩ G₂.V).Subsingleton := by
    intro a ha b hb
    by_contra hab
    exact h_not_sub₂₁ (GM19.ins_subset_of_two_common hsl hGW_K hconf hG₁_cir hG₁_sub hG₁_max
      hG₂_cir hG₂_sub ha.1 ha.2 hb.1 hb.2 hab)
  have hU12_eq_V12 : G₁.U ∩ G₂.U = G₁.V ∩ G₂.V := by
    apply Subset.antisymm
    · rintro x ⟨hx₁, hx₂⟩
      by_cases hx_KV : x ∈ K.V
      · exact ⟨GM19.mem_V_of_mem_U_sub hG₁_K hx₁ hx_KV,
          GM19.mem_V_of_mem_U_sub hG₂_K hx₂ hx_KV⟩
      · rw [G₁.U_eq] at hx₁
        rcases hx₁ with hxV₁ | hxE₁
        · exact (hx_KV (hG₁_K.1 hxV₁)).elim
        · rcases mem_iUnion₂.mp hxE₁ with ⟨e, he₁, hx_cl⟩
          have he_K : e ∈ K.E := hG₁_K.2 he₁
          have hxe : x ∈ e := (K.closure_diff_V he_K).subset ⟨hx_cl, hx_KV⟩
          have he₂ : e ∈ G₂.E := by
            by_contra he_not₂
            exact disjoint_left.mp (GM11.edge_disjoint_U hG₂_K he_K he_not₂) hxe hx₂
          rcases K.edge_cond e he_K with ⟨u, v, huv, hcap, _⟩ | ⟨u, hcap, _⟩
          · have hu_cl : u ∈ closure e ∧ u ∈ K.V := hcap.symm.subset (Or.inl rfl)
            have hv_cl : v ∈ closure e ∧ v ∈ K.V := hcap.symm.subset (Or.inr rfl)
            have hu_V12 : u ∈ G₁.V ∩ G₂.V :=
              ⟨GM19.mem_V_of_mem_U_sub hG₁_K (G₁.closure_subset_U he₁ hu_cl.1) hu_cl.2,
               GM19.mem_V_of_mem_U_sub hG₂_K (G₂.closure_subset_U he₂ hu_cl.1) hu_cl.2⟩
            have hv_V12 : v ∈ G₁.V ∩ G₂.V :=
              ⟨GM19.mem_V_of_mem_U_sub hG₁_K (G₁.closure_subset_U he₁ hv_cl.1) hv_cl.2,
               GM19.mem_V_of_mem_U_sub hG₂_K (G₂.closure_subset_U he₂ hv_cl.1) hv_cl.2⟩
            exact (huv (hV12_sub hu_V12 hv_V12)).elim
          · have hu_cl : u ∈ closure e ∧ u ∈ K.V := hcap.symm.subset rfl
            have hl_uu : K.toGraph.IsLink e u u :=
              ⟨he_K, hu_cl.2, hu_cl.2, hcap.trans (pair_eq_singleton u).symm⟩
            have hbip := GM11.bipartite_of_preRadial hP e u u hl_uu
            tauto
    · exact inter_subset_inter G₁.V_subset_U G₂.V_subset_U
  have hU12_sub : (G₁.U ∩ G₂.U).Subsingleton := hU12_eq_V12 ▸ hV12_sub
  have hG₂U_disj_int₁ : Disjoint G₂.U (discInt E₁) := by
    have h_diff_pre : IsPreconnected (G₂.U \ G₁.U) := by
      rcases hU12_sub.eq_empty_or_singleton with h_emp | ⟨w, hw⟩
      · have h_eq : G₂.U \ G₁.U = G₂.U :=
          sdiff_eq_left.mpr (disjoint_iff_inter_eq_empty.mpr (inter_comm G₂.U G₁.U ▸ h_emp))
        rw [h_eq]
        exact (isPathConnected_of_isOArc (GM11.IsCircuit.isOArc_U hG₂_cir)).isConnected.isPreconnected
      · have hw₁₂ : w ∈ G₁.U ∧ w ∈ G₂.U := hw.symm.subset (mem_singleton w)
        have h_eq : G₂.U \ G₁.U = G₂.U \ {w} := by
          ext y
          simp only [mem_sdiff, mem_singleton_iff]
          exact ⟨fun ⟨hy₂, hy₁⟩ => ⟨hy₂, fun hyw => hy₁ (hyw.symm ▸ hw₁₂.1)⟩,
            fun ⟨hy₂, hyw⟩ => ⟨hy₂, fun hy₁ => hyw (hw.subset ⟨hy₁, hy₂⟩)⟩⟩
        rw [h_eq]
        exact (Surface.isPathConnected_oArc_diff
          (GM11.IsCircuit.isOArc_U hG₂_cir) hw₁₂.2).isConnected.isPreconnected
    have h_disj_bd : Disjoint (G₂.U \ G₁.U) (discBd E₁) := by
      rw [hE₁_bd₀]
      exact disjoint_sdiff_left
    rcases hE₁_disc₀.side hS₀.2.2 h_diff_pre h_disj_bd with h_in | h_out
    · exfalso
      have hG₂U_sub : G₂.U ⊆ E₁ := by
        intro y hy₂
        by_cases hy₁ : y ∈ G₁.U
        · exact Surface.discBd_subset E₁ (hE₁_bd₀.symm ▸ hy₁)
        · exact Surface.discInt_subset E₁ (h_in ⟨hy₂, hy₁⟩)
      exact h_not_sub₂₁ ((GM11.theorem_4_2_proof hsl hGW_K).monotone G₂ G₁
        hG₂_cir hG₂_sub hG₂_len hG₁_cir hG₁_sub hG₁_len hG₂U_sub)
    · refine disjoint_left.mpr fun y hy₂ hy_int₁ => ?_
      have hy_not_G₁ : y ∉ G₁.U := hE₁_bd₀ ▸ hy_int₁.2
      exact disjoint_left.mp h_out ⟨hy₂, hy_not_G₁⟩ hy_int₁.1
  have hint₁_disj_E₂ : Disjoint (discInt E₁) E₂ := by
    have h_disj_bd₂ : Disjoint (discInt E₁) (discBd E₂) := by
      rw [hE₂_bd₀]
      exact hG₂U_disj_int₁.symm
    rcases hE₂_disc₀.side hS₀.2.2 hE₁_disc₀.isPreconnected_discInt h_disj_bd₂ with h_in | h_out
    · exact (hx₁_not_E₂ (Surface.discInt_subset E₂ (h_in hx₁_E₁))).elim
    · exact h_out
  have h_not_sub₁₂ : ¬ (E₁ ⊆ E₂) :=
    fun h => hx₁_not_E₂ (h (Surface.discInt_subset E₁ hx₁_E₁))
  have hG₁U_disj_int₂ : Disjoint G₁.U (discInt E₂) := by
    have h_diff_pre : IsPreconnected (G₁.U \ G₂.U) := by
      rcases hU12_sub.eq_empty_or_singleton with h_emp | ⟨w, hw⟩
      · have h_eq : G₁.U \ G₂.U = G₁.U :=
          sdiff_eq_left.mpr (disjoint_iff_inter_eq_empty.mpr h_emp)
        rw [h_eq]
        exact (isPathConnected_of_isOArc (GM11.IsCircuit.isOArc_U hG₁_cir)).isConnected.isPreconnected
      · have hw₁₂ : w ∈ G₁.U ∧ w ∈ G₂.U := hw.symm.subset (mem_singleton w)
        have h_eq : G₁.U \ G₂.U = G₁.U \ {w} := by
          ext y
          simp only [mem_sdiff, mem_singleton_iff]
          exact ⟨fun ⟨hy₁, hy₂⟩ => ⟨hy₁, fun hyw => hy₂ (hyw.symm ▸ hw₁₂.2)⟩,
            fun ⟨hy₁, hyw⟩ => ⟨hy₁, fun hy₂ => hyw (hw.subset ⟨hy₁, hy₂⟩)⟩⟩
        rw [h_eq]
        exact (Surface.isPathConnected_oArc_diff
          (GM11.IsCircuit.isOArc_U hG₁_cir) hw₁₂.1).isConnected.isPreconnected
    have h_disj_bd : Disjoint (G₁.U \ G₂.U) (discBd E₂) := by
      rw [hE₂_bd₀]
      exact disjoint_sdiff_left
    rcases hE₂_disc₀.side hS₀.2.2 h_diff_pre h_disj_bd with h_in | h_out
    · exfalso
      have hG₁U_sub : G₁.U ⊆ E₂ := by
        intro y hy₁
        by_cases hy₂ : y ∈ G₂.U
        · exact Surface.discBd_subset E₂ (hE₂_bd₀.symm ▸ hy₂)
        · exact Surface.discInt_subset E₂ (h_in ⟨hy₁, hy₂⟩)
      exact h_not_sub₁₂ ((GM11.theorem_4_2_proof hsl hGW_K).monotone G₁ G₂
        hG₁_cir hG₁_sub hG₁_len hG₂_cir hG₂_sub hG₂_len hG₁U_sub)
    · refine disjoint_left.mpr fun y hy₁ hy_int₂ => ?_
      have hy_not_G₂ : y ∉ G₂.U := hE₂_bd₀ ▸ hy_int₂.2
      exact disjoint_left.mp h_out ⟨hy₁, hy_not_G₂⟩ hy_int₂.1
  have hE12_sub_U12 : E₁ ∩ E₂ ⊆ G₁.U ∩ G₂.U := by
    rintro y ⟨hy₁, hy₂⟩
    have hy_bd₁ : y ∈ discBd E₁ := by
      by_contra hy_not_bd₁
      exact disjoint_left.mp hint₁_disj_E₂ ⟨hy₁, hy_not_bd₁⟩ hy₂
    have hy_bd₂ : y ∈ discBd E₂ := by
      by_contra hy_not_bd₂
      exact disjoint_left.mp hG₁U_disj_int₂ (hE₁_bd₀ ▸ hy_bd₁) ⟨hy₂, hy_not_bd₂⟩
    exact ⟨hE₁_bd₀ ▸ hy_bd₁, hE₂_bd₀ ▸ hy_bd₂⟩
  have hE12_sub : (E₁ ∩ E₂).Subsingleton := hU12_sub.anti hE12_sub_U12
  obtain ⟨hE₁_disc, hE₂_disc, hE₁_bd, hE₂_bd, hdisj₁₂, hdisj₂₁, hKB_eq, hKB_closed,
      hAB, hord_le, hAB_V⟩ :=
    pullback_two_circuits_separation hS cap h𝒯 hθ_θ₂ hθ₂_pos hθ₄_pos hP hins hW
      hG₁_cir hG₁_sub hG₂_cir hG₂_sub hE12_sub
  let K_B := closure (univ \ E₁) ∩ closure (univ \ E₂)
  let A := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E₁) ∪
           (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' E₂)
  let B := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' K_B)
  let CuffsRest : Set (Set S) := (cuffs S \ {C₁}) \ {C₂}
  have hCuffsRest_sub : CuffsRest ⊆ cuffs S := fun _ hc => hc.1.1
  have hCuffsRest_card : CuffsRest.ncard + 2 ≤ (cuffs S).ncard := by
    have h1 : ((cuffs S \ {C₁}) \ {C₂}).ncard + 1 = (cuffs S \ {C₁}).ncard :=
      ncard_sdiff_singleton_add_one ⟨hr₂.1, hne.symm⟩ hcuffs_fin.sdiff
    have h2 : (cuffs S \ {C₁}).ncard + 1 = (cuffs S).ncard :=
      ncard_sdiff_singleton_add_one hr₁.1 hcuffs_fin
    dsimp only [CuffsRest]
    omega
  have hdisj_c1 : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) E₁ :=
    fun c hc => hG₁_other c hc.1.1 hc.1.2
  have hdisj_c2 : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) E₂ :=
    fun c hc => hG₂_other c hc.1.1 hc.2
  by_cases hdisj_E12 : Disjoint E₁ E₂
  · -- Case (10)(iii): `E₁` and `E₂` are disjoint.
    rcases hG₁_cir with ⟨p₁, W₁, _, _, hV₁, _⟩
    rcases hG₂_cir with ⟨p₂, W₂, _, _, hV₂, _⟩
    have hp₁_V : p₁ ∈ G₁.V := hV₁ ▸ W₁.start_mem_support
    have hp₂_V : p₂ ∈ G₂.V := hV₂ ▸ W₂.start_mem_support
    have hp₁_GW : p₁ ∈ G_W.U := hG₁_sub.U_subset (G₁.V_subset_U hp₁_V)
    have hp₁_E₁ : p₁ ∈ E₁ := Surface.discBd_subset E₁ (hE₁_bd.symm ▸ G₁.V_subset_U hp₁_V)
    have hp₂_GW : p₂ ∈ G_W.U := hG₂_sub.U_subset (G₂.V_subset_U hp₂_V)
    have hp₂_E₂ : p₂ ∈ E₂ := Surface.discBd_subset E₂ (hE₂_bd.symm ▸ G₂.V_subset_U hp₂_V)
    obtain ⟨L₀, a₀, b₀, hL₀_line, hL₀_sub_GW, _, ha₀_fr, _, hb₀_fr, hL₀_int_GW⟩ :=
      exists_line_crossing_of_isPathConnected hGW_pc hE₁_disc.isClosed hE₂_disc.isClosed
        (hdisj_E12.mono inter_subset_right inter_subset_right)
        hp₁_GW hp₁_E₁ hp₂_GW hp₂_E₂
    have ha₀_bd₁ : a₀ ∈ discBd E₁ :=
      (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hE₁_disc) ▸ ha₀_fr
    have hb₀_bd₂ : b₀ ∈ discBd E₂ :=
      (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hE₂_disc) ▸ hb₀_fr
    have hKB_W : H₀.U ∩ K_B ⊆ (discInt E₁ ∪ discInt E₂)ᶜ := by
      rintro x ⟨_, hxKB⟩ hx12
      dsimp [K_B, E₁, E₂] at hxKB
      rw [hKB_eq] at hxKB
      exact hxKB hx12
    have hW_bd_norm : (discBd E₁ ∪ discBd E₂) ∩ (H₀.U ∩ K_B) ⊆ H₀.V := by
      rintro x ⟨hx_bd1 | hx_bd2, hxU, _⟩
      · rw [hE₁_bd] at hx_bd1
        exact ((subdrawing_radial_inter_U hP hG₁_K).1.subset ⟨hx_bd1, hxU⟩).2
      · rw [hE₂_bd] at hx_bd2
        exact ((subdrawing_radial_inter_U hP hG₂_K).1.subset ⟨hx_bd2, hxU⟩).2
    have hL₀_int : L₀ \ {a₀, b₀} ⊆ (E₁ ∪ E₂ ∪ ⋃ c ∈ CuffsRest, cap.cuffDisc c)ᶜ := by
      rintro x hx (hx12 | hx_c)
      · exact (hL₀_int_GW hx).2 hx12
      · rcases mem_iUnion₂.mp hx_c with ⟨c, hc, hxc⟩
        obtain ⟨r_c, hr_c, _, _, _, _⟩ := exists_unique_cuffRegion hS cap hΓ hc.1.1
        exact disjoint_left.mp (hdisj_GW_other c hc.1.1 hc.1.2 r_c hr_c)
          ((hL₀_int_GW hx).1) (Or.inr (subset_closure hxc))
    have hL₀_norm : L₀ ∩ (H₀.U ∩ K_B) ⊆ H₀.V :=
      fun x ⟨hxL₀, hxHU, _⟩ => hGW_norm ⟨hL₀_sub_GW hxL₀, hxHU⟩
    have hL₀_card : (L₀ ∩ (H₀.V ∩ K_B)).ncard ≤ θ₄ := by
      have h_sub : L₀ ∩ (H₀.V ∩ K_B) ⊆ G_W.U ∩ H₀.V :=
        fun x ⟨hxL₀, hxHV, _⟩ => ⟨hL₀_sub_GW hxL₀, hxHV⟩
      exact (ncard_le_ncard h_sub (H₀.finite_V.subset inter_subset_right)).trans hGW_card
    have hbd_V : ∀ v ∈ B.vertexSet, cap.emb v ∉ L₀ →
        (cap.emb v ∈ discBd E₁ ∪ discBd E₂ ∪ (⋃ c ∈ CuffsRest, cap.emb '' c) ↔
          v ∈ (A ∩ B).vertexSet ∨ v ∈ Γ.V ∩ bd S) := by
      intro v hvB _
      obtain ⟨hvΓ, hvKB⟩ : v ∈ Γ.V ∧ cap.emb v ∈ K_B := hvB
      have hv_HV : cap.emb v ∈ H₀.V := mem_image_of_mem cap.emb hvΓ
      constructor
      · rintro ((hv_bd1 | hv_bd2) | hv_c)
        · rw [hE₁_bd] at hv_bd1
          have hv_G₁V : cap.emb v ∈ G₁.V :=
            ((subdrawing_radial_inter_U hP hG₁_K).2.subset ⟨hv_bd1, hv_HV⟩).1
          exact Or.inl ((hAB_V v).mpr ⟨hvΓ, Or.inl hv_G₁V, hv_HV⟩)
        · rw [hE₂_bd] at hv_bd2
          have hv_G₂V : cap.emb v ∈ G₂.V :=
            ((subdrawing_radial_inter_U hP hG₂_K).2.subset ⟨hv_bd2, hv_HV⟩).1
          exact Or.inl ((hAB_V v).mpr ⟨hvΓ, Or.inr hv_G₂V, hv_HV⟩)
        · rcases mem_iUnion₂.mp hv_c with ⟨c, hc, u, hu_c, h_eq⟩
          obtain rfl : u = v := hinj_emb h_eq
          refine Or.inr ⟨hvΓ, ?_⟩
          rw [← sUnion_cuffs]
          exact ⟨c, hc.1.1, hu_c⟩
      · rintro (hvAB | ⟨_, hv_bd⟩)
        · obtain ⟨_, hv_G12, _⟩ := (hAB_V v).mp hvAB
          rcases hv_G12 with hv1 | hv2
          · exact Or.inl (Or.inl (hE₁_bd.symm ▸ G₁.V_subset_U hv1))
          · exact Or.inl (Or.inr (hE₂_bd.symm ▸ G₂.V_subset_U hv2))
        · rw [← sUnion_cuffs] at hv_bd
          rcases hv_bd with ⟨c, hc, hvc⟩
          have hv_cl_c : cap.emb v ∈ closure (cap.cuffDisc c) :=
            Surface.discBd_subset _ ((cap.cuffDisc_bd c hc).symm ▸ mem_image_of_mem cap.emb hvc)
          have hv_not_int : cap.emb v ∉ discInt E₁ ∪ discInt E₂ := by
            dsimp [K_B, E₁, E₂] at hvKB
            rwa [hKB_eq] at hvKB
          by_cases hc1 : c = C₁
          · subst hc1
            exact (hv_not_int (Or.inl (hG₁_int (Or.inr hv_cl_c)))).elim
          · by_cases hc2 : c = C₂
            · subst hc2
              exact (hv_not_int (Or.inr (hG₂_int (Or.inr hv_cl_c)))).elim
            · exact Or.inr (mem_iUnion₂.mpr ⟨c, ⟨⟨hc, hc1⟩, hc2⟩, mem_image_of_mem cap.emb hvc⟩)
    exact contradiction_of_two_discs_and_line hS cap hΓ_loopless hΓ_bd h𝒯 hL hL_bd
      hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3 hKB_closed hAB hord_le rfl
      hE₁_disc hE₂_disc hdisj_E12 hCuffsRest_sub hCuffsRest_card hdisj_c1 hdisj_c2
      hKB_W hW_bd_norm hL₀_line ha₀_bd₁ hb₀_bd₂ hL₀_int hL₀_norm hL₀_card hbd_V
  · -- Case (10)(ii): `E₁ ∩ E₂ = {v₀}`.
    rw [Set.not_disjoint_iff_nonempty_inter] at hdisj_E12
    obtain ⟨v₀, hv₀_12⟩ := hdisj_E12
    have hE12_eq : E₁ ∩ E₂ = {v₀} :=
      Subset.antisymm (fun x hx => hE12_sub hx hv₀_12) (singleton_subset_iff.mpr hv₀_12)
    have hv₀_U12 : v₀ ∈ G₁.U ∩ G₂.U := hE12_sub_U12 hv₀_12
    have hv₀_bd₁ : v₀ ∈ discBd E₁ := hE₁_bd.symm ▸ hv₀_U12.1
    have hv₀_bd₂ : v₀ ∈ discBd E₂ := hE₂_bd.symm ▸ hv₀_U12.2
    let A_fix : Set S₀ := (G₁.V ∩ H₀.V) \ {v₀}
    have hA_fix_fin : A_fix.Finite := (G₁.finite_V.subset inter_subset_left).sdiff
    have hA_fix_sub : A_fix ⊆ discBd E₁ := by
      rw [hE₁_bd]
      exact sdiff_subset.trans (inter_subset_left.trans G₁.V_subset_U)
    obtain ⟨Δ₁, hΔ₁_sub_E₁, hΔ₁_disc, hΔ₁_sub, hΔ₁_int, hΔ₁_bd_A, _, hΔ₁_rad⟩ :=
      exists_subdisc_fixing_bd_subset_and_int hE₁_disc isCompact_empty (empty_subset _)
        hA_fix_fin hA_fix_sub
    obtain ⟨q₀, hq₀_bd₁, L₀, hL₀_line', hL₀_sub, hL₀_inter_Δ₁⟩ :=
      hΔ₁_rad v₀ ⟨hv₀_bd₁, fun h => h.2 rfl⟩
    have hL₀_line : IsLineWithEnds L₀ q₀ v₀ := GM11.IsLineWithEnds.symm hL₀_line'
    have hdisj_Δ₁_E₂ : Disjoint Δ₁ E₂ := by
      refine disjoint_left.mpr fun x hxΔ₁ hxE₂ => ?_
      rcases hΔ₁_sub hxΔ₁ with hx_int₁ | ⟨⟨hxG₁, _⟩, hxv₀⟩
      · exact disjoint_left.mp hdisj₁₂ hx_int₁ hxE₂
      · have hxE₁ : x ∈ E₁ := Surface.discBd_subset E₁ (hE₁_bd.symm ▸ G₁.V_subset_U hxG₁)
        exact hxv₀ (hE12_eq.subset ⟨hxE₁, hxE₂⟩)
    have hdisj_c1' : ∀ c ∈ CuffsRest, Disjoint (cap.cuffDisc c) Δ₁ :=
      fun c hc => (hdisj_c1 c hc).mono_right hΔ₁_sub_E₁
    have hKB_W : H₀.U ∩ K_B ⊆ (discInt Δ₁ ∪ discInt E₂)ᶜ := by
      rintro x ⟨_, hxKB⟩ (hx1 | hx2)
      · dsimp [K_B, E₁, E₂] at hxKB
        rw [hKB_eq] at hxKB
        exact hxKB (Or.inl (hΔ₁_int hx1))
      · dsimp [K_B, E₁, E₂] at hxKB
        rw [hKB_eq] at hxKB
        exact hxKB (Or.inr hx2)
    have hW_bd_norm : (discBd Δ₁ ∪ discBd E₂) ∩ (H₀.U ∩ K_B) ⊆ H₀.V := by
      rintro x ⟨hx_bd1 | hx_bd2, hxU, hxKB⟩
      · rcases hΔ₁_sub (Surface.discBd_subset Δ₁ hx_bd1) with hx_int₁ | ⟨⟨_, hxHV⟩, _⟩
        · dsimp [K_B, E₁, E₂] at hxKB
          rw [hKB_eq] at hxKB
          exact (hxKB (Or.inl hx_int₁)).elim
        · exact hxHV
      · rw [hE₂_bd] at hx_bd2
        exact ((subdrawing_radial_inter_U hP hG₂_K).1.subset ⟨hx_bd2, hxU⟩).2
    have hL₀_int : L₀ \ {q₀, v₀} ⊆ (Δ₁ ∪ E₂ ∪ ⋃ c ∈ CuffsRest, cap.cuffDisc c)ᶜ := by
      rintro x ⟨hxL₀, hx_ne⟩ ((hxΔ₁ | hxE₂) | hx_c)
      · have hxq₀ : x = q₀ := hL₀_inter_Δ₁.subset ⟨hxL₀, hxΔ₁⟩
        exact hx_ne (Or.inl hxq₀)
      · rcases hL₀_sub hxL₀ with hx_int₁ | rfl
        · exact disjoint_left.mp hdisj₁₂ hx_int₁ hxE₂
        · exact hx_ne (Or.inr rfl)
      · rcases mem_iUnion₂.mp hx_c with ⟨c, hc, hxc⟩
        rcases hL₀_sub hxL₀ with hx_int₁ | rfl
        · exact disjoint_left.mp (hdisj_c1 c hc) hxc (Surface.discInt_subset E₁ hx_int₁)
        · exact disjoint_left.mp (hdisj_c1 c hc) hxc hv₀_12.1
    have hL₀_inter_KB : L₀ ∩ K_B ⊆ {v₀} := by
      rintro x ⟨hxL₀, hxKB⟩
      rcases hL₀_sub hxL₀ with hx_int₁ | rfl
      · dsimp [K_B, E₁, E₂] at hxKB
        rw [hKB_eq] at hxKB
        exact (hxKB (Or.inl hx_int₁)).elim
      · rfl
    have hL₀_norm : L₀ ∩ (H₀.U ∩ K_B) ⊆ H₀.V := by
      rintro x ⟨hxL₀, hxHU, hxKB⟩
      have hxv₀ : x = v₀ := hL₀_inter_KB ⟨hxL₀, hxKB⟩
      subst hxv₀
      exact ((subdrawing_radial_inter_U hP hG₁_K).1.subset ⟨hv₀_U12.1, hxHU⟩).2
    have hL₀_card : (L₀ ∩ (H₀.V ∩ K_B)).ncard ≤ θ₄ := by
      have h_sub : L₀ ∩ (H₀.V ∩ K_B) ⊆ {v₀} :=
        fun x ⟨hxL₀, _, hxKB⟩ => hL₀_inter_KB ⟨hxL₀, hxKB⟩
      calc (L₀ ∩ (H₀.V ∩ K_B)).ncard
          ≤ ({v₀} : Set S₀).ncard := ncard_le_ncard h_sub (finite_singleton v₀)
        _ = 1 := ncard_singleton v₀
        _ ≤ θ₄ := hθ₄_pos
    have hbd_V : ∀ v ∈ B.vertexSet, cap.emb v ∉ L₀ →
        (cap.emb v ∈ discBd Δ₁ ∪ discBd E₂ ∪ (⋃ c ∈ CuffsRest, cap.emb '' c) ↔
          v ∈ (A ∩ B).vertexSet ∨ v ∈ Γ.V ∩ bd S) := by
      intro v hvB hv_not_L₀
      obtain ⟨hvΓ, hvKB⟩ : v ∈ Γ.V ∧ cap.emb v ∈ K_B := hvB
      have hv_HV : cap.emb v ∈ H₀.V := mem_image_of_mem cap.emb hvΓ
      have hv_ne_v₀ : cap.emb v ≠ v₀ := fun h => hv_not_L₀ (h ▸ hL₀_line.right_mem)
      constructor
      · rintro ((hv_bd1 | hv_bd2) | hv_c)
        · rcases hΔ₁_sub (Surface.discBd_subset Δ₁ hv_bd1) with hv_int₁ | ⟨⟨hv_G₁V, _⟩, _⟩
          · dsimp [K_B, E₁, E₂] at hvKB
            rw [hKB_eq] at hvKB
            exact (hvKB (Or.inl hv_int₁)).elim
          · exact Or.inl ((hAB_V v).mpr ⟨hvΓ, Or.inl hv_G₁V, hv_HV⟩)
        · rw [hE₂_bd] at hv_bd2
          have hv_G₂V : cap.emb v ∈ G₂.V :=
            ((subdrawing_radial_inter_U hP hG₂_K).2.subset ⟨hv_bd2, hv_HV⟩).1
          exact Or.inl ((hAB_V v).mpr ⟨hvΓ, Or.inr hv_G₂V, hv_HV⟩)
        · rcases mem_iUnion₂.mp hv_c with ⟨c, hc, u, hu_c, h_eq⟩
          obtain rfl : u = v := hinj_emb h_eq
          refine Or.inr ⟨hvΓ, ?_⟩
          rw [← sUnion_cuffs]
          exact ⟨c, hc.1.1, hu_c⟩
      · rintro (hvAB | ⟨_, hv_bd⟩)
        · obtain ⟨_, hv_G12, _⟩ := (hAB_V v).mp hvAB
          rcases hv_G12 with hv1 | hv2
          · exact Or.inl (Or.inl (hΔ₁_bd_A ⟨⟨hv1, hv_HV⟩, hv_ne_v₀⟩))
          · exact Or.inl (Or.inr (hE₂_bd.symm ▸ G₂.V_subset_U hv2))
        · rw [← sUnion_cuffs] at hv_bd
          rcases hv_bd with ⟨c, hc, hvc⟩
          have hv_cl_c : cap.emb v ∈ closure (cap.cuffDisc c) :=
            Surface.discBd_subset _ ((cap.cuffDisc_bd c hc).symm ▸ mem_image_of_mem cap.emb hvc)
          have hv_not_int : cap.emb v ∉ discInt E₁ ∪ discInt E₂ := by
            dsimp [K_B, E₁, E₂] at hvKB
            rwa [hKB_eq] at hvKB
          by_cases hc1 : c = C₁
          · subst hc1
            exact (hv_not_int (Or.inl (hG₁_int (Or.inr hv_cl_c)))).elim
          · by_cases hc2 : c = C₂
            · subst hc2
              exact (hv_not_int (Or.inr (hG₂_int (Or.inr hv_cl_c)))).elim
            · exact Or.inr (mem_iUnion₂.mpr ⟨c, ⟨⟨hc, hc1⟩, hc2⟩, mem_image_of_mem cap.emb hvc⟩)
    exact contradiction_of_two_discs_and_line hS cap hΓ_loopless hΓ_bd h𝒯 hL hL_bd
      hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos h_ind2 h_ind3 hKB_closed hAB hord_le rfl
      hΔ₁_disc hE₂_disc hdisj_Δ₁_E₂ hCuffsRest_sub hCuffsRest_card hdisj_c1' hdisj_c2
      hKB_W hW_bd_norm hL₀_line hq₀_bd₁ hv₀_bd₂ hL₀_int hL₀_norm hL₀_card hbd_V

end GM21
end GraphMinor
