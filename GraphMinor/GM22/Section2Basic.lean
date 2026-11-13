module

public import GraphMinor.GM22.Cited
public import GraphMinor.GM09.Basic
public import GraphMinor.GM06.Section3Basic

/-!
# Graph Minors XXII, Section 2 (Part 1): Effect on $Z$, Vital Subgraphs, and Proofs of 2.2 and 2.4

This file proves the basic properties of `AreConnectedIn`, `effectOn`, and `IsVitalFor`, together
with **2.2** (`theorem_2_2`) and **2.4** (`theorem_2_4`) of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (pages 531–532).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09

universe u v w

variable {α : Type u} {β : Type v}

/-! ## 1. Characterizations of `AreConnectedIn` and `effectOn` -/

/-- Two vertices `u, v` are `L`-connected if and only if `u, v ∈ V(L)` and there is a walk in `L`
from `u` to `v`. -/
theorem areConnectedIn_iff_walk {L : Graph α β} {u v : α} :
    AreConnectedIn L u v ↔ u ∈ V(L) ∧ v ∈ V(L) ∧ Nonempty (GraphWalk L u v) := by
  constructor
  · rintro ⟨C, hC, hu, hv⟩
    obtain ⟨W⟩ := hC.2.1.2 u hu v hv
    obtain ⟨W', _, _⟩ := exists_walk_up_of_le hC.1 W
    exact ⟨hC.1.vertexSet_mono hu, hC.1.vertexSet_mono hv, ⟨W'⟩⟩
  · rintro ⟨hu, hv, ⟨W⟩⟩
    exact ⟨compOf L u, isGraphComponent_compOf hu, self_mem_reachSet hu, hv, ⟨W⟩⟩

theorem areConnectedIn_self_iff {L : Graph α β} {u : α} :
    AreConnectedIn L u u ↔ u ∈ V(L) := by
  rw [areConnectedIn_iff_walk]
  exact ⟨fun h => h.1, fun hu => ⟨hu, hu, ⟨.nil hu⟩⟩⟩

theorem AreConnectedIn.left_mem {L : Graph α β} {u v : α} (h : AreConnectedIn L u v) :
    u ∈ V(L) :=
  (areConnectedIn_iff_walk.mp h).1

theorem AreConnectedIn.right_mem {L : Graph α β} {u v : α} (h : AreConnectedIn L u v) :
    v ∈ V(L) :=
  (areConnectedIn_iff_walk.mp h).2.1

theorem AreConnectedIn.symm {L : Graph α β} {u v : α} (h : AreConnectedIn L u v) :
    AreConnectedIn L v u := by
  rcases h with ⟨C, hC, hu, hv⟩
  exact ⟨C, hC, hv, hu⟩

theorem AreConnectedIn.trans {L : Graph α β} {u v w : α}
    (h₁ : AreConnectedIn L u v) (h₂ : AreConnectedIn L v w) :
    AreConnectedIn L u w := by
  rw [areConnectedIn_iff_walk] at h₁ h₂ ⊢
  rcases h₁ with ⟨hu, _, ⟨W₁⟩⟩
  rcases h₂ with ⟨_, hw, ⟨W₂⟩⟩
  exact ⟨hu, hw, ⟨W₁.append W₂⟩⟩

theorem AreConnectedIn.mono {L₁ L₂ : Graph α β} (hle : L₁ ≤ L₂) {u v : α}
    (h : AreConnectedIn L₁ u v) : AreConnectedIn L₂ u v := by
  rw [areConnectedIn_iff_walk] at h ⊢
  rcases h with ⟨hu, hv, ⟨W⟩⟩
  obtain ⟨W', _, _⟩ := exists_walk_up_of_le hle W
  exact ⟨hle.vertexSet_mono hu, hle.vertexSet_mono hv, ⟨W'⟩⟩

theorem areConnectedIn_iff_exists_path {L : Graph α β} {u v : α} :
    AreConnectedIn L u v ↔ ∃ P : Graph α β, IsGraphPathWithEnds L P u v := by
  rw [areConnectedIn_iff_walk]
  constructor
  · rintro ⟨_, _, ⟨W⟩⟩
    obtain ⟨P, hP, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
    exact ⟨P, hP⟩
  · rintro ⟨P, hP⟩
    have hPL := hP.1
    have hleft := hP.left_mem
    have hright := hP.right_mem
    rcases hP with ⟨_, W, _, _, _⟩
    obtain ⟨W', _, _⟩ := exists_walk_up_of_le hPL W
    exact ⟨hPL.vertexSet_mono hleft, hPL.vertexSet_mono hright, ⟨W'⟩⟩

/-- Two subgraphs `L₁, L₂` have the same effect on `Z` if and only if for all `u, v ∈ Z`, `u, v`
are `L₁`-connected if and only if they are `L₂`-connected. -/
theorem effectOn_eq_iff_areConnectedIn {L₁ L₂ : Graph α β} {Z : Set α} :
    effectOn L₁ Z = effectOn L₂ Z ↔
      ∀ u ∈ Z, ∀ v ∈ Z, (AreConnectedIn L₁ u v ↔ AreConnectedIn L₂ u v) := by
  constructor
  · intro heq u hu v hv
    have imp_of_eq : ∀ {M₁ M₂ : Graph α β}, effectOn M₁ Z = effectOn M₂ Z →
        AreConnectedIn M₁ u v → AreConnectedIn M₂ u v := by
      intro M₁ M₂ hM ⟨C₁, hC₁, hu₁, hv₁⟩
      have hmem : V(C₁) ∩ Z ∈ effectOn M₁ Z :=
        ⟨⟨u, hu₁, hu⟩, C₁, hC₁, rfl⟩
      rw [hM] at hmem
      rcases hmem with ⟨_, C₂, hC₂, hB⟩
      have hu₂ : u ∈ V(C₂) ∩ Z := by rw [← hB]; exact ⟨hu₁, hu⟩
      have hv₂ : v ∈ V(C₂) ∩ Z := by rw [← hB]; exact ⟨hv₁, hv⟩
      exact ⟨C₂, hC₂, hu₂.1, hv₂.1⟩
    exact ⟨imp_of_eq heq, imp_of_eq heq.symm⟩
  · intro hiff
    have sub_of_iff : ∀ {M₁ M₂ : Graph α β},
        (∀ u ∈ Z, ∀ v ∈ Z, AreConnectedIn M₁ u v ↔ AreConnectedIn M₂ u v) →
        effectOn M₁ Z ⊆ effectOn M₂ Z := by
      rintro M₁ M₂ h B ⟨⟨u, huB⟩, C₁, hC₁, rfl⟩
      rcases huB with ⟨huC₁, huZ⟩
      have hu₁ : AreConnectedIn M₁ u u := ⟨C₁, hC₁, huC₁, huC₁⟩
      have hu₂ : AreConnectedIn M₂ u u := (h u huZ u huZ).mp hu₁
      rcases hu₂ with ⟨C₂, hC₂, huC₂, _⟩
      refine ⟨⟨u, huC₁, huZ⟩, C₂, hC₂, ?_⟩
      ext v
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨hvC₁, hvZ⟩
        have hconn₁ : AreConnectedIn M₁ u v := ⟨C₁, hC₁, huC₁, hvC₁⟩
        have hconn₂ : AreConnectedIn M₂ u v := (h u huZ v hvZ).mp hconn₁
        rcases hconn₂ with ⟨C₂', hC₂', huC₂', hvC₂'⟩
        have heqC : C₂' = C₂ := isGraphComponent_eq_of_mem_inter hC₂' hC₂ ⟨u, huC₂', huC₂⟩
        exact ⟨heqC ▸ hvC₂', hvZ⟩
      · rintro ⟨hvC₂, hvZ⟩
        have hconn₂ : AreConnectedIn M₂ u v := ⟨C₂, hC₂, huC₂, hvC₂⟩
        have hconn₁ : AreConnectedIn M₁ u v := (h u huZ v hvZ).mpr hconn₂
        rcases hconn₁ with ⟨C₁', hC₁', huC₁', hvC₁'⟩
        have heqC : C₁' = C₁ := isGraphComponent_eq_of_mem_inter hC₁' hC₁ ⟨u, huC₁', huC₁⟩
        exact ⟨heqC ▸ hvC₁', hvZ⟩
    exact Subset.antisymm (sub_of_iff hiff) (sub_of_iff fun u hu v hv => (hiff u hu v hv).symm)

/-- "If two subgraphs $L_1, L_2$ have the same effect on $Z$ then necessarily
$V(L_1) \cap Z = V(L_2) \cap Z$." (Graph Minors XXII, Section 2, page 531). -/
theorem inter_eq_of_effectOn_eq {L₁ L₂ : Graph α β} {Z : Set α}
    (h : effectOn L₁ Z = effectOn L₂ Z) : V(L₁) ∩ Z = V(L₂) ∩ Z := by
  ext u
  simp only [mem_inter_iff]
  by_cases huZ : u ∈ Z
  · simp only [huZ, and_true]
    rw [← areConnectedIn_self_iff, ← areConnectedIn_self_iff]
    exact effectOn_eq_iff_areConnectedIn.mp h u huZ u huZ
  · simp [huZ]

/-- If $L$ is vital for $Z$ in $G$ and $Z \subseteq Z' \subseteq V(L)$, then $L$ is vital for $Z'$
in $G$. -/
theorem IsVitalFor.mono_Z {G L : Graph α β} {Z Z' : Set α}
    (h : IsVitalFor G L Z) (hZZ' : Z ⊆ Z') (hZ'L : Z' ⊆ V(L)) :
    IsVitalFor G L Z' := by
  refine ⟨h.1, hZ'L, fun L' hL'G heff' => h.2.2 L' hL'G ?_⟩
  rw [effectOn_eq_iff_areConnectedIn] at heff' ⊢
  exact fun u hu v hv => heff' u (hZZ' hu) v (hZZ' hv)

/-! ## 2. Proof of 2.2 -/

/-- Deleting an edge `e` that belongs to a simple closed walk `C` of `L` preserves reachability
between all vertices of `L`. -/
private theorem areConnectedIn_deleteEdges_of_mem_simpleClosed
    {L : Graph α β} {w₀ : α} {C : GraphWalk L w₀ w₀}
    (hC : C.IsSimpleClosed) {e : β} (he : e ∈ C.edges) {u v : α} :
    AreConnectedIn (L.deleteEdges {e}) u v ↔ AreConnectedIn L u v := by
  constructor
  · exact fun h => h.mono deleteEdges_le
  · rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
    rintro ⟨hu, hv, ⟨W⟩⟩
    have hV_eq : V(L.deleteEdges {e}) = V(L) := vertexSet_deleteEdges L {e}
    refine ⟨hV_eq.symm ▸ hu, hV_eq.symm ▸ hv, ?_⟩
    -- Any step along `e` can be replaced by the complementary simple walk along `C`.
    have hstep_e : ∀ {x y : α}, L.IsLink e x y →
        Nonempty (GraphWalk (L.deleteEdges {e}) x y) := by
      intro x y hlink
      have hind : ∀ {a b : α} (W₀ : GraphWalk L a b),
          W₀.edges.Nodup → e ∈ W₀.edges →
          Nonempty (GraphWalk (L.deleteEdges {e}) a x) ∧
            Nonempty (GraphWalk (L.deleteEdges {e}) y b) ∨
          Nonempty (GraphWalk (L.deleteEdges {e}) a y) ∧
            Nonempty (GraphWalk (L.deleteEdges {e}) x b) := by
        intro a b W₀
        induction W₀ with
        | nil _ => simp
        | @cons a₁ m₁ b₁ f hf rest ih =>
          intro hnd hef
          have hnd_cons := List.nodup_cons.mp hnd
          rcases List.mem_cons.mp hef with rfl | hef_rest
          · -- `f = e`, so `rest` does not contain `e`.
            have hrest_del : Nonempty (GraphWalk (L.deleteEdges {e}) m₁ b₁) := by
              obtain ⟨W', _, _⟩ := rest.exists_transfer (G' := L.deleteEdges {e})
                (fun f' x' y' hf' hl' => by
                  rw [deleteEdges_isLink]
                  exact ⟨hl', fun hfe => hnd_cons.1 (mem_singleton_iff.mp hfe ▸ hf')⟩)
                (fun z hz => by
                  rw [hV_eq]
                  exact rest.mem_vertexSet_of_mem_support hz)
              exact ⟨W'⟩
            rcases hlink.eq_and_eq_or_eq_and_eq hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨⟨.nil (hV_eq.symm ▸ hf.left_mem)⟩, hrest_del⟩
            · exact Or.inr ⟨⟨.nil (hV_eq.symm ▸ hf.left_mem)⟩, hrest_del⟩
          · -- `f ≠ e`, so the first step `hf` is in `L.deleteEdges {e}`.
            have hfe : f ≠ e := fun h => hnd_cons.1 (h ▸ hef_rest)
            have hf_del : (L.deleteEdges {e}).IsLink f a₁ m₁ := by
              rw [deleteEdges_isLink]
              exact ⟨hf, hfe⟩
            rcases ih hnd_cons.2 hef_rest with ⟨⟨W₁⟩, ⟨W₂⟩⟩ | ⟨⟨W₁⟩, ⟨W₂⟩⟩
            · exact Or.inl ⟨⟨.cons hf_del W₁⟩, ⟨W₂⟩⟩
            · exact Or.inr ⟨⟨.cons hf_del W₁⟩, ⟨W₂⟩⟩
      rcases hind C hC.2 he with ⟨⟨W₁⟩, ⟨W₂⟩⟩ | ⟨⟨W₁⟩, ⟨W₂⟩⟩
      · exact ⟨W₁.reverse.append W₂.reverse⟩
      · exact ⟨W₂.append W₁⟩
    have hwalk : ∀ {a b : α}, GraphWalk L a b →
        Nonempty (GraphWalk (L.deleteEdges {e}) a b) := by
      intro a b W₀
      induction W₀ with
      | nil ha => exact ⟨.nil (hV_eq.symm ▸ ha)⟩
      | @cons a₁ m₁ b₁ f hf rest ih =>
        obtain ⟨W_rest⟩ := ih
        by_cases hfe : f = e
        · subst hfe
          obtain ⟨W_e⟩ := hstep_e hf
          exact ⟨W_e.append W_rest⟩
        · have hf_del : (L.deleteEdges {e}).IsLink f a₁ m₁ := by
            rw [deleteEdges_isLink]
            exact ⟨hf, hfe⟩
          exact ⟨.cons hf_del W_rest⟩
    exact hwalk W

/-- If `L` is a forest, no edge of `L` is a loop. -/
theorem not_isLink_self_of_isGraphForest {L : Graph α β} (hF : IsGraphForest L)
    {e : β} {v : α} (hlink : L.IsLink e v v) : False := by
  let W : GraphWalk L v v := .cons hlink (.nil hlink.left_mem)
  have hclosed : W.IsSimpleClosed := ⟨by simp [W], by simp [W]⟩
  have hlen := hF v W hclosed
  simp [W] at hlen

/-- If `L` is a forest with finite edge set and `vertexValency L v ≤ 1`, then any two edges
incident with `v` in `L` are equal. -/
theorem eq_of_isLink_of_vertexValency_le_one {L : Graph α β} (hEL : E(L).Finite)
    (hF : IsGraphForest L) {v u₁ u₂ : α} {e₁ e₂ : β} (hval : vertexValency L v ≤ 1)
    (h₁ : L.IsLink e₁ v u₁) (h₂ : L.IsLink e₂ v u₂) : e₁ = e₂ ∧ u₁ = u₂ := by
  have hne₁ : u₁ ≠ v := fun h => not_isLink_self_of_isGraphForest hF (h ▸ h₁)
  have hne₂ : u₂ ≠ v := fun h => not_isLink_self_of_isGraphForest hF (h ▸ h₂)
  have he₁S : e₁ ∈ {e ∈ E(L) | ∃ w ≠ v, L.IsLink e v w} := ⟨h₁.edge_mem, u₁, hne₁, h₁⟩
  have he₂S : e₂ ∈ {e ∈ E(L) | ∃ w ≠ v, L.IsLink e v w} := ⟨h₂.edge_mem, u₂, hne₂, h₂⟩
  have hS_le : {e ∈ E(L) | ∃ w ≠ v, L.IsLink e v w}.ncard ≤ 1 := by
    unfold vertexValency at hval
    omega
  have hfin : {e ∈ E(L) | ∃ w ≠ v, L.IsLink e v w}.Finite := hEL.subset fun _ h => h.1
  have he_eq : e₁ = e₂ := (ncard_le_one_iff hfin).mp hS_le he₁S he₂S
  subst he_eq
  exact ⟨rfl, h₁.right_unique h₂⟩

/-- Deleting a vertex `v ∉ Z` of degree at most 1 in a forest `L` with finite edge set preserves
`L`-connectivity between all pairs of vertices in `Z`. -/
private theorem areConnectedIn_deleteVerts_singleton_of_valency_le_one
    {L : Graph α β} (hEL : E(L).Finite) (hF : IsGraphForest L) {Z : Set α} {v : α}
    (hvZ : v ∉ Z) (hval : vertexValency L v ≤ 1)
    {x y : α} (hx : x ∈ Z) (hy : y ∈ Z) :
    AreConnectedIn (L.deleteVerts {v}) x y ↔ AreConnectedIn L x y := by
  constructor
  · exact fun h => h.mono deleteVerts_le
  · intro hconn
    rw [areConnectedIn_iff_walk] at hconn
    rcases hconn with ⟨hxL, hyL, ⟨W₀⟩⟩
    obtain ⟨W, hW_simple, _, _⟩ := exists_isSimple_subwalk W₀
    have hxv : x ≠ v := fun h => hvZ (h ▸ hx)
    have hyv : y ≠ v := fun h => hvZ (h ▸ hy)
    -- Show `v ∉ W.support` because `W` is simple with ends `x ≠ v` and `y ≠ v`, and `v` has degree ≤ 1.
    have hv_not_mem : v ∉ W.support := by
      have hind : ∀ {a b : α} (W₁ : GraphWalk L a b),
          W₁.IsSimple → b ≠ v → (v ∈ W₁.support → a = v) := by
        intro a b W₁
        induction W₁ with
        | nil _ =>
          intro _ _ hv_mem
          simp only [GraphWalk.support_nil, List.mem_singleton] at hv_mem
          exact hv_mem.symm
        | @cons a₁ m₁ b₁ e₁ h₁ rest ih =>
          intro hsimp hbv hv_mem
          have hnd := List.nodup_cons.mp hsimp
          rcases List.mem_cons.mp hv_mem with rfl | hv_rest
          · rfl
          · have hm₁v : m₁ = v := ih hnd.2 hbv hv_rest
            subst hm₁v
            cases rest with
            | nil _ => exact (hbv rfl).elim
            | @cons _ m₂ _ e₂ h₂ rest₂ =>
              have heq := eq_of_isLink_of_vertexValency_le_one hEL hF hval h₁.symm h₂
              exact (hnd.1 (heq.2.symm ▸ List.mem_cons_of_mem _ rest₂.start_mem_support)).elim
      intro hv_mem
      exact hxv (hind W hW_simple hyv hv_mem)
    obtain ⟨W', _, _⟩ := W.exists_transfer (G' := L.deleteVerts {v})
      (fun e u w he hl => by
        rw [deleteVerts_isLink]
        have hm := walk_isLink_mem_support W he hl
        refine ⟨hl, fun hu => ?_, fun hw => ?_⟩
        · rw [mem_singleton_iff] at hu
          exact hv_not_mem (hu ▸ hm.1)
        · rw [mem_singleton_iff] at hw
          exact hv_not_mem (hw ▸ hm.2))
      (fun z hz => by
        rw [vertexSet_deleteVerts]
        refine ⟨W.mem_vertexSet_of_mem_support hz, fun hzv => ?_⟩
        rw [mem_singleton_iff] at hzv
        exact hv_not_mem (hzv ▸ hz))
    rw [areConnectedIn_iff_walk]
    rw [vertexSet_deleteVerts]
    exact ⟨⟨hxL, hxv⟩, ⟨hyL, hyv⟩, ⟨W'⟩⟩

/-- Any vital subgraph `L` of `G` is a forest. -/
theorem IsVitalFor.isGraphForest {G L : Graph α β} {Z : Set α}
    (hvit : IsVitalFor G L Z) : IsGraphForest L := by
  intro w₀ C hC
  by_contra hlen
  cases C with
  | nil _ => exact hlen rfl
  | @cons _ m _ e he rest =>
    let L' := L.deleteEdges {e}
    have hL'G : L' ≤ G := deleteEdges_le.trans hvit.1
    have heff : effectOn L' Z = effectOn L Z := by
      rw [effectOn_eq_iff_areConnectedIn]
      intro u _ v _
      exact areConnectedIn_deleteEdges_of_mem_simpleClosed hC (by simp)
    have heq : L' = L := hvit.2.2 L' hL'G heff
    have he_mem : e ∈ E(L') := by
      rw [heq]
      exact he.edge_mem
    rw [edgeSet_deleteEdges] at he_mem
    exact he_mem.2 (mem_singleton e)

/-- Any vital subgraph `L` of `G` satisfies `V(L) = V(G)`. -/
theorem IsVitalFor.vertexSet_eq {G L : Graph α β} {Z : Set α}
    (hvit : IsVitalFor G L Z) : V(L) = V(G) := by
  apply Subset.antisymm hvit.1.vertexSet_mono
  intro v hvG
  by_contra hvL
  let L' := subgraphUnion G L (Graph.noEdge ({v} : Set α) β)
  have hno_le : Graph.noEdge ({v} : Set α) β ≤ G := by
    refine ⟨singleton_subset_iff.mpr hvG, fun e x y hlink => ?_⟩
    simp at hlink
  have hL'G : L' ≤ G := subgraphUnion_le hvit.1 hno_le
  have hLL' : L ≤ L' := le_subgraphUnion_left hvit.1 hno_le
  have heff : effectOn L' Z = effectOn L Z := by
    rw [effectOn_eq_iff_areConnectedIn]
    intro x hx y hy
    constructor
    · intro hconn
      rw [areConnectedIn_iff_walk] at hconn ⊢
      rcases hconn with ⟨_, _, ⟨W⟩⟩
      have hlink_eq : ∀ e a b, L'.IsLink e a b → L.IsLink e a b := by
        intro e a b hl
        rcases (subgraphUnion_isLink hvit.1 hno_le).mp hl with hlL | hlno
        · exact hlL
        · simp at hlno
      obtain ⟨W', _, _⟩ := W.exists_transfer
        (fun e a b _ hl => hlink_eq e a b hl)
        (fun z hz => by
          cases W with
          | nil _ =>
            simp only [GraphWalk.support_nil, List.mem_singleton] at hz
            exact hz ▸ hvit.2.1 hx
          | cons h r =>
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hvit.2.1 hx
            · obtain ⟨e₀, a₀, hl₀⟩ : ∃ e₀ a₀, L'.IsLink e₀ a₀ z := by
                have hmem : ∀ {p q : α} (W₀ : GraphWalk L' p q),
                    (∃ e₀ a₀, L'.IsLink e₀ a₀ p) → ∀ z ∈ W₀.support, ∃ e₀ a₀, L'.IsLink e₀ a₀ z := by
                  intro p q W₀
                  induction W₀ with
                  | nil _ =>
                    intro hp z hz'
                    simp only [GraphWalk.support_nil, List.mem_singleton] at hz'
                    exact hz' ▸ hp
                  | cons h₁ r₁ ih =>
                    intro hp z hz'
                    rcases List.mem_cons.mp hz' with rfl | hz'
                    · exact hp
                    · exact ih ⟨_, _, h₁⟩ z hz'
                exact hmem r ⟨_, _, h⟩ z hz
              exact (hlink_eq e₀ a₀ z hl₀).right_mem)
      exact ⟨hvit.2.1 hx, hvit.2.1 hy, ⟨W'⟩⟩
    · exact fun h => h.mono hLL'
  have heq : L' = L := hvit.2.2 L' hL'G heff
  have hv_in : v ∈ V(L) := by
    rw [← heq, vertexSet_subgraphUnion]
    exact Or.inr (mem_singleton v)
  exact hvL hv_in

/-- **Graph Minors XXII, 2.2** (Section 2, page 531):
"If $L$ is a subgraph of $G$, and $L$ is vital for $Z \subseteq V(G)$, then $L$ is a forest,
$V(L) = V(G)$, and every vertex of $L$ not in $Z$ has degree at least 2 in $L$." -/
theorem theorem_2_2_proof {G L : Graph α β} {Z : Set α} (hE : E(G).Finite) (_hZ : Z ⊆ V(G))
    (hvit : IsVitalFor G L Z) :
    IsGraphForest L ∧ V(L) = V(G) ∧ ∀ v ∈ V(L) \ Z, 2 ≤ vertexValency L v := by
  have hF : IsGraphForest L := hvit.isGraphForest
  have hVL : V(L) = V(G) := hvit.vertexSet_eq
  have hEL : E(L).Finite := hE.subset hvit.1.edgeSet_mono
  refine ⟨hF, hVL, ?_⟩
  rintro v ⟨hvL, hvZ⟩
  by_contra hlt
  push Not at hlt
  have hval : vertexValency L v ≤ 1 := Nat.le_of_lt_succ hlt
  let L' := L.deleteVerts {v}
  have hL'G : L' ≤ G := deleteVerts_le.trans hvit.1
  have heff : effectOn L' Z = effectOn L Z := by
    rw [effectOn_eq_iff_areConnectedIn]
    intro x hx y hy
    exact areConnectedIn_deleteVerts_singleton_of_valency_le_one hEL hF hvZ hval hx hy
  have heq : L' = L := hvit.2.2 L' hL'G heff
  have hv_in : v ∈ V(L') := by
    rw [heq]
    exact hvL
  rw [vertexSet_deleteVerts] at hv_in
  exact hv_in.2 (mem_singleton v)

/-! ## 3. Proof of 2.4 -/

/-- In a forest `L`, if `L.IsLink e u₀ v₀`, there is no walk between `u₀` and `v₀` in
`L.deleteEdges {e}`. -/
private theorem not_areConnectedIn_deleteEdges_of_isGraphForest
    {L : Graph α β} (hF : IsGraphForest L) {e : β} {u₀ v₀ : α}
    (hlink : L.IsLink e u₀ v₀) :
    ¬ AreConnectedIn (L.deleteEdges {e}) u₀ v₀ := by
  intro hconn
  rw [areConnectedIn_iff_walk] at hconn
  rcases hconn with ⟨_, _, ⟨W₀⟩⟩
  obtain ⟨W₁, hW₁_simple, _, _⟩ := exists_isSimple_subwalk W₀
  obtain ⟨W, hs, he⟩ := exists_walk_up_of_le (deleteEdges_le (G := L) (F := {e})) W₁
  have hW_simple : W.IsSimple := by
    unfold GraphWalk.IsSimple; rw [hs]; exact hW₁_simple
  have he_not_mem : e ∉ W.edges := by
    rw [he]
    intro he_in
    have heE := walk_edges_subset_edgeSet W₁ e he_in
    rw [edgeSet_deleteEdges] at heE
    exact heE.2 (mem_singleton e)
  have hclosed : (GraphWalk.cons hlink.symm W).IsSimpleClosed := by
    refine ⟨hW_simple, ?_⟩
    simp only [GraphWalk.edges_cons, List.nodup_cons]
    exact ⟨he_not_mem, hW_simple.edges_nodup⟩
  have hlen := hF v₀ (GraphWalk.cons hlink.symm W) hclosed
  simp at hlen

/-- In any graph `M`, connectivity in `M` vs `M.deleteEdges {e}` when `M.IsLink e u₀ v₀`: two
vertices `x, y ∈ V(M)` are `M`-connected if and only if they are `(M.deleteEdges {e})`-connected or
connected to `{u₀, v₀}` on opposite sides of `e`. -/
private theorem areConnectedIn_iff_deleteEdges_or
    {M : Graph α β} {e : β} {u₀ v₀ : α} (hlink : M.IsLink e u₀ v₀) {x y : α} :
    AreConnectedIn M x y ↔
      AreConnectedIn (M.deleteEdges {e}) x y ∨
      (AreConnectedIn (M.deleteEdges {e}) x u₀ ∧ AreConnectedIn (M.deleteEdges {e}) v₀ y) ∨
      (AreConnectedIn (M.deleteEdges {e}) x v₀ ∧ AreConnectedIn (M.deleteEdges {e}) u₀ y) := by
  have hV_eq : V(M.deleteEdges {e}) = V(M) := vertexSet_deleteEdges M {e}
  have hu₀_del : AreConnectedIn (M.deleteEdges {e}) u₀ u₀ :=
    areConnectedIn_self_iff.mpr (hV_eq.symm ▸ hlink.left_mem)
  have hv₀_del : AreConnectedIn (M.deleteEdges {e}) v₀ v₀ :=
    areConnectedIn_self_iff.mpr (hV_eq.symm ▸ hlink.right_mem)
  have he_conn : AreConnectedIn M u₀ v₀ := by
    rw [areConnectedIn_iff_walk]
    exact ⟨hlink.left_mem, hlink.right_mem, ⟨.cons hlink (.nil hlink.right_mem)⟩⟩
  constructor
  · intro hconn
    rw [areConnectedIn_iff_walk] at hconn
    rcases hconn with ⟨_, _, ⟨W⟩⟩
    have hind : ∀ {a b : α}, GraphWalk M a b →
        AreConnectedIn (M.deleteEdges {e}) a b ∨
        (AreConnectedIn (M.deleteEdges {e}) a u₀ ∧ AreConnectedIn (M.deleteEdges {e}) v₀ b) ∨
        (AreConnectedIn (M.deleteEdges {e}) a v₀ ∧ AreConnectedIn (M.deleteEdges {e}) u₀ b) := by
      intro a b W₀
      induction W₀ with
      | @nil a ha =>
        exact Or.inl (areConnectedIn_self_iff.mpr (hV_eq.symm ▸ ha))
      | @cons a m b f hf rest ih =>
        by_cases hfe : f = e
        · subst hfe
          have ha_u_or_v : (a = u₀ ∧ m = v₀) ∨ (a = v₀ ∧ m = u₀) := hf.eq_and_eq_or_eq_and_eq hlink
          rcases ha_u_or_v with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rcases ih with h_mb | ⟨_, h_vy⟩ | ⟨_, h_uy⟩
            · exact Or.inr (Or.inl ⟨hu₀_del, h_mb⟩)
            · exact Or.inr (Or.inl ⟨hu₀_del, h_vy⟩)
            · exact Or.inl h_uy
          · rcases ih with h_mb | ⟨_, h_vy⟩ | ⟨_, h_uy⟩
            · exact Or.inr (Or.inr ⟨hv₀_del, h_mb⟩)
            · exact Or.inl h_vy
            · exact Or.inr (Or.inr ⟨hv₀_del, h_uy⟩)
        · have hf_del : AreConnectedIn (M.deleteEdges {e}) a m := by
            rw [areConnectedIn_iff_walk]
            have hlink_del : (M.deleteEdges {e}).IsLink f a m := by
              rw [deleteEdges_isLink]
              exact ⟨hf, hfe⟩
            exact ⟨hlink_del.left_mem, hlink_del.right_mem, ⟨.cons hlink_del (.nil hlink_del.right_mem)⟩⟩
          rcases ih with h_mb | ⟨h_mu, h_vy⟩ | ⟨h_mv, h_uy⟩
          · exact Or.inl (hf_del.trans h_mb)
          · exact Or.inr (Or.inl ⟨hf_del.trans h_mu, h_vy⟩)
          · exact Or.inr (Or.inr ⟨hf_del.trans h_mv, h_uy⟩)
    exact hind W
  · rintro (h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact h.mono deleteEdges_le
    · exact (h₁.mono deleteEdges_le).trans (he_conn.trans (h₂.mono deleteEdges_le))
    · exact (h₁.mono deleteEdges_le).trans (he_conn.symm.trans (h₂.mono deleteEdges_le))

/-- **Graph Minors XXII, 2.4** (Section 2, page 532):
"Let $L$ be a subgraph of $G$, vital for $Z \subseteq V(G)$, and let $e \in E(L)$ with both ends
in $Z$. Then $L \setminus \{e\}$ is vital for $Z$ in $G$." -/
theorem theorem_2_4_proof {G L : Graph α β} {Z : Set α} {e : β} {u₀ v₀ : α}
    (hZ : Z ⊆ V(G)) (hvit : IsVitalFor G L Z)
    (hlink : L.IsLink e u₀ v₀) (hu₀ : u₀ ∈ Z) (hv₀ : v₀ ∈ Z) :
    IsVitalFor G (L.deleteEdges {e}) Z := by
  have hF : IsGraphForest L := hvit.isGraphForest
  refine ⟨deleteEdges_le.trans hvit.1, ?_, ?_⟩
  · rw [vertexSet_deleteEdges]
    exact hvit.2.1
  · intro L' hL'G heff
    have hiff_del := effectOn_eq_iff_areConnectedIn.mp heff
    -- First, `u₀` and `v₀` are not connected in `L.deleteEdges {e}`, hence not in `L'`.
    have hnot_conn_del : ¬ AreConnectedIn (L.deleteEdges {e}) u₀ v₀ :=
      not_areConnectedIn_deleteEdges_of_isGraphForest hF hlink
    have hnot_conn_L' : ¬ AreConnectedIn L' u₀ v₀ :=
      fun h => hnot_conn_del ((hiff_del u₀ hu₀ v₀ hv₀).mp h)
    have hlink_G : G.IsLink e u₀ v₀ := hlink.mono hvit.1
    have he_not_L' : e ∉ E(L') := by
      intro heL'
      have hlink_L' : L'.IsLink e u₀ v₀ := (hL'G.isLink_iff heL').mpr hlink_G
      apply hnot_conn_L'
      rw [areConnectedIn_iff_walk]
      exact ⟨hlink_L'.left_mem, hlink_L'.right_mem, ⟨.cons hlink_L' (.nil hlink_L'.right_mem)⟩⟩
    -- Let `E_e` be the subgraph of `G` with vertex set `{u₀, v₀}` and edge `{e}`.
    let E_e : Graph α β := (G.induce {u₀, v₀}).restrict {e}
    have hEe_G : E_e ≤ G :=
      restrict_le.trans (G.induce_le (pair_subset (hZ hu₀) (hZ hv₀)))
    let L'' := subgraphUnion G L' E_e
    have hL''G : L'' ≤ G := subgraphUnion_le hL'G hEe_G
    have hu₀_L' : u₀ ∈ V(L') := by
      have : u₀ ∈ V(L') ∩ Z := by
        rw [inter_eq_of_effectOn_eq heff, vertexSet_deleteEdges]
        exact ⟨hvit.2.1 hu₀, hu₀⟩
      exact this.1
    have hv₀_L' : v₀ ∈ V(L') := by
      have : v₀ ∈ V(L') ∩ Z := by
        rw [inter_eq_of_effectOn_eq heff, vertexSet_deleteEdges]
        exact ⟨hvit.2.1 hv₀, hv₀⟩
      exact this.1
    have hVL'' : V(L'') = V(L') := by
      rw [vertexSet_subgraphUnion]
      exact union_eq_left.mpr (pair_subset hu₀_L' hv₀_L')
    have hlink_Ee : E_e.IsLink e u₀ v₀ := by
      simp [E_e, restrict_isLink, induce_isLink, hlink_G]
    have hlink_L'' : L''.IsLink e u₀ v₀ := by
      rw [subgraphUnion_isLink hL'G hEe_G]
      exact Or.inr hlink_Ee
    have hdel_L'' : L''.deleteEdges {e} = L' := by
      refine (Compatible.of_le_le (deleteEdges_le.trans hL''G) hL'G).ext ?_ ?_
      · rw [vertexSet_deleteEdges, hVL'']
      · rw [edgeSet_deleteEdges, edgeSet_subgraphUnion hL'G hEe_G]
        ext f
        simp only [mem_sdiff, mem_union, mem_singleton_iff]
        constructor
        · rintro ⟨hfL' | hfEe, hfe⟩
          · exact hfL'
          · exfalso
            have : f ∈ {e} := hfEe.2
            exact hfe (mem_singleton_iff.mp this)
        · intro hfL'
          exact ⟨Or.inl hfL', fun hfe => he_not_L' (hfe ▸ hfL')⟩
    have heff_L'' : effectOn L'' Z = effectOn L Z := by
      rw [effectOn_eq_iff_areConnectedIn]
      intro x hx y hy
      rw [areConnectedIn_iff_deleteEdges_or hlink_L'', areConnectedIn_iff_deleteEdges_or hlink,
        hdel_L'']
      simp only [hiff_del x hx y hy, hiff_del x hx u₀ hu₀, hiff_del v₀ hv₀ y hy,
        hiff_del x hx v₀ hv₀, hiff_del u₀ hu₀ y hy]
    have heq_L'' : L'' = L := hvit.2.2 L'' hL''G heff_L''
    rw [← hdel_L'', heq_L'']

end GraphMinor.GM22
