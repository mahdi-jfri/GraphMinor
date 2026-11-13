module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section2f
public import GraphMinor.Surface.Defs

/-!
# Graph Minors III, Section 2g: Forest Minor Embedding into $Y_\lambda$ (for (2.3))

This file proves the forest-to-$Y_\lambda$ step of `(2.3)` (page 55) of N. Robertson and
P. D. Seymour, *Graph Minors. III. Planar Tree-Width*, J. Combin. Theory Ser. B **36** (1984),
49–64:
- `isMinorModel_of_loopless_link`: criterion constructing `IsMinorModel H G ηv ηe` for loopless
  graphs `H` from disjoint nonempty induced-connected vertex branch sets and representative link
  edges;
- `not_reflTransGen_deleteEdge_of_no_circuit`: deleting an edge `e₀` of an acyclic graph `F`
  separates its two endpoints;
- `subVal`, `heapIdx`, `binNodeOfWord`: binary-word coordinates on branch `0` of `TreeYInternal`
  compatible with `treeYInternalParent` and `treeYLeafParent`;
- `exists_treeY_minor_of_forest`: every finite simple forest is isomorphic to a minor of
  `treeY lam` (`N(0, lam)`) for some `lam ≥ 1`.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Classical
open Graph
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11

universe u v u₁ v₁ u₂ v₂

/-! ## 1. Minor-Model Criterion for Loopless Graphs -/

/-- Construct `IsMinorModel H G ηv ηe` for a loopless graph `H` from pairwise-disjoint nonempty
branch sets, injective edge representatives realizing every link of `H`, and connectivity of each
induced branch subgraph after deleting `ηe '' E(H)`. -/
theorem isMinorModel_of_loopless_link {α₁ : Type u₁} {β₁ : Type v₁}
    {α₂ : Type u₂} {β₂ : Type v₂}
    {H : Graph α₁ β₁} {G : Graph α₂ β₂}
    {ηv : α₁ → Set α₂} {ηe : β₁ → β₂}
    (hNoLoop : ∀ e ∈ E(H), ∀ u, ¬ H.IsLoopAt e u)
    (hv_ne : ∀ v ∈ V(H), (ηv v).Nonempty)
    (hv_sub : ∀ v ∈ V(H), ηv v ⊆ V(G))
    (hv_disj : ∀ v₁ ∈ V(H), ∀ v₂ ∈ V(H), v₁ ≠ v₂ → Disjoint (ηv v₁) (ηv v₂))
    (he_inj : Set.InjOn ηe E(H))
    (he_link : ∀ ⦃e u v⦄, H.IsLink e u v → ∃ x ∈ ηv u, ∃ y ∈ ηv v, G.IsLink (ηe e) x y)
    (hv_conn : ∀ u ∈ V(H), ∀ x ∈ ηv u, ∀ y ∈ ηv u,
      Relation.ReflTransGen ((G.deleteEdges (ηe '' E(H))).induce (ηv u)).Adj x y) :
    IsMinorModel H G ηv ηe where
  vertex_nonempty := hv_ne
  vertex_subset := hv_sub
  edge_mem e he := by
    obtain ⟨u, v, hl⟩ := H.exists_isLink_of_mem_edgeSet he
    obtain ⟨x, _, y, _, hG⟩ := he_link hl
    exact hG.edge_mem
  vertex_disjoint := hv_disj
  edge_injOn := he_inj
  inc_iff u hu e he := by
    constructor
    · rintro ⟨v, hl⟩
      obtain ⟨x, hxu, y, _, hG⟩ := he_link hl
      exact ⟨x, hxu, y, hG⟩
    · rintro ⟨z, hzu, w, hGw⟩
      obtain ⟨a, b, hl⟩ := H.exists_isLink_of_mem_edgeSet he
      obtain ⟨x, hxa, y, hyb, hG⟩ := he_link hl
      rcases hGw.left_eq_or_eq hG with rfl | rfl
      · have hua : u = a := by
          by_contra hne
          exact Set.disjoint_left.mp (hv_disj u hu a hl.left_mem hne) hzu hxa
        subst hua
        exact ⟨b, hl⟩
      · have hub : u = b := by
          by_contra hne
          exact Set.disjoint_left.mp (hv_disj u hu b hl.right_mem hne) hzu hyb
        subst hub
        exact ⟨a, hl.symm⟩
  isLoopAt_iff u hu e he := by
    constructor
    · intro hloop
      exact (hNoLoop e he u hloop).elim
    · intro hall
      exfalso
      obtain ⟨a, b, hl⟩ := H.exists_isLink_of_mem_edgeSet he
      have hab : a ≠ b := fun h => hNoLoop e he a (h ▸ hl)
      obtain ⟨x, hxa, y, hyb, hG⟩ := he_link hl
      have hxu : x ∈ ηv u := hall x ⟨y, hG⟩
      have hyu : y ∈ ηv u := hall y ⟨x, hG.symm⟩
      have hua : u = a := by
        by_contra hne
        exact Set.disjoint_left.mp (hv_disj u hu a hl.left_mem hne) hxu hxa
      have hub : u = b := by
        by_contra hne
        exact Set.disjoint_left.mp (hv_disj u hu b hl.right_mem hne) hyu hyb
      exact hab (hua.symm.trans hub)
  connected u hu := by
    refine ⟨(G.deleteEdges (ηe '' E(H))).induce (ηv u), ?_, rfl, ?_⟩
    · refine Graph.induce_le ?_
      change ηv u ⊆ V(G)
      exact hv_sub u hu
    · obtain ⟨x₀, hx₀⟩ := hv_ne u hu
      exact ⟨⟨x₀, hx₀⟩, hv_conn u hu⟩

/-! ## 2. Acyclic Graph Splitting Lemmas -/

private theorem mem_support_endpoints_of_mem_edges {α : Type u} {β : Type v} {G : Graph α β}
    {u v x y : α} {e : β} (W : GraphWalk G u v) (he : e ∈ W.edges) (hl : G.IsLink e x y) :
    x ∈ W.support ∧ y ∈ W.support := by
  induction W with
  | nil _ => cases he
  | @cons a b c f hlf rest ih =>
    rcases List.mem_cons.mp he with rfl | hrest
    · rcases hl.left_eq_or_eq hlf with rfl | rfl
      · rw [hl.right_unique hlf]
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ rest.start_mem_support⟩
      · rw [hl.right_unique hlf.symm]
        exact ⟨List.mem_cons_of_mem _ rest.start_mem_support, List.mem_cons_self⟩
    · obtain ⟨hx, hy⟩ := ih hrest
      exact ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy⟩

/-- Any simple walk `W` (`W.IsSimple`) has duplicate-free edges (`W.edges.Nodup`). -/
theorem edges_nodup_of_isSimple' {α : Type u} {β : Type v} {G : Graph α β} {u v : α}
    {W : GraphWalk G u v} (hW : W.IsSimple) :
    W.edges.Nodup := by
  induction W with
  | nil _ => exact List.nodup_nil
  | @cons a b c e hl rest ih =>
    have hnd := List.nodup_cons.mp hW
    refine List.nodup_cons.mpr ⟨?_, ih hnd.2⟩
    intro he_mem
    exact hnd.1 (mem_support_endpoints_of_mem_edges rest he_mem hl).1

/-- Any `Relation.ReflTransGen G.Adj x y` for `x ∈ V(G)` yields a simple `GraphWalk G x y`. -/
theorem exists_isSimple_walk_of_reflTransGen {α : Type u} {β : Type v} {G : Graph α β}
    {x y : α} (hx : x ∈ V(G)) (hxy : Relation.ReflTransGen G.Adj x y) :
    ∃ W : GraphWalk G x y, W.IsSimple := by
  have hex : ∃ n : ℕ, ∃ W : GraphWalk G x y, W.length = n := by
    induction hxy with
    | refl => exact ⟨0, .nil hx, rfl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨n, W, rfl⟩ := ih
      obtain ⟨e, hl⟩ := hbc
      exact ⟨W.length + 1, W.append (.cons hl (.nil hl.right_mem)), by rw [GraphWalk.length_append]; rfl⟩
  let n₀ := Nat.find hex
  obtain ⟨W, hlen⟩ : ∃ W : GraphWalk G x y, W.length = n₀ := Nat.find_spec hex
  refine ⟨W, ?_⟩
  by_contra hnot
  have hshort : ∀ {a b : α} (Q : GraphWalk G a b), ¬ Q.support.Nodup →
      ∃ Q' : GraphWalk G a b, Q'.length < Q.length := by
    intro a b Q
    induction Q with
    | nil _ => exact fun h => (h (List.nodup_singleton _)).elim
    | @cons p q r e hl rest ih =>
      intro h
      by_cases hrest : rest.support.Nodup
      · have hp_mem : p ∈ rest.support := by
          by_contra hp
          exact h (List.nodup_cons.mpr ⟨hp, hrest⟩)
        obtain ⟨Q₁, Q₂, hsplit⟩ := rest.exists_append_of_mem hp_mem
        have hlen_eq : rest.length = Q₁.length + Q₂.length := by
          rw [← GraphWalk.length_append, ← hsplit]
        exact ⟨Q₂, by simp only [GraphWalk.length_cons]; omega⟩
      · obtain ⟨Q', hlt⟩ := ih hrest
        exact ⟨.cons hl Q', Nat.add_lt_add_right hlt 1⟩
  obtain ⟨W', hlt⟩ := hshort W hnot
  dsimp only [n₀] at hlen
  exact Nat.find_min hex (hlen ▸ hlt) ⟨W', rfl⟩

/-- Lift a `GraphWalk G u v` to a walk on `(G.induce S).restrict E₀` when its support lies in `S`
and its edges lie in `E₀`. -/
def liftWalkRestrictInduce {α : Type u} {β : Type v} {G : Graph α β}
    {S : Set α} {E₀ : Set β} (_hSG : S ⊆ V(G))
    {u v : α} (W : GraphWalk G u v)
    (hV : ∀ x ∈ W.support, x ∈ S) (hE : ∀ e ∈ W.edges, e ∈ E₀) :
    GraphWalk ((G.induce S).restrict E₀) u v :=
  match W with
  | .nil _ => .nil (hV u (by simp))
  | .cons (v := b) (e := e) hl rest =>
    have hl' : ((G.induce S).restrict E₀).IsLink e u b :=
      ⟨hE e (by simp), hl, hV u (by simp), hV b (by simp [rest.start_mem_support])⟩
    .cons hl' (liftWalkRestrictInduce _hSG rest
      (fun x hx => hV x (List.mem_cons_of_mem _ hx))
      (fun f hf => hE f (List.mem_cons_of_mem _ hf)))

@[simp]
theorem liftWalkRestrictInduce_support {α : Type u} {β : Type v} {G : Graph α β}
    {S : Set α} {E₀ : Set β} (hSG : S ⊆ V(G)) {u v : α} (W : GraphWalk G u v)
    (hV : ∀ x ∈ W.support, x ∈ S) (hE : ∀ e ∈ W.edges, e ∈ E₀) :
    (liftWalkRestrictInduce hSG W hV hE).support = W.support := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => exact congrArg (_ :: ·) (ih _ _)

@[simp]
theorem liftWalkRestrictInduce_edges {α : Type u} {β : Type v} {G : Graph α β}
    {S : Set α} {E₀ : Set β} (hSG : S ⊆ V(G)) {u v : α} (W : GraphWalk G u v)
    (hV : ∀ x ∈ W.support, x ∈ S) (hE : ∀ e ∈ W.edges, e ∈ E₀) :
    (liftWalkRestrictInduce hSG W hV hE).edges = W.edges := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => exact congrArg (_ :: ·) (ih _ _)

@[simp]
theorem liftWalkRestrictInduce_length {α : Type u} {β : Type v} {G : Graph α β}
    {S : Set α} {E₀ : Set β} (hSG : S ⊆ V(G)) {u v : α} (W : GraphWalk G u v)
    (hV : ∀ x ∈ W.support, x ∈ S) (hE : ∀ e ∈ W.edges, e ∈ E₀) :
    (liftWalkRestrictInduce hSG W hV hE).length = W.length := by
  unfold GraphWalk.length
  rw [liftWalkRestrictInduce_edges]

/-- In a simple graph `F` with no circuit (`∀ C' ≤ F, ¬ IsGraphCircuit F C'`), deleting any edge
`e₀` linking `r` and `s` disconnects `r` from `s`. -/
theorem not_reflTransGen_deleteEdge_of_no_circuit {α : Type u} {β : Type v}
    {F : Graph α β} (_hSimple : F.Simple)
    (hNoCirc : ∀ C' ≤ F, ¬ GM09.IsGraphCircuit F C')
    {e₀ : β} {r s : α} (hl₀ : F.IsLink e₀ r s) :
    ¬ Relation.ReflTransGen (F.deleteEdges {e₀}).Adj r s := by
  intro hconn
  have hsymm : Relation.ReflTransGen (F.deleteEdges {e₀}).Adj s r := by
    clear hNoCirc hl₀
    induction hconn with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hbc.symm) ih
  have hs_mem : s ∈ V(F.deleteEdges {e₀}) := hl₀.right_mem
  obtain ⟨W, hW_simp⟩ := exists_isSimple_walk_of_reflTransGen hs_mem hsymm
  have he₀_not_W : e₀ ∉ W.edges := by
    intro he_mem
    have hle : ∀ {a b : α} (Q : GraphWalk (F.deleteEdges {e₀}) a b),
        e₀ ∈ Q.edges → False := by
      intro a b Q hmem
      induction Q with
      | nil _ => cases hmem
      | @cons p q t f hlf rest ih =>
        rcases List.mem_cons.mp hmem with rfl | hrest
        · rw [Graph.deleteEdges_isLink] at hlf
          exact hlf.2 (mem_singleton e₀)
        · exact ih hrest
    exact hle W he_mem
  have hWF_le : F.deleteEdges {e₀} ≤ F := Graph.deleteEdges_le
  let WF : GraphWalk F s r := W.mono hWF_le
  have hWF_sup : WF.support = W.support := by
    dsimp only [WF]
    exact GraphWalk.support_mono hWF_le W
  have hWF_edg : WF.edges = W.edges := by
    dsimp only [WF]
    exact GraphWalk.edges_mono hWF_le W
  let Wc : GraphWalk F r r := .cons hl₀ WF
  have hWc_sc : Wc.IsSimpleClosed := by
    refine ⟨?_, ?_⟩
    · dsimp only [Wc]
      simp only [GraphWalk.support_cons, List.tail_cons, hWF_sup]
      exact hW_simp
    · dsimp only [Wc]
      simp only [GraphWalk.edges_cons, hWF_edg]
      exact List.nodup_cons.mpr ⟨he₀_not_W, edges_nodup_of_isSimple' hW_simp⟩
  let S : Set α := {x | x ∈ Wc.support}
  let E₀ : Set β := {e | e ∈ Wc.edges}
  have hSF : S ⊆ V(F) := by
    intro x hx
    have hmem : ∀ {a b : α} (Q : GraphWalk F a b), ∀ z ∈ Q.support, z ∈ V(F) := by
      intro a b Q z hz
      induction Q with
      | nil ha =>
        rcases List.mem_singleton.mp hz with rfl
        exact ha
      | cons hl rest ih =>
        rcases List.mem_cons.mp hz with rfl | hrest
        · exact hl.left_mem
        · exact ih hrest
    exact hmem Wc x hx
  let C' : Graph α β := (F.induce S).restrict E₀
  have hC'_le : C' ≤ F := Graph.restrict_le.trans (Graph.induce_le hSF)
  let WC' : GraphWalk C' r r :=
    liftWalkRestrictInduce hSF Wc (fun _ hx => hx) (fun _ he => he)
  have hCirc : GM09.IsGraphCircuit F C' := by
    refine ⟨hC'_le, r, WC', ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · dsimp only [WC']
        rw [liftWalkRestrictInduce_support]
        exact hWc_sc.1
      · dsimp only [WC']
        rw [liftWalkRestrictInduce_edges]
        exact hWc_sc.2
    · dsimp only [WC']
      rw [liftWalkRestrictInduce_length]
      dsimp only [Wc]
      simp
    · ext x
      dsimp only [C', WC', S]
      rw [liftWalkRestrictInduce_support]
      rfl
    · ext e
      dsimp only [WC']
      rw [liftWalkRestrictInduce_edges]
      change e ∈ E(F.induce S) ∩ E₀ ↔ e ∈ Wc.edges
      rw [Graph.edgeSet_induce, mem_inter_iff]
      refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
      have he_F : e ∈ E(F) := by
        have hmem_F : ∀ {a b : α} (Q : GraphWalk F a b), ∀ f ∈ Q.edges, f ∈ E(F) := by
          intro a b Q f hf
          induction Q with
          | nil _ => cases hf
          | cons hlg _ ih =>
            rcases List.mem_cons.mp hf with rfl | hrest
            · exact hlg.edge_mem
            · exact ih hrest
        exact hmem_F Wc e he
      obtain ⟨p, q, hlpq⟩ := F.exists_isLink_of_mem_edgeSet he_F
      obtain ⟨hp, hq⟩ := mem_support_endpoints_of_mem_edges Wc he hlpq
      exact ⟨p, q, hlpq, hp, hq⟩
  exact hNoCirc C' hC'_le hCirc

/-- `IsGraphCircuit` is invariant under passing between subgraphs `C' ≤ H ≤ G`. -/
theorem isGraphCircuit_iff_of_le {α : Type u} {β : Type v} {G H C' : Graph α β}
    (hHG : H ≤ G) (hCH : C' ≤ H) :
    GM09.IsGraphCircuit H C' ↔ GM09.IsGraphCircuit G C' := by
  unfold GM09.IsGraphCircuit
  exact ⟨fun ⟨_, rest⟩ => ⟨hCH.trans hHG, rest⟩, fun ⟨_, rest⟩ => ⟨hCH, rest⟩⟩

/-! ## 3. Binary-Word Coordinates on Branch `0` of `TreeYInternal` -/

/-- Binary offset of a bit-word `w : List Bool` in `[0, 2 ^ w.length)`:
`false` selects the lower half `[0, 2 ^ k)` and `true` selects `[2 ^ k, 2 * 2 ^ k)`. -/
def subVal : List Bool → ℕ
  | [] => 0
  | false :: w => subVal w
  | true :: w => 2 ^ w.length + subVal w

theorem subVal_lt_pow (w : List Bool) : subVal w < 2 ^ w.length := by
  induction w with
  | nil => simp [subVal]
  | cons b w ih =>
    cases b <;> simp only [subVal, List.length_cons, pow_succ'] <;> omega

theorem subVal_snoc (w : List Bool) (b : Bool) :
    subVal (w ++ [b]) = 2 * subVal w + (if b then 1 else 0) := by
  induction w with
  | nil => cases b <;> simp [subVal]
  | cons a w ih =>
    cases a <;>
      (simp only [List.cons_append, subVal, List.length_append, List.length_singleton, ih, pow_succ']
       try omega)

theorem subVal_inj_of_length_eq {w₁ w₂ : List Bool} (hlen : w₁.length = w₂.length)
    (heq : subVal w₁ = subVal w₂) : w₁ = w₂ := by
  induction w₁ generalizing w₂ with
  | nil =>
    cases w₂ with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons b₁ t₁ ih =>
    cases w₂ with
    | nil => simp at hlen
    | cons b₂ t₂ =>
      simp only [List.length_cons] at hlen
      have hlen' : t₁.length = t₂.length := by omega
      have hlt₁ := subVal_lt_pow t₁
      rw [hlen'] at hlt₁
      have hlt₂ := subVal_lt_pow t₂
      cases b₁ <;> cases b₂ <;> simp only [subVal, hlen'] at heq
      · exact congrArg (List.cons false) (ih hlen' heq)
      · omega
      · omega
      · exact congrArg (List.cons true) (ih hlen' (by omega))

/-- 1-based binary heap index `2 ^ w.length + subVal w` of a bit-word `w`. -/
def heapIdx (w : List Bool) : ℕ :=
  2 ^ w.length + subVal w

theorem heapIdx_bounds (w : List Bool) :
    1 ≤ heapIdx w ∧ 2 ^ w.length ≤ heapIdx w ∧ heapIdx w < 2 ^ (w.length + 1) := by
  have hlt := subVal_lt_pow w
  have hpos : 1 ≤ 2 ^ w.length := Nat.one_le_pow _ _ (by omega)
  unfold heapIdx
  rw [pow_succ']
  omega

theorem heapIdx_lt_pow {w : List Bool} {h : ℕ} (hw : w.length < h) :
    heapIdx w - 1 < 2 ^ h - 1 := by
  obtain ⟨_, _, hlt⟩ := heapIdx_bounds w
  have hle : 2 ^ (w.length + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hw
  omega

theorem heapIdx_snoc (w : List Bool) (b : Bool) :
    heapIdx (w ++ [b]) = 2 * heapIdx w + (if b then 1 else 0) := by
  unfold heapIdx
  rw [List.length_append, List.length_singleton, pow_succ', subVal_snoc]
  omega

theorem heapIdx_inj : Function.Injective heapIdx := by
  intro w₁ w₂ heq
  have hb₁ := heapIdx_bounds w₁
  have hb₂ := heapIdx_bounds w₂
  have hlen : w₁.length = w₂.length := by
    rcases lt_trichotomy w₁.length w₂.length with hlt | heql | hgt
    · have hpow : 2 ^ (w₁.length + 1) ≤ 2 ^ w₂.length := Nat.pow_le_pow_right (by omega) hlt
      omega
    · exact heql
    · have hpow : 2 ^ (w₂.length + 1) ≤ 2 ^ w₁.length := Nat.pow_le_pow_right (by omega) hgt
      omega
  unfold heapIdx at heq
  rw [hlen] at heq
  exact subVal_inj_of_length_eq hlen (Nat.add_left_cancel heq)

/-- Embed a bit-word `w` of length `< h` as an internal node in branch `0` of
`TreeYInternal (h + 1)`. -/
def binNodeOfWord (h : ℕ) (w : List Bool) (hw : w.length < h) : TreeYInternal (h + 1) :=
  some (⟨0, by omega⟩, ⟨heapIdx w - 1, by
    have : h + 1 - 1 = h := by omega
    rw [this]
    exact heapIdx_lt_pow hw⟩)

theorem binNodeOfWord_inj {h : ℕ} {w₁ w₂ : List Bool} (hw₁ : w₁.length < h)
    (hw₂ : w₂.length < h) (heq : binNodeOfWord h w₁ hw₁ = binNodeOfWord h w₂ hw₂) :
    w₁ = w₂ := by
  unfold binNodeOfWord at heq
  injection heq with hp
  have hm := congrArg (fun p => p.2.1) hp
  dsimp only at hm
  have h1 := (heapIdx_bounds w₁).1
  have h2 := (heapIdx_bounds w₂).1
  exact heapIdx_inj (by omega)

theorem binNodeOfWord_ne_none (h : ℕ) (w : List Bool) (hw : w.length < h) :
    binNodeOfWord h w hw ≠ none := by
  simp [binNodeOfWord]

theorem treeYInternalParent_binNodeOfWord_snoc {h : ℕ} (w : List Bool) (b : Bool)
    (hwb : (w ++ [b]).length < h) :
    treeYInternalParent (binNodeOfWord h (w ++ [b]) hwb) =
      binNodeOfWord h w (by rw [List.length_append, List.length_singleton] at hwb; omega) := by
  have hw_lt : w.length < h := by
    rw [List.length_append, List.length_singleton] at hwb; omega
  have h1 := (heapIdx_bounds w).1
  have hsnoc := heapIdx_snoc w b
  have hne0 : heapIdx (w ++ [b]) - 1 ≠ 0 := by
    cases b <;> (simp at hsnoc; omega)
  unfold binNodeOfWord treeYInternalParent
  simp only [hne0, ↓reduceDIte]
  congr 1
  ext
  · rfl
  · dsimp only
    cases b <;> (simp at hsnoc; omega)

theorem treeYLeafParent_subVal_snoc {h : ℕ} (w : List Bool) (b : Bool)
    (hwb : (w ++ [b]).length = h) :
    treeYLeafParent (h + 1) ⟨subVal (w ++ [b]), by
      have hlt := subVal_lt_pow (w ++ [b])
      rw [hwb] at hlt
      have : h + 1 - 1 = h := by omega
      rw [this]; omega⟩ =
      binNodeOfWord h w (by rw [← hwb, List.length_append, List.length_singleton]; omega) := by
  have hh_pos : 1 ≤ h := by
    rw [← hwb, List.length_append, List.length_singleton]; omega
  have hnot_le : ¬ h + 1 ≤ 1 := by omega
  have hw_len : w.length = h - 1 := by
    rw [← hwb, List.length_append, List.length_singleton]; omega
  have hlt_pow : subVal (w ++ [b]) < 2 ^ h := by
    rw [← hwb]; exact subVal_lt_pow (w ++ [b])
  unfold treeYLeafParent binNodeOfWord
  simp only [hnot_le, ↓reduceDIte]
  congr 1
  ext
  · dsimp only
    have hsub1 : h + 1 - 1 = h := by omega
    rw [hsub1, Nat.div_eq_of_lt hlt_pow]
  · dsimp only
    have hsub1 : h + 1 - 1 = h := by omega
    have hsub2 : h + 1 - 2 = h - 1 := by omega
    rw [hsub1, hsub2, Nat.mod_eq_of_lt hlt_pow, subVal_snoc, ← hw_len]
    unfold heapIdx
    cases b <;> (simp; try omega)

/-- For any `h ≥ 1`, `w : List Bool`, and `b : Bool` with `(w ++ [b]).length < h`, the internal edge
`Sum.inl (Sum.inl (binNodeOfWord h (w ++ [b]) hwb))` links `Sum.inl (binNodeOfWord h (w ++ [b]) _)`
and `Sum.inl (binNodeOfWord h w _)` in `graphN d (h + 1)`. -/
theorem graphN_isLink_binNode_snoc (d : ℕ) {h : ℕ} (w : List Bool) (b : Bool)
    (hwb : (w ++ [b]).length < h) :
    (graphN d (h + 1)).IsLink
      (Sum.inl (Sum.inl (binNodeOfWord h (w ++ [b]) hwb)))
      (Sum.inl (binNodeOfWord h (w ++ [b]) hwb))
      (Sum.inl (binNodeOfWord h w (by
        rw [List.length_append, List.length_singleton] at hwb; omega))) := by
  change binNodeOfWord h (w ++ [b]) hwb ≠ none ∧ _
  refine ⟨binNodeOfWord_ne_none h (w ++ [b]) hwb, Or.inl ⟨rfl, ?_⟩⟩
  rw [treeYInternalParent_binNodeOfWord_snoc w b hwb]

/-! ## 4. Abstract Complete Binary Tree on `{w : List Bool // w.length < h}` -/

/-- The finite complete binary tree graph of height `h` (`h ≥ 1`) whose vertices are bit-words
`w : List Bool` of length `< h` and whose edges are non-empty bit-words `w` of length `< h`
linking `w` to `w.dropLast`. -/
def binWordTree (h : ℕ) : Graph (List Bool) (List Bool) where
  vertexSet := {w | w.length < h}
  edgeSet := {w | w ≠ [] ∧ w.length < h}
  IsLink e u v :=
    e ≠ [] ∧ e.length < h ∧ ((u = e ∧ v = e.dropLast) ∨ (v = e ∧ u = e.dropLast))
  isLink_symm _ _ := ⟨fun _ _ h => ⟨h.1, h.2.1, h.2.2.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := by
    rcases h1.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2.2.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl h3.symm
    · exact Or.inr h3.symm
    · exact Or.inr h4.symm
    · exact Or.inl h4.symm
  edge_mem_iff_exists_isLink e := by
    simp only [mem_ofPred_eq]
    exact ⟨fun ⟨hne, hlt⟩ => ⟨e, e.dropLast, hne, hlt, Or.inl ⟨rfl, rfl⟩⟩,
      fun ⟨_, _, hne, hlt, _⟩ => ⟨hne, hlt⟩⟩
  left_mem_of_isLink e u v h := by
    simp only [mem_ofPred_eq]
    rcases h.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.2.1
    · rw [List.length_dropLast]
      exact lt_of_le_of_lt (Nat.sub_le _ _) h.2.1

theorem dropLast_cons_ne_nil (b : Bool) {w : List Bool} (hw : w ≠ []) :
    (b :: w).dropLast = b :: w.dropLast := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a t => rfl

/-- Left-spine bit-words `[false, ..., false]` of length `≤ k`, connecting `[]` down to
`List.replicate k false` in `binWordTree`. -/
theorem reflTransGen_replicate_false {h : ℕ} {S : Set (List Bool)} {D : Set (List Bool)}
    (k : ℕ) (hk : k < h)
    (hS : ∀ j ≤ k, List.replicate j false ∈ S)
    (hD : ∀ j, 1 ≤ j → j ≤ k → List.replicate j false ∉ D) :
    Relation.ReflTransGen (((binWordTree h).deleteEdges D).induce S).Adj
      [] (List.replicate k false) := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ m ih =>
    have hm_lt : m < h := by omega
    have hprev := ih hm_lt (fun j hj => hS j (by omega)) (fun j hj1 hjm => hD j hj1 (by omega))
    refine Relation.ReflTransGen.tail hprev ?_
    let e := List.replicate (m + 1) false
    have he_eq : e = List.replicate m false ++ [false] := List.replicate_succ'
    have he_ne : e ≠ [] := by simp [e]
    have he_len : e.length < h := by simp [e, hk]
    have he_drop : e.dropLast = List.replicate m false := by
      rw [he_eq, List.dropLast_append_of_ne_nil (by simp)]
      simp
    refine ⟨e, ?_⟩
    rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
    refine ⟨⟨?_, hD (m + 1) (by omega) (le_rfl)⟩, hS m (by omega), hS (m + 1) le_rfl⟩
    exact ⟨he_ne, he_len, Or.inr ⟨rfl, he_drop.symm⟩⟩

/-- Transport a minor model of `F` in `binWordTree h` by prepending a bit `b :: ·` and lifting
height from `h` to `H ≥ h + 1`. -/
theorem transport_cons_adj {h H : ℕ} (hH : h + 1 ≤ H) (b : Bool)
    {S : Set (List Bool)} {D : Set (List Bool)} {x y : List Bool}
    (hadj : (((binWordTree h).deleteEdges D).induce S).Adj x y) :
    (((binWordTree H).deleteEdges ((List.cons b) '' D)).induce ((List.cons b) '' S)).Adj
      (b :: x) (b :: y) := by
  obtain ⟨e, hl⟩ := hadj
  rw [Graph.induce_isLink, Graph.deleteEdges_isLink] at hl
  obtain ⟨⟨⟨he_ne, he_lt, he_ends⟩, he_not_D⟩, hxS, hyS⟩ := hl
  refine ⟨b :: e, ?_⟩
  rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
  refine ⟨⟨⟨List.cons_ne_nil b e, ?_, ?_⟩, ?_⟩,
    mem_image_of_mem _ hxS, mem_image_of_mem _ hyS⟩
  · simp only [List.length_cons]; omega
  · rw [dropLast_cons_ne_nil b he_ne]
    rcases he_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro ⟨d, hd, hbd⟩
    exact he_not_D ((List.cons.inj hbd).2 ▸ hd)

theorem transport_cons_reflTransGen {h H : ℕ} (hH : h + 1 ≤ H) (b : Bool)
    {S : Set (List Bool)} {D : Set (List Bool)} {x y : List Bool}
    (hconn : Relation.ReflTransGen (((binWordTree h).deleteEdges D).induce S).Adj x y) :
    Relation.ReflTransGen
      (((binWordTree H).deleteEdges ((List.cons b) '' D)).induce ((List.cons b) '' S)).Adj
      (b :: x) (b :: y) := by
  induction hconn with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (transport_cons_adj hH b hstep)

theorem adj_mono_induce_deleteEdges {α : Type u} {β : Type v} {G : Graph α β}
    {S S' : Set α} {D D' : Set β} (hS : S ⊆ S') (hD : D' ⊆ D) {x y : α}
    (h : (((G.deleteEdges D).induce S).Adj x y)) :
    (((G.deleteEdges D').induce S').Adj x y) := by
  obtain ⟨e, hl⟩ := h
  rw [Graph.induce_isLink, Graph.deleteEdges_isLink] at hl
  refine ⟨e, ?_⟩
  rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
  exact ⟨⟨hl.1.1, fun hmem => hl.1.2 (hD hmem)⟩, hS hl.2.1, hS hl.2.2⟩

theorem reflTransGen_mono_induce_deleteEdges {α : Type u} {β : Type v} {G : Graph α β}
    {S S' : Set α} {D D' : Set β} (hS : S ⊆ S') (hD : D' ⊆ D) {x y : α}
    (h : Relation.ReflTransGen (((G.deleteEdges D).induce S).Adj) x y) :
    Relation.ReflTransGen (((G.deleteEdges D').induce S').Adj) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih (adj_mono_induce_deleteEdges hS hD hstep)

theorem reflTransGen_mono_rel {γ : Type*} {R₁ R₂ : γ → γ → Prop}
    (h : ∀ ⦃x y⦄, R₁ x y → R₂ x y) {a b : γ} (hr : Relation.ReflTransGen R₁ a b) :
    Relation.ReflTransGen R₂ a b := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (h hstep)

theorem reflTransGen_symm_of {γ : Type*} {R : γ → γ → Prop}
    (hsym : ∀ ⦃x y⦄, R x y → R y x) {a b : γ} (hr : Relation.ReflTransGen R a b) :
    Relation.ReflTransGen R b a := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (hsym hstep)) ih

/-! ## 5. Rooted Minor Embedding of Any Finite Simple Forest into `binWordTree` and `treeY` -/

/-- Every finite simple forest `F` admits a minor model in `binWordTree h` for some `h ≥ 1` such
that any chosen vertex `r` (when `r ∈ V(F)`) contains the root `[]` in its branch set. -/
theorem exists_binWordTree_model_of_forest {α : Type u} {β : Type v}
    (F : Graph α β) (hSimple : F.Simple) (hVF : V(F).Finite)
    (hNoCirc : ∀ C' ≤ F, ¬ GM09.IsGraphCircuit F C') (r : α) :
    ∃ (h : ℕ) (ηv : α → Set (List Bool)) (ηe : β → List Bool),
      1 ≤ h ∧
      IsMinorModel F (binWordTree h) ηv ηe ∧
      (r ∈ V(F) → [] ∈ ηv r) := by
  suffices hind : ∀ n : ℕ, ∀ (F₀ : Graph α β),
      F₀.Simple → V(F₀).Finite → V(F₀).ncard = n →
      (∀ C' ≤ F₀, ¬ GM09.IsGraphCircuit F₀ C') → ∀ r₀ : α,
      ∃ (h : ℕ) (ηv : α → Set (List Bool)) (ηe : β → List Bool),
        1 ≤ h ∧ IsMinorModel F₀ (binWordTree h) ηv ηe ∧ (r₀ ∈ V(F₀) → [] ∈ ηv r₀) from
    hind V(F).ncard F hSimple hVF rfl hNoCirc r
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F₀ hS₀ hVF₀ hn hNoCirc₀ r₀
    by_cases hV_empty : V(F₀) = ∅
    · refine ⟨1, fun _ => ∅, fun _ => [], le_rfl, ?_, fun hr => (notMem_empty r₀ (hV_empty ▸ hr)).elim⟩
      have hE_empty : E(F₀) = ∅ := by
        ext e
        simp only [mem_empty_iff_false, iff_false]
        intro he
        obtain ⟨u, _, hl⟩ := F₀.exists_isLink_of_mem_edgeSet he
        exact notMem_empty u (hV_empty ▸ hl.left_mem)
      exact isMinorModel_of_loopless_link
        (fun e he => (notMem_empty e (hE_empty ▸ he)).elim)
        (fun v hv => (notMem_empty v (hV_empty ▸ hv)).elim)
        (fun v hv => (notMem_empty v (hV_empty ▸ hv)).elim)
        (fun v₁ hv₁ => (notMem_empty v₁ (hV_empty ▸ hv₁)).elim)
        (fun e₁ he₁ => (notMem_empty e₁ (hE_empty ▸ he₁)).elim)
        (fun _ _ _ hl => (notMem_empty _ (hV_empty ▸ hl.left_mem)).elim)
        (fun u hu => (notMem_empty u (hV_empty ▸ hu)).elim)
    · have hV_ne : V(F₀).Nonempty := nonempty_iff_ne_empty.mpr hV_empty
      let base : α := if r₀ ∈ V(F₀) then r₀ else hV_ne.some
      have hbase_mem : base ∈ V(F₀) := by
        dsimp only [base]
        split_ifs with hr₀
        · exact hr₀
        · exact hV_ne.some_mem
      let V₁ : Set α := {z ∈ V(F₀) | Relation.ReflTransGen F₀.Adj base z}
      let V₂ : Set α := V(F₀) \ V₁
      have hbase_V₁ : base ∈ V₁ := ⟨hbase_mem, Relation.ReflTransGen.refl⟩
      have hV₁_sub : V₁ ⊆ V(F₀) := fun _ hz => hz.1
      have hV₂_sub : V₂ ⊆ V(F₀) := sdiff_subset
      by_cases hV₂_ne : V₂.Nonempty
      · -- Disconnected case: split into `F₁ = F₀.induce V₁` and `F₂ = F₀.induce V₂`
        have hno_cross : ∀ ⦃e u v⦄, F₀.IsLink e u v →
            (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∈ V₂ ∧ v ∈ V₂) := by
          intro e u v hl
          by_cases hu : u ∈ V₁
          · exact Or.inl ⟨hu, hl.right_mem, Relation.ReflTransGen.tail hu.2 ⟨e, hl⟩⟩
          · refine Or.inr ⟨⟨hl.left_mem, hu⟩, ⟨hl.right_mem, fun hv => hu ?_⟩⟩
            exact ⟨hl.left_mem, Relation.ReflTransGen.tail hv.2 ⟨e, hl.symm⟩⟩
        let F₁ := F₀.induce V₁
        let F₂ := F₀.induce V₂
        have hF₁_le : F₁ ≤ F₀ := Graph.induce_le hV₁_sub
        have hF₂_le : F₂ ≤ F₀ := Graph.induce_le hV₂_sub
        have hVF₁_eq : V(F₁) = V₁ := rfl
        have hVF₂_eq : V(F₂) = V₂ := rfl
        obtain ⟨y₀, hy₀⟩ := hV₂_ne
        have hn₁ : V(F₁).ncard < n := by
          rw [← hn, hVF₁_eq]
          exact ncard_lt_ncard ⟨hV₁_sub, fun hsub => hy₀.2 (hsub hy₀.1)⟩ hVF₀
        have hn₂ : V(F₂).ncard < n := by
          rw [← hn, hVF₂_eq]
          exact ncard_lt_ncard ⟨hV₂_sub, fun hsub => (hsub hbase_mem).2 hbase_V₁⟩ hVF₀
        obtain ⟨h₁, ηv₁, ηe₁, hh₁, hm₁, hroot₁⟩ := ih V(F₁).ncard hn₁ F₁
          (Simple.mono hS₀ hF₁_le) (hVF₀.subset (hVF₁_eq ▸ hV₁_sub)) rfl
          (fun C' hC' => by rw [isGraphCircuit_iff_of_le hF₁_le hC']; exact hNoCirc₀ C' (hC'.trans hF₁_le))
          base
        obtain ⟨h₂, ηv₂, ηe₂, hh₂, hm₂, _⟩ := ih V(F₂).ncard hn₂ F₂
          (Simple.mono hS₀ hF₂_le) (hVF₀.subset (hVF₂_eq ▸ hV₂_sub)) rfl
          (fun C' hC' => by rw [isGraphCircuit_iff_of_le hF₂_le hC']; exact hNoCirc₀ C' (hC'.trans hF₂_le))
          y₀
        let H := max h₁ h₂ + 1
        have hH₁ : h₁ + 1 ≤ H := by dsimp only [H]; omega
        have hH₂ : h₂ + 1 ≤ H := by dsimp only [H]; omega
        have hbase_root : [] ∈ ηv₁ base := hroot₁ (hVF₁_eq ▸ hbase_V₁)
        let ηv : α → Set (List Bool) := fun v =>
          if v = base then insert [] ((List.cons false) '' ηv₁ v)
          else if v ∈ V₁ then (List.cons false) '' ηv₁ v
          else (List.cons true) '' ηv₂ v
        let ηe : β → List Bool := fun e =>
          if e ∈ E(F₁) then false :: ηe₁ e else true :: ηe₂ e
        have hE_part : ∀ e ∈ E(F₀), (e ∈ E(F₁) ∧ e ∉ E(F₂)) ∨ (e ∉ E(F₁) ∧ e ∈ E(F₂)) := by
          intro e he
          obtain ⟨u, v, hl⟩ := F₀.exists_isLink_of_mem_edgeSet he
          rcases hno_cross hl with ⟨hu₁, hv₁⟩ | ⟨hu₂, hv₂⟩
          · refine Or.inl ⟨⟨u, v, (Graph.induce_isLink F₀ V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩, ?_⟩
            rintro ⟨a, b, hl₂⟩
            have hl₂' := (Graph.induce_isLink F₀ V₂ e a b).mp hl₂
            rcases hl₂'.1.left_eq_or_eq hl with h_eq | h_eq
            · exact hl₂'.2.1.2 (h_eq.symm ▸ hu₁)
            · exact hl₂'.2.1.2 (h_eq.symm ▸ hv₁)
          · refine Or.inr ⟨?_, ⟨u, v, (Graph.induce_isLink F₀ V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩⟩⟩
            rintro ⟨a, b, hl₁⟩
            have hl₁' := (Graph.induce_isLink F₀ V₁ e a b).mp hl₁
            rcases hl₁'.1.left_eq_or_eq hl with h_eq | h_eq
            · exact hu₂.2 (h_eq ▸ hl₁'.2.1)
            · exact hv₂.2 (h_eq ▸ hl₁'.2.1)
        refine ⟨H, ηv, ηe, by dsimp only [H]; omega, ?_, fun hr₀ => ?_⟩
        · refine isMinorModel_of_loopless_link
            (fun e _ u hl => hS₀.not_isLoopAt e u hl)
            (fun v hv => ?_)
            (fun v hv => ?_)
            (fun v₁ hv₁ v₂ hv₂ hne => ?_)
            (fun e₁ he₁ e₂ he₂ heq => ?_)
            (fun e u v hl => ?_)
            (fun u hu x hx y hy => ?_)
          · dsimp only [ηv]
            split_ifs with hvb hv₁
            · exact ⟨[], mem_insert _ _⟩
            · obtain ⟨w, hw⟩ := hm₁.vertex_nonempty v (hVF₁_eq ▸ hv₁)
              exact ⟨false :: w, mem_image_of_mem _ hw⟩
            · have hv₂ : v ∈ V₂ := ⟨hv, hv₁⟩
              obtain ⟨w, hw⟩ := hm₂.vertex_nonempty v (hVF₂_eq ▸ hv₂)
              exact ⟨true :: w, mem_image_of_mem _ hw⟩
          · dsimp only [ηv]
            split_ifs with hvb hv₁
            · subst v
              rintro w (rfl | ⟨w', hw', rfl⟩)
              · change [].length < H; simp; dsimp only [H]; omega
              · have hw'_lt : w'.length < h₁ := hm₁.vertex_subset base (hVF₁_eq ▸ hbase_V₁) hw'
                change (false :: w').length < H; simp only [List.length_cons]; omega
            · rintro _ ⟨w', hw', rfl⟩
              have hw'_lt : w'.length < h₁ := hm₁.vertex_subset v (hVF₁_eq ▸ hv₁) hw'
              change (false :: w').length < H; simp only [List.length_cons]; omega
            · have hv₂ : v ∈ V₂ := ⟨hv, hv₁⟩
              rintro _ ⟨w', hw', rfl⟩
              have hw'_lt : w'.length < h₂ := hm₂.vertex_subset v (hVF₂_eq ▸ hv₂) hw'
              change (true :: w').length < H; simp only [List.length_cons]; omega
          · rw [Set.disjoint_left]
            intro w hw₁ hw₂
            have hmem1 : ∀ z ∈ V(F₀), ∀ w' ∈ ηv z,
                (w' = [] ∧ z = base) ∨
                (∃ u', w' = false :: u' ∧ z ∈ V₁ ∧ u' ∈ ηv₁ z) ∨
                (∃ u', w' = true :: u' ∧ z ∈ V₂ ∧ u' ∈ ηv₂ z) := by
              intro z hz w' hw'
              dsimp only [ηv] at hw'
              split_ifs at hw' with hzb hz₁
              · rcases hw' with rfl | ⟨u', hu', rfl⟩
                · exact Or.inl ⟨rfl, hzb⟩
                · exact Or.inr (Or.inl ⟨u', rfl, hzb ▸ hbase_V₁, hu'⟩)
              · obtain ⟨u', hu', rfl⟩ := hw'
                exact Or.inr (Or.inl ⟨u', rfl, hz₁, hu'⟩)
              · obtain ⟨u', hu', rfl⟩ := hw'
                exact Or.inr (Or.inr ⟨u', rfl, ⟨hz, hz₁⟩, hu'⟩)
            rcases hmem1 v₁ hv₁ w hw₁ with ⟨hw_eq₁, hv₁_b⟩ | ⟨u₁, hw_eq₁, hv₁_1, hu₁⟩ | ⟨u₁, hw_eq₁, hv₁_2, hu₁⟩ <;>
              rcases hmem1 v₂ hv₂ w hw₂ with ⟨hw_eq₂, hv₂_b⟩ | ⟨u₂, hw_eq₂, hv₂_1, hu₂⟩ | ⟨u₂, hw_eq₂, hv₂_2, hu₂⟩
            · exact hne (hv₁_b.trans hv₂_b.symm)
            · cases hw_eq₁.symm.trans hw_eq₂
            · cases hw_eq₁.symm.trans hw_eq₂
            · cases hw_eq₁.symm.trans hw_eq₂
            · exact Set.disjoint_left.mp
                (hm₁.vertex_disjoint v₁ (hVF₁_eq ▸ hv₁_1) v₂ (hVF₁_eq ▸ hv₂_1) hne)
                hu₁ ((List.cons.inj (hw_eq₁.symm.trans hw_eq₂)).2 ▸ hu₂)
            · cases hw_eq₁.symm.trans hw_eq₂
            · cases hw_eq₁.symm.trans hw_eq₂
            · cases hw_eq₁.symm.trans hw_eq₂
            · exact Set.disjoint_left.mp
                (hm₂.vertex_disjoint v₁ (hVF₂_eq ▸ hv₁_2) v₂ (hVF₂_eq ▸ hv₂_2) hne)
                hu₁ ((List.cons.inj (hw_eq₁.symm.trans hw_eq₂)).2 ▸ hu₂)
          · dsimp only [ηe] at heq
            rcases hE_part e₁ he₁ with ⟨he₁_1, _⟩ | ⟨he₁_n1, he₁_2⟩ <;>
              rcases hE_part e₂ he₂ with ⟨he₂_1, _⟩ | ⟨he₂_n1, he₂_2⟩
            · simp only [he₁_1, he₂_1, ↓reduceIte] at heq
              exact hm₁.edge_injOn he₁_1 he₂_1 (List.cons.inj heq).2
            · simp only [he₁_1, he₂_n1, ↓reduceIte] at heq
              cases heq
            · simp only [he₁_n1, he₂_1, ↓reduceIte] at heq
              cases heq
            · simp only [he₁_n1, he₂_n1, ↓reduceIte] at heq
              exact hm₂.edge_injOn he₁_2 he₂_2 (List.cons.inj heq).2
          · rcases hno_cross hl with ⟨hu₁, hv₁⟩ | ⟨hu₂, hv₂⟩
            · have hl₁ : F₁.IsLink e u v := (Graph.induce_isLink F₀ V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
              have he₁ : e ∈ E(F₁) := hl₁.edge_mem
              obtain ⟨x', hx'u, hinc_x⟩ := (hm₁.inc_iff u (hVF₁_eq ▸ hu₁) e he₁).mp ⟨v, hl₁⟩
              obtain ⟨y', hy'v, hinc_y⟩ := (hm₁.inc_iff v (hVF₁_eq ▸ hv₁) e he₁).mp ⟨u, hl₁.symm⟩
              obtain ⟨z₁, hl_bw₁⟩ := hinc_x
              obtain ⟨z₂, hl_bw₂⟩ := hinc_y
              have hxy_ne : x' ≠ y' := by
                intro hxy
                have huv : u ≠ v := fun h => hS₀.not_isLoopAt e u (h ▸ hl)
                exact Set.disjoint_left.mp
                  (hm₁.vertex_disjoint u (hVF₁_eq ▸ hu₁) v (hVF₁_eq ▸ hv₁) huv) hx'u (hxy ▸ hy'v)
              have hl_xy : (binWordTree h₁).IsLink (ηe₁ e) x' y' :=
                (hl_bw₁.left_eq_or_eq hl_bw₂).elim (fun h1 => absurd h1 hxy_ne)
                  (fun h1 => h1 ▸ hl_bw₂.symm)
              have hfx_mem : false :: x' ∈ ηv u := by
                dsimp only [ηv]
                split_ifs with hub
                · exact mem_insert_of_mem _ (mem_image_of_mem _ hx'u)
                · exact mem_image_of_mem _ hx'u
              have hfy_mem : false :: y' ∈ ηv v := by
                dsimp only [ηv]
                split_ifs with hvb
                · exact mem_insert_of_mem _ (mem_image_of_mem _ hy'v)
                · exact mem_image_of_mem _ hy'v
              refine ⟨false :: x', hfx_mem, false :: y', hfy_mem, ?_⟩
              have hηe_eq : ηe e = false :: ηe₁ e := by dsimp only [ηe]; simp only [he₁, ↓reduceIte]
              rw [hηe_eq]
              obtain ⟨hne_e, hlt_e, hends⟩ := hl_xy
              refine ⟨List.cons_ne_nil _ _, by simp only [List.length_cons]; omega, ?_⟩
              rw [dropLast_cons_ne_nil false hne_e]
              rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩
            · have hl₂ : F₂.IsLink e u v := (Graph.induce_isLink F₀ V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩
              have he₂ : e ∈ E(F₂) := hl₂.edge_mem
              have he_not₁ : e ∉ E(F₁) := (hE_part e hl.edge_mem).resolve_left (fun h => h.2 he₂) |>.1
              obtain ⟨x', hx'u, z₁, hl_bw₁⟩ := (hm₂.inc_iff u (hVF₂_eq ▸ hu₂) e he₂).mp ⟨v, hl₂⟩
              obtain ⟨y', hy'v, z₂, hl_bw₂⟩ := (hm₂.inc_iff v (hVF₂_eq ▸ hv₂) e he₂).mp ⟨u, hl₂.symm⟩
              have hxy_ne : x' ≠ y' := by
                intro hxy
                have huv : u ≠ v := fun h => hS₀.not_isLoopAt e u (h ▸ hl)
                exact Set.disjoint_left.mp
                  (hm₂.vertex_disjoint u (hVF₂_eq ▸ hu₂) v (hVF₂_eq ▸ hv₂) huv) hx'u (hxy ▸ hy'v)
              have hl_xy : (binWordTree h₂).IsLink (ηe₂ e) x' y' :=
                (hl_bw₁.left_eq_or_eq hl_bw₂).elim (fun h1 => absurd h1 hxy_ne)
                  (fun h1 => h1 ▸ hl_bw₂.symm)
              have htx_mem : true :: x' ∈ ηv u := by
                have hub : u ≠ base := fun h => hu₂.2 (h ▸ hbase_V₁)
                dsimp only [ηv]
                simp only [hub, hu₂.2, ↓reduceIte]
                exact mem_image_of_mem _ hx'u
              have hty_mem : true :: y' ∈ ηv v := by
                have hvb : v ≠ base := fun h => hv₂.2 (h ▸ hbase_V₁)
                dsimp only [ηv]
                simp only [hvb, hv₂.2, ↓reduceIte]
                exact mem_image_of_mem _ hy'v
              refine ⟨true :: x', htx_mem, true :: y', hty_mem, ?_⟩
              have hηe_eq : ηe e = true :: ηe₂ e := by dsimp only [ηe]; simp only [he_not₁, ↓reduceIte]
              rw [hηe_eq]
              obtain ⟨hne_e, hlt_e, hends⟩ := hl_xy
              refine ⟨List.cons_ne_nil _ _, by simp only [List.length_cons]; omega, ?_⟩
              rw [dropLast_cons_ne_nil true hne_e]
              rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩
          · -- Branch-set connectivity in `binWordTree H`
            have hD₁_sub : ηe '' E(F₀) ∩ range (List.cons false) ⊆ (List.cons false) '' (ηe₁ '' E(F₁)) := by
              rintro _ ⟨⟨e, he, rfl⟩, ⟨w, hw⟩⟩
              dsimp only [ηe] at hw ⊢
              rcases hE_part e he with ⟨he₁, _⟩ | ⟨he_n1, _⟩
              · simp only [he₁, ↓reduceIte]
                exact mem_image_of_mem _ (mem_image_of_mem _ he₁)
              · simp only [he_n1, ↓reduceIte] at hw
                cases hw
            have hconn_sub₁ : ∀ v ∈ V₁, ∀ a ∈ ηv₁ v, ∀ b ∈ ηv₁ v,
                Relation.ReflTransGen
                  (((binWordTree H).deleteEdges (ηe '' E(F₀))).induce ((List.cons false) '' ηv₁ v)).Adj
                  (false :: a) (false :: b) := by
              intro v hv a ha b hb
              obtain ⟨K, hK_le, hVK, hK_conn⟩ := hm₁.connected v (hVF₁_eq ▸ hv)
              have hrel_ind : Relation.ReflTransGen
                  (((binWordTree h₁).deleteEdges (ηe₁ '' E(F₁))).induce (ηv₁ v)).Adj a b :=
                reflTransGen_mono_rel (fun p q ⟨f, hlf⟩ => ⟨f, (Graph.induce_isLink _ _ f p q).mpr
                  ⟨hlf.mono hK_le, hVK ▸ hlf.left_mem, hVK ▸ hlf.right_mem⟩⟩)
                  (hK_conn.2 a (hVK ▸ ha) b (hVK ▸ hb))
              refine reflTransGen_mono_rel (fun p q ⟨f, hlf⟩ => ?_)
                (transport_cons_reflTransGen hH₁ false hrel_ind)
              rw [Graph.induce_isLink, Graph.deleteEdges_isLink] at hlf
              refine ⟨f, (Graph.induce_isLink _ _ f p q).mpr
                ⟨(Graph.deleteEdges_isLink _ _ f p q).mpr ⟨hlf.1.1, ?_⟩, hlf.2.1, hlf.2.2⟩⟩
              intro hf_img
              obtain ⟨w, rfl⟩ : f ∈ range (List.cons false) := by
                rcases hlf.1.1.2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩
                · obtain ⟨a', _, rfl⟩ := hlf.2.1; exact ⟨a', rfl⟩
                · obtain ⟨b', _, rfl⟩ := hlf.2.2; exact ⟨b', rfl⟩
              exact hlf.1.2 (hD₁_sub ⟨hf_img, ⟨w, rfl⟩⟩)
            by_cases hub : u = base
            · subst hub
              have hηv_base : ηv base = insert [] ((List.cons false) '' ηv₁ base) := by
                dsimp only [ηv]; simp only [↓reduceIte]
              have hroot_step : (((binWordTree H).deleteEdges (ηe '' E(F₀))).induce (ηv base)).Adj
                  [] [false] := by
                refine ⟨[false], ?_⟩
                rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
                refine ⟨⟨⟨by simp, by simp; dsimp only [H]; omega, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩,
                  hηv_base ▸ mem_insert _ _,
                  hηv_base ▸ mem_insert_of_mem _ (mem_image_of_mem _ hbase_root)⟩
                rintro ⟨e, he, heq⟩
                dsimp only [ηe] at heq
                rcases hE_part e he with ⟨he₁, _⟩ | ⟨he_n1, _⟩
                · simp only [he₁, ↓reduceIte] at heq
                  have he_mem := hm₁.edge_mem e he₁
                  rw [(List.cons.inj heq).2] at he_mem
                  exact he_mem.1 rfl
                · simp only [he_n1, ↓reduceIte] at heq
                  cases heq
              have hto_root : ∀ z ∈ ηv base,
                  Relation.ReflTransGen
                    (((binWordTree H).deleteEdges (ηe '' E(F₀))).induce (ηv base)).Adj [] z := by
                intro z hz
                rw [hηv_base] at hz
                rcases hz with rfl | ⟨w, hw, rfl⟩
                · exact Relation.ReflTransGen.refl
                · have hsub : (List.cons false) '' ηv₁ base ⊆ ηv base := by
                    rw [hηv_base]; exact subset_insert _ _
                  have hpath := reflTransGen_mono_induce_deleteEdges hsub subset_rfl
                    (hconn_sub₁ base hbase_V₁ [] hbase_root w hw)
                  exact Relation.ReflTransGen.head hroot_step hpath
              exact Relation.ReflTransGen.trans
                (reflTransGen_symm_of (fun _ _ h => h.symm) (hto_root x hx)) (hto_root y hy)
            · by_cases hu₁ : u ∈ V₁
              · have hηv_u : ηv u = (List.cons false) '' ηv₁ u := by
                  dsimp only [ηv]; simp only [hub, hu₁, ↓reduceIte]
                rw [hηv_u] at hx hy ⊢
                obtain ⟨a, ha, rfl⟩ := hx
                obtain ⟨b, hb, rfl⟩ := hy
                exact hconn_sub₁ u hu₁ a ha b hb
              · have hu₂ : u ∈ V₂ := ⟨hu, hu₁⟩
                have hηv_u : ηv u = (List.cons true) '' ηv₂ u := by
                  dsimp only [ηv]; simp only [hub, hu₁, ↓reduceIte]
                rw [hηv_u] at hx hy ⊢
                obtain ⟨a, ha, rfl⟩ := hx
                obtain ⟨b, hb, rfl⟩ := hy
                obtain ⟨K, hK_le, hVK, hK_conn⟩ := hm₂.connected u (hVF₂_eq ▸ hu₂)
                have hrel_ind : Relation.ReflTransGen
                    (((binWordTree h₂).deleteEdges (ηe₂ '' E(F₂))).induce (ηv₂ u)).Adj a b :=
                  reflTransGen_mono_rel (fun p q ⟨f, hlf⟩ => ⟨f, (Graph.induce_isLink _ _ f p q).mpr
                    ⟨hlf.mono hK_le, hVK ▸ hlf.left_mem, hVK ▸ hlf.right_mem⟩⟩)
                    (hK_conn.2 a (hVK ▸ ha) b (hVK ▸ hb))
                refine reflTransGen_mono_rel (fun p q ⟨f, hlf⟩ => ?_)
                  (transport_cons_reflTransGen hH₂ true hrel_ind)
                rw [Graph.induce_isLink, Graph.deleteEdges_isLink] at hlf
                refine ⟨f, (Graph.induce_isLink _ _ f p q).mpr
                  ⟨(Graph.deleteEdges_isLink _ _ f p q).mpr ⟨hlf.1.1, ?_⟩, hlf.2.1, hlf.2.2⟩⟩
                rintro ⟨e, he, hf_eq⟩
                dsimp only [ηe] at hf_eq
                rcases hE_part e he with ⟨he₁, _⟩ | ⟨he_n1, he₂⟩
                · simp only [he₁, ↓reduceIte] at hf_eq
                  rcases hlf.1.1.2.2 with ⟨hp, _⟩ | ⟨hq, _⟩
                  · obtain ⟨a', _, heq'⟩ := hlf.2.1; cases heq'.trans (hp.trans hf_eq.symm)
                  · obtain ⟨b', _, heq'⟩ := hlf.2.2; cases heq'.trans (hq.trans hf_eq.symm)
                · simp only [he_n1, ↓reduceIte] at hf_eq
                  exact hlf.1.2 (hf_eq ▸ mem_image_of_mem _ (mem_image_of_mem _ he₂))
        · have hrb : r₀ = base := by dsimp only [base]; simp only [hr₀, ↓reduceIte]
          rw [hrb]
          dsimp only [ηv]
          simp only [↓reduceIte]
          exact mem_insert _ _
      · -- Connected case: `V₂ = ∅`, so `V₁ = V(F₀)`
        have hV₁_all : ∀ z ∈ V(F₀), Relation.ReflTransGen F₀.Adj base z := by
          intro z hz
          by_contra hnot
          exact hV₂_ne ⟨z, hz, fun hz₁ => hnot hz₁.2⟩
        by_cases hE_ne : E(F₀).Nonempty
        · -- Nonempty edge set: find an edge `e₀` incident with `base`
          obtain ⟨e_any, he_any⟩ := hE_ne
          obtain ⟨u_any, v_any, hl_any⟩ := F₀.exists_isLink_of_mem_edgeSet he_any
          have hex_inc : ∃ e₀ s, F₀.IsLink e₀ base s := by
            by_cases hbu : base = u_any
            · exact ⟨e_any, v_any, hbu ▸ hl_any⟩
            · obtain ⟨W, _⟩ := exists_isSimple_walk_of_reflTransGen hbase_mem
                (hV₁_all u_any hl_any.left_mem)
              cases W with
              | nil _ => exact (hbu rfl).elim
              | @cons _ s _ e₀ hl₀ _ => exact ⟨e₀, s, hl₀⟩
          obtain ⟨e₀, s, hl₀⟩ := hex_inc
          have hbs : base ≠ s := fun h => hS₀.not_isLoopAt e₀ base (h ▸ hl₀)
          let F' := F₀.deleteEdges {e₀}
          have hnot_conn : ¬ Relation.ReflTransGen F'.Adj base s :=
            not_reflTransGen_deleteEdge_of_no_circuit hS₀ hNoCirc₀ hl₀
          let W₁ : Set α := {z ∈ V(F₀) | Relation.ReflTransGen F'.Adj base z}
          let W₂ : Set α := V(F₀) \ W₁
          have hbase_W₁ : base ∈ W₁ := ⟨hbase_mem, Relation.ReflTransGen.refl⟩
          have hs_W₂ : s ∈ W₂ := ⟨hl₀.right_mem, fun hs => hnot_conn hs.2⟩
          have hW₁_sub : W₁ ⊆ V(F₀) := fun _ hz => hz.1
          have hW₂_sub : W₂ ⊆ V(F₀) := sdiff_subset
          have hno_cross' : ∀ ⦃e u v⦄, F'.IsLink e u v →
              (u ∈ W₁ ∧ v ∈ W₁) ∨ (u ∈ W₂ ∧ v ∈ W₂) := by
            intro e u v hl
            have hlF₀ : F₀.IsLink e u v := ((Graph.deleteEdges_isLink F₀ {e₀} e u v) ▸ hl).1
            by_cases hu : u ∈ W₁
            · exact Or.inl ⟨hu, hlF₀.right_mem, Relation.ReflTransGen.tail hu.2 ⟨e, hl⟩⟩
            · refine Or.inr ⟨⟨hlF₀.left_mem, hu⟩, ⟨hlF₀.right_mem, fun hv => hu ?_⟩⟩
              exact ⟨hlF₀.left_mem, Relation.ReflTransGen.tail hv.2 ⟨e, hl.symm⟩⟩
          let F₁ := F'.induce W₁
          let F₂ := F'.induce W₂
          have hF'_le : F' ≤ F₀ := Graph.deleteEdges_le
          have hF₁_le' : F₁ ≤ F' := Graph.induce_le hW₁_sub
          have hF₂_le' : F₂ ≤ F' := Graph.induce_le hW₂_sub
          have hF₁_le : F₁ ≤ F₀ := hF₁_le'.trans hF'_le
          have hF₂_le : F₂ ≤ F₀ := hF₂_le'.trans hF'_le
          have hVF₁_eq : V(F₁) = W₁ := rfl
          have hVF₂_eq : V(F₂) = W₂ := rfl
          have hn₁ : V(F₁).ncard < n := by
            rw [← hn, hVF₁_eq]
            exact ncard_lt_ncard ⟨hW₁_sub, fun hsub => hs_W₂.2 (hsub hs_W₂.1)⟩ hVF₀
          have hn₂ : V(F₂).ncard < n := by
            rw [← hn, hVF₂_eq]
            exact ncard_lt_ncard ⟨hW₂_sub, fun hsub => (hsub hbase_mem).2 hbase_W₁⟩ hVF₀
          obtain ⟨h₁, ηv₁, ηe₁, hh₁, hm₁, hroot₁⟩ := ih V(F₁).ncard hn₁ F₁
            (Simple.mono hS₀ hF₁_le) (hVF₀.subset (hVF₁_eq ▸ hW₁_sub)) rfl
            (fun C' hC' => by rw [isGraphCircuit_iff_of_le hF₁_le hC']; exact hNoCirc₀ C' (hC'.trans hF₁_le))
            base
          obtain ⟨h₂, ηv₂, ηe₂, hh₂, hm₂, hroot₂⟩ := ih V(F₂).ncard hn₂ F₂
            (Simple.mono hS₀ hF₂_le) (hVF₀.subset (hVF₂_eq ▸ hW₂_sub)) rfl
            (fun C' hC' => by rw [isGraphCircuit_iff_of_le hF₂_le hC']; exact hNoCirc₀ C' (hC'.trans hF₂_le))
            s
          let H := max h₁ h₂ + 1
          have hH₁ : h₁ + 1 ≤ H := by dsimp only [H]; omega
          have hH₂ : h₂ + 1 ≤ H := by dsimp only [H]; omega
          have hbase_root : [] ∈ ηv₁ base := hroot₁ (hVF₁_eq ▸ hbase_W₁)
          have hs_root : [] ∈ ηv₂ s := hroot₂ (hVF₂_eq ▸ hs_W₂)
          let ηv : α → Set (List Bool) := fun v =>
            if v = base then insert [] ((List.cons false) '' ηv₁ v)
            else if v ∈ W₁ then (List.cons false) '' ηv₁ v
            else (List.cons true) '' ηv₂ v
          let ηe : β → List Bool := fun e =>
            if e = e₀ then [true]
            else if e ∈ E(F₁) then false :: ηe₁ e
            else true :: ηe₂ e
          have hE_part : ∀ e ∈ E(F₀), e ≠ e₀ →
              (e ∈ E(F₁) ∧ e ∉ E(F₂)) ∨ (e ∉ E(F₁) ∧ e ∈ E(F₂)) := by
            intro e he hne₀
            obtain ⟨u, v, hl⟩ := F₀.exists_isLink_of_mem_edgeSet he
            have hl' : F'.IsLink e u v := (Graph.deleteEdges_isLink F₀ {e₀} e u v).mpr ⟨hl, hne₀⟩
            rcases hno_cross' hl' with ⟨hu₁, hv₁⟩ | ⟨hu₂, hv₂⟩
            · refine Or.inl ⟨⟨u, v, (Graph.induce_isLink F' W₁ e u v).mpr ⟨hl', hu₁, hv₁⟩⟩, ?_⟩
              rintro ⟨a, b, hl₂⟩
              have hl₂' := (Graph.induce_isLink F' W₂ e a b).mp hl₂
              rcases hl₂'.1.left_eq_or_eq hl' with h_eq | h_eq
              · exact hl₂'.2.1.2 (h_eq.symm ▸ hu₁)
              · exact hl₂'.2.1.2 (h_eq.symm ▸ hv₁)
            · refine Or.inr ⟨?_, ⟨u, v, (Graph.induce_isLink F' W₂ e u v).mpr ⟨hl', hu₂, hv₂⟩⟩⟩
              rintro ⟨a, b, hl₁⟩
              have hl₁' := (Graph.induce_isLink F' W₁ e a b).mp hl₁
              rcases hl₁'.1.left_eq_or_eq hl' with h_eq | h_eq
              · exact hu₂.2 (h_eq ▸ hl₁'.2.1)
              · exact hv₂.2 (h_eq ▸ hl₁'.2.1)
          refine ⟨H, ηv, ηe, by dsimp only [H]; omega, ?_, fun hr₀ => ?_⟩
          · refine isMinorModel_of_loopless_link
              (fun e _ u hl => hS₀.not_isLoopAt e u hl)
              (fun v hv => ?_)
              (fun v hv => ?_)
              (fun v₁ hv₁ v₂ hv₂ hne => ?_)
              (fun e₁ he₁ e₂ he₂ heq => ?_)
              (fun e u v hl => ?_)
              (fun u hu x hx y hy => ?_)
            · dsimp only [ηv]
              split_ifs with hvb hv₁
              · exact ⟨[], mem_insert _ _⟩
              · obtain ⟨w, hw⟩ := hm₁.vertex_nonempty v (hVF₁_eq ▸ hv₁)
                exact ⟨false :: w, mem_image_of_mem _ hw⟩
              · obtain ⟨w, hw⟩ := hm₂.vertex_nonempty v (hVF₂_eq ▸ ⟨hv, hv₁⟩)
                exact ⟨true :: w, mem_image_of_mem _ hw⟩
            · dsimp only [ηv]
              split_ifs with hvb hv₁
              · subst v
                rintro w (rfl | ⟨w', hw', rfl⟩)
                · change [].length < H; simp; dsimp only [H]; omega
                · have hw'_lt : w'.length < h₁ := hm₁.vertex_subset base (hVF₁_eq ▸ hbase_W₁) hw'
                  change (false :: w').length < H; simp only [List.length_cons]; omega
              · rintro _ ⟨w', hw', rfl⟩
                have hw'_lt : w'.length < h₁ := hm₁.vertex_subset v (hVF₁_eq ▸ hv₁) hw'
                change (false :: w').length < H; simp only [List.length_cons]; omega
              · rintro _ ⟨w', hw', rfl⟩
                have hw'_lt : w'.length < h₂ := hm₂.vertex_subset v (hVF₂_eq ▸ ⟨hv, hv₁⟩) hw'
                change (true :: w').length < H; simp only [List.length_cons]; omega
            · rw [Set.disjoint_left]
              intro w hw₁ hw₂
              have hmem1 : ∀ z ∈ V(F₀), ∀ w' ∈ ηv z,
                  (w' = [] ∧ z = base) ∨
                  (∃ u', w' = false :: u' ∧ z ∈ W₁ ∧ u' ∈ ηv₁ z) ∨
                  (∃ u', w' = true :: u' ∧ z ∈ W₂ ∧ u' ∈ ηv₂ z) := by
                intro z hz w' hw'
                dsimp only [ηv] at hw'
                split_ifs at hw' with hzb hz₁
                · rcases hw' with rfl | ⟨u', hu', rfl⟩
                  · exact Or.inl ⟨rfl, hzb⟩
                  · exact Or.inr (Or.inl ⟨u', rfl, hzb ▸ hbase_W₁, hu'⟩)
                · obtain ⟨u', hu', rfl⟩ := hw'
                  exact Or.inr (Or.inl ⟨u', rfl, hz₁, hu'⟩)
                · obtain ⟨u', hu', rfl⟩ := hw'
                  exact Or.inr (Or.inr ⟨u', rfl, ⟨hz, hz₁⟩, hu'⟩)
              rcases hmem1 v₁ hv₁ w hw₁ with ⟨hw_eq₁, hv₁_b⟩ | ⟨u₁, hw_eq₁, hv₁_1, hu₁⟩ | ⟨u₁, hw_eq₁, hv₁_2, hu₁⟩ <;>
                rcases hmem1 v₂ hv₂ w hw₂ with ⟨hw_eq₂, hv₂_b⟩ | ⟨u₂, hw_eq₂, hv₂_1, hu₂⟩ | ⟨u₂, hw_eq₂, hv₂_2, hu₂⟩
              · exact hne (hv₁_b.trans hv₂_b.symm)
              · cases hw_eq₁.symm.trans hw_eq₂
              · cases hw_eq₁.symm.trans hw_eq₂
              · cases hw_eq₁.symm.trans hw_eq₂
              · exact Set.disjoint_left.mp
                  (hm₁.vertex_disjoint v₁ (hVF₁_eq ▸ hv₁_1) v₂ (hVF₁_eq ▸ hv₂_1) hne)
                  hu₁ ((List.cons.inj (hw_eq₁.symm.trans hw_eq₂)).2 ▸ hu₂)
              · cases hw_eq₁.symm.trans hw_eq₂
              · cases hw_eq₁.symm.trans hw_eq₂
              · cases hw_eq₁.symm.trans hw_eq₂
              · exact Set.disjoint_left.mp
                  (hm₂.vertex_disjoint v₁ (hVF₂_eq ▸ hv₁_2) v₂ (hVF₂_eq ▸ hv₂_2) hne)
                  hu₁ ((List.cons.inj (hw_eq₁.symm.trans hw_eq₂)).2 ▸ hu₂)
            · dsimp only [ηe] at heq
              by_cases h10 : e₁ = e₀ <;> by_cases h20 : e₂ = e₀
              · exact h10.trans h20.symm
              · subst e₁
                rcases hE_part e₂ he₂ h20 with ⟨he₂_1, _⟩ | ⟨he₂_n1, he₂_2⟩
                · simp only [↓reduceIte, h20, he₂_1] at heq
                  cases heq
                · simp only [↓reduceIte, h20, he₂_n1] at heq
                  have hm := hm₂.edge_mem e₂ he₂_2
                  rw [← (List.cons.inj heq).2] at hm
                  exact (hm.1 rfl).elim
              · subst e₂
                rcases hE_part e₁ he₁ h10 with ⟨he₁_1, _⟩ | ⟨he₁_n1, he₁_2⟩
                · simp only [↓reduceIte, h10, he₁_1] at heq
                  cases heq
                · simp only [↓reduceIte, h10, he₁_n1] at heq
                  have hm := hm₂.edge_mem e₁ he₁_2
                  rw [(List.cons.inj heq).2] at hm
                  exact (hm.1 rfl).elim
              · rcases hE_part e₁ he₁ h10 with ⟨he₁_1, _⟩ | ⟨he₁_n1, he₁_2⟩ <;>
                  rcases hE_part e₂ he₂ h20 with ⟨he₂_1, _⟩ | ⟨he₂_n1, he₂_2⟩
                · simp only [h10, h20, he₁_1, he₂_1, ↓reduceIte] at heq
                  exact hm₁.edge_injOn he₁_1 he₂_1 (List.cons.inj heq).2
                · simp only [h10, h20, he₁_1, he₂_n1, ↓reduceIte] at heq
                  cases heq
                · simp only [h10, h20, he₁_n1, he₂_1, ↓reduceIte] at heq
                  cases heq
                · simp only [h10, h20, he₁_n1, he₂_n1, ↓reduceIte] at heq
                  exact hm₂.edge_injOn he₁_2 he₂_2 (List.cons.inj heq).2
            · by_cases he₀ : e = e₀
              · subst e
                have hηe₀ : ηe e₀ = [true] := by dsimp only [ηe]; simp only [↓reduceIte]
                have hroot_in_base : [] ∈ ηv base := by
                  dsimp only [ηv]; simp only [↓reduceIte]; exact mem_insert _ _
                have htrue_in_s : [true] ∈ ηv s := by
                  have hsb : s ≠ base := hbs.symm
                  dsimp only [ηv]
                  simp only [hsb, hs_W₂.2, ↓reduceIte]
                  exact mem_image_of_mem _ hs_root
                have hl_true : (binWordTree H).IsLink [true] [] [true] :=
                  ⟨by simp, by simp; dsimp only [H]; omega, Or.inr ⟨rfl, rfl⟩⟩
                rcases hl.left_eq_or_eq hl₀ with rfl | rfl
                · rw [hl.right_unique hl₀, hηe₀]
                  exact ⟨[], hroot_in_base, [true], htrue_in_s, hl_true⟩
                · rw [hl.right_unique hl₀.symm, hηe₀]
                  exact ⟨[true], htrue_in_s, [], hroot_in_base, hl_true.symm⟩
              · have hl' : F'.IsLink e u v := (Graph.deleteEdges_isLink F₀ {e₀} e u v).mpr ⟨hl, he₀⟩
                rcases hno_cross' hl' with ⟨hu₁, hv₁⟩ | ⟨hu₂, hv₂⟩
                · have hl₁ : F₁.IsLink e u v := (Graph.induce_isLink F' W₁ e u v).mpr ⟨hl', hu₁, hv₁⟩
                  have he₁ : e ∈ E(F₁) := hl₁.edge_mem
                  obtain ⟨x', hx'u, z₁, hl_bw₁⟩ := (hm₁.inc_iff u (hVF₁_eq ▸ hu₁) e he₁).mp ⟨v, hl₁⟩
                  obtain ⟨y', hy'v, z₂, hl_bw₂⟩ := (hm₁.inc_iff v (hVF₁_eq ▸ hv₁) e he₁).mp ⟨u, hl₁.symm⟩
                  have hxy_ne : x' ≠ y' := by
                    intro hxy
                    have huv : u ≠ v := fun h => hS₀.not_isLoopAt e u (h ▸ hl)
                    exact Set.disjoint_left.mp
                      (hm₁.vertex_disjoint u (hVF₁_eq ▸ hu₁) v (hVF₁_eq ▸ hv₁) huv) hx'u (hxy ▸ hy'v)
                  have hl_xy : (binWordTree h₁).IsLink (ηe₁ e) x' y' :=
                    (hl_bw₁.left_eq_or_eq hl_bw₂).elim (fun h1 => absurd h1 hxy_ne)
                      (fun h1 => h1 ▸ hl_bw₂.symm)
                  have hfx_mem : false :: x' ∈ ηv u := by
                    dsimp only [ηv]
                    split_ifs with hub
                    · exact mem_insert_of_mem _ (mem_image_of_mem _ hx'u)
                    · exact mem_image_of_mem _ hx'u
                  have hfy_mem : false :: y' ∈ ηv v := by
                    dsimp only [ηv]
                    split_ifs with hvb
                    · exact mem_insert_of_mem _ (mem_image_of_mem _ hy'v)
                    · exact mem_image_of_mem _ hy'v
                  refine ⟨false :: x', hfx_mem, false :: y', hfy_mem, ?_⟩
                  have hηe_eq : ηe e = false :: ηe₁ e := by
                    dsimp only [ηe]; simp only [he₀, he₁, ↓reduceIte]
                  rw [hηe_eq]
                  obtain ⟨hne_e, hlt_e, hends⟩ := hl_xy
                  refine ⟨List.cons_ne_nil _ _, by simp only [List.length_cons]; omega, ?_⟩
                  rw [dropLast_cons_ne_nil false hne_e]
                  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Or.inl ⟨rfl, rfl⟩
                  · exact Or.inr ⟨rfl, rfl⟩
                · have hl₂ : F₂.IsLink e u v := (Graph.induce_isLink F' W₂ e u v).mpr ⟨hl', hu₂, hv₂⟩
                  have he₂ : e ∈ E(F₂) := hl₂.edge_mem
                  have he_not₁ : e ∉ E(F₁) :=
                    (hE_part e hl.edge_mem he₀).resolve_left (fun h => h.2 he₂) |>.1
                  obtain ⟨x', hx'u, z₁, hl_bw₁⟩ := (hm₂.inc_iff u (hVF₂_eq ▸ hu₂) e he₂).mp ⟨v, hl₂⟩
                  obtain ⟨y', hy'v, z₂, hl_bw₂⟩ := (hm₂.inc_iff v (hVF₂_eq ▸ hv₂) e he₂).mp ⟨u, hl₂.symm⟩
                  have hxy_ne : x' ≠ y' := by
                    intro hxy
                    have huv : u ≠ v := fun h => hS₀.not_isLoopAt e u (h ▸ hl)
                    exact Set.disjoint_left.mp
                      (hm₂.vertex_disjoint u (hVF₂_eq ▸ hu₂) v (hVF₂_eq ▸ hv₂) huv) hx'u (hxy ▸ hy'v)
                  have hl_xy : (binWordTree h₂).IsLink (ηe₂ e) x' y' :=
                    (hl_bw₁.left_eq_or_eq hl_bw₂).elim (fun h1 => absurd h1 hxy_ne)
                      (fun h1 => h1 ▸ hl_bw₂.symm)
                  have htx_mem : true :: x' ∈ ηv u := by
                    have hub : u ≠ base := fun h => hu₂.2 (h ▸ hbase_W₁)
                    dsimp only [ηv]
                    simp only [hub, hu₂.2, ↓reduceIte]
                    exact mem_image_of_mem _ hx'u
                  have hty_mem : true :: y' ∈ ηv v := by
                    have hvb : v ≠ base := fun h => hv₂.2 (h ▸ hbase_W₁)
                    dsimp only [ηv]
                    simp only [hvb, hv₂.2, ↓reduceIte]
                    exact mem_image_of_mem _ hy'v
                  refine ⟨true :: x', htx_mem, true :: y', hty_mem, ?_⟩
                  have hηe_eq : ηe e = true :: ηe₂ e := by
                    dsimp only [ηe]; simp only [he₀, he_not₁, ↓reduceIte]
                  rw [hηe_eq]
                  obtain ⟨hne_e, hlt_e, hends⟩ := hl_xy
                  refine ⟨List.cons_ne_nil _ _, by simp only [List.length_cons]; omega, ?_⟩
                  rw [dropLast_cons_ne_nil true hne_e]
                  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Or.inl ⟨rfl, rfl⟩
                  · exact Or.inr ⟨rfl, rfl⟩
            · -- Branch-set connectivity in `binWordTree H`
              have hconn_sub₁ : ∀ v ∈ W₁, ∀ a ∈ ηv₁ v, ∀ b ∈ ηv₁ v,
                  Relation.ReflTransGen
                    (((binWordTree H).deleteEdges (ηe '' E(F₀))).induce ((List.cons false) '' ηv₁ v)).Adj
                    (false :: a) (false :: b) := by
                intro v hv a ha b hb
                obtain ⟨K, hK_le, hVK, hK_conn⟩ := hm₁.connected v (hVF₁_eq ▸ hv)
                have hrel_ind : Relation.ReflTransGen
                    (((binWordTree h₁).deleteEdges (ηe₁ '' E(F₁))).induce (ηv₁ v)).Adj a b :=
                  reflTransGen_mono_rel (fun p q ⟨f, hlf⟩ => ⟨f, (Graph.induce_isLink _ _ f p q).mpr
                    ⟨hlf.mono hK_le, hVK ▸ hlf.left_mem, hVK ▸ hlf.right_mem⟩⟩)
                    (hK_conn.2 a (hVK ▸ ha) b (hVK ▸ hb))
                refine reflTransGen_mono_rel (fun p q ⟨f, hlf⟩ => ?_)
                  (transport_cons_reflTransGen hH₁ false hrel_ind)
                rw [Graph.induce_isLink, Graph.deleteEdges_isLink] at hlf
                refine ⟨f, (Graph.induce_isLink _ _ f p q).mpr
                  ⟨(Graph.deleteEdges_isLink _ _ f p q).mpr ⟨hlf.1.1, ?_⟩, hlf.2.1, hlf.2.2⟩⟩
                rintro ⟨e, he, hf_eq⟩
                dsimp only [ηe] at hf_eq
                by_cases he₀ : e = e₀
                · simp only [he₀, ↓reduceIte] at hf_eq
                  rcases hlf.1.1.2.2 with ⟨hp, _⟩ | ⟨hq, _⟩
                  · obtain ⟨a', _, heq'⟩ := hlf.2.1; cases heq'.trans (hp.trans hf_eq.symm)
                  · obtain ⟨b', _, heq'⟩ := hlf.2.2; cases heq'.trans (hq.trans hf_eq.symm)
                · rcases hE_part e he he₀ with ⟨he₁, _⟩ | ⟨he_n1, _⟩
                  · simp only [he₀, he₁, ↓reduceIte] at hf_eq
                    exact hlf.1.2 (hf_eq ▸ mem_image_of_mem _ (mem_image_of_mem _ he₁))
                  · simp only [he₀, he_n1, ↓reduceIte] at hf_eq
                    rcases hlf.1.1.2.2 with ⟨hp, _⟩ | ⟨hq, _⟩
                    · obtain ⟨a', _, heq'⟩ := hlf.2.1; cases heq'.trans (hp.trans hf_eq.symm)
                    · obtain ⟨b', _, heq'⟩ := hlf.2.2; cases heq'.trans (hq.trans hf_eq.symm)
              by_cases hub : u = base
              · subst hub
                have hηv_base : ηv base = insert [] ((List.cons false) '' ηv₁ base) := by
                  dsimp only [ηv]; simp only [↓reduceIte]
                have hroot_step : (((binWordTree H).deleteEdges (ηe '' E(F₀))).induce (ηv base)).Adj
                    [] [false] := by
                  refine ⟨[false], ?_⟩
                  rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
                  refine ⟨⟨⟨by simp, by simp; dsimp only [H]; omega, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩,
                    hηv_base ▸ mem_insert _ _,
                    hηv_base ▸ mem_insert_of_mem _ (mem_image_of_mem _ hbase_root)⟩
                  rintro ⟨e, he, heq⟩
                  dsimp only [ηe] at heq
                  by_cases he₀ : e = e₀
                  · simp only [he₀, ↓reduceIte] at heq; cases heq
                  · rcases hE_part e he he₀ with ⟨he₁, _⟩ | ⟨he_n1, _⟩
                    · simp only [he₀, he₁, ↓reduceIte] at heq
                      have he_mem := hm₁.edge_mem e he₁
                      rw [(List.cons.inj heq).2] at he_mem
                      exact he_mem.1 rfl
                    · simp only [he₀, he_n1, ↓reduceIte] at heq; cases heq
                have hto_root : ∀ z ∈ ηv base,
                    Relation.ReflTransGen
                      (((binWordTree H).deleteEdges (ηe '' E(F₀))).induce (ηv base)).Adj [] z := by
                  intro z hz
                  rw [hηv_base] at hz
                  rcases hz with rfl | ⟨w, hw, rfl⟩
                  · exact Relation.ReflTransGen.refl
                  · have hsub : (List.cons false) '' ηv₁ base ⊆ ηv base := by
                      rw [hηv_base]; exact subset_insert _ _
                    have hpath := reflTransGen_mono_induce_deleteEdges hsub subset_rfl
                      (hconn_sub₁ base hbase_W₁ [] hbase_root w hw)
                    exact Relation.ReflTransGen.head hroot_step hpath
                exact Relation.ReflTransGen.trans
                  (reflTransGen_symm_of (fun _ _ h => h.symm) (hto_root x hx)) (hto_root y hy)
              · by_cases hu₁ : u ∈ W₁
                · have hηv_u : ηv u = (List.cons false) '' ηv₁ u := by
                    dsimp only [ηv]; simp only [hub, hu₁, ↓reduceIte]
                  rw [hηv_u] at hx hy ⊢
                  obtain ⟨a, ha, rfl⟩ := hx
                  obtain ⟨b, hb, rfl⟩ := hy
                  exact hconn_sub₁ u hu₁ a ha b hb
                · have hu₂ : u ∈ W₂ := ⟨hu, hu₁⟩
                  have hηv_u : ηv u = (List.cons true) '' ηv₂ u := by
                    dsimp only [ηv]; simp only [hub, hu₁, ↓reduceIte]
                  rw [hηv_u] at hx hy ⊢
                  obtain ⟨a, ha, rfl⟩ := hx
                  obtain ⟨b, hb, rfl⟩ := hy
                  obtain ⟨K, hK_le, hVK, hK_conn⟩ := hm₂.connected u (hVF₂_eq ▸ hu₂)
                  have hrel_ind : Relation.ReflTransGen
                      (((binWordTree h₂).deleteEdges (ηe₂ '' E(F₂))).induce (ηv₂ u)).Adj a b :=
                    reflTransGen_mono_rel (fun p q ⟨f, hlf⟩ => ⟨f, (Graph.induce_isLink _ _ f p q).mpr
                      ⟨hlf.mono hK_le, hVK ▸ hlf.left_mem, hVK ▸ hlf.right_mem⟩⟩)
                      (hK_conn.2 a (hVK ▸ ha) b (hVK ▸ hb))
                  refine reflTransGen_mono_rel (fun p q ⟨f, hlf⟩ => ?_)
                    (transport_cons_reflTransGen hH₂ true hrel_ind)
                  rw [Graph.induce_isLink, Graph.deleteEdges_isLink] at hlf
                  refine ⟨f, (Graph.induce_isLink _ _ f p q).mpr
                    ⟨(Graph.deleteEdges_isLink _ _ f p q).mpr ⟨hlf.1.1, ?_⟩, hlf.2.1, hlf.2.2⟩⟩
                  rintro ⟨e, he, hf_eq⟩
                  dsimp only [ηe] at hf_eq
                  by_cases he₀ : e = e₀
                  · simp only [he₀, ↓reduceIte] at hf_eq
                    rcases hlf.1.1.2.2 with ⟨_, hq⟩ | ⟨_, hp⟩
                    · obtain ⟨b', _, heq'⟩ := hlf.2.2
                      cases heq'.trans (hq.trans (by rw [← hf_eq]))
                    · obtain ⟨a', _, heq'⟩ := hlf.2.1
                      cases heq'.trans (hp.trans (by rw [← hf_eq]))
                  · rcases hE_part e he he₀ with ⟨he₁, _⟩ | ⟨he_n1, he₂⟩
                    · simp only [he₀, he₁, ↓reduceIte] at hf_eq
                      rcases hlf.1.1.2.2 with ⟨hp, _⟩ | ⟨hq, _⟩
                      · obtain ⟨a', _, heq'⟩ := hlf.2.1; cases heq'.trans (hp.trans hf_eq.symm)
                      · obtain ⟨b', _, heq'⟩ := hlf.2.2; cases heq'.trans (hq.trans hf_eq.symm)
                    · simp only [he₀, he_n1, ↓reduceIte] at hf_eq
                      exact hlf.1.2 (hf_eq ▸ mem_image_of_mem _ (mem_image_of_mem _ he₂))
          · have hrb : r₀ = base := by dsimp only [base]; simp only [hr₀, ↓reduceIte]
            rw [hrb]
            dsimp only [ηv]
            simp only [↓reduceIte]
            exact mem_insert _ _
        · -- `E(F₀) = ∅` and connected: `V(F₀) = {base}`
          have hE_emp : E(F₀) = ∅ := not_nonempty_iff_eq_empty.mp hE_ne
          have hV_eq : V(F₀) = {base} := by
            ext z
            constructor
            · intro hz
              have hconn := hV₁_all z hz
              cases hconn with
              | refl => rfl
              | tail _ hstep =>
                obtain ⟨e, hl⟩ := hstep
                exact (notMem_empty e (hE_emp ▸ hl.edge_mem)).elim
            · rintro rfl
              exact hbase_mem
          refine ⟨1, fun _ => {[]}, fun _ => [], le_rfl, ?_, fun _ => mem_singleton []⟩
          exact isMinorModel_of_loopless_link
            (fun e he => (notMem_empty e (hE_emp ▸ he)).elim)
            (fun _ _ => singleton_nonempty [])
            (fun _ _ w hw => by rcases mem_singleton_iff.mp hw with rfl; change [].length < 1; simp)
            (fun v₁ hv₁ v₂ hv₂ hne => by
              rw [hV_eq] at hv₁ hv₂
              exact (hne (hv₁.trans hv₂.symm)).elim)
            (fun e₁ he₁ => (notMem_empty e₁ (hE_emp ▸ he₁)).elim)
            (fun e _ _ hl => (notMem_empty e (hE_emp ▸ hl.edge_mem)).elim)
            (fun _ _ x hx y hy => by
              rw [mem_singleton_iff.mp hx, mem_singleton_iff.mp hy])

/-- Map a minor model in `binWordTree h` (`h ≥ 1`) into a minor model in `treeY (h + 1)`. -/
theorem isMinorModel_treeY_of_binWordTree {α : Type u} {β : Type v}
    {F : Graph α β} {h : ℕ} {ηv : α → Set (List Bool)} {ηe : β → List Bool}
    (hSimple : F.Simple) (hm : IsMinorModel F (binWordTree h) ηv ηe) :
    ∃ (φv : α → Set (GraphNVertex 0 (h + 1))) (φe : β → GraphNEdge 0 (h + 1)),
      IsMinorModel F (treeY (h + 1)) φv φe := by
  let φv : α → Set (GraphNVertex 0 (h + 1)) := fun v =>
    {z | ∃ (w : List Bool) (hw : w.length < h), w ∈ ηv v ∧ z = Sum.inl (binNodeOfWord h w hw)}
  let φe : β → GraphNEdge 0 (h + 1) := fun e =>
    if he : (ηe e).length < h then Sum.inl (Sum.inl (binNodeOfWord h (ηe e) he))
    else Sum.inl (Sum.inl none)
  refine ⟨φv, φe, isMinorModel_of_loopless_link
    (fun e _ u hl => hSimple.not_isLoopAt e u hl)
    (fun v hv => ?_)
    (fun v _ => subset_univ _)
    (fun v₁ hv₁ v₂ hv₂ hne => ?_)
    (fun e₁ he₁ e₂ he₂ heq => ?_)
    (fun e u v hl => ?_)
    (fun u hu x hx y hy => ?_)⟩
  · obtain ⟨w, hw⟩ := hm.vertex_nonempty v hv
    exact ⟨Sum.inl (binNodeOfWord h w (hm.vertex_subset v hv hw)),
      w, hm.vertex_subset v hv hw, hw, rfl⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨w₁, hw₁_lt, hw₁, rfl⟩ ⟨w₂, hw₂_lt, hw₂, heq⟩
    injection heq with h'
    have hw_eq := binNodeOfWord_inj hw₁_lt hw₂_lt h'
    exact Set.disjoint_left.mp (hm.vertex_disjoint v₁ hv₁ v₂ hv₂ hne) hw₁ (hw_eq ▸ hw₂)
  · have hlt₁ : (ηe e₁).length < h := (hm.edge_mem e₁ he₁).2
    have hlt₂ : (ηe e₂).length < h := (hm.edge_mem e₂ he₂).2
    dsimp only [φe] at heq
    simp only [hlt₁, hlt₂, ↓reduceDIte] at heq
    injection heq with h1
    injection h1 with h2
    exact hm.edge_injOn he₁ he₂ (binNodeOfWord_inj hlt₁ hlt₂ h2)
  · have he : e ∈ E(F) := hl.edge_mem
    obtain ⟨x', hx'u, z₁, hbw₁⟩ := (hm.inc_iff u hl.left_mem e he).mp ⟨v, hl⟩
    obtain ⟨y', hy'v, z₂, hbw₂⟩ := (hm.inc_iff v hl.right_mem e he).mp ⟨u, hl.symm⟩
    have hxy_ne : x' ≠ y' := by
      intro hxy
      have huv : u ≠ v := fun h' => hSimple.not_isLoopAt e u (h' ▸ hl)
      exact Set.disjoint_left.mp (hm.vertex_disjoint u hl.left_mem v hl.right_mem huv)
        hx'u (hxy ▸ hy'v)
    have hl_xy : (binWordTree h).IsLink (ηe e) x' y' :=
      (hbw₁.left_eq_or_eq hbw₂).elim (fun h1 => absurd h1 hxy_ne) (fun h1 => h1 ▸ hbw₂.symm)
    obtain ⟨hne_e, hlt_e, hends⟩ := hl_xy
    have hsnoc : ηe e = (ηe e).dropLast ++ [(ηe e).getLast hne_e] :=
      (List.dropLast_append_getLast hne_e).symm
    have hsnoc_lt : ((ηe e).dropLast ++ [(ηe e).getLast hne_e]).length < h := hsnoc ▸ hlt_e
    have hl_treeY := graphN_isLink_binNode_snoc 0 (ηe e).dropLast ((ηe e).getLast hne_e) hsnoc_lt
    have hφe_eq : φe e = Sum.inl (Sum.inl (binNodeOfWord h (ηe e) hlt_e)) := by
      dsimp only [φe]; simp only [hlt_e, ↓reduceDIte]
    have hnode_eq : binNodeOfWord h ((ηe e).dropLast ++ [(ηe e).getLast hne_e]) hsnoc_lt =
        binNodeOfWord h (ηe e) hlt_e := by
      congr 1; exact hsnoc.symm
    rw [hnode_eq] at hl_treeY
    have hx_lt : x'.length < h := hm.vertex_subset u hl.left_mem hx'u
    have hy_lt : y'.length < h := hm.vertex_subset v hl.right_mem hy'v
    refine ⟨Sum.inl (binNodeOfWord h x' hx_lt), ⟨x', hx_lt, hx'u, rfl⟩,
      Sum.inl (binNodeOfWord h y' hy_lt), ⟨y', hy_lt, hy'v, rfl⟩, ?_⟩
    rw [hφe_eq]
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hl_treeY
    · exact hl_treeY.symm
  · obtain ⟨w₁, hw₁_lt, hw₁, rfl⟩ := hx
    obtain ⟨w₂, hw₂_lt, hw₂, rfl⟩ := hy
    obtain ⟨K, hK_le, hVK, hK_conn⟩ := hm.connected u hu
    have hrel : Relation.ReflTransGen K.Adj w₁ w₂ := hK_conn.2 w₁ (hVK ▸ hw₁) w₂ (hVK ▸ hw₂)
    have hsub_u := hm.vertex_subset u hu
    induction hrel with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hab hstep ih_step =>
      obtain ⟨f, hlf⟩ := hstep
      have hlf_del : ((binWordTree h).deleteEdges (ηe '' E(F))).IsLink f a b := hlf.mono hK_le
      rw [Graph.deleteEdges_isLink] at hlf_del
      obtain ⟨⟨hf_ne, hf_lt, hf_ends⟩, hf_not_img⟩ := hlf_del
      have ha_u : a ∈ ηv u := hVK ▸ hlf.left_mem
      have hb_u : b ∈ ηv u := hVK ▸ hlf.right_mem
      have ha_lt : a.length < h := hsub_u ha_u
      have hb_lt : b.length < h := hsub_u hb_u
      refine Relation.ReflTransGen.tail (ih_step ha_lt ha_u) ?_
      have hsnoc : f = f.dropLast ++ [f.getLast hf_ne] := (List.dropLast_append_getLast hf_ne).symm
      have hsnoc_lt : (f.dropLast ++ [f.getLast hf_ne]).length < h := hsnoc ▸ hf_lt
      have hl_f := graphN_isLink_binNode_snoc 0 f.dropLast (f.getLast hf_ne) hsnoc_lt
      have hnode_eq : binNodeOfWord h (f.dropLast ++ [f.getLast hf_ne]) hsnoc_lt =
          binNodeOfWord h f hf_lt := by
        congr 1; exact hsnoc.symm
      rw [hnode_eq] at hl_f
      refine ⟨Sum.inl (Sum.inl (binNodeOfWord h f hf_lt)), ?_⟩
      rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
      refine ⟨⟨?_, ?_⟩, ⟨a, ha_lt, ha_u, rfl⟩, ⟨b, hb_lt, hb_u, rfl⟩⟩
      · rcases hf_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hl_f
        · exact hl_f.symm
      · rintro ⟨e, he, heq⟩
        have he_lt : (ηe e).length < h := (hm.edge_mem e he).2
        dsimp only [φe] at heq
        simp only [he_lt, ↓reduceDIte] at heq
        injection heq with h1
        injection h1 with h2
        exact hf_not_img ⟨e, he, binNodeOfWord_inj he_lt hf_lt h2⟩

/-- Every finite simple forest is isomorphic to a minor of `treeY lam` for some `lam ≥ 1`
(Graph Minors III, Section 2, proof of `(2.3)`, page 55:
"But any forest is isomorphic to a minor of one of $Y_1, Y_2, Y_3, \dots$."). -/
theorem exists_treeY_minor_of_forest {α : Type u} {β : Type v}
    (F : Graph α β) (hSimple : F.Simple) (hVF : V(F).Finite) (hEF : E(F).Finite)
    (hNoCirc : ∀ C' ≤ F, ¬ GM09.IsGraphCircuit F C') :
    ∃ lam : ℕ, 1 ≤ lam ∧ IsIsoMinor F (treeY lam) := by
  by_cases hne : Nonempty α
  · obtain ⟨r⟩ := hne
    obtain ⟨h, ηv, ηe, hh, hm, _⟩ := exists_binWordTree_model_of_forest F hSimple hVF hNoCirc r
    obtain ⟨φv, φe, hmY⟩ := isMinorModel_treeY_of_binWordTree hSimple hm
    exact ⟨h + 1, by omega, isIsoMinor_of_isMinorModel F (treeY (h + 1))
      hVF hEF (Set.toFinite _) (Set.toFinite _) φv φe hmY⟩
  · refine ⟨1, le_rfl, ?_⟩
    have hmY : IsMinorModel F (treeY 1) (fun v => (hne ⟨v⟩).elim) (fun _ => Sum.inl (Sum.inr ⟨0, by omega⟩)) :=
      isMinorModel_of_loopless_link
        (fun _ _ u => (hne ⟨u⟩).elim)
        (fun v _ => (hne ⟨v⟩).elim)
        (fun v _ => (hne ⟨v⟩).elim)
        (fun v₁ _ => (hne ⟨v₁⟩).elim)
        (fun e₁ he₁ => by
          obtain ⟨u, _, _⟩ := F.exists_isLink_of_mem_edgeSet he₁
          exact (hne ⟨u⟩).elim)
        (fun _ u _ _ => (hne ⟨u⟩).elim)
        (fun u _ => (hne ⟨u⟩).elim)
    exact isIsoMinor_of_isMinorModel F (treeY 1)
      hVF hEF (Set.toFinite _) (Set.toFinite _) _ _ hmY

end GraphMinor.GM03
