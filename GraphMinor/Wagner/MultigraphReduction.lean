module

public import GraphMinor.GM16.Defs
public import GraphMinor.Planar.Defs
public import GraphMinor.HP25.Web
import GraphMinor.GM01.Basic
import GraphMinor.GM05.MinorTransfer
import GraphMinor.GM16.Section2
import GraphMinor.Minor.Basic
public import GraphMinor.Wagner.PlanarBridge
import GraphMinor.Wagner.CliqueSumMinor

/-!
# Multigraph and Separation Clique-Sum Reductions for Wagner's Theorem

This file reduces the "only if" direction of Wagner's theorem (`GraphMinor.GM16.theorem_1_2_proof`) from
arbitrary finite multigraphs `G : Graph α β` to finite simple graphs `K : SimpleGraph (Fin N)` on
`N ≥ 5` vertices:

1. `hasTreeStructureOver_of_simple_verts`: eliminates loops (via 1-clique-sums with a single-loop
   planar graph) and parallel edges (via 2-clique-sums with a 3-edge dipole planar graph) by strong
   induction on `E(G).ncard`, without changing `V(G)`.
2. `hasTreeStructureOver_of_ncard_le_four`: deduces that every finite multigraph on at most `4`
   vertices has a tree-structure over planar graphs and `V_8`.
3. `exists_simple_torsos_of_sep`: decomposes a finite simple graph `G` along a vertex
   separation `(V₁, V₂)` of order `(V₁ ∩ V₂).ncard ≤ 3` via two clique-sums (splitting off a
   multigraph on `V₁ ∩ V₂` of order `≤ 3`) into two simple graphs `G₁, G₂` isomorphic to the
   simple torsos on `V₁` and `V₂`.
4. `hasTreeStructureOver_of_finSimple_step`: combines these reductions with a bijection
   `Fin N ≃ V(G)` to reduce the "only if" direction to the `SimpleGraph (Fin N)` core (`N ≥ 5`).
-/

public section

namespace GraphMinor.Wagner

open Set Function Graph SimpleGraph

variable {α : Type*} {β : Type*}

/-- The base class of Graph Minors XVI, (1.2): graphs on `α` and `β ⊕ ℕ` that are either planar
or isomorphic to `V_8`. -/
@[expose] def WagnerClass (α : Type*) (β : Type*) : Set (Graph α (β ⊕ ℕ)) :=
  {H : Graph α (β ⊕ ℕ) | IsPlanar H ∨ Nonempty (Iso H GM16.wagnerGraphV8)}

/-- `K : SimpleGraph γ` contains `K_5` as a minor: five pairwise disjoint nonempty connected
vertex subsets with an edge of `K` between every pair of distinct subsets. -/
@[expose] def HasK5MinorSimple {γ : Type*} (K : SimpleGraph γ) : Prop :=
  ∃ B : Fin 5 → Set γ,
    (∀ i, (B i).Nonempty) ∧
    (∀ i, (K.induce (B i)).Preconnected) ∧
    (∀ ⦃i j⦄, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ ⦃i j⦄, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, K.Adj x y)

/-- The simple torso of `K : SimpleGraph (Fin N)` on `A` across `S`: the induced subgraph on `A`
with all pairs of distinct vertices in `A ∩ S` made adjacent. -/
@[expose] def torsoOn {N : ℕ} (K : SimpleGraph (Fin N)) (A S : Finset (Fin N)) :
    SimpleGraph {x : Fin N // x ∈ A} where
  Adj x y := x ≠ y ∧ (K.Adj x.1 y.1 ∨ (x.1 ∈ S ∧ y.1 ∈ S))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp (fun ha => ha.symm) (fun hs => ⟨hs.2, hs.1⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-! ### Helper Lemmas on `subgraphOfVE` and Minor Monotonicity -/

private theorem isIsoMinor_of_le_right {α' β' γ' δ' : Type*} {L : Graph α' β'}
    {H G : Graph γ' δ'} (hm : IsIsoMinor L H) (hle : H ≤ G) : IsIsoMinor L G := by
  rcases hm with ⟨G', hG'H, C, hC, hiso⟩
  exact ⟨G', hG'H.trans hle, C, hC, hiso⟩

private theorem subgraphOfVE_isLink {β' : Type*} (G₀ : Graph α β') (W : Set α) (F : Set β')
    (e : β') (x y : α) :
    (GM16.subgraphOfVE G₀ W F).IsLink e x y ↔ e ∈ F ∧ G₀.IsLink e x y ∧ x ∈ W ∧ y ∈ W := by
  simp [GM16.subgraphOfVE]

private theorem subgraphOfVE_self {β' : Type*} (G₀ : Graph α β') :
    GM16.subgraphOfVE G₀ V(G₀) E(G₀) = G₀ := by
  ext e x y
  · rfl
  · rw [subgraphOfVE_isLink]
    exact ⟨fun h => h.2.1, fun h => ⟨h.edge_mem, h, h.left_mem, h.right_mem⟩⟩

/-! ### Equivalence of `HasK5MinorSimple` and `IsIsoMinor (completeGraph 5)` -/

private theorem walk_toSubgraph_of_induce_walk {γ : Type*} {K : SimpleGraph γ} {X : Set γ}
    (S : (⊤ : SimpleGraph γ).Subgraph)
    (hverts : S.verts = X)
    (hadj : ∀ ⦃a b : γ⦄, a ∈ X → b ∈ X → K.Adj a b → S.Adj a b)
    {u v : X} (w : (K.induce X).Walk u v) :
    ∃ p : (⊤ : SimpleGraph γ).Walk u.1 v.1, p.toSubgraph ≤ S := by
  induction w with
  | @nil u =>
    refine ⟨.nil, ?_⟩
    rw [Walk.toSubgraph, SimpleGraph.singletonSubgraph_le_iff, hverts]
    exact u.2
  | @cons a b c hab _ ih =>
    obtain ⟨p, hp⟩ := ih
    have habK : K.Adj a.1 b.1 := hab
    have habT : (⊤ : SimpleGraph γ).Adj a.1 b.1 := habK.ne
    refine ⟨.cons habT p, ?_⟩
    rw [Walk.toSubgraph, sup_le_iff, SimpleGraph.subgraphOfAdj_le_iff]
    exact ⟨hadj a.2 b.2 habK, hp⟩

/-- On a finite vertex type, `HasK5MinorSimple K` is equivalent to
`IsIsoMinor (GM16.completeGraph 5) (Graph.ofSimpleGraph K)`. -/
theorem hasK5MinorSimple_iff_isIsoMinor {γ : Type*} [Finite γ] (K : SimpleGraph γ) :
    HasK5MinorSimple K ↔ IsIsoMinor (GM16.completeGraph 5) (Graph.ofSimpleGraph K) := by
  classical
  rw [GM01.ofSimpleGraph_eq_toGraph K, completeGraph_eq_toGraph_top 5]
  constructor
  · rintro ⟨B, hne, hpre, hdisj, hadj⟩
    let S : Fin 5 → (⊤ : SimpleGraph γ).Subgraph := fun i =>
      { verts := B i
        Adj := fun x y => x ∈ B i ∧ y ∈ B i ∧ K.Adj x y
        adj_sub := fun h => h.2.2.ne
        edge_vert := fun h => h.1
        symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ }
    refine GM01.isIsoMinor_toGraph_of_connected_subgraphs finite_univ finite_univ S ?_ ?_ ?_ ?_
    · intro i _
      exact ⟨fun _ _ => trivial, fun _ _ h => by simpa using h.2.2⟩
    · intro i _
      rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
      refine ⟨hne i, fun {x y} hx hy => ?_⟩
      obtain ⟨w⟩ := hpre i ⟨x, hx⟩ ⟨y, hy⟩
      exact walk_toSubgraph_of_induce_walk (S i) rfl (fun a b ha hb h => ⟨ha, hb, h⟩) w
    · intro i _ j _ hij
      exact hdisj hij
    · intro i j hij
      obtain ⟨x, hx, y, hy, hxy⟩ := hadj hij.ne
      exact ⟨x, hx, y, hy, by simpa using hxy⟩
  · intro hm
    let G₀ := GM01.toGraph (SimpleGraph.toSubgraph K le_top)
    have hV₀ : V(G₀).Finite := finite_univ
    have hE₀ : E(G₀).Finite := GM01.finite_edgeSet_of_finite_verts finite_univ
    have hm' : IsIsoMinor (GM16.completeGraph 5) (GM16.liftEdgeInl G₀) := by
      rw [completeGraph_eq_toGraph_top 5]
      exact Iso.isIsoMinor_right hm (GM16.iso_liftEdgeInl G₀)
    have hE' : E(GM16.liftEdgeInl G₀).Finite := hE₀.image Sum.inl
    have : Nonempty (Sym2 γ ⊕ ℕ) := ⟨Sum.inr 0⟩
    obtain ⟨ηv, ηe, hmodel⟩ :=
      exists_isMinorModel_of_isIsoMinor (G := GM16.liftEdgeInl G₀) hV₀ hE' hm'
    refine ⟨ηv, fun i => hmodel.vertex_nonempty i trivial, ?_,
      fun i j hij => hmodel.vertex_disjoint i trivial j trivial hij, ?_⟩
    · intro i ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨B, hB_le, hVB, hB_conn⟩ := hmodel.connected i trivial
      have hB_le' : B ≤ GM16.liftEdgeInl G₀ := hB_le.trans Graph.deleteEdges_le
      have hwalk := hB_conn.2 x (hVB.symm ▸ hx) y (hVB.symm ▸ hy)
      have haux : ∀ {a b : γ}, Relation.ReflTransGen B.Adj a b →
          (ha : a ∈ ηv i) → (hb : b ∈ ηv i) →
          (K.induce (ηv i)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
        intro a b hw
        induction hw using Relation.ReflTransGen.head_induction_on with
        | refl => intro _ _; exact Reachable.rfl
        | @head u w huw _ ih =>
          intro hu hb
          obtain ⟨e, hlB⟩ := huw
          have hw_mem : w ∈ ηv i := hVB ▸ hlB.right_mem
          obtain ⟨e₀, _, hlG₀⟩ := hB_le'.2 hlB
          have hadjK : K.Adj u w := by simpa [G₀] using hlG₀.2
          exact (Adj.reachable (G := K.induce (ηv i)) (u := ⟨u, hu⟩) (v := ⟨w, hw_mem⟩)
            hadjK).trans (ih hw_mem hb)
      exact haux hwalk hx hy
    · intro i j hij
      let e : Sym2 (Fin 5) := s(i, j)
      have he_link : (GM16.completeGraph 5).IsLink e i j := ⟨hij, rfl⟩
      obtain ⟨x, hx, hxe⟩ := (hmodel.inc_iff i trivial e he_link.edge_mem).mp he_link.inc_left
      obtain ⟨y, hy, hye⟩ := (hmodel.inc_iff j trivial e he_link.edge_mem).mp he_link.inc_right
      have hxy : x ≠ y := fun h =>
        Set.disjoint_left.mp (hmodel.vertex_disjoint i trivial j trivial hij) hx (h ▸ hy)
      have hother : y = hxe.other := hye.eq_of_isLink_of_ne_left hxe.isLink_other hxy.symm
      have hlink' : (GM16.liftEdgeInl G₀).IsLink (ηe e) x y := hother.symm ▸ hxe.isLink_other
      obtain ⟨e₀, _, hlG₀⟩ := hlink'
      exact ⟨x, hx, y, hy, by simpa [G₀] using hlG₀.2⟩

/-- If `G` is a simple graph (`IsSimpleGraphRep G`) and `eV : γ ≃ V(G)` matches `K : SimpleGraph γ`
with the adjacency of `G`, then `Graph.ofSimpleGraph K` is isomorphic to `G`. -/
theorem nonempty_iso_ofSimpleGraph_of_equiv {γ β' : Type*} {K : SimpleGraph γ} {G : Graph α β'}
    (hSimple : IsSimpleGraphRep G) (eV : γ ≃ V(G))
    (hadj : ∀ i j : γ, K.Adj i j ↔ i ≠ j ∧ G.Adj (eV i).1 (eV j).1) :
    Nonempty (Iso (Graph.ofSimpleGraph K) G) := by
  classical
  rw [GM01.ofSimpleGraph_eq_toGraph K]
  let f : γ → α := fun i => (eV i).1
  have hf_inj : Function.Injective f := Subtype.val_injective.comp eV.injective
  have himg : Sym2.map f '' E(GM01.toGraph (SimpleGraph.toSubgraph K le_top)) =
      E(GM01.toGraph (GM05.simpleShadow G)) := by
    ext e
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      induction e₀ using Sym2.ind with
      | _ i j =>
        have hKij : K.Adj i j := by simpa using he₀
        obtain ⟨hij, hGij⟩ := (hadj i j).mp hKij
        show s(f i, f j) ∈ (GM05.simpleShadow G).edgeSet
        exact ⟨hf_inj.ne hij, hGij⟩
    · intro he
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨huv, hGuv⟩ : u ≠ v ∧ G.Adj u v := he
        have hu : u ∈ V(G) := hGuv.left_mem
        have hv : v ∈ V(G) := hGuv.right_mem
        let i := eV.symm ⟨u, hu⟩
        let j := eV.symm ⟨v, hv⟩
        have hfi : f i = u := congrArg Subtype.val (eV.apply_symm_apply ⟨u, hu⟩)
        have hfj : f j = v := congrArg Subtype.val (eV.apply_symm_apply ⟨v, hv⟩)
        have hij : i ≠ j := fun h => huv (hfi ▸ hfj ▸ congrArg f h)
        have hKij : K.Adj i j := (hadj i j).mpr ⟨hij, by change G.Adj (f i) (f j); rwa [hfi, hfj]⟩
        refine ⟨s(i, j), by simpa using hKij, ?_⟩
        change s(f i, f j) = s(u, v)
        rw [hfi, hfj]
  let iso₁ : Iso (GM01.toGraph (SimpleGraph.toSubgraph K le_top))
      (GM01.toGraph (GM05.simpleShadow G)) :=
    { vertexEquiv := (Equiv.Set.univ γ).trans eV
      edgeEquiv :=
        (Equiv.Set.image (Sym2.map f) _ (Sym2.map.injective hf_inj)).trans (Set.equivOfEq himg)
      isLink_iff := fun ⟨e, he⟩ ⟨i, _⟩ ⟨j, _⟩ => by
        change (e = s(i, j) ∧ K.Adj i j) ↔
          Sym2.map f e = s(f i, f j) ∧ f i ≠ f j ∧ G.Adj (f i) (f j)
        constructor
        · rintro ⟨rfl, hKij⟩
          obtain ⟨hij, hGij⟩ := (hadj i j).mp hKij
          exact ⟨rfl, hf_inj.ne hij, hGij⟩
        · rintro ⟨hef, hne, hGij⟩
          have he_eq : e = s(i, j) := Sym2.map.injective hf_inj (by simpa using hef)
          exact ⟨he_eq, (hadj i j).mpr ⟨ fun h => hne (congrArg f h), hGij ⟩⟩ }
  exact ⟨iso₁.trans (isoToGraphSimpleShadow G hSimple).symm⟩

/-! ### Part 1: Loop and Parallel-Edge Reductions -/

/-- If every finite simple graph `H : Graph α (β ⊕ ℕ)` with `V(H) = V(G)` and no `K_5` minor has a
tree-structure over `WagnerClass α β`, then the finite multigraph `G` itself does. -/
theorem hasTreeStructureOver_of_simple_verts {G : Graph α (β ⊕ ℕ)}
    (hEG : E(G).Finite)
    (hnoK5 : ¬ IsIsoMinor (GM16.completeGraph 5) G)
    (hsimple : ∀ H : Graph α (β ⊕ ℕ), V(H) = V(G) → E(H).Finite → IsSimpleGraphRep H →
      ¬ IsIsoMinor (GM16.completeGraph 5) H → GM16.HasTreeStructureOver (WagnerClass α β) H) :
    GM16.HasTreeStructureOver (WagnerClass α β) G := by
  classical
  have hmain : ∀ (m : ℕ) (G' : Graph α (β ⊕ ℕ)),
      V(G') = V(G) → E(G').Finite → E(G').ncard = m →
      ¬ IsIsoMinor (GM16.completeGraph 5) G' →
      GM16.HasTreeStructureOver (WagnerClass α β) G' := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro G' hVG' hEG' hm_eq hnoK5'
      by_cases hSimp : IsSimpleGraphRep G'
      · exact hsimple G' hVG' hEG' hSimp hnoK5'
      · by_cases hHasLoop : ∃ e x, G'.IsLoopAt e x
        · obtain ⟨e, x, hloop⟩ := hHasLoop
          have hlink : G'.IsLink e x x := hloop
          have hx : x ∈ V(G') := hlink.left_mem
          have he : e ∈ E(G') := hlink.edge_mem
          let H₁ := GM16.subgraphOfVE G' V(G') (E(G') \ {e})
          let H₂ := GM16.subgraphOfVE G' {x} {e}
          let K := GM16.subgraphOfVE G' {x} ∅
          have hF₁ : ∀ d ∈ E(G') \ {e}, ∃ u ∈ V(G'), ∃ v ∈ V(G'), G'.IsLink d u v := by
            intro d hd
            obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet hd.1
            exact ⟨u, hl.left_mem, v, hl.right_mem, hl⟩
          have hF₂ : ∀ d ∈ ({e} : Set (β ⊕ ℕ)), ∃ u ∈ ({x} : Set α), ∃ v ∈ ({x} : Set α),
              G'.IsLink d u v := by
            intro d hd
            rw [mem_singleton_iff] at hd
            exact ⟨x, rfl, x, rfl, hd ▸ hlink⟩
          have hFK : ∀ d ∈ (∅ : Set (β ⊕ ℕ)), ∃ u ∈ ({x} : Set α), ∃ v ∈ ({x} : Set α),
              G'.IsLink d u v := fun _ hd => hd.elim
          have hsepG : GM06.IsGraphSeparation G' H₁ H₂ := by
            have hs := GM16.isGraphSeparation_subgraphOfVE (G₀ := G')
              subset_rfl subset_rfl (singleton_subset_iff.mpr hx)
              (fun d hd => by
                obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet hd
                exact ⟨u, hl.left_mem, v, hl.right_mem, hl⟩)
              hF₁ hF₂ (union_eq_self_of_subset_right (singleton_subset_iff.mpr hx))
              (sdiff_union_of_subset (singleton_subset_iff.mpr he)) disjoint_sdiff_left
            rwa [subgraphOfVE_self G'] at hs
          have hsep₁ : GM06.IsGraphSeparation H₁ H₁ K :=
            GM16.isGraphSeparation_subgraphOfVE subset_rfl subset_rfl
              (singleton_subset_iff.mpr hx) hF₁ hF₁ hFK
              (union_eq_self_of_subset_right (singleton_subset_iff.mpr hx))
              (union_empty _) (Set.disjoint_empty _)
          have hsep₂ : GM06.IsGraphSeparation H₂ H₂ K :=
            GM16.isGraphSeparation_subgraphOfVE (singleton_subset_iff.mpr hx)
              (singleton_subset_iff.mpr hx) (singleton_subset_iff.mpr hx) hF₂ hF₂ hFK
              (union_self _) (union_empty _) (Set.disjoint_empty _)
          have hinter : V(H₁) ∩ V(H₂) = {x} :=
            inter_eq_self_of_subset_right (singleton_subset_iff.mpr hx)
          have hK_comp : GM16.IsCompleteGraphOn K (V(H₁) ∩ V(H₂)) := by
            rw [hinter]
            refine ⟨rfl, ?_, ?_⟩
            · intro d u hloopK
              exact ((subgraphOfVE_isLink G' {x} ∅ d u u).mp hloopK).1
            · intro u hu v hv huv
              exact (huv (hu.trans hv.symm)).elim
          have hsum : GM16.IsCliqueSum G' H₁ H₂ := ⟨H₁, H₂, K, hsepG, hK_comp, hsep₁, hsep₂⟩
          have hPH₂ : IsPlanar H₂ := by
            refine isPlanar_of_single_loop rfl (GM16.edgeSet_subgraphOfVE hF₂) ?_
            exact (subgraphOfVE_isLink G' {x} {e} e x x).mpr ⟨rfl, hlink, rfl, rfl⟩
          have hEH₁ : E(H₁) = E(G') \ {e} := GM16.edgeSet_subgraphOfVE hF₁
          have hEH₁_fin : E(H₁).Finite := hEG'.subset (hEH₁ ▸ sdiff_subset)
          have hlt : E(H₁).ncard < m := by
            rw [← hm_eq, hEH₁]
            exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h he).2 rfl⟩ hEG'
          have hnoK5_H₁ : ¬ IsIsoMinor (GM16.completeGraph 5) H₁ := fun hm₁ =>
            hnoK5' (isIsoMinor_of_le_right hm₁ (GM16.subgraphOfVE_le subset_rfl))
          exact .cliqueSum hsum (ih _ hlt H₁ hVG' hEH₁_fin rfl hnoK5_H₁) (.base (Or.inl hPH₂))
        · push Not at hHasLoop
          have hPar : ∃ e₁ e₂ x y, e₁ ≠ e₂ ∧ G'.IsLink e₁ x y ∧ G'.IsLink e₂ x y := by
            by_contra hno
            push Not at hno
            exact hSimp ⟨hHasLoop, fun e₁ e₂ x y h1 h2 =>
              by_contra fun hne => hno e₁ e₂ x y hne h1 h2⟩
          obtain ⟨e₁, e₂, x, y, he₁₂, hl₁, hl₂⟩ := hPar
          have hxy : x ≠ y := fun h => hHasLoop e₁ x (h ▸ hl₁)
          have hx : x ∈ V(G') := hl₁.left_mem
          have hy : y ∈ V(G') := hl₁.right_mem
          have he₁ : e₁ ∈ E(G') := hl₁.edge_mem
          have he₂ : e₂ ∈ E(G') := hl₂.edge_mem
          have hN_fin : (Sum.inr ⁻¹' E(G') : Set ℕ).Finite :=
            hEG'.preimage Sum.inr_injective.injOn
          let f : β ⊕ ℕ := Sum.inr (hN_fin.toFinset.sup id + 1)
          have hf_notG' : f ∉ E(G') := by
            intro hmem
            have hn : hN_fin.toFinset.sup id + 1 ∈ hN_fin.toFinset :=
              hN_fin.mem_toFinset.mpr hmem
            have hle : hN_fin.toFinset.sup id + 1 ≤ hN_fin.toFinset.sup id :=
              Finset.le_sup (f := id) hn
            omega
          have he₁f : e₁ ≠ f := fun h => hf_notG' (h ▸ he₁)
          have he₂f : e₂ ≠ f := fun h => hf_notG' (h ▸ he₂)
          let G_full : Graph α (β ⊕ ℕ) :=
            { vertexSet := V(G')
              edgeSet := E(G') ∪ {f}
              IsLink := fun d u v =>
                G'.IsLink d u v ∨ (d = f ∧ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)))
              isLink_symm := fun d _ => ⟨by
                rintro u v (h | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
                · exact Or.inl h.symm
                · exact Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
                · exact Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
              eq_or_eq_of_isLink_of_isLink := by
                rintro d u v z w (h1 | ⟨rfl, h1⟩) (h2 | ⟨hd2, h2⟩)
                · exact G'.eq_or_eq_of_isLink_of_isLink h1 h2
                · exact (hf_notG' (hd2 ▸ h1.edge_mem)).elim
                · exact (hf_notG' h2.edge_mem).elim
                · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
                    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Or.inl rfl
                  · exact Or.inr rfl
                  · exact Or.inr rfl
                  · exact Or.inl rfl
              edge_mem_iff_exists_isLink := fun d => by
                constructor
                · rintro (hd | rfl)
                  · obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet hd
                    exact ⟨u, v, Or.inl hl⟩
                  · exact ⟨x, y, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
                · rintro ⟨u, v, h | ⟨rfl, _⟩⟩
                  · exact Or.inl h.edge_mem
                  · exact Or.inr rfl
              left_mem_of_isLink := by
                rintro d u v (h | ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩)
                · exact h.left_mem
                · exact hx
                · exact hy }
          have hG'_eq : GM16.subgraphOfVE G_full V(G') E(G') = G' := by
            ext d u v
            · rfl
            · rw [subgraphOfVE_isLink]
              constructor
              · rintro ⟨hd, h | ⟨rfl, _⟩, _, _⟩
                · exact h
                · exact (hf_notG' hd).elim
              · intro h
                exact ⟨h.edge_mem, Or.inl h, h.left_mem, h.right_mem⟩
          let H₁ := GM16.subgraphOfVE G_full V(G') (E(G') \ {e₁, e₂})
          let H₂ := GM16.subgraphOfVE G_full {x, y} {e₁, e₂}
          let K := GM16.subgraphOfVE G_full {x, y} {f}
          let G₁ := GM16.subgraphOfVE G_full V(G') ((E(G') \ {e₁, e₂}) ∪ {f})
          let G₂ := GM16.subgraphOfVE G_full {x, y} {e₁, e₂, f}
          have hxy_sub : ({x, y} : Set α) ⊆ V(G') := by
            rintro z (rfl | rfl) <;> assumption
          have hFG : ∀ d ∈ E(G'), ∃ u ∈ V(G'), ∃ v ∈ V(G'), G_full.IsLink d u v := by
            intro d hd
            obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet hd
            exact ⟨u, hl.left_mem, v, hl.right_mem, Or.inl hl⟩
          have hFH₁ : ∀ d ∈ E(G') \ {e₁, e₂}, ∃ u ∈ V(G'), ∃ v ∈ V(G'), G_full.IsLink d u v :=
            fun d hd => hFG d hd.1
          have hFH₂ : ∀ d ∈ ({e₁, e₂} : Set (β ⊕ ℕ)),
              ∃ u ∈ ({x, y} : Set α), ∃ v ∈ ({x, y} : Set α), G_full.IsLink d u v := by
            rintro d (rfl | rfl)
            · exact ⟨x, by simp, y, by simp, Or.inl hl₁⟩
            · exact ⟨x, by simp, y, by simp, Or.inl hl₂⟩
          have hFK : ∀ d ∈ ({f} : Set (β ⊕ ℕ)),
              ∃ u ∈ ({x, y} : Set α), ∃ v ∈ ({x, y} : Set α), G_full.IsLink d u v := by
            rintro d rfl
            exact ⟨x, by simp, y, by simp, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
          have hFG₁ : ∀ d ∈ (E(G') \ {e₁, e₂}) ∪ {f},
              ∃ u ∈ V(G'), ∃ v ∈ V(G'), G_full.IsLink d u v := by
            rintro d (hd | rfl)
            · exact hFH₁ d hd
            · exact ⟨x, hx, y, hy, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
          have hFG₂ : ∀ d ∈ ({e₁, e₂, f} : Set (β ⊕ ℕ)),
              ∃ u ∈ ({x, y} : Set α), ∃ v ∈ ({x, y} : Set α), G_full.IsLink d u v := by
            rintro d (rfl | rfl | rfl)
            · exact ⟨x, by simp, y, by simp, Or.inl hl₁⟩
            · exact ⟨x, by simp, y, by simp, Or.inl hl₂⟩
            · exact ⟨x, by simp, y, by simp, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
          have he₁₂_sub : ({e₁, e₂} : Set (β ⊕ ℕ)) ⊆ E(G') := by
            rintro d (rfl | rfl) <;> assumption
          have hsepG : GM06.IsGraphSeparation G' H₁ H₂ := by
            have hs := GM16.isGraphSeparation_subgraphOfVE (G₀ := G_full)
              subset_rfl subset_rfl hxy_sub hFG hFH₁ hFH₂
              (union_eq_self_of_subset_right hxy_sub)
              (sdiff_union_of_subset he₁₂_sub) disjoint_sdiff_left
            rwa [hG'_eq] at hs
          have hdisj₁K : Disjoint (E(G') \ {e₁, e₂}) ({f} : Set (β ⊕ ℕ)) :=
            disjoint_singleton_right.mpr fun h => hf_notG' h.1
          have hdisj₂K : Disjoint ({e₁, e₂} : Set (β ⊕ ℕ)) ({f} : Set (β ⊕ ℕ)) := by
            rw [disjoint_singleton_right]
            rintro (h | h)
            · exact he₁f h.symm
            · exact he₂f h.symm
          have hF₂_union : ({e₁, e₂} : Set (β ⊕ ℕ)) ∪ {f} = {e₁, e₂, f} := by
            ext d; simp; tauto
          have hsep₁ : GM06.IsGraphSeparation G₁ H₁ K :=
            GM16.isGraphSeparation_subgraphOfVE subset_rfl subset_rfl hxy_sub
              hFG₁ hFH₁ hFK (union_eq_self_of_subset_right hxy_sub) rfl hdisj₁K
          have hsep₂ : GM06.IsGraphSeparation G₂ H₂ K :=
            GM16.isGraphSeparation_subgraphOfVE hxy_sub hxy_sub hxy_sub
              hFG₂ hFH₂ hFK (union_self _) hF₂_union hdisj₂K
          have hK_comp : GM16.IsCompleteGraphOn K (V(H₁) ∩ V(H₂)) := by
            rw [show V(H₁) ∩ V(H₂) = {x, y} from inter_eq_self_of_subset_right hxy_sub]
            refine ⟨rfl, ?_, ?_⟩
            · intro d u hloopK
              obtain ⟨hd, hfl, _, _⟩ := (subgraphOfVE_isLink G_full {x, y} {f} d u u).mp hloopK
              rw [mem_singleton_iff] at hd
              subst hd
              rcases hfl with hlG' | ⟨_, ⟨rfl, hxy'⟩ | ⟨rfl, hyx'⟩⟩
              · exact hf_notG' hlG'.edge_mem
              · exact hxy hxy'
              · exact hxy hyx'.symm
            · intro u hu v hv huv
              refine ⟨f, ?_, fun d hd => ?_⟩
              · dsimp only
                rw [subgraphOfVE_isLink]
                refine ⟨rfl, Or.inr ⟨rfl, ?_⟩, hu, hv⟩
                rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
                · exact (huv rfl).elim
                · exact Or.inl ⟨rfl, rfl⟩
                · exact Or.inr ⟨rfl, rfl⟩
                · exact (huv rfl).elim
              · exact ((subgraphOfVE_isLink G_full {x, y} {f} d u v).mp hd).1
          have hsum : GM16.IsCliqueSum G' G₁ G₂ := ⟨H₁, H₂, K, hsepG, hK_comp, hsep₁, hsep₂⟩
          have hPG₂ : IsPlanar G₂ := by
            refine isPlanar_of_three_parallel hxy he₁₂ he₁f he₂f rfl
              (GM16.edgeSet_subgraphOfVE hFG₂) ?_ ?_ ?_
            · exact (subgraphOfVE_isLink G_full {x, y} {e₁, e₂, f} e₁ x y).mpr
                ⟨by simp, Or.inl hl₁, by simp, by simp⟩
            · exact (subgraphOfVE_isLink G_full {x, y} {e₁, e₂, f} e₂ x y).mpr
                ⟨by simp, Or.inl hl₂, by simp, by simp⟩
            · exact (subgraphOfVE_isLink G_full {x, y} {e₁, e₂, f} f x y).mpr
                ⟨by simp, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, by simp, by simp⟩
          -- `G₁` is isomorphic to `G'.deleteEdges {e₂}` (`GM16.subgraphOfVE G' V(G') (E(G') \ {e₂})`)
          let H_keep := GM16.subgraphOfVE G' V(G') (E(G') \ {e₂})
          have hFkeep : ∀ d ∈ E(G') \ {e₂}, ∃ u ∈ V(G'), ∃ v ∈ V(G'), G'.IsLink d u v :=
            fun d hd => by
              obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet hd.1
              exact ⟨u, hl.left_mem, v, hl.right_mem, hl⟩
          have hEG₁ : E(G₁) = (E(G') \ {e₁, e₂}) ∪ {f} := GM16.edgeSet_subgraphOfVE hFG₁
          have hEHkeep : E(H_keep) = E(G') \ {e₂} := GM16.edgeSet_subgraphOfVE hFkeep
          let edgeMap : E(G₁) → E(H_keep) := fun ⟨d, hd⟩ =>
            if hdf : d = f then
              ⟨e₁, hEHkeep.symm ▸ ⟨he₁, he₁₂⟩⟩
            else
              ⟨d, by
                rw [hEG₁] at hd
                rcases hd with ⟨hdG', hne₁₂⟩ | rfl
                · rw [hEHkeep]
                  exact ⟨hdG', fun h => hne₁₂ (Or.inr h)⟩
                · exact (hdf rfl).elim⟩
          let edgeInv : E(H_keep) → E(G₁) := fun ⟨d, hd⟩ =>
            if hde₁ : d = e₁ then
              ⟨f, hEG₁.symm ▸ Or.inr rfl⟩
            else
              ⟨d, by
                rw [hEHkeep] at hd
                rw [hEG₁]
                exact Or.inl ⟨hd.1, by rintro (rfl | rfl); exact hde₁ rfl; exact hd.2 rfl⟩⟩
          let isoG₁ : Iso G₁ H_keep :=
            { vertexEquiv := Equiv.refl V(G')
              edgeEquiv :=
                { toFun := edgeMap
                  invFun := edgeInv
                  left_inv := fun ⟨d, hd⟩ => by
                    ext
                    by_cases hdf : d = f
                    · subst hdf
                      simp [edgeMap, edgeInv]
                    · have hde₁ : d ≠ e₁ := by
                        rw [hEG₁] at hd
                        rcases hd with ⟨_, hne⟩ | rfl
                        · exact fun h => hne (Or.inl h)
                        · exact (hdf rfl).elim
                      simp [edgeMap, edgeInv, hdf, hde₁]
                  right_inv := fun ⟨d, hd⟩ => by
                    ext
                    by_cases hde₁ : d = e₁
                    · subst hde₁
                      simp [edgeMap, edgeInv]
                    · have hdf : d ≠ f := by
                        rw [hEHkeep] at hd
                        exact fun h => hf_notG' (h ▸ hd.1)
                      simp [edgeMap, edgeInv, hde₁, hdf] }
              isLink_iff := fun ⟨d, hd⟩ ⟨u, hu⟩ ⟨v, hv⟩ => by
                change G₁.IsLink d u v ↔ H_keep.IsLink (edgeMap ⟨d, hd⟩).1 u v
                by_cases hdf : d = f
                · subst hdf
                  simp only [edgeMap, ↓reduceDIte]
                  rw [subgraphOfVE_isLink, subgraphOfVE_isLink]
                  constructor
                  · rintro ⟨_, hlG' | ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, _, _⟩
                    · exact (hf_notG' hlG'.edge_mem).elim
                    · exact ⟨⟨he₁, he₁₂⟩, hl₁, hu, hv⟩
                    · exact ⟨⟨he₁, he₁₂⟩, hl₁.symm, hu, hv⟩
                  · rintro ⟨_, hl_e₁, _, _⟩
                    rcases G'.eq_or_eq_of_isLink_of_isLink hl_e₁ hl₁ with rfl | rfl
                    · have hv_eq : v = y := hl_e₁.right_unique hl₁
                      subst hv_eq
                      exact ⟨by simp, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, hu, hv⟩
                    · have hv_eq : v = x := hl_e₁.right_unique hl₁.symm
                      subst hv_eq
                      exact ⟨by simp, Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, hu, hv⟩
                · have hmem : d ∈ E(G') \ {e₁, e₂} := by
                    rw [hEG₁] at hd
                    exact hd.resolve_right hdf
                  simp only [edgeMap, hdf, ↓reduceDIte]
                  rw [subgraphOfVE_isLink, subgraphOfVE_isLink]
                  constructor
                  · rintro ⟨_, hlG' | ⟨rfl, _⟩, _, _⟩
                    · exact ⟨⟨hmem.1, fun h => hmem.2 (Or.inr h)⟩, hlG', hu, hv⟩
                    · exact (hdf rfl).elim
                  · rintro ⟨_, hlG', _, _⟩
                    exact ⟨Or.inl hmem, Or.inl hlG', hu, hv⟩ }
          have hEG₁_fin : E(G₁).Finite := by
            rw [hEG₁]
            exact (hEG'.subset sdiff_subset).union (finite_singleton f)
          have hncard_eq : E(G₁).ncard = E(H_keep).ncard := by
            have : Nat.card E(G₁) = Nat.card E(H_keep) := Nat.card_congr isoG₁.edgeEquiv
            simpa only [Nat.card_coe_set_eq] using this
          have hlt : E(G₁).ncard < m := by
            rw [hncard_eq, ← hm_eq, hEHkeep]
            exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h he₂).2 rfl⟩ hEG'
          have hnoK5_G₁ : ¬ IsIsoMinor (GM16.completeGraph 5) G₁ := fun hm₁ =>
            hnoK5' (isIsoMinor_of_le_right (Iso.isIsoMinor_right hm₁ isoG₁)
              (GM16.subgraphOfVE_le subset_rfl))
          exact .cliqueSum hsum (ih _ hlt G₁ hVG' hEG₁_fin rfl hnoK5_G₁) (.base (Or.inl hPG₂))
  exact hmain E(G).ncard G rfl hEG rfl hnoK5

/-- No finite graph on at most `4` vertices has a `K_5` minor. -/
theorem not_isIsoMinor_completeGraph_five_of_ncard_le_four {β' : Type*} {G : Graph α β'}
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hcard : V(G).ncard ≤ 4) :
    ¬ IsIsoMinor (GM16.completeGraph 5) G := by
  intro hm
  rw [completeGraph_eq_toGraph_top 5, ← GM05.isIsoMinor_simpleShadow_iff finite_univ hVG hEG,
    ← completeGraph_eq_toGraph_top 5] at hm
  have hP : IsPlanar (GM01.toGraph (GM05.simpleShadow G)) :=
    isPlanar_of_simple_ncard_le_four hVG (GM01.finite_edgeSet_of_finite_verts hVG)
      (isSimpleGraphRep_toGraph _) hcard
  exact not_isIsoMinor_completeGraph_five_of_isPlanar hP hm

/-- Every finite multigraph `G : Graph α (β ⊕ ℕ)` on at most `4` vertices has a tree-structure
over `WagnerClass α β`. -/
theorem hasTreeStructureOver_of_ncard_le_four {G : Graph α (β ⊕ ℕ)}
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hcard : V(G).ncard ≤ 4) :
    GM16.HasTreeStructureOver (WagnerClass α β) G := by
  refine hasTreeStructureOver_of_simple_verts hEG
    (not_isIsoMinor_completeGraph_five_of_ncard_le_four hVG hEG hcard) ?_
  intro H hVH hEH hSimp _
  exact .base (Or.inl (isPlanar_of_simple_ncard_le_four (hVH ▸ hVG) hEH hSimp (hVH ▸ hcard)))

/-! ### Part 2: Two-Step Separation Clique-Sum Decomposition for Simple Graphs -/

/-- If `G : Graph α (β ⊕ ℕ)` is a finite simple graph with a vertex separation `(V₁, V₂)` of order
`(V₁ ∩ V₂).ncard ≤ 3`, then there exist finite simple graphs `G₁, G₂` on `V₁, V₂` realizing the
simple torsos across `V₁ ∩ V₂` such that tree-structures for `G₁` and `G₂` yield one for `G`. -/
theorem exists_simple_torsos_of_sep {G : Graph α (β ⊕ ℕ)}
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hSimple : IsSimpleGraphRep G)
    {V₁ V₂ : Set α} (hV₁_sub : V₁ ⊆ V(G)) (hV₂_sub : V₂ ⊆ V(G))
    (hV_union : V₁ ∪ V₂ = V(G)) (hS_card : (V₁ ∩ V₂).ncard ≤ 3)
    (hsep_edges : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂)) :
    ∃ G₁ G₂ : Graph α (β ⊕ ℕ),
      V(G₁) = V₁ ∧ E(G₁).Finite ∧ IsSimpleGraphRep G₁ ∧
      (∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v →
        (G₁.Adj u v ↔ G.Adj u v ∨ (u ∈ V₁ ∩ V₂ ∧ v ∈ V₁ ∩ V₂))) ∧
      V(G₂) = V₂ ∧ E(G₂).Finite ∧ IsSimpleGraphRep G₂ ∧
      (∀ u ∈ V₂, ∀ v ∈ V₂, u ≠ v →
        (G₂.Adj u v ↔ G.Adj u v ∨ (u ∈ V₁ ∩ V₂ ∧ v ∈ V₁ ∩ V₂))) ∧
      (GM16.HasTreeStructureOver (WagnerClass α β) G₁ →
        GM16.HasTreeStructureOver (WagnerClass α β) G₂ →
        GM16.HasTreeStructureOver (WagnerClass α β) G) := by
  classical
  let S : Set α := V₁ ∩ V₂
  have hS_sub : S ⊆ V(G) := inter_subset_left.trans hV₁_sub
  have hS_fin : S.Finite := hVG.subset hS_sub
  let _ : Fintype S := hS_fin.fintype
  have hN_fin : (Sum.inr ⁻¹' E(G) : Set ℕ).Finite := hEG.preimage Sum.inr_injective.injOn
  let B₀ : ℕ := hN_fin.toFinset.sup id + 1
  have hB₀_notMem : ∀ n : ℕ, (Sum.inr (B₀ + n) : β ⊕ ℕ) ∉ E(G) := by
    intro n hmem
    have hn : B₀ + n ∈ hN_fin.toFinset := hN_fin.mem_toFinset.mpr hmem
    have hle : B₀ + n ≤ hN_fin.toFinset.sup id := Finset.le_sup (f := id) hn
    dsimp only [B₀] at hle
    omega
  let enc := Fintype.equivFin (Bool × Sym2 S)
  let freshEdge (b : Bool) (x y : S) : β ⊕ ℕ := Sum.inr (B₀ + (enc (b, s(x, y))).1)
  have hfresh_symm : ∀ b x y, freshEdge b x y = freshEdge b y x := by
    intro b x y; dsimp [freshEdge]; rw [Sym2.eq_swap]
  have hfresh_notMem : ∀ b x y, freshEdge b x y ∉ E(G) := fun _ _ _ => hB₀_notMem _
  have hfresh_inj : ∀ {b₁ b₂ : Bool} {x₁ y₁ x₂ y₂ : S},
      freshEdge b₁ x₁ y₁ = freshEdge b₂ x₂ y₂ ↔ b₁ = b₂ ∧ s(x₁, y₁) = s(x₂, y₂) := by
    intro b₁ b₂ x₁ y₁ x₂ y₂
    constructor
    · intro h
      have h1 : enc (b₁, s(x₁, y₁)) = enc (b₂, s(x₂, y₂)) :=
        Fin.ext (Nat.add_left_cancel (Sum.inr.inj h))
      exact Prod.mk.inj (enc.injective h1)
    · rintro ⟨rfl, h⟩; dsimp [freshEdge]; rw [h]
  let FK (b : Bool) : Set (β ⊕ ℕ) :=
    {e | ∃ (u v : α) (hu : u ∈ S) (hv : v ∈ S), u ≠ v ∧ e = freshEdge b ⟨u, hu⟩ ⟨v, hv⟩}
  let G_full : Graph α (β ⊕ ℕ) :=
    { vertexSet := V(G)
      edgeSet := E(G) ∪ FK false ∪ FK true
      IsLink := fun e u v =>
        G.IsLink e u v ∨
          ∃ (b : Bool) (hu : u ∈ S) (hv : v ∈ S), u ≠ v ∧ e = freshEdge b ⟨u, hu⟩ ⟨v, hv⟩
      isLink_symm := fun e _ => ⟨by
        rintro u v (h | ⟨b, hu, hv, hne, rfl⟩)
        · exact Or.inl h.symm
        · exact Or.inr ⟨b, hv, hu, hne.symm, hfresh_symm b ⟨u, hu⟩ ⟨v, hv⟩⟩⟩
      eq_or_eq_of_isLink_of_isLink := by
        rintro e u v z w (h1 | ⟨b₁, hu, hv, _, rfl⟩) (h2 | ⟨b₂, hz, hw, _, he₂⟩)
        · exact G.eq_or_eq_of_isLink_of_isLink h1 h2
        · exact (hfresh_notMem b₂ ⟨z, hz⟩ ⟨w, hw⟩ (he₂ ▸ h1.edge_mem)).elim
        · exact (hfresh_notMem b₁ ⟨u, hu⟩ ⟨v, hv⟩ h2.edge_mem).elim
        · rcases Sym2.eq_iff.mp (hfresh_inj.mp he₂).2 with ⟨huz, _⟩ | ⟨huw, _⟩
          · exact Or.inl (congrArg Subtype.val huz)
          · exact Or.inr (congrArg Subtype.val huw)
      edge_mem_iff_exists_isLink := fun e => by
        constructor
        · rintro ((heG | ⟨u, v, hu, hv, hne, rfl⟩) | ⟨u, v, hu, hv, hne, rfl⟩)
          · obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet heG
            exact ⟨u, v, Or.inl hl⟩
          · exact ⟨u, v, Or.inr ⟨false, hu, hv, hne, rfl⟩⟩
          · exact ⟨u, v, Or.inr ⟨true, hu, hv, hne, rfl⟩⟩
        · rintro ⟨u, v, h | ⟨b, hu, hv, hne, rfl⟩⟩
          · exact Or.inl (Or.inl h.edge_mem)
          · cases b
            · exact Or.inl (Or.inr ⟨u, v, hu, hv, hne, rfl⟩)
            · exact Or.inr ⟨u, v, hu, hv, hne, rfl⟩
      left_mem_of_isLink := by
        rintro e u v (h | ⟨_, hu, _⟩)
        · exact h.left_mem
        · exact hS_sub hu }
  have hFK_fin : ∀ b : Bool, (FK b).Finite := by
    intro b
    have hsub : FK b ⊆ Set.range (fun p : S × S => freshEdge b p.1 p.2) := by
      rintro _ ⟨u, v, hu, hv, _, rfl⟩
      exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
    exact (Set.finite_range _).subset hsub
  have hFK_disj_G : ∀ b : Bool, Disjoint E(G) (FK b) := by
    intro b
    rw [Set.disjoint_left]
    rintro _ heG ⟨u, v, hu, hv, _, rfl⟩
    exact hfresh_notMem b ⟨u, hu⟩ ⟨v, hv⟩ heG
  have hFK_disj : Disjoint (FK false) (FK true) := by
    rw [Set.disjoint_left]
    rintro _ ⟨u₁, v₁, hu₁, hv₁, _, rfl⟩ ⟨u₂, v₂, hu₂, hv₂, _, heq⟩
    exact Bool.false_ne_true (hfresh_inj.mp heq).1
  -- Partition `E(G)` into `E_S`, `E₁`, `E₂`
  let E_S : Set (β ⊕ ℕ) := {e ∈ E(G) | ∃ x ∈ S, ∃ y ∈ S, G.IsLink e x y}
  let E₁ : Set (β ⊕ ℕ) := {e ∈ E(G) \ E_S | ∃ x ∈ V₁, ∃ y ∈ V₁, G.IsLink e x y}
  let E₂ : Set (β ⊕ ℕ) := {e ∈ E(G) \ E_S | ∃ x ∈ V₂, ∃ y ∈ V₂, G.IsLink e x y}
  have hdisj_E₁_E₂ : Disjoint E₁ E₂ := by
    rw [Set.disjoint_left]
    rintro e ⟨⟨heG, hnotS⟩, x₁, hx₁, y₁, hy₁, hl₁⟩ ⟨_, x₂, hx₂, y₂, hy₂, hl₂⟩
    apply hnotS
    refine ⟨heG, x₁, ⟨hx₁, ?_⟩, y₁, ⟨hy₁, ?_⟩, hl₁⟩
    · rcases G.eq_or_eq_of_isLink_of_isLink hl₁ hl₂ with rfl | rfl <;> assumption
    · rcases G.eq_or_eq_of_isLink_of_isLink hl₁.symm hl₂ with rfl | rfl <;> assumption
  have hdisj_E₁_ES : Disjoint E₁ E_S :=
    Set.disjoint_left.mpr fun _ h1 hS => h1.1.2 hS
  have hdisj_E₂_ES : Disjoint E₂ E_S :=
    Set.disjoint_left.mpr fun _ h2 hS => h2.1.2 hS
  have hE_part : E₁ ∪ (E₂ ∪ E_S) = E(G) := by
    ext e
    constructor
    · rintro (h1 | h2 | hS)
      · exact h1.1.1
      · exact h2.1.1
      · exact hS.1
    · intro heG
      by_cases hS : e ∈ E_S
      · exact Or.inr (Or.inr hS)
      · obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet heG
        rcases hsep_edges e x y hl with ⟨hx₁, hy₁⟩ | ⟨hx₂, hy₂⟩
        · exact Or.inl ⟨⟨heG, hS⟩, x, hx₁, y, hy₁, hl⟩
        · exact Or.inr (Or.inl ⟨⟨heG, hS⟩, x, hx₂, y, hy₂, hl⟩)
  have hG_eq : GM16.subgraphOfVE G_full V(G) E(G) = G := by
    ext e x y
    · rfl
    · rw [subgraphOfVE_isLink]
      constructor
      · rintro ⟨heG, hl | ⟨b, hu, hv, _, rfl⟩, _, _⟩
        · exact hl
        · exact (hfresh_notMem b ⟨x, hu⟩ ⟨y, hv⟩ heG).elim
      · intro hl
        exact ⟨hl.edge_mem, Or.inl hl, hl.left_mem, hl.right_mem⟩
  let H₁ := GM16.subgraphOfVE G_full V₁ E₁
  let H_mid := GM16.subgraphOfVE G_full V₂ (E₂ ∪ E_S)
  let K₁ := GM16.subgraphOfVE G_full S (FK false)
  let G₁ := GM16.subgraphOfVE G_full V₁ (E₁ ∪ FK false)
  let G_mid := GM16.subgraphOfVE G_full V₂ ((E₂ ∪ E_S) ∪ FK false)
  let H₂ := GM16.subgraphOfVE G_full V₂ E₂
  let H_S := GM16.subgraphOfVE G_full S (E_S ∪ FK false)
  let K₂ := GM16.subgraphOfVE G_full S (FK true)
  let G₂ := GM16.subgraphOfVE G_full V₂ (E₂ ∪ FK true)
  let G_S := GM16.subgraphOfVE G_full S ((E_S ∪ FK false) ∪ FK true)
  have hFE₁ : ∀ e ∈ E₁, ∃ x ∈ V₁, ∃ y ∈ V₁, G_full.IsLink e x y := by
    rintro e ⟨_, x, hx, y, hy, hl⟩; exact ⟨x, hx, y, hy, Or.inl hl⟩
  have hFE₂ : ∀ e ∈ E₂, ∃ x ∈ V₂, ∃ y ∈ V₂, G_full.IsLink e x y := by
    rintro e ⟨_, x, hx, y, hy, hl⟩; exact ⟨x, hx, y, hy, Or.inl hl⟩
  have hFES : ∀ e ∈ E_S, ∃ x ∈ S, ∃ y ∈ S, G_full.IsLink e x y := by
    rintro e ⟨_, x, hx, y, hy, hl⟩; exact ⟨x, hx, y, hy, Or.inl hl⟩
  have hFFK : ∀ (b : Bool), ∀ e ∈ FK b, ∃ x ∈ S, ∃ y ∈ S, G_full.IsLink e x y := by
    rintro b _ ⟨u, v, hu, hv, hne, rfl⟩
    exact ⟨u, hu, v, hv, Or.inr ⟨b, hu, hv, hne, rfl⟩⟩
  have hS_V₁ : S ⊆ V₁ := inter_subset_left
  have hS_V₂ : S ⊆ V₂ := inter_subset_right
  have liftW : ∀ {W₁ W₂ : Set α} (hsub : W₁ ⊆ W₂) {F : Set (β ⊕ ℕ)},
      (∀ e ∈ F, ∃ x ∈ W₁, ∃ y ∈ W₁, G_full.IsLink e x y) →
      ∀ e ∈ F, ∃ x ∈ W₂, ∃ y ∈ W₂, G_full.IsLink e x y := by
    intro W₁ W₂ hsub F hF e he
    obtain ⟨x, hx, y, hy, hl⟩ := hF e he
    exact ⟨x, hsub hx, y, hsub hy, hl⟩
  have liftU : ∀ {W : Set α} {F₁ F₂ : Set (β ⊕ ℕ)},
      (∀ e ∈ F₁, ∃ x ∈ W, ∃ y ∈ W, G_full.IsLink e x y) →
      (∀ e ∈ F₂, ∃ x ∈ W, ∃ y ∈ W, G_full.IsLink e x y) →
      ∀ e ∈ F₁ ∪ F₂, ∃ x ∈ W, ∃ y ∈ W, G_full.IsLink e x y := by
    rintro W F₁ F₂ h1 h2 e (he₁ | he₂)
    · exact h1 e he₁
    · exact h2 e he₂
  have hK_complete : ∀ b : Bool,
      GM16.IsCompleteGraphOn (GM16.subgraphOfVE G_full S (FK b)) S := by
    intro b
    refine ⟨rfl, ?_, ?_⟩
    · intro e x hloop
      obtain ⟨⟨u, v, hu, hv, _, rfl⟩, hl, _, _⟩ :=
        (subgraphOfVE_isLink G_full S (FK b) e x x).mp hloop
      rcases hl with hlG | ⟨_, _, _, hxx, _⟩
      · exact hfresh_notMem b ⟨u, hu⟩ ⟨v, hv⟩ hlG.edge_mem
      · exact hxx rfl
    · intro x hx y hy hxy
      let e₀ := freshEdge b ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨e₀, ?_, fun d hd => ?_⟩
      · dsimp only
        rw [subgraphOfVE_isLink]
        exact ⟨⟨x, y, hx, hy, hxy, rfl⟩, Or.inr ⟨b, hx, hy, hxy, rfl⟩, hx, hy⟩
      · obtain ⟨⟨u, v, hu, hv, _, he_fk⟩, hl, _, _⟩ :=
          (subgraphOfVE_isLink G_full S (FK b) d x y).mp hd
        rcases hl with hlG | ⟨b', hx', hy', _, rfl⟩
        · exact (hfresh_notMem b ⟨u, hu⟩ ⟨v, hv⟩ (he_fk ▸ hlG.edge_mem)).elim
        · have hb_eq : b = b' := (hfresh_inj.mp he_fk.symm).1
          subst hb_eq
          rfl
  have hFG : ∀ e ∈ E(G), ∃ x ∈ V(G), ∃ y ∈ V(G), G_full.IsLink e x y := by
    intro e he
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
    exact ⟨x, hl.left_mem, y, hl.right_mem, Or.inl hl⟩
  have hFHmid : ∀ e ∈ E₂ ∪ E_S, ∃ x ∈ V₂, ∃ y ∈ V₂, G_full.IsLink e x y :=
    liftU hFE₂ (liftW hS_V₂ hFES)
  have hFG₁ : ∀ e ∈ E₁ ∪ FK false, ∃ x ∈ V₁, ∃ y ∈ V₁, G_full.IsLink e x y :=
    liftU hFE₁ (liftW hS_V₁ (hFFK false))
  have hFGmid : ∀ e ∈ (E₂ ∪ E_S) ∪ FK false, ∃ x ∈ V₂, ∃ y ∈ V₂, G_full.IsLink e x y :=
    liftU hFHmid (liftW hS_V₂ (hFFK false))
  have hFHS : ∀ e ∈ E_S ∪ FK false, ∃ x ∈ S, ∃ y ∈ S, G_full.IsLink e x y :=
    liftU hFES (hFFK false)
  have hFG₂ : ∀ e ∈ E₂ ∪ FK true, ∃ x ∈ V₂, ∃ y ∈ V₂, G_full.IsLink e x y :=
    liftU hFE₂ (liftW hS_V₂ (hFFK true))
  have hFGS : ∀ e ∈ (E_S ∪ FK false) ∪ FK true, ∃ x ∈ S, ∃ y ∈ S, G_full.IsLink e x y :=
    liftU hFHS (hFFK true)
  have hdisj_E₁_mid : Disjoint E₁ (E₂ ∪ E_S) :=
    disjoint_union_right.mpr ⟨hdisj_E₁_E₂, hdisj_E₁_ES⟩
  have hdisj_E₁_FK0 : Disjoint E₁ (FK false) :=
    (hFK_disj_G false).mono_left (fun _ h => h.1.1)
  have hdisj_mid_FK0 : Disjoint (E₂ ∪ E_S) (FK false) :=
    (hFK_disj_G false).mono_left (by rintro _ (h | h); exact h.1.1; exact h.1)
  have hdisj_E₂_HS : Disjoint E₂ (E_S ∪ FK false) :=
    disjoint_union_right.mpr ⟨hdisj_E₂_ES, (hFK_disj_G false).mono_left (fun _ h => h.1.1)⟩
  have hdisj_E₂_FK1 : Disjoint E₂ (FK true) :=
    (hFK_disj_G true).mono_left (fun _ h => h.1.1)
  have hdisj_HS_FK1 : Disjoint (E_S ∪ FK false) (FK true) :=
    disjoint_union_left.mpr ⟨(hFK_disj_G true).mono_left (fun _ h => h.1), hFK_disj⟩
  have hsep_G : GM06.IsGraphSeparation G H₁ H_mid := by
    have hs := GM16.isGraphSeparation_subgraphOfVE (G₀ := G_full) subset_rfl hV₁_sub hV₂_sub
      hFG hFE₁ hFHmid hV_union hE_part hdisj_E₁_mid
    rwa [hG_eq] at hs
  have hsep_G₁ : GM06.IsGraphSeparation G₁ H₁ K₁ :=
    GM16.isGraphSeparation_subgraphOfVE hV₁_sub hV₁_sub hS_sub
      hFG₁ hFE₁ (hFFK false) (union_eq_self_of_subset_right hS_V₁) rfl hdisj_E₁_FK0
  have hsep_Gmid₁ : GM06.IsGraphSeparation G_mid H_mid K₁ :=
    GM16.isGraphSeparation_subgraphOfVE hV₂_sub hV₂_sub hS_sub
      hFGmid hFHmid (hFFK false) (union_eq_self_of_subset_right hS_V₂) rfl hdisj_mid_FK0
  have hsum₁ : GM16.IsCliqueSum G G₁ G_mid :=
    ⟨H₁, H_mid, K₁, hsep_G, hK_complete false, hsep_G₁, hsep_Gmid₁⟩
  have hmid_edges_eq : E₂ ∪ (E_S ∪ FK false) = (E₂ ∪ E_S) ∪ FK false := (union_assoc _ _ _).symm
  have hsep_mid₂ : GM06.IsGraphSeparation G_mid H₂ H_S :=
    GM16.isGraphSeparation_subgraphOfVE hV₂_sub hV₂_sub hS_sub
      hFGmid hFE₂ hFHS (union_eq_self_of_subset_right hS_V₂) hmid_edges_eq hdisj_E₂_HS
  have hsep_G₂ : GM06.IsGraphSeparation G₂ H₂ K₂ :=
    GM16.isGraphSeparation_subgraphOfVE hV₂_sub hV₂_sub hS_sub
      hFG₂ hFE₂ (hFFK true) (union_eq_self_of_subset_right hS_V₂) rfl hdisj_E₂_FK1
  have hsep_GS : GM06.IsGraphSeparation G_S H_S K₂ :=
    GM16.isGraphSeparation_subgraphOfVE hS_sub hS_sub hS_sub
      hFGS hFHS (hFFK true) (union_self _) rfl hdisj_HS_FK1
  have hsum₂ : GM16.IsCliqueSum G_mid G₂ G_S := by
    refine ⟨H₂, H_S, K₂, hsep_mid₂, ?_, hsep_G₂, hsep_GS⟩
    simpa only [show V(H₂) ∩ V(H_S) = S from inter_eq_self_of_subset_right hS_V₂]
      using hK_complete true
  have hEGS_fin : E(G_S).Finite := by
    rw [GM16.edgeSet_subgraphOfVE hFGS]
    exact ((hEG.subset fun _ h => h.1).union (hFK_fin false)).union (hFK_fin true)
  have htree_GS : GM16.HasTreeStructureOver (WagnerClass α β) G_S :=
    hasTreeStructureOver_of_ncard_le_four hS_fin hEGS_fin (hS_card.trans (by decide))
  have hTorsoProps : ∀ (W : Set α) (EW : Set (β ⊕ ℕ)) (b : Bool)
      (hEW_sub : EW ⊆ E(G) \ E_S)
      (hEW_intro : ∀ d u v, G.IsLink d u v → u ∈ W → v ∈ W → d ∉ E_S → d ∈ EW)
      (hFGW : ∀ e ∈ EW ∪ FK b, ∃ x ∈ W, ∃ y ∈ W, G_full.IsLink e x y),
      let GW := GM16.subgraphOfVE G_full W (EW ∪ FK b)
      E(GW).Finite ∧ IsSimpleGraphRep GW ∧
      ∀ u ∈ W, ∀ v ∈ W, u ≠ v → (GW.Adj u v ↔ G.Adj u v ∨ (u ∈ S ∧ v ∈ S)) := by
    intro W EW b hEW_sub hEW_intro hFGW GW
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · rw [GM16.edgeSet_subgraphOfVE hFGW]
      exact (hEG.subset fun _ h => (hEW_sub h).1).union (hFK_fin b)
    · intro d x hloop
      obtain ⟨hd, hl, _, _⟩ := (subgraphOfVE_isLink G_full W (EW ∪ FK b) d x x).mp hloop
      rcases hl with hlG | ⟨_, _, _, hxx, _⟩
      · exact hSimple.1 d x hlG
      · exact hxx rfl
    · intro d₁ d₂ x y hl₁ hl₂
      obtain ⟨hd₁, hfl₁, _, _⟩ := (subgraphOfVE_isLink G_full W (EW ∪ FK b) d₁ x y).mp hl₁
      obtain ⟨hd₂, hfl₂, _, _⟩ := (subgraphOfVE_isLink G_full W (EW ∪ FK b) d₂ x y).mp hl₂
      rcases hd₁ with h₁E | ⟨u₁, v₁, hu₁, hv₁, _, rfl⟩ <;>
        rcases hd₂ with h₂E | ⟨u₂, v₂, hu₂, hv₂, _, rfl⟩
      · have hg₁ : G.IsLink d₁ x y := hfl₁.resolve_right fun ⟨b', hx', hy', _, heq⟩ =>
          hfresh_notMem b' ⟨x, hx'⟩ ⟨y, hy'⟩ (heq ▸ (hEW_sub h₁E).1)
        have hg₂ : G.IsLink d₂ x y := hfl₂.resolve_right fun ⟨b', hx', hy', _, heq⟩ =>
          hfresh_notMem b' ⟨x, hx'⟩ ⟨y, hy'⟩ (heq ▸ (hEW_sub h₂E).1)
        exact hSimple.2 d₁ d₂ x y hg₁ hg₂
      · exfalso
        have hg₁ : G.IsLink d₁ x y := hfl₁.resolve_right fun ⟨b', hx', hy', _, heq⟩ =>
          hfresh_notMem b' ⟨x, hx'⟩ ⟨y, hy'⟩ (heq ▸ (hEW_sub h₁E).1)
        rcases hfl₂ with hg₂ | ⟨_, hxS, hyS, _, _⟩
        · exact hfresh_notMem b ⟨u₂, hu₂⟩ ⟨v₂, hv₂⟩ hg₂.edge_mem
        · exact (hEW_sub h₁E).2 ⟨hg₁.edge_mem, x, hxS, y, hyS, hg₁⟩
      · exfalso
        have hg₂ : G.IsLink d₂ x y := hfl₂.resolve_right fun ⟨b', hx', hy', _, heq⟩ =>
          hfresh_notMem b' ⟨x, hx'⟩ ⟨y, hy'⟩ (heq ▸ (hEW_sub h₂E).1)
        rcases hfl₁ with hg₁ | ⟨_, hxS, hyS, _, _⟩
        · exact hfresh_notMem b ⟨u₁, hu₁⟩ ⟨v₁, hv₁⟩ hg₁.edge_mem
        · exact (hEW_sub h₂E).2 ⟨hg₂.edge_mem, x, hxS, y, hyS, hg₂⟩
      · rcases hfl₁ with hg₁ | ⟨b₁', hx₁, hy₁, _, heq₁⟩
        · exact (hfresh_notMem b ⟨u₁, hu₁⟩ ⟨v₁, hv₁⟩ hg₁.edge_mem).elim
        · rcases hfl₂ with hg₂ | ⟨b₂', hx₂, hy₂, _, heq₂⟩
          · exact (hfresh_notMem b ⟨u₂, hu₂⟩ ⟨v₂, hv₂⟩ hg₂.edge_mem).elim
          · have hb₁ : b = b₁' := (hfresh_inj.mp heq₁).1
            have hb₂ : b = b₂' := (hfresh_inj.mp heq₂).1
            subst hb₁
            cases hb₂
            exact heq₁.trans heq₂.symm
    · intro u huW v hvW huv
      constructor
      · rintro ⟨d, hl⟩
        obtain ⟨hd, hfl, _, _⟩ := (subgraphOfVE_isLink G_full W (EW ∪ FK b) d u v).mp hl
        rcases hfl with hg | ⟨_, huS, hvS, _, _⟩
        · exact Or.inl ⟨d, hg⟩
        · exact Or.inr ⟨huS, hvS⟩
      · rintro (⟨d, hg⟩ | ⟨huS, hvS⟩)
        · by_cases hdS : d ∈ E_S
          · obtain ⟨_, x', hx', y', hy', hg'⟩ := hdS
            have huS : u ∈ S := by
              rcases G.eq_or_eq_of_isLink_of_isLink hg hg' with rfl | rfl <;> assumption
            have hvS : v ∈ S := by
              rcases G.eq_or_eq_of_isLink_of_isLink hg.symm hg' with rfl | rfl <;> assumption
            exact ⟨freshEdge b ⟨u, huS⟩ ⟨v, hvS⟩,
              (subgraphOfVE_isLink G_full W (EW ∪ FK b) _ u v).mpr
                ⟨Or.inr ⟨u, v, huS, hvS, huv, rfl⟩, Or.inr ⟨b, huS, hvS, huv, rfl⟩, huW, hvW⟩⟩
          · exact ⟨d, (subgraphOfVE_isLink G_full W (EW ∪ FK b) d u v).mpr
              ⟨Or.inl (hEW_intro d u v hg huW hvW hdS), Or.inl hg, huW, hvW⟩⟩
        · exact ⟨freshEdge b ⟨u, huS⟩ ⟨v, hvS⟩,
            (subgraphOfVE_isLink G_full W (EW ∪ FK b) _ u v).mpr
              ⟨Or.inr ⟨u, v, huS, hvS, huv, rfl⟩, Or.inr ⟨b, huS, hvS, huv, rfl⟩, huW, hvW⟩⟩
  obtain ⟨hEG₁, hSimp₁, hAdj₁⟩ := hTorsoProps V₁ E₁ false
    (fun _ h => h.1)
    (fun d u v hg hu hv hdS => ⟨⟨hg.edge_mem, hdS⟩, u, hu, v, hv, hg⟩) hFG₁
  obtain ⟨hEG₂, hSimp₂, hAdj₂⟩ := hTorsoProps V₂ E₂ true
    (fun _ h => h.1)
    (fun d u v hg hu hv hdS => ⟨⟨hg.edge_mem, hdS⟩, u, hu, v, hv, hg⟩) hFG₂
  exact ⟨G₁, G₂, rfl, hEG₁, hSimp₁, hAdj₁, rfl, hEG₂, hSimp₂, hAdj₂,
    fun ht₁ ht₂ => .cliqueSum hsum₁ ht₁ (.cliqueSum hsum₂ ht₂ htree_GS)⟩

/-! ### Part 3: Reduction of General Finite Multigraphs to `SimpleGraph (Fin N)` (`N ≥ 5`) -/

private theorem isPlanar_of_fin_planeEmbedding {N : ℕ} (hN : 1 ≤ N)
    {G : Graph α (β ⊕ ℕ)} (hVG : V(G).Finite) (hEG : E(G).Finite) (hSimple : IsSimpleGraphRep G)
    (eV : Fin N ≃ V(G)) {K : SimpleGraph (Fin N)}
    (hadj : ∀ i j : Fin N, K.Adj i j ↔ i ≠ j ∧ G.Adj (eV i).1 (eV j).1)
    (φ : HP25.PlaneEmbedding K Set.univ) : IsPlanar G := by
  classical
  let i₀ : Fin N := ⟨0, hN⟩
  let idx : α → Fin N := fun x => if hx : x ∈ V(G) then eV.symm ⟨x, hx⟩ else i₀
  have hidx_spec : ∀ {x : α} (hx : x ∈ V(G)), eV (idx x) = ⟨x, hx⟩ := fun hx => by
    simp [idx, hx]
  have hidx_inj : InjOn idx V(G) := by
    intro x hx y hy hxy
    have h1 := congrArg (fun i => (eV i).1) hxy
    simpa [hidx_spec hx, hidx_spec hy] using h1
  have hK_of_shadow : ∀ {u v : α}, u ∈ V(G) → v ∈ V(G) →
      (GM05.simpleShadow G).spanningCoe.Adj u v → K.Adj (idx u) (idx v) := by
    intro u v hu hv ⟨hne, hg⟩
    rw [hadj]
    refine ⟨fun h => hne (hidx_inj hu hv h), ?_⟩
    simpa [hidx_spec hu, hidx_spec hv] using hg
  let ψ : HP25.PlaneEmbedding (GM05.simpleShadow G).spanningCoe V(G) :=
    { pt := φ.pt ∘ idx
      line := fun u v => φ.line (idx u) (idx v)
      finite := hVG
      injOn := fun x hx y hy hpt => hidx_inj hx hy (φ.injOn trivial trivial hpt)
      line_comm := fun u v => φ.line_comm (idx u) (idx v)
      isLine := fun u hu v hv huv =>
        φ.isLine (idx u) trivial (idx v) trivial (hK_of_shadow hu hv huv)
      inter := fun u hu v hv u' hu' v' hv' huv huv' hne z hz => by
        have hne' : s(idx u, idx v) ≠ s(idx u', idx v') := by
          intro heq
          apply hne
          rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [hidx_inj hu hu' h1, hidx_inj hv hv' h2]
          · rw [hidx_inj hu hv' h1, hidx_inj hv hu' h2, Sym2.eq_swap]
        obtain ⟨k, ⟨hk1, hk2⟩, hzk⟩ := φ.inter (idx u) trivial (idx v) trivial
          (idx u') trivial (idx v') trivial (hK_of_shadow hu hv huv)
          (hK_of_shadow hu' hv' huv') hne' hz
        let w : α := (eV k).1
        have hwV : w ∈ V(G) := (eV k).2
        have hidx_w : idx w = k := by
          simp [idx, hwV, w]
        refine ⟨w, ⟨?_, ?_⟩, by simpa [Function.comp_apply, hidx_w] using hzk⟩
        · rcases hk1 with rfl | rfl
          · exact Or.inl (congrArg Subtype.val (hidx_spec hu))
          · exact Or.inr (congrArg Subtype.val (hidx_spec hv))
        · rcases hk2 with rfl | rfl
          · exact Or.inl (congrArg Subtype.val (hidx_spec hu'))
          · exact Or.inr (congrArg Subtype.val (hidx_spec hv'))
      avoid := fun u hu v hv huv w hw hpt => by
        rcases φ.avoid (idx u) trivial (idx v) trivial (hK_of_shadow hu hv huv)
          (idx w) trivial hpt with h1 | h2
        · exact Or.inl (hidx_inj hw hu h1)
        · exact Or.inr (hidx_inj hw hv h2) }
  exact isPlanar_of_planeEmbedding hVG hEG hSimple ⟨ψ⟩

/-- Given the structural dichotomy for `K_5`-minor-free simple graphs on `Fin N` (`N ≥ 5`), every
finite `K_5`-minor-free graph `G : Graph α β` has a tree-structure over planar graphs and `V_8`. -/
theorem hasTreeStructureOver_of_finSimple_step
    (hcore : ∀ (N : ℕ), 5 ≤ N → ∀ (K : SimpleGraph (Fin N)), ¬ HasK5MinorSimple K →
      Nonempty (HP25.PlaneEmbedding K Set.univ) ∨
      Nonempty (Iso (Graph.ofSimpleGraph K) GM16.wagnerGraphV8) ∨
      ∃ A₁ A₂ : Finset (Fin N),
        A₁ ∪ A₂ = Finset.univ ∧ A₁.card < N ∧ A₂.card < N ∧ (A₁ ∩ A₂).card ≤ 3 ∧
        (∀ x y, K.Adj x y → (x ∈ A₁ ∧ y ∈ A₁) ∨ (x ∈ A₂ ∧ y ∈ A₂)) ∧
        ¬ HasK5MinorSimple (torsoOn K A₁ (A₁ ∩ A₂)) ∧
        ¬ HasK5MinorSimple (torsoOn K A₂ (A₁ ∩ A₂)))
    {G₀ : Graph α β} (hVG₀ : V(G₀).Finite) (hEG₀ : E(G₀).Finite)
    (hnoK5₀ : ¬ IsIsoMinor (GM16.completeGraph 5) G₀) :
    GM16.HasTreeStructureOver (WagnerClass α β) (GM16.liftEdgeInl G₀) := by
  classical
  have hmain : ∀ (N : ℕ) (G : Graph α (β ⊕ ℕ)),
      V(G).Finite → E(G).Finite → V(G).ncard = N →
      ¬ IsIsoMinor (GM16.completeGraph 5) G →
      GM16.HasTreeStructureOver (WagnerClass α β) G := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro G hVG hEG hN_eq hnoK5
      by_cases hle4 : N ≤ 4
      · exact hasTreeStructureOver_of_ncard_le_four hVG hEG (hN_eq ▸ hle4)
      · have hN5 : 5 ≤ N := by omega
        refine hasTreeStructureOver_of_simple_verts hEG hnoK5 ?_
        intro H hVH hEH hSimpH hnoK5H
        have hVH_fin : V(H).Finite := hVH ▸ hVG
        have hNH_eq : V(H).ncard = N := hVH ▸ hN_eq
        let _ : Fintype V(H) := hVH_fin.fintype
        have hcard_eq : Fintype.card (Fin N) = Fintype.card V(H) := by
          rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hNH_eq]
        let eV : Fin N ≃ V(H) := Fintype.equivOfCardEq hcard_eq
        let K : SimpleGraph (Fin N) :=
          { Adj := fun i j => i ≠ j ∧ H.Adj (eV i).1 (eV j).1
            symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
            loopless := ⟨fun _ h => h.1 rfl⟩ }
        obtain ⟨isoKH⟩ :=
          nonempty_iso_ofSimpleGraph_of_equiv (K := K) hSimpH eV (fun _ _ => Iff.rfl)
        have hnoK5_K : ¬ HasK5MinorSimple K := by
          rw [hasK5MinorSimple_iff_isIsoMinor]
          exact fun hm => hnoK5H (Iso.isIsoMinor_right hm isoKH)
        rcases hcore N hN5 K hnoK5_K with hφ | hiso |
          ⟨A₁, A₂, hA_union, hA₁_lt, hA₂_lt, hS_le3, hK_sep, hnoT₁, hnoT₂⟩
        · exact .base (Or.inl (isPlanar_of_fin_planeEmbedding (by omega)
            hVH_fin hEH hSimpH eV (K := K) (fun _ _ => Iff.rfl) (Classical.choice hφ)))
        · exact .base (Or.inr ⟨isoKH.symm.trans (Classical.choice hiso)⟩)
        · let f : Fin N → α := fun i => (eV i).1
          have hf_inj : Function.Injective f := Subtype.val_injective.comp eV.injective
          let V₁ : Set α := f '' (A₁ : Set (Fin N))
          let V₂ : Set α := f '' (A₂ : Set (Fin N))
          have hV₁_sub : V₁ ⊆ V(H) := by rintro _ ⟨i, _, rfl⟩; exact (eV i).2
          have hV₂_sub : V₂ ⊆ V(H) := by rintro _ ⟨i, _, rfl⟩; exact (eV i).2
          have hV_union : V₁ ∪ V₂ = V(H) := by
            ext x
            constructor
            · rintro (h | h)
              · exact hV₁_sub h
              · exact hV₂_sub h
            · intro hx
              let i := eV.symm ⟨x, hx⟩
              have hfi : f i = x := congrArg Subtype.val (eV.apply_symm_apply ⟨x, hx⟩)
              have hi_mem : i ∈ (A₁ ∪ A₂ : Finset (Fin N)) := hA_union.symm ▸ Finset.mem_univ i
              rcases Finset.mem_union.mp hi_mem with hi₁ | hi₂
              · exact Or.inl ⟨i, hi₁, hfi⟩
              · exact Or.inr ⟨i, hi₂, hfi⟩
          have hInter_eq : V₁ ∩ V₂ = f '' ((A₁ ∩ A₂ : Finset (Fin N)) : Set (Fin N)) := by
            rw [Finset.coe_inter, Set.image_inter hf_inj]
          have hS_ncard : (V₁ ∩ V₂).ncard ≤ 3 := by
            rw [hInter_eq, Set.ncard_image_of_injective _ hf_inj, Set.ncard_coe_finset]
            exact hS_le3
          have hH_sep : ∀ d x y, H.IsLink d x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂) := by
            intro d x y hl
            have hxy : x ≠ y := fun h => hSimpH.1 d x (h ▸ hl)
            let i := eV.symm ⟨x, hl.left_mem⟩
            let j := eV.symm ⟨y, hl.right_mem⟩
            have hfi : f i = x := congrArg Subtype.val (eV.apply_symm_apply _)
            have hfj : f j = y := congrArg Subtype.val (eV.apply_symm_apply _)
            have hij : i ≠ j := fun h => hxy (hfi ▸ hfj ▸ congrArg f h)
            have hKij : K.Adj i j := ⟨hij, by change H.Adj (f i) (f j); rw [hfi, hfj]; exact ⟨d, hl⟩⟩
            rcases hK_sep i j hKij with ⟨hi₁, hj₁⟩ | ⟨hi₂, hj₂⟩
            · exact Or.inl ⟨⟨i, hi₁, hfi⟩, ⟨j, hj₁, hfj⟩⟩
            · exact Or.inr ⟨⟨i, hi₂, hfi⟩, ⟨j, hj₂, hfj⟩⟩
          obtain ⟨G₁, G₂, hVG₁, hEG₁, hSimp₁, hAdj₁, hVG₂, hEG₂, hSimp₂, hAdj₂, hmk⟩ :=
            exists_simple_torsos_of_sep hVH_fin hEH hSimpH hV₁_sub hV₂_sub
              hV_union hS_ncard hH_sep
          have hTorsoIso : ∀ (A : Finset (Fin N)) (GA : Graph α (β ⊕ ℕ)),
              V(GA) = f '' (A : Set (Fin N)) → IsSimpleGraphRep GA →
              (∀ u ∈ f '' (A : Set (Fin N)), ∀ v ∈ f '' (A : Set (Fin N)), u ≠ v →
                (GA.Adj u v ↔ H.Adj u v ∨ (u ∈ V₁ ∩ V₂ ∧ v ∈ V₁ ∩ V₂))) →
              ¬ HasK5MinorSimple (torsoOn K A (A₁ ∩ A₂)) →
              ¬ IsIsoMinor (GM16.completeGraph 5) GA := by
            intro A GA hVGA hSimpGA hAdjGA hnoTA
            let eA : {x : Fin N // x ∈ A} ≃ V(GA) :=
              (Equiv.Set.image f (A : Set (Fin N)) hf_inj).trans (Set.equivOfEq hVGA.symm)
            have hadjA : ∀ p q : {x : Fin N // x ∈ A},
                (torsoOn K A (A₁ ∩ A₂)).Adj p q ↔ p ≠ q ∧ GA.Adj (eA p).1 (eA q).1 := by
              rintro ⟨i, hi⟩ ⟨j, hj⟩
              have hfiA : f i ∈ f '' (A : Set (Fin N)) := ⟨i, hi, rfl⟩
              have hfjA : f j ∈ f '' (A : Set (Fin N)) := ⟨j, hj, rfl⟩
              change (Subtype.mk i hi ≠ Subtype.mk j hj ∧
                ((i ≠ j ∧ H.Adj (f i) (f j)) ∨ (i ∈ A₁ ∩ A₂ ∧ j ∈ A₁ ∩ A₂))) ↔
                Subtype.mk i hi ≠ Subtype.mk j hj ∧ GA.Adj (f i) (f j)
              refine and_congr_right fun hne_sub => ?_
              have hij : i ≠ j := fun h => hne_sub (Subtype.ext h)
              have hfij : f i ≠ f j := hf_inj.ne hij
              rw [hAdjGA (f i) hfiA (f j) hfjA hfij]
              have hS_iff : ∀ k : Fin N, f k ∈ V₁ ∩ V₂ ↔ k ∈ A₁ ∩ A₂ := by
                intro k
                rw [hInter_eq]
                exact ⟨fun ⟨k', hk', heq⟩ => hf_inj heq ▸ hk', fun hk => ⟨k, hk, rfl⟩⟩
              rw [hS_iff i, hS_iff j]
              exact ⟨fun h => h.imp_left fun h1 => h1.2,
                fun h => h.imp_left fun h1 => ⟨hij, h1⟩⟩
            have hisoA :=
              nonempty_iso_ofSimpleGraph_of_equiv (K := torsoOn K A (A₁ ∩ A₂)) hSimpGA eA hadjA
            intro hmGA
            apply hnoTA
            rw [hasK5MinorSimple_iff_isIsoMinor]
            exact Iso.isIsoMinor_right hmGA (Classical.choice hisoA).symm
          have hnoG₁ := hTorsoIso A₁ G₁ hVG₁ hSimp₁ hAdj₁ hnoT₁
          have hnoG₂ := hTorsoIso A₂ G₂ hVG₂ hSimp₂ hAdj₂ hnoT₂
          have hVG₁_fin : V(G₁).Finite := hVG₁ ▸ (A₁.finite_toSet.image f)
          have hVG₂_fin : V(G₂).Finite := hVG₂ ▸ (A₂.finite_toSet.image f)
          have hcard₁ : V(G₁).ncard = A₁.card := by
            rw [hVG₁, Set.ncard_image_of_injective _ hf_inj, Set.ncard_coe_finset]
          have hcard₂ : V(G₂).ncard = A₂.card := by
            rw [hVG₂, Set.ncard_image_of_injective _ hf_inj, Set.ncard_coe_finset]
          exact hmk (ih A₁.card hA₁_lt G₁ hVG₁_fin hEG₁ hcard₁ hnoG₁)
            (ih A₂.card hA₂_lt G₂ hVG₂_fin hEG₂ hcard₂ hnoG₂)
  exact hmain V(GM16.liftEdgeInl G₀).ncard (GM16.liftEdgeInl G₀) hVG₀ (hEG₀.image Sum.inl) rfl
    fun hm => hnoK5₀ (Iso.isIsoMinor_right hm (GM16.iso_liftEdgeInl G₀).symm)

end GraphMinor.Wagner

