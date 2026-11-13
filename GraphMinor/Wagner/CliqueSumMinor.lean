module

public import GraphMinor.GM16.Defs
public import GraphMinor.Planar.Defs
import GraphMinor.GM01.Basic
import GraphMinor.GM05.MinorTransfer
import GraphMinor.GM16.Section2
import GraphMinor.Minor.Basic
import GraphMinor.Wagner.PlanarBridge
import GraphMinor.Wagner.V8NoK5

/-!
# Clique-Sums, Complete-Graph Minors, and Sufficiency of Wagner's Tree-Structure

This file proves the "if" direction of Wagner's theorem (`GraphMinor.GM16.theorem_1_2_proof`):
1. If `G` is a finite clique-sum of `G₁` and `G₂` (`GM16.IsCliqueSum G G₁ G₂`), then any
   `K_n` minor of `G` can be projected into `G₁` or `G₂`
   (`isIsoMinor_completeGraph_of_isCliqueSum`, `not_isIsoMinor_completeGraph_of_isCliqueSum`).
2. Consequently, if `liftEdgeInl G` has a tree-structure over the class of graphs that are either
   planar or isomorphic to `V_8`, then `G` has no `K_5` minor
   (`not_isIsoMinor_completeGraph_five_of_hasTreeStructureOver`).
3. Small-case sanity checks (`smallCase_bot`, `smallCase_single_loop`, `smallCase_K4`,
   `smallCase_V8`) verifying both sides of Wagner's characterization on the null graph, a single
   vertex with a loop, `K_4`, and `V_8`.
-/

public section

namespace GraphMinor.Wagner

open Set Graph SimpleGraph

variable {α : Type*} {β : Type*} {α' : Type*} {β' : Type*}

/-- Planarity is preserved under graph isomorphism. -/
theorem isPlanar_of_iso {H : Graph α' β'} {G : Graph α β} (e : Iso H G) (hG : IsPlanar G) :
    IsPlanar H := by
  rcases hG with ⟨_, _, S, tS, hSurf, hSph, ⟨Γ⟩⟩
  let Γ' : Surface.GraphDrawing H S := Surface.GraphDrawing.ofIso e Γ
  exact ⟨Γ'.finite_V, Γ'.finite_E, S, tS, hSurf, hSph, ⟨Γ'⟩⟩

private theorem isLink_of_le_of_mem_edgeSet {H G : Graph α β} (hle : H ≤ G)
    {e : β} {u v : α} (hlink : G.IsLink e u v) (he : e ∈ E(H)) : H.IsLink e u v := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  have hGxy : G.IsLink e x y := hle.2 hxy
  rcases G.eq_or_eq_of_isLink_of_isLink hGxy hlink with hx | hx <;> subst x
  · have hy : y = v := hGxy.right_unique hlink
    subst y
    exact hxy
  · have hy : y = u := hGxy.right_unique hlink.symm
    subst y
    exact hxy.symm

private theorem adj_or_adj_of_isGraphSeparation {G H₁ H₂ : Graph α β}
    (hsep : GM06.IsGraphSeparation G H₁ H₂) {u v : α} (hadj : G.Adj u v) :
    H₁.Adj u v ∨ H₂.Adj u v := by
  obtain ⟨e, hlink⟩ := hadj
  have he : e ∈ E(H₁) ∪ E(H₂) := hsep.2.2.2.1.symm ▸ hlink.edge_mem
  rcases he with he₁ | he₂
  · exact Or.inl ⟨e, isLink_of_le_of_mem_edgeSet hsep.1 hlink he₁⟩
  · exact Or.inr ⟨e, isLink_of_le_of_mem_edgeSet hsep.2.1 hlink he₂⟩

private theorem isGraphSeparation_symm {G H₁ H₂ : Graph α β}
    (hsep : GM06.IsGraphSeparation G H₁ H₂) : GM06.IsGraphSeparation G H₂ H₁ :=
  ⟨hsep.2.1, hsep.1, Set.union_comm _ _ ▸ hsep.2.2.1,
    Set.union_comm _ _ ▸ hsep.2.2.2.1, hsep.2.2.2.2.symm⟩

/-- Symmetry of `GM16.IsCliqueSum`. -/
theorem isCliqueSum_symm {G G₁ G₂ : Graph α β} (hsum : GM16.IsCliqueSum G G₁ G₂) :
    GM16.IsCliqueSum G G₂ G₁ := by
  rcases hsum with ⟨H₁, H₂, K, hsep, hK, hsep₁, hsep₂⟩
  refine ⟨H₂, H₁, K, isGraphSeparation_symm hsep, ?_, hsep₂, hsep₁⟩
  simpa only [Set.inter_comm] using hK

private theorem sep_crossing_nonempty {G H₁ H₂ : Graph α β}
    (hsep : GM06.IsGraphSeparation G H₁ H₂) {X : Set α}
    {x y : α} (hwalk : Relation.ReflTransGen (G.induce X).Adj x y)
    (hxX : x ∈ X) (hx₁ : x ∈ V(H₁)) (hy₂ : y ∈ V(H₂)) :
    (X ∩ (V(H₁) ∩ V(H₂))).Nonempty := by
  induction hwalk using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨y, hxX, hx₁, hy₂⟩
  | @head a b hadj _ ih =>
    obtain ⟨e, hlink, haX, hbX⟩ := hadj
    by_cases hb₁ : b ∈ V(H₁)
    · exact ih hbX hb₁
    · rcases adj_or_adj_of_isGraphSeparation hsep ⟨e, hlink⟩ with hadj₁ | hadj₂
      · exact (hb₁ hadj₁.right_mem).elim
      · exact ⟨a, haX, hx₁, hadj₂.left_mem⟩

private theorem proj_walk_aux {G H₁ H₂ K G₁ : Graph α β}
    (hsep : GM06.IsGraphSeparation G H₁ H₂)
    (hK : GM16.IsCompleteGraphOn K (V(H₁) ∩ V(H₂)))
    (hsep₁ : GM06.IsGraphSeparation G₁ H₁ K)
    {X : Set α} {y : α} (hy : y ∈ X ∩ V(H₁))
    {a : α} (hwalk : Relation.ReflTransGen (G.induce X).Adj a y) :
    (a ∈ V(H₁) → Relation.ReflTransGen (G₁.induce (X ∩ V(H₁))).Adj a y) ∧
      (a ∈ V(H₂) → ∃ z ∈ X ∩ (V(H₁) ∩ V(H₂)),
        Relation.ReflTransGen (G₁.induce (X ∩ V(H₁))).Adj z y) := by
  induction hwalk using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exact ⟨fun _ => .refl, fun ha₂ => ⟨y, ⟨hy.1, hy.2, ha₂⟩, .refl⟩⟩
  | @head u b hadj _ ih =>
    obtain ⟨e, hlink, huX, hbX⟩ := hadj
    rcases adj_or_adj_of_isGraphSeparation hsep ⟨e, hlink⟩ with ⟨e₁, hl₁⟩ | hadj₂
    · have hu₁ : u ∈ V(H₁) := hl₁.left_mem
      have hb₁ : b ∈ V(H₁) := hl₁.right_mem
      have hadj_G₁ : (G₁.induce (X ∩ V(H₁))).Adj u b :=
        ⟨e₁, hsep₁.1.2 hl₁, ⟨huX, hu₁⟩, ⟨hbX, hb₁⟩⟩
      have hpath : Relation.ReflTransGen (G₁.induce (X ∩ V(H₁))).Adj u y :=
        .head hadj_G₁ (ih.1 hb₁)
      exact ⟨fun _ => hpath, fun hu₂ => ⟨u, ⟨huX, hu₁, hu₂⟩, hpath⟩⟩
    · have hb₂ : b ∈ V(H₂) := hadj₂.right_mem
      obtain ⟨z, hz, hzy⟩ := ih.2 hb₂
      refine ⟨fun hu₁ => ?_, fun _ => ⟨z, hz, hzy⟩⟩
      have hu₂ : u ∈ V(H₂) := hadj₂.left_mem
      by_cases huz : u = z
      · exact huz ▸ hzy
      · obtain ⟨eK, hlK, _⟩ := hK.2.2 u ⟨hu₁, hu₂⟩ z hz.2 huz
        have hadj_uz : (G₁.induce (X ∩ V(H₁))).Adj u z :=
          ⟨eK, hsep₁.2.1.2 hlK, ⟨huX, hu₁⟩, ⟨hz.1, hz.2.1⟩⟩
        exact .head hadj_uz hzy

private theorem isIsoMinor_completeGraph_of_side_meets {n : ℕ}
    {G H₁ H₂ K G₁ : Graph α β}
    (hV₁ : V(G₁).Finite) (hE₁ : E(G₁).Finite)
    (hsep : GM06.IsGraphSeparation G H₁ H₂)
    (hK : GM16.IsCompleteGraphOn K (V(H₁) ∩ V(H₂)))
    (hsep₁ : GM06.IsGraphSeparation G₁ H₁ K)
    (ηv : Fin n → Set α)
    (h_disj : ∀ {i j : Fin n}, i ≠ j → Disjoint (ηv i) (ηv j))
    (h_conn : ∀ i : Fin n, ∀ x ∈ ηv i, ∀ y ∈ ηv i,
      Relation.ReflTransGen (G.induce (ηv i)).Adj x y)
    (h_adj : ∀ {i j : Fin n}, i ≠ j → ∃ x ∈ ηv i, ∃ y ∈ ηv j, x ≠ y ∧ G.Adj x y)
    (h_meets : ∀ i : Fin n, (ηv i ∩ V(H₁)).Nonempty) :
    IsIsoMinor (GM16.completeGraph n) G₁ := by
  rw [completeGraph_eq_toGraph_top n]
  rw [← GM05.isIsoMinor_simpleShadow_iff finite_univ hV₁ hE₁]
  refine GM01.isIsoMinor_toGraph_of_connected_subgraphs finite_univ hV₁
    (fun i => GM05.simpleShadow (G₁.induce (ηv i ∩ V(H₁)))) ?_ ?_ ?_ ?_
  · intro i _
    exact GM05.simpleShadow_mono
      (G₁.induce_le (Set.inter_subset_right.trans hsep₁.1.vertexSet_mono))
  · intro i _
    rw [← GM05.graphConnected_iff_simpleShadow_connected]
    refine ⟨h_meets i, fun x hx y hy => ?_⟩
    exact (proj_walk_aux hsep hK hsep₁ hy (h_conn i x hx.1 y hy.1)).1 hx.2
  · intro i _ j _ hij
    exact (h_disj hij).mono Set.inter_subset_left Set.inter_subset_left
  · intro i j hij_adj
    have hij : i ≠ j := hij_adj.ne
    obtain ⟨x, hx, y, hy, hxy, hadjG⟩ := h_adj hij
    rcases adj_or_adj_of_isGraphSeparation hsep hadjG with ⟨e₁, hl₁⟩ | hadj₂
    · exact ⟨x, ⟨hx, hl₁.left_mem⟩, y, ⟨hy, hl₁.right_mem⟩, hxy, e₁, hsep₁.1.2 hl₁⟩
    · obtain ⟨u₀, hu₀⟩ := h_meets i
      obtain ⟨v₀, hv₀⟩ := h_meets j
      obtain ⟨x', hx'⟩ := sep_crossing_nonempty hsep
        (h_conn i u₀ hu₀.1 x hx) hu₀.1 hu₀.2 hadj₂.left_mem
      obtain ⟨y', hy'⟩ := sep_crossing_nonempty hsep
        (h_conn j v₀ hv₀.1 y hy) hv₀.1 hv₀.2 hadj₂.right_mem
      have hx'y' : x' ≠ y' := fun h =>
        Set.disjoint_left.mp (h_disj hij) hx'.1 (h ▸ hy'.1)
      obtain ⟨eK, hlK, _⟩ := hK.2.2 x' hx'.2 y' hy'.2 hx'y'
      exact ⟨x', ⟨hx'.1, hx'.2.1⟩, y', ⟨hy'.1, hy'.2.1⟩, hx'y', eK, hsep₁.2.1.2 hlK⟩

/-- If a finite graph `G` is a clique-sum of `G₁` and `G₂` and contains `K_n` as a minor, then
`G₁` or `G₂` contains `K_n` as a minor. -/
theorem isIsoMinor_completeGraph_of_isCliqueSum {n : ℕ} {G G₁ G₂ : Graph α β}
    (hsum : GM16.IsCliqueSum G G₁ G₂) (hV : V(G).Finite) (hE : E(G).Finite)
    (hm : IsIsoMinor (GM16.completeGraph n) G) :
    IsIsoMinor (GM16.completeGraph n) G₁ ∨ IsIsoMinor (GM16.completeGraph n) G₂ := by
  classical
  obtain ⟨⟨hV₁, hE₁⟩, ⟨hV₂, hE₂⟩⟩ := hsum.finite_of_finite hV hE
  rcases hsum with ⟨H₁, H₂, K, hsep, hK, hsep₁, hsep₂⟩
  have hm' : IsIsoMinor (GM16.completeGraph n) (GM16.liftEdgeInl G) :=
    Iso.isIsoMinor_right hm (GM16.iso_liftEdgeInl G)
  have hE' : E(GM16.liftEdgeInl G).Finite := hE.image Sum.inl
  have : Nonempty (β ⊕ ℕ) := ⟨Sum.inr 0⟩
  obtain ⟨ηv, ηe, hmodel⟩ :=
    exists_isMinorModel_of_isIsoMinor (G := GM16.liftEdgeInl G) hV hE' hm'
  have h_nonempty : ∀ i : Fin n, (ηv i).Nonempty := fun i => hmodel.vertex_nonempty i trivial
  have h_sub : ∀ i : Fin n, ηv i ⊆ V(G) := fun i => hmodel.vertex_subset i trivial
  have h_disj : ∀ {i j : Fin n}, i ≠ j → Disjoint (ηv i) (ηv j) :=
    fun hij => hmodel.vertex_disjoint _ trivial _ trivial hij
  have h_conn : ∀ i : Fin n, ∀ x ∈ ηv i, ∀ y ∈ ηv i,
      Relation.ReflTransGen (G.induce (ηv i)).Adj x y := by
    intro i x hx y hy
    obtain ⟨B, hB_le, hVB, hB_conn⟩ := hmodel.connected i trivial
    have hB_le' : B ≤ GM16.liftEdgeInl G := hB_le.trans Graph.deleteEdges_le
    have hwalk := hB_conn.2 x (hVB.symm ▸ hx) y (hVB.symm ▸ hy)
    induction hwalk using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | @head a b hab _ ih =>
      obtain ⟨e, hlB⟩ := hab
      have ha : a ∈ ηv i := hVB ▸ hlB.left_mem
      have hb : b ∈ ηv i := hVB ▸ hlB.right_mem
      obtain ⟨e₀, _, hlG⟩ := hB_le'.2 hlB
      exact .head ⟨e₀, hlG, ha, hb⟩ (ih hb)
  have h_adj : ∀ {i j : Fin n}, i ≠ j → ∃ x ∈ ηv i, ∃ y ∈ ηv j, x ≠ y ∧ G.Adj x y := by
    intro i j hij
    let e : Sym2 (Fin n) := s(i, j)
    have he_link : (GM16.completeGraph n).IsLink e i j := ⟨hij, rfl⟩
    obtain ⟨x, hx, hxe⟩ := (hmodel.inc_iff i trivial e he_link.edge_mem).mp he_link.inc_left
    obtain ⟨y, hy, hye⟩ := (hmodel.inc_iff j trivial e he_link.edge_mem).mp he_link.inc_right
    have hxy : x ≠ y := fun h => Set.disjoint_left.mp (h_disj hij) hx (h ▸ hy)
    have hother : y = hxe.other := hye.eq_of_isLink_of_ne_left hxe.isLink_other hxy.symm
    have hlink' : (GM16.liftEdgeInl G).IsLink (ηe e) x y := hother.symm ▸ hxe.isLink_other
    obtain ⟨e₀, _, hlG⟩ := hlink'
    exact ⟨x, hx, y, hy, hxy, e₀, hlG⟩
  by_cases h_all₁ : ∀ i : Fin n, (ηv i ∩ V(H₁)).Nonempty
  · exact Or.inl (isIsoMinor_completeGraph_of_side_meets
      hV₁ hE₁ hsep hK hsep₁ ηv h_disj h_conn h_adj h_all₁)
  · rw [not_forall] at h_all₁
    obtain ⟨i₀, hi₀_empty⟩ := h_all₁
    have hi₀_sub₂ : ηv i₀ ⊆ V(H₂) := by
      intro x hx
      have hxG : x ∈ V(H₁) ∪ V(H₂) := hsep.2.2.1.symm ▸ h_sub i₀ hx
      rcases hxG with hx₁ | hx₂
      · exact (hi₀_empty ⟨x, hx, hx₁⟩).elim
      · exact hx₂
    have h_all₂ : ∀ j : Fin n, (ηv j ∩ V(H₂)).Nonempty := by
      intro j
      by_cases hji₀ : j = i₀
      · subst j
        obtain ⟨x, hx⟩ := h_nonempty i₀
        exact ⟨x, hx, hi₀_sub₂ hx⟩
      · obtain ⟨x, hx, y, hy, _, hadjG⟩ := h_adj (Ne.symm hji₀)
        rcases adj_or_adj_of_isGraphSeparation hsep hadjG with hadj₁ | hadj₂
        · exact (hi₀_empty ⟨x, hx, hadj₁.left_mem⟩).elim
        · exact ⟨y, hy, hadj₂.right_mem⟩
    have hK' : GM16.IsCompleteGraphOn K (V(H₂) ∩ V(H₁)) := by
      simpa only [Set.inter_comm] using hK
    exact Or.inr (isIsoMinor_completeGraph_of_side_meets
      hV₂ hE₂ (isGraphSeparation_symm hsep) hK' hsep₂ ηv h_disj h_conn h_adj h_all₂)

/-- A clique-sum of two finite `K_n`-minor-free graphs has no `K_n` minor. -/
theorem not_isIsoMinor_completeGraph_of_isCliqueSum {n : ℕ} {G G₁ G₂ : Graph α β}
    (hsum : GM16.IsCliqueSum G G₁ G₂) (hV : V(G).Finite) (hE : E(G).Finite)
    (h₁ : ¬ IsIsoMinor (GM16.completeGraph n) G₁)
    (h₂ : ¬ IsIsoMinor (GM16.completeGraph n) G₂) :
    ¬ IsIsoMinor (GM16.completeGraph n) G := fun hm =>
  (isIsoMinor_completeGraph_of_isCliqueSum hsum hV hE hm).elim h₁ h₂

/-- The "if" direction of Graph Minors XVI, (1.2): if `liftEdgeInl G` has a tree-structure over the
class of graphs that are planar or isomorphic to `V_8`, then `G` has no `K_5` minor. -/
theorem not_isIsoMinor_completeGraph_five_of_hasTreeStructureOver {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite)
    (htree : GM16.HasTreeStructureOver
      {H : Graph α (β ⊕ ℕ) | IsPlanar H ∨ Nonempty (Iso H GM16.wagnerGraphV8)}
      (GM16.liftEdgeInl G)) :
    ¬ IsIsoMinor (GM16.completeGraph 5) G := by
  have hElift : E(GM16.liftEdgeInl G).Finite := hE.image Sum.inl
  have htree_fin := htree.with_finite hV hElift
  have haux : ∀ {G' : Graph α (β ⊕ ℕ)},
      GM16.HasTreeStructureOver
        {H ∈ {H : Graph α (β ⊕ ℕ) | IsPlanar H ∨ Nonempty (Iso H GM16.wagnerGraphV8)} |
          V(H).Finite ∧ E(H).Finite} G' →
      V(G').Finite → E(G').Finite →
      ¬ IsIsoMinor (GM16.completeGraph 5) G' := by
    intro G' h hVG' hEG'
    induction h with
    | base hG' =>
      rcases hG'.1 with hP | ⟨eV8⟩
      · exact not_isIsoMinor_completeGraph_five_of_isPlanar hP
      · exact not_isIsoMinor_completeGraph_five_of_iso_wagnerGraphV8 eV8
    | cliqueSum hsum _ _ ih₁ ih₂ =>
      obtain ⟨⟨hV₁, hE₁⟩, ⟨hV₂, hE₂⟩⟩ := hsum.finite_of_finite hVG' hEG'
      exact not_isIsoMinor_completeGraph_of_isCliqueSum hsum hVG' hEG' (ih₁ hV₁ hE₁) (ih₂ hV₂ hE₂)
  intro hm
  exact haux htree_fin hV hElift (Iso.isIsoMinor_right hm (GM16.iso_liftEdgeInl G))

/-! ### Small-Case Sanity Checks -/

/-- Small case 1: both sides of Wagner's characterization hold for the null graph `⊥`. -/
theorem smallCase_bot :
    ¬ IsIsoMinor (GM16.completeGraph 5) (⊥ : Graph α β) ∧
      GM16.HasTreeStructureOver
        {H : Graph α (β ⊕ ℕ) | IsPlanar H ∨ Nonempty (Iso H GM16.wagnerGraphV8)}
        (GM16.liftEdgeInl (⊥ : Graph α β)) := by
  have hP : IsPlanar (GM16.liftEdgeInl (⊥ : Graph α β)) :=
    isPlanar_of_iso (GM16.iso_liftEdgeInl (⊥ : Graph α β)).symm (isPlanar_bot α β)
  exact ⟨not_isIsoMinor_completeGraph_five_of_isPlanar (isPlanar_bot α β), .base (Or.inl hP)⟩

/-- Small case 2: both sides hold for one vertex with a single loop. -/
theorem smallCase_single_loop {G : Graph α β} {v : α} {e : β}
    (hV : V(G) = {v}) (hE : E(G) = {e}) (hloop : G.IsLoopAt e v) :
    ¬ IsIsoMinor (GM16.completeGraph 5) G ∧
      GM16.HasTreeStructureOver
        {H : Graph α (β ⊕ ℕ) | IsPlanar H ∨ Nonempty (Iso H GM16.wagnerGraphV8)}
        (GM16.liftEdgeInl G) := by
  have hPG : IsPlanar G := isPlanar_of_single_loop hV hE hloop
  have hPlift : IsPlanar (GM16.liftEdgeInl G) :=
    isPlanar_of_iso (GM16.iso_liftEdgeInl G).symm hPG
  exact ⟨not_isIsoMinor_completeGraph_five_of_isPlanar hPG, .base (Or.inl hPlift)⟩

/-- Small case 3: both sides hold for `K_4`. -/
theorem smallCase_K4 :
    ¬ IsIsoMinor (GM16.completeGraph 5) (GM16.completeGraph 4) ∧
      GM16.HasTreeStructureOver
        {H : Graph (Fin 4) (Sym2 (Fin 4) ⊕ ℕ) | IsPlanar H ∨ Nonempty (Iso H GM16.wagnerGraphV8)}
        (GM16.liftEdgeInl (GM16.completeGraph 4)) := by
  have hPK4 : IsPlanar (GM16.completeGraph 4) := isPlanar_completeGraph_of_le_four (by decide)
  have hPlift : IsPlanar (GM16.liftEdgeInl (GM16.completeGraph 4)) :=
    isPlanar_of_iso (GM16.iso_liftEdgeInl (GM16.completeGraph 4)).symm hPK4
  exact ⟨not_isIsoMinor_completeGraph_five_of_isPlanar hPK4, .base (Or.inl hPlift)⟩

/-- Small case 4: both sides hold for `V_8` itself. -/
theorem smallCase_V8 :
    ¬ IsIsoMinor (GM16.completeGraph 5) GM16.wagnerGraphV8 ∧
      GM16.HasTreeStructureOver
        {H : Graph (Fin 8) (Fin 12 ⊕ ℕ) | IsPlanar H ∨ Nonempty (Iso H GM16.wagnerGraphV8)}
        (GM16.liftEdgeInl GM16.wagnerGraphV8) :=
  ⟨not_isIsoMinor_completeGraph_five_wagnerGraphV8,
    .base (Or.inr ⟨(GM16.iso_liftEdgeInl GM16.wagnerGraphV8).symm⟩)⟩

end GraphMinor.Wagner
