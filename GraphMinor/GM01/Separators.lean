module

public import GraphMinor.GM01.Defs
public import GraphMinor.GM01.Basic
public import GraphMinor.GM01.Contraction
import GraphMinor.GM01.UniquePaths

/-!
# Graph Minors I, (2.7): Connected Subgraphs Separating Two Vertex Sets

This file formalizes (2.7) of Robertson and Seymour, *Graph Minors I. Excluding a forest*
(pages 47–48), together with the shared reduction lemmas for minimal counterexamples in (2.7) and
(2.8):
* `Path.eq_of_toSubgraph_le` and `isUniqueDisjointPathFamily_of_edgeSet_subset`: uniqueness of a
  disjoint path family when the union of its edge sets is fixed.
* `separates_contractSubgraph`, `Separates.of_le`, `Separates.mono_endpoints`: preservation of
  vertex separation under contracting a connected subgraph or deleting edges or vertices.
* `numComponents_contractSubgraphMap_le`: behavior of `numComponents` under edge contraction.
* `GM01.theorem_2_7`: if there are `m` disjoint paths in `G ∈ 𝓕_θ` from `A₁` to `A₂` and
  `B₁, …, Bₙ` are disjoint connected subgraphs of `G` each separating `A₁` and `A₂`, then
  `m < θ ^ 2 / 2` or `n < θ ^ (2 * θ)`.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph Set

variable {α : Type*}

/-! ### Uniqueness of paths in a path subgraph and uniqueness of disjoint path families -/

private lemma walk_eq_of_isPath_of_toSubgraph_le {u v : α}
    (p q : (⊤ : SimpleGraph α).Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hle : q.toSubgraph ≤ p.toSubgraph) : q = p := by
  induction p with
  | @nil u =>
    cases q with
    | nil => rfl
    | @cons _ w _ hadj q' =>
      have hadj_q : (Walk.cons hadj q').toSubgraph.Adj u w :=
        Subgraph.sup_adj.2 (Or.inl (by simp))
      have hadj_p : (Walk.nil : (⊤ : SimpleGraph α).Walk u u).toSubgraph.Adj u w :=
        hle.2 hadj_q
      have hne : u ≠ w := hadj.ne
      rw [Walk.toSubgraph, singletonSubgraph_adj] at hadj_p
      exact hadj_p.elim
  | @cons u x v hadj p' ih =>
    have hp_cons : (Walk.cons hadj p').IsPath := hp
    rw [Walk.cons_isPath_iff] at hp_cons
    rcases hp_cons with ⟨hp', hu_not_p'⟩
    cases q with
    | nil =>
      exact (hu_not_p' (Walk.end_mem_support p')).elim
    | @cons _ y _ hadj_q q' =>
      have hq_cons : (Walk.cons hadj_q q').IsPath := hq
      rw [Walk.cons_isPath_iff] at hq_cons
      rcases hq_cons with ⟨hq', hu_not_q'⟩
      have hadj_uy : (Walk.cons hadj p').toSubgraph.Adj u y :=
        hle.2 (Subgraph.sup_adj.2 (Or.inl (by simp)))
      change ((⊤ : SimpleGraph α).subgraphOfAdj hadj ⊔ p'.toSubgraph).Adj u y at hadj_uy
      rw [Subgraph.sup_adj, subgraphOfAdj_adj] at hadj_uy
      have hyx : y = x := by
        rcases hadj_uy with heq | hadj_p'
        · rw [Sym2.eq_iff] at heq
          rcases heq with ⟨_, rfl⟩ | ⟨_, heq2⟩
          · rfl
          · exact (hadj.ne heq2.symm).elim
        · have hu_mem : u ∈ p'.support := (Walk.mem_verts_toSubgraph p').1 hadj_p'.fst_mem
          exact (hu_not_p' hu_mem).elim
      subst hyx
      have hq'_le : q'.toSubgraph ≤ p'.toSubgraph := by
        refine ⟨fun z hz ↦ ?_, fun a b hab ↦ ?_⟩
        · have hz_q : z ∈ q'.support := (Walk.mem_verts_toSubgraph q').1 hz
          have hz_ne_u : z ≠ u := fun heq ↦ hu_not_q' (heq ▸ hz_q)
          have hz_cons : z ∈ (Walk.cons hadj p').toSubgraph.verts :=
            hle.1 (Or.inr hz)
          change z ∈ ((⊤ : SimpleGraph α).subgraphOfAdj hadj).verts ∪ p'.toSubgraph.verts at hz_cons
          rw [subgraphOfAdj_verts, mem_union, mem_insert_iff, mem_singleton_iff] at hz_cons
          rcases hz_cons with (rfl | rfl) | hz_p'
          · exact (hz_ne_u rfl).elim
          · exact (Walk.mem_verts_toSubgraph p').2 p'.start_mem_support
          · exact hz_p'
        · have hab_cons : (Walk.cons hadj p').toSubgraph.Adj a b :=
            hle.2 (Subgraph.sup_adj.2 (Or.inr hab))
          change ((⊤ : SimpleGraph α).subgraphOfAdj hadj ⊔ p'.toSubgraph).Adj a b at hab_cons
          rw [Subgraph.sup_adj, subgraphOfAdj_adj] at hab_cons
          rcases hab_cons with heq | hab_p'
          · rw [Sym2.eq_iff] at heq
            rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact (hu_not_q' ((Walk.mem_verts_toSubgraph q').1 hab.fst_mem)).elim
            · exact (hu_not_q' ((Walk.mem_verts_toSubgraph q').1 hab.snd_mem)).elim
          · exact hab_p'
      rw [ih q' hp' hq' hq'_le]

lemma Path.eq_of_toSubgraph_le {P Q : Path α} (hfirst : Q.first = P.first)
    (hlast : Q.last = P.last) (hle : Q.toSubgraph ≤ P.toSubgraph) : Q = P := by
  rcases P with ⟨u₁, v₁, p, hp⟩
  rcases Q with ⟨u₂, v₂, q, hq⟩
  dsimp at hfirst hlast
  subst hfirst hlast
  congr
  exact walk_eq_of_isPath_of_toSubgraph_le p q hp hq hle

/-- If `P` is a family of `m` disjoint paths in `G` with `A₁ = range (first ∘ P)` and
`A₂ = range (last ∘ P)`, and every family `P'` of `m` disjoint paths in `G` from `A₁` to `A₂` has
its edges contained in `⋃ i, (P i).edgeSet`, then `P` is the unique family of `m` disjoint paths in
`G` from `A₁` to `A₂`. -/
lemma isUniqueDisjointPathFamily_of_edgeSet_subset {G : (⊤ : SimpleGraph α).Subgraph} {m : ℕ}
    (P : Fin m → Path α)
    (hP_fam : IsDisjointPathFamily G (Set.range fun i ↦ (P i).first)
      (Set.range fun i ↦ (P i).last) P)
    (hP_edges : ∀ P' : Fin m → Path α,
      IsDisjointPathFamily G (Set.range fun i ↦ (P i).first)
        (Set.range fun i ↦ (P i).last) P' →
      (⋃ k, (P' k).edgeSet) ⊆ ⋃ i, (P i).edgeSet) :
    IsUniqueDisjointPathFamily G (Set.range fun i ↦ (P i).first)
      (Set.range fun i ↦ (P i).last) P := by
  classical
  refine ⟨hP_fam, fun P' hP'_fam ↦ ?_⟩
  have hsub_edges := hP_edges P' hP'_fam
  have hex_i : ∀ k : Fin m, ∃ i : Fin m, P' k = P i := by
    intro k
    rcases (hP'_fam.1 k).2.1 with ⟨i, hi_first⟩
    refine ⟨i, ?_⟩
    have hwalk_le :
        ∀ {u v : α} (w : (⊤ : SimpleGraph α).Walk u v),
          w.toSubgraph ≤ (P' k).toSubgraph → u ∈ (P i).verts → w.toSubgraph ≤ (P i).toSubgraph := by
      intro u v w hw_le hu_i
      induction w with
      | nil =>
        rw [Walk.toSubgraph, singletonSubgraph_le_iff]
        exact hu_i
      | @cons u x v hadj w' ih =>
        have hux_P' : (P' k).toSubgraph.Adj u x :=
          hw_le.2 (Subgraph.sup_adj.2 (Or.inl (by simp)))
        have hux_mem : s(u, x) ∈ ⋃ i', (P i').edgeSet :=
          hsub_edges (mem_iUnion.2 ⟨k, hux_P'⟩)
        rcases mem_iUnion.1 hux_mem with ⟨i', hi'_adj⟩
        change (P i').toSubgraph.Adj u x at hi'_adj
        have hi'_eq : i' = i := by
          by_contra hne
          exact (hP_fam.2 hne).notMem_of_mem_left hi'_adj.fst_mem hu_i
        subst hi'_eq
        have hx_i : x ∈ (P i').verts := hi'_adj.snd_mem
        have hw'_le : w'.toSubgraph ≤ (P' k).toSubgraph :=
          (le_sup_right : w'.toSubgraph ≤ _).trans hw_le
        change (⊤ : SimpleGraph α).subgraphOfAdj hadj ⊔ w'.toSubgraph ≤ (P i').toSubgraph
        exact sup_le (subgraphOfAdj_le_of_adj _ hi'_adj) (ih hw'_le hx_i)
    have hle_i : (P' k).toSubgraph ≤ (P i).toSubgraph :=
      hwalk_le (P' k).walk le_rfl (hi_first ▸ (P i).first_mem_verts)
    rcases (hP'_fam.1 k).2.2 with ⟨i₂, hi₂_last⟩
    have hi₂_eq : i₂ = i := by
      by_contra hne
      have hmem₁ : (P' k).last ∈ (P i₂).verts := hi₂_last ▸ (P i₂).last_mem_verts
      have hmem₂ : (P' k).last ∈ (P i).verts := hle_i.1 (P' k).last_mem_verts
      exact (hP_fam.2 hne).notMem_of_mem_left hmem₁ hmem₂
    subst hi₂_eq
    exact Path.eq_of_toSubgraph_le hi_first.symm hi₂_last.symm hle_i
  choose f hf using hex_i
  have hf_inj : Function.Injective f := by
    intro k₁ k₂ heq
    by_contra hne
    have hmem₁ : (P (f k₁)).first ∈ (P' k₁).verts := by
      rw [← hf k₁]
      exact (P' k₁).first_mem_verts
    have hmem₂ : (P (f k₁)).first ∈ (P' k₂).verts := by
      rw [heq, ← hf k₂]
      exact (P' k₂).first_mem_verts
    exact (hP'_fam.2 hne).notMem_of_mem_left hmem₁ hmem₂
  have hf_surj : Function.Surjective f := Finite.surjective_of_injective hf_inj
  ext Q
  simp only [mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨f k, (hf k).symm⟩
  · rintro ⟨i, rfl⟩
    rcases hf_surj i with ⟨k, rfl⟩
    exact ⟨k, hf k⟩

/-! ### Separation and `numComponents` under contraction and deletion -/

lemma Separates.mono_endpoints {G : (⊤ : SimpleGraph α).Subgraph} {S A₁ A₂ A₁' A₂' : Set α}
    (hsep : Separates G S A₁ A₂) (h₁ : A₁' ⊆ A₁) (h₂ : A₂' ⊆ A₂) :
    Separates G S A₁' A₂' :=
  fun P ⟨hP_le, hP_1, hP_2⟩ ↦ hsep P ⟨hP_le, h₁ hP_1, h₂ hP_2⟩

lemma Separates.of_le {G H : (⊤ : SimpleGraph α).Subgraph} (hle : H ≤ G) {S A₁ A₂ : Set α}
    (hsep : Separates G S A₁ A₂) : Separates H S A₁ A₂ :=
  fun P ⟨hP_le, hP_1, hP_2⟩ ↦ hsep P ⟨hP_le.trans hle, hP_1, hP_2⟩

lemma toSubgraph_le_deleteVerts_iff {G H : (⊤ : SimpleGraph α).Subgraph} {S : Set α} :
    H ≤ G.deleteVerts S ↔ H ≤ G ∧ Disjoint H.verts S := by
  constructor
  · intro h
    refine ⟨h.trans G.deleteVerts_le, ?_⟩
    rw [Set.disjoint_left]
    intro x hx
    exact (h.1 hx).2
  · rintro ⟨hH_le, hdisj⟩
    refine ⟨fun x hx ↦ ⟨hH_le.1 hx, hdisj.notMem_of_mem_left hx⟩, fun x y hxy ↦ ?_⟩
    rw [Subgraph.deleteVerts_adj]
    exact ⟨hH_le.1 hxy.fst_mem, hdisj.notMem_of_mem_left hxy.fst_mem,
      hH_le.1 hxy.snd_mem, hdisj.notMem_of_mem_left hxy.snd_mem, hH_le.2 hxy⟩

/-- Contracting a preconnected subgraph `C ≤ G` into `u₀ ∈ C.verts` preserves separation. -/
lemma separates_contractSubgraph {G C : (⊤ : SimpleGraph α).Subgraph} {u₀ : α}
    (hC_le : C ≤ G) (hC_conn : C.Preconnected) (hu₀ : u₀ ∈ C.verts)
    {S A₁ A₂ : Set α} (hA₁ : A₁ ⊆ G.verts) (hA₂ : A₂ ⊆ G.verts)
    (hsep : Separates G S A₁ A₂) :
    Separates (contractSubgraph G C u₀)
      (contractMap C.verts u₀ '' S)
      (contractMap C.verts u₀ '' A₁)
      (contractMap C.verts u₀ '' A₂) := by
  let G' := contractSubgraph G C u₀
  let f := contractMap C.verts u₀
  have hsame_fiber :
      ∀ {a₁ a₂ : α}, a₁ ∈ G.verts → a₂ ∈ G.verts → f a₁ = f a₂ → f a₁ ∉ f '' S →
        ∃ p : (⊤ : SimpleGraph α).Walk a₁ a₂, p.toSubgraph ≤ G.deleteVerts S := by
    intro a₁ a₂ ha₁ ha₂ hfeq hnot_S
    have ha₁_not_S : a₁ ∉ S := fun h ↦ hnot_S ⟨a₁, h, rfl⟩
    by_cases heq : a₁ = a₂
    · subst heq
      refine ⟨.nil, ?_⟩
      rw [Walk.toSubgraph, singletonSubgraph_le_iff]
      exact ⟨ha₁, ha₁_not_S⟩
    · have ha₁_C : a₁ ∈ C.verts := by
        by_contra hnot₁
        have h1 : f a₁ = a₁ := contractMap_of_notMem hnot₁
        by_cases ha₂_C : a₂ ∈ C.verts
        · have h2 : f a₂ = u₀ := contractMap_of_mem ha₂_C
          rw [h1, h2] at hfeq
          exact hnot₁ (hfeq ▸ hu₀)
        · have h2 : f a₂ = a₂ := contractMap_of_notMem ha₂_C
          rw [h1, h2] at hfeq
          exact heq hfeq
      have ha₂_C : a₂ ∈ C.verts := by
        by_contra hnot₂
        have h1 : f a₁ = u₀ := contractMap_of_mem ha₁_C
        have h2 : f a₂ = a₂ := contractMap_of_notMem hnot₂
        rw [h1, h2] at hfeq
        exact hnot₂ (hfeq.symm ▸ hu₀)
      have hC_disj_S : Disjoint C.verts S := by
        rw [Set.disjoint_left]
        intro c hc hs
        apply hnot_S
        refine ⟨c, hs, ?_⟩
        change contractMap C.verts u₀ c = contractMap C.verts u₀ a₁
        rw [contractMap_of_mem hc, contractMap_of_mem ha₁_C]
      have hC_le_del : C ≤ G.deleteVerts S :=
        toSubgraph_le_deleteVerts_iff.2 ⟨hC_le, hC_disj_S⟩
      rcases (Subgraph.preconnected_iff_forall_exists_walk_subgraph C).1 hC_conn ha₁_C ha₂_C with
        ⟨p, hp⟩
      exact ⟨p, hp.trans hC_le_del⟩
  have hlift_walk :
      ∀ {x y : α} (w : (⊤ : SimpleGraph α).Walk x y),
        w.toSubgraph ≤ G' → Disjoint w.toSubgraph.verts (f '' S) →
        ∀ {a b : α}, a ∈ G.verts → b ∈ G.verts → f a = x → f b = y →
          ∃ p : (⊤ : SimpleGraph α).Walk a b, p.toSubgraph ≤ G.deleteVerts S := by
    intro x y w hw_le hw_disj
    induction w with
    | @nil x =>
      intro a b ha hb hfa hfb
      have hx_not_S : x ∉ f '' S :=
        hw_disj.notMem_of_mem_left (by simp [Walk.toSubgraph])
      exact hsame_fiber ha hb (hfa.trans hfb.symm) (hfa.symm ▸ hx_not_S)
    | @cons x y z hadj w' ih =>
      intro a b ha hb hfa hfb
      have hxy_G' : G'.Adj x y := hw_le.2 (Subgraph.sup_adj.2 (Or.inl (by simp)))
      rcases hxy_G'.2.2.2 with ⟨a', b', hfa', hfb', hab'_G⟩
      have hx_mem : x ∈ (Walk.cons hadj w').toSubgraph.verts :=
        Or.inl (Or.inl rfl)
      have hy_mem : y ∈ (Walk.cons hadj w').toSubgraph.verts :=
        Or.inl (Or.inr rfl)
      have hx_not_S : x ∉ f '' S := hw_disj.notMem_of_mem_left hx_mem
      have hy_not_S : y ∉ f '' S := hw_disj.notMem_of_mem_left hy_mem
      have ha'_G : a' ∈ G.verts := hab'_G.fst_mem
      have hb'_G : b' ∈ G.verts := hab'_G.snd_mem
      have ha'_not_S : a' ∉ S := fun h ↦ hx_not_S ⟨a', h, hfa'⟩
      have hb'_not_S : b' ∉ S := fun h ↦ hy_not_S ⟨b', h, hfb'⟩
      have hab'_del : (G.deleteVerts S).Adj a' b' := by
        rw [Subgraph.deleteVerts_adj]
        exact ⟨ha'_G, ha'_not_S, hb'_G, hb'_not_S, hab'_G⟩
      rcases hsame_fiber ha ha'_G (hfa.trans hfa'.symm) (hfa.symm ▸ hx_not_S) with ⟨p₁, hp₁⟩
      have hw'_le : w'.toSubgraph ≤ G' := (le_sup_right : w'.toSubgraph ≤ _).trans hw_le
      have hw'_disj : Disjoint w'.toSubgraph.verts (f '' S) :=
        hw_disj.mono_left (le_sup_right : w'.toSubgraph ≤ _).1
      rcases ih hw'_le hw'_disj hb'_G hb hfb' hfb with ⟨p₂, hp₂⟩
      refine ⟨p₁.append (Walk.cons ((top_adj a' b').2 hab'_G.ne) p₂), ?_⟩
      rw [Walk.toSubgraph_append]
      exact sup_le hp₁ (sup_le (subgraphOfAdj_le_of_adj _ hab'_del) hp₂)
  intro Q ⟨hQ_le, hQ_first, hQ_last⟩ hQ_avoids
  rcases hQ_first with ⟨a, haA₁, hfa⟩
  rcases hQ_last with ⟨b, hbA₂, hfb⟩
  rcases hlift_walk Q.walk hQ_le hQ_avoids (hA₁ haA₁) (hA₂ hbA₂) hfa hfb with ⟨p, hp⟩
  let P₀ := Path.ofWalk p
  have hP₀_del : P₀.toSubgraph ≤ G.deleteVerts S := (Path.ofWalk_toSubgraph_le p).trans hp
  rcases toSubgraph_le_deleteVerts_iff.1 hP₀_del with ⟨hP₀_le, hP₀_disj⟩
  exact hsep P₀ ⟨hP₀_le, haA₁, hbA₂⟩ hP₀_disj

/-- Contracting a set `C` into `u₀` does not increase the number of connected components of a
finite subgraph `H`. -/
lemma numComponents_contractSubgraphMap_le {C : Set α} {u₀ : α} {H : (⊤ : SimpleGraph α).Subgraph}
    (hH_fin : H.verts.Finite) :
    numComponents (contractSubgraphMap C u₀ H) ≤ numComponents H := by
  let H' := contractSubgraphMap C u₀ H
  have : Finite H.verts := hH_fin.to_subtype
  let : Fintype H.verts := Fintype.ofFinite H.verts
  have : Finite H.coe.ConnectedComponent := Quot.finite _
  let φ_v (x : H.verts) : H'.verts := ⟨contractMap C u₀ x.1, ⟨x.1, x.2, rfl⟩⟩
  have hφ_v_surj : Function.Surjective φ_v := by
    rintro ⟨y, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hφ_reach : ∀ {x y : H.verts}, H.coe.Reachable x y → H'.coe.Reachable (φ_v x) (φ_v y) := by
    intro x y h
    rcases h with ⟨w⟩
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hadj w' ih =>
      by_cases heq : φ_v a = φ_v b
      · rw [heq]
        exact ih
      · have hadj' : H'.coe.Adj (φ_v a) (φ_v b) := by
          have hne_val : (φ_v a).1 ≠ (φ_v b).1 := fun h ↦ heq (Subtype.ext h)
          exact ⟨hne_val, a.1, b.1, rfl, rfl, hadj⟩
        exact hadj'.reachable.trans ih
  let Φ : H.coe.ConnectedComponent → H'.coe.ConnectedComponent :=
    Quot.lift (fun x ↦ H'.coe.connectedComponentMk (φ_v x)) (fun x y h ↦
      SimpleGraph.ConnectedComponent.eq.2 (hφ_reach h))
  have hΦ_surj : Function.Surjective Φ := by
    intro c'
    rcases Quot.exists_rep c' with ⟨y, rfl⟩
    rcases hφ_v_surj y with ⟨x, rfl⟩
    exact ⟨H.coe.connectedComponentMk x, rfl⟩
  exact Nat.card_le_card_of_surjective Φ hΦ_surj

/-! ### Endpoints of `contractSubpath` and 1-edge subpaths -/

lemma Path.subpath_verts_of_toSubgraph_adj (P : Path α) {u v : α}
    (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v)
    (hadj : P.toSubgraph.Adj u v) :
    (P.subpath u v hu hv (Or.inl huv)).verts = {u, v} := by
  ext x
  rw [P.mem_subpath_verts_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨_, hux | rfl, hxv | rfl⟩
    · exact (P.not_toSubgraph_adj_of_precedes_precedes hux hxv hadj).elim
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨hu, Or.inr rfl, Or.inl huv⟩
    · exact ⟨hv, Or.inl huv, Or.inr rfl⟩

lemma Path.contractSubpath_first_eq_contractMap (P : Path α) (u v : α)
    (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v) :
    (P.contractSubpath u v hu hv huv).first =
      contractMap (P.subpath u v hu hv (Or.inl huv)).verts u P.first := by
  rw [P.contractSubpath_first]
  let R := P.subpath u v hu hv (Or.inl huv)
  by_cases hmem : P.first ∈ R.verts
  · rw [contractMap_of_mem hmem]
    change P.first ∈ (P.subpath u v hu hv (Or.inl huv)).verts at hmem
    rw [P.mem_subpath_verts_iff] at hmem
    rcases hmem.2.1 with hprec | rfl
    · exact (P.not_precedes_first hprec).elim
    · rfl
  · rw [contractMap_of_notMem hmem]

lemma Path.contractSubpath_last_eq_contractMap (P : Path α) (u v : α)
    (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v) :
    (P.contractSubpath u v hu hv huv).last =
      contractMap (P.subpath u v hu hv (Or.inl huv)).verts u P.last := by
  let Q := P.contractSubpath u v hu hv huv
  let R := P.subpath u v hu hv (Or.inl huv)
  have hQ_last_mem : Q.last ∈ Q.verts := Q.last_mem_verts
  rw [P.contractSubpath_verts u v hu hv huv] at hQ_last_mem
  rcases hQ_last_mem with ⟨a, haP, hfa⟩
  by_contra hne
  have ha_ne_last : a ≠ P.last := fun heq ↦ hne (hfa.symm.trans (congrArg _ heq))
  have ha_prec : P.Precedes a P.last := by
    rcases P.precedes_or_eq_or_precedes haP P.last_mem_verts with hprec | heq | hprec
    · exact hprec
    · exact (ha_ne_last heq).elim
    · exact (P.not_last_precedes hprec).elim
  have hQ_prec : Q.Precedes (contractMap R.verts u a) (contractMap R.verts u P.last) :=
    P.contractSubpath_precedes_of_precedes u v hu hv huv haP P.last_mem_verts ha_prec
      (hfa.symm ▸ hne)
  rw [hfa] at hQ_prec
  exact Q.not_last_precedes hQ_prec

lemma exists_precedes_of_path_edgeSet {P : Path α} {e : Sym2 α} (he : e ∈ P.edgeSet) :
    ∃ u v, e = s(u, v) ∧ u ∈ P.verts ∧ v ∈ P.verts ∧ P.Precedes u v ∧ P.toSubgraph.Adj u v := by
  induction e using Sym2.ind with
  | _ x y =>
    have hadj : P.toSubgraph.Adj x y := he
    have hx : x ∈ P.verts := hadj.fst_mem
    have hy : y ∈ P.verts := hadj.snd_mem
    rcases P.precedes_or_eq_or_precedes hx hy with hprec | rfl | hprec
    · exact ⟨x, y, rfl, hx, hy, hprec, hadj⟩
    · exact (hadj.ne rfl).elim
    · exact ⟨y, x, Sym2.eq_swap, hy, hx, hprec, hadj.symm⟩

/-! ### Shared reduction step: contracting an edge in `E(P_{i₀}) ∩ E(B_{j₀})` -/

/-- If `e ∈ (P i₀).edgeSet ∩ (B j₀).edgeSet`, contracting `e` produces a smaller graph `G'` in `𝓕 θ`
with disjoint paths `P'` avoiding `X` and disjoint subgraphs `B'` separating `A₁'` and `A₂'`. -/
lemma contract_shared_path_subgraph_edge {θ m n : ℕ}
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    {A₁ A₂ X : Set α} (hA₁ : A₁ ⊆ G.verts) (hA₂ : A₂ ⊆ G.verts) (hX : X ⊆ G.verts)
    (P : Fin m → Path α) (hP_fam : IsDisjointPathFamily G A₁ A₂ P)
    (hP_avoids : ∀ i, (P i).Avoids X)
    (B : Fin n → (⊤ : SimpleGraph α).Subgraph) (hB_le : ∀ j, B j ≤ G)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hB_sep : ∀ j, Separates G (X ∪ (B j).verts) A₁ A₂)
    {i₀ : Fin m} {j₀ : Fin n} {e : Sym2 α}
    (heP : e ∈ (P i₀).edgeSet) (heB : e ∈ (B j₀).edgeSet) :
    ∃ (G' : (⊤ : SimpleGraph α).Subgraph) (A₁' A₂' : Set α)
      (P' : Fin m → Path α) (B' : Fin n → (⊤ : SimpleGraph α).Subgraph),
      G'.verts.Finite ∧ G' ∈ 𝓕 θ ∧
      G'.verts.ncard < G.verts.ncard ∧ G'.edgeSet.ncard ≤ G.edgeSet.ncard ∧
      A₁' ⊆ G'.verts ∧ A₂' ⊆ G'.verts ∧ X ⊆ G'.verts ∧
      IsDisjointPathFamily G' A₁' A₂' P' ∧ (∀ i, (P' i).Avoids X) ∧
      (∀ j, B' j ≤ G') ∧
      (∀ j, (B j).Connected → (B' j).Connected) ∧
      (∀ j, numComponents (B' j) ≤ numComponents (B j)) ∧
      Pairwise (fun j j' ↦ Disjoint (B' j).verts (B' j').verts) ∧
      (∀ j, Separates G' (X ∪ (B' j).verts) A₁' A₂') := by
  classical
  rcases exists_precedes_of_path_edgeSet heP with ⟨u₀, v₀, rfl, hu₀P, hv₀P, huv_prec, hadj_P⟩
  have hadj_B : (B j₀).Adj u₀ v₀ := heB
  let R := (P i₀).subpath u₀ v₀ hu₀P hv₀P (Or.inl huv_prec)
  let C := R.toSubgraph
  have hC_verts : C.verts = {u₀, v₀} :=
    (P i₀).subpath_verts_of_toSubgraph_adj hu₀P hv₀P huv_prec hadj_P
  have hu₀_C : u₀ ∈ C.verts := by rw [hC_verts]; simp
  have hv₀_C : v₀ ∈ C.verts := by rw [hC_verts]; simp
  have hC_le_P : C ≤ (P i₀).toSubgraph := (P i₀).subpath_toSubgraph_le _ _ _
  have hC_le_G : C ≤ G := hC_le_P.trans (hP_fam.1 i₀).1
  have hC_conn : C.Connected := R.connected_toSubgraph
  let G' := contractSubgraph G C u₀
  let f := contractMap C.verts u₀
  have hC_sub_Pi₀ : C.verts ⊆ (P i₀).verts := hC_le_P.1
  have hC_sub_Bj₀ : C.verts ⊆ (B j₀).verts := by
    rw [hC_verts]
    intro x hx
    rcases mem_insert_iff.1 hx with rfl | hx'
    · exact hadj_B.fst_mem
    · rw [mem_singleton_iff.1 hx']
      exact hadj_B.snd_mem
  have hC_disj_X : Disjoint C.verts X :=
    (hP_avoids i₀).mono_left hC_sub_Pi₀
  let A₁' := f '' A₁
  let A₂' := f '' A₂
  have hX'_eq : f '' X = X := by
    ext x
    simp only [f, mem_image]
    constructor
    · rintro ⟨a, haX, rfl⟩
      have ha_not_C : a ∉ C.verts := hC_disj_X.symm.notMem_of_mem_left haX
      rw [contractMap_of_notMem ha_not_C]
      exact haX
    · intro hxX
      have hx_not_C : x ∉ C.verts := hC_disj_X.symm.notMem_of_mem_left hxX
      exact ⟨x, hxX, contractMap_of_notMem hx_not_C⟩
  let P' (i : Fin m) : Path α :=
    if i = i₀ then (P i₀).contractSubpath u₀ v₀ hu₀P hv₀P huv_prec else P i
  let B' (j : Fin n) : (⊤ : SimpleGraph α).Subgraph :=
    contractSubgraphMap C.verts u₀ (B j)
  have hP'_verts : ∀ i, (P' i).verts = f '' (P i).verts := by
    intro i
    dsimp [P', f]
    split_ifs with hi
    · subst hi
      exact (P i).contractSubpath_verts u₀ v₀ hu₀P hv₀P huv_prec
    · have hdisj_i : Disjoint (P i).verts C.verts :=
        (hP_fam.2 hi).mono_right hC_sub_Pi₀
      ext x
      simp only [mem_image]
      constructor
      · intro hx
        exact ⟨x, hx, contractMap_of_notMem (hdisj_i.notMem_of_mem_left hx)⟩
      · rintro ⟨a, ha, rfl⟩
        rwa [contractMap_of_notMem (hdisj_i.notMem_of_mem_left ha)]
  refine ⟨G', A₁', A₂', P', B',
    contractSubgraph_verts_finite hfin C u₀,
    mem_𝓕_contractSubgraph hfin hG hC_le_G hC_conn hu₀_C,
    ncard_verts_contractSubgraph_lt hfin hC_le_G hv₀_C huv_prec.ne.symm,
    ncard_edgeSet_contractSubgraph_le hfin u₀,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact contractMap_mem_sdiff (hC_le_G.1 hu₀_C) (hA₁ ha)
  · rintro _ ⟨a, ha, rfl⟩
    exact contractMap_mem_sdiff (hC_le_G.1 hu₀_C) (hA₂ ha)
  · rw [← hX'_eq]
    rintro _ ⟨a, haX, rfl⟩
    exact contractMap_mem_sdiff (hC_le_G.1 hu₀_C) (hX haX)
  · refine ⟨fun i ↦ ?_, fun i₁ i₂ hne ↦ ?_⟩
    · dsimp [P']
      split_ifs with hi
      · subst hi
        refine ⟨(P i).contractSubpath_toSubgraph_le (hP_fam.1 i).1 u₀ v₀ hu₀P hv₀P huv_prec,
          ?_, ?_⟩
        · rw [(P i).contractSubpath_first_eq_contractMap u₀ v₀ hu₀P hv₀P huv_prec]
          exact ⟨(P i).first, (hP_fam.1 i).2.1, rfl⟩
        · rw [(P i).contractSubpath_last_eq_contractMap u₀ v₀ hu₀P hv₀P huv_prec]
          exact ⟨(P i).last, (hP_fam.1 i).2.2, rfl⟩
      · have hdisj_i : Disjoint (P i).verts C.verts :=
          (hP_fam.2 hi).mono_right hC_sub_Pi₀
        refine ⟨le_contractSubgraph_of_disjoint (hP_fam.1 i).1
          (hdisj_i.mono_right sdiff_subset), ?_, ?_⟩
        · refine ⟨(P i).first, (hP_fam.1 i).2.1, ?_⟩
          exact contractMap_of_notMem (hdisj_i.notMem_of_mem_left (P i).first_mem_verts)
        · refine ⟨(P i).last, (hP_fam.1 i).2.2, ?_⟩
          exact contractMap_of_notMem (hdisj_i.notMem_of_mem_left (P i).last_mem_verts)
    · change Disjoint (P' i₁).verts (P' i₂).verts
      rw [hP'_verts i₁, hP'_verts i₂]
      change Disjoint (contractSubgraphMap C.verts u₀ (P i₁).toSubgraph).verts
        (contractSubgraphMap C.verts u₀ (P i₂).toSubgraph).verts
      have hdisj_C : Disjoint (P i₁).verts C.verts ∨ Disjoint (P i₂).verts C.verts := by
        by_cases h₁ : i₁ = i₀
        · subst h₁
          exact Or.inr ((hP_fam.2 hne.symm).mono_right hC_sub_Pi₀)
        · exact Or.inl ((hP_fam.2 h₁).mono_right hC_sub_Pi₀)
      exact contractSubgraphMap_disjoint (hP_fam.2 hne) hdisj_C hu₀_C
  · intro i
    rw [Path.Avoids, hP'_verts i, Set.disjoint_left]
    rintro _ ⟨a, haP, rfl⟩ hxX
    dsimp [f] at hxX
    by_cases haC : a ∈ C.verts
    · rw [contractMap_of_mem haC] at hxX
      exact hC_disj_X.notMem_of_mem_left hu₀_C hxX
    · rw [contractMap_of_notMem haC] at hxX
      exact (hP_avoids i).notMem_of_mem_left haP hxX
  · intro j
    exact contractSubgraphMap_le (hC_le_G.1 hu₀_C) (hB_le j)
  · intro j hconn
    exact contractSubgraphMap_connected hconn
  · intro j
    exact numComponents_contractSubgraphMap_le (hfin.subset (hB_le j).1)
  · intro j₁ j₂ hne
    have hdisj_C : Disjoint (B j₁).verts C.verts ∨ Disjoint (B j₂).verts C.verts := by
      by_cases h₁ : j₁ = j₀
      · subst h₁
        exact Or.inr ((hB_disj hne.symm).mono_right hC_sub_Bj₀)
      · exact Or.inl ((hB_disj h₁).mono_right hC_sub_Bj₀)
    exact contractSubgraphMap_disjoint (hB_disj hne) hdisj_C hu₀_C
  · intro j
    have hsep' := separates_contractSubgraph hC_le_G hC_conn.preconnected hu₀_C hA₁ hA₂ (hB_sep j)
    rwa [Set.image_union, hX'_eq] at hsep'

/-! ### Shared reduction step: contracting an edge incident with `v₀ ∉ X ∪ ⋃ V(P_i)` -/

/-- If `v₀ ∈ G.verts \ (X ∪ ⋃ i, (P i).verts)` is adjacent to `u₀` via an edge of `B j₀`,
contracting `{u₀, v₀}` into `u₀` produces a smaller graph `G'` in `𝓕 θ` while leaving `P`, `A₁`,
`A₂`, and `X` unchanged. -/
lemma contract_outside_vertex_edge {θ m n : ℕ}
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    {A₁ A₂ X : Set α} (P : Fin m → Path α)
    (hA₁ : A₁ ⊆ ⋃ i, (P i).verts) (hA₂ : A₂ ⊆ ⋃ i, (P i).verts)
    (hX : X ⊆ G.verts)
    (hP_fam : IsDisjointPathFamily G A₁ A₂ P)
    (B : Fin n → (⊤ : SimpleGraph α).Subgraph) (hB_le : ∀ j, B j ≤ G)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hB_sep : ∀ j, Separates G (X ∪ (B j).verts) A₁ A₂)
    {j₀ : Fin n} {u₀ v₀ : α} (hadj_B : (B j₀).Adj u₀ v₀)
    (hv₀_not_X : v₀ ∉ X) (hv₀_not_P : ∀ i, v₀ ∉ (P i).verts) :
    ∃ (G' : (⊤ : SimpleGraph α).Subgraph) (B' : Fin n → (⊤ : SimpleGraph α).Subgraph),
      G'.verts.Finite ∧ G' ∈ 𝓕 θ ∧
      G'.verts.ncard < G.verts.ncard ∧ G'.edgeSet.ncard ≤ G.edgeSet.ncard ∧
      X ⊆ G'.verts ∧
      IsDisjointPathFamily G' A₁ A₂ P ∧
      (∀ j, B' j ≤ G') ∧
      (∀ j, (B j).Connected → (B' j).Connected) ∧
      (∀ j, numComponents (B' j) ≤ numComponents (B j)) ∧
      Pairwise (fun j j' ↦ Disjoint (B' j).verts (B' j').verts) ∧
      (∀ j, Separates G' (X ∪ (B' j).verts) A₁ A₂) := by
  have hadj_G : G.Adj u₀ v₀ := (hB_le j₀).2 hadj_B
  let C := (⊤ : SimpleGraph α).subgraphOfAdj ((top_adj u₀ v₀).2 hadj_G.ne)
  have hC_verts : C.verts = {u₀, v₀} := by simp [C]
  have hu₀_C : u₀ ∈ C.verts := by simp [hC_verts]
  have hv₀_C : v₀ ∈ C.verts := by simp [hC_verts]
  have hC_le_G : C ≤ G := subgraphOfAdj_le_of_adj G hadj_G
  have hC_conn : C.Connected :=
    Subgraph.subgraphOfAdj_connected ((top_adj u₀ v₀).2 hadj_G.ne)
  have hC_sdiff : C.verts \ {u₀} = {v₀} := by
    rw [hC_verts]
    ext x
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, hne⟩
      · exact (hne rfl).elim
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, hadj_G.ne.symm⟩
  have hf_eq_self : ∀ {x : α}, x ≠ v₀ → contractMap C.verts u₀ x = x := by
    intro x hx
    by_cases hxu : x = u₀
    · subst hxu
      exact contractMap_of_mem hu₀_C
    · refine contractMap_of_notMem ?_
      rw [hC_verts, mem_insert_iff, mem_singleton_iff]
      tauto
  have hC_sub_Bj₀ : C.verts ⊆ (B j₀).verts := by
    rw [hC_verts]
    intro x hx
    rcases mem_insert_iff.1 hx with rfl | hx'
    · exact hadj_B.fst_mem
    · rw [mem_singleton_iff.1 hx']
      exact hadj_B.snd_mem
  let G' := contractSubgraph G C u₀
  let B' (j : Fin n) : (⊤ : SimpleGraph α).Subgraph := contractSubgraphMap C.verts u₀ (B j)
  refine ⟨G', B',
    contractSubgraph_verts_finite hfin C u₀,
    mem_𝓕_contractSubgraph hfin hG hC_le_G hC_conn hu₀_C,
    ncard_verts_contractSubgraph_lt hfin hC_le_G hv₀_C hadj_G.ne.symm,
    ncard_edgeSet_contractSubgraph_le hfin u₀,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [contractSubgraph_verts, hC_sdiff, mem_sdiff, mem_singleton_iff]
    exact ⟨hX hx, fun heq ↦ hv₀_not_X (heq ▸ hx)⟩
  · refine ⟨fun i ↦ ⟨?_, (hP_fam.1 i).2.1, (hP_fam.1 i).2.2⟩, hP_fam.2⟩
    refine le_contractSubgraph_of_disjoint (hP_fam.1 i).1 ?_
    rw [hC_sdiff, Set.disjoint_singleton_right]
    exact hv₀_not_P i
  · intro j
    exact contractSubgraphMap_le (hC_le_G.1 hu₀_C) (hB_le j)
  · intro j hconn
    exact contractSubgraphMap_connected hconn
  · intro j
    exact numComponents_contractSubgraphMap_le (hfin.subset (hB_le j).1)
  · intro j₁ j₂ hne
    have hdisj_C : Disjoint (B j₁).verts C.verts ∨ Disjoint (B j₂).verts C.verts := by
      by_cases h₁ : j₁ = j₀
      · subst h₁
        exact Or.inr ((hB_disj hne.symm).mono_right hC_sub_Bj₀)
      · exact Or.inl ((hB_disj h₁).mono_right hC_sub_Bj₀)
    exact contractSubgraphMap_disjoint (hB_disj hne) hdisj_C hu₀_C
  · intro j
    have hA₁_G : A₁ ⊆ G.verts := fun x hx ↦ by
      rcases mem_iUnion.1 (hA₁ hx) with ⟨i, hxi⟩
      exact (hP_fam.1 i).1.1 hxi
    have hA₂_G : A₂ ⊆ G.verts := fun x hx ↦ by
      rcases mem_iUnion.1 (hA₂ hx) with ⟨i, hxi⟩
      exact (hP_fam.1 i).1.1 hxi
    have hsep' := separates_contractSubgraph hC_le_G hC_conn.preconnected hu₀_C hA₁_G hA₂_G (hB_sep j)
    have himg_A₁ : contractMap C.verts u₀ '' A₁ = A₁ := by
      ext x
      simp only [mem_image]
      refine ⟨?_, fun hx ↦ ?_⟩
      · rintro ⟨a, ha, rfl⟩
        rcases mem_iUnion.1 (hA₁ ha) with ⟨i, hai⟩
        rw [hf_eq_self (fun h ↦ hv₀_not_P i (h ▸ hai))]
        exact ha
      · rcases mem_iUnion.1 (hA₁ hx) with ⟨i, hxi⟩
        exact ⟨x, hx, hf_eq_self (fun h ↦ hv₀_not_P i (h ▸ hxi))⟩
    have himg_A₂ : contractMap C.verts u₀ '' A₂ = A₂ := by
      ext x
      simp only [mem_image]
      refine ⟨?_, fun hx ↦ ?_⟩
      · rintro ⟨a, ha, rfl⟩
        rcases mem_iUnion.1 (hA₂ ha) with ⟨i, hai⟩
        rw [hf_eq_self (fun h ↦ hv₀_not_P i (h ▸ hai))]
        exact ha
      · rcases mem_iUnion.1 (hA₂ hx) with ⟨i, hxi⟩
        exact ⟨x, hx, hf_eq_self (fun h ↦ hv₀_not_P i (h ▸ hxi))⟩
    have himg_X : contractMap C.verts u₀ '' X = X := by
      ext x
      simp only [mem_image]
      refine ⟨?_, fun hx ↦ ⟨x, hx, hf_eq_self (fun h ↦ hv₀_not_X (h ▸ hx))⟩⟩
      rintro ⟨a, ha, rfl⟩
      rw [hf_eq_self (fun h ↦ hv₀_not_X (h ▸ ha))]
      exact ha
    rwa [Set.image_union, himg_X, himg_A₁, himg_A₂] at hsep'

/-! ### Proof of (2.7) (pages 47–48) -/

/-- **Graph Minors I, (2.7)** (page 47):
"Suppose that there are $m$ disjoint paths in $G \in \mathscr{F}_\theta$ from $A_1$ to $A_2$, where
$A_1, A_2 \subseteq V(G)$; and that $B_1, \dots, B_n$ are disjoint connected subgraphs of $G$, and
for $1 \le j \le n$, $V(B_j)$ separates $A_1$ and $A_2$. Then either $m < \frac{1}{2}\theta^2$ or
$n < \theta^{2\theta}$."
This is the simple special case. The full statement is `GM01.Full.theorem_2_7_proof`. -/
theorem theorem_2_7_simple {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    {A₁ A₂ : Set α} (hA₁ : A₁ ⊆ G.verts) (hA₂ : A₂ ⊆ G.verts)
    (P : Fin m → Path α) (hP_fam : IsDisjointPathFamily G A₁ A₂ P)
    (B : Fin n → (⊤ : SimpleGraph α).Subgraph) (hB_le : ∀ j, B j ≤ G)
    (hB_conn : ∀ j, (B j).Connected)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hB_sep : ∀ j, Separates G (B j).verts A₁ A₂) :
    m < θ ^ 2 / 2 ∨ n < θ ^ (2 * θ) := by
  classical
  -- Strong induction on `|V(G)| + |E(G)| + m` ("If possible, choose a counterexample with
  -- `|V(G)| + |E(G)| + m` minimum", page 47).
  suffices hind :
      ∀ (N : ℕ) {m : ℕ} {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
        {A₁ A₂ : Set α} (hA₁ : A₁ ⊆ G.verts) (hA₂ : A₂ ⊆ G.verts)
        (P : Fin m → Path α) (hP_fam : IsDisjointPathFamily G A₁ A₂ P)
        (B : Fin n → (⊤ : SimpleGraph α).Subgraph) (hB_le : ∀ j, B j ≤ G)
        (hB_conn : ∀ j, (B j).Connected)
        (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
        (hB_sep : ∀ j, Separates G (B j).verts A₁ A₂),
        G.verts.ncard + G.edgeSet.ncard + m = N →
        m < θ ^ 2 / 2 ∨ n < θ ^ (2 * θ) by
    exact hind _ hfin hG hA₁ hA₂ P hP_fam B hB_le hB_conn hB_disj hB_sep rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro m G hfin hG A₁ A₂ hA₁ hA₂ P hP_fam B hB_le hB_conn hB_disj hB_sep hN
    by_contra hnot
    rcases not_or.1 hnot with ⟨hm_ge, hn_ge⟩
    have hm_ge' : θ ^ 2 / 2 ≤ m := not_lt.1 hm_ge
    -- "Then evidently we have `m = ½ θ²`."
    rcases lt_or_eq_of_le hm_ge' with hm_gt | hm_eq
    · let P' (i : Fin (m - 1)) : Path α := P ⟨i.val, by omega⟩
      have hP'_fam : IsDisjointPathFamily G A₁ A₂ P' :=
        ⟨fun i ↦ hP_fam.1 ⟨i.val, by omega⟩,
          fun i₁ i₂ hne ↦ hP_fam.2 (fun h ↦ hne (Fin.ext (Fin.mk.inj h)))⟩
      have hlt : G.verts.ncard + G.edgeSet.ncard + (m - 1) < N := by omega
      rcases ih _ hlt hfin hG hA₁ hA₂ P' hP'_fam B hB_le hB_conn hB_disj hB_sep rfl with h1 | h2
      · omega
      · exact hn_ge h2
    -- Replace `A₁` and `A₂` by the endpoints of `P₁, …, Pₘ` (which preserves `G`, `P`, `B`, and
    -- the measure `|V(G)| + |E(G)| + m`).
    let A₁₀ : Set α := Set.range fun i ↦ (P i).first
    let A₂₀ : Set α := Set.range fun i ↦ (P i).last
    have hA₁₀_sub : A₁₀ ⊆ A₁ := by rintro _ ⟨i, rfl⟩; exact (hP_fam.1 i).2.1
    have hA₂₀_sub : A₂₀ ⊆ A₂ := by rintro _ ⟨i, rfl⟩; exact (hP_fam.1 i).2.2
    have hA₁₀_G : A₁₀ ⊆ G.verts := hA₁₀_sub.trans hA₁
    have hA₂₀_G : A₂₀ ⊆ G.verts := hA₂₀_sub.trans hA₂
    have hP_fam₀ : IsDisjointPathFamily G A₁₀ A₂₀ P :=
      ⟨fun i ↦ ⟨(hP_fam.1 i).1, ⟨i, rfl⟩, ⟨i, rfl⟩⟩, hP_fam.2⟩
    have hB_sep₀ : ∀ j, Separates G (B j).verts A₁₀ A₂₀ :=
      fun j ↦ (hB_sep j).mono_endpoints hA₁₀_sub hA₂₀_sub
    have hB_sep_empty : ∀ j, Separates G (∅ ∪ (B j).verts) A₁₀ A₂₀ := by
      intro j; simpa using hB_sep₀ j
    have hP_avoids_empty : ∀ i, (P i).Avoids ∅ := fun i ↦ disjoint_empty _
    -- "If some `Pᵢ` and some `Bⱼ` have an edge in common, we can contract that edge and produce a
    -- smaller counterexample. Thus no edge belongs to both some `Pᵢ` and some `Bⱼ`."
    have hno_shared_edge :
        ∀ (P' : Fin m → Path α), IsDisjointPathFamily G A₁₀ A₂₀ P' →
          ∀ i j, Disjoint (P' i).edgeSet (B j).edgeSet := by
      intro P' hP'_fam i j
      rw [Set.disjoint_left]
      intro e heP heB
      have hP'_avoids : ∀ k, (P' k).Avoids ∅ := fun k ↦ disjoint_empty _
      rcases contract_shared_path_subgraph_edge hfin hG hA₁₀_G hA₂₀_G (empty_subset _) P' hP'_fam
        hP'_avoids B hB_le hB_disj hB_sep_empty heP heB with
        ⟨G', A₁', A₂', P'', B', hG'_fin, hG'_mem, hV_lt, hE_le, hA₁'_G, hA₂'_G, _,
          hP''_fam, _, hB'_le, hB'_conn, _, hB'_disj, hB'_sep⟩
      have hB'_sep' : ∀ k, Separates G' (B' k).verts A₁' A₂' := by
        intro k; simpa using hB'_sep k
      have hlt : G'.verts.ncard + G'.edgeSet.ncard + m < N := by omega
      rcases ih _ hlt hG'_fin hG'_mem hA₁'_G hA₂'_G P'' hP''_fam B' hB'_le
        (fun k ↦ hB'_conn k (hB_conn k)) hB'_disj hB'_sep' rfl with h1 | h2
      · exact hm_ge h1
      · exact hn_ge h2
    -- "Moreover, every edge belongs either to some `Pᵢ` or to some `Bⱼ`, for otherwise we could
    -- delete it."
    have hedge_cover : G.edgeSet ⊆ (⋃ i, (P i).edgeSet) ∪ ⋃ j, (B j).edgeSet := by
      intro e heG
      by_contra hnot_mem
      rw [mem_union, mem_iUnion, mem_iUnion, not_or, not_exists, not_exists] at hnot_mem
      rcases hnot_mem with ⟨hnot_P, hnot_B⟩
      let G' := G.deleteEdges {e}
      have hG'_le : G' ≤ G := G.deleteEdges_le {e}
      have hG'_fin : G'.verts.Finite := hfin
      have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le hG'_le hG
      have hE_fin : G.edgeSet.Finite := finite_edgeSet_of_finite_verts hfin
      have hG'_edgeSet : G'.edgeSet = G.edgeSet \ {e} := by
        ext x
        induction x using Sym2.ind with
        | _ a b => simp [G', Subgraph.deleteEdges_adj]
      have hE_lt : G'.edgeSet.ncard < G.edgeSet.ncard := by
        rw [hG'_edgeSet]
        exact Set.ncard_sdiff_singleton_lt_of_mem heG hE_fin
      have hV_eq : G'.verts.ncard = G.verts.ncard := rfl
      have hP_fam' : IsDisjointPathFamily G' A₁₀ A₂₀ P := by
        refine ⟨fun i ↦ ⟨?_, (hP_fam₀.1 i).2.1, (hP_fam₀.1 i).2.2⟩, hP_fam₀.2⟩
        refine ⟨(hP_fam₀.1 i).1.1, fun x y hxy ↦ ?_⟩
        rw [Subgraph.deleteEdges_adj]
        exact ⟨(hP_fam₀.1 i).1.2 hxy, fun heq ↦ hnot_P i (heq ▸ hxy)⟩
      have hB_le' : ∀ j, B j ≤ G' := by
        intro j
        refine ⟨(hB_le j).1, fun x y hxy ↦ ?_⟩
        rw [Subgraph.deleteEdges_adj]
        exact ⟨(hB_le j).2 hxy, fun heq ↦ hnot_B j (heq ▸ hxy)⟩
      have hB_sep' : ∀ j, Separates G' (B j).verts A₁₀ A₂₀ :=
        fun j ↦ (hB_sep₀ j).of_le hG'_le
      have hlt : G'.verts.ncard + G'.edgeSet.ncard + m < N := by omega
      rcases ih _ hlt hG'_fin hG'_mem hA₁₀_G hA₂₀_G P hP_fam' B hB_le' hB_conn hB_disj hB_sep' rfl
        with h1 | h2
      · exact hm_ge h1
      · exact hn_ge h2
    -- "It follows that `{P₁', …, Pₘ'} = {P₁, …, Pₘ}`, and so the set `{P₁, …, Pₘ}` is unique."
    have hP_unique : IsUniqueDisjointPathFamily G A₁₀ A₂₀ P := by
      refine isUniqueDisjointPathFamily_of_edgeSet_subset P hP_fam₀ (fun P' hP'_fam e he ↦ ?_)
      rcases mem_iUnion.1 he with ⟨k, he_P'k⟩
      have he_G : e ∈ G.edgeSet := Subgraph.edgeSet_mono (hP'_fam.1 k).1 he_P'k
      rcases hedge_cover he_G with he_P | he_B
      · exact he_P
      · rcases mem_iUnion.1 he_B with ⟨j, he_Bj⟩
        exact ((hno_shared_edge P' hP'_fam k j).notMem_of_mem_left he_P'k he_Bj).elim
    -- "We claim that every vertex `v` of `G` is in some `Pᵢ`. For if not, and `v` is an isolated
    -- vertex, we can delete `v`, and if `v` is not an isolated vertex, we can contract some edge
    -- incident with `v`; in either case we produce a smaller counterexample, which is impossible."
    have hP_span : G.verts ⊆ ⋃ i, (P i).verts := by
      intro v₀ hv₀G
      by_contra hv₀_not_P
      rw [mem_iUnion, not_exists] at hv₀_not_P
      by_cases hex_adj : ∃ u₀, G.Adj u₀ v₀
      · rcases hex_adj with ⟨u₀, hadj_G⟩
        have he_G : s(u₀, v₀) ∈ G.edgeSet := hadj_G
        have he_B : s(u₀, v₀) ∈ ⋃ j, (B j).edgeSet := by
          rcases hedge_cover he_G with he_P | he_B
          · rcases mem_iUnion.1 he_P with ⟨i, hi_adj⟩
            change (P i).toSubgraph.Adj u₀ v₀ at hi_adj
            exact (hv₀_not_P i hi_adj.snd_mem).elim
          · exact he_B
        rcases mem_iUnion.1 he_B with ⟨j₀, hadj_B⟩
        change (B j₀).Adj u₀ v₀ at hadj_B
        have hA₁₀_P : A₁₀ ⊆ ⋃ i, (P i).verts := by
          rintro _ ⟨i, rfl⟩
          exact mem_iUnion.2 ⟨i, (P i).first_mem_verts⟩
        have hA₂₀_P : A₂₀ ⊆ ⋃ i, (P i).verts := by
          rintro _ ⟨i, rfl⟩
          exact mem_iUnion.2 ⟨i, (P i).last_mem_verts⟩
        rcases contract_outside_vertex_edge hfin hG P hA₁₀_P hA₂₀_P (empty_subset _) hP_fam₀
          B hB_le hB_disj hB_sep_empty hadj_B (notMem_empty v₀) hv₀_not_P with
          ⟨G', B', hG'_fin, hG'_mem, hV_lt, hE_le, _, hP_fam', hB'_le, hB'_conn, _, hB'_disj,
            hB'_sep⟩
        have hA₁₀_G' : A₁₀ ⊆ G'.verts := by
          rintro _ ⟨i, rfl⟩
          exact (hP_fam'.1 i).1.1 (P i).first_mem_verts
        have hA₂₀_G' : A₂₀ ⊆ G'.verts := by
          rintro _ ⟨i, rfl⟩
          exact (hP_fam'.1 i).1.1 (P i).last_mem_verts
        have hB'_sep' : ∀ j, Separates G' (B' j).verts A₁₀ A₂₀ := by
          intro j; simpa using hB'_sep j
        have hlt : G'.verts.ncard + G'.edgeSet.ncard + m < N := by omega
        rcases ih _ hlt hG'_fin hG'_mem hA₁₀_G' hA₂₀_G' P hP_fam' B' hB'_le
          (fun j ↦ hB'_conn j (hB_conn j)) hB'_disj hB'_sep' rfl with h1 | h2
        · exact hm_ge h1
        · exact hn_ge h2
      · -- `v₀` is an isolated vertex in `G`; delete `v₀`.
        let G' := G.deleteVerts {v₀}
        have hG'_le : G' ≤ G := G.deleteVerts_le
        have hG'_fin : G'.verts.Finite := hfin.subset hG'_le.1
        have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le hG'_le hG
        have hV_lt : G'.verts.ncard < G.verts.ncard := by
          rw [Subgraph.deleteVerts_verts]
          exact Set.ncard_sdiff_singleton_lt_of_mem hv₀G hfin
        have hE_le : G'.edgeSet.ncard ≤ G.edgeSet.ncard :=
          Set.ncard_le_ncard (Subgraph.edgeSet_mono hG'_le) (finite_edgeSet_of_finite_verts hfin)
        have hP_fam' : IsDisjointPathFamily G' A₁₀ A₂₀ P := by
          refine ⟨fun i ↦ ⟨?_, (hP_fam₀.1 i).2.1, (hP_fam₀.1 i).2.2⟩, hP_fam₀.2⟩
          exact toSubgraph_le_deleteVerts_iff.2
            ⟨(hP_fam₀.1 i).1, Set.disjoint_singleton_right.2 (hv₀_not_P i)⟩
        have hA₁₀_G' : A₁₀ ⊆ G'.verts := by
          rintro _ ⟨i, rfl⟩
          exact (hP_fam'.1 i).1.1 (P i).first_mem_verts
        have hA₂₀_G' : A₂₀ ⊆ G'.verts := by
          rintro _ ⟨i, rfl⟩
          exact (hP_fam'.1 i).1.1 (P i).last_mem_verts
        have hB_not_v₀ : ∀ j, v₀ ∉ (B j).verts := by
          intro j hv₀B
          have hθ_sq : 36 ≤ θ ^ 2 := by
            rw [sq]
            exact Nat.mul_le_mul hθ hθ
          have hm_pos : 0 < m := by omega
          let i₀ : Fin m := ⟨0, hm_pos⟩
          have hP0_meets : ((P i₀).verts ∩ (B j).verts).Nonempty := by
            have hnot_avoids := hB_sep₀ j (P i₀) (hP_fam₀.1 i₀)
            rwa [Path.Avoids, Set.not_disjoint_iff] at hnot_avoids
          rcases hP0_meets with ⟨w, hwP, hwB⟩
          have hw_ne_v₀ : w ≠ v₀ := fun heq ↦ hv₀_not_P _ (heq ▸ hwP)
          rcases exists_path_of_preconnected (hB_conn j).preconnected hwB hv₀B with
            ⟨Q, hQ_le_B, hQ_first, hQ_last⟩
          rcases Q with ⟨a, b, q, hq⟩
          dsimp at hQ_first hQ_last
          subst hQ_first hQ_last
          cases q with
          | nil => exact hw_ne_v₀ rfl
          | @cons _ z _ hadj q' =>
            have hex_inc : ∀ {x y : α} (w' : (⊤ : SimpleGraph α).Walk x y),
                x ≠ y → w'.toSubgraph ≤ G → ∃ u, G.Adj u y := by
              intro x y w' hne hw'_le
              induction w' with
              | nil => exact (hne rfl).elim
              | @cons x u y hadj' w'' ih' =>
                by_cases huy : u = y
                · subst huy
                  exact ⟨x, hw'_le.2 (Subgraph.sup_adj.2 (Or.inl (by simp)))⟩
                · exact ih' huy ((le_sup_right : w''.toSubgraph ≤ _).trans hw'_le)
            rcases hex_inc (Walk.cons hadj q') hw_ne_v₀ (hQ_le_B.trans (hB_le j)) with ⟨u₀, hu₀⟩
            exact hex_adj ⟨u₀, hu₀⟩
        have hB_le' : ∀ j, B j ≤ G' := fun j ↦
          toSubgraph_le_deleteVerts_iff.2 ⟨hB_le j, Set.disjoint_singleton_right.2 (hB_not_v₀ j)⟩
        have hB_sep' : ∀ j, Separates G' (B j).verts A₁₀ A₂₀ :=
          fun j ↦ (hB_sep₀ j).of_le hG'_le
        have hlt : G'.verts.ncard + G'.edgeSet.ncard + m < N := by omega
        rcases ih _ hlt hG'_fin hG'_mem hA₁₀_G' hA₂₀_G' P hP_fam' B hB_le' hB_conn hB_disj hB_sep'
          rfl with h1 | h2
        · exact hm_ge h1
        · exact hn_ge h2
    -- "For `1 ≤ j ≤ n`, each `Pᵢ` meets `Bⱼ`, by our hypothesis. By (2.6),
    -- `n < 2 m θ^{2θ - 2} m.choose (θ² / 2) = θ^{2θ}`, a contradiction, as required."
    have hB_meet : ∀ j, θ ^ 2 / 2 ≤ {i : Fin m | ((P i).verts ∩ (B j).verts).Nonempty}.ncard := by
      intro j
      have heq_univ : {i : Fin m | ((P i).verts ∩ (B j).verts).Nonempty} = Set.univ := by
        ext i
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        have hnot_avoids := hB_sep₀ j (P i) (hP_fam₀.1 i)
        rwa [Path.Avoids, Set.not_disjoint_iff] at hnot_avoids
      rw [heq_univ, Set.ncard_univ, Nat.card_fin]
      exact hm_ge'
    have hn_lt :=
      theorem_2_6_simple hθ heven hm_ge' hfin hG P hP_unique hP_span B hB_le hB_conn hB_disj hB_meet
    have h_arith : 2 * m * θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) = θ ^ (2 * θ) := by
      rw [← hm_eq, Nat.choose_self, mul_one]
      rcases heven with ⟨k, rfl⟩
      have h2m : 2 * ((k + k) ^ 2 / 2) = (k + k) ^ 2 := by
        have hsq : (k + k) ^ 2 = 2 * ((k + k) * k) := by
          rw [sq, mul_add, ← two_mul, ← mul_assoc]
        rw [hsq, Nat.mul_div_cancel_left _ (by omega)]
      rw [h2m, ← pow_add]
      congr 1
      omega
    rw [h_arith] at hn_lt
    exact hn_ge hn_lt

end GraphMinor.GM01
end
