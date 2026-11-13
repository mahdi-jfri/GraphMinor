module

public import GraphMinor.GM13.Section5
import GraphMinor.Thomason.UniformTheorem

/-!
# Graph Minors XIII, Section 5: (5.5) and (5.6)

This file proves (5.5) and (5.6) of N. Robertson and P. D. Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110 (page 83):

- `theorem_5_5` ((5.5), page 83, citing Thomason [28]), from `GraphMinor.Thomason.thomason84`
- `theorem_5_6` ((5.6), page 83)

They are separate from `Section5.lean` because the proof of Thomason's bound for small `p`
uses Section 6.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16

universe u v w

variable {α : Type u} {β : Type v}


/-- **Graph Minors XIII, (5.5)** (page 83):
"*Let $p \ge 1$ be an integer, and let $G$ be a non-null simple graph with*

$$
|E(G)| \ge 2.68 p(\log_2(p))^{1/2} |V(G)|.
$$

*Then $G$ has a $K_p$-minor.*" -/
theorem theorem_5_5_proof {G : Graph α β} {p : ℕ}
    (hp : 1 ≤ p) (hfinV : V(G).Finite) (hfinE : E(G).Finite)
    (hne : V(G).Nonempty) (hsimple : IsSimpleGraph G)
    (hedges : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) * (V(G).ncard : ℝ) ≤
      (E(G).ncard : ℝ)) :
    HasGraphModel (completeGraph p) G := by
  exact Thomason.thomason84 G p hp hfinV hfinE hne hsimple hedges

/-- **Graph Minors XIII, (5.6)** (page 83):
"For every integer $p \ge 0$, every $2p$-connected simple graph $G$ with $|E(G)| \ge 8.04 p(\log_2 3p)^{1/2} |V(G)|$ is $p$-linked." -/
theorem theorem_5_6_proof {G : Graph α β} {p : ℕ}
    (hfinV : V(G).Finite) (hfinE : E(G).Finite)
    (hsimple : IsSimpleGraph G)
    (hconn : IsKConnectedGraph G (2 * p))
    (hedges : (8.04 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 (3 * p)) * (V(G).ncard : ℝ) ≤
      (E(G).ncard : ℝ)) :
    IsPLinked G p := by
  refine ⟨le_of_lt hconn.1, fun s t hs ht hs_inj ht_inj hdisj_st => ?_⟩
  by_cases hp0 : p = 0
  · subst hp0
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · have hp1 : 1 ≤ p := Nat.pos_of_ne_zero hp0
    have h3p1 : 1 ≤ 3 * p := by omega
    have hneV : V(G).Nonempty := (ncard_pos hfinV).mp (by have := hconn.1; omega)
    have hedges' :
        (2.68 : ℝ) * ((3 * p : ℕ) : ℝ) * Real.sqrt (Real.logb 2 (3 * p : ℕ)) * (V(G).ncard : ℝ) ≤
          (E(G).ncard : ℝ) := by
      push_cast
      linarith
    obtain ⟨vMap, eMap, hModel⟩ :=
      theorem_5_5_proof h3p1 hfinV hfinE hneV hsimple hedges'
    -- Orient `G` into a digraph `D` with `D.toGraph = G`
    rcases hneV with ⟨v_def, hv_def⟩
    let headD (e : β) : α :=
      if he : e ∈ E(G) then Classical.choose ((G.edge_mem_iff_exists_isLink e).mp he) else v_def
    let tailD (e : β) : α :=
      if he : e ∈ E(G) then
        Classical.choose (Classical.choose_spec ((G.edge_mem_iff_exists_isLink e).mp he))
      else v_def
    have hlinkD (e : β) (he : e ∈ E(G)) : G.IsLink e (headD e) (tailD e) := by
      dsimp [headD, tailD]
      simp only [he, ↓reduceDIte]
      exact Classical.choose_spec (Classical.choose_spec ((G.edge_mem_iff_exists_isLink e).mp he))
    let D : Digraph α β := {
      vertexSet := V(G)
      edgeSet := E(G)
      head := headD
      tail := tailD
      head_mem := fun e he => G.left_mem_of_isLink (hlinkD e he)
      tail_mem := fun e he => G.left_mem_of_isLink (hlinkD e he).symm
    }
    have hDtoGraph : D.toGraph = G := by
      refine Graph.ext rfl (fun e x y => ?_)
      simp only [Digraph.toGraph, D]
      refine ⟨fun ⟨he, h⟩ => ?_, fun hlink => ⟨hlink.edge_mem, ?_⟩⟩
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hlinkD e he
        · exact (hlinkD e he).symm
      · have h0 := hlinkD e hlink.edge_mem
        rcases G.eq_or_eq_of_isLink_of_isLink h0 hlink with h1 | h1
        · have hlink' : G.IsLink e (headD e) y := by rw [h1]; exact hlink
          exact Or.inl ⟨h1, h0.right_unique hlink'⟩
        · have hlink' : G.IsLink e (headD e) x := by rw [h1]; exact hlink.symm
          exact Or.inr ⟨h1, h0.right_unique hlink'⟩
    let sub (i : Fin (3 * p)) : Digraph α β := D.subdigraphOf V(vMap i) E(vMap i)
    have hsub_V (i : Fin (3 * p)) : (sub i).vertexSet = V(vMap i) :=
      inter_eq_self_of_subset_right (hModel.sub_of_mem (mem_univ i)).vertexSet_mono
    have hsub_toGraph (i : Fin (3 * p)) : (sub i).toGraph = vMap i := by
      have hle : vMap i ≤ G := hModel.sub_of_mem (mem_univ i)
      refine Graph.ext (hsub_V i) (fun e x y => ?_)
      simp only [Digraph.toGraph, sub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨⟨heG, heV⟩, _, _⟩, h⟩
        have hlinkG : G.IsLink e x y := by
          rw [← hDtoGraph]; exact ⟨heG, h⟩
        exact (hle.isLink_iff heV).mpr hlinkG
      · intro hlink_v
        have hlinkG : G.IsLink e x y := hlink_v.mono hle
        have hlinkD' : D.toGraph.IsLink e x y := hDtoGraph ▸ hlinkG
        have heV : e ∈ E(vMap i) := hlink_v.edge_mem
        have hxV : x ∈ V(vMap i) := hlink_v.left_mem
        have hyV : y ∈ V(vMap i) := hlink_v.right_mem
        refine ⟨⟨⟨hlinkD'.1, heV⟩, ?_⟩, hlinkD'.2⟩
        rcases hlinkD'.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1.symm ▸ hxV, h2.symm ▸ hyV⟩
        · exact ⟨h1.symm ▸ hyV, h2.symm ▸ hxV⟩
    have hsub_conn (i : Fin (3 * p)) : (sub i).IsConnected := by
      refine ⟨(hsub_V i).symm ▸ hModel.nonempty_of_mem (mem_univ i), fun u hu v hv => ?_⟩
      rw [hsub_V i] at hu hv
      rw [hsub_toGraph i]
      exact hModel.connected_of_mem (mem_univ i) u hu v hv
    have hsub_disj : Pairwise (fun i j : Fin (3 * p) => Disjoint (sub i).vertexSet (sub j).vertexSet) := by
      intro i j hij
      rw [hsub_V i, hsub_V j]
      exact hModel.disjoint_of_ne (mem_univ i) (mem_univ j) hij
    have hadj : ∀ i j : Fin (3 * p), i < j → D.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet := by
      intro i j hlt
      have hij : i ≠ j := ne_of_lt hlt
      have hlinkK : (GM16.completeGraph (3 * p)).IsLink s(i, j) i j := ⟨hij, rfl⟩
      rcases hModel.link_ends_of_ne hlinkK hij with ⟨x, hx, y, hy, hlinkG⟩
      have hlinkD' : D.toGraph.IsLink (eMap ⟨s(i, j), hlinkK.edge_mem⟩) x y := hDtoGraph ▸ hlinkG
      refine ⟨eMap ⟨s(i, j), hlinkK.edge_mem⟩, hlinkD'.1, ?_⟩
      rw [hsub_V i, hsub_V j]
      rcases hlinkD'.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm ▸ hx, h2.symm ▸ hy⟩
      · exact Or.inr ⟨h1.symm ▸ hy, h2.symm ▸ hx⟩
    -- Apply `theorem_5_4_proof` with `Z = range s ∪ range t` and `Z_part r = {s r, t r}`
    let Z : Set α := Set.range s ∪ Set.range t
    have hZ_sub : Z ⊆ D.vertexSet := by
      rintro _ (⟨r, rfl⟩ | ⟨r, rfl⟩)
      · exact hs r
      · exact ht r
    have hZ_card : Z.ncard = 2 * p := by
      rw [ncard_union_eq hdisj_st (Set.toFinite _) (Set.toFinite _),
        ncard_range_of_injective hs_inj, ncard_range_of_injective ht_inj, Nat.card_fin]
      omega
    have hno_sep : ∀ (i : Fin (3 * p)) (A B : Digraph α β),
        D.IsSeparation A B → Z ⊆ A.vertexSet → (D.interSub A (sub i)).IsNull →
        2 * p ≤ Digraph.separationOrder A B := by
      intro i A B hsep hZA hnull
      by_contra hlt_ord
      push Not at hlt_ord
      let S : Set α := A.vertexSet ∩ B.vertexSet
      have hS_sub : S ⊆ V(G) :=
        inter_subset_left.trans hsep.sub_left.vertexSet_subset
      have hS_lt : S.ncard < 2 * p := hlt_ord
      have hZ_not_sub : ¬ Z ⊆ S := by
        intro hsub_ZS
        have hle := ncard_le_ncard hsub_ZS (hfinV.subset hS_sub)
        omega
      rcases not_subset.mp hZ_not_sub with ⟨z₀, hz₀Z, hz₀NotS⟩
      have hz₀A : z₀ ∈ A.vertexSet := hZA hz₀Z
      rcases (hsub_conn i).1 with ⟨y₀, hy₀⟩
      have hy₀NotA : y₀ ∉ A.vertexSet := by
        intro hy₀A
        have h : y₀ ∈ (D.interSub A (sub i)).vertexSet :=
          ⟨hsep.sub_left.vertexSet_subset hy₀A, hy₀A, hy₀⟩
        rw [hnull.1] at h; exact h
      have hy₀G : y₀ ∈ D.vertexSet := (D.subdigraphOf_isSubdigraph _ _).vertexSet_subset hy₀
      have hy₀B : y₀ ∈ B.vertexSet := (hsep.vertexSet_union ▸ hy₀G).resolve_left hy₀NotA
      have hy₀NotS : y₀ ∉ S := fun h => hy₀NotA h.1
      have hz₀_del : z₀ ∈ V(deleteVertices G S) := ⟨hZ_sub hz₀Z, hz₀NotS⟩
      have hy₀_del : y₀ ∈ V(deleteVertices G S) := ⟨hy₀G, hy₀NotS⟩
      rcases hconn.2 S hS_sub hS_lt z₀ hz₀_del y₀ hy₀_del with ⟨W⟩
      -- Any walk in `deleteVertices G S` from `z₀ ∈ A.vertexSet` to `y₀ ∈ B.vertexSet` must meet `S`
      have hW_no : ∀ {u v : α} (W₀ : GraphWalk (deleteVertices G S) u v),
          u ∈ A.vertexSet → v ∈ A.vertexSet := by
        intro u v W₀ huA
        induction W₀ with
        | nil _ => exact huA
        | @cons x y z e hlink rest ih_w =>
          apply ih_w
          have hxNotS : x ∉ S := hlink.left_mem.2
          have hxNotB : x ∉ B.vertexSet := fun hxB => hxNotS ⟨huA, hxB⟩
          have hlinkG : G.IsLink e x y := hlink.mono (deleteVertices_le G S)
          have hlinkD' : D.toGraph.IsLink e x y := hDtoGraph ▸ hlinkG
          have heNotB : e ∉ B.edgeSet := by
            intro heB
            rcases hlinkD'.2 with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact hxNotB (h1 ▸ hsep.sub_right.head_eq heB ▸ B.head_mem heB)
            · exact hxNotB (h2 ▸ hsep.sub_right.tail_eq heB ▸ B.tail_mem heB)
          have heA : e ∈ A.edgeSet := (hsep.edgeSet_union ▸ hlinkD'.1).resolve_right heNotB
          rcases hlinkD'.2 with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact h2 ▸ hsep.sub_left.tail_eq heA ▸ A.tail_mem heA
          · exact h1 ▸ hsep.sub_left.head_eq heA ▸ A.head_mem heA
      exact hy₀NotA (hW_no W hz₀A)
    let Z_part (r : Fin p) : Set α := {s r, t r}
    have hZ_nonempty (r : Fin p) : (Z_part r).Nonempty := ⟨s r, Or.inl rfl⟩
    have hZ_disj : Pairwise (fun r₁ r₂ : Fin p => Disjoint (Z_part r₁) (Z_part r₂)) := by
      intro r₁ r₂ hne
      rw [Set.disjoint_iff]
      rintro x ⟨rfl | rfl, h2⟩
      · rcases h2 with h | h
        · exact hne (hs_inj h)
        · exact Set.disjoint_left.mp hdisj_st ⟨r₁, rfl⟩ ⟨r₂, h.symm⟩
      · rcases h2 with h | h
        · exact Set.disjoint_left.mp hdisj_st ⟨r₂, h.symm⟩ ⟨r₁, rfl⟩
        · exact hne (ht_inj h)
    have hZ_union : (⋃ r : Fin p, Z_part r) = Z := by
      ext x
      simp only [Z_part, Z, mem_iUnion, mem_insert_iff, mem_singleton_iff, mem_union, mem_range]
      exact ⟨fun ⟨r, h⟩ => h.elim (fun h1 => Or.inl ⟨r, h1.symm⟩) (fun h2 => Or.inr ⟨r, h2.symm⟩),
        fun h => h.elim (fun ⟨r, h1⟩ => ⟨r, Or.inl h1.symm⟩) (fun ⟨r, h2⟩ => ⟨r, Or.inr h2.symm⟩)⟩
    obtain ⟨T, hT_sub, hT_conn, hT_disj, hT_Z⟩ :=
      theorem_5_4_proof ⟨hfinV, hfinE⟩ hZ_sub hZ_card (by omega)
        (fun i => D.subdigraphOf_isSubdigraph _ _) hsub_conn hsub_disj hadj hno_sep
        Z_part hZ_nonempty hZ_disj hZ_union
    -- Extract a path `P r` in `(T r).toGraph ≤ G` from `s r` to `t r` for each `r : Fin p`
    have hex_P (r : Fin p) :
        ∃ P : Graph α β, IsGraphPathWithEnds G P (s r) (t r) ∧ V(P) ⊆ (T r).vertexSet := by
      have hsr_mem : s r ∈ (T r).vertexSet := by
        have h : s r ∈ (T r).vertexSet ∩ Z := by rw [hT_Z r]; exact Or.inl rfl
        exact h.1
      have htr_mem : t r ∈ (T r).vertexSet := by
        have h : t r ∈ (T r).vertexSet ∩ Z := by rw [hT_Z r]; exact Or.inr rfl
        exact h.1
      rcases (hT_conn r).2 (s r) hsr_mem (t r) htr_mem with ⟨W⟩
      obtain ⟨P, hP_path, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
      have hTr_le_G : (T r).toGraph ≤ G := by
        rw [← hDtoGraph]
        refine ⟨(hT_sub r).vertexSet_subset, fun e x y ⟨he, h⟩ => ⟨(hT_sub r).edgeSet_subset he, ?_⟩⟩
        rw [← (hT_sub r).head_eq he, ← (hT_sub r).tail_eq he]
        exact h
      exact ⟨P, hP_path.mono hTr_le_G, hP_path.le.vertexSet_mono⟩
    let P (r : Fin p) : Graph α β := Classical.choose (hex_P r)
    have hP_spec (r : Fin p) : IsGraphPathWithEnds G (P r) (s r) (t r) ∧ V(P r) ⊆ (T r).vertexSet :=
      Classical.choose_spec (hex_P r)
    refine ⟨P, fun r₁ r₂ hne => ?_, fun r => (hP_spec r).1⟩
    exact Disjoint.mono (hP_spec r₁).2 (hP_spec r₂).2 (hT_disj hne)

end GraphMinor.GM13
