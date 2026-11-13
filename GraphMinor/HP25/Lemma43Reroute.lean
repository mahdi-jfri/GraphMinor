module

public import GraphMinor.HP25.Alternate
public import GraphMinor.HP25.Web
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.CrossTools

/-!
# Rerouting a crossing around a new edge

Tools for Claim A of case 2 of Lemma 4.3 (Humeau and Pous, page 14): "Let $(P_1,P_2)$ be a crossing
of $C$ in $G+vw$, with, say, $vw\in E(P_1)$. The path $P_2$ must contain some inner vertex of $vPw$
as otherwise $(P_2,P_1vPwP_1)$ would be a crossing of $C$ in $G$."

* `isCrossed_sup_edge_cases'`: a crossing in `G + uv` is a crossing in `G`, or has a path through the
  edge `uv` and a path of `G`;
* `reroute_edge`: replacing the edge `uv` in the first path by a walk of `G` from `u` to `v` that
  misses the second path and the frame gives a crossing in `G`;
* list facts: the first entry of a list in a set, chains in `G + uv` that miss `v`, and vertices of
  chains of a graph on `S`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- The first entry of a list that lies in a set `Z`. -/
theorem exists_first_mem {Z : Set V} : ∀ (l : List V), (∃ w ∈ l, w ∈ Z) →
    ∃ α u β, l = α ++ u :: β ∧ u ∈ Z ∧ ∀ w ∈ α, w ∉ Z
  | [], h => by simp at h
  | x :: t, h => by
    by_cases hx : x ∈ Z
    · exact ⟨[], x, t, rfl, hx, by simp⟩
    · obtain ⟨w, hw, hwZ⟩ := h
      rcases List.mem_cons.mp hw with rfl | hw
      · exact absurd hwZ hx
      · obtain ⟨α, u, β, rfl, hu, hα⟩ := exists_first_mem t ⟨w, hw, hwZ⟩
        refine ⟨x :: α, u, β, rfl, hu, fun w hw => ?_⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hx
        · exact hα w hw

/-- A chain of `G + uv` that misses `v` is a chain of `G`. -/
theorem isChain_of_sup_edge {u v : V} : ∀ {l : List V}, l.IsChain (G ⊔ edge u v).Adj → v ∉ l →
    l.IsChain G.Adj
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.isChain_singleton _
  | a :: b :: t, h, hv => by
    rw [List.isChain_cons_cons] at h ⊢
    refine ⟨?_, isChain_of_sup_edge h.2 fun h' => hv (List.mem_cons_of_mem _ h')⟩
    rcases (sup_adj _ _ _ _).mp h.1 with h1 | h1
    · exact h1
    · rcases ((edge_adj _ _ _ _).mp h1).1 with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact absurd (by simp) hv
      · exact absurd (by simp) hv

/-- The entries of a chain with at least two entries of a graph on `S` lie in `S`. -/
theorem mem_of_isChain {S : Set V} (hs : IsSupportedOn G S) :
    ∀ {l : List V}, l.IsChain G.Adj → 2 ≤ l.length → ∀ v ∈ l, v ∈ S
  | [], _, h, _, _ => by simp at h
  | [_], _, h, _, _ => by simp at h
  | a :: b :: t, hc, _, v, hv => by
    rw [List.isChain_cons_cons] at hc
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hs hc.1
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact hs hc.1.symm
      · exact mem_of_isChain hs hc.2 (by simp; exact List.length_pos_of_mem hv) v
          (List.mem_cons_of_mem _ hv)

/-- A chain from `a` to `b` whose only entries in `T` are `a` and `b` contains a `T`-path. -/
theorem exists_tPath_of_chain {T W : List V} {a b : V} (hW : W.IsChain G.Adj)
    (hh : W.head? = some a) (hl : W.getLast? = some b) (ha : a ∈ T) (hb : b ∈ T)
    (hin : ∀ u ∈ W, u ∈ T → u = a ∨ u = b) :
    ∃ p : G.Walk a b, IsTPath G T p ∧ ∀ u ∈ p.support, u ∈ W := by
  classical
  obtain ⟨p, hp⟩ := exists_walk_of_chain W hW hh hl
  have hsub : ∀ u ∈ p.bypass.support, u ∈ W := fun u hu => hp ▸ p.support_bypass_subset_support hu
  refine ⟨p.bypass, ⟨p.bypass_isPath, ha, hb, fun u hu h1 h2 => ?_⟩, hsub⟩
  have : u ∉ T := fun hT => (hin u (hsub u hu) hT).elim h1 h2
  exact ⟨this, this⟩

/-- The two ends of an edge of a walk are consecutive in its list of vertices. -/
theorem Walk.exists_split_of_mem_edges {u v a b : V} {p : G.Walk a b} (h : s(u, v) ∈ p.edges) :
    ∃ X₁ X₂, p.support = X₁ ++ u :: v :: X₂ ∨ p.support = X₁ ++ v :: u :: X₂ := by
  rw [Walk.edges_eq_map_darts, List.mem_map] at h
  obtain ⟨d, hd, he⟩ := h
  obtain ⟨s, t, hst⟩ := (Walk.mem_darts_iff_fst_snd_infix_support).mp hd
  have e : d.edge = s(d.fst, d.snd) := rfl
  rw [e] at he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨s, t, Or.inl (by rw [← hst, ← h1, ← h2]; simp)⟩
  · exact ⟨s, t, Or.inr (by rw [← hst, ← h1, ← h2]; simp)⟩

/-- **Crossings in an edge extension, general edge.** A crossing of `T` in `G + uv` is a crossing in
`G`, or consists of a path `Q` through the edge `uv` and a path `R` of `G`, with alternating ends. -/
theorem isCrossed_sup_edge_cases' {T : List V} {u v : V} (hc : IsCrossed (G ⊔ edge u v) T) :
    IsCrossed G T ∨ ∃ a b c d, ∃ (Q : (G ⊔ edge u v).Walk a b) (R : G.Walk c d),
      Alternate T a b c d ∧ IsTPath (G ⊔ edge u v) T Q ∧ s(u, v) ∈ Q.edges ∧ IsTPath G T R ∧
      Q.support.Disjoint R.support := by
  obtain ⟨a, b, c, d, Q, R, hcr⟩ := hc
  have halt := hcr.alternate
  obtain ⟨hidx, hQ, hR, hdisj⟩ := hcr
  by_cases hQe : s(u, v) ∈ Q.edges
  · have hRe : s(u, v) ∉ R.edges := fun h =>
      hdisj (Q.fst_mem_support_of_mem_edges hQe) (R.fst_mem_support_of_mem_edges h)
    obtain ⟨R', hR', hRs⟩ := hR.transfer hRe
    exact Or.inr ⟨a, b, c, d, Q, R', halt, hQ, hQe, hR', by rw [hRs]; exact hdisj⟩
  · by_cases hRe : s(u, v) ∈ R.edges
    · obtain ⟨Q', hQ', hQs⟩ := hQ.transfer hQe
      refine Or.inr ⟨c, d, b, a, R, Q'.reverse, halt.comm, hR, hRe, hQ'.reverse, ?_⟩
      rw [Walk.support_reverse, hQs]
      exact fun _ h1 h2 => hdisj (List.mem_reverse.mp h2) h1
    · obtain ⟨Q', hQ', hQs⟩ := hQ.transfer hQe
      obtain ⟨R', hR', hRs⟩ := hR.transfer hRe
      exact Or.inl ⟨a, b, c, d, Q', R', hidx, hQ', hR', by rw [hQs, hRs]; exact hdisj⟩

/-- **Replacing an edge by a walk**, on lists: in a chain `X₁ u v X₂` of `G + uv` without
repetition, from `a` to `b`, replace the step `uv` by a chain `Z` of `G` from `u` to `v` whose only
entries in `T` are `u` and `v`. The result contains a `T`-path of `G` from `a` to `b`. -/
theorem reroute_core {T : List V} {u v a b : V} {X₁ X₂ Z : List V}
    (hX : (X₁ ++ u :: v :: X₂).IsChain (G ⊔ edge u v).Adj) (hnd : (X₁ ++ u :: v :: X₂).Nodup)
    (hh : (X₁ ++ u :: v :: X₂).head? = some a) (hl : (X₁ ++ u :: v :: X₂).getLast? = some b)
    (ha : a ∈ T) (hb : b ∈ T) (hin : ∀ x ∈ X₁ ++ u :: v :: X₂, x ∈ T → x = a ∨ x = b)
    (hZ : Z.IsChain G.Adj) (hZh : Z.head? = some u) (hZl : Z.getLast? = some v)
    (hZT : ∀ x ∈ Z, x ∈ T → x = u ∨ x = v) :
    ∃ p : G.Walk a b, IsTPath G T p ∧ ∀ x ∈ p.support, x ∈ X₁ ++ u :: v :: X₂ ∨ x ∈ Z := by
  have hnd' := hnd
  rw [List.nodup_append, List.nodup_cons, List.nodup_cons] at hnd'
  have huv : u ≠ v := fun h => hnd'.2.1.1 (by simp [h])
  have hvX₁ : v ∉ X₁ := fun h => hnd'.2.2 v h v (by simp) rfl
  have huX₂ : u ∉ v :: X₂ := hnd'.2.1.1
  -- the two parts of the chain avoid the new edge
  have e1 : X₁ ++ u :: v :: X₂ = (X₁ ++ [u]) ++ (v :: X₂) := by simp
  rw [e1] at hX
  have c1 : (X₁ ++ [u]).IsChain G.Adj := isChain_of_sup_edge hX.left_of_append (by
    simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hvX₁, huv.symm⟩)
  have c2 : (v :: X₂).IsChain G.Adj := by
    rw [edge_comm] at hX
    exact isChain_of_sup_edge hX.right_of_append huX₂
  obtain ⟨Z', rfl⟩ : ∃ Z', Z = u :: Z' := by
    match Z, hZh with
    | w :: Z', h => exact ⟨Z', by rw [Option.some_injective _ h]⟩
  have c3 : (X₁ ++ [u] ++ Z').IsChain G.Adj := isChain_append_of_last c1 (by simp) hZ
  have hl3 : (X₁ ++ [u] ++ Z').getLast? = some v := by
    rw [List.append_assoc, List.getLast?_append]
    simp only [List.singleton_append]
    rw [hZl]
    rfl
  have c4 : (X₁ ++ [u] ++ Z' ++ X₂).IsChain G.Adj := isChain_append_of_last c3 hl3 c2
  have hh4 : (X₁ ++ [u] ++ Z' ++ X₂).head? = some a := by
    rw [← hh]
    simp [List.head?_append]
  have hl4 : (X₁ ++ [u] ++ Z' ++ X₂).getLast? = some b := by
    rw [← hl, List.getLast?_append, hl3]
    have e2 : X₁ ++ u :: v :: X₂ = (X₁ ++ [u, v]) ++ X₂ := by simp
    rw [e2, List.getLast?_append]
    simp
  have hmem : ∀ x ∈ X₁ ++ [u] ++ Z' ++ X₂, x ∈ X₁ ++ u :: v :: X₂ ∨ x ∈ u :: Z' := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with ((hx | rfl) | hx) | hx
    · exact Or.inl (by simp [hx])
    · exact Or.inr (by simp)
    · exact Or.inr (by simp [hx])
    · exact Or.inl (by simp [hx])
  obtain ⟨p, hp, hps⟩ := exists_tPath_of_chain c4 hh4 hl4 ha hb (fun x hx hxT => by
    rcases hmem x hx with hx | hx
    · exact hin x hx hxT
    · rcases hZT x hx hxT with rfl | rfl
      · exact hin x (by simp) hxT
      · exact hin x (by simp) hxT)
  exact ⟨p, hp, fun x hx => hmem x (hps x hx)⟩

/-- **Rerouting a crossing around the new edge.** Let `(Q, R)` be a crossing of `T` in `G + uv`,
with `uv` an edge of `Q` and `R` a path of `G`. A walk `Z` of `G` from `u` to `v` whose only
vertices in `T` are `u` and `v`, and that misses `R`, replaces the edge: `T` is crossed in `G`. -/
theorem reroute_edge {T : List V} {u v a b c d : V} {Z : List V}
    (Q : (G ⊔ edge u v).Walk a b) (R : G.Walk c d) (halt : Alternate T a b c d)
    (hQ : IsTPath (G ⊔ edge u v) T Q) (hQe : s(u, v) ∈ Q.edges) (hR : IsTPath G T R)
    (hdisj : Q.support.Disjoint R.support)
    (hZ : Z.IsChain G.Adj) (hZh : Z.head? = some u) (hZl : Z.getLast? = some v)
    (hZT : ∀ x ∈ Z, x ∈ T → x = u ∨ x = v) (hZR : ∀ x ∈ Z, x ∉ R.support) :
    IsCrossed G T := by
  have hQin : ∀ x ∈ Q.support, x ∈ T → x = a ∨ x = b := fun x hx hxT => by
    by_contra hne
    push Not at hne
    exact (hQ.2.2.2 x hx hne.1 hne.2).1 hxT
  have hQh : Q.support.head? = some a := by rw [← Walk.cons_tail_support]; rfl
  have hQl : Q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  obtain ⟨X₁, X₂, hX | hX⟩ := Walk.exists_split_of_mem_edges hQe
  · have hc := Q.isChain_adj_support
    have hnd := hQ.1.support_nodup
    rw [hX] at hc hnd hQh hQl hQin
    obtain ⟨p, hp, hps⟩ := reroute_core hc hnd hQh hQl hQ.2.1 hQ.2.2.1 hQin hZ hZh hZl hZT
    refine isCrossed_of_alternate' halt p R hp hR fun x h1 h2 => ?_
    rcases hps x h1 with h | h
    · rw [← hX] at h; exact hdisj h h2
    · exact hZR x h h2
  · have hc := Q.isChain_adj_support
    have hnd := hQ.1.support_nodup
    rw [hX, edge_comm] at hc
    rw [hX] at hnd hQh hQl hQin
    have hZr : Z.reverse.IsChain G.Adj := List.isChain_reverse.mpr (hZ.imp fun _ _ h => h.symm)
    obtain ⟨p, hp, hps⟩ := reroute_core hc hnd hQh hQl hQ.2.1 hQ.2.2.1 hQin hZr
      (by rw [List.head?_reverse]; exact hZl) (by rw [List.getLast?_reverse]; exact hZh)
      (fun x hx hxT => (hZT x (List.mem_reverse.mp hx) hxT).symm)
    refine isCrossed_of_alternate' halt p R hp hR fun x h1 h2 => ?_
    rcases hps x h1 with h | h
    · rw [← hX] at h; exact hdisj h h2
    · exact hZR x (List.mem_reverse.mp h) h2

end GraphMinor.HP25
