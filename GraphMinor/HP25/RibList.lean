module

public import GraphMinor.HP25.WebPath
public import GraphMinor.HP25.SplitTools

/-!
# Filtering the vertices of a path

Section 3.4 of Humeau and Pous (page 9): "in a web with rib $R$, the intersection with $R$ of a path
with endpoints in $R$ yields an induced path. Indeed, if such a path $P$ uses a clique vertex $u$,
then we can take the longest subpath $Q$ of $P$ containing $u$, and whose inner vertices are all
clique vertices. The endpoints of $Q$ are on a triangle $T$ of the rib. In particular $Q$ can be
replaced in $P$ by an edge of $T$".

`WebData.exists_rib_path` proves the form of this observation used in Proposition 3.2. The strip
argument of Lemma 5.4 (`Sec5Strip.lean`) needs the list of rib vertices of a path, in order, and
needs to know where each of its edges comes from. This file proves:

* `exists_stretch_of_filter`: two consecutive entries `u, v` of a filtered list come from a stretch
  `u K v` of the list whose inner entries `K` are removed by the filter; `isListEdge_filter` is the
  converse;
* `isChain_filter`: a filtered list is a chain when each such stretch joins related ends;
* `WebData.tri_eq_head`, `WebData.adj_of_stretch`: the clique vertices of a stretch of a walk of a web
  between two rib vertices `u`, `v` all have the same triangle, which contains `u` and `v`; so `u`
  and `v` are adjacent;
* `WebData.isPathList_filter`: the rib vertices of a path of a web, in order, form a path of the rib.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*}

/-! ### Filtered lists -/

/-- An edge of a list comes from two consecutive entries. -/
theorem IsListEdge.exists_split {l : List V} {u v : V} (h : IsListEdge l u v) :
    ∃ l₀ l₁, l = l₀ ++ u :: v :: l₁ ∨ l = l₀ ++ v :: u :: l₁ := by
  induction l with
  | nil => obtain ⟨pr, hpr, -⟩ := h; simp at hpr
  | cons x l ih =>
    cases l with
    | nil => obtain ⟨pr, hpr, -⟩ := h; simp at hpr
    | cons y l =>
      obtain ⟨pr, hpr, he⟩ := h
      have hz : (x :: y :: l).zip (x :: y :: l).tail = (x, y) :: (y :: l).zip (y :: l).tail := rfl
      rw [hz] at hpr
      rcases List.mem_cons.mp hpr with rfl | hpr
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨[], l, Or.inl rfl⟩
        · exact ⟨[], l, Or.inr rfl⟩
      · obtain ⟨l₀, l₁, h⟩ := ih ⟨pr, hpr, he⟩
        exact ⟨x :: l₀, l₁, by rcases h with h | h <;> simp [h]⟩

/-- Two consecutive entries of a filtered list come from a stretch `u K v` of the list whose inner
entries are removed. -/
theorem exists_stretch_of_filter {p : V → Bool} {L F₀ F₁ : List V} {u v : V}
    (h : L.filter p = F₀ ++ u :: v :: F₁) :
    ∃ L₀ K L₁, L = L₀ ++ u :: K ++ v :: L₁ ∧ ∀ k ∈ K, p k = false := by
  obtain ⟨l₁, l₂, rfl, -, h2⟩ := List.filter_eq_append_iff.mp h
  obtain ⟨m₁, m₂, rfl, -, -, h3⟩ := List.filter_eq_cons_iff.mp h2
  obtain ⟨n₁, n₂, rfl, hn, -, -⟩ := List.filter_eq_cons_iff.mp h3
  exact ⟨l₁ ++ m₁, n₁, n₂, by simp, fun k hk => by simpa using hn k hk⟩

/-- The ends of a stretch `u K v` whose inner entries are removed are consecutive in the filtered
list. -/
theorem isListEdge_filter {p : V → Bool} {L₀ K L₁ : List V} {u v : V} (hu : p u = true)
    (hv : p v = true) (hK : ∀ k ∈ K, p k = false) :
    IsListEdge ((L₀ ++ u :: K ++ v :: L₁).filter p) u v := by
  have hKf : K.filter p = [] := List.filter_eq_nil_iff.mpr fun k hk => by simp [hK k hk]
  have e : (L₀ ++ u :: K ++ v :: L₁).filter p = L₀.filter p ++ (u :: v :: L₁.filter p) := by
    simp [List.filter_append, hu, hv, hKf]
  rw [e]
  exact IsListEdge.append_right ⟨(u, v), by simp, rfl⟩

/-- A filtered list is a chain for `r` when the ends of every stretch `u K v` whose inner entries are
removed are related. -/
theorem isChain_filter {p : V → Bool} {r : V → V → Prop} {L : List V}
    (h : ∀ L₀ u K v L₁, L = L₀ ++ u :: K ++ v :: L₁ → p u = true → p v = true →
      (∀ k ∈ K, p k = false) → r u v) :
    (L.filter p).IsChain r := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro u v F₀ F₁ he
  have hu : p u = true := List.of_mem_filter (l := L) (by rw [he]; simp)
  have hv : p v = true := List.of_mem_filter (l := L) (by rw [he]; simp)
  obtain ⟨L₀, K, L₁, hL, hK⟩ := exists_stretch_of_filter he
  exact h L₀ u K v L₁ hL hu hv hK

/-! ### Stretches through cliques -/

namespace WebData

variable {H : SimpleGraph V} {S : Set V} {C : List V} {R : Set V} {tri : V → Set V}

/-- A rib vertex adjacent to a clique vertex lies on its triangle. -/
theorem mem_tri_of_adj (W : WebData H S C R tri) {x u : V} (hx : x ∉ R) (hu : u ∈ R)
    (h : H.Adj x u) : u ∈ tri x := by
  rcases (W.adj_iff x ⟨W.supp h, hx⟩ u).mp h with h | ⟨h, -⟩
  · exact h
  · exact absurd hu h.2

/-- Consecutive clique vertices of a walk have the same triangle. -/
theorem tri_eq_head (W : WebData H S C R tri) :
    ∀ {k₀ : V} {K : List V}, (k₀ :: K).IsChain H.Adj → (∀ k ∈ k₀ :: K, k ∉ R) →
      ∀ k ∈ k₀ :: K, tri k = tri k₀
  | k₀, [], _, _, k, hk => by rw [List.mem_singleton.mp hk]
  | k₀, k₁ :: K, hc, hR, k, hk => by
    have hadj := (List.isChain_cons_cons.mp hc).1
    have h01 : tri k₁ = tri k₀ := by
      have hk₀ : k₀ ∈ S \ R := ⟨W.supp hadj, hR k₀ (by simp)⟩
      rcases (W.adj_iff k₀ hk₀ k₁).mp hadj with h | ⟨-, -, h⟩
      · exact absurd (W.tri_subset hk₀ h) (hR k₁ (by simp))
      · exact h
    rcases List.mem_cons.mp hk with rfl | hk
    · rfl
    · rw [tri_eq_head W (List.isChain_cons_cons.mp hc).2
        (fun x hx => hR x (List.mem_cons_of_mem _ hx)) k hk, h01]

/-- **A stretch through a clique.** In a walk `u K v` of the web between rib vertices whose inner
vertices are clique vertices, every inner vertex has `u` and `v` on its triangle, and `u`, `v` are
adjacent when distinct. -/
theorem adj_of_stretch (W : WebData H S C R tri) {u v : V} {K : List V}
    (hc : (u :: K ++ [v]).IsChain H.Adj) (hu : u ∈ R) (hv : v ∈ R) (huv : u ≠ v)
    (hK : ∀ k ∈ K, k ∉ R) : H.Adj u v ∧ ∀ k ∈ K, u ∈ tri k ∧ v ∈ tri k := by
  rcases K with _ | ⟨k₀, K⟩
  · exact ⟨(List.isChain_cons_cons.mp hc).1, by simp⟩
  have hc2 : (u :: k₀ :: (K ++ [v])).IsChain H.Adj := by simpa using hc
  have hc' : (k₀ :: K).IsChain H.Adj := by
    have := (List.isChain_cons_cons.mp hc2).2
    rw [← List.cons_append] at this
    exact this.left_of_append
  have huk := (List.isChain_cons_cons.mp hc2).1
  have htri := W.tri_eq_head hc' hK
  have hu₀ : u ∈ tri k₀ := W.mem_tri_of_adj (hK k₀ (by simp)) hu huk.symm
  obtain ⟨K', kl, hKe⟩ : ∃ K' kl, k₀ :: K = K' ++ [kl] :=
    ⟨(k₀ :: K).dropLast, (k₀ :: K).getLast (by simp), (List.dropLast_append_getLast _).symm⟩
  have hkl : kl ∈ k₀ :: K := by rw [hKe]; simp
  have hlv : H.Adj kl v := by
    refine List.isChain_iff_forall_rel_of_append_cons_cons.mp hc (l₁ := u :: K') (l₂ := []) ?_
    rw [List.cons_append (a := u) (as := k₀ :: K), hKe]; simp
  have hv₀ : v ∈ tri k₀ := by
    rw [← htri kl hkl]
    exact W.mem_tri_of_adj (hK kl hkl) hv hlv
  refine ⟨W.adj_of_mem_tri ⟨W.supp huk.symm, hK k₀ (by simp)⟩ hu₀ hv₀ huv, fun k hk => ?_⟩
  rw [htri k hk]
  exact ⟨hu₀, hv₀⟩

/-- **The rib vertices of a path of the web form a path of the rib.** -/
theorem isPathList_filter (W : WebData H S C R tri) [DecidablePred (· ∈ R)] {L : List V}
    (hc : L.IsChain H.Adj) (hnd : L.Nodup) : IsPathList H R (L.filter fun x => decide (x ∈ R)) := by
  refine ⟨hnd.filter _, isChain_filter fun L₀ u K v L₁ he hu hv hK => ?_, fun x hx => ?_⟩
  · have hc' : (u :: K ++ [v]).IsChain H.Adj := hc.infix ⟨L₀, L₁, by rw [he]; simp⟩
    have hnd' : (u :: K ++ [v]).Nodup := hnd.sublist (List.IsInfix.sublist ⟨L₀, L₁, by rw [he]; simp⟩)
    have huv : u ≠ v := fun h => by subst h; simp at hnd'
    exact (W.adj_of_stretch hc' (of_decide_eq_true hu) (of_decide_eq_true hv) huv
      fun k hk => of_decide_eq_false (hK k hk)).1
  · exact of_decide_eq_true (List.mem_filter.mp hx).2

end WebData

end GraphMinor.HP25
