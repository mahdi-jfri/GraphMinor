module

public import GraphMinor.GM01.Defs
import GraphMinor.GM01.Basic
import GraphMinor.GM01.ConnectedSubgraphs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-!
# Graph Minors I, (2.5) and (2.6): Unique Disjoint Path Families

This file formalizes (2.5) and (2.6) of Robertson and Seymour, *Graph Minors I. Excluding a forest*
(pages 44–47):
* `GM01.lemma_2_5_step_1`, `GM01.lemma_2_5_step_2`, `GM01.lemma_2_5_step_3_trans`, and
  `GM01.lemma_2_5_step_3_irrefl`: Steps 1–3 of the proof of (2.5).
* `GM01.theorem_2_5`: existence of the integer-valued potential function `μ` on `V(G)` when `G` is
  spanned by a unique family of `m` disjoint paths from `A₁` to `A₂`.
* `GM01.theorem_2_6`: bound `n < 2 * m * θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2)` on the number of
  disjoint connected subgraphs `B₁, …, Bₙ` each meeting at least `θ ^ 2 / 2` paths of a unique
  spanning family of `m` disjoint paths.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph Set

variable {α : Type*}

/-! ### Path endpoint order lemmas and joining two vertex-disjoint paths by an edge -/

namespace Path

/-- Join two vertex-disjoint paths `Q` and `S` by an edge between `Q.last` and `S.first`. -/
def joinEdge (Q S : Path α) (hne : Q.last ≠ S.first) (hdisj : Disjoint Q.verts S.verts) :
    Path α :=
  have hlast_not_S : Q.last ∉ S.walk.support := by
    rw [← S.mem_verts_iff]
    exact hdisj.notMem_of_mem_left Q.last_mem_verts
  let S' : Path α :=
    { first := Q.last
      last := S.last
      walk := Walk.cons ((top_adj Q.last S.first).2 hne) S.walk
      isPath := S.isPath.cons hlast_not_S }
  have hdisj' : ∀ x ∈ Q.verts, ∀ y ∈ S'.verts, x = y → x = Q.last := by
    intro x hx y hy hxy
    subst hxy
    rw [Path.mem_verts_iff] at hy
    change x ∈ Q.last :: S.walk.support at hy
    rcases List.mem_cons.1 hy with rfl | hxS
    · rfl
    · rw [← S.mem_verts_iff] at hxS
      exact (hdisj.notMem_of_mem_left hx hxS).elim
  Q.append (rfl : Q.last = S'.first) hdisj'

@[simp]
lemma joinEdge_first (Q S : Path α) (hne : Q.last ≠ S.first) (hdisj : Disjoint Q.verts S.verts) :
    (Q.joinEdge S hne hdisj).first = Q.first := by
  dsimp [joinEdge]

@[simp]
lemma joinEdge_last (Q S : Path α) (hne : Q.last ≠ S.first) (hdisj : Disjoint Q.verts S.verts) :
    (Q.joinEdge S hne hdisj).last = S.last := by
  dsimp [joinEdge]

lemma joinEdge_toSubgraph (Q S : Path α) (hne : Q.last ≠ S.first)
    (hdisj : Disjoint Q.verts S.verts) :
    (Q.joinEdge S hne hdisj).toSubgraph =
      Q.toSubgraph ⊔ ((⊤ : SimpleGraph α).subgraphOfAdj ((top_adj Q.last S.first).2 hne) ⊔
        S.toSubgraph) := by
  dsimp [joinEdge]
  rw [append_toSubgraph]
  rfl

lemma joinEdge_verts (Q S : Path α) (hne : Q.last ≠ S.first)
    (hdisj : Disjoint Q.verts S.verts) :
    (Q.joinEdge S hne hdisj).verts = Q.verts ∪ S.verts := by
  ext x
  rw [Path.verts, joinEdge_toSubgraph]
  simp only [Subgraph.verts_sup, subgraphOfAdj_verts, mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (hxQ | (rfl | rfl) | hxS)
    · exact Or.inl hxQ
    · exact Or.inl Q.last_mem_verts
    · exact Or.inr S.first_mem_verts
    · exact Or.inr hxS
  · rintro (hxQ | hxS)
    · exact Or.inl hxQ
    · exact Or.inr (Or.inr hxS)

lemma joinEdge_toSubgraph_le {G : (⊤ : SimpleGraph α).Subgraph} (Q S : Path α)
    (hQ : Q.toSubgraph ≤ G) (hS : S.toSubgraph ≤ G) (hadj : G.Adj Q.last S.first)
    (hdisj : Disjoint Q.verts S.verts) :
    (Q.joinEdge S hadj.ne hdisj).toSubgraph ≤ G := by
  rw [joinEdge_toSubgraph]
  exact sup_le hQ (sup_le (subgraphOfAdj_le_of_adj _ hadj) hS)

lemma joinEdge_adj_last_first (Q S : Path α) (hne : Q.last ≠ S.first)
    (hdisj : Disjoint Q.verts S.verts) :
    (Q.joinEdge S hne hdisj).toSubgraph.Adj Q.last S.first := by
  rw [joinEdge_toSubgraph]
  exact Subgraph.sup_adj.2 (Or.inr (Subgraph.sup_adj.2 (Or.inl (by simp))))

end Path

/-! ### Step 1, Step 2, and Step 3 of (2.5) (pages 44–45) -/

/-- `u` and `v` are joined by an edge of `G` that is not in any of the paths `P₁, …, Pₘ`
(Graph Minors I, (2.5), page 44). -/
def IsCrossEdge (G : (⊤ : SimpleGraph α).Subgraph) {m : ℕ} (P : Fin m → Path α) (u v : α) : Prop :=
  G.Adj u v ∧ ∀ i, ¬ (P i).toSubgraph.Adj u v

lemma IsCrossEdge.symm {G : (⊤ : SimpleGraph α).Subgraph} {m : ℕ} {P : Fin m → Path α} {u v : α}
    (h : IsCrossEdge G P u v) : IsCrossEdge G P v u :=
  ⟨h.1.symm, fun i hadj ↦ h.2 i hadj.symm⟩

/-- Cyclic predecessor `(j - 1) mod r` on `Fin r` (so `0` maps to `r - 1`, corresponding to the
paper's `v₀ = vᵣ` in 1-based indexing). -/
def prevFin (r : ℕ) (hr : 1 ≤ r) (j : Fin r) : Fin r :=
  if j.val = 0 then ⟨r - 1, by omega⟩ else ⟨j.val - 1, by omega⟩

/-- Cyclic successor `(j + 1) mod r` on `Fin r`. -/
def nextFin (r : ℕ) (hr : 1 ≤ r) (j : Fin r) : Fin r :=
  if h : j.val + 1 = r then ⟨0, by omega⟩ else ⟨j.val + 1, by omega⟩

lemma prevFin_eq_of_zero {r : ℕ} (hr : 1 ≤ r) {j : Fin r} (hj : j.val = 0) :
    prevFin r hr j = ⟨r - 1, by omega⟩ :=
  ite_eq_left hj

lemma prevFin_eq_of_ne_zero {r : ℕ} (hr : 1 ≤ r) {j : Fin r} (hj : j.val ≠ 0) :
    prevFin r hr j = ⟨j.val - 1, by omega⟩ :=
  ite_eq_right hj

lemma prevFin_nextFin (r : ℕ) (hr : 1 ≤ r) (j : Fin r) :
    prevFin r hr (nextFin r hr j) = j := by
  by_cases hj : j.val + 1 = r
  · have hnext : nextFin r hr j = ⟨0, by omega⟩ := dite_eq_left hj
    rw [hnext, prevFin_eq_of_zero hr rfl]
    ext; dsimp; omega
  · have hnext : nextFin r hr j = ⟨j.val + 1, by omega⟩ := dite_eq_right hj
    rw [hnext, prevFin_eq_of_ne_zero hr (by dsimp; omega)]
    ext; dsimp

lemma nextFin_prevFin (r : ℕ) (hr : 1 ≤ r) (j : Fin r) :
    nextFin r hr (prevFin r hr j) = j := by
  by_cases hj : j.val = 0
  · rw [prevFin_eq_of_zero hr hj]
    dsimp [nextFin]
    have heq : (r - 1) + 1 = r := by omega
    rw [dite_eq_left heq]
    ext; dsimp; omega
  · rw [prevFin_eq_of_ne_zero hr hj]
    dsimp [nextFin]
    have hne : (j.val - 1) + 1 ≠ r := by omega
    rw [dite_eq_right hne]
    ext; dsimp; omega

lemma prevFin_injective (r : ℕ) (hr : 1 ≤ r) : Function.Injective (prevFin r hr) :=
  Function.LeftInverse.injective (nextFin_prevFin r hr)

/-- **Graph Minors I, (2.5) Step 1** (page 44):
"There is no sequence $u_1, v_1, u_2, v_2, \dots, u_r, v_r$ of distinct vertices of $G$, where
$r \ge 1$, and for $1 \le j \le r$ $v_{j - 1}, u_j$ are adjacent, joined by an edge not in any of
$P_1, \dots, P_m$ (setting $v_0 = v_r$), and $u_1, u_2, \dots, u_r$ are all on different $P_i$'s,
and for $1 \le j \le r$, $v_j$ occurs after $u_j$ on one of $P_1, \dots, P_m$." -/
lemma lemma_2_5_step_1 {G : (⊤ : SimpleGraph α).Subgraph} {A₁ A₂ : Set α} {m r : ℕ}
    {P : Fin m → Path α} (hP_unique : IsUniqueDisjointPathFamily G A₁ A₂ P)
    (hr : 1 ≤ r) (u v : Fin r → α) (pIdx : Fin r → Fin m)
    (hpIdx_inj : Function.Injective pIdx)
    (huv_prec : ∀ j, (P (pIdx j)).Precedes (u j) (v j))
    (hcross : ∀ j, IsCrossEdge G P (v (prevFin r hr j)) (u j)) :
    False := by
  classical
  have hP_fromTo : ∀ i, (P i).IsFromTo G A₁ A₂ := hP_unique.1.1
  have hP_disj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts := hP_unique.1.2
  have hu_mem : ∀ j, u j ∈ (P (pIdx j)).verts := fun j ↦ (huv_prec j).fst_mem
  have hv_mem : ∀ j, v j ∈ (P (pIdx j)).verts := fun j ↦ (huv_prec j).snd_mem
  let Q (j : Fin r) : Path α := (P (pIdx j)).takeUntil (u j) (hu_mem j)
  let S (j : Fin r) : Path α := (P (pIdx j)).dropUntil (v j) (hv_mem j)
  have hQ_sub : ∀ j, (Q j).verts ⊆ (P (pIdx j)).verts :=
    fun j ↦ ((P (pIdx j)).takeUntil_toSubgraph_le (hu_mem j)).1
  have hS_sub : ∀ j, (S j).verts ⊆ (P (pIdx j)).verts :=
    fun j ↦ ((P (pIdx j)).dropUntil_toSubgraph_le (hv_mem j)).1
  have hQS_disj_same : ∀ j, Disjoint (Q j).verts (S j).verts := by
    intro j
    rw [Set.disjoint_left]
    intro x hxQ hxS
    rw [(P (pIdx j)).mem_takeUntil_verts_iff (hu_mem j)] at hxQ
    rw [(P (pIdx j)).mem_dropUntil_verts_iff (hv_mem j)] at hxS
    rcases hxQ.2 with hxu | rfl
    · rcases hxS.2 with hvx | rfl
      · exact (hxu.trans (huv_prec j)).asymm hvx
      · exact hxu.asymm (huv_prec j)
    · rcases hxS.2 with hvx | heq
      · exact (huv_prec j).asymm hvx
      · exact (huv_prec j).ne heq
  have hQS_disj : ∀ j₁ j₂, Disjoint (Q j₁).verts (S j₂).verts := by
    intro j₁ j₂
    by_cases h : j₁ = j₂
    · subst h; exact hQS_disj_same j₁
    · exact (hP_disj (hpIdx_inj.ne h)).mono (hQ_sub j₁) (hS_sub j₂)
  have hQ_disj : Pairwise fun j₁ j₂ ↦ Disjoint (Q j₁).verts (Q j₂).verts :=
    fun j₁ j₂ hne ↦ (hP_disj (hpIdx_inj.ne hne)).mono (hQ_sub j₁) (hQ_sub j₂)
  have hS_disj : Pairwise fun j₁ j₂ ↦ Disjoint (S j₁).verts (S j₂).verts :=
    fun j₁ j₂ hne ↦ (hP_disj (hpIdx_inj.ne hne)).mono (hS_sub j₁) (hS_sub j₂)
  have hadj_QS : ∀ j, G.Adj (Q j).last (S (prevFin r hr j)).first := by
    intro j
    rw [(P (pIdx j)).takeUntil_last, (P (pIdx (prevFin r hr j))).dropUntil_first]
    exact (hcross j).1.symm
  let P_reroute (j : Fin r) : Path α :=
    (Q j).joinEdge (S (prevFin r hr j)) (hadj_QS j).ne (hQS_disj j (prevFin r hr j))
  have hP_reroute_verts : ∀ j, (P_reroute j).verts = (Q j).verts ∪ (S (prevFin r hr j)).verts :=
    fun j ↦ Path.joinEdge_verts _ _ _ _
  have hP_reroute_fromTo : ∀ j, (P_reroute j).IsFromTo G A₁ A₂ := by
    intro j
    let j' := prevFin r hr j
    refine ⟨Path.joinEdge_toSubgraph_le (Q j) (S j')
        (((P (pIdx j)).takeUntil_toSubgraph_le _).trans (hP_fromTo (pIdx j)).1)
        (((P (pIdx j')).dropUntil_toSubgraph_le _).trans (hP_fromTo (pIdx j')).1)
        (hadj_QS j) (hQS_disj j j'), ?_, ?_⟩
    · rw [Path.joinEdge_first, (P (pIdx j)).takeUntil_first]
      exact (hP_fromTo (pIdx j)).2.1
    · rw [Path.joinEdge_last, (P (pIdx j')).dropUntil_last]
      exact (hP_fromTo (pIdx j')).2.2
  let P_new (i : Fin m) : Path α :=
    if h : ∃ j, pIdx j = i then P_reroute h.choose else P i
  have hP_new_eq : ∀ j, P_new (pIdx j) = P_reroute j := by
    intro j
    have hex : ∃ j', pIdx j' = pIdx j := ⟨j, rfl⟩
    have hchoose : hex.choose = j := hpIdx_inj hex.choose_spec
    dsimp [P_new]
    rw [dite_eq_left hex, hchoose]
  have hP_new_family : IsDisjointPathFamily G A₁ A₂ P_new := by
    refine ⟨fun i ↦ ?_, fun i₁ i₂ hne ↦ ?_⟩
    · dsimp [P_new]
      split_ifs with h
      · exact hP_reroute_fromTo h.choose
      · exact hP_fromTo i
    · change Disjoint (P_new i₁).verts (P_new i₂).verts
      by_cases h₁ : ∃ j, pIdx j = i₁ <;> by_cases h₂ : ∃ j, pIdx j = i₂
      · obtain ⟨j₁, rfl⟩ := h₁
        obtain ⟨j₂, rfl⟩ := h₂
        rw [hP_new_eq j₁, hP_new_eq j₂, hP_reroute_verts j₁, hP_reroute_verts j₂]
        have hne_j : j₁ ≠ j₂ := fun h ↦ hne (congrArg pIdx h)
        have hne_prev : prevFin r hr j₁ ≠ prevFin r hr j₂ :=
          (prevFin_injective r hr).ne hne_j
        exact (Disjoint.union_left (hQ_disj hne_j) (hQS_disj j₂ _).symm).union_right
          (Disjoint.union_left (hQS_disj j₁ _) (hS_disj hne_prev))
      · obtain ⟨j₁, rfl⟩ := h₁
        rw [hP_new_eq j₁, hP_reroute_verts j₁]
        have hP_new_i₂ : P_new i₂ = P i₂ := dite_eq_right h₂
        rw [hP_new_i₂]
        have hne1 : pIdx j₁ ≠ i₂ := hne
        have hne2 : pIdx (prevFin r hr j₁) ≠ i₂ := fun h ↦ h₂ ⟨prevFin r hr j₁, h⟩
        exact Disjoint.union_left
          ((hP_disj hne1).mono_left (hQ_sub j₁))
          ((hP_disj hne2).mono_left (hS_sub (prevFin r hr j₁)))
      · obtain ⟨j₂, rfl⟩ := h₂
        rw [hP_new_eq j₂, hP_reroute_verts j₂]
        have hP_new_i₁ : P_new i₁ = P i₁ := dite_eq_right h₁
        rw [hP_new_i₁]
        have hne1 : i₁ ≠ pIdx j₂ := hne
        have hne2 : i₁ ≠ pIdx (prevFin r hr j₂) := fun h ↦ h₁ ⟨prevFin r hr j₂, h.symm⟩
        exact Disjoint.union_right
          ((hP_disj hne1).mono_right (hQ_sub j₂))
          ((hP_disj hne2).mono_right (hS_sub (prevFin r hr j₂)))
      · have hP_new_i₁ : P_new i₁ = P i₁ := dite_eq_right h₁
        have hP_new_i₂ : P_new i₂ = P i₂ := dite_eq_right h₂
        rw [hP_new_i₁, hP_new_i₂]
        exact hP_disj hne
  have hrange_eq : Set.range P_new = Set.range P := hP_unique.2 P_new hP_new_family
  let j₀ : Fin r := ⟨0, by omega⟩
  have hmem_range : P_reroute j₀ ∈ Set.range P := by
    rw [← hrange_eq]
    exact ⟨pIdx j₀, hP_new_eq j₀⟩
  rcases hmem_range with ⟨k, hk⟩
  have hadj_e₀ : (P_reroute j₀).toSubgraph.Adj (Q j₀).last (S (prevFin r hr j₀)).first :=
    Path.joinEdge_adj_last_first _ _ _ _
  rw [(P (pIdx j₀)).takeUntil_last, (P (pIdx (prevFin r hr j₀))).dropUntil_first, ← hk] at hadj_e₀
  exact (hcross j₀).2 k hadj_e₀.symm

/-- **Graph Minors I, (2.5) Step 2** (pages 44–45):
"There is no sequence $u_1, v_1, \dots, u_r, v_r$ of vertices of $G$, where $r \ge 1$, such that for
$1 \le i \le r$, $v_{i - 1}, u_i$ are adjacent, joined by an edge not in any of $P_1, \dots, P_m$
(setting $v_0 = v_r$), and for $1 \le i \le r$, $v_i$ occurs after $u_i$ on one of
$P_1, \dots, P_m$." -/
lemma lemma_2_5_step_2 {G : (⊤ : SimpleGraph α).Subgraph} {A₁ A₂ : Set α} {m r : ℕ}
    {P : Fin m → Path α} (hP_unique : IsUniqueDisjointPathFamily G A₁ A₂ P)
    (hr : 1 ≤ r) (u v : Fin r → α) (pIdx : Fin r → Fin m)
    (huv_prec : ∀ j, (P (pIdx j)).Precedes (u j) (v j))
    (hcross : ∀ j, IsCrossEdge G P (v (prevFin r hr j)) (u j)) :
    False := by
  classical
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hinj : Function.Injective pIdx
    · exact lemma_2_5_step_1 hP_unique hr u v pIdx hinj huv_prec hcross
    · simp only [Function.Injective, not_forall, exists_prop] at hinj
      rcases hinj with ⟨j₁, j₂, hp_eq, hj_ne⟩
      have hu₁ : u j₁ ∈ (P (pIdx j₁)).verts := (huv_prec j₁).fst_mem
      have hu₂ : u j₂ ∈ (P (pIdx j₁)).verts := hp_eq ▸ (huv_prec j₂).fst_mem
      have hex_pair :
          ∃ j j' : Fin r, j ≠ j' ∧ pIdx j = pIdx j' ∧ (P (pIdx j)).Precedes (u j) (v j') := by
        rcases (P (pIdx j₁)).precedes_or_eq_or_precedes hu₁ hu₂ with hprec | heq | hprec
        · refine ⟨j₁, j₂, hj_ne, hp_eq, hprec.trans (hp_eq ▸ huv_prec j₂)⟩
        · refine ⟨j₁, j₂, hj_ne, hp_eq, ?_⟩
          rw [heq, hp_eq]
          exact huv_prec j₂
        · refine ⟨j₂, j₁, Ne.symm hj_ne, hp_eq.symm, ?_⟩
          rw [← hp_eq]
          exact hprec.trans (huv_prec j₁)
      rcases hex_pair with ⟨j, j', hj_ne, hp_jj', huv_jj'⟩
      have hj_val_ne : j.val ≠ j'.val := Fin.val_ne_of_ne hj_ne
      let r' : ℕ := if j'.val < j.val then j.val - j'.val else r - (j'.val - j.val)
      have hr'_pos : 1 ≤ r' := by
        dsimp [r']
        split_ifs <;> omega
      have hr'_lt : r' < r := by
        dsimp [r']
        split_ifs <;> omega
      let idx (k : Fin r') : Fin r :=
        if h : j'.val + 1 + k.val < r then
          ⟨j'.val + 1 + k.val, h⟩
        else
          ⟨j'.val + 1 + k.val - r, by
            dsimp [r'] at k
            have := k.isLt
            split_ifs at this <;> omega⟩
      have hidx_last : ∀ k : Fin r', k.val + 1 = r' → idx k = j := by
        intro k hk
        by_cases h : j'.val + 1 + k.val < r
        · have hidx_eq : idx k = ⟨j'.val + 1 + k.val, h⟩ := dite_eq_left h
          rw [hidx_eq]
          ext; dsimp
          dsimp [r'] at hk
          split_ifs at hk <;> omega
        · have hidx_eq : idx k = ⟨j'.val + 1 + k.val - r, by omega⟩ := dite_eq_right h
          rw [hidx_eq]
          ext; dsimp
          dsimp [r'] at hk
          split_ifs at hk <;> omega
      have hidx_zero : ∀ k : Fin r', k.val = 0 → prevFin r hr (idx k) = j' := by
        intro k hk
        by_cases hlt : j'.val + 1 + k.val < r
        · have hidx_eq : idx k = ⟨j'.val + 1 + k.val, hlt⟩ := dite_eq_left hlt
          rw [hidx_eq, prevFin_eq_of_ne_zero hr (by dsimp; omega)]
          ext; dsimp; omega
        · have hidx_eq : idx k = ⟨j'.val + 1 + k.val - r, by omega⟩ := dite_eq_right hlt
          rw [hidx_eq, prevFin_eq_of_zero hr (by dsimp; omega)]
          ext; dsimp; omega
      have hidx_succ :
          ∀ k : Fin r', k.val ≠ 0 → prevFin r hr (idx k) = idx (prevFin r' hr'_pos k) := by
        intro k hk
        rw [prevFin_eq_of_ne_zero hr'_pos hk]
        by_cases hlt1 : j'.val + 1 + k.val < r
        · have hlt2 : j'.val + 1 + (k.val - 1) < r := by omega
          have h1 : idx k = ⟨j'.val + 1 + k.val, hlt1⟩ := dite_eq_left hlt1
          have h2 : idx ⟨k.val - 1, by omega⟩ = ⟨j'.val + 1 + (k.val - 1), hlt2⟩ :=
            dite_eq_left hlt2
          rw [h1, h2, prevFin_eq_of_ne_zero hr (by dsimp; omega)]
          ext; dsimp; omega
        · by_cases hlt2 : j'.val + 1 + (k.val - 1) < r
          · have h1 : idx k = ⟨j'.val + 1 + k.val - r, by omega⟩ := dite_eq_right hlt1
            have h2 : idx ⟨k.val - 1, by omega⟩ = ⟨j'.val + 1 + (k.val - 1), hlt2⟩ :=
              dite_eq_left hlt2
            rw [h1, h2, prevFin_eq_of_zero hr (by dsimp; omega)]
            ext; dsimp; omega
          · have h1 : idx k = ⟨j'.val + 1 + k.val - r, by omega⟩ := dite_eq_right hlt1
            have h2 : idx ⟨k.val - 1, by omega⟩ = ⟨j'.val + 1 + (k.val - 1) - r, by omega⟩ :=
              dite_eq_right hlt2
            rw [h1, h2, prevFin_eq_of_ne_zero hr (by dsimp; omega)]
            ext; dsimp; omega
      let u' (k : Fin r') : α := u (idx k)
      let v' (k : Fin r') : α := if k.val + 1 = r' then v j' else v (idx k)
      let pIdx' (k : Fin r') : Fin m := pIdx (idx k)
      refine ih r' hr'_lt hr'_pos u' v' pIdx' (fun k ↦ ?_) (fun k ↦ ?_)
      · dsimp [u', v', pIdx']
        split_ifs with hk
        · rw [hidx_last k hk]
          exact huv_jj'
        · exact huv_prec (idx k)
      · dsimp [u', v']
        by_cases hk0 : k.val = 0
        · have hprev_last : (prevFin r' hr'_pos k).val + 1 = r' := by
            rw [prevFin_eq_of_zero hr'_pos hk0]
            dsimp; omega
          rw [ite_eq_left hprev_last, ← hidx_zero k hk0]
          exact hcross (idx k)
        · have hprev_not_last : (prevFin r' hr'_pos k).val + 1 ≠ r' := by
            rw [prevFin_eq_of_ne_zero hr'_pos hk0]
            dsimp; omega
          rw [ite_eq_right hprev_not_last, ← hidx_succ k hk0]
          exact hcross (idx k)

/-- The strict partial order `u < v` on `V(G)` defined in Step 3 of (2.5) (Graph Minors I,
page 45): there is a sequence `u₀, v₀, …, uᵣ, vᵣ` (`r ≥ 0`) with `u₀ = u` and `vᵣ = v` such that
`v₀` occurs after `u₀` on some `Pᵢ`, for `1 ≤ j ≤ r` the vertices `v_{j-1}` and `uⱼ` are joined by
an edge of `G` not in any `Pᵢ`, for `1 ≤ j ≤ r - 1` the vertex `vⱼ` occurs after `uⱼ` on some `Pᵢ`,
and either `vᵣ = uᵣ` or `vᵣ` occurs after `uᵣ` on some `Pᵢ`. -/
def Step3Rel (G : (⊤ : SimpleGraph α).Subgraph) {m : ℕ} (P : Fin m → Path α) (u v : α) : Prop :=
  ∃ (r : ℕ) (uSeq vSeq : Fin (r + 1) → α) (pIdx : Fin (r + 1) → Fin m),
    uSeq 0 = u ∧ vSeq (Fin.last r) = v ∧
    (P (pIdx 0)).Precedes (uSeq 0) (vSeq 0) ∧
    (∀ j : Fin r, IsCrossEdge G P (vSeq j.castSucc) (uSeq j.succ)) ∧
    (∀ j : Fin r, j.val + 1 < r → (P (pIdx j.succ)).Precedes (uSeq j.succ) (vSeq j.succ)) ∧
    (vSeq (Fin.last r) = uSeq (Fin.last r) ∨
      (P (pIdx (Fin.last r))).Precedes (uSeq (Fin.last r)) (vSeq (Fin.last r)))

/-- **Graph Minors I, (2.5) Step 3 (transitivity)** (page 45):
If `u < v` and `v < w` under `Step3Rel`, then `u < w`. -/
lemma lemma_2_5_step_3_trans {G : (⊤ : SimpleGraph α).Subgraph} {A₁ A₂ : Set α} {m : ℕ}
    {P : Fin m → Path α} (hP_fam : IsDisjointPathFamily G A₁ A₂ P)
    {u v w : α} (huv : Step3Rel G P u v) (hvw : Step3Rel G P v w) :
    Step3Rel G P u w := by
  rcases huv with ⟨r, uSeq, vSeq, pIdx, hu0, hvr, hprec0, hcross, hprec_mid, hlast⟩
  rcases hvw with ⟨s, uSeq', vSeq', pIdx', hu0', hvs', hprec0', hcross', hprec_mid', hlast'⟩
  have hP_disj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts := hP_fam.2
  have hprec_all : ∀ k : Fin (r + 1), k.val < r → (P (pIdx k)).Precedes (uSeq k) (vSeq k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
    · have hk_eq : k = 0 := Fin.ext hk0
      rw [hk_eq]
      exact hprec0
    · let j : Fin r := ⟨k.val - 1, by omega⟩
      have hk_eq : k = j.succ := by
        ext; dsimp [j]; omega
      rw [hk_eq]
      exact hprec_mid j (by dsimp [j]; omega)
  have hprec_join : (P (pIdx' 0)).Precedes (uSeq (Fin.last r)) (vSeq' 0) := by
    rcases hlast with heq | hprec_r
    · rw [← heq, hvr, ← hu0']
      exact hprec0'
    · have hv_mem1 : v ∈ (P (pIdx (Fin.last r))).verts := hvr ▸ hprec_r.snd_mem
      have hv_mem2 : v ∈ (P (pIdx' 0)).verts := hu0' ▸ hprec0'.fst_mem
      have hp_eq : pIdx (Fin.last r) = pIdx' 0 := by
        by_contra hne
        exact (hP_disj hne).notMem_of_mem_left hv_mem1 hv_mem2
      rw [← hp_eq]
      have hprec0'' : (P (pIdx (Fin.last r))).Precedes (vSeq (Fin.last r)) (vSeq' 0) := by
        rw [hp_eq, hvr, ← hu0']
        exact hprec0'
      exact hprec_r.trans hprec0''
  let uCat (k : Fin (r + s + 1)) : α :=
    if h : k.val ≤ r then uSeq ⟨k.val, by omega⟩ else uSeq' ⟨k.val - r, by omega⟩
  let vCat (k : Fin (r + s + 1)) : α :=
    if h : k.val < r then vSeq ⟨k.val, by omega⟩ else vSeq' ⟨k.val - r, by omega⟩
  let pCat (k : Fin (r + s + 1)) : Fin m :=
    if h : k.val < r then pIdx ⟨k.val, by omega⟩ else pIdx' ⟨k.val - r, by omega⟩
  have huCat_le : ∀ (k : Fin (r + s + 1)) (h : k.val ≤ r), uCat k = uSeq ⟨k.val, by omega⟩ :=
    fun k h ↦ dite_eq_left h
  have huCat_gt : ∀ (k : Fin (r + s + 1)) (h : ¬ k.val ≤ r), uCat k = uSeq' ⟨k.val - r, by omega⟩ :=
    fun k h ↦ dite_eq_right h
  have hvCat_lt : ∀ (k : Fin (r + s + 1)) (h : k.val < r), vCat k = vSeq ⟨k.val, by omega⟩ :=
    fun k h ↦ dite_eq_left h
  have hvCat_ge : ∀ (k : Fin (r + s + 1)) (h : ¬ k.val < r), vCat k = vSeq' ⟨k.val - r, by omega⟩ :=
    fun k h ↦ dite_eq_right h
  have hpCat_lt : ∀ (k : Fin (r + s + 1)) (h : k.val < r), pCat k = pIdx ⟨k.val, by omega⟩ :=
    fun k h ↦ dite_eq_left h
  have hpCat_ge : ∀ (k : Fin (r + s + 1)) (h : ¬ k.val < r), pCat k = pIdx' ⟨k.val - r, by omega⟩ :=
    fun k h ↦ dite_eq_right h
  refine ⟨r + s, uCat, vCat, pCat, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [huCat_le 0 (by simp)]
    exact hu0
  · rw [hvCat_ge (Fin.last (r + s)) (by simp)]
    have heq : (⟨(Fin.last (r + s)).val - r, by omega⟩ : Fin (s + 1)) = Fin.last s := by
      ext; simp
    rw [heq]
    exact hvs'
  · by_cases hr0 : 0 < r
    · rw [hpCat_lt 0 (by simpa using hr0), huCat_le 0 (by simp), hvCat_lt 0 (by simpa using hr0)]
      exact hprec0
    · have hr_eq : r = 0 := by omega
      have h0_not_lt : ¬ (0 : Fin (r + s + 1)).val < r := by simp [hr_eq]
      rw [hpCat_ge 0 h0_not_lt, huCat_le 0 (by simp), hvCat_ge 0 h0_not_lt]
      have h0_last : (⟨(0 : Fin (r + s + 1)).val, by simp⟩ : Fin (r + 1)) = Fin.last r := by
        ext; simp [hr_eq]
      have h0_zero : (⟨(0 : Fin (r + s + 1)).val - r, by simp⟩ : Fin (s + 1)) = 0 := by
        ext; simp
      rw [h0_last, h0_zero]
      exact hprec_join
  · intro j
    by_cases hj : j.val < r
    · rw [hvCat_lt j.castSucc hj, huCat_le j.succ (by simp; omega)]
      exact hcross ⟨j.val, hj⟩
    · rw [hvCat_ge j.castSucc hj, huCat_gt j.succ (by simp; omega)]
      let j' : Fin s := ⟨j.val - r, by omega⟩
      have h1 : (⟨j.castSucc.val - r, by omega⟩ : Fin (s + 1)) = j'.castSucc := by
        ext; dsimp [j']
      have h2 : (⟨j.succ.val - r, by omega⟩ : Fin (s + 1)) = j'.succ := by
        ext; dsimp [j']; omega
      rw [h1, h2]
      exact hcross' j'
  · intro j hj_lt
    have hjsucc : j.succ.val = j.val + 1 := rfl
    by_cases hj1 : j.succ.val < r
    · rw [hpCat_lt j.succ hj1, huCat_le j.succ (by omega), hvCat_lt j.succ hj1]
      exact hprec_all ⟨j.succ.val, by omega⟩ hj1
    · by_cases hj2 : j.succ.val = r
      · rw [hpCat_ge j.succ hj1, huCat_le j.succ (by omega), hvCat_ge j.succ hj1]
        have h1 : (⟨j.succ.val, by omega⟩ : Fin (r + 1)) = Fin.last r := by
          ext; simpa using hj2
        have h2 : (⟨j.succ.val - r, by omega⟩ : Fin (s + 1)) = 0 := by
          ext; dsimp; omega
        rw [h1, h2]
        exact hprec_join
      · rw [hpCat_ge j.succ hj1, huCat_gt j.succ (by omega), hvCat_ge j.succ hj1]
        let j' : Fin s := ⟨j.succ.val - r - 1, by omega⟩
        have h_eq : (⟨j.succ.val - r, by omega⟩ : Fin (s + 1)) = j'.succ := by
          ext; dsimp [j']; omega
        rw [h_eq]
        exact hprec_mid' j' (by dsimp [j']; omega)
  · by_cases hs0 : s = 0
    · rw [hpCat_ge (Fin.last (r + s)) (by simp), huCat_le (Fin.last (r + s)) (by simp [hs0]),
        hvCat_ge (Fin.last (r + s)) (by simp)]
      have h1 : (⟨(Fin.last (r + s)).val, by omega⟩ : Fin (r + 1)) = Fin.last r := by
        ext; simp [hs0]
      have h2 : (⟨(Fin.last (r + s)).val - r, by omega⟩ : Fin (s + 1)) = 0 := by
        ext; simp [hs0]
      rw [h1, h2]
      exact Or.inr hprec_join
    · rw [hpCat_ge (Fin.last (r + s)) (by simp),
        huCat_gt (Fin.last (r + s)) (by simp; omega),
        hvCat_ge (Fin.last (r + s)) (by simp)]
      have h_eq : (⟨(Fin.last (r + s)).val - r, by omega⟩ : Fin (s + 1)) = Fin.last s := by
        ext; simp
      rw [h_eq]
      exact hlast'

/-- **Graph Minors I, (2.5) Step 3 (irreflexivity)** (page 45):
For every vertex `v`, `¬ Step3Rel G P v v`. -/
lemma lemma_2_5_step_3_irrefl {G : (⊤ : SimpleGraph α).Subgraph} {A₁ A₂ : Set α} {m : ℕ}
    {P : Fin m → Path α} (hP_unique : IsUniqueDisjointPathFamily G A₁ A₂ P) (v : α) :
    ¬ Step3Rel G P v v := by
  rintro ⟨r, uSeq, vSeq, pIdx, hu0, hvr, hprec0, hcross, hprec_mid, hlast⟩
  have hP_disj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts := hP_unique.1.2
  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
  · have h0 : Fin.last 0 = (0 : Fin 1) := rfl
    rw [h0] at hvr
    rw [hu0, hvr] at hprec0
    exact hprec0.ne rfl
  · have hprec_last : (P (pIdx 0)).Precedes (uSeq (Fin.last r)) (vSeq 0) := by
      rcases hlast with heq | hprec_r
      · rw [← heq, hvr, ← hu0]
        exact hprec0
      · have hv_mem1 : v ∈ (P (pIdx (Fin.last r))).verts := hvr ▸ hprec_r.snd_mem
        have hv_mem2 : v ∈ (P (pIdx 0)).verts := hu0 ▸ hprec0.fst_mem
        have hp_eq : pIdx (Fin.last r) = pIdx 0 := by
          by_contra hne
          exact (hP_disj hne).notMem_of_mem_left hv_mem1 hv_mem2
        rw [← hp_eq]
        have hprec0' : (P (pIdx (Fin.last r))).Precedes (vSeq (Fin.last r)) (vSeq 0) := by
          rw [hp_eq, hvr, ← hu0]
          exact hprec0
        exact hprec_r.trans hprec0'
    let u' (j : Fin r) : α := uSeq j.succ
    let v' (j : Fin r) : α := if j.val + 1 = r then vSeq 0 else vSeq j.succ
    let pIdx' (j : Fin r) : Fin m := if j.val + 1 = r then pIdx 0 else pIdx j.succ
    refine lemma_2_5_step_2 hP_unique hr_pos u' v' pIdx' (fun j ↦ ?_) (fun j ↦ ?_)
    · dsimp [u', v', pIdx']
      split_ifs with hj
      · have hj_last : j.succ = Fin.last r := by
          ext; dsimp; exact hj
        rw [hj_last]
        exact hprec_last
      · exact hprec_mid j (by omega)
    · dsimp [u', v']
      by_cases hj0 : j.val = 0
      · have hprev_last : (prevFin r hr_pos j).val + 1 = r := by
          rw [prevFin_eq_of_zero hr_pos hj0]
          dsimp; omega
        rw [ite_eq_left hprev_last]
        have hj_eq : j = ⟨0, hr_pos⟩ := Fin.ext hj0
        rw [hj_eq]
        exact hcross ⟨0, hr_pos⟩
      · have hprev_not_last : (prevFin r hr_pos j).val + 1 ≠ r := by
          rw [prevFin_eq_of_ne_zero hr_pos hj0]
          dsimp; omega
        rw [ite_eq_right hprev_not_last]
        have hprev_succ : (prevFin r hr_pos j).succ = j.castSucc := by
          rw [prevFin_eq_of_ne_zero hr_pos hj0]
          ext; dsimp; omega
        rw [hprev_succ]
        exact hcross j

/-! ### Step 4 and Proof of (2.5) (pages 45–46) -/

private lemma exists_support_getElem_of_toSubgraph_adj {V : Type*} {G : SimpleGraph V}
    {a b u v : V} (w : G.Walk a b) (hadj : w.toSubgraph.Adj u v) :
    ∃ (k : ℕ) (hk : k + 1 < w.support.length),
      (w.support[k] = u ∧ w.support[k + 1] = v) ∨
        (w.support[k] = v ∧ w.support[k + 1] = u) := by
  induction w with
  | nil => simp at hadj
  | @cons x y z h w ih =>
    change (G.subgraphOfAdj h ⊔ w.toSubgraph).Adj u v at hadj
    rw [Subgraph.sup_adj, subgraphOfAdj_adj] at hadj
    rcases hadj with heq | hadj'
    · refine ⟨0, by simp [Walk.support_cons], ?_⟩
      have h0 : (Walk.cons h w).support[0] = x := rfl
      have h1 : (Walk.cons h w).support[1] = y := by simp [Walk.support_cons]
      rw [h0, h1]
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rcases ih hadj' with ⟨k, hk, hkv⟩
      have hlen : (Walk.cons h w).support.length = w.support.length + 1 := by
        simp [Walk.support_cons]
      refine ⟨k + 1, by omega, ?_⟩
      simpa [Walk.support_cons] using hkv

lemma Path.not_toSubgraph_adj_of_precedes_precedes (P : Path α) {u u' v : α}
    (h1 : P.Precedes u u') (h2 : P.Precedes u' v) :
    ¬ P.toSubgraph.Adj u v := by
  classical
  intro hadj
  rcases exists_support_getElem_of_toSubgraph_adj P.walk hadj with ⟨k, hk, ⟨hku, hkv⟩ | ⟨hkv, hku⟩⟩
  · have hidx_u : P.walk.support.idxOf u = k := by
      rw [← hku]
      exact P.support_nodup.idxOf_getElem k (by omega)
    have hidx_v : P.walk.support.idxOf v = k + 1 := by
      rw [← hkv]
      exact P.support_nodup.idxOf_getElem (k + 1) hk
    have hlt1 := (P.precedes_iff_idxOf.1 h1).2.2
    have hlt2 := (P.precedes_iff_idxOf.1 h2).2.2
    omega
  · have hidx_v : P.walk.support.idxOf v = k := by
      rw [← hkv]
      exact P.support_nodup.idxOf_getElem k (by omega)
    have hidx_u : P.walk.support.idxOf u = k + 1 := by
      rw [← hku]
      exact P.support_nodup.idxOf_getElem (k + 1) hk
    have hlt1 := (P.precedes_iff_idxOf.1 h1).2.2
    have hlt2 := (P.precedes_iff_idxOf.1 h2).2.2
    omega

private lemma exists_adj_mem_notMem_of_walk {V : Type*} {G : SimpleGraph V} {X : Set V}
    {a b : V} (w : G.Walk a b) (ha : a ∈ X) (hb : b ∉ X) :
    ∃ u v, w.toSubgraph.Adj u v ∧ u ∈ X ∧ v ∉ X := by
  induction w with
  | nil => exact (hb ha).elim
  | @cons x y z h w ih =>
    by_cases hy : y ∈ X
    · rcases ih hy hb with ⟨u, v, hadj, hu, hv⟩
      exact ⟨u, v, Subgraph.sup_adj.2 (Or.inr hadj), hu, hv⟩
    · exact ⟨x, y, Subgraph.sup_adj.2 (Or.inl (by simp)), ha, hy⟩

lemma Path.exists_isFirstGe_of_mem (P : Path α) (μ : α → ℤ) (t : ℤ) {v : α}
    (hv : v ∈ P.verts) (ht : t ≤ μ v) :
    ∃ u', P.IsFirstGe μ t u' ∧ (u' = v ∨ P.Precedes u' v) := by
  have hne : (P.verts ∩ {w | t ≤ μ w}).Nonempty := ⟨v, hv, ht⟩
  rcases P.exists_first_mem hne with ⟨u', ⟨hu'_mem, hu'_ge⟩, hu'_min⟩
  refine ⟨u', ⟨hu'_mem, hu'_ge, fun w hw hprec ↦ ?_⟩, hu'_min v ⟨hv, ht⟩⟩
  by_contra hnot
  have hnot' : t ≤ μ w := not_lt.1 hnot
  rcases hu'_min w ⟨hw, hnot'⟩ with rfl | hprec'
  · exact hprec.ne rfl
  · exact hprec.asymm hprec'

lemma step3Rel_of_precedes (G : (⊤ : SimpleGraph α).Subgraph) {m : ℕ} (P : Fin m → Path α)
    (i : Fin m) {u v : α} (hprec : (P i).Precedes u v) :
    Step3Rel G P u v :=
  ⟨0, fun _ ↦ u, fun k ↦ if k = 0 then v else u, fun _ ↦ i,
    rfl, rfl, hprec, fun j ↦ j.elim0, fun j ↦ j.elim0, Or.inr hprec⟩

/-- **Graph Minors I, (2.5)** (page 44):
"If $A_1, A_2 \subseteq V(G)$, and there is a unique set $\{P_1, \dots, P_m\}$ of $m$ disjoint paths
in $G$ from $A_1$ to $A_2$, and every vertex of $G$ is in one of these paths, then there is an
integer-valued function $\mu$ defined on $V(G)$, such that
(i) if $v'$ is after $v$ on $P_i$, then $\mu(v') > \mu(v)$ ($1 \le i \le m$);
(ii) for any integer $t$, $Z_t$ separates $\{v \colon \mu(v) < t\}$ from
$\{v \colon \mu(v) \ge t\}$, where
$Z_t = \{v \colon \text{for some } i, v \text{ is the first vertex on } P_i \text{ with } \mu(v) \ge t\}$."
This is the simple special case. The full statement is `GM01.Full.theorem_2_5_proof`. -/
theorem theorem_2_5_simple {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite)
    {A₁ A₂ : Set α} {m : ℕ} (P : Fin m → Path α)
    (hP_unique : IsUniqueDisjointPathFamily G A₁ A₂ P)
    (hP_span : G.verts ⊆ ⋃ i, (P i).verts) :
    ∃ μ : α → ℤ,
      (∀ i (v v' : α), (P i).Precedes v v' → μ v < μ v') ∧
      ∀ t : ℤ, Separates G {v | ∃ i, (P i).IsFirstGe μ t v}
        {v | μ v < t} {v | t ≤ μ v} := by
  classical
  let μ (v : α) : ℤ := ({w ∈ G.verts | Step3Rel G P w v}.ncard : ℤ)
  have hμ_lt_of_step3Rel : ∀ {u v : α}, u ∈ G.verts → Step3Rel G P u v → μ u < μ v := by
    intro u v hu huv
    let Su : Set α := {w ∈ G.verts | Step3Rel G P w u}
    let Sv : Set α := {w ∈ G.verts | Step3Rel G P w v}
    have hSv_fin : Sv.Finite := hfin.subset (fun x hx ↦ hx.1)
    have hsub : Su ⊆ Sv := fun w ⟨hw, hwu⟩ ↦ ⟨hw, lemma_2_5_step_3_trans hP_unique.1 hwu huv⟩
    have hu_mem : u ∈ Sv := ⟨hu, huv⟩
    have hu_notMem : u ∉ Su := fun ⟨_, huu⟩ ↦ lemma_2_5_step_3_irrefl hP_unique u huu
    have hssub : Su ⊂ Sv := LE.le.ssubset_of_mem_notMem hsub hu_mem hu_notMem
    have hlt_nat : Su.ncard < Sv.ncard := Set.ncard_lt_ncard hssub hSv_fin
    exact Int.ofNat_lt.2 hlt_nat
  have hμ_mono : ∀ i (v v' : α), (P i).Precedes v v' → μ v < μ v' := by
    intro i v v' hprec
    have hv_verts : v ∈ G.verts := (hP_unique.1.1 i).1.1 hprec.fst_mem
    exact hμ_lt_of_step3Rel hv_verts (step3Rel_of_precedes G P i hprec)
  refine ⟨μ, hμ_mono, fun t Q hQ hQ_avoids ↦ ?_⟩
  have hfirst_in : Q.first ∈ {w : α | μ w < t} := hQ.2.1
  have hlast_out : Q.last ∉ {w : α | μ w < t} := by
    change ¬ μ Q.last < t
    have : t ≤ μ Q.last := hQ.2.2
    omega
  rcases exists_adj_mem_notMem_of_walk Q.walk hfirst_in hlast_out with ⟨u, v, hadj_Q, hu_lt, hv_ge⟩
  change μ u < t at hu_lt
  have hv_ge' : t ≤ μ v := not_lt.1 hv_ge
  have hadj_G : G.Adj u v := hQ.1.2 hadj_Q
  have hv_Q : v ∈ Q.verts := hadj_Q.snd_mem
  have hv_G : v ∈ G.verts := hadj_G.snd_mem
  have hv_union : v ∈ ⋃ i, (P i).verts := hP_span hv_G
  rcases mem_iUnion.1 hv_union with ⟨i, hv_Pi⟩
  rcases (P i).exists_isFirstGe_of_mem μ t hv_Pi hv_ge' with ⟨u', hu'_first, hu'_eq_or_prec⟩
  have hu'_Z : u' ∈ {w | ∃ i, (P i).IsFirstGe μ t w} := ⟨i, hu'_first⟩
  have hv_not_Z : v ∉ {w | ∃ i, (P i).IsFirstGe μ t w} :=
    hQ_avoids.notMem_of_mem_left hv_Q
  have hu'_prec_v : (P i).Precedes u' v := by
    rcases hu'_eq_or_prec with rfl | hprec
    · exact (hv_not_Z hu'_Z).elim
    · exact hprec
  have hcross_vu : IsCrossEdge G P v u := by
    refine ⟨hadj_G.symm, fun k hadj_Pk ↦ ?_⟩
    have hv_Pk : v ∈ (P k).verts := hadj_Pk.fst_mem
    have hk_eq : k = i := by
      by_contra hne
      exact (hP_unique.1.2 hne).notMem_of_mem_left hv_Pk hv_Pi
    subst hk_eq
    have hu_Pi : u ∈ (P k).verts := hadj_Pk.snd_mem
    have hu'_Pi : u' ∈ (P k).verts := hu'_first.1
    have hu_prec_u' : (P k).Precedes u u' := by
      rcases (P k).precedes_or_eq_or_precedes hu_Pi hu'_Pi with hprec | rfl | hprec
      · exact hprec
      · have := hu'_first.2.1; omega
      · have := hμ_mono k u' u hprec
        have := hu'_first.2.1
        omega
    exact (P k).not_toSubgraph_adj_of_precedes_precedes hu_prec_u' hu'_prec_v hadj_Pk.symm
  have hstep_u'_u : Step3Rel G P u' u := by
    let uSeq : Fin 2 → α := fun k ↦ if k = 0 then u' else u
    let vSeq : Fin 2 → α := fun k ↦ if k = 0 then v else u
    let pIdx : Fin 2 → Fin m := fun _ ↦ i
    refine ⟨1, uSeq, vSeq, pIdx, rfl, rfl, hu'_prec_v, ?_, ?_, Or.inl rfl⟩
    · intro j
      have hj0 : j = 0 := Subsingleton.elim j 0
      subst hj0
      exact hcross_vu
    · intro j hj
      omega
  have hu'_G : u' ∈ G.verts := (hP_unique.1.1 i).1.1 hu'_first.1
  have hμ_u'_lt_u : μ u' < μ u := hμ_lt_of_step3Rel hu'_G hstep_u'_u
  have hμ_u'_ge : t ≤ μ u' := hu'_first.2.1
  omega

/-! ### Proof of (2.6) (pages 46–47) -/

lemma Path.isFirstGe_unique (P : Path α) (μ : α → ℤ) (t : ℤ) {u v : α}
    (hu : P.IsFirstGe μ t u) (hv : P.IsFirstGe μ t v) : u = v := by
  rcases P.precedes_or_eq_or_precedes hu.1 hv.1 with hprec | heq | hprec
  · have := hv.2.2 u hu.1 hprec
    have := hu.2.1
    omega
  · exact heq
  · have := hu.2.2 v hv.1 hprec
    have := hv.2.1
    omega

private lemma finite_and_ncard_Z_le {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite)
    {m : ℕ} (P : Fin m → Path α) (hP_le : ∀ i, (P i).toSubgraph ≤ G)
    (μ : α → ℤ) (t : ℤ) :
    {v | ∃ i, (P i).IsFirstGe μ t v}.Finite ∧ {v | ∃ i, (P i).IsFirstGe μ t v}.ncard ≤ m := by
  classical
  let V := hfin.toFinset
  let F (i : Fin m) : Finset α := V.filter (fun v ↦ (P i).IsFirstGe μ t v)
  have hF_card : ∀ i, (F i).card ≤ 1 := by
    intro i
    rw [Finset.card_le_one]
    intro u hu v hv
    rw [Finset.mem_filter] at hu hv
    exact (P i).isFirstGe_unique μ t hu.2 hv.2
  let S : Finset α := Finset.univ.biUnion F
  have hS_eq : (S : Set α) = {v | ∃ i, (P i).IsFirstGe μ t v} := by
    ext v
    simp only [S, F, V, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, Finite.mem_toFinset]
    exact ⟨fun ⟨i, _, hf⟩ ↦ ⟨i, hf⟩, fun ⟨i, hf⟩ ↦ ⟨i, (hP_le i).1 hf.1, hf⟩⟩
  refine ⟨hS_eq ▸ S.finite_toSet, ?_⟩
  rw [← hS_eq, Set.ncard_coe_finset]
  calc
    S.card ≤ ∑ i : Fin m, (F i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum (fun i _ ↦ hF_card i)
    _ = m := by simp

private lemma mem_Z_of_mu_eq {G : (⊤ : SimpleGraph α).Subgraph} {m : ℕ} (P : Fin m → Path α)
    (hP_span : G.verts ⊆ ⋃ i, (P i).verts) (μ : α → ℤ)
    (hμ_mono : ∀ i (v v' : α), (P i).Precedes v v' → μ v < μ v')
    {v : α} (hv : v ∈ G.verts) (t : ℤ) (hμv : μ v = t) :
    v ∈ {w | ∃ i, (P i).IsFirstGe μ t w} := by
  rcases mem_iUnion.1 (hP_span hv) with ⟨i, hv_Pi⟩
  refine ⟨i, hv_Pi, by omega, fun u _ hprec ↦ ?_⟩
  have := hμ_mono i u v hprec
  omega

private lemma card_filter_meets_le {n : ℕ} (B : Fin n → (⊤ : SimpleGraph α).Subgraph)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    {X : Set α} (hX : X.Finite)
    [DecidablePred fun j : Fin n ↦ ((B j).verts ∩ X).Nonempty] :
    (Finset.univ.filter (fun j : Fin n ↦ ((B j).verts ∩ X).Nonempty)).card ≤ X.ncard := by
  classical
  let F := Finset.univ.filter (fun j : Fin n ↦ ((B j).verts ∩ X).Nonempty)
  rcases F.eq_empty_or_nonempty with hF_empty | ⟨j₀, hj₀⟩
  · simp [F, hF_empty]
  · rw [Finset.mem_filter] at hj₀
    let a₀ : α := hj₀.2.some
    let f (j : Fin n) : α :=
      if h : ((B j).verts ∩ X).Nonempty then h.some else a₀
    have hf_maps : Set.MapsTo f F hX.toFinset := by
      intro j hj
      rw [Finset.mem_coe, Finset.mem_filter] at hj
      rw [Finset.mem_coe, Finite.mem_toFinset]
      have h_eq : f j = hj.2.some := dite_eq_left hj.2
      rw [h_eq]
      exact hj.2.some_mem.2
    have hf_inj : Set.InjOn f F := by
      intro j₁ hj₁ j₂ hj₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hj₁ hj₂
      have h₁ : f j₁ ∈ (B j₁).verts := by
        have h_eq : f j₁ = hj₁.2.some := dite_eq_left hj₁.2
        rw [h_eq]
        exact hj₁.2.some_mem.1
      have h₂ : f j₂ ∈ (B j₂).verts := by
        have h_eq : f j₂ = hj₂.2.some := dite_eq_left hj₂.2
        rw [h_eq]
        exact hj₂.2.some_mem.1
      rw [heq] at h₁
      by_contra hne
      exact (hB_disj hne).notMem_of_mem_left h₁ h₂
    calc
      F.card ≤ hX.toFinset.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
      _ = X.ncard := by rw [← Set.ncard_coe_finset, Finite.coe_toFinset]

/-- **Graph Minors I, (2.6)** (page 46):
"Suppose that $G \in \mathcal{F}_\theta$, and $A_1, A_2 \subseteq V(G)$, and $m > 0$ is an integer,
and the following conditions are satisfied:
(i) there is a unique set $\{P_1, \dots, P_m\}$ of $m$ disjoint paths in $G$ from $A_1$ to $A_2$;
(ii) every vertex of $G$ is in one of $P_1, \dots, P_m$;
(iii) $B_1, \dots, B_n$ are disjoint connected subgraphs of $G$, and each $B_j$ meets at least
$\frac{1}{2}\theta^2$ of $P_1, \dots, P_m$.
Then $n < 2m\theta^{2\theta - 2} \binom{m}{\frac{1}{2}\theta^2}$."

The proof of (2.6), pages 46–47, bounds the new blocks by the union
`Z_{k_{l'} - 1} ∪ Z_{k_{l'}}`, as printed. The general-graph form is
`GM01.Full.theorem_2_6_proof`. -/
theorem theorem_2_6_simple {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) (hm : θ ^ 2 / 2 ≤ m)
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    {A₁ A₂ : Set α} (P : Fin m → Path α)
    (hP_unique : IsUniqueDisjointPathFamily G A₁ A₂ P)
    (hP_span : G.verts ⊆ ⋃ i, (P i).verts)
    (B : Fin n → (⊤ : SimpleGraph α).Subgraph)
    (hB_le : ∀ j, B j ≤ G) (hB_conn : ∀ j, (B j).Connected)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hB_meet : ∀ j, θ ^ 2 / 2 ≤ {i : Fin m | ((P i).verts ∩ (B j).verts).Nonempty}.ncard) :
    n < 2 * m * θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) := by
  classical
  rcases theorem_2_5_simple hfin P hP_unique hP_span with ⟨μ, hμ_mono, hμ_sep⟩
  have hP_le : ∀ i, (P i).toSubgraph ≤ G := fun i ↦ (hP_unique.1.1 i).1
  let Z (t : ℤ) : Set α := {v | ∃ i, (P i).IsFirstGe μ t v}
  have hZ_fin : ∀ t, (Z t).Finite := fun t ↦ (finite_and_ncard_Z_le hfin P hP_le μ t).1
  have hZ_card : ∀ t, (Z t).ncard ≤ m := fun t ↦ (finite_and_ncard_Z_le hfin P hP_le μ t).2
  have hB_fin : ∀ j, (B j).verts.Finite := fun j ↦ hfin.subset (hB_le j).1
  have hB_ne : ∀ j, ((hB_fin j).toFinset.image μ).Nonempty := by
    intro j
    rcases (hB_conn j).nonempty with ⟨v, hv⟩
    exact ⟨μ v, Finset.mem_image.2 ⟨v, (hB_fin j).mem_toFinset.2 hv, rfl⟩⟩
  let maxμ (j : Fin n) : ℤ := ((hB_fin j).toFinset.image μ).max' (hB_ne j)
  have hmaxμ_le : ∀ j, ∀ v ∈ (B j).verts, μ v ≤ maxμ j := by
    intro j v hv
    exact Finset.le_max' _ (μ v) (Finset.mem_image.2 ⟨v, (hB_fin j).mem_toFinset.2 hv, rfl⟩)
  have hmaxμ_mem : ∀ j, ∃ v ∈ (B j).verts, μ v = maxμ j := by
    intro j
    have hmem := Finset.max'_mem ((hB_fin j).toFinset.image μ) (hB_ne j)
    rcases Finset.mem_image.1 hmem with ⟨v, hv, hμv⟩
    exact ⟨v, (hB_fin j).mem_toFinset.1 hv, hμv⟩
  let J (t : ℤ) : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n ↦ ∃ v ∈ (B j).verts, μ v < t)
  have hstep_bound :
      ∀ (E : Finset (Fin n)) (j₀ : Fin n),
        j₀ ∈ E → (∀ j ∈ E, maxμ j₀ ≤ maxμ j) →
        (E.filter (fun j ↦ ∃ v ∈ (B j).verts, μ v < maxμ j₀ + 1)).card ≤ 2 * m := by
    intro E j₀ hj₀_mem hj₀_min
    let k : ℤ := maxμ j₀ + 1
    let X : Set α := Z (k - 1) ∪ Z k
    have hX_fin : X.Finite := (hZ_fin (k - 1)).union (hZ_fin k)
    have hX_card : X.ncard ≤ 2 * m := by
      calc
        X.ncard ≤ (Z (k - 1)).ncard + (Z k).ncard := Set.ncard_union_le _ _
        _ ≤ m + m := Nat.add_le_add (hZ_card (k - 1)) (hZ_card k)
        _ = 2 * m := by omega
    have hsub :
        E.filter (fun j ↦ ∃ v ∈ (B j).verts, μ v < k) ⊆
          Finset.univ.filter (fun j : Fin n ↦ ((B j).verts ∩ X).Nonempty) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ j, ?_⟩
      rcases hj with ⟨hjE, u, huB, hu_lt⟩
      by_cases hex_ge : ∃ u' ∈ (B j).verts, k ≤ μ u'
      · rcases hex_ge with ⟨u', hu'B, hu'_ge⟩
        rcases exists_path_of_preconnected (hB_conn j).preconnected huB hu'B with
          ⟨Q, hQ_le_B, hQ_first, hQ_last⟩
        have hQ_fromTo : Q.IsFromTo G {v | μ v < k} {v | k ≤ μ v} :=
          ⟨hQ_le_B.trans (hB_le j), hQ_first.symm ▸ hu_lt, hQ_last.symm ▸ hu'_ge⟩
        have hnot_avoids : ¬ Q.Avoids (Z k) := hμ_sep k Q hQ_fromTo
        rw [Path.Avoids, Set.not_disjoint_iff] at hnot_avoids
        rcases hnot_avoids with ⟨w, hwQ, hwZ⟩
        exact ⟨w, hQ_le_B.1 hwQ, Or.inr hwZ⟩
      · have hall_lt : ∀ v ∈ (B j).verts, μ v < k := by
          intro v hv
          by_contra hge
          exact hex_ge ⟨v, hv, not_lt.1 hge⟩
        rcases hmaxμ_mem j with ⟨v, hvB, hμv⟩
        have hv_lt : μ v < k := hall_lt v hvB
        have hv_ge : maxμ j₀ ≤ μ v := hμv.symm ▸ hj₀_min j hjE
        have hμv_eq : μ v = k - 1 := by dsimp [k] at hv_lt ⊢; omega
        have hvZ : v ∈ Z (k - 1) :=
          mem_Z_of_mu_eq P hP_span μ hμ_mono ((hB_le j).1 hvB) (k - 1) hμv_eq
        exact ⟨v, hvB, Or.inl hvZ⟩
    calc
      (E.filter (fun j ↦ ∃ v ∈ (B j).verts, μ v < k)).card ≤
          (Finset.univ.filter (fun j : Fin n ↦ ((B j).verts ∩ X).Nonempty)).card :=
        Finset.card_le_card hsub
      _ ≤ X.ncard := card_filter_meets_le B hB_disj hX_fin
      _ ≤ 2 * m := hX_card
  have hm_pos : 0 < m := by
    have : 36 ≤ θ ^ 2 := by nlinarith
    omega
  have hind :
      ∀ l : ℕ, 2 * l * m ≤ n →
        ∃ (kSeq : Fin l → ℤ) (jSeq : Fin l → Fin n),
          (∀ r : Fin l, ∀ v ∈ (B (jSeq r)).verts, μ v < kSeq r) ∧
          (∀ r₁ r₂ : Fin l, r₁ < r₂ → ∀ v ∈ (B (jSeq r₂)).verts, kSeq r₁ ≤ μ v) ∧
          (∀ r₁ r₂ : Fin l, r₁ ≤ r₂ → kSeq r₁ ≤ kSeq r₂) ∧
          (∀ r : Fin l, (J (kSeq r)).card ≤ 2 * (r.val + 1) * m) := by
    intro l
    induction l with
    | zero =>
      intro _
      exact ⟨Fin.elim0, Fin.elim0, fun r ↦ r.elim0, fun r ↦ r.elim0,
        fun r ↦ r.elim0, fun r ↦ r.elim0⟩
    | succ l ih =>
      intro hln
      have hln' : 2 * l * m ≤ n := by
        calc
          2 * l * m ≤ 2 * (l + 1) * m := by nlinarith
          _ ≤ n := hln
      rcases ih hln' with ⟨kSeq, jSeq, hk_upper, hk_lower, hk_mono, hJ_card⟩
      rcases Nat.eq_zero_or_pos l with rfl | hl_pos
      · have hn_pos : 0 < n := by nlinarith
        have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty := by
          have : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
          exact Finset.univ_nonempty
        rcases Finset.exists_min_image Finset.univ maxμ huniv_ne with ⟨j₀, hj₀_mem, hj₀_min⟩
        let k₀ : ℤ := maxμ j₀ + 1
        refine ⟨fun _ ↦ k₀, fun _ ↦ j₀, ?_, ?_, ?_, ?_⟩
        · intro _ v hv
          have := hmaxμ_le j₀ v hv
          dsimp [k₀]; omega
        · intro r₁ r₂ hlt
          omega
        · intro _ _ _
          exact le_rfl
        · intro r
          have hr0 : r.val = 0 := by omega
          rw [hr0]
          have hJ_eq :
              J k₀ = (Finset.univ : Finset (Fin n)).filter (fun j ↦ ∃ v ∈ (B j).verts, μ v < k₀) :=
            rfl
          rw [hJ_eq]
          simpa using hstep_bound Finset.univ j₀ hj₀_mem hj₀_min
      · let r_last : Fin l := ⟨l - 1, by omega⟩
        let E : Finset (Fin n) := Finset.univ \ J (kSeq r_last)
        have hJ_last_lt : (J (kSeq r_last)).card < (Finset.univ : Finset (Fin n)).card := by
          rw [Finset.card_univ, Fintype.card_fin]
          have h1 := hJ_card r_last
          have hr_val : r_last.val + 1 = l := by dsimp [r_last]; omega
          rw [hr_val] at h1
          have hlt_m : 2 * l * m < 2 * (l + 1) * m := by nlinarith
          omega
        have hE_ne : E.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          have hsub : (Finset.univ : Finset (Fin n)) ⊆ J (kSeq r_last) :=
            Finset.sdiff_eq_empty_iff_subset.1 hempty
          exact not_le_of_gt hJ_last_lt (Finset.card_le_card hsub)
        rcases Finset.exists_min_image E maxμ hE_ne with ⟨j₀, hj₀_mem, hj₀_min⟩
        let k₀ : ℤ := maxμ j₀ + 1
        have hj₀_not_J : j₀ ∉ J (kSeq r_last) := (Finset.mem_sdiff.1 hj₀_mem).2
        have hj₀_ge_last : ∀ v ∈ (B j₀).verts, kSeq r_last ≤ μ v := by
          intro v hv
          by_contra hlt
          exact hj₀_not_J (Finset.mem_filter.2 ⟨Finset.mem_univ j₀, v, hv, not_le.1 hlt⟩)
        have hk_last_lt_k₀ : kSeq r_last < k₀ := by
          rcases (hB_conn j₀).nonempty with ⟨v₀, hv₀⟩
          have h1 := hj₀_ge_last v₀ hv₀
          have h2 := hmaxμ_le j₀ v₀ hv₀
          dsimp [k₀]; omega
        have hJ_sdiff_eq :
            J k₀ \ J (kSeq r_last) = E.filter (fun j ↦ ∃ v ∈ (B j).verts, μ v < k₀) := by
          ext j
          simp only [J, E, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
        have hJ_k₀_card : (J k₀).card ≤ 2 * (l + 1) * m := by
          calc
            (J k₀).card ≤ (J k₀ \ J (kSeq r_last)).card + (J (kSeq r_last)).card :=
              Finset.card_le_card_sdiff_add_card
            _ ≤ 2 * m + 2 * (r_last.val + 1) * m := by
              rw [hJ_sdiff_eq]
              exact Nat.add_le_add (hstep_bound E j₀ hj₀_mem hj₀_min) (hJ_card r_last)
            _ = 2 * (l + 1) * m := by
              have : r_last.val + 1 = l := by dsimp [r_last]; omega
              rw [this]
              linarith
        let kSeq' (r : Fin (l + 1)) : ℤ :=
          if h : r.val < l then kSeq ⟨r.val, h⟩ else k₀
        let jSeq' (r : Fin (l + 1)) : Fin n :=
          if h : r.val < l then jSeq ⟨r.val, h⟩ else j₀
        have hkSeq'_lt : ∀ (r : Fin (l + 1)) (h : r.val < l), kSeq' r = kSeq ⟨r.val, h⟩ :=
          fun r h ↦ dite_eq_left h
        have hkSeq'_ge : ∀ (r : Fin (l + 1)) (h : ¬ r.val < l), kSeq' r = k₀ :=
          fun r h ↦ dite_eq_right h
        have hjSeq'_lt : ∀ (r : Fin (l + 1)) (h : r.val < l), jSeq' r = jSeq ⟨r.val, h⟩ :=
          fun r h ↦ dite_eq_left h
        have hjSeq'_ge : ∀ (r : Fin (l + 1)) (h : ¬ r.val < l), jSeq' r = j₀ :=
          fun r h ↦ dite_eq_right h
        refine ⟨kSeq', jSeq', ?_, ?_, ?_, ?_⟩
        · intro r v hv
          by_cases hr : r.val < l
          · rw [hjSeq'_lt r hr] at hv
            rw [hkSeq'_lt r hr]
            exact hk_upper ⟨r.val, hr⟩ v hv
          · rw [hjSeq'_ge r hr] at hv
            rw [hkSeq'_ge r hr]
            have := hmaxμ_le j₀ v hv
            dsimp [k₀]; omega
        · intro r₁ r₂ hlt v hv
          have hr₁ : r₁.val < l := by
            have := r₂.isLt
            have : r₁.val < r₂.val := hlt
            omega
          rw [hkSeq'_lt r₁ hr₁]
          by_cases hr₂ : r₂.val < l
          · rw [hjSeq'_lt r₂ hr₂] at hv
            exact hk_lower ⟨r₁.val, hr₁⟩ ⟨r₂.val, hr₂⟩ hlt v hv
          · rw [hjSeq'_ge r₂ hr₂] at hv
            have hle_last : (⟨r₁.val, hr₁⟩ : Fin l) ≤ r_last := by
              change r₁.val ≤ l - 1
              omega
            exact le_trans (hk_mono ⟨r₁.val, hr₁⟩ r_last hle_last) (hj₀_ge_last v hv)
        · intro r₁ r₂ hle
          by_cases hr₂ : r₂.val < l
          · have hr₁ : r₁.val < l := by
              have : r₁.val ≤ r₂.val := hle
              omega
            rw [hkSeq'_lt r₁ hr₁, hkSeq'_lt r₂ hr₂]
            exact hk_mono ⟨r₁.val, hr₁⟩ ⟨r₂.val, hr₂⟩ hle
          · rw [hkSeq'_ge r₂ hr₂]
            by_cases hr₁ : r₁.val < l
            · rw [hkSeq'_lt r₁ hr₁]
              have hle_last : (⟨r₁.val, hr₁⟩ : Fin l) ≤ r_last := by
                change r₁.val ≤ l - 1
                omega
              exact le_trans (hk_mono ⟨r₁.val, hr₁⟩ r_last hle_last) (le_of_lt hk_last_lt_k₀)
            · rw [hkSeq'_ge r₁ hr₁]
        · intro r
          by_cases hr : r.val < l
          · rw [hkSeq'_lt r hr]
            exact hJ_card ⟨r.val, hr⟩
          · rw [hkSeq'_ge r hr]
            have hr_eq : r.val = l := by omega
            rw [hr_eq]
            exact hJ_k₀_card
  let s : ℕ := θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2)
  by_contra hnot_lt
  have hge : 2 * s * m ≤ n := by
    have hge' : 2 * m * θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) ≤ n := not_lt.1 hnot_lt
    dsimp [s]
    linarith
  rcases hind s hge with ⟨kSeq, jSeq, hk_upper, hk_lower, _, _⟩
  have hjSeq_inj : Function.Injective jSeq := by
    intro r₁ r₂ heq
    rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
    · rcases (hB_conn (jSeq r₂)).nonempty with ⟨v, hv⟩
      have h1 : μ v < kSeq r₁ := hk_upper r₁ v (heq ▸ hv)
      have h2 : kSeq r₁ ≤ μ v := hk_lower r₁ r₂ hlt v hv
      omega
    · rfl
    · rcases (hB_conn (jSeq r₁)).nonempty with ⟨v, hv⟩
      have h1 : μ v < kSeq r₂ := hk_upper r₂ v (heq ▸ hv)
      have h2 : kSeq r₂ ≤ μ v := hk_lower r₂ r₁ hgt v hv
      omega
  let C (r : Fin s) : (⊤ : SimpleGraph α).Subgraph := B (jSeq r)
  have hC_le : ∀ r, C r ≤ G := fun r ↦ hB_le (jSeq r)
  have hC_conn : ∀ r, (C r).Connected := fun r ↦ hB_conn (jSeq r)
  have hC_disj : Pairwise fun r₁ r₂ ↦ Disjoint (C r₁).verts (C r₂).verts :=
    fun r₁ r₂ hne ↦ hB_disj (hjSeq_inj.ne hne)
  have hC_meet : ∀ r, θ ^ 2 / 2 ≤ {i : Fin m | ((P i).verts ∩ (C r).verts).Nonempty}.ncard :=
    fun r ↦ hB_meet (jSeq r)
  have hP_order : ∀ i, (P i).MeetsInOrder C := by
    intro i r₁ r₂ hlt u ⟨huP, huC⟩ v ⟨hvP, hvC⟩
    have hμu : μ u < kSeq r₁ := hk_upper r₁ u huC
    have hμv : kSeq r₁ ≤ μ v := hk_lower r₁ r₂ hlt v hvC
    have hμ_lt : μ u < μ v := lt_of_lt_of_le hμu hμv
    rcases (P i).precedes_or_eq_or_precedes huP hvP with hprec | rfl | hprec
    · exact hprec
    · exact (lt_irrefl (μ u) hμ_lt).elim
    · have := hμ_mono i v u hprec
      omega
  have hs_lt : s < θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) :=
    theorem_2_4_simple hθ heven hm hfin hG P C hP_le hP_unique.1.2 hC_le hC_conn hC_disj hC_meet hP_order
  exact lt_irrefl s hs_lt

end GraphMinor.GM01
end
