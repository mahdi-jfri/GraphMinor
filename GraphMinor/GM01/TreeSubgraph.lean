module

public import GraphMinor.GM01.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tree Subgraphs and the Elementary Subgraph Lemma for Graph Minors I, (2.3)

This file proves the properties of tree subgraphs (`IsTreeSubgraph`) and end-vertices (`IsLeafOf`)
needed for (2.3) of Graph Minors I:
* every finite tree with `θ ^ 2 / 2` vertices (`6 ≤ θ` even) contains either a path subgraph on `θ`
  vertices or a tree subgraph with `θ` end-vertices (`IsTreeSubgraph.exists_path_or_tree_leaves`);
* removing the end-vertices of a finite tree with at least `3` end-vertices leaves a nonempty
  connected subgraph adjacent to every end-vertex (`connected_deleteVerts_leaves`);
* the numerical inequality of (2.3) (`nat_choose_grid_bound_2_3`).
-/

public section

namespace GraphMinor.GM01

open SimpleGraph Set

variable {α : Type*}

/-! ### Path vertex cardinality and truncation -/

/-- The number of vertices of a path `P` equals `P.walk.support.length`. -/
lemma Path.ncard_verts (P : Path α) : P.verts.ncard = P.walk.support.length := by
  classical
  have hset : P.verts = (P.walk.support.toFinset : Set α) := by
    ext x
    simp [Path.mem_verts_iff]
  rw [hset, ncard_coe_finset, List.card_toFinset, P.support_nodup.dedup]

/-- The initial subpath of `P` on the first `k` vertices (for `1 ≤ k ≤ P.verts.ncard`). -/
noncomputable def Path.takeVerts (P : Path α) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ P.verts.ncard) : Path α :=
  have hlen : k - 1 < P.walk.support.length := by
    have hcard := P.ncard_verts
    omega
  P.takeUntil (P.walk.support[k - 1]'hlen) (P.mem_verts_iff.2 (List.getElem_mem hlen))

lemma Path.takeVerts_toSubgraph_le (P : Path α) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ P.verts.ncard) : (P.takeVerts hk1 hk).toSubgraph ≤ P.toSubgraph := by
  rw [Path.takeVerts]
  exact P.takeUntil_toSubgraph_le _

lemma Path.ncard_verts_takeVerts (P : Path α) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ P.verts.ncard) : (P.takeVerts hk1 hk).verts.ncard = k := by
  classical
  have hcard := P.ncard_verts
  have hlen : k - 1 < P.walk.support.length := by omega
  let u := P.walk.support[k - 1]'hlen
  have hu' : u ∈ P.walk.support := List.getElem_mem hlen
  rw [Path.takeVerts, Path.ncard_verts]
  change (P.walk.takeUntil u hu').support.length = k
  rw [Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take, List.length_take]
  have hidx : P.walk.support.idxOf u = k - 1 := P.support_nodup.idxOf_getElem (k - 1) hlen
  rw [hidx]
  omega

/-! ### Acyclicity and tree subgraphs -/

lemma IsTreeSubgraph.connected {T : (⊤ : SimpleGraph α).Subgraph} (hT : IsTreeSubgraph T) :
    T.Connected :=
  ⟨hT.1⟩

lemma IsTreeSubgraph.isAcyclic {T : (⊤ : SimpleGraph α).Subgraph} (hT : IsTreeSubgraph T) :
    T.coe.IsAcyclic :=
  hT.2

lemma isAcyclic_of_le {T H : (⊤ : SimpleGraph α).Subgraph} (hT : T.coe.IsAcyclic) (hle : H ≤ T) :
    H.coe.IsAcyclic :=
  hT.comap (Subgraph.inclusion hle)
    (fun _ _ h ↦ Subtype.ext (congrArg (Subtype.val : T.verts → α) h))

lemma isTreeSubgraph_of_le_of_connected {T H : (⊤ : SimpleGraph α).Subgraph}
    (hT : IsTreeSubgraph T) (hle : H ≤ T) (hconn : H.Connected) : IsTreeSubgraph H :=
  ⟨hconn.coe, isAcyclic_of_le hT.isAcyclic hle⟩

/-- Lift a walk whose `toSubgraph` is contained in `T` to a walk in `T.coe`. -/
def toSubgraphWalk {T : (⊤ : SimpleGraph α).Subgraph} :
    ∀ {u v : α} (p : (⊤ : SimpleGraph α).Walk u v) (hp : p.toSubgraph ≤ T),
      T.coe.Walk ⟨u, Subgraph.verts_mono hp p.start_mem_verts_toSubgraph⟩
        ⟨v, Subgraph.verts_mono hp p.end_mem_verts_toSubgraph⟩
  | _, _, .nil, _ => .nil
  | _, _, .cons _ p, hp =>
    have h₁ : T.Adj _ _ := hp.2 (by simp)
    .cons h₁ (toSubgraphWalk p ((le_sup_right : p.toSubgraph ≤ _).trans hp))

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma map_toSubgraphWalk {T : (⊤ : SimpleGraph α).Subgraph} {u v : α}
    (p : (⊤ : SimpleGraph α).Walk u v) (hp : p.toSubgraph ≤ T) :
    (toSubgraphWalk p hp).map T.hom = p := by
  induction p <;> simp [toSubgraphWalk, *]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma length_toSubgraphWalk {T : (⊤ : SimpleGraph α).Subgraph} {u v : α}
    (p : (⊤ : SimpleGraph α).Walk u v) (hp : p.toSubgraph ≤ T) :
    (toSubgraphWalk p hp).length = p.length := by
  induction p <;> simp [toSubgraphWalk, *]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma getVert_toSubgraphWalk {T : (⊤ : SimpleGraph α).Subgraph} {u v : α}
    (p : (⊤ : SimpleGraph α).Walk u v) (hp : p.toSubgraph ≤ T) (i : ℕ) :
    ((toSubgraphWalk p hp).getVert i : α) = p.getVert i := by
  induction p generalizing i with
  | nil => rfl
  | cons _ p ih =>
    cases i <;> simp [toSubgraphWalk, *]

lemma isPath_toSubgraphWalk {T : (⊤ : SimpleGraph α).Subgraph} {u v : α}
    {p : (⊤ : SimpleGraph α).Walk u v} (hp_path : p.IsPath) (hp : p.toSubgraph ≤ T) :
    (toSubgraphWalk p hp).IsPath := by
  rw [Walk.isPath_def]
  have hnodup : ((toSubgraphWalk p hp).map T.hom).support.Nodup := by
    rw [map_toSubgraphWalk]
    exact hp_path.support_nodup
  rw [Walk.support_map] at hnodup
  exact hnodup.of_map _

lemma mem_support_toSubgraphWalk {T : (⊤ : SimpleGraph α).Subgraph} {u v w : α}
    (p : (⊤ : SimpleGraph α).Walk u v) (hp : p.toSubgraph ≤ T) (hw : w ∈ p.support)
    (hwT : w ∈ T.verts) :
    (⟨w, hwT⟩ : T.verts) ∈ (toSubgraphWalk p hp).support := by
  have hw_map : w ∈ ((toSubgraphWalk p hp).map T.hom).support := by
     rwa [map_toSubgraphWalk]
  rw [Walk.support_map] at hw_map
  rcases List.mem_map.1 hw_map with ⟨x, hx, heq⟩
  have hx_eq : x = ⟨w, hwT⟩ := Subtype.ext heq
  exact hx_eq ▸ hx

lemma penultimate_toSubgraphWalk {T : (⊤ : SimpleGraph α).Subgraph} {u v : α}
    (p : (⊤ : SimpleGraph α).Walk u v) (hp : p.toSubgraph ≤ T) :
    ((toSubgraphWalk p hp).penultimate : α) = p.penultimate := by
  simp [Walk.penultimate]

/-! ### End-vertices (`IsLeafOf`) and internal vertices of paths -/

lemma IsLeafOf.mem {T : (⊤ : SimpleGraph α).Subgraph} {v : α} (h : IsLeafOf T v) : v ∈ T.verts :=
  h.1

lemma IsLeafOf.existsUnique_adj {T : (⊤ : SimpleGraph α).Subgraph} {v : α} (h : IsLeafOf T v) :
    ∃! u, T.Adj v u := by
  obtain ⟨u, hu⟩ := Set.ncard_eq_one.1 h.2
  refine ⟨u, ?_, fun w hw ↦ ?_⟩
  · have : u ∈ T.neighborSet v := hu ▸ Set.mem_singleton u
    exact this
  · have : w ∈ T.neighborSet v := hw
    rwa [hu, Set.mem_singleton_iff] at this

lemma isLeafOf_iff_existsUnique_adj {T : (⊤ : SimpleGraph α).Subgraph} {v : α} :
    IsLeafOf T v ↔ v ∈ T.verts ∧ ∃! u, T.Adj v u := by
  refine ⟨fun h ↦ ⟨h.1, h.existsUnique_adj⟩, fun ⟨hv, u, hu, hunique⟩ ↦ ⟨hv, ?_⟩⟩
  have hset : T.neighborSet v = {u} := by
    ext w
    simp only [Subgraph.mem_neighborSet, mem_singleton_iff]
    exact ⟨hunique w, fun h ↦ h ▸ hu⟩
  rw [hset, ncard_singleton]

/-- No internal vertex of a path in `T` is an end-vertex of `T`. -/
lemma not_isLeafOf_of_internal_mem_path {T : (⊤ : SimpleGraph α).Subgraph}
    (hT_fin : T.verts.Finite) {P : Path α} (hP : P.toSubgraph ≤ T) {w : α}
    (hw : w ∈ P.verts) (hfirst : w ≠ P.first) (hlast : w ≠ P.last) :
    ¬ IsLeafOf T w := by
  rw [P.mem_verts_iff, Walk.mem_support_iff_exists_getVert] at hw
  obtain ⟨i, rfl, hi⟩ := hw
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hfirst P.walk.getVert_zero
  have hilt : i < P.walk.length := by
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact (hlast P.walk.getVert_length).elim
    · exact hlt
  have hncard_P : (P.toSubgraph.neighborSet (P.walk.getVert i)).ncard = 2 :=
    P.isPath.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
  have hsub : P.toSubgraph.neighborSet (P.walk.getVert i) ⊆ T.neighborSet (P.walk.getVert i) :=
    fun _ hx ↦ hP.2 hx
  have hfin : (T.neighborSet (P.walk.getVert i)).Finite :=
    hT_fin.subset (T.neighborSet_subset_verts _)
  have hle : 2 ≤ (T.neighborSet (P.walk.getVert i)).ncard := by
    rw [← hncard_P]
    exact ncard_le_ncard hsub hfin
  intro hleaf
  have := hleaf.2
  omega

/-- Deleting any set of end-vertices from a preconnected finite subgraph leaves it preconnected. -/
lemma preconnected_deleteVerts_of_subset_leaves {T : (⊤ : SimpleGraph α).Subgraph}
    (hT_fin : T.verts.Finite) (hT_conn : T.Preconnected) {S : Set α}
    (hS : S ⊆ {v | IsLeafOf T v}) : (T.deleteVerts S).Preconnected := by
  rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
  intro u v hu hv
  rw [Subgraph.deleteVerts_verts] at hu hv
  obtain ⟨P, hP, rfl, rfl⟩ := exists_path_of_preconnected hT_conn hu.1 hv.1
  have hverts_sub : P.verts ⊆ T.verts \ S := by
    intro w hw
    refine ⟨hP.1 hw, fun hwS ↦ ?_⟩
    by_cases hfirst : w = P.first
    · exact hu.2 (hfirst ▸ hwS)
    · by_cases hlast : w = P.last
      · exact hv.2 (hlast ▸ hwS)
      · exact not_isLeafOf_of_internal_mem_path hT_fin hP hw hfirst hlast (hS hwS)
  refine ⟨P.walk, hverts_sub, fun x y hxy ↦ ?_⟩
  rw [Subgraph.deleteVerts_adj]
  exact ⟨(hverts_sub hxy.fst_mem).1, (hverts_sub hxy.fst_mem).2,
    (hverts_sub hxy.snd_mem).1, (hverts_sub hxy.snd_mem).2, hP.2 hxy⟩

/-- Deleting the end-vertices of a connected finite subgraph with at least `3` end-vertices leaves a
connected subgraph in which every end-vertex has a neighbor. -/
lemma connected_deleteVerts_leaves {Q : (⊤ : SimpleGraph α).Subgraph}
    (hQ_fin : Q.verts.Finite) (hQ_conn : Q.Connected)
    (hL : 3 ≤ {v | IsLeafOf Q v}.ncard) :
    (Q.deleteVerts {v | IsLeafOf Q v}).Connected ∧
      ∀ x ∈ {v | IsLeafOf Q v}, ∃ y ∈ (Q.deleteVerts {v | IsLeafOf Q v}).verts, Q.Adj x y := by
  let L := {v | IsLeafOf Q v}
  have hadj_internal : ∀ x ∈ L, ∃ y ∈ (Q.deleteVerts L).verts, Q.Adj x y := by
    intro x hx
    obtain ⟨y, hxy, hy_unique⟩ := hx.existsUnique_adj
    refine ⟨y, ?_, hxy⟩
    rw [Subgraph.deleteVerts_verts]
    refine ⟨hxy.snd_mem, fun hyL ↦ ?_⟩
    have hsub : Q.verts ⊆ ({x, y} : Set α) := by
      intro w hw
      by_cases hwx : w = x
      · exact Or.inl hwx
      · by_cases hwy : w = y
        · exact Or.inr hwy
        · exfalso
          obtain ⟨P, hP, hfirst, hlast⟩ := exists_path_of_preconnected hQ_conn.preconnected hx.1 hw
          have hnil : ¬ P.walk.Nil := Walk.not_nil_of_ne (by rw [hfirst, hlast]; exact Ne.symm hwx)
          have hadj_snd : Q.Adj x P.walk.snd := by
            rw [← hfirst]
            exact hP.2 (P.walk.toSubgraph_adj_snd hnil)
          have hsnd_y : P.walk.snd = y := hy_unique _ hadj_snd
          have hy_mem : y ∈ P.verts := by
            rw [← hsnd_y, P.mem_verts_iff]
            exact P.walk.getVert_mem_support 1
          have hy_ne_first : y ≠ P.first := by
            rw [hfirst]
            exact hxy.ne.symm
          have hy_ne_last : y ≠ P.last := by
            rw [hlast]
            exact Ne.symm hwy
          exact not_isLeafOf_of_internal_mem_path hQ_fin hP hy_mem hy_ne_first hy_ne_last hyL
    have hcard_le : {v | IsLeafOf Q v}.ncard ≤ 2 := by
      have hL_sub : {v | IsLeafOf Q v} ⊆ ({x, y} : Set α) := fun w hw ↦ hsub hw.1
      have hxy_le : ({x, y} : Set α).ncard ≤ 2 := by
        simpa using ncard_insert_le x {y}
      exact (ncard_le_ncard hL_sub (Set.toFinite _)).trans hxy_le
    omega
  have hL_fin : {v | IsLeafOf Q v}.Finite := hQ_fin.subset fun v hv ↦ hv.1
  have hnonempty : {v | IsLeafOf Q v}.Nonempty := (ncard_pos hL_fin).1 (by omega)
  obtain ⟨x₀, hx₀⟩ := hnonempty
  obtain ⟨y₀, hy₀, -⟩ := hadj_internal x₀ hx₀
  refine ⟨Subgraph.connected_iff.2 ⟨preconnected_deleteVerts_of_subset_leaves hQ_fin
    hQ_conn.preconnected Subset.rfl, ⟨y₀, hy₀⟩⟩, hadj_internal⟩

/-! ### Deleting a single end-vertex when there are more than `θ` end-vertices -/

private lemma exists_tree_with_leaves_of_ge {T : (⊤ : SimpleGraph α).Subgraph}
    (hT_fin : T.verts.Finite) (hT : IsTreeSubgraph T) {θ : ℕ} (hθ : 3 ≤ θ)
    (hL : θ ≤ {v | IsLeafOf T v}.ncard) :
    ∃ Q ≤ T, IsTreeSubgraph Q ∧ {v | IsLeafOf Q v}.ncard = θ := by
  classical
  revert hT_fin hT hL
  refine Nat.strong_induction_on (p := fun n ↦ ∀ T : (⊤ : SimpleGraph α).Subgraph,
      T.verts.ncard = n → T.verts.Finite → IsTreeSubgraph T → θ ≤ {v | IsLeafOf T v}.ncard →
      ∃ Q ≤ T, IsTreeSubgraph Q ∧ {v | IsLeafOf Q v}.ncard = θ)
    T.verts.ncard (fun n ih T hn hT_fin hT hL ↦ ?_) T rfl
  rcases eq_or_lt_of_le hL with heq | hlt
  · exact ⟨T, le_rfl, hT, heq.symm⟩
  · have hL_fin : {v | IsLeafOf T v}.Finite := hT_fin.subset (fun v hv ↦ hv.1)
    obtain ⟨v₀, hv₀⟩ : {v | IsLeafOf T v}.Nonempty := (ncard_pos hL_fin).1 (by omega)
    obtain ⟨_, hadj_internal⟩ := connected_deleteVerts_leaves hT_fin hT.connected (by omega)
    let T' := T.deleteVerts ({v₀} : Set α)
    have hT'_le : T' ≤ T := Subgraph.deleteVerts_le
    have hT'_fin : T'.verts.Finite := hT_fin.subset hT'_le.1
    obtain ⟨u₀, hu₀_mem, hv₀u₀⟩ := hadj_internal v₀ hv₀
    have hu₀_T' : u₀ ∈ T'.verts := by
      rw [Subgraph.deleteVerts_verts]
      exact ⟨hu₀_mem.1, by simp [hv₀u₀.ne.symm]⟩
    have hT'_conn : T'.Connected :=
      Subgraph.connected_iff.2 ⟨preconnected_deleteVerts_of_subset_leaves hT_fin
        hT.connected.preconnected (singleton_subset_iff.2 hv₀), ⟨u₀, hu₀_T'⟩⟩
    have hT'_tree : IsTreeSubgraph T' := isTreeSubgraph_of_le_of_connected hT hT'_le hT'_conn
    have hL_sub : {v | IsLeafOf T v} \ {v₀} ⊆ {v | IsLeafOf T' v} := by
      intro w ⟨hwL, hwne⟩
      rw [mem_singleton_iff] at hwne
      obtain ⟨z, hz_mem, hwz⟩ := hadj_internal w hwL
      obtain ⟨z', hwz', hz'_unique⟩ := hwL.existsUnique_adj
      have hzz' : z = z' := hz'_unique z hwz
      have hzv₀ : z ≠ v₀ := fun h ↦ hz_mem.2 (h ▸ hv₀)
      have hwT' : w ∈ T'.verts := ⟨hwL.1, hwne⟩
      rw [mem_ofPred_eq, isLeafOf_iff_existsUnique_adj]
      refine ⟨hwT', z, ?_, fun y hy ↦ ?_⟩
      · change (T.deleteVerts ({v₀} : Set α)).Adj w z
        rw [Subgraph.deleteVerts_adj]
        exact ⟨hwL.1, hwne, hz_mem.1, hzv₀, hwz⟩
      · exact (hz'_unique y (hT'_le.2 hy)).trans hzz'.symm
    have hL'_fin : {v | IsLeafOf T' v}.Finite := hT'_fin.subset (fun v hv ↦ hv.1)
    have hL'_card : θ ≤ {v | IsLeafOf T' v}.ncard := by
      have h1 := ncard_le_ncard hL_sub hL'_fin
      rw [ncard_sdiff_singleton_of_mem hv₀] at h1
      omega
    have hn' : T'.verts.ncard < n := by
      rw [← hn, Subgraph.deleteVerts_verts, ncard_sdiff_singleton_of_mem hv₀.1]
      have : 1 ≤ T.verts.ncard := (ncard_pos hT_fin).2 ⟨v₀, hv₀.1⟩
      omega
    obtain ⟨Q, hQ_le, hQ_tree, hQ_card⟩ := ih T'.verts.ncard hn' T' rfl hT'_fin hT'_tree hL'_card
    exact ⟨Q, hQ_le.trans hT'_le, hQ_tree, hQ_card⟩

/-! ### Endpoints of a maximum-length path in a tree are end-vertices -/

private lemma isLeafOf_last_of_maximal_path {T : (⊤ : SimpleGraph α).Subgraph}
    (hT : IsTreeSubgraph T) {P : Path α} (hP : P.toSubgraph ≤ T) (hne : P.first ≠ P.last)
    (hmax : ∀ Q : Path α, Q.toSubgraph ≤ T → Q.verts.ncard ≤ P.verts.ncard) :
    IsLeafOf T P.last := by
  have hnil : ¬ P.walk.Nil := Walk.not_nil_of_ne hne
  have hadj_pen : T.Adj P.last P.walk.penultimate :=
    (hP.2 (P.walk.toSubgraph_adj_penultimate hnil)).symm
  have hset : T.neighborSet P.last = {P.walk.penultimate} := by
    ext w
    simp only [Subgraph.mem_neighborSet, mem_singleton_iff]
    refine ⟨fun hadj ↦ ?_, fun h ↦ h ▸ hadj_pen⟩
    by_cases hw : w ∈ P.verts
    · have hwT : w ∈ T.verts := hadj.snd_mem
      let q := toSubgraphWalk P.walk hP
      have hq_path : q.IsPath := isPath_toSubgraphWalk P.isPath hP
      have hw_supp : (⟨w, hwT⟩ : T.verts) ∈ q.support :=
        mem_support_toSubgraphWalk P.walk hP (P.mem_verts_iff.1 hw) hwT
      have hadj_coe : T.coe.Adj ⟨P.last, hP.1 P.walk.end_mem_verts_toSubgraph⟩ ⟨w, hwT⟩ := hadj
      have hpen := hT.isAcyclic.eq_penultimate_of_adj_end hq_path hadj_coe hw_supp
      exact (congrArg Subtype.val hpen).trans (penultimate_toSubgraphWalk P.walk hP)
    · exfalso
      have hw_supp : w ∉ P.walk.support := by rwa [← P.mem_verts_iff]
      let Q : Path α :=
        { first := P.first
          last := w
          walk := P.walk.concat (T.adj_sub hadj)
          isPath := P.isPath.concat hw_supp (T.adj_sub hadj) }
      have hQ_le : Q.toSubgraph ≤ T := by
        dsimp [Q, Path.toSubgraph]
        rw [Walk.concat_eq_append, Walk.toSubgraph_append]
        refine sup_le hP ?_
        simp only [Walk.toSubgraph, singletonSubgraph_le_iff, hadj.snd_mem, sup_le_iff, and_true]
        exact subgraphOfAdj_le_of_adj T hadj
      have hQ_card : Q.verts.ncard = P.verts.ncard + 1 := by
        rw [Q.ncard_verts, P.ncard_verts]
        simp [Q]
      have := hmax Q hQ_le
      omega
  refine ⟨hP.1 P.last_mem_verts, ?_⟩
  rw [hset, ncard_singleton]

private lemma isLeafOf_first_of_maximal_path {T : (⊤ : SimpleGraph α).Subgraph}
    (hT : IsTreeSubgraph T) {P : Path α} (hP : P.toSubgraph ≤ T) (hne : P.first ≠ P.last)
    (hmax : ∀ Q : Path α, Q.toSubgraph ≤ T → Q.verts.ncard ≤ P.verts.ncard) :
    IsLeafOf T P.first := by
  have hrev_le : P.reverse.toSubgraph ≤ T := by simpa using hP
  have hrev_ne : P.reverse.first ≠ P.reverse.last := hne.symm
  have hrev_max : ∀ Q : Path α, Q.toSubgraph ≤ T → Q.verts.ncard ≤ P.reverse.verts.ncard := by
    intro Q hQ
    rw [P.reverse_verts]
    exact hmax Q hQ
  exact isLeafOf_last_of_maximal_path hT hrev_le hrev_ne hrev_max

private lemma exists_maximal_path_in_subgraph {H : (⊤ : SimpleGraph α).Subgraph}
    (hH_fin : H.verts.Finite) (P₀ : Path α) (hP₀ : P₀.toSubgraph ≤ H) :
    ∃ P : Path α, P.toSubgraph ≤ H ∧ P₀.verts.ncard ≤ P.verts.ncard ∧
      ∀ Q : Path α, Q.toSubgraph ≤ H → Q.verts.ncard ≤ P.verts.ncard := by
  have hmain : ∀ d : ℕ, ∀ P₁ : Path α, P₁.toSubgraph ≤ H →
      H.verts.ncard - P₁.verts.ncard = d →
      ∃ P : Path α, P.toSubgraph ≤ H ∧ P₁.verts.ncard ≤ P.verts.ncard ∧
        ∀ Q : Path α, Q.toSubgraph ≤ H → Q.verts.ncard ≤ P.verts.ncard := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro P₁ hP₁ hd
      by_cases hmax : ∀ Q : Path α, Q.toSubgraph ≤ H → Q.verts.ncard ≤ P₁.verts.ncard
      · exact ⟨P₁, hP₁, le_rfl, hmax⟩
      · push Not at hmax
        obtain ⟨Q₁, hQ₁, hlt⟩ := hmax
        have hQ₁_le_H : Q₁.verts.ncard ≤ H.verts.ncard := ncard_le_ncard hQ₁.1 hH_fin
        have hd' : H.verts.ncard - Q₁.verts.ncard < d := by omega
        obtain ⟨P, hP, hQ₁P, hP_max⟩ := ih _ hd' Q₁ hQ₁ rfl
        exact ⟨P, hP, hlt.le.trans hQ₁P, hP_max⟩
  exact hmain (H.verts.ncard - P₀.verts.ncard) P₀ hP₀ rfl

/-- If `T' = T.deleteVerts {v | IsLeafOf T v}` contains a path on `k ≥ 1` vertices and
`2 ≤ T.verts.ncard`, then `T` contains a path on at least `k + 2` vertices. -/
private lemma exists_longer_path_of_path_in_deleteVerts_leaves
    {T : (⊤ : SimpleGraph α).Subgraph} (hT_fin : T.verts.Finite) (hT : IsTreeSubgraph T)
    (hcard2 : 2 ≤ T.verts.ncard) {k : ℕ}
    {P₀ : Path α} (hP₀ : P₀.toSubgraph ≤ T.deleteVerts {v | IsLeafOf T v})
    (hP₀_card : k ≤ P₀.verts.ncard) :
    ∃ P : Path α, P.toSubgraph ≤ T ∧ k + 2 ≤ P.verts.ncard := by
  classical
  let L := {v | IsLeafOf T v}
  let T' := T.deleteVerts L
  have hT'_le : T' ≤ T := Subgraph.deleteVerts_le
  have hT'_fin : T'.verts.Finite := hT_fin.subset hT'_le.1
  have hT'_conn : T'.Connected :=
    Subgraph.connected_iff.2 ⟨preconnected_deleteVerts_of_subset_leaves hT_fin
      hT.connected.preconnected Subset.rfl, ⟨P₀.first, hP₀.1 P₀.first_mem_verts⟩⟩
  have hT'_tree : IsTreeSubgraph T' := isTreeSubgraph_of_le_of_connected hT hT'_le hT'_conn
  obtain ⟨P, hP, hP₀P, hP_max⟩ := exists_maximal_path_in_subgraph hT'_fin P₀ hP₀
  have hPL : k ≤ P.verts.ncard := hP₀_card.trans hP₀P
  by_cases hne : P.first = P.last
  · -- `P` is a single vertex `x = P.first`.
    let x := P.first
    have hxT' : x ∈ T'.verts := hP.1 P.first_mem_verts
    rw [Subgraph.deleteVerts_verts] at hxT'
    have hxT : x ∈ T.verts := hxT'.1
    have hx_not_leaf : ¬ IsLeafOf T x := hxT'.2
    have hP_card1 : P.verts.ncard = 1 := by
      have hnil : P.walk.Nil := P.isPath.nil_iff_eq.2 hne
      rw [P.ncard_verts, Walk.nil_iff_support_eq.1 hnil, List.length_singleton]
    obtain ⟨a, b, ha, hb, hab⟩ := (one_lt_ncard_iff hT_fin).1 (by omega)
    have hnt : T.verts.Nontrivial := ⟨a, ha, b, hb, hab⟩
    have : Nontrivial T.verts := Set.nontrivial_coe_sort.2 hnt
    obtain ⟨u₀, hu₀⟩ := hT.connected.preconnected.exists_adj_of_nontrivial ⟨x, hxT⟩
    have hpos : 0 < (T.neighborSet x).ncard :=
      (ncard_pos (hT_fin.subset (T.neighborSet_subset_verts x))).2 ⟨u₀, hu₀⟩
    have hne1 : (T.neighborSet x).ncard ≠ 1 := fun h1 ↦ hx_not_leaf ⟨hxT, h1⟩
    have hgt1 : 1 < (T.neighborSet x).ncard := by omega
    obtain ⟨u, w, hu, hw, huw⟩ :=
      (one_lt_ncard_iff (hT_fin.subset (T.neighborSet_subset_verts x))).1 hgt1
    have hux : T.Adj u x := hu.symm
    have hxw : T.Adj x w := hw
    let w_walk : (⊤ : SimpleGraph α).Walk u w :=
      Walk.cons (T.adj_sub hux) (Walk.cons (T.adj_sub hxw) Walk.nil)
    have hw_path : w_walk.IsPath := by
      simp [w_walk, huw, hux.ne, hxw.ne]
    let Q : Path α := ⟨u, w, w_walk, hw_path⟩
    refine ⟨Q, ?_, ?_⟩
    · dsimp [Q, w_walk, Path.toSubgraph]
      simp only [singletonSubgraph_le_iff, hxw.snd_mem, sup_le_iff, and_true]
      exact ⟨subgraphOfAdj_le_of_adj T hux, subgraphOfAdj_le_of_adj T hxw⟩
    · have hQ_card : Q.verts.ncard = 3 := by
        rw [Q.ncard_verts]
        simp [Q, w_walk]
      omega
  · -- `P.first ≠ P.last`, so both `P.first` and `P.last` are end-vertices of `T'`.
    have hleaf_first : IsLeafOf T' P.first := isLeafOf_first_of_maximal_path hT'_tree hP hne hP_max
    have hleaf_last : IsLeafOf T' P.last := isLeafOf_last_of_maximal_path hT'_tree hP hne hP_max
    have hfirst_T' : P.first ∈ T'.verts := hP.1 P.first_mem_verts
    have hlast_T' : P.last ∈ T'.verts := hP.1 P.last_mem_verts
    rw [Subgraph.deleteVerts_verts] at hfirst_T' hlast_T'
    have hexists_leaf_adj : ∀ z : α, z ∈ T.verts → z ∉ L → IsLeafOf T' z →
        ∃ u ∈ L, T.Adj z u := by
      intro z hzT hzL hz_leaf'
      by_contra! hno
      have hsub : T.neighborSet z ⊆ T'.neighborSet z := by
        intro u hu
        rw [Subgraph.mem_neighborSet, Subgraph.deleteVerts_adj]
        exact ⟨hzT, hzL, hu.snd_mem, fun huL ↦ hno u huL hu, hu⟩
      have heq : T'.neighborSet z = T.neighborSet z :=
        Subset.antisymm (fun _ hx ↦ hT'_le.2 hx) hsub
      exact hzL ⟨hzT, heq ▸ hz_leaf'.2⟩
    obtain ⟨u, huL, hfirst_u⟩ := hexists_leaf_adj P.first hfirst_T'.1 hfirst_T'.2 hleaf_first
    obtain ⟨w, hwL, hlast_w⟩ := hexists_leaf_adj P.last hlast_T'.1 hlast_T'.2 hleaf_last
    have hu_notMem : u ∉ P.verts := fun huP ↦ (hP.1 huP).2 huL
    have hw_notMem : w ∉ P.verts := fun hwP ↦ (hP.1 hwP).2 hwL
    have huw : u ≠ w := by
      rintro rfl
      obtain ⟨z, huz, hz_unique⟩ := huL.existsUnique_adj
      have h1 : P.first = z := hz_unique P.first hfirst_u.symm
      have h2 : P.last = z := hz_unique P.last hlast_w.symm
      exact hne (h1.trans h2.symm)
    have hw_supp : w ∉ P.walk.support := by rwa [← P.mem_verts_iff]
    let p₁ := P.walk.concat (T.adj_sub hlast_w)
    have hp₁_path : p₁.IsPath := P.isPath.concat hw_supp (T.adj_sub hlast_w)
    have hu_supp₁ : u ∉ p₁.support := by
      rw [Walk.support_concat, List.mem_append, List.mem_singleton]
      rintro (huP | rfl)
      · exact hu_notMem (P.mem_verts_iff.2 huP)
      · exact huw rfl
    let p₂ := Walk.cons (T.adj_sub hfirst_u.symm) p₁
    have hp₂_path : p₂.IsPath := hp₁_path.cons hu_supp₁
    let Q : Path α := ⟨u, w, p₂, hp₂_path⟩
    refine ⟨Q, ?_, ?_⟩
    · change (Walk.cons (T.adj_sub hfirst_u.symm) (P.walk.concat (T.adj_sub hlast_w))).toSubgraph ≤ T
      rw [Walk.toSubgraph, Walk.concat_eq_append, Walk.toSubgraph_append]
      refine sup_le (subgraphOfAdj_le_of_adj T hfirst_u.symm) (sup_le (hP.trans hT'_le) ?_)
      simp only [Walk.toSubgraph, singletonSubgraph_le_iff, hlast_w.snd_mem, sup_le_iff, and_true]
      exact subgraphOfAdj_le_of_adj T hlast_w
    · have hQ_card : Q.verts.ncard = P.verts.ncard + 2 := by
        rw [Q.ncard_verts, P.ncard_verts]
        simp [Q, p₂, p₁]
      omega

/-! ### Bounding the vertex count when all paths and leaf counts are small -/

private lemma ncard_verts_le_of_forall_path_lt_of_forall_leaves_lt
    {θ : ℕ} (hθ : 3 ≤ θ) :
    ∀ (m : ℕ) {T : (⊤ : SimpleGraph α).Subgraph},
      T.verts.Finite → IsTreeSubgraph T →
      (∀ Q ≤ T, IsTreeSubgraph Q → {v | IsLeafOf Q v}.ncard < θ) →
      (∀ P : Path α, P.toSubgraph ≤ T → P.verts.ncard < 2 * m) →
      T.verts.ncard ≤ m * (θ - 1)
  | 0, T, _, hT, _, hpath => by
    obtain ⟨v, hv⟩ := hT.connected.nonempty
    have h1 := hpath (Path.singleton v) (by simp [Path.singleton, Path.toSubgraph, hv])
    rw [(Path.singleton v).ncard_verts] at h1
    simp [Path.singleton] at h1
  | m + 1, T, hT_fin, hT, hleaves, hpath => by
    rcases le_or_gt T.verts.ncard 1 with hle1 | hgt1
    · have : 1 ≤ (m + 1) * (θ - 1) := Nat.mul_pos (by omega) (by omega)
      omega
    · rcases Nat.eq_zero_or_pos m with rfl | hm_pos
      · obtain ⟨u, v, hu, hv, huv⟩ := (one_lt_ncard_iff hT_fin).1 hgt1
        obtain ⟨P, hP, rfl, rfl⟩ := exists_path_of_preconnected hT.connected.preconnected hu hv
        have hlt2 := hpath P hP
        have hge2 : 2 ≤ P.verts.ncard := by
          have hsub : ({P.first, P.last} : Set α) ⊆ P.verts := by
            intro w hw
            rcases hw with rfl | rfl
            · exact P.first_mem_verts
            · exact P.last_mem_verts
          have hpair : ({P.first, P.last} : Set α).ncard = 2 := ncard_pair huv
          rw [← hpair]
          exact ncard_le_ncard hsub (hT_fin.subset hP.1)
        omega
      · let L := {v | IsLeafOf T v}
        let T' := T.deleteVerts L
        have hL_sub : L ⊆ T.verts := fun v hv ↦ hv.1
        have hL_fin : L.Finite := hT_fin.subset hL_sub
        have hL_card : L.ncard ≤ θ - 1 := by
          have hlt : L.ncard < θ := hleaves T le_rfl hT
          omega
        have hT'_le : T' ≤ T := Subgraph.deleteVerts_le
        have hT'_fin : T'.verts.Finite := hT_fin.subset hT'_le.1
        have hsplit : T.verts.ncard = T'.verts.ncard + L.ncard := by
          change T.verts.ncard = (T.verts \ L).ncard + L.ncard
          have := ncard_sdiff_add_ncard_of_subset hL_sub hT_fin
          omega
        rcases T'.verts.eq_empty_or_nonempty with hempty | hne'
        · have h0 : T'.verts.ncard = 0 := by simp [hempty]
          have : θ - 1 ≤ (m + 1) * (θ - 1) := Nat.le_mul_of_pos_left _ (by omega)
          omega
        · have hT'_conn : T'.Connected :=
            Subgraph.connected_iff.2 ⟨preconnected_deleteVerts_of_subset_leaves hT_fin
              hT.connected.preconnected Subset.rfl, hne'⟩
          have hT'_tree : IsTreeSubgraph T' := isTreeSubgraph_of_le_of_connected hT hT'_le hT'_conn
          have hleaves' : ∀ Q ≤ T', IsTreeSubgraph Q → {v | IsLeafOf Q v}.ncard < θ :=
            fun Q hQ hQ_tree ↦ hleaves Q (hQ.trans hT'_le) hQ_tree
          have hpath' : ∀ P₀ : Path α, P₀.toSubgraph ≤ T' → P₀.verts.ncard < 2 * m := by
            intro P₀ hP₀
            by_contra! hge
            obtain ⟨P, hP, hP_card⟩ :=
              exists_longer_path_of_path_in_deleteVerts_leaves hT_fin hT hgt1 hP₀ hge
            have := hpath P hP
            omega
          have hih := ncard_verts_le_of_forall_path_lt_of_forall_leaves_lt hθ m
            hT'_fin hT'_tree hleaves' hpath'
          calc
            T.verts.ncard = T'.verts.ncard + L.ncard := hsplit
            _ ≤ m * (θ - 1) + (θ - 1) := Nat.add_le_add hih hL_card
            _ = (m + 1) * (θ - 1) := by ring

/-- Elementary subgraph lemma of Graph Minors I, (2.3) (page 43):
"It is elementary that for $1 \le j \le n$, $B_j$ has a subgraph $Q_j$ which is either a path with
$\theta$ vertices or a tree with $\theta$ end-vertices." -/
theorem IsTreeSubgraph.exists_path_or_tree_leaves {T : (⊤ : SimpleGraph α).Subgraph}
    (hT_fin : T.verts.Finite) (hT : IsTreeSubgraph T) {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    (hcard : T.verts.ncard = θ ^ 2 / 2) :
    ∃ Q ≤ T, (IsPathSubgraph Q ∧ Q.verts.ncard = θ) ∨
      (IsTreeSubgraph Q ∧ {v | IsLeafOf Q v}.ncard = θ) := by
  classical
  by_cases hpath : ∃ P : Path α, P.toSubgraph ≤ T ∧ θ ≤ P.verts.ncard
  · obtain ⟨P, hP_le, hP_card⟩ := hpath
    let P' := P.takeVerts (by omega : 1 ≤ θ) hP_card
    refine ⟨P'.toSubgraph, (P.takeVerts_toSubgraph_le _ _).trans hP_le,
      Or.inl ⟨⟨P', rfl⟩, P.ncard_verts_takeVerts _ _⟩⟩
  · by_cases htree : ∃ Q₀ ≤ T, IsTreeSubgraph Q₀ ∧ θ ≤ {v | IsLeafOf Q₀ v}.ncard
    · obtain ⟨Q₀, hQ₀_le, hQ₀_tree, hQ₀_leaves⟩ := htree
      obtain ⟨Q, hQ_le, hQ_tree, hQ_card⟩ :=
        exists_tree_with_leaves_of_ge (hT_fin.subset hQ₀_le.1) hQ₀_tree (by omega) hQ₀_leaves
      exact ⟨Q, hQ_le.trans hQ₀_le, Or.inr ⟨hQ_tree, hQ_card⟩⟩
    · exfalso
      push Not at hpath htree
      rcases heven with ⟨m, rfl⟩
      have hθ_eq : m + m = 2 * m := by ring
      rw [hθ_eq] at hθ hcard hpath htree
      have hle := ncard_verts_le_of_forall_path_lt_of_forall_leaves_lt (by omega : 3 ≤ 2 * m) m
        hT_fin hT htree hpath
      have hcard_eq : (2 * m) ^ 2 / 2 = 2 * m * m := by
        have : (2 * m) ^ 2 = 2 * (2 * m * m) := by ring
        rw [this, Nat.mul_div_right _ (by omega)]
      rw [hcard_eq] at hcard
      have : m * (2 * m - 1) < 2 * m * m := by
        calc
          m * (2 * m - 1) < m * (2 * m) := by
            refine Nat.mul_lt_mul_of_pos_left ?_ (by omega)
            omega
          _ = 2 * m * m := by ring
      omega

/-! ### Arithmetic inequality of (2.3) (page 44) -/

private lemma pow_three_le_two_pow {θ : ℕ} (hθ : 10 ≤ θ) : θ ^ 3 ≤ 2 ^ θ := by
  induction θ, hθ using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hstep : (k + 1) ^ 3 ≤ 2 * k ^ 3 := by
      calc
        (k + 1) ^ 3 = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := by ring
        _ ≤ k ^ 3 + 3 * k ^ 2 + 3 * k ^ 2 + k ^ 2 := by
          have hk2 : 1 ≤ k ^ 2 := by nlinarith
          have hk1 : 3 * k ≤ 3 * k ^ 2 := by nlinarith
          omega
        _ = k ^ 3 + 7 * k ^ 2 := by ring
        _ ≤ k ^ 3 + k * k ^ 2 := by
          have : 7 * k ^ 2 ≤ k * k ^ 2 := Nat.mul_le_mul_right _ (by omega)
          omega
        _ = 2 * k ^ 3 := by ring
    calc
      (k + 1) ^ 3 ≤ 2 * k ^ 3 := hstep
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by ring

private lemma two_mul_le_factorial {θ : ℕ} (hθ : 6 ≤ θ) : 2 * θ ≤ θ.factorial := by
  induction θ, hθ using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    calc
      2 * (k + 1) ≤ (k + 1) * (2 * k) := by nlinarith
      _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_left _ ih

/-- Numerical inequality at the end of the proof of Graph Minors I, (2.3) (page 44):
for `6 ≤ θ`, `Nat.choose (θ ^ 2 / 2) θ * (θ * θ.factorial / 2 + θ * (θ - 1)) ≤ θ ^ (2 * θ - 2)`. -/
lemma nat_choose_grid_bound_2_3 {θ : ℕ} (hθ : 6 ≤ θ) :
    (θ ^ 2 / 2).choose θ * (θ * θ.factorial / 2 + θ * (θ - 1)) ≤ θ ^ (2 * θ - 2) := by
  rcases lt_or_ge θ 10 with hlt | hge10
  · interval_cases θ <;> decide
  · have hfac : 2 * (θ - 1) ≤ θ.factorial := by
      have := two_mul_le_factorial (by omega : 6 ≤ θ)
      omega
    have hsum_le : θ * θ.factorial / 2 + θ * (θ - 1) ≤ θ.factorial * θ := by
      have h1 : 2 * (θ * (θ - 1)) ≤ θ * θ.factorial := by
        calc
          2 * (θ * (θ - 1)) = θ * (2 * (θ - 1)) := by ring
          _ ≤ θ * θ.factorial := Nat.mul_le_mul_left θ hfac
      have h2 : θ * θ.factorial / 2 * 2 ≤ θ * θ.factorial := Nat.div_mul_le_self _ 2
      nlinarith
    have hchoose_fac : (θ ^ 2 / 2).choose θ * θ.factorial ≤ (θ ^ 2 / 2) ^ θ := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow (θ ^ 2 / 2) θ
    have hpow_le : (θ ^ 2 / 2) ^ θ * 2 ^ θ ≤ θ ^ (2 * θ) := by
      rw [← mul_pow, show θ ^ (2 * θ) = (θ ^ 2) ^ θ by rw [← pow_mul]]
      exact Nat.pow_le_pow_left (Nat.div_mul_le_self (θ ^ 2) 2) θ
    have hpow_bound : (θ ^ 2 / 2) ^ θ * θ ≤ θ ^ (2 * θ - 2) := by
      have h2pos : 0 < 2 ^ θ := by positivity
      refine Nat.le_of_mul_le_mul_right ?_ h2pos
      calc
        (θ ^ 2 / 2) ^ θ * θ * 2 ^ θ = (θ ^ 2 / 2) ^ θ * 2 ^ θ * θ := by ring
        _ ≤ θ ^ (2 * θ) * θ := Nat.mul_le_mul_right θ hpow_le
        _ = θ ^ (2 * θ - 2) * θ ^ 3 := by
          rw [← pow_succ, ← pow_add]
          congr 1
          omega
        _ ≤ θ ^ (2 * θ - 2) * 2 ^ θ := Nat.mul_le_mul_left _ (pow_three_le_two_pow hge10)
    calc
      (θ ^ 2 / 2).choose θ * (θ * θ.factorial / 2 + θ * (θ - 1))
        ≤ (θ ^ 2 / 2).choose θ * (θ.factorial * θ) := Nat.mul_le_mul_left _ hsum_le
      _ = (θ ^ 2 / 2).choose θ * θ.factorial * θ := by ring
      _ ≤ (θ ^ 2 / 2) ^ θ * θ := Nat.mul_le_mul_right θ hchoose_fac
      _ ≤ θ ^ (2 * θ - 2) := hpow_bound

end GraphMinor.GM01
