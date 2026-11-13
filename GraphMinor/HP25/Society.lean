module

public import GraphMinor.HP25.Alternate
public import GraphMinor.GM13.Defs
public import GraphMinor.GM09.Section2e
import GraphMinor.GM09.Section3a
import GraphMinor.HP25.CrossTools
import GraphMinor.Compute.Bridge13

/-!
# The society of a cycle, and crossings against crosses

To use the two paths theorem of Graph Minors XIII, Section 8, for a graph `G` with a cycle `C`
(Humeau and Pous, Definition 2.4, page 6), we view `(G, Ω)` as a society, with `Ω` the cyclic order
of `C` (`cycleSociety`). A cross of this society (Graph Minors IX, Section 2, page 44: two disjoint
paths with ends `p₁, q₁, p₂, q₂ ∈ Ω̄` in this cyclic order) may pass through vertices of `C`, while a
crossing of `C` (Humeau and Pous) uses two `C`-paths. They are matched by `isCrossed_of_hasCross`:
a path of a cross that passes through a vertex `w` of `C` is cut at `w`, and one of the two pieces
still has ends that alternate with the other path. Induction on the total length ends with two
`C`-paths.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `{a, b}` and `{c, d}` alternate on `T`, in either orientation of the second pair. -/
def Alt (T : List V) (a b c d : V) : Prop :=
  Alternate T a b c d ∨ Alternate T a b d c

theorem Alternate.mem {T : List V} {a b c d : V} (h : Alternate T a b c d) :
    a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ d ∈ T := by
  obtain ⟨k, L₁, L₂, hrot, hc, hd⟩ := h
  have hm : ∀ x, x ∈ a :: L₁ ++ b :: L₂ → x ∈ T := fun x hx => by
    rw [← hrot] at hx
    exact List.mem_rotate.mp hx
  exact ⟨hm a (by simp), hm b (by simp), hm c (by simp [hc]), hm d (by simp [hd])⟩

/-- Cutting the first pair at a vertex `w` of the arc from `a` to `b` that holds `c`. -/
private theorem Alternate.split_left {T : List V} {a b c d w : V} {k : ℕ} {L₁ L₂ : List V}
    (hrot : T.rotate k = a :: L₁ ++ b :: L₂) (hc : c ∈ L₁) (hd : d ∈ L₂) (hw : w ∈ L₁)
    (hwc : w ≠ c) : Alternate T a w c d ∨ Alternate T w b c d := by
  obtain ⟨X, Y, rfl⟩ := List.append_of_mem hw
  rcases List.mem_append.mp hc with hcX | hcY
  · left
    refine ⟨k, X, Y ++ b :: L₂, ?_, hcX, by simp [hd]⟩
    rw [hrot]
    simp
  · right
    have hcY' : c ∈ Y := by
      rcases List.mem_cons.mp hcY with h | h
      · exact absurd h.symm hwc
      · exact h
    refine ⟨k + (X.length + 1), Y, L₂ ++ a :: X, ?_, hcY', by simp [hd]⟩
    rw [← List.rotate_rotate, hrot]
    have e : a :: (X ++ w :: Y) ++ b :: L₂ = a :: X ++ w :: (Y ++ b :: L₂) := by simp
    rw [e, rotate_cons_append_cons']
    simp

/-- Cutting the first pair at a vertex `w` of `T` other than the four ends. -/
theorem Alternate.split {T : List V} {a b c d w : V} (h : Alternate T a b c d) (hwT : w ∈ T)
    (hwa : w ≠ a) (hwb : w ≠ b) (hwc : w ≠ c) (hwd : w ≠ d) :
    Alternate T a w c d ∨ Alternate T w b c d := by
  obtain ⟨k, L₁, L₂, hrot, hc, hd⟩ := h
  have hw : w ∈ a :: L₁ ++ b :: L₂ := by rw [← hrot]; exact List.mem_rotate.mpr hwT
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hw
  rcases hw with h | h | h | h
  · exact absurd h hwa
  · exact Alternate.split_left hrot hc hd h hwc
  · exact absurd h hwb
  · -- `w` lies on the arc from `b` to `a`: use the swapped form
    have hrot' : T.rotate (k + (L₁.length + 1)) = b :: L₂ ++ a :: L₁ := by
      rw [← List.rotate_rotate, hrot, rotate_cons_append_cons']
    rcases Alternate.split_left hrot' hd hc h hwd with h' | h'
    · exact Or.inr h'.swap
    · exact Or.inl h'.swap

theorem Alt.swap {T : List V} {a b c d : V} (h : Alt T a b c d) : Alt T b a c d := by
  rcases h with h | h
  · exact Or.inr h.swap
  · exact Or.inl h.swap

theorem Alt.symm₂ {T : List V} {a b c d : V} (h : Alt T a b c d) : Alt T a b d c :=
  h.symm

theorem Alt.comm {T : List V} {a b c d : V} (h : Alt T a b c d) : Alt T c d a b := by
  rcases h with h | h
  · exact Or.inr h.comm
  · exact Or.inl h.comm.swap

theorem Alt.mem {T : List V} {a b c d : V} (h : Alt T a b c d) :
    a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ d ∈ T := by
  rcases h with h | h
  · exact h.mem
  · obtain ⟨h1, h2, h3, h4⟩ := h.mem
    exact ⟨h1, h2, h4, h3⟩

/-- Cutting the first pair at a vertex `w` of `T` other than the four ends. -/
theorem Alt.split {T : List V} {a b c d w : V} (h : Alt T a b c d) (hwT : w ∈ T)
    (hwa : w ≠ a) (hwb : w ≠ b) (hwc : w ≠ c) (hwd : w ≠ d) :
    Alt T a w c d ∨ Alt T w b c d := by
  rcases h with h | h
  · rcases h.split hwT hwa hwb hwc hwd with h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inr (Or.inl h')
  · rcases h.split hwT hwa hwb hwd hwc with h' | h'
    · exact Or.inl (Or.inr h')
    · exact Or.inr (Or.inr h')

/-- Indices `i < r < j < s` give alternation. -/
theorem alternate_of_idx {T : List V} {i r j s : ℕ} (hir : i < r) (hrj : r < j) (hjs : j < s)
    (hs : s < T.length) :
    Alternate T (T[i]'(by omega)) (T[j]'(by omega)) (T[r]'(by omega)) (T[s]'hs) := by
  refine ⟨i, (T.drop (i + 1)).take (j - i - 1), T.drop (j + 1) ++ T.take i, ?_, ?_, ?_⟩
  · rw [List.rotate_eq_drop_append_take (by omega)]
    have e1 : T.drop i = T[i] :: T.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
    have e2 : T.drop (i + 1) = (T.drop (i + 1)).take (j - i - 1) ++ T[j] :: T.drop (j + 1) := by
      conv_lhs => rw [← List.take_append_drop (j - i - 1) (T.drop (i + 1))]
      congr 1
      rw [List.drop_drop, List.drop_eq_getElem_cons (by omega)]
      congr 2 <;> omega
    rw [e1]
    nth_rw 1 [e2]
    simp only [List.cons_append, List.append_assoc]
  · rw [List.mem_iff_getElem]
    exact ⟨r - i - 1, by simp; omega, by simp; congr 1; omega⟩
  · refine List.mem_append_left _ (List.mem_iff_getElem.mpr ⟨s - j - 1, by simp; omega, ?_⟩)
    simp
    congr 1
    omega

private theorem length_pos_of_ne {u v : V} {p : G.Walk u v} (h : u ≠ v) : 0 < p.length := by
  rcases Nat.eq_zero_or_pos p.length with h0 | h0
  · exact absurd (Walk.eq_of_length_eq_zero h0) h
  · exact h0

/-- **Disjoint paths with alternating ends give a crossing.** The paths may pass through vertices
of `T`; each such vertex cuts its path into two pieces, one of which still alternates. -/
theorem isCrossed_of_alt_paths {T : List V} :
    ∀ (n : ℕ) {a b c d : V} (P : G.Walk a b) (Q : G.Walk c d), P.length + Q.length ≤ n →
      P.IsPath → Q.IsPath → P.support.Disjoint Q.support → Alt T a b c d → IsCrossed G T := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c d P Q hlen hP hQ hdisj halt
  obtain ⟨haT, hbT, hcT, hdT⟩ := halt.mem
  by_cases hPw : ∃ w ∈ P.support, w ≠ a ∧ w ≠ b ∧ w ∈ T
  · obtain ⟨w, hw, hwa, hwb, hwT⟩ := hPw
    have hwQ : w ∉ Q.support := fun h => hdisj hw h
    have hwc : w ≠ c := fun h => hwQ (h ▸ Q.start_mem_support)
    have hwd : w ≠ d := fun h => hwQ (h ▸ Q.end_mem_support)
    have hspec := congrArg Walk.length (P.take_spec hw)
    rw [Walk.length_append] at hspec
    have h1 : 0 < (P.takeUntil w hw).length := length_pos_of_ne (Ne.symm hwa)
    have h2 : 0 < (P.dropUntil w hw).length := length_pos_of_ne hwb
    rcases halt.split hwT hwa hwb hwc hwd with h | h
    · exact ih _ (by omega) (P.takeUntil w hw) Q le_rfl (hP.takeUntil hw) hQ
        (fun x hx1 hx2 => hdisj (P.support_takeUntil_subset_support hw hx1) hx2) h
    · exact ih _ (by omega) (P.dropUntil w hw) Q le_rfl (hP.dropUntil hw) hQ
        (fun x hx1 hx2 => hdisj (P.support_dropUntil_subset_support hw hx1) hx2) h
  by_cases hQw : ∃ w ∈ Q.support, w ≠ c ∧ w ≠ d ∧ w ∈ T
  · obtain ⟨w, hw, hwc, hwd, hwT⟩ := hQw
    have hwP : w ∉ P.support := fun h => hdisj h hw
    have hwa : w ≠ a := fun h => hwP (h ▸ P.start_mem_support)
    have hwb : w ≠ b := fun h => hwP (h ▸ P.end_mem_support)
    have hspec := congrArg Walk.length (Q.take_spec hw)
    rw [Walk.length_append] at hspec
    have h1 : 0 < (Q.takeUntil w hw).length := length_pos_of_ne (Ne.symm hwc)
    have h2 : 0 < (Q.dropUntil w hw).length := length_pos_of_ne hwd
    rcases halt.comm.split hwT hwc hwd hwa hwb with h | h
    · exact ih _ (by omega) P (Q.takeUntil w hw) le_rfl hP (hQ.takeUntil hw)
        (fun x hx1 hx2 => hdisj hx1 (Q.support_takeUntil_subset_support hw hx2)) h.comm
    · exact ih _ (by omega) P (Q.dropUntil w hw) le_rfl hP (hQ.dropUntil hw)
        (fun x hx1 hx2 => hdisj hx1 (Q.support_dropUntil_subset_support hw hx2)) h.comm
  push Not at hPw hQw
  have tP : IsTPath G T P := ⟨hP, haT, hbT, fun x hx hxa hxb => ⟨hPw x hx hxa hxb, hPw x hx hxa hxb⟩⟩
  have tQ : IsTPath G T Q := ⟨hQ, hcT, hdT, fun x hx hxc hxd => ⟨hQw x hx hxc hxd, hQw x hx hxc hxd⟩⟩
  rcases halt with h | h
  · exact isCrossed_of_alternate' h P Q tP tQ hdisj
  · exact isCrossed_of_alternate' h P Q.reverse tP (IsTPath.reverse tQ)
      (fun x hx1 hx2 => hdisj hx1 (by simpa using hx2))

/-- Crossing pairs of the cyclic order of a list alternate on the list (first with sorted
indices). -/
private theorem alt_of_crosses_sorted {C : List V} (hnd : C.Nodup) (hne : C ≠ []) {i j k l : ℕ}
    (hij : i < j) (hj : j < C.length) (hkl : k < l) (hl : l < C.length)
    (h : (GM09.CyclicPerm.ofNodupList C hnd hne).Crosses (C[i]'(by omega)) (C[j]'hj)
      (C[k]'(by omega)) (C[l]'hl)) :
    Alt C (C[i]'(by omega)) (C[j]'hj) (C[k]'(by omega)) (C[l]'hl) := by
  rcases (GM09.CyclicPerm.ofNodupList_crosses_iff C hnd hne hij hj hkl hl).mp h with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl (alternate_of_idx h1 h2 h3 hl)
  · exact Alt.comm (Or.inl (alternate_of_idx h1 h2 h3 hj))

/-- Crossing pairs of the cyclic order of a list alternate on the list. -/
theorem alt_of_crosses {C : List V} (hnd : C.Nodup) (hne : C ≠ []) {p₁ p₂ q₁ q₂ : V}
    (h : (GM09.CyclicPerm.ofNodupList C hnd hne).Crosses p₁ p₂ q₁ q₂) : Alt C p₁ p₂ q₁ q₂ := by
  obtain ⟨hp₁, hp₂, hq₁, hq₂, hp, hq⟩ := Compute.crosses_mem_and_ne h
  simp only [GM09.CyclicPerm.ofNodupList_bar, Set.mem_ofPred_eq] at hp₁ hp₂ hq₁ hq₂
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp₁
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp₂
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq₁
  obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.mp hq₂
  have hij : i ≠ j := fun e => hp (by subst e; rfl)
  have hkl : k ≠ l := fun e => hq (by subst e; rfl)
  rcases Nat.lt_or_gt_of_ne hij with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hkl with h2 | h2
  · exact alt_of_crosses_sorted hnd hne h1 hj h2 hl h
  · exact (alt_of_crosses_sorted hnd hne h1 hj h2 hk h.swap_right).symm₂
  · exact (alt_of_crosses_sorted hnd hne h1 hi h2 hl h.swap_left).swap
  · exact (alt_of_crosses_sorted hnd hne h1 hi h2 hk h.swap_left.swap_right).swap.symm₂

/-- The society `(G, Ω)` of a graph `G` and a list `C` without repetition, with `Ω` the cyclic
order of `C` (Graph Minors IX, Section 1: a society is a graph with a cyclic permutation of a
subset of its vertices). -/
@[expose] noncomputable def cycleSociety [Finite V] (G : SimpleGraph V) (C : List V) (hnd : C.Nodup)
    (hne : C ≠ []) : GM09.Society V (Sym2 V) where
  G := Graph.ofSimpleGraph G
  Ω := GM09.CyclicPerm.ofNodupList C hnd hne
  finite_V := Set.toFinite _
  finite_E := Set.toFinite _
  bar_subset := fun _ _ => Set.mem_univ _

theorem cycleSociety_G [Finite V] (G : SimpleGraph V) (C : List V) (hnd : C.Nodup) (hne : C ≠ []) :
    (cycleSociety G C hnd hne).G = Graph.ofSimpleGraph G := rfl

theorem cycleSociety_bar [Finite V] (G : SimpleGraph V) (C : List V) (hnd : C.Nodup)
    (hne : C ≠ []) : (cycleSociety G C hnd hne).Ω.bar = {x | x ∈ C} := rfl

/-- **A cross of the society of a cycle is a crossing of the cycle.** -/
theorem isCrossed_of_hasCross [Finite V] {C : List V} (hnd : C.Nodup) (hne : C ≠ [])
    (h : GM13.HasCross (cycleSociety G C hnd hne)) : IsCrossed G C := by
  obtain ⟨P, Q, hdisj, p₁, p₂, q₁, q₂, ⟨hP, _, _, _⟩, ⟨hQ, _, _, _⟩, hcr⟩ := h
  rcases hP with ⟨hP_le, W₁, hW₁_simple, hVP, _⟩
  rcases hQ with ⟨hQ_le, W₂, hW₂_simple, hVQ, _⟩
  rw [cycleSociety_G] at hP_le hQ_le
  obtain ⟨W₁', hs₁, _⟩ := GM09.exists_walk_up_of_le hP_le W₁
  obtain ⟨W₂', hs₂, _⟩ := GM09.exists_walk_up_of_le hQ_le W₂
  have hW₁'_simple : W₁'.IsSimple := by
    unfold Surface.GraphWalk.IsSimple; rw [hs₁]; exact hW₁_simple
  have hW₂'_simple : W₂'.IsSimple := by
    unfold Surface.GraphWalk.IsSimple; rw [hs₂]; exact hW₂_simple
  refine isCrossed_of_alt_paths _ W₁'.toSimpleGraphWalk W₂'.toSimpleGraphWalk le_rfl
    (Surface.GraphWalk.isPath_toSimpleGraphWalk hW₁'_simple)
    (Surface.GraphWalk.isPath_toSimpleGraphWalk hW₂'_simple) ?_ (alt_of_crosses hnd hne hcr)
  intro v hv₁ hv₂
  rw [Surface.GraphWalk.support_toSimpleGraphWalk, hs₁] at hv₁
  rw [Surface.GraphWalk.support_toSimpleGraphWalk, hs₂] at hv₂
  have hvP : v ∈ P.vertexSet := by rw [hVP]; exact hv₁
  have hvQ : v ∈ Q.vertexSet := by rw [hVQ]; exact hv₂
  exact Set.disjoint_left.mp hdisj hvP hvQ

/-- **A crossing of a cycle is a cross of its society.** -/
theorem hasCross_of_isCrossed [Finite V] {C : List V} (hnd : C.Nodup) (hne : C ≠ [])
    (h : IsCrossed G C) : GM13.HasCross (cycleSociety G C hnd hne) := by
  obtain ⟨a, b, c, d, Q, R, ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, tQ, tR, hdisj⟩ := h
  have hsl : s < C.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hs; exact absurd hs (by simp)
  rw [List.getElem?_eq_some_iff] at hi hr hj hs
  obtain ⟨_, hi⟩ := hi
  obtain ⟨_, hr⟩ := hr
  obtain ⟨_, hj⟩ := hj
  obtain ⟨_, hs⟩ := hs
  subst hi hr hj hs
  have hcr := (GM09.CyclicPerm.ofNodupList_crosses_iff C hnd hne (by omega : i < j) (by omega)
    (by omega : r < s) hsl).mpr (Or.inl ⟨hir, hrj, hjs⟩)
  obtain ⟨hp₁, hp₂, hq₁, hq₂, hp_ne, hq_ne⟩ := Compute.crosses_mem_and_ne hcr
  refine ⟨GM09.walkSubgraph Q.toGraphWalk, GM09.walkSubgraph R.toGraphWalk, ?_, _, _, _, _,
    ⟨GM09.isGraphPathWithEnds_walkSubgraph (SimpleGraph.Walk.isSimple_toGraphWalk tQ.1),
      hp_ne, hp₁, hp₂⟩,
    ⟨GM09.isGraphPathWithEnds_walkSubgraph (SimpleGraph.Walk.isSimple_toGraphWalk tR.1),
      hq_ne, hq₁, hq₂⟩, hcr⟩
  rw [Set.disjoint_left]
  intro v hv₁ hv₂
  rw [GM09.vertexSet_walkSubgraph, Set.mem_ofPred_eq,
    SimpleGraph.Walk.support_toGraphWalk] at hv₁ hv₂
  exact hdisj hv₁ hv₂

/-- **Crossed and cross agree**: a cycle is crossed exactly when its society has a cross. -/
theorem isCrossed_iff_hasCross [Finite V] {C : List V} (hnd : C.Nodup) (hne : C ≠ []) :
    IsCrossed G C ↔ GM13.HasCross (cycleSociety G C hnd hne) :=
  ⟨hasCross_of_isCrossed hnd hne, isCrossed_of_hasCross hnd hne⟩

end GraphMinor.HP25
