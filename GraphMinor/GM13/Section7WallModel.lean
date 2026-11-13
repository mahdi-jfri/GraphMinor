module

public import GraphMinor.Minor.Model
public import Mathlib.Combinatorics.Graph.Simple
public import GraphMinor.GM09.Defs
import GraphMinor.GM09.Basic
import GraphMinor.GM09.Section3a
import GraphMinor.GM14.CylinderParts
import GraphMinor.GM16.ConnectedPathStar
import GraphMinor.GM16.GraphPathSystemUnion

/-!
# A graph is a minor of its subdivisions

The proof of (7.4) (Graph Minors XIII, page 90) applies XII (4.4) to the wall tangle of `H`.
That tangle is induced from a minor model of a wall in `H`. This file builds the model.

Let `S` be a simple graph, `c` a one-to-one map of its vertices into `G`, and for each edge `ab`
of `S` let `P(ab)` be a path of `G` from `c a` to `c b`. The paths of distinct edges share no
edge and meet only in vertices `c v`, and each path meets the vertices `c v` only in its ends.
Orient each edge from its end of smaller rank to its end of larger rank. The model edge of `ab`
is the last edge of `P(ab)`, and the branch set of `v` is `c v` together with the rest of the
paths of the edges leaving `v` (`exists_isMinorModel_of_paths`).
-/

public section

namespace GraphMinor.GM13

open Set Function
open Graph
open GraphMinor
open GraphMinor.GM09

universe u v w

variable {α : Type u} {β : Type v}

/-- **The last edge of a path.** A path `P` from `a` to `b ≠ a` has an edge `ℓ` from some `q` to
`b`, and a subpath from `a` to `q` that misses `b` and `ℓ`. -/
theorem _root_.GraphMinor.GM09.IsGraphPathWithEnds.exists_last_edge {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    ∃ (ℓ : β) (q : α) (Q : Graph α β), P.IsLink ℓ q b ∧ Q ≤ P ∧ IsGraphPathWithEnds G Q a q ∧
      b ∉ V(Q) ∧ ℓ ∉ E(Q) := by
  obtain ⟨ℓ, -, q, hlink⟩ := hP.symm.exists_inc_left_of_ne (Ne.symm hab)
  have hqb : q ≠ b := by
    rintro rfl
    exact GM14.IsGraphPathWithEnds.no_loop hP hlink
  obtain ⟨Q, Q₂, hQP, -, hQ, hQ₂, -, hint, -⟩ := hP.exists_split_at hlink.right_mem
  have hbQ : b ∉ V(Q) := by
    intro hb
    have : b ∈ V(Q) ∩ V(Q₂) := ⟨hb, hQ₂.right_mem⟩
    rw [hint] at this
    exact hqb (this.symm)
  refine ⟨ℓ, q, Q, hlink.symm, hQP, hQ.mono hP.le, hbQ, fun hℓ => ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hℓ
  rcases hlink.eq_and_eq_or_eq_and_eq (hxy.mono hQP) with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hbQ hxy.left_mem
  · exact hbQ hxy.right_mem

/-- **A graph is a minor of its subdivisions.** Let `S` be a simple graph, `rk` a one-to-one rank
of its vertices, and `c` a one-to-one map of its vertices into `V(G)`. For each edge `ab` of `S`
let `P(ab)` be a path of `G` from `c a` to `c b` that meets the vertices `c v` only in its ends,
where paths of distinct edges share no edge and meet only in vertices `c v`. Then `S` has a minor
model in `G` whose model edge of each edge `e` is an edge of `P(e)`. -/
theorem exists_isMinorModel_of_paths [Nonempty β] {ν : Type w} {S : SimpleGraph ν}
    {G : Graph α β} (rk : ν → ℕ) (hrk : Injective rk) (c : ν → α) (hc : Injective c)
    (hcG : ∀ v, c v ∈ V(G)) (P : Sym2 ν → Graph α β)
    (hP : ∀ a b, S.Adj a b → IsGraphPathWithEnds G (P s(a, b)) (c a) (c b))
    (hPc : ∀ a b, S.Adj a b → V(P s(a, b)) ∩ range c ⊆ {c a, c b})
    (hPV : ∀ e ∈ S.edgeSet, ∀ e' ∈ S.edgeSet, e ≠ e' → V(P e) ∩ V(P e') ⊆ range c)
    (hPE : ∀ e ∈ S.edgeSet, ∀ e' ∈ S.edgeSet, e ≠ e' → Disjoint E(P e) E(P e')) :
    ∃ (ηv : ν → Set α) (ηe : Sym2 ν → β),
      IsMinorModel (Graph.ofSimpleGraph S) G ηv ηe ∧ ∀ e ∈ S.edgeSet, ηe e ∈ E(P e) := by
  classical
  -- orient each edge from the end of smaller rank
  have hor : ∀ e : Sym2 ν, ∃ a b : ν, e ∈ S.edgeSet → e = s(a, b) ∧ S.Adj a b ∧ rk a < rk b := by
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      by_cases hxy : S.Adj x y
      · rcases lt_or_gt_of_ne (fun h => hxy.ne (hrk h)) with h | h
        · exact ⟨x, y, fun _ => ⟨rfl, hxy, h⟩⟩
        · exact ⟨y, x, fun _ => ⟨Sym2.eq_swap, hxy.symm, h⟩⟩
      · exact ⟨x, y, fun he => (hxy he).elim⟩
  choose lo hi hlohi using hor
  have hlast : ∀ e : Sym2 ν, ∃ (ℓ : β) (q : α) (Q : Graph α β), e ∈ S.edgeSet →
      (P e).IsLink ℓ q (c (hi e)) ∧ Q ≤ P e ∧ IsGraphPathWithEnds G Q (c (lo e)) q ∧
        c (hi e) ∉ V(Q) ∧ ℓ ∉ E(Q) := by
    intro e
    by_cases he : e ∈ S.edgeSet
    · obtain ⟨hee, hadj, -⟩ := hlohi e he
      have hPe := hP _ _ hadj
      rw [← hee] at hPe
      obtain ⟨ℓ, q, Q, h⟩ := hPe.exists_last_edge (fun h => hadj.ne (hc h))
      exact ⟨ℓ, q, Q, fun _ => h⟩
    · exact ⟨Classical.arbitrary β, c (lo e), P e, fun h => (he h).elim⟩
  choose ℓ q Q hQ using hlast
  -- the basic facts about one edge
  have hPe : ∀ e ∈ S.edgeSet, IsGraphPathWithEnds G (P e) (c (lo e)) (c (hi e)) := by
    intro e he
    obtain ⟨hee, hadj, -⟩ := hlohi e he
    have := hP _ _ hadj
    rwa [← hee] at this
  have hlink : ∀ e ∈ S.edgeSet, G.IsLink (ℓ e) (q e) (c (hi e)) :=
    fun e he => (hQ e he).1.mono (hPe e he).le
  have hℓP : ∀ e ∈ S.edgeSet, ℓ e ∈ E(P e) := fun e he => (hQ e he).1.edge_mem
  have hF3 : ∀ e ∈ S.edgeSet, ∀ z ∈ V(Q e), z ∈ range c → z = c (lo e) := by
    intro e he z hz hzc
    obtain ⟨hee, hadj, -⟩ := hlohi e he
    have hzP : z ∈ V(P e) := (hQ e he).2.1.vertexSet_mono hz
    have h1 := hPc _ _ hadj (show z ∈ V(P s(lo e, hi e)) ∩ range c from ⟨hee ▸ hzP, hzc⟩)
    rcases h1 with h1 | h1
    · exact h1
    · exact ((hQ e he).2.2.2.1 (h1 ▸ hz)).elim
  let arms (v : ν) := {e : Sym2 ν // e ∈ S.edgeSet ∧ lo e = v}
  let ηv : ν → Set α := fun v => {c v} ∪ ⋃ i : arms v, V(Q i.1)
  have hdisj : ∀ v w z, z ∈ ηv v → z ∈ ηv w → v = w := by
    have hside : ∀ v z, z ∈ ηv v → z ∈ range c → z = c v := by
      intro v z hz hzc
      rcases hz with hz | hz
      · exact hz
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
        rw [hF3 i.1 i.2.1 z hi hzc, i.2.2]
    intro v w z hv hw
    rcases hv with hv | hv
    · exact hc ((hside w z hw ⟨v, hv.symm⟩).symm.trans hv).symm
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      rcases hw with hw | hw
      · exact hc ((hside v z (Or.inr (mem_iUnion.mpr ⟨i, hi⟩)) ⟨w, hw.symm⟩).symm.trans hw)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hw
        by_cases hij : i.1 = j.1
        · rw [← i.2.2, ← j.2.2, hij]
        · have hzc : z ∈ range c := hPV i.1 i.2.1 j.1 j.2.1 hij
            ⟨(hQ i.1 i.2.1).2.1.vertexSet_mono hi, (hQ j.1 j.2.1).2.1.vertexSet_mono hj⟩
          have h1 := hF3 i.1 i.2.1 z hi hzc
          have h2 := hF3 j.1 j.2.1 z hj hzc
          rw [← i.2.2, ← j.2.2]
          exact hc (h1.symm.trans h2)
  have hqmem : ∀ e (he : e ∈ S.edgeSet), q e ∈ ηv (lo e) :=
    fun e he => Or.inr (mem_iUnion.mpr ⟨⟨e, he, rfl⟩, (hQ e he).2.2.1.right_mem⟩)
  have hhimem : ∀ e, c (hi e) ∈ ηv (hi e) := fun e => Or.inl rfl
  have hEeq : E(Graph.ofSimpleGraph S) = S.edgeSet := rfl
  refine ⟨ηv, ℓ, ?_, hℓP⟩
  refine ⟨fun v _ => ⟨c v, Or.inl rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- vertex_subset
    intro v _ z hz
    rcases hz with hz | hz
    · exact hz ▸ hcG v
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact (hQ i.1 i.2.1).2.2.1.le.vertexSet_mono hi
  · -- edge_mem
    intro e he
    exact (hlink e he).edge_mem
  · -- vertex_disjoint
    intro v₁ _ v₂ _ hne
    exact Set.disjoint_left.mpr fun z h₁ h₂ => hne (hdisj v₁ v₂ z h₁ h₂)
  · -- edge_injOn
    intro e he e' he' heq
    by_contra hne
    exact Set.disjoint_left.mp (hPE e he e' he' hne) (hℓP e he) (heq ▸ hℓP e' he')
  · -- inc_iff
    intro v _ e he
    obtain ⟨hee, hadj, -⟩ := hlohi e he
    constructor
    · rintro ⟨y, hy, -⟩
      rw [hee] at hy
      rcases Sym2.eq_iff.mp hy with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact ⟨q e, hqmem e he, (hlink e he).inc_left⟩
      · exact ⟨c (hi e), hhimem e, (hlink e he).inc_right⟩
    · rintro ⟨x, hx, hinc⟩
      refine ⟨if v = lo e then hi e else lo e, ?_, he⟩
      rcases hinc.eq_or_eq_of_isLink (hlink e he) with rfl | rfl
      · have := hdisj _ _ _ (hqmem e he) hx
        subst this
        rw [if_pos rfl]
        exact hee
      · have := hdisj _ _ _ (hhimem e) hx
        subst this
        have hne : hi e ≠ lo e := fun h => hadj.ne (h.symm)
        rw [if_neg hne]
        exact hee.trans Sym2.eq_swap
  · -- isLoopAt_iff
    intro v _ e he
    obtain ⟨hee, hadj, hlt⟩ := hlohi e he
    constructor
    · rintro ⟨hev, -⟩
      rw [hee] at hev
      rcases Sym2.eq_iff.mp hev with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (hadj.ne (h1.trans h2.symm)).elim
      · exact (hadj.ne (h1.trans h2.symm)).elim
    · intro hall
      have h1 := hdisj _ _ _ (hqmem e he) (hall _ (hlink e he).inc_left)
      have h2 := hdisj _ _ _ (hhimem e) (hall _ (hlink e he).inc_right)
      exact (hadj.ne (h1.trans h2.symm)).elim
  · -- connected
    intro v _
    let F := ℓ '' S.edgeSet
    have hArmDel (i : arms v) : Q i.1 ≤ G.deleteEdges F := by
      have hQi := hQ i.1 i.2.1
      refine ⟨hQi.2.2.1.le.vertexSet_mono, ?_⟩
      intro f x y hl
      refine ⟨hl.mono hQi.2.2.1.le, ?_⟩
      rintro ⟨e', he', rfl⟩
      by_cases hie : i.1 = e'
      · subst hie
        exact hQi.2.2.2.2 hl.edge_mem
      · exact Set.disjoint_left.mp (hPE i.1 i.2.1 e' he' hie)
          (hQi.2.1.edgeSet_mono hl.edge_mem) (hℓP e' he')
    have hRoot : ({c v} : Set α) ⊆ V(G.deleteEdges F) := by
      rintro x hx
      exact (mem_singleton_iff.mp hx).symm ▸ hcG v
    refine ⟨GM16.pathSystemGraph (G.deleteEdges F) {c v} (fun i : arms v => Q i.1),
      GM16.pathSystemGraph_le hRoot hArmDel, rfl, ?_⟩
    refine GM16.graphConnected_pathSystemGraph_star (b := fun i : arms v => q i.1) fun i => ?_
    have h := (hQ i.1 i.2.1).2.2.1.of_le (hArmDel i)
    rwa [i.2.2] at h

end GraphMinor.GM13
