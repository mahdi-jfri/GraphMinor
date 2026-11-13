module

public import GraphMinor.GM21.Section6Jumps
public import GraphMinor.GM06.Defs
import GraphMinor.GM21.Section6TwoEdges
import GraphMinor.GM06.Section3Dual
import GraphMinor.Surface.ArcTools
import GraphMinor.GM21.LinkagePaths
import GraphMinor.GM21.LinkageLemmas

/-!
# Graph Minors XXI, (6.3), the last step: a jump is drawn as a line

The last step of the proof of (6.3) (page 29 of the preprint) treats each `Σ`-jump `J` as a
curve: "every $\Sigma$-jump $J$ is homotopic in $\hat{\Sigma}$ to the lines in $bd(\Sigma)$ joining
the ends of $J$". Here we show that `J` is drawn as a line.

`jumpLine Γ ιE J` is the union of the closures of the edges of `Γ` that belong to `J`. If `J` is a
path of the drawing with at least one edge, we number its vertices `w 0, …, w m` along the path. The
closures of its edges are lines from `w i` to `w (i + 1)`, and two different edges have closures
that meet only in vertices. So the union of the first `k` of them is a line from `w 0` to `w k`
that meets `V(Γ)` exactly in `w 0, …, w k` (`jumpLine_spec`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Function Hypergraph GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- The drawing of a subgraph `J` of `Γ`: the union of the closures of the edges `e` of `Γ` with
`ιE e ∈ E(J)`. -/
def jumpLine (Γ : Drawing S) (ιE : Set S → β) (J : Hypergraph α β) : Set S :=
  ⋃ e ∈ {e ∈ Γ.E | ιE e ∈ J.edgeSet}, closure e

theorem mem_jumpLine {Γ : Drawing S} {ιE : Set S → β} {J : Hypergraph α β} {z : S} :
    z ∈ jumpLine Γ ιE J ↔ ∃ e ∈ Γ.E, ιE e ∈ J.edgeSet ∧ z ∈ closure e := by
  simp only [jumpLine, mem_iUnion, mem_ofPred_eq, exists_prop, and_assoc]

variable [T2Space S]

/-- The closures of two different edges of a drawing meet only in vertices. -/
theorem closure_inter_closure_subset (Γ : Drawing S) {e e' : Set S} (he : e ∈ Γ.E)
    (he' : e' ∈ Γ.E) (hne : e ≠ e') : closure e ∩ closure e' ⊆ Γ.V := by
  rintro z ⟨hz, hz'⟩
  by_contra hzV
  have hzU : z ∈ Γ.U := closure_minimal (fun y hy => (he.2.1 hy).1) Γ.isClosed_U hz
  have h1 := DiscLine.closure_inter_sdiff_subset Γ he ⟨hz, hzU, hzV⟩
  have h2 := DiscLine.closure_inter_sdiff_subset Γ he' ⟨hz', hzU, hzV⟩
  exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he he' hne) h1 h2

variable {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}

omit [T2Space S] in
/-- The vertices of `Γ` in the closure of an edge `e` are the two ends of `ιE e`. -/
theorem closure_inter_V_eq (hiso : IsDrawingIso Γ Γ_sub ιV ιE) {e : Set S} (he : e ∈ Γ.E)
    {u w : S} (hu : u ∈ Γ.V) (hw : w ∈ Γ.V) (huw : u ≠ w) (h2 : (Γ_sub.ends (ιE e)).ncard = 2)
    (hiu : Γ_sub.Inc (ιE e) (ιV u)) (hiw : Γ_sub.Inc (ιE e) (ιV w)) :
    closure e ∩ Γ.V = {u, w} := by
  have hne : ιV u ≠ ιV w := fun h => huw (hiso.ιV_injOn hu hw h)
  have hsub : ({ιV u, ιV w} : Set α) ⊆ Γ_sub.ends (ιE e) := by
    rintro _ (rfl | h)
    · exact hiu
    · exact (mem_singleton_iff.mp h) ▸ hiw
  have hfin : (Γ_sub.ends (ιE e)).Finite := finite_of_ncard_ne_zero (by omega)
  have heq : ({ιV u, ιV w} : Set α) = Γ_sub.ends (ιE e) :=
    eq_of_subset_of_ncard_le hsub (by rw [h2, ncard_pair hne]) hfin
  ext z
  constructor
  · rintro ⟨hz, hzV⟩
    have hzi : ιV z ∈ Γ_sub.ends (ιE e) := (hiso.inc_iff e he z hzV).2 hz
    rw [← heq] at hzi
    rcases hzi with h | h
    · exact Or.inl (hiso.ιV_injOn hzV hu h)
    · exact Or.inr (hiso.ιV_injOn hzV hw (mem_singleton_iff.mp h))
  · rintro (rfl | h)
    · exact ⟨(hiso.inc_iff e he z hu).1 hiu, hu⟩
    · rw [mem_singleton_iff.mp h]
      exact ⟨(hiso.inc_iff e he w hw).1 hiw, hw⟩

/-- **A jump is drawn as a line.** Let `J ≤ Γ_sub` be a path with at least one edge. Then the
union of the closures of the edges of `J` is a line between the two vertices of `Γ` that are the
ends of `J`, and it meets `V(Γ)` exactly in the vertices of `J`. -/
theorem jumpLine_spec (hiso : IsDrawingIso Γ Γ_sub ιV ιE)
    (h2 : ∀ e ∈ Γ_sub.edgeSet, (Γ_sub.ends e).ncard = 2) {J : Hypergraph α β} (hJ : J ≤ Γ_sub)
    (hJp : IsPathGraph J) (hJE : J.edgeSet.Nonempty) :
    ∃ x ∈ Γ.V, ∃ y ∈ Γ.V, x ≠ y ∧ terminals J = {ιV x, ιV y} ∧
      IsLineWithEnds (jumpLine Γ ιE J) x y ∧
      jumpLine Γ ιE J ∩ Γ.V = {z ∈ Γ.V | ιV z ∈ J.vertexSet} := by
  classical
  obtain ⟨x₁, -, x₂, -, -, ⟨m, hm, w, hinj, h0, hmw, hV, hadj⟩, hdeg1⟩ :=
    exists_isIndexedPath_of_isPathGraph hJp hJE
  have hwΓ : ∀ i, w i ∈ ιV '' Γ.V := fun i =>
    hiso.ιV_image ▸ hJ.vertexSet_subset (hV ▸ mem_range_self i)
  choose w' hw'V hw'eq using hwΓ
  have hw'inj : Injective w' := fun i j h => hinj (by rw [← hw'eq i, ← hw'eq j, h])
  -- The edge between `w i` and `w (i + 1)`.
  have hedge : ∀ i : Fin m, ∃ e ∈ Γ.E, ιE e ∈ J.edgeSet ∧
      closure e ∩ Γ.V = {w' i.castSucc, w' i.succ} := by
    intro i
    obtain ⟨-, f, hfi, hfk⟩ := (hadj i.castSucc i.succ).2 (Or.inl (by simp))
    have hfJ := J.edge_mem_of_inc hfi
    obtain ⟨e, he, rfl⟩ : f ∈ ιE '' Γ.E := hiso.ιE_image ▸ hJ.edgeSet_subset hfJ
    refine ⟨e, he, hfJ, closure_inter_V_eq hiso he (hw'V _) (hw'V _) (fun h => ?_)
      (h2 _ (hJ.edgeSet_subset hfJ)) ?_ ?_⟩
    · have := congrArg Fin.val (hw'inj h)
      simp at this
    · rw [hw'eq]
      exact GM10.inc_of_le hJ hfi
    · rw [hw'eq]
      exact GM10.inc_of_le hJ hfk
  choose e he heJ hecl using hedge
  -- The vertex `w' j` with `j ≤ k`, as a set.
  let Vk : ℕ → Set S := fun k => {z | ∃ j : Fin (m + 1), j.1 ≤ k ∧ z = w' j}
  let P : ℕ → Set S := fun k => ⋃ (i : Fin m) (_ : i.1 < k), closure (e i)
  have hind : ∀ k, 1 ≤ k → ∀ hk : k ≤ m,
      IsLineWithEnds (P k) (w' 0) (w' ⟨k, by omega⟩) ∧ P k ∩ Γ.V = Vk k := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro hk
      have hP1 : P 1 = closure (e ⟨0, by omega⟩) := by
        ext z
        simp only [P, mem_iUnion, exists_prop]
        constructor
        · rintro ⟨i, hi, hz⟩
          have : i = ⟨0, by omega⟩ := Fin.ext (show i.1 = 0 by omega)
          exact this ▸ hz
        · intro hz
          exact ⟨⟨0, by omega⟩, by simp, hz⟩
      have hcl := hecl ⟨0, by omega⟩
      have hc0 : (⟨0, by omega⟩ : Fin m).castSucc = 0 := rfl
      have hs0 : (⟨0, by omega⟩ : Fin m).succ = ⟨1, by omega⟩ := rfl
      rw [hc0, hs0] at hcl
      refine ⟨?_, ?_⟩
      · rw [hP1]
        refine DiscLine.isLineWithEnds_closure_edge Γ (he _) hcl fun h => ?_
        have := congrArg Fin.val (hw'inj h)
        simp at this
      · rw [hP1, hcl]
        ext z
        simp only [Vk, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
        constructor
        · rintro (rfl | rfl)
          · exact ⟨0, by simp, rfl⟩
          · exact ⟨⟨1, by omega⟩, le_rfl, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h | h
          · exact Or.inl (congrArg w' (Fin.ext h))
          · exact Or.inr (congrArg w' (Fin.ext h))
    | succ k hk1 ih =>
      intro hk
      obtain ⟨hline, hvert⟩ := ih (by omega)
      let i₀ : Fin m := ⟨k, by omega⟩
      have hcl := hecl i₀
      have hc : i₀.castSucc = ⟨k, by omega⟩ := rfl
      have hs : i₀.succ = ⟨k + 1, by omega⟩ := rfl
      rw [hc, hs] at hcl
      have hPs : P (k + 1) = P k ∪ closure (e i₀) := by
        ext z
        simp only [P, mem_iUnion, mem_union, exists_prop]
        constructor
        · rintro ⟨i, hi, hz⟩
          by_cases hik : i.1 < k
          · exact Or.inl ⟨i, hik, hz⟩
          · have : i = i₀ := Fin.ext (by simp [i₀]; omega)
            exact Or.inr (this ▸ hz)
        · rintro (⟨i, hi, hz⟩ | hz)
          · exact ⟨i, by omega, hz⟩
          · exact ⟨i₀, by simp [i₀], hz⟩
      have hwk : w' ⟨k, by omega⟩ ∈ P k ∩ Γ.V := hvert ▸ ⟨⟨k, by omega⟩, le_rfl, rfl⟩
      have hcap : P k ∩ closure (e i₀) = {w' ⟨k, by omega⟩} := by
        ext z
        constructor
        · rintro ⟨hz, hz'⟩
          obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
          have hne : e i ≠ e i₀ := by
            intro h
            have h' := hecl i
            rw [h, hcl] at h'
            have hmem : w' ⟨k + 1, by omega⟩ ∈ ({w' i.castSucc, w' i.succ} : Set S) :=
              h' ▸ Or.inr rfl
            rcases hmem with h'' | h''
            · have := congrArg Fin.val (hw'inj h'')
              simp at this
              omega
            · have := congrArg Fin.val (hw'inj (mem_singleton_iff.mp h''))
              simp at this
              omega
          have hzV : z ∈ Γ.V := closure_inter_closure_subset Γ (he i) (he i₀) hne ⟨hzi, hz'⟩
          have hz1 : z ∈ Vk k := hvert ▸ ⟨hz, hzV⟩
          have hz2 : z ∈ ({w' ⟨k, by omega⟩, w' ⟨k + 1, by omega⟩} : Set S) := hcl ▸ ⟨hz', hzV⟩
          obtain ⟨j, hj, rfl⟩ := hz1
          rcases hz2 with h | h
          · exact h
          · have := congrArg Fin.val (hw'inj (mem_singleton_iff.mp h))
            simp at this
            omega
        · rintro rfl
          exact ⟨hwk.1, (hcl.symm ▸ (Or.inl rfl : w' ⟨k, by omega⟩ ∈
            ({w' ⟨k, by omega⟩, w' ⟨k + 1, by omega⟩} : Set S)) : _ ∈ closure (e i₀) ∩ Γ.V).1⟩
      refine ⟨?_, ?_⟩
      · rw [hPs]
        refine hline.union (DiscLine.isLineWithEnds_closure_edge Γ (he i₀) hcl fun h => ?_) hcap
        have := congrArg Fin.val (hw'inj h)
        simp at this
      · rw [hPs, union_inter_distrib_right, hvert, hcl]
        ext z
        simp only [Vk, mem_union, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro (⟨j, hj, rfl⟩ | rfl | rfl)
          · exact ⟨j, by omega, rfl⟩
          · exact ⟨⟨k, by omega⟩, by simp, rfl⟩
          · exact ⟨⟨k + 1, by omega⟩, le_rfl, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          by_cases hjk : j.1 ≤ k
          · exact Or.inl ⟨j, hjk, rfl⟩
          · exact Or.inr (Or.inr (congrArg w' (Fin.ext (by simp; omega))))
  obtain ⟨hline, hvert⟩ := hind m hm le_rfl
  -- The drawing of `J` is the union of the first `m` closures.
  have hJline : jumpLine Γ ιE J = P m := by
    ext z
    rw [mem_jumpLine]
    constructor
    · rintro ⟨e', he', he'J, hz⟩
      have hends := hJp.2.2.2.1 _ he'J
      obtain ⟨a, b, hab, hab'⟩ := ncard_eq_two.mp hends
      have ha : J.Inc (ιE e') a := show a ∈ J.ends (ιE e') from hab' ▸ Or.inl rfl
      have hb : J.Inc (ιE e') b := show b ∈ J.ends (ιE e') from hab' ▸ Or.inr rfl
      obtain ⟨ia, rfl⟩ : a ∈ range w := hV ▸ J.vertex_mem_of_inc ha
      obtain ⟨ib, rfl⟩ : b ∈ range w := hV ▸ J.vertex_mem_of_inc hb
      -- The two ends are consecutive.
      have hcons := (hadj ia ib).1 ⟨hab, ιE e', ha, hb⟩
      -- The edge `e i` with the same ends.
      have key : ∀ i : Fin m, ({w i.castSucc, w i.succ} : Set α) = {w ia, w ib} →
          z ∈ P m := by
        intro i hi
        have hiJ := heJ i
        have hinc : ∀ j : Fin (m + 1), w' j ∈ closure (e i) → J.Inc (ιE (e i)) (w j) := by
          intro j hj
          rw [← hw'eq j]
          exact (GM10.inc_iff_of_le hJ hiJ).2 ((hiso.inc_iff _ (he i) _ (hw'V j)).2 hj)
        have hmem : ∀ j : Fin (m + 1), w' j ∈ ({w' i.castSucc, w' i.succ} : Set S) →
            w' j ∈ closure (e i) := fun j hj =>
          (((hecl i).symm ▸ hj : w' j ∈ closure (e i) ∩ Γ.V)).1
        have hsub : ({w i.castSucc, w i.succ} : Set α) ⊆ J.ends (ιE (e i)) := by
          rintro _ (rfl | h)
          · exact hinc _ (hmem _ (Or.inl rfl))
          · rw [mem_singleton_iff.mp h]
            exact hinc _ (hmem _ (Or.inr rfl))
        have hne' : w i.castSucc ≠ w i.succ := fun h => by
          have := congrArg Fin.val (hinj h)
          simp at this
        have heq1 : J.ends (ιE (e i)) = {w i.castSucc, w i.succ} :=
          (eq_of_subset_of_ncard_le hsub (by rw [hJp.2.2.2.1 _ hiJ, ncard_pair hne'])
            (finite_of_ncard_ne_zero (by rw [hJp.2.2.2.1 _ hiJ]; omega))).symm
        have heq2 : J.ends (ιE e') = {w ia, w ib} := hab'
        have hfe : ιE (e i) = ιE e' :=
          hJp.2.2.2.2.1 _ hiJ _ he'J (by rw [heq1, heq2, hi])
        have he'eq : e i = e' := hiso.ιE_injOn (he i) he' hfe
        exact mem_iUnion₂.mpr ⟨i, i.2, he'eq ▸ hz⟩
      rcases hcons with h | h
      · exact key ⟨ia.1, by omega⟩ (by
          rw [show (⟨ia.1, by omega⟩ : Fin m).castSucc = ia from Fin.ext rfl,
            show (⟨ia.1, by omega⟩ : Fin m).succ = ib from Fin.ext (by simp; omega)])
      · exact key ⟨ib.1, by omega⟩ (by
          rw [show (⟨ib.1, by omega⟩ : Fin m).castSucc = ib from Fin.ext rfl,
            show (⟨ib.1, by omega⟩ : Fin m).succ = ia from Fin.ext (by simp; omega), pair_comm])
    · intro hz
      obtain ⟨i, -, hzi⟩ := mem_iUnion₂.mp hz
      exact ⟨e i, he i, heJ i, hzi⟩
  have hm' : (⟨m, by omega⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ := rfl
  refine ⟨w' 0, hw'V 0, w' ⟨m, by omega⟩, hw'V _, fun h => ?_, ?_, hJline ▸ hline, ?_⟩
  · have := congrArg Fin.val (hw'inj h)
    simp at this
    omega
  · -- The terminals are the vertices of degree at most one, which are `w 0` and `w m`.
    rw [hw'eq, hw'eq, h0, hm', hmw]
    ext z
    simp only [terminals, IsTerminal, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    rw [vertexDegree_eq_ncard_incidentEdges hJp.2.2.2.1]
    constructor
    · rintro ⟨hz, hdeg⟩
      exact (hdeg1 z hz).1 hdeg
    · intro h
      have hz : z ∈ J.vertexSet := by
        rcases h with rfl | rfl
        · exact hV ▸ h0 ▸ mem_range_self _
        · exact hV ▸ hmw ▸ mem_range_self _
      exact ⟨hz, (hdeg1 z hz).2 h⟩
  · rw [hJline, hvert]
    ext z
    simp only [Vk, mem_ofPred_eq]
    constructor
    · rintro ⟨j, -, rfl⟩
      exact ⟨hw'V j, (hw'eq j).symm ▸ hV ▸ mem_range_self j⟩
    · rintro ⟨hzV, hzJ⟩
      obtain ⟨j, hj⟩ : ιV z ∈ range w := hV ▸ hzJ
      exact ⟨j, by omega, hiso.ιV_injOn hzV (hw'V j) (hj.symm.trans (hw'eq j).symm)⟩

end LastStep
end GM21
end GraphMinor
