module

public import GraphMinor.GM21.LinkagePaths
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, (1.2)

"**1.2** *If $L$ is a vital $5$-linkage in a simple graph $G$, then either some two terminals in
different components of $L$ are adjacent in $G$, or some terminal has the same degree in $G$ and in
$L$, or $G$ is null.*" (page 2 of the preprint.)

The paper gives no proof, so we give our own. Suppose that all
three conclusions fail. Then every terminal `t` has an edge `tu` of `G` that is not in `L`.

* If `u` is on the component of `t`, then `L` is not vital: shortcut the path along `tu`
  (`not_reachable_of_extra_edge`, which uses `no_chord_of_isVitalLinkage`,
  and simplicity when `u` is the neighbour of `t` on its path).
* If `u` is a terminal of another component, the first conclusion holds.
* So `u` is an inner vertex of another path. A $5$-linkage has at most two components with an edge,
  so there are two such paths `P` (ends `a, b`) and `Q` (ends `c, d`), with edges from `a, b` to
  inner vertices `x, y` of `Q` and from `c, d` to inner vertices `u, v` of `P`. Then the paths
  `a x Q y b` and `c u P v d` replace `P` and `Q` (`not_exchange`), and `L` is
  not vital.

The argument proves the statement for every vital linkage with at most two components that have
an edge, and a $5$-linkage is one of these.
-/

@[expose] public section

namespace GraphMinor.GM21

open Set Hypergraph

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v}

/-! ## Unions of vertex-disjoint subgraphs -/

section Union

variable {G A B : Hypergraph α β}

theorem union_inc_iff {e : β} {x : α} : (A ∪ B).Inc e x ↔ A.Inc e x ∨ B.Inc e x := Iff.rfl

/-- An edge of `A` is not an edge of `B` when `A, B` are vertex-disjoint subgraphs of a graph. -/
theorem not_inc_of_disjoint (hG : G.IsGraph) (hA : A ≤ G) (hB : B ≤ G)
    (hd : Disjoint A.vertexSet B.vertexSet) {e : β} (he : e ∈ A.edgeSet) (x : α) :
    ¬ B.Inc e x := by
  intro hx
  have heB := B.edge_mem_of_inc hx
  obtain ⟨w, hw⟩ := (hG e (hA.edgeSet_subset he)).1
  have hwA : A.Inc e w := (GM10.inc_iff_of_le hA he).2 hw
  have hwB : B.Inc e w := (GM10.inc_iff_of_le hB heB).2 hw
  exact disjoint_left.1 hd (A.vertex_mem_of_inc hwA) (B.vertex_mem_of_inc hwB)

variable (hG : G.IsGraph) (hA : A ≤ G) (hB : B ≤ G) (hd : Disjoint A.vertexSet B.vertexSet)
include hG hA hB hd

/-- An edge of `A ∪ B` at a vertex of `A` is an edge of `A`. -/
theorem union_inc_iff_left {e : β} {x : α} (hx : x ∈ A.vertexSet) :
    (A ∪ B).Inc e x ↔ A.Inc e x := by
  refine ⟨fun h ↦ h.elim id fun h ↦ ?_, Or.inl⟩
  exact (disjoint_left.1 hd hx (B.vertex_mem_of_inc h)).elim

theorem union_inc_iff_of_mem_left {e : β} (he : e ∈ A.edgeSet) {x : α} :
    (A ∪ B).Inc e x ↔ A.Inc e x :=
  ⟨fun h ↦ h.elim id fun h ↦ (not_inc_of_disjoint hG hA hB hd he x h).elim, Or.inl⟩

/-- A walk of `A ∪ B` that starts in `A` stays in `A`. -/
theorem reachable_left_of_reachable_union {x y : α} (hx : x ∈ A.vertexSet)
    (h : (A ∪ B).skeleton.Reachable x y) : A.skeleton.Reachable x y ∧ y ∈ A.vertexSet := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨SimpleGraph.Reachable.refl _, hx⟩
  | @cons x z y hxz _ ih =>
    obtain ⟨hne, e, hex, hez⟩ := hxz
    have hex' : A.Inc e x := (union_inc_iff_left hG hA hB hd hx).1 hex
    have heA : e ∈ A.edgeSet := A.edge_mem_of_inc hex'
    have hez' : A.Inc e z := (union_inc_iff_of_mem_left hG hA hB hd heA).1 hez
    obtain ⟨hr, hy⟩ := ih (A.vertex_mem_of_inc hez')
    exact ⟨(SimpleGraph.Adj.reachable (G := A.skeleton) ⟨hne, e, hex', hez'⟩).trans hr, hy⟩

/-- A connected subgraph of `A ∪ B` that meets `A` is a subgraph of `A`. -/
theorem le_left_of_le_union {C : Hypergraph α β} (hC : C ≤ A ∪ B)
    (hconn : ∀ x ∈ C.vertexSet, ∀ y ∈ C.vertexSet, C.skeleton.Reachable x y)
    {x : α} (hxC : x ∈ C.vertexSet) (hxA : x ∈ A.vertexSet) : C ≤ A := by
  have hAU := le_union_left hA hB
  have hV : C.vertexSet ⊆ A.vertexSet := fun y hy ↦
    (reachable_left_of_reachable_union hG hA hB hd hxA
      (reachable_of_le hC (hconn x hxC y hy))).2
  refine (GM10.le_iff_of_le hC hAU).2 ⟨hV, fun e he ↦ ?_⟩
  have hCG : C ≤ G := hC.trans (union_le hA hB)
  obtain ⟨w, hw⟩ := (hG e (hCG.edgeSet_subset he)).1
  have hwC : C.Inc e w := (GM10.inc_iff_of_le hCG he).2 hw
  have hwU : (A ∪ B).Inc e w := inc_of_le hC hwC
  exact A.edge_mem_of_inc
    ((union_inc_iff_left hG hA hB hd (hV (C.vertex_mem_of_inc hwC))).1 hwU)

/-- The components of `A ∪ B` are those of `A` and those of `B`. -/
theorem isComponentOf_union_iff {C : Hypergraph α β} :
    IsComponentOf (A ∪ B) C ↔ IsComponentOf A C ∨ IsComponentOf B C := by
  have hAU := le_union_left hA hB
  have hBU := le_union_right hA hB
  constructor
  · intro hC
    obtain ⟨x, hx⟩ := hC.2.1
    have hxU := hC.1.vertexSet_subset hx
    rcases hxU with hxA | hxB
    · have hCA := le_left_of_le_union hG hA hB hd hC.1 hC.2.2.1 hx hxA
      refine Or.inl ⟨hCA, hC.2.1, hC.2.2.1, fun C' hC' hne hconn hle ↦ ?_⟩
      exact hC.2.2.2 C' (hC'.trans hAU) hne hconn hle
    · have hCB := le_left_of_le_union hG hB hA hd.symm (Hypergraph.union_comm A B ▸ hC.1) hC.2.2.1 hx hxB
      refine Or.inr ⟨hCB, hC.2.1, hC.2.2.1, fun C' hC' hne hconn hle ↦ ?_⟩
      exact hC.2.2.2 C' (hC'.trans hBU) hne hconn hle
  · rintro (hC | hC)
    · refine ⟨hC.1.trans hAU, hC.2.1, hC.2.2.1, fun C' hC' hne hconn hle ↦ ?_⟩
      obtain ⟨x, hx⟩ := hC.2.1
      have hC'A := le_left_of_le_union hG hA hB hd hC' hconn (hle.vertexSet_subset hx)
        (hC.1.vertexSet_subset hx)
      exact hC.2.2.2 C' hC'A hne hconn hle
    · refine ⟨hC.1.trans hBU, hC.2.1, hC.2.2.1, fun C' hC' hne hconn hle ↦ ?_⟩
      obtain ⟨x, hx⟩ := hC.2.1
      have hC'B := le_left_of_le_union hG hB hA hd.symm (Hypergraph.union_comm A B ▸ hC') hconn
        (hle.vertexSet_subset hx) (hC.1.vertexSet_subset hx)
      exact hC.2.2.2 C' hC'B hne hconn hle

theorem incidentEdges_union_left {x : α} (hx : x ∈ A.vertexSet) :
    incidentEdges (A ∪ B) x = incidentEdges A x := by
  ext e
  simp only [incidentEdges, mem_ofPred_eq]
  rw [union_inc_iff_left hG hA hB hd hx]
  exact ⟨fun ⟨_, h⟩ ↦ ⟨A.edge_mem_of_inc h, h⟩, fun ⟨he, h⟩ ↦ ⟨Or.inl he, h⟩⟩

theorem vertexDegree_union_left {x : α} (hx : x ∈ A.vertexSet) :
    vertexDegree (A ∪ B) x = vertexDegree A x := by
  unfold vertexDegree
  rw [incidentEdges_union_left hG hA hB hd hx]
  congr 2
  ext e
  simp only [mem_ofPred_eq]
  refine and_congr_right fun he ↦ ?_
  have : (A ∪ B).ends e = A.ends e := by
    ext w
    exact union_inc_iff_of_mem_left hG hA hB hd he.1
  rw [this]

theorem terminals_union : terminals (A ∪ B) = terminals A ∪ terminals B := by
  ext x
  simp only [terminals, IsTerminal, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨hx | hx, hdeg⟩
    · exact Or.inl ⟨hx, (vertexDegree_union_left hG hA hB hd hx) ▸ hdeg⟩
    · have := vertexDegree_union_left hG hB hA hd.symm hx
      rw [Hypergraph.union_comm] at this
      exact Or.inr ⟨hx, this ▸ hdeg⟩
  · rintro (⟨hx, hdeg⟩ | ⟨hx, hdeg⟩)
    · exact ⟨Or.inl hx, (vertexDegree_union_left hG hA hB hd hx).symm ▸ hdeg⟩
    · have := vertexDegree_union_left hG hB hA hd.symm hx
      rw [Hypergraph.union_comm] at this
      exact ⟨Or.inr hx, this.symm ▸ hdeg⟩

/-- The union of two vertex-disjoint linkages is a linkage, and its pattern is the union of their
patterns. -/
theorem isLinkage_union (h₁ : IsLinkage G A) (h₂ : IsLinkage G B) :
    IsLinkage G (A ∪ B) ∧ linkagePattern (A ∪ B) = linkagePattern A ∪ linkagePattern B := by
  have hU := union_le hA hB
  refine ⟨⟨hU, isGraph_of_le hU hG, fun C hC ↦ ?_⟩, ?_⟩
  · rcases (isComponentOf_union_iff hG hA hB hd).1 hC with hC | hC
    · exact h₁.2.2 C hC
    · exact h₂.2.2 C hC
  · ext X
    simp only [linkagePattern, mem_ofPred_eq, mem_union]
    rw [terminals_union hG hA hB hd]
    constructor
    · rintro ⟨C, hC, rfl⟩
      rcases (isComponentOf_union_iff hG hA hB hd).1 hC with hC | hC
      · refine Or.inl ⟨C, hC, ?_⟩
        rw [union_inter_distrib_right]
        have : terminals B ∩ C.vertexSet = ∅ :=
          eq_empty_of_forall_notMem fun y hy ↦ disjoint_left.1 hd
            (hC.1.vertexSet_subset hy.2) hy.1.1
        rw [this, union_empty]
      · refine Or.inr ⟨C, hC, ?_⟩
        rw [union_inter_distrib_right]
        have : terminals A ∩ C.vertexSet = ∅ :=
          eq_empty_of_forall_notMem fun y hy ↦ disjoint_left.1 hd hy.1.1
            (hC.1.vertexSet_subset hy.2)
        rw [this, empty_union]
    · rintro (⟨C, hC, rfl⟩ | ⟨C, hC, rfl⟩)
      · refine ⟨C, (isComponentOf_union_iff hG hA hB hd).2 (Or.inl hC), ?_⟩
        rw [union_inter_distrib_right]
        have : terminals B ∩ C.vertexSet = ∅ :=
          eq_empty_of_forall_notMem fun y hy ↦ disjoint_left.1 hd
            (hC.1.vertexSet_subset hy.2) hy.1.1
        rw [this, union_empty]
      · refine ⟨C, (isComponentOf_union_iff hG hA hB hd).2 (Or.inr hC), ?_⟩
        rw [union_inter_distrib_right]
        have : terminals A ∩ C.vertexSet = ∅ :=
          eq_empty_of_forall_notMem fun y hy ↦ disjoint_left.1 hd hy.1.1
            (hC.1.vertexSet_subset hy.2)
        rw [this, empty_union]

end Union

/-! ## A path is a linkage -/

section PathLinkage

variable {G P : Hypergraph α β}

theorem eq_of_isComponentOf_of_isPathGraph (hP : IsPathGraph P) {C : Hypergraph α β}
    (hC : IsComponentOf P C) : C = P :=
  (hC.2.2.2 P le_rfl hP.2.1 hP.2.2.1 hC.1).symm

theorem isComponentOf_self_of_isPathGraph (hP : IsPathGraph P) : IsComponentOf P P :=
  ⟨le_rfl, hP.2.1, hP.2.2.1, fun _ hC' _ _ hle ↦ le_antisymm hC' hle⟩

/-- A path in `G` is a linkage in `G`, and its pattern has the one block `terminals P`. -/
theorem isLinkage_of_isPathGraph (hP : IsPathGraph P) (hPG : P ≤ G) :
    IsLinkage G P ∧ linkagePattern P = {terminals P} := by
  refine ⟨⟨hPG, hP.1, fun C hC ↦ eq_of_isComponentOf_of_isPathGraph hP hC ▸ hP⟩, ?_⟩
  ext X
  simp only [linkagePattern, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨C, hC, rfl⟩
    rw [eq_of_isComponentOf_of_isPathGraph hP hC]
    exact inter_eq_left.2 fun x hx ↦ hx.1
  · rintro rfl
    exact ⟨P, isComponentOf_self_of_isPathGraph hP, (inter_eq_left.2 fun x hx ↦ hx.1).symm⟩

end PathLinkage

/-! ## Subgraphs given by vertex and edge sets -/

/-- The subgraph of `G` with vertex set `V` and edge set `E`. -/
def spanSub (G : Hypergraph α β) (V : Set α) (E : Set β) (hV : V ⊆ G.vertexSet)
    (hE : ∀ e ∈ E, e ∈ G.edgeSet ∧ G.ends e ⊆ V) : Hypergraph α β where
  vertexSet := V
  edgeSet := E
  Inc e x := e ∈ E ∧ G.Inc e x
  vertex_mem_of_inc := fun e _ h ↦ (hE e h.1).2 h.2
  edge_mem_of_inc := fun _ _ h ↦ h.1
  vertexSet_finite := G.vertexSet_finite.subset hV
  edgeSet_finite := G.edgeSet_finite.subset fun e he ↦ (hE e he).1

theorem spanSub_le {G : Hypergraph α β} {V : Set α} {E : Set β} (hV : V ⊆ G.vertexSet)
    (hE : ∀ e ∈ E, e ∈ G.edgeSet ∧ G.ends e ⊆ V) : spanSub G V E hV hE ≤ G where
  vertexSet_subset := hV
  edgeSet_subset := fun e he ↦ (hE e he).1
  ends_eq e he := by
    ext x
    exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩

/-! ## The new path `a x Q y b` -/

section Exchange

variable {G Q : Hypergraph α β}

/-- An edge of a subgraph `Q` of a loopless graph whose ends are `x ≠ y` has ends `{x, y}`. -/
theorem ends_eq_pair_of_inc {e : β} {x y : α} (h2 : ∀ e ∈ G.edgeSet, (G.ends e).ncard = 2)
    (he : e ∈ G.edgeSet) (hx : G.Inc e x) (hy : G.Inc e y) (hxy : x ≠ y) :
    G.ends e = {x, y} := by
  have hfin : (G.ends e).Finite := G.vertexSet_finite.subset fun _ hw ↦ G.vertex_mem_of_inc hw
  exact eq_pair_of_mem_of_ncard_le_two hfin (h2 e he).le hx hy hxy

variable (hG : G.IsGraph) (h2 : ∀ e ∈ G.edgeSet, (G.ends e).ncard = 2)
  (hinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, G.ends e₁ = G.ends e₂ → e₁ = e₂)
  (hQG : Q ≤ G) {n : ℕ} {w : ℕ → α} (hw : Set.InjOn w (Set.Iic n))
  (hadj : ∀ k ≤ n, ∀ l ≤ n, Q.skeleton.Adj (w k) (w l) ↔ (k + 1 = l ∨ l + 1 = k))
  {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) {a b : α} (hab : a ≠ b)
  (ha : a ∉ w '' Set.Iic n) (hb : b ∉ w '' Set.Iic n) {ea eb : β}
  (hea : ea ∈ G.edgeSet) (heaa : G.Inc ea a) (heai : G.Inc ea (w i))
  (heb : eb ∈ G.edgeSet) (hebb : G.Inc eb b) (hebj : G.Inc eb (w j))
  (hwG : ∀ k ≤ n, w k ∈ G.vertexSet) (haG : a ∈ G.vertexSet) (hbG : b ∈ G.vertexSet)

/-- The vertices of `a x Q y b`. -/
def exVerts (w : ℕ → α) (i j : ℕ) (a b : α) : Set α := {a, b} ∪ w '' Set.Icc i j

/-- The edges of `a x Q y b`. -/
def exEdges (Q : Hypergraph α β) (w : ℕ → α) (i j : ℕ) (ea eb : β) : Set β :=
  {ea, eb} ∪ {e ∈ Q.edgeSet | Q.ends e ⊆ w '' Set.Icc i j}

include hG h2 hQG hij hjn ha hb heaa heai hebb hebj hea heb in
theorem exEdges_spec : ∀ e ∈ exEdges Q w i j ea eb, e ∈ G.edgeSet ∧ G.ends e ⊆ exVerts w i j a b := by
  have hi : i ∈ Set.Icc i j := ⟨le_rfl, hij⟩
  have hj : j ∈ Set.Icc i j := ⟨hij, le_rfl⟩
  have hai : a ≠ w i := fun h ↦ ha ⟨i, hij.trans hjn, h.symm⟩
  have hbj : b ≠ w j := fun h ↦ hb ⟨j, hjn, h.symm⟩
  rintro e ((rfl | rfl) | ⟨heQ, hsub⟩)
  · refine ⟨hea, ?_⟩
    rw [ends_eq_pair_of_inc h2 hea heaa heai hai]
    rintro x (rfl | rfl)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr ⟨i, hi, rfl⟩
  · refine ⟨heb, ?_⟩
    rw [ends_eq_pair_of_inc h2 heb hebb hebj hbj]
    rintro x (rfl | rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨j, hj, rfl⟩
  · refine ⟨hQG.edgeSet_subset heQ, ?_⟩
    rw [hQG.ends_eq e heQ]
    exact hsub.trans subset_union_right

include hjn hwG haG hbG in
theorem exVerts_subset : exVerts w i j a b ⊆ G.vertexSet := by
  rintro x ((rfl | rfl) | ⟨k, hk, rfl⟩)
  · exact haG
  · exact hbG
  · exact hwG k (hk.2.trans hjn)

/-- The sequence `a, w i, …, w j, b`. -/
def exSeq (w : ℕ → α) (i j : ℕ) (a b : α) (p : ℕ) : α :=
  if p = 0 then a else if p ≤ j - i + 1 then w (i + p - 1) else b

include hw hij hjn hab ha hb in
theorem exSeq_injOn : Set.InjOn (exSeq w i j a b) (Set.Iic (j - i + 2)) := by
  intro p hp q hq hpq
  simp only [Set.mem_Iic] at hp hq
  have hwa : ∀ k ≤ n, w k ≠ a := fun k hk h ↦ ha ⟨k, hk, h⟩
  have hwb : ∀ k ≤ n, w k ≠ b := fun k hk h ↦ hb ⟨k, hk, h⟩
  unfold exSeq at hpq
  by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0 <;> simp only [hp0, hq0, ite_true, ite_false] at hpq
  · omega
  · split_ifs at hpq with hq1
    · exact (hwa _ (by omega) hpq.symm).elim
    · exact (hab hpq).elim
  · split_ifs at hpq with hp1
    · exact (hwa _ (by omega) hpq).elim
    · exact (hab hpq.symm).elim
  · split_ifs at hpq with hp1 hq1 hq1
    · have := hw (show i + p - 1 ∈ Set.Iic n by simp; omega)
        (show i + q - 1 ∈ Set.Iic n by simp; omega) hpq
      omega
    · exact (hwb _ (by omega) hpq).elim
    · exact (hwb _ (by omega) hpq.symm).elim
    · omega

theorem exSeq_zero : exSeq w i j a b 0 = a := by simp [exSeq]

theorem exSeq_last : exSeq w i j a b (j - i + 2) = b := by
  have h1 : ¬ (j - i + 2 = 0) := by omega
  have h2 : ¬ (j - i + 2 ≤ j - i + 1) := by omega
  simp only [exSeq, h1, h2, ite_false]

include hij in
theorem exSeq_mid {p : ℕ} (hp1 : 1 ≤ p) (hp : p ≤ j - i + 1) :
    exSeq w i j a b p = w (i + p - 1) := by
  unfold exSeq
  split_ifs <;> first | rfl | omega

include hij in
theorem range_exSeq : exSeq w i j a b '' Set.Iic (j - i + 2) = exVerts w i j a b := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [Set.mem_Iic] at hp
    by_cases hp0 : p = 0
    · subst hp0; rw [exSeq_zero]; exact Or.inl (Or.inl rfl)
    by_cases hpl : p ≤ j - i + 1
    · rw [exSeq_mid hij (by omega) hpl]
      exact Or.inr ⟨i + p - 1, ⟨by omega, by omega⟩, rfl⟩
    · rw [show p = j - i + 2 by omega, exSeq_last]
      exact Or.inl (Or.inr rfl)
  · rintro ((rfl | rfl) | ⟨k, ⟨hk1, hk2⟩, rfl⟩)
    · exact ⟨0, by simp, exSeq_zero⟩
    · exact ⟨j - i + 2, by simp, exSeq_last⟩
    · refine ⟨k - i + 1, by simp; omega, ?_⟩
      rw [exSeq_mid hij (by omega) (by omega)]
      congr 1
      omega

include hij in
theorem exSeq_of_mem {k : ℕ} (hk1 : i ≤ k) (hk2 : k ≤ j) : exSeq w i j a b (k - i + 1) = w k := by
  rw [exSeq_mid hij (by omega) (by omega)]
  congr 1
  omega

/-- The new path `a, w i, …, w j, b` as a subgraph of `G`. -/
def exPath (G Q : Hypergraph α β) (w : ℕ → α) (i j : ℕ) (a b : α) (ea eb : β)
    (hV : exVerts w i j a b ⊆ G.vertexSet)
    (hE : ∀ e ∈ exEdges Q w i j ea eb, e ∈ G.edgeSet ∧ G.ends e ⊆ exVerts w i j a b) :
    Hypergraph α β :=
  spanSub G (exVerts w i j a b) (exEdges Q w i j ea eb) hV hE

include hG h2 hinj hQG hw hadj hij hjn hab ha hb hea heaa heai heb hebb hebj in
/-- Two vertices of the new path are adjacent exactly when they are consecutive in the sequence. -/
theorem exPath_adj (hV : exVerts w i j a b ⊆ G.vertexSet)
    (hE : ∀ e ∈ exEdges Q w i j ea eb, e ∈ G.edgeSet ∧ G.ends e ⊆ exVerts w i j a b)
    {p q : ℕ} (hp : p ≤ j - i + 2) (hq : q ≤ j - i + 2) :
    (exPath G Q w i j a b ea eb hV hE).skeleton.Adj (exSeq w i j a b p) (exSeq w i j a b q) ↔
      (p + 1 = q ∨ q + 1 = p) := by
  have hinjf := exSeq_injOn hw hij hjn hab ha hb
  have idx : ∀ {r s : ℕ}, r ≤ j - i + 2 → s ≤ j - i + 2 →
      exSeq w i j a b r = exSeq w i j a b s → r = s := fun hr hs h ↦
    hinjf (Set.mem_Iic.2 hr) (Set.mem_Iic.2 hs) h
  have f0 : exSeq w i j a b 0 = a := exSeq_zero
  have f1 : exSeq w i j a b 1 = w i := by
    rw [exSeq_mid hij le_rfl (by omega)]; congr 1
  have fl : exSeq w i j a b (j - i + 2) = b := exSeq_last
  have fl' : exSeq w i j a b (j - i + 1) = w j := by
    rw [exSeq_mid hij (by omega) le_rfl]; congr 1; omega
  have hai : a ≠ w i := fun h ↦ ha ⟨i, hij.trans hjn, h.symm⟩
  have hbj : b ≠ w j := fun h ↦ hb ⟨j, hjn, h.symm⟩
  constructor
  · rintro ⟨hne, e, ⟨he, hpe⟩, ⟨-, hqe⟩⟩
    have hpq : p ≠ q := fun h ↦ hne (h ▸ rfl)
    rcases he with (rfl | rfl) | ⟨heQ, hsub⟩
    · have hp' : p = 0 ∨ p = 1 := by
        rcases (show exSeq w i j a b p ∈ ({a, w i} : Set α) from
          (ends_eq_pair_of_inc h2 hea heaa heai hai) ▸ hpe) with h | h
        · exact Or.inl (idx hp (by omega) (h.trans f0.symm))
        · exact Or.inr (idx hp (by omega) (h.trans f1.symm))
      have hq' : q = 0 ∨ q = 1 := by
        rcases (show exSeq w i j a b q ∈ ({a, w i} : Set α) from
          (ends_eq_pair_of_inc h2 hea heaa heai hai) ▸ hqe) with h | h
        · exact Or.inl (idx hq (by omega) (h.trans f0.symm))
        · exact Or.inr (idx hq (by omega) (h.trans f1.symm))
      omega
    · have hp' : p = j - i + 2 ∨ p = j - i + 1 := by
        rcases (show exSeq w i j a b p ∈ ({b, w j} : Set α) from
          (ends_eq_pair_of_inc h2 heb hebb hebj hbj) ▸ hpe) with h | h
        · exact Or.inl (idx hp le_rfl (h.trans fl.symm))
        · exact Or.inr (idx hp (by omega) (h.trans fl'.symm))
      have hq' : q = j - i + 2 ∨ q = j - i + 1 := by
        rcases (show exSeq w i j a b q ∈ ({b, w j} : Set α) from
          (ends_eq_pair_of_inc h2 heb hebb hebj hbj) ▸ hqe) with h | h
        · exact Or.inl (idx hq le_rfl (h.trans fl.symm))
        · exact Or.inr (idx hq (by omega) (h.trans fl'.symm))
      omega
    · have hpQ : Q.Inc e (exSeq w i j a b p) := (GM10.inc_iff_of_le hQG heQ).2 hpe
      have hqQ : Q.Inc e (exSeq w i j a b q) := (GM10.inc_iff_of_le hQG heQ).2 hqe
      obtain ⟨k, ⟨hk1, hk2⟩, hk⟩ := hsub hpQ
      obtain ⟨l, ⟨hl1, hl2⟩, hl⟩ := hsub hqQ
      have hA : Q.skeleton.Adj (w k) (w l) := ⟨hk ▸ hl ▸ hne, e, hk ▸ hpQ, hl ▸ hqQ⟩
      have hkl := (hadj k (hk2.trans hjn) l (hl2.trans hjn)).1 hA
      have hpk : p = k - i + 1 := idx hp (by omega) (hk.symm.trans (exSeq_of_mem hij hk1 hk2).symm)
      have hql : q = l - i + 1 := idx hq (by omega) (hl.symm.trans (exSeq_of_mem hij hl1 hl2).symm)
      omega
  · have key : ∀ {p q : ℕ}, q ≤ j - i + 2 → p + 1 = q →
        (exPath G Q w i j a b ea eb hV hE).skeleton.Adj (exSeq w i j a b p)
          (exSeq w i j a b q) := by
      intro p q hq hpq
      have hne : exSeq w i j a b p ≠ exSeq w i j a b q := fun h ↦ by
        have := idx (by omega) hq h; omega
      by_cases hp0 : p = 0
      · subst hp0; subst hpq
        rw [f0, f1] at hne ⊢
        exact ⟨hne, ea, ⟨Or.inl (Or.inl rfl), heaa⟩, ⟨Or.inl (Or.inl rfl), heai⟩⟩
      by_cases hql : q = j - i + 2
      · subst hql
        have hp' : p = j - i + 1 := by omega
        subst hp'
        rw [fl', fl] at hne ⊢
        exact ⟨hne, eb, ⟨Or.inl (Or.inr rfl), hebj⟩, ⟨Or.inl (Or.inr rfl), hebb⟩⟩
      · rw [exSeq_mid hij (by omega) (by omega), exSeq_mid hij (by omega) (by omega)] at hne ⊢
        have hA := (hadj (i + p - 1) (by omega) (i + q - 1) (by omega)).2 (Or.inl (by omega))
        obtain ⟨-, e, hx, hy⟩ := hA
        have heQ := Q.edge_mem_of_inc hx
        have hxG := (GM10.inc_iff_of_le hQG heQ).1 hx
        have hyG := (GM10.inc_iff_of_le hQG heQ).1 hy
        have hends : Q.ends e = {w (i + p - 1), w (i + q - 1)} := by
          rw [← hQG.ends_eq e heQ]
          exact ends_eq_pair_of_inc h2 (hQG.edgeSet_subset heQ) hxG hyG hne
        have heE : e ∈ exEdges Q w i j ea eb := by
          refine Or.inr ⟨heQ, ?_⟩
          rw [hends]
          rintro x (rfl | rfl)
          · exact ⟨i + p - 1, ⟨by omega, by omega⟩, rfl⟩
          · exact ⟨i + q - 1, ⟨by omega, by omega⟩, rfl⟩
        exact ⟨hne, e, ⟨heE, hxG⟩, ⟨heE, hyG⟩⟩
    rintro (h | h)
    · exact key hq h
    · exact (key hp h).symm

include hG h2 hinj hQG hw hadj hij hjn hab ha hb hea heaa heai heb hebb hebj in
/-- The new path is a path of `G` whose terminals are `a` and `b`. -/
theorem exPath_spec (hV : exVerts w i j a b ⊆ G.vertexSet)
    (hE : ∀ e ∈ exEdges Q w i j ea eb, e ∈ G.edgeSet ∧ G.ends e ⊆ exVerts w i j a b) :
    IsPathGraph (exPath G Q w i j a b ea eb hV hE) ∧
      terminals (exPath G Q w i j a b ea eb hV hE) = {a, b} := by
  set P := exPath G Q w i j a b ea eb hV hE with hPdef
  have hPG : P ≤ G := spanSub_le hV hE
  have hPgraph : P.IsGraph := isGraph_of_le hPG hG
  have hP2 : ∀ e ∈ P.edgeSet, (P.ends e).ncard = 2 := fun e he ↦ by
    rw [← hPG.ends_eq e he]; exact h2 e (hPG.edgeSet_subset he)
  have hPinj : ∀ e₁ ∈ P.edgeSet, ∀ e₂ ∈ P.edgeSet, P.ends e₁ = P.ends e₂ → e₁ = e₂ :=
    fun e₁ he₁ e₂ he₂ h ↦ hinj e₁ (hPG.edgeSet_subset he₁) e₂ (hPG.edgeSet_subset he₂)
      (by rw [hPG.ends_eq e₁ he₁, hPG.ends_eq e₂ he₂, h])
  have hinjf := exSeq_injOn hw hij hjn hab ha hb
  have hidx : IsIndexedPath P a b := by
    refine ⟨j - i + 2, by omega, fun p ↦ exSeq w i j a b p.1, ?_, exSeq_zero, exSeq_last, ?_, ?_⟩
    · intro p q h
      exact Fin.ext (hinjf (Set.mem_Iic.2 (Nat.lt_succ_iff.1 p.2))
        (Set.mem_Iic.2 (Nat.lt_succ_iff.1 q.2)) h)
    · change exVerts w i j a b = _
      rw [← range_exSeq hij]
      ext x
      exact ⟨fun ⟨p, hp, h⟩ ↦ ⟨⟨p, Nat.lt_succ_iff.2 hp⟩, h⟩,
        fun ⟨p, h⟩ ↦ ⟨p.1, Set.mem_Iic.2 (Nat.lt_succ_iff.1 p.2), h⟩⟩
    · intro p q
      exact exPath_adj hG h2 hinj hQG hw hadj hij hjn hab ha hb hea heaa heai heb hebb hebj hV hE
        (Nat.lt_succ_iff.1 p.2) (Nat.lt_succ_iff.1 q.2)
  obtain ⟨hpath, hterm⟩ := isPathGraph_of_isIndexedPath hPgraph hP2 hPinj hidx
  refine ⟨hpath, ?_⟩
  ext x
  simp only [terminals, IsTerminal, mem_ofPred_eq, vertexDegree_eq_ncard_incidentEdges hP2,
    mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hx, hdeg⟩
    exact (hterm x hx).1 hdeg
  · intro h
    have hx : x ∈ P.vertexSet := by
      rcases h with rfl | rfl
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
    exact ⟨hx, (hterm x hx).2 h⟩

end Exchange

/-! ## Indexed paths with natural-number indices -/

section Indexed

variable {G Q : Hypergraph α β}

/-- An indexed path `Q` from `c` to `d`, with the sequence indexed by natural numbers. -/
theorem exists_nat_seq_of_isIndexedPath {c d : α} (h : IsIndexedPath Q c d) :
    ∃ (n : ℕ) (w : ℕ → α), 1 ≤ n ∧ Set.InjOn w (Set.Iic n) ∧ w 0 = c ∧ w n = d ∧
      Q.vertexSet = w '' Set.Iic n ∧
      ∀ k ≤ n, ∀ l ≤ n, Q.skeleton.Adj (w k) (w l) ↔ (k + 1 = l ∨ l + 1 = k) := by
  obtain ⟨n, hn, v, hinj, hv0, hvn, hV, hadj⟩ := h
  let w : ℕ → α := fun k ↦ if hk : k ≤ n then v ⟨k, Nat.lt_succ_iff.2 hk⟩ else c
  have hw : ∀ k (hk : k ≤ n), w k = v ⟨k, Nat.lt_succ_iff.2 hk⟩ := fun k hk ↦ by simp only [w, hk, dite_true]
  refine ⟨n, w, hn, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk l hl h
    rw [hw k hk, hw l hl] at h
    exact congrArg Fin.val (hinj h)
  · rw [hw 0 (Nat.zero_le _)]; exact hv0
  · rw [hw n le_rfl]; exact hvn
  · rw [hV]
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.1, Set.mem_Iic.2 (Nat.lt_succ_iff.1 k.2), hw _ (Nat.lt_succ_iff.1 k.2)⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, (hw k hk).symm⟩
  · intro k hk l hl
    rw [hw k hk, hw l hl, hadj]

variable (hG : G.IsGraph) (h2 : ∀ e ∈ G.edgeSet, (G.ends e).ncard = 2)
  (hinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, G.ends e₁ = G.ends e₂ → e₁ = e₂)
include hG h2 hinj

/-- An indexed path in a simple graph is a path whose terminals are its two ends. -/
theorem isPathGraph_terminals_of_isIndexedPath (hQG : Q ≤ G) {c d : α} (h : IsIndexedPath Q c d) :
    IsPathGraph Q ∧ terminals Q = {c, d} := by
  have hQgraph : Q.IsGraph := isGraph_of_le hQG hG
  have hQ2 : ∀ e ∈ Q.edgeSet, (Q.ends e).ncard = 2 := fun e he ↦ by
    rw [← hQG.ends_eq e he]; exact h2 e (hQG.edgeSet_subset he)
  have hQinj : ∀ e₁ ∈ Q.edgeSet, ∀ e₂ ∈ Q.edgeSet, Q.ends e₁ = Q.ends e₂ → e₁ = e₂ :=
    fun e₁ he₁ e₂ he₂ hh ↦ hinj e₁ (hQG.edgeSet_subset he₁) e₂ (hQG.edgeSet_subset he₂)
      (by rw [hQG.ends_eq e₁ he₁, hQG.ends_eq e₂ he₂, hh])
  obtain ⟨hpath, hterm⟩ := isPathGraph_of_isIndexedPath hQgraph hQ2 hQinj h
  refine ⟨hpath, ?_⟩
  have hcV : c ∈ Q.vertexSet := by
    obtain ⟨n, _, v, _, hv0, _, hV, _⟩ := h
    rw [hV, ← hv0]; exact ⟨0, rfl⟩
  have hdV : d ∈ Q.vertexSet := by
    obtain ⟨n, _, v, _, _, hvn, hV, _⟩ := h
    rw [hV, ← hvn]; exact ⟨_, rfl⟩
  ext x
  simp only [terminals, IsTerminal, mem_ofPred_eq, vertexDegree_eq_ncard_incidentEdges hQ2,
    mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hx, hdeg⟩
    exact (hterm x hx).1 hdeg
  · intro hx'
    have hx : x ∈ Q.vertexSet := by rcases hx' with rfl | rfl <;> assumption
    exact ⟨hx, (hterm x hx).2 hx'⟩

/-- The new path through the inside of `Q` (the path `P'` of the exchange): for ends `a, b`
outside `Q` with edges to inner vertices `w i₁, w j₁` of `Q`, there is a path of `G` with
terminals `a, b`, containing the edge at `a`, whose other vertices are inner vertices of `Q`. -/
theorem exists_exchange_path (hQG : Q ≤ G) {n : ℕ} {w : ℕ → α} (hw : Set.InjOn w (Set.Iic n))
    (hadj : ∀ k ≤ n, ∀ l ≤ n, Q.skeleton.Adj (w k) (w l) ↔ (k + 1 = l ∨ l + 1 = k))
    (hwG : ∀ k ≤ n, w k ∈ G.vertexSet)
    {i₁ j₁ : ℕ} (hi₁ : 1 ≤ i₁) (hi₁n : i₁ + 1 ≤ n) (hj₁ : 1 ≤ j₁) (hj₁n : j₁ + 1 ≤ n)
    {a b : α} (hab : a ≠ b) (ha : a ∉ w '' Set.Iic n) (hb : b ∉ w '' Set.Iic n)
    (haG : a ∈ G.vertexSet) (hbG : b ∈ G.vertexSet) {ea eb : β}
    (hea : ea ∈ G.edgeSet) (heaa : G.Inc ea a) (heai : G.Inc ea (w i₁))
    (heb : eb ∈ G.edgeSet) (hebb : G.Inc eb b) (hebj : G.Inc eb (w j₁)) :
    ∃ P' : Hypergraph α β, P' ≤ G ∧ IsPathGraph P' ∧ terminals P' = {a, b} ∧
      P'.vertexSet ⊆ {a, b} ∪ w '' Set.Icc 1 (n - 1) ∧ ea ∈ P'.edgeSet := by
  rcases le_total i₁ j₁ with hij | hji
  · have hV := exVerts_subset (i := i₁) (j := j₁) (by omega) hwG haG hbG
    have hE := exEdges_spec hG h2 hQG hij (by omega) ha hb hea heaa heai heb hebb hebj
    obtain ⟨hpath, hterm⟩ := exPath_spec hG h2 hinj hQG hw hadj hij (by omega) hab ha hb
      hea heaa heai heb hebb hebj hV hE
    refine ⟨_, spanSub_le hV hE, hpath, hterm, ?_, Or.inl (Or.inl rfl)⟩
    rintro x ((rfl | rfl) | ⟨k, ⟨hk1, hk2⟩, rfl⟩)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨k, ⟨by omega, by omega⟩, rfl⟩
  · have hV := exVerts_subset (i := j₁) (j := i₁) (a := b) (b := a) (by omega) hwG hbG haG
    have hE := exEdges_spec hG h2 hQG hji (by omega) hb ha heb hebb hebj hea heaa heai
    obtain ⟨hpath, hterm⟩ := exPath_spec hG h2 hinj hQG hw hadj hji (by omega) hab.symm hb ha
      heb hebb hebj hea heaa heai hV hE
    refine ⟨_, spanSub_le hV hE, hpath, hterm.trans (pair_comm b a), ?_, Or.inl (Or.inr rfl)⟩
    rintro x ((rfl | rfl) | ⟨k, ⟨hk1, hk2⟩, rfl⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr ⟨k, ⟨by omega, by omega⟩, rfl⟩

end Indexed

/-! ## The exchange contradicts vitality -/

section ExchangeVital

variable {G L P Q : Hypergraph α β}

/-- A linkage is the union of two of its components and of what is left when their vertices are
deleted. -/
theorem eq_union_of_isComponentOf (hLg : L.IsGraph) (hP : IsComponentOf L P)
    (hQ : IsComponentOf L Q) :
    L = (P ∪ Q) ∪ GM10.deleteVertices L (P.vertexSet ∪ Q.vertexSet) := by
  have hR := GM10.deleteVertices_le L (P.vertexSet ∪ Q.vertexSet)
  have hU : (P ∪ Q) ∪ GM10.deleteVertices L (P.vertexSet ∪ Q.vertexSet) ≤ L :=
    GM10.union_le (GM10.union_le hP.1 hQ.1) hR
  refine (GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU le_rfl ?_ ?_).symm
  · ext x
    refine ⟨fun hx ↦ hU.vertexSet_subset hx, fun hx ↦ ?_⟩
    by_cases hxPQ : x ∈ P.vertexSet ∪ Q.vertexSet
    · exact Or.inl hxPQ
    · exact Or.inr ⟨hx, hxPQ⟩
  · ext e
    refine ⟨fun he ↦ hU.edgeSet_subset he, fun he ↦ ?_⟩
    by_cases hinc : ∃ x ∈ P.vertexSet ∪ Q.vertexSet, L.Inc e x
    · obtain ⟨x, hx | hx, hex⟩ := hinc
      · have : e ∈ incidentEdges P x := by
          rw [incidentEdges_component_eq hLg hP hx]; exact ⟨he, hex⟩
        exact Or.inl (Or.inl this.1)
      · have : e ∈ incidentEdges Q x := by
          rw [incidentEdges_component_eq hLg hQ hx]; exact ⟨he, hex⟩
        exact Or.inl (Or.inr this.1)
    · push Not at hinc
      exact Or.inr ⟨he, fun x hx hex ↦ hinc x hx hex⟩

variable (hG : G.IsGraph) (h2 : ∀ e ∈ G.edgeSet, (G.ends e).ncard = 2)
  (hinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, G.ends e₁ = G.ends e₂ → e₁ = e₂)
include hG h2 hinj

/-- **The exchange.** Let `P` (ends `a, b`) and `Q` (ends `c, d`) be distinct components of
a vital linkage `L`. Then there are no edges from `a, b` to inner vertices of `Q` together with
edges from `c, d` to inner vertices of `P`. -/
theorem not_exchange (hL : IsVitalLinkage G L) (hP : IsComponentOf L P) (hQ : IsComponentOf L Q)
    (hPQ : P ≠ Q) {a b c d : α} (hPt : terminals P = {a, b}) (hQt : terminals Q = {c, d})
    {m : ℕ} {wP : ℕ → α} (hwP : Set.InjOn wP (Set.Iic m)) (hP0 : wP 0 = a) (hPm : wP m = b)
    (hVP : P.vertexSet = wP '' Set.Iic m)
    (hadjP : ∀ k ≤ m, ∀ l ≤ m, P.skeleton.Adj (wP k) (wP l) ↔ (k + 1 = l ∨ l + 1 = k))
    {n : ℕ} {wQ : ℕ → α} (hwQ : Set.InjOn wQ (Set.Iic n)) (hQ0 : wQ 0 = c) (hQn : wQ n = d)
    (hVQ : Q.vertexSet = wQ '' Set.Iic n)
    (hadjQ : ∀ k ≤ n, ∀ l ≤ n, Q.skeleton.Adj (wQ k) (wQ l) ↔ (k + 1 = l ∨ l + 1 = k))
    {i₁ j₁ i₂ j₂ : ℕ} (hi₁ : 1 ≤ i₁) (hi₁n : i₁ + 1 ≤ n) (hj₁ : 1 ≤ j₁) (hj₁n : j₁ + 1 ≤ n)
    (hi₂ : 1 ≤ i₂) (hi₂m : i₂ + 1 ≤ m) (hj₂ : 1 ≤ j₂) (hj₂m : j₂ + 1 ≤ m)
    {ea eb ec ed : β}
    (hea : ea ∈ G.edgeSet) (heaa : G.Inc ea a) (heai : G.Inc ea (wQ i₁))
    (heb : eb ∈ G.edgeSet) (hebb : G.Inc eb b) (hebj : G.Inc eb (wQ j₁))
    (hec : ec ∈ G.edgeSet) (hecc : G.Inc ec c) (heci : G.Inc ec (wP i₂))
    (hed : ed ∈ G.edgeSet) (hedd : G.Inc ed d) (hedj : G.Inc ed (wP j₂)) : False := by
  have hLG : L ≤ G := hL.1.1
  have hLg : L.IsGraph := hL.1.2.1
  have hPG : P ≤ G := hP.1.trans hLG
  have hQG : Q ≤ G := hQ.1.trans hLG
  have hdPQ := (disjoint_of_isComponentOf_ne hLg hP hQ hPQ).1
  have hwPV : ∀ k ≤ m, wP k ∈ P.vertexSet := fun k hk ↦ hVP ▸ ⟨k, Set.mem_Iic.2 hk, rfl⟩
  have hwQV : ∀ k ≤ n, wQ k ∈ Q.vertexSet := fun k hk ↦ hVQ ▸ ⟨k, Set.mem_Iic.2 hk, rfl⟩
  have haP : a ∈ P.vertexSet := hP0 ▸ hwPV 0 (Nat.zero_le _)
  have hbP : b ∈ P.vertexSet := hPm ▸ hwPV m le_rfl
  have hcQ : c ∈ Q.vertexSet := hQ0 ▸ hwQV 0 (Nat.zero_le _)
  have hdQ : d ∈ Q.vertexSet := hQn ▸ hwQV n le_rfl
  have hab : a ≠ b := fun h ↦ by
    have := hwP (Set.mem_Iic.2 (Nat.zero_le m)) (Set.mem_Iic.2 le_rfl) (hP0.trans (h.trans hPm.symm))
    omega
  have hcd : c ≠ d := fun h ↦ by
    have := hwQ (Set.mem_Iic.2 (Nat.zero_le n)) (Set.mem_Iic.2 le_rfl) (hQ0.trans (h.trans hQn.symm))
    omega
  have notQ : ∀ x ∈ P.vertexSet, x ∉ wQ '' Set.Iic n := fun x hx hxQ ↦
    disjoint_left.1 hdPQ hx (hVQ ▸ hxQ)
  have notP : ∀ x ∈ Q.vertexSet, x ∉ wP '' Set.Iic m := fun x hx hxP ↦
    disjoint_left.1 hdPQ (hVP ▸ hxP) hx
  obtain ⟨P', hP'G, hP'path, hP't, hP'V, heaP'⟩ := exists_exchange_path hG h2 hinj hQG hwQ hadjQ
    (fun k hk ↦ hQG.vertexSet_subset (hwQV k hk)) hi₁ hi₁n hj₁ hj₁n hab (notQ a haP) (notQ b hbP)
    (hPG.vertexSet_subset haP) (hPG.vertexSet_subset hbP) hea heaa heai heb hebb hebj
  obtain ⟨Q', hQ'G, hQ'path, hQ't, hQ'V, -⟩ := exists_exchange_path hG h2 hinj hPG hwP hadjP
    (fun k hk ↦ hPG.vertexSet_subset (hwPV k hk)) hi₂ hi₂m hj₂ hj₂m hcd (notP c hcQ) (notP d hdQ)
    (hQG.vertexSet_subset hcQ) (hQG.vertexSet_subset hdQ) hec hecc heci hed hedd hedj
  -- The vertices of `P'` are in `P ∪ Q`, and so are those of `Q'`; and `P', Q'` are disjoint.
  have hP'sub : P'.vertexSet ⊆ P.vertexSet ∪ Q.vertexSet := by
    intro x hx
    rcases hP'V hx with (rfl | rfl) | ⟨k, ⟨_, hk⟩, rfl⟩
    · exact Or.inl haP
    · exact Or.inl hbP
    · exact Or.inr (hwQV k (by omega))
  have hQ'sub : Q'.vertexSet ⊆ P.vertexSet ∪ Q.vertexSet := by
    intro x hx
    rcases hQ'V hx with (rfl | rfl) | ⟨k, ⟨_, hk⟩, rfl⟩
    · exact Or.inr hcQ
    · exact Or.inr hdQ
    · exact Or.inl (hwPV k (by omega))
  have hdP'Q' : Disjoint P'.vertexSet Q'.vertexSet := by
    rw [disjoint_left]
    intro x hx₁ hx₂
    rcases hP'V hx₁ with (rfl | rfl) | ⟨k, ⟨hk1, hk2⟩, rfl⟩ <;>
      rcases hQ'V hx₂ with (h | h) | ⟨l, ⟨hl1, hl2⟩, hl⟩
    · exact disjoint_left.1 hdPQ haP (h ▸ hcQ)
    · exact disjoint_left.1 hdPQ haP (h ▸ hdQ)
    · have := hwP (Set.mem_Iic.2 (by omega : l ≤ m)) (Set.mem_Iic.2 (Nat.zero_le m))
        (hl.trans hP0.symm)
      omega
    · exact disjoint_left.1 hdPQ hbP (h ▸ hcQ)
    · exact disjoint_left.1 hdPQ hbP (h ▸ hdQ)
    · have := hwP (Set.mem_Iic.2 (by omega : l ≤ m)) (Set.mem_Iic.2 le_rfl) (hl.trans hPm.symm)
      omega
    · have := hwQ (Set.mem_Iic.2 (by omega : k ≤ n)) (Set.mem_Iic.2 (Nat.zero_le n))
        (h.trans hQ0.symm)
      omega
    · have := hwQ (Set.mem_Iic.2 (by omega : k ≤ n)) (Set.mem_Iic.2 le_rfl) (h.trans hQn.symm)
      omega
    · exact disjoint_left.1 hdPQ (hl ▸ hwPV l (by omega)) (hwQV k (by omega))
  set R := GM10.deleteVertices L (P.vertexSet ∪ Q.vertexSet) with hRdef
  have hRL : R ≤ L := GM10.deleteVertices_le L _
  have hRG : R ≤ G := hRL.trans hLG
  have hRlink : IsLinkage G R := isLinkage_of_le hL.1 hRL hRG
  have hdR : ∀ {X : Set α}, X ⊆ P.vertexSet ∪ Q.vertexSet → Disjoint X R.vertexSet :=
    fun hX ↦ disjoint_left.2 fun x hx hxR ↦ hxR.2 (hX hx)
  -- The new linkage.
  obtain ⟨hP'link, hP'pat⟩ := isLinkage_of_isPathGraph hP'path hP'G
  obtain ⟨hQ'link, hQ'pat⟩ := isLinkage_of_isPathGraph hQ'path hQ'G
  obtain ⟨hUlink, hUpat⟩ := isLinkage_union hG hP'G hQ'G hdP'Q' hP'link hQ'link
  have hUG : P' ∪ Q' ≤ G := GM10.union_le hP'G hQ'G
  obtain ⟨hL'link, hL'pat⟩ := isLinkage_union hG hUG hRG
    (hdR (union_subset hP'sub hQ'sub)) hUlink hRlink
  -- The old linkage.
  obtain ⟨hPlink, hPpat⟩ := isLinkage_of_isPathGraph (hL.1.2.2 P hP) hPG
  obtain ⟨hQlink, hQpat⟩ := isLinkage_of_isPathGraph (hL.1.2.2 Q hQ) hQG
  obtain ⟨hPQlink, hPQpat⟩ := isLinkage_union hG hPG hQG hdPQ hPlink hQlink
  have hPQG : P ∪ Q ≤ G := GM10.union_le hPG hQG
  obtain ⟨-, hLpat⟩ := isLinkage_union hG hPQG hRG (hdR subset_rfl) hPQlink hRlink
  have hLeq := eq_union_of_isComponentOf hLg hP hQ
  have hpat : linkagePattern ((P' ∪ Q') ∪ R) = linkagePattern L := by
    rw [hLeq, hL'pat, hLpat, hUpat, hPQpat, hP'pat, hQ'pat, hPpat, hQpat, hP't, hQ't, hPt, hQt]
  have hEq := hL.2.2 _ hL'link hpat
  -- The edge at `a` is new.
  have heaL : ea ∈ L.edgeSet := hEq ▸ Or.inl (Or.inl heaP')
  have haL : L.Inc ea a := (GM10.inc_iff_of_le hLG heaL).2 heaa
  have heaP : ea ∈ P.edgeSet := by
    have : ea ∈ incidentEdges P a := by
      rw [incidentEdges_component_eq hLg hP haP]; exact ⟨heaL, haL⟩
    exact this.1
  have hxP : P.Inc ea (wQ i₁) := (GM10.inc_iff_of_le hPG heaP).2 heai
  exact disjoint_left.1 hdPQ (P.vertex_mem_of_inc hxP) (hwQV i₁ (by omega))

end ExchangeVital

/-! ## Proof of (1.2) -/

section Main

variable {G L : Hypergraph α β} (hG : G.IsGraph) (h2 : ∀ e ∈ G.edgeSet, (G.ends e).ncard = 2)
  (hinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, G.ends e₁ = G.ends e₂ → e₁ = e₂)
  (hL : IsVitalLinkage G L)
include hG h2 hinj hL

/-- A vertex whose degree in `G` is not its degree in `L` has an edge of `G` not in `L`. -/
theorem exists_extra_edge {t : α}
    (hdeg : vertexDegree G t ≠ vertexDegree L t) :
    ∃ e u, e ∈ G.edgeSet ∧ e ∉ L.edgeSet ∧ G.Inc e t ∧ G.Inc e u ∧ u ≠ t ∧ u ∈ L.vertexSet := by
  have hLG := hL.1.1
  have hL2 : ∀ e ∈ L.edgeSet, (L.ends e).ncard = 2 := fun e he ↦ hL.1.ends_ncard_eq_two he
  rw [vertexDegree_eq_ncard_incidentEdges h2, vertexDegree_eq_ncard_incidentEdges hL2] at hdeg
  have hsub := incidentEdges_subset_of_le hLG t
  have hnot : ¬ incidentEdges G t ⊆ incidentEdges L t := fun h ↦
    hdeg (congrArg ncard (Subset.antisymm h hsub))
  obtain ⟨e, ⟨he, het⟩, heL⟩ := not_subset.1 hnot
  have heL' : e ∉ L.edgeSet := fun h ↦ heL ⟨h, (GM10.inc_iff_of_le hLG h).2 het⟩
  have hfin : (G.ends e).Finite := G.vertexSet_finite.subset fun _ hw ↦ G.vertex_mem_of_inc hw
  obtain ⟨u, hu, hut⟩ : ∃ u ∈ G.ends e, u ≠ t := by
    by_contra! hc
    have : G.ends e ⊆ {t} := fun u hu ↦ hc u hu
    have := (ncard_le_ncard this (finite_singleton t)).trans_eq (ncard_singleton t)
    rw [h2 e he] at this
    omega
  exact ⟨e, u, he, heL', het, hu, hut, hL.2.1 ▸ G.vertex_mem_of_inc hu⟩

/-- The component of a vertex `x` of `L` that has an edge, written as a path `w 0, …, w n` between
its two terminals. -/
theorem component_data {x : α} (hx : x ∈ L.vertexSet)
    (hE : (reachableComponent L x).edgeSet.Nonempty) :
    ∃ (c d : α) (n : ℕ) (w : ℕ → α), terminals L ∩ (reachableComponent L x).vertexSet = {c, d} ∧
      terminals (reachableComponent L x) = {c, d} ∧ IsIndexedPath (reachableComponent L x) c d ∧ 1 ≤ n ∧ Set.InjOn w (Set.Iic n) ∧
      w 0 = c ∧ w n = d ∧ (reachableComponent L x).vertexSet = w '' Set.Iic n ∧
      ∀ k ≤ n, ∀ l ≤ n, (reachableComponent L x).skeleton.Adj (w k) (w l) ↔
        (k + 1 = l ∨ l + 1 = k) := by
  have hLg := hL.1.2.1
  have hC := isComponentOf_reachableComponent hLg hx
  have hpath := hL.1.2.2 _ hC
  obtain ⟨c, -, d, -, -, hidx, -⟩ := exists_isIndexedPath_of_isPathGraph hpath hE
  obtain ⟨-, hterm⟩ := isPathGraph_terminals_of_isIndexedPath hG h2 hinj
    ((reachableComponent_le L x).trans hL.1.1) hidx
  obtain ⟨n, w, hn, hw, hw0, hwn, hV, hadj⟩ := exists_nat_seq_of_isIndexedPath hidx
  exact ⟨c, d, n, w, (hL.1.terminals_inter_component_eq hC).trans hterm, hterm, hidx, hn, hw, hw0,
    hwn, hV, hadj⟩

/-- The component of a vertex of `L` that is not a terminal has an edge. -/
theorem edgeSet_nonempty_of_not_terminal {x : α} (hx : x ∈ L.vertexSet) (hxt : x ∉ terminals L) :
    (reachableComponent L x).edgeSet.Nonempty := by
  by_contra hE
  rw [not_nonempty_iff_eq_empty] at hE
  have hLg := hL.1.2.1
  have hC := isComponentOf_reachableComponent hLg hx
  have hxC := self_mem_reachableComponent hx
  have h0 : (incidentEdges (reachableComponent L x) x) = ∅ :=
    eq_empty_of_forall_notMem fun e he ↦ by
      have h := he.1
      rw [hE] at h
      exact h
  have h0' : vertexDegree L x = 0 := by
    rw [← vertexDegree_component_eq hLg hC hxC]
    unfold vertexDegree
    rw [h0]
    simp
  exact hxt ⟨hx, by omega⟩

/-- **An extra edge at a terminal.** An edge of `G` not in `L` from a terminal `t` does not end on
the component of `t`. -/
theorem not_reachable_of_extra_edge {t u : α} {e : β} (ht : t ∈ terminals L)
    (he : e ∈ G.edgeSet) (heL : e ∉ L.edgeSet) (het : G.Inc e t) (heu : G.Inc e u) (hut : u ≠ t) :
    ¬ L.skeleton.Reachable t u := by
  intro hr
  have hLg := hL.1.2.1
  have htL : t ∈ L.vertexSet := ht.1
  have hC := isComponentOf_reachableComponent hLg htL
  have huL : u ∈ L.vertexSet := hL.2.1 ▸ G.vertex_mem_of_inc heu
  have huC : u ∈ (reachableComponent L t).vertexSet := ⟨huL, hr⟩
  have htC := self_mem_reachableComponent htL
  have hE : (reachableComponent L t).edgeSet.Nonempty := by
    by_contra hE
    rw [not_nonempty_iff_eq_empty] at hE
    obtain ⟨z, hz, -⟩ := isPathGraph_empty_edgeSet (hL.1.2.2 _ hC) hE
    rw [hz] at huC htC
    exact hut (huC.trans htC.symm)
  obtain ⟨c, d, -, -, hterm, -, hidx, -⟩ := component_data hG h2 hinj hL htL hE
  have htcd : t ∈ ({c, d} : Set α) := hterm ▸ ⟨ht, htC⟩
  -- Write the path from `t`.
  obtain ⟨t', hidx'⟩ : ∃ t', IsIndexedPath (reachableComponent L t) t t' := by
    rcases htcd with rfl | rfl
    · exact ⟨d, hidx⟩
    · exact ⟨c, hidx.symm⟩
  obtain ⟨m, hm, v, hvinj, hv0, hvm, hV, hadj⟩ := hidx'
  obtain ⟨k, hk⟩ : u ∈ Set.range v := hV ▸ huC
  have hk0 : k ≠ 0 := fun h ↦ hut (by rw [← hk, h, hv0])
  have hGadj : G.skeleton.Adj (v 0) (v k) := by
    rw [hv0, hk]; exact ⟨hut.symm, e, het, heu⟩
  by_cases hk1 : k.1 = 1
  · -- `u` is the neighbour of `t` on its path: then `e` is parallel to an edge of `L`.
    have hA : (reachableComponent L t).skeleton.Adj (v 0) (v k) := (hadj 0 k).2 (Or.inl (by
      simp [hk1]))
    obtain ⟨-, e', h1, h2'⟩ := hA
    have hCG : reachableComponent L t ≤ G := (reachableComponent_le L t).trans hL.1.1
    have he'C := (reachableComponent L t).edge_mem_of_inc h1
    have h1G := (GM10.inc_iff_of_le hCG he'C).1 h1
    have h2G := (GM10.inc_iff_of_le hCG he'C).1 h2'
    rw [hv0] at h1G
    rw [hk] at h2G
    have := hinj e he e' (hCG.edgeSet_subset he'C)
      ((ends_eq_pair_of_inc h2 he het heu hut.symm).trans
        (ends_eq_pair_of_inc h2 (hCG.edgeSet_subset he'C) h1G h2G hut.symm).symm)
    exact heL (this ▸ (reachableComponent_le L t).edgeSet_subset he'C)
  · exact no_chord_of_isVitalLinkage hG hL hC hm hvinj hv0 hvm hV hadj
      (i₀ := 0) (j₀ := k) (by
        have : k.1 ≠ 0 := fun h ↦ hk0 (Fin.ext h)
        simp only [Fin.val_zero]
        omega) hGadj

omit hG h2 hinj hL in
/-- Two vertices of `L` that are not joined by a path of `L` have disjoint components. -/
theorem disjoint_reachableComponent {x y : α} (h : ¬ L.skeleton.Reachable x y) :
    Disjoint (reachableComponent L x).vertexSet (reachableComponent L y).vertexSet :=
  disjoint_left.2 fun _ hz hz' ↦ h (hz.2.trans hz'.2.symm)

/-- The component of a vertex of `L` that is not a terminal contains exactly two terminals. -/
theorem ncard_terminals_inter {x : α} (hx : x ∈ L.vertexSet) (hxt : x ∉ terminals L) :
    (terminals L ∩ (reachableComponent L x).vertexSet).ncard = 2 := by
  obtain ⟨c, d, n, w, hterm, -, -, hn, hw, hw0, hwn, -⟩ :=
    component_data hG h2 hinj hL hx (edgeSet_nonempty_of_not_terminal hG h2 hinj hL hx hxt)
  have hcd : c ≠ d := fun h ↦ by
    have := hw (Set.mem_Iic.2 (Nat.zero_le n)) (Set.mem_Iic.2 le_rfl) (hw0.trans (h.trans hwn.symm))
    omega
  rw [hterm, ncard_pair hcd]

/-- A `5`-linkage has no three vertices that are not terminals and lie in three different
components: each such component has two terminals, which would give six terminals. -/
theorem not_three_components (h5 : (terminals L).ncard ≤ 5) {x y z : α}
    (hx : x ∈ L.vertexSet) (hxt : x ∉ terminals L) (hy : y ∈ L.vertexSet) (hyt : y ∉ terminals L)
    (hz : z ∈ L.vertexSet) (hzt : z ∉ terminals L) (hxy : ¬ L.skeleton.Reachable x y)
    (hxz : ¬ L.skeleton.Reachable x z) (hyz : ¬ L.skeleton.Reachable y z) : False := by
  have hfin : (terminals L).Finite := L.vertexSet_finite.subset fun _ h ↦ h.1
  set A := terminals L ∩ (reachableComponent L x).vertexSet
  set B := terminals L ∩ (reachableComponent L y).vertexSet
  set C := terminals L ∩ (reachableComponent L z).vertexSet
  have hA : A.Finite := hfin.subset inter_subset_left
  have hB : B.Finite := hfin.subset inter_subset_left
  have hC : C.Finite := hfin.subset inter_subset_left
  have hAB : Disjoint A B := (disjoint_reachableComponent hxy).mono inter_subset_right
    inter_subset_right
  have hABC : Disjoint (A ∪ B) C := disjoint_union_left.2
    ⟨(disjoint_reachableComponent hxz).mono inter_subset_right inter_subset_right,
      (disjoint_reachableComponent hyz).mono inter_subset_right inter_subset_right⟩
  have hsub : A ∪ B ∪ C ⊆ terminals L :=
    union_subset (union_subset inter_subset_left inter_subset_left) inter_subset_left
  have := ncard_le_ncard hsub hfin
  rw [ncard_union_eq hABC (hA.union hB) hC, ncard_union_eq hAB hA hB,
    ncard_terminals_inter hG h2 hinj hL hx hxt, ncard_terminals_inter hG h2 hinj hL hy hyt,
    ncard_terminals_inter hG h2 hinj hL hz hzt] at this
  omega

omit hG h2 hinj hL in
/-- A vertex of a component that is not a terminal is an inner vertex of its path. -/
theorem exists_inner_index {x z : α} {c d : α} {n : ℕ} {w : ℕ → α}
    (hterm : terminals L ∩ (reachableComponent L x).vertexSet = {c, d}) (hw0 : w 0 = c)
    (hwn : w n = d) (hV : (reachableComponent L x).vertexSet = w '' Set.Iic n)
    (hz : z ∈ (reachableComponent L x).vertexSet) (hzt : z ∉ terminals L) :
    ∃ k, 1 ≤ k ∧ k + 1 ≤ n ∧ w k = z := by
  have hc : c ∈ terminals L := (hterm.symm.subset (by simp) : c ∈ terminals L ∩ _).1
  have hd : d ∈ terminals L := (hterm.symm.subset (by simp) : d ∈ terminals L ∩ _).1
  obtain ⟨k, hk, rfl⟩ := hV ▸ hz
  refine ⟨k, ?_, ?_, rfl⟩
  · by_contra h
    obtain rfl : k = 0 := by omega
    exact hzt (hw0 ▸ hc)
  · by_contra h
    obtain rfl : k = n := by have := Set.mem_Iic.1 hk; omega
    exact hzt (hwn ▸ hd)

variable (hno1 : ∀ t₁ ∈ terminals L, ∀ t₂ ∈ terminals L, ¬ L.skeleton.Reachable t₁ t₂ →
    ¬ G.skeleton.Adj t₁ t₂)
  (hno2 : ∀ t ∈ terminals L, vertexDegree G t ≠ vertexDegree L t)
include hno1 hno2

/-- If no two terminals in different components are adjacent and no terminal has the same degree
in `G` and in `L`, then each terminal `t` has an edge of `G` to a vertex `u` that is not a terminal
and lies in another component. -/
theorem exists_inner_neighbour {t : α} (ht : t ∈ terminals L) :
    ∃ u e, u ∈ L.vertexSet ∧ u ∉ terminals L ∧ ¬ L.skeleton.Reachable t u ∧ e ∈ G.edgeSet ∧
      G.Inc e t ∧ G.Inc e u := by
  obtain ⟨e, u, he, heL, het, heu, hut, huL⟩ :=
    exists_extra_edge hG h2 hinj hL (hno2 t ht)
  have hr := not_reachable_of_extra_edge hG h2 hinj hL ht he heL het heu hut
  exact ⟨u, e, huL, fun hu ↦ hno1 t ht u hu hr ⟨hut.symm, e, het, heu⟩, hr, he, het, heu⟩

/-- **The main step, for `5`-linkages.** If no two terminals in different components are
adjacent and no terminal has the same degree in `G` and in `L`, then `G` is null. -/
theorem vertexSet_eq_empty_of_vital (h5 : (terminals L).ncard ≤ 5) : G.vertexSet = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
  have hxL : x ∈ L.vertexSet := hL.2.1 ▸ hx
  have hLg := hL.1.2.1
  -- Some vertex `y` of `L` is not a terminal.
  obtain ⟨y, hyL, hyt⟩ : ∃ y ∈ L.vertexSet, y ∉ terminals L := by
    by_cases hxt : x ∈ terminals L
    · obtain ⟨u, -, huL, hut, -⟩ := exists_inner_neighbour hG h2 hinj hL hno1 hno2 hxt
      exact ⟨u, huL, hut⟩
    · exact ⟨x, hxL, hxt⟩
  -- The path `P` through `y`, with ends `a` and `b`.
  have hPC := isComponentOf_reachableComponent hLg hyL
  obtain ⟨a, b, m, wP, htermP, htP, -, -, hwP, hP0, hPm, hVP, hadjP⟩ :=
    component_data hG h2 hinj hL hyL (edgeSet_nonempty_of_not_terminal hG h2 hinj hL hyL hyt)
  have haP : a ∈ terminals L ∩ (reachableComponent L y).vertexSet := htermP.symm.subset (by simp)
  have hbP : b ∈ terminals L ∩ (reachableComponent L y).vertexSet := htermP.symm.subset (by simp)
  -- The extra edges at `a` and `b` end at inner vertices `x₁` and `y₁`.
  obtain ⟨x₁, ea, hx₁L, hx₁t, hax₁, hea, heaa, heax₁⟩ :=
    exists_inner_neighbour hG h2 hinj hL hno1 hno2 haP.1
  obtain ⟨y₁, eb, hy₁L, hy₁t, hby₁, heb, hebb, heby₁⟩ :=
    exists_inner_neighbour hG h2 hinj hL hno1 hno2 hbP.1
  have hyx₁ : ¬ L.skeleton.Reachable y x₁ := fun h ↦ hax₁ (haP.2.2.symm.trans h)
  have hyy₁ : ¬ L.skeleton.Reachable y y₁ := fun h ↦ hby₁ (hbP.2.2.symm.trans h)
  -- By counting, `x₁` and `y₁` lie on one path `Q`, with ends `c` and `d`.
  have hx₁y₁ : L.skeleton.Reachable x₁ y₁ := by
    by_contra h
    exact not_three_components hG h2 hinj hL h5 hyL hyt hx₁L hx₁t hy₁L hy₁t hyx₁ hyy₁ h
  have hQC := isComponentOf_reachableComponent hLg hx₁L
  obtain ⟨c, d, n, wQ, htermQ, htQ, -, -, hwQ, hQ0, hQn, hVQ, hadjQ⟩ :=
    component_data hG h2 hinj hL hx₁L (edgeSet_nonempty_of_not_terminal hG h2 hinj hL hx₁L hx₁t)
  have hcQ : c ∈ terminals L ∩ (reachableComponent L x₁).vertexSet := htermQ.symm.subset (by simp)
  have hdQ : d ∈ terminals L ∩ (reachableComponent L x₁).vertexSet := htermQ.symm.subset (by simp)
  -- The extra edges at `c` and `d` end at inner vertices `u₂` and `v₂`, which by counting lie on `P`.
  obtain ⟨u₂, ec, hu₂L, hu₂t, hcu₂, hec, hecc, hecu₂⟩ :=
    exists_inner_neighbour hG h2 hinj hL hno1 hno2 hcQ.1
  obtain ⟨v₂, ed, hv₂L, hv₂t, hdv₂, hed, hedd, hedv₂⟩ :=
    exists_inner_neighbour hG h2 hinj hL hno1 hno2 hdQ.1
  have hyu₂ : L.skeleton.Reachable y u₂ := by
    by_contra h
    exact not_three_components hG h2 hinj hL h5 hyL hyt hx₁L hx₁t hu₂L hu₂t hyx₁ h
      fun h' ↦ hcu₂ (hcQ.2.2.symm.trans h')
  have hyv₂ : L.skeleton.Reachable y v₂ := by
    by_contra h
    exact not_three_components hG h2 hinj hL h5 hyL hyt hx₁L hx₁t hv₂L hv₂t hyx₁ h
      fun h' ↦ hdv₂ (hdQ.2.2.symm.trans h')
  -- The positions of the four inner vertices on their paths.
  obtain ⟨i₁, hi₁, hi₁n, rfl⟩ := exists_inner_index (L := L) htermQ hQ0 hQn hVQ
    (self_mem_reachableComponent hx₁L) hx₁t
  obtain ⟨j₁, hj₁, hj₁n, rfl⟩ := exists_inner_index (L := L) htermQ hQ0 hQn hVQ ⟨hy₁L, hx₁y₁⟩ hy₁t
  obtain ⟨i₂, hi₂, hi₂m, rfl⟩ := exists_inner_index (L := L) htermP hP0 hPm hVP ⟨hu₂L, hyu₂⟩ hu₂t
  obtain ⟨j₂, hj₂, hj₂m, rfl⟩ := exists_inner_index (L := L) htermP hP0 hPm hVP ⟨hv₂L, hyv₂⟩ hv₂t
  have hPQ : reachableComponent L y ≠ reachableComponent L (wQ i₁) := fun h ↦
    hyx₁ (h ▸ self_mem_reachableComponent hx₁L : wQ i₁ ∈ (reachableComponent L y).vertexSet).2
  exact not_exchange hG h2 hinj hL hPC hQC hPQ htP htQ hwP hP0 hPm hVP hadjP hwQ hQ0 hQn hVQ
    hadjQ hi₁ hi₁n hj₁ hj₁n hi₂ hi₂m hj₂ hj₂m hea heaa heax₁ heb hebb heby₁ hec hecc hecu₂ hed
    hedd hedv₂

end Main

/-- **Graph Minors XXI, (1.2).** Let `L` be a vital `5`-linkage in a simple graph `G`: a graph with
no loops (each edge has two ends) and no parallel edges. Then some two terminals in different
components of `L` are adjacent in `G`, or some terminal has the same degree in `G` and in `L`, or
`G` is null. If the first two outcomes fail, then the
ends of a path of `L` send edges into the inside of a second path, and its ends send edges into
the inside of the first path, and then the exchange (`not_exchange`) contradicts vitality. -/
theorem theorem_1_2_proof {G L : Hypergraph α β} (hG : G.IsGraph)
    (h2 : ∀ e ∈ G.edgeSet, (G.ends e).ncard = 2)
    (hinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, G.ends e₁ = G.ends e₂ → e₁ = e₂)
    (hL : IsVitalPLinkage G L 5) :
    (∃ t₁ ∈ terminals L, ∃ t₂ ∈ terminals L,
      (¬ ∃ C, IsComponentOf L C ∧ t₁ ∈ C.vertexSet ∧ t₂ ∈ C.vertexSet) ∧ G.skeleton.Adj t₁ t₂) ∨
    (∃ t ∈ terminals L, vertexDegree G t = vertexDegree L t) ∨ G.vertexSet = ∅ := by
  by_cases h1 : ∃ t₁ ∈ terminals L, ∃ t₂ ∈ terminals L,
      (¬ ∃ C, IsComponentOf L C ∧ t₁ ∈ C.vertexSet ∧ t₂ ∈ C.vertexSet) ∧ G.skeleton.Adj t₁ t₂
  · exact Or.inl h1
  by_cases h2' : ∃ t ∈ terminals L, vertexDegree G t = vertexDegree L t
  · exact Or.inr (Or.inl h2')
  refine Or.inr (Or.inr (vertexSet_eq_empty_of_vital hG h2 hinj hL.1 ?_ ?_ hL.2.2))
  · intro t₁ ht₁ t₂ ht₂ hr hadj
    refine h1 ⟨t₁, ht₁, t₂, ht₂, ?_, hadj⟩
    rintro ⟨C, hC, h₁, h₂⟩
    rw [eq_reachableComponent_of_isComponentOf hL.1.1.2.1 hC h₁] at h₂
    exact hr h₂.2
  · exact fun t ht h ↦ h2' ⟨t, ht, h⟩

end GraphMinor.GM21
