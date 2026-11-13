module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import GraphMinor.HP25.Defs
public import GraphMinor.HP25.Web
public import GraphMinor.HP25.EdgeFaces
public import GraphMinor.HP25.Alternate
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Prop23
import GraphMinor.HP25.Prop34Tools
import GraphMinor.HP25.Lemma33

/-!
# Cycle bridges, attachment lists, and candidate endpoint pairs (Sections 5 and 5.1)

This file formalizes the definitions and basic properties of Section 5 and Section 5.1 of the
crossing-extractor note (`docs/crossing/crossing_extractor.tex`):

* `Bridge V`, `IsBridge G S D B`: a `D`-bridge of `G` on `S`, which is either a connected component
  of `G - V(D)` together with its incident edges to `D`, or a single chord with both endpoints on
  `D`, excluding cycle edges.
* `IsBridgeAttachment G D B d`: `d ∈ D` is an attachment of the bridge `B`.
* `UsesBridge G D P B` and `UsesDistinctBridges G S D Q R`: when a `D`-path uses a bridge `B`, and
  when two crossing paths use distinct `D`-bridges. We prove that every `D`-path in a crossing uses
  a unique `D`-bridge, that paths using distinct bridges with distinct endpoints are vertex-disjoint,
  and that a crossing uses distinct bridges if and only if no walk in `G - V(D)` connects an inner
  vertex of `Q` to an inner vertex of `R`.
* `attachmentCandidates t` and `candidatesOfIndices γ t`: the cyclic distance-1 and distance-2
  candidate pairs `{t_i, t_{i+1}}` and `{t_i, t_{i+2}}` modulo `h` (omitting loops), and the bound
  `length_attachmentCandidates_le` ("There are at most twice as many candidates as attachments.").
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph Set GraphMinor.HP25

variable {V : Type*}

/-! ### 1. Off-cycle subgraph and off-cycle components -/

/-- The subgraph of `G` induced by the vertices outside the cycle `D` ($K - V(D)$). -/
def offCycleGraph (G : SimpleGraph V) (D : List V) : SimpleGraph V :=
  HP25.restrict G {v | v ∉ D}

theorem offCycleGraph_adj {G : SimpleGraph V} {D : List V} {u v : V} :
    (offCycleGraph G D).Adj u v ↔ G.Adj u v ∧ u ∉ D ∧ v ∉ D :=
  Iff.rfl

theorem offCycleGraph_le (G : SimpleGraph V) (D : List V) : offCycleGraph G D ≤ G :=
  fun _ _ h => h.1

/-- The connected component of `v` in `G - V(D)`. -/
def offCycleComp (G : SimpleGraph V) (D : List V) (v : V) : Set V :=
  {w | w ∉ D ∧ (offCycleGraph G D).Reachable v w}

theorem mem_offCycleComp_iff {G : SimpleGraph V} {D : List V} {v w : V} :
    w ∈ offCycleComp G D v ↔ w ∉ D ∧ (offCycleGraph G D).Reachable v w :=
  Iff.rfl

theorem mem_offCycleComp_self {G : SimpleGraph V} {D : List V} {v : V} (hv : v ∉ D) :
    v ∈ offCycleComp G D v :=
  ⟨hv, Reachable.refl v⟩

theorem not_mem_of_mem_offCycleComp {G : SimpleGraph V} {D : List V} {v w : V}
    (hw : w ∈ offCycleComp G D v) : w ∉ D :=
  hw.1

theorem offCycleComp_closed_adj {G : SimpleGraph V} {D : List V} {v u w : V}
    (hu : u ∈ offCycleComp G D v) (hw : w ∉ D) (hadj : G.Adj u w) :
    w ∈ offCycleComp G D v :=
  ⟨hw, hu.2.trans ( Adj.reachable ⟨hadj, hu.1, hw⟩ )⟩

theorem offCycleComp_eq_of_mem {G : SimpleGraph V} {D : List V} {v w : V}
    (hw : w ∈ offCycleComp G D v) :
    offCycleComp G D w = offCycleComp G D v := by
  ext z
  simp only [mem_offCycleComp_iff]
  exact ⟨fun ⟨hz, hwz⟩ => ⟨hz, hw.2.trans hwz⟩,
    fun ⟨hz, hvz⟩ => ⟨hz, hw.2.symm.trans hvz⟩⟩

theorem offCycleComp_eq_or_disjoint {G : SimpleGraph V} {D : List V} {u v : V} :
    offCycleComp G D u = offCycleComp G D v ∨
      Disjoint (offCycleComp G D u) (offCycleComp G D v) := by
  by_cases h : (offCycleComp G D u ∩ offCycleComp G D v).Nonempty
  · left
    obtain ⟨w, hwu, hwv⟩ := h
    rw [← offCycleComp_eq_of_mem hwu, ← offCycleComp_eq_of_mem hwv]
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp h

private theorem walk_end_mem_supp {G : SimpleGraph V} {S : Set V} (hG : IsSupportedOn G S)
    {u v : V} (p : G.Walk u v) (hu : u ∈ S) : v ∈ S := by
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hG hadj.symm)

theorem offCycleComp_subset_supp {G : SimpleGraph V} {S : Set V} {D : List V} {v : V}
    (hG : IsSupportedOn G S) (hvS : v ∈ S) :
    offCycleComp G D v ⊆ S := by
  intro w ⟨_, hreach⟩
  obtain ⟨p⟩ := hreach
  exact walk_end_mem_supp hG (p.mapLe (offCycleGraph_le G D)) hvS

/-- `A` is a connected component of `K - V(D)` for the graph `G` supported on `S`. -/
def IsOffCycleComp (G : SimpleGraph V) (S : Set V) (D : List V) (A : Set V) : Prop :=
  ∃ v ∈ S, v ∉ D ∧ A = offCycleComp G D v

/-! ### 2. `D`-bridges and their attachments (Section 5) -/

/-- A `D`-bridge (Section 5 of the note). "A *$D$-bridge* is either a component of $K-V(D)$,
together with its edges to $D$, or a single *chord*: an edge that is not an edge of $D$ and has both
ends on $D$." -/
inductive Bridge (V : Type*)
  | comp (A : Set V)
  | chord (e : Sym2 V)

/-- `e` is a chord of the cycle `D` in `G`: an edge of `G` with both endpoints on `D` that is not a
cycle edge of `D`. In the words of Section 5, a *chord* is "an edge that is not an edge of $D$ and
has both ends on $D$." -/
def IsChordBridge (G : SimpleGraph V) (D : List V) (e : Sym2 V) : Prop :=
  ∃ u v : V, e = s(u, v) ∧ u ∈ D ∧ v ∈ D ∧ G.Adj u v ∧ ¬ PlaneEmbedding.IsCycleEdge D u v

/-- `B` is a valid `D`-bridge of `G` on vertex set `S` (Section 5 of the note):
a `D`-bridge is either "a component of $K-V(D)$, together with its edges to $D$", or "a single
*chord*: an edge that is not an edge of $D$ and has both ends on $D$." -/
def IsBridge (G : SimpleGraph V) (S : Set V) (D : List V) : Bridge V → Prop
  | .comp A => IsOffCycleComp G S D A
  | .chord e => IsChordBridge G D e

/-- `d` is an attachment on `D` of the bridge `B`: for a component bridge `A`, a vertex of `D`
adjacent in `G` to a vertex of `A`; for a chord bridge `e`, an endpoint of `e` on `D`. -/
def IsBridgeAttachment (G : SimpleGraph V) (D : List V) : Bridge V → V → Prop
  | .comp A, d => d ∈ D ∧ ∃ a ∈ A, G.Adj a d
  | .chord e, d => d ∈ D ∧ d ∈ e

/-- The subgraph of `G` corresponding to a bridge `B` with selected endpoints `p, q`: for a
component bridge `A`, the induced subgraph `G[A ∪ {p, q}]` without `D`-edges (`p` to `q`); for a
chord bridge `e`, the single edge `e`. -/
def UsesBridge (G : SimpleGraph V) {u v : V} (P : G.Walk u v) : Bridge V → Prop
  | .comp A => (∃ x ∈ P.support, x ≠ u ∧ x ≠ v) ∧ ∀ x ∈ P.support, x ≠ u → x ≠ v → x ∈ A
  | .chord e => (∀ x ∈ P.support, x = u ∨ x = v) ∧ e = s(u, v)

/-- Two walks `Q` and `R` use distinct `D`-bridges of `G` on `S` (Section 5 of the note:
"Return a crossing whose two paths use distinct $D$-bridges, or correctly report that no such
crossing exists."). -/
def UsesDistinctBridges (G : SimpleGraph V) (S : Set V) (D : List V)
    {u₁ v₁ u₂ v₂ : V} (Q : G.Walk u₁ v₁) (R : G.Walk u₂ v₂) : Prop :=
  ∃ B₁ B₂ : Bridge V, IsBridge G S D B₁ ∧ IsBridge G S D B₂ ∧ B₁ ≠ B₂ ∧
    UsesBridge G Q B₁ ∧ UsesBridge G R B₂

/-! ### 3. Properties of bridges and `D`-paths -/

/-- "Different component bridges have disjoint sets of inner vertices" (Section 5). -/
theorem IsBridge.disjoint_of_ne {G : SimpleGraph V} {S : Set V} {D : List V} {A₁ A₂ : Set V}
    (h₁ : IsBridge G S D (.comp A₁)) (h₂ : IsBridge G S D (.comp A₂))
    (hne : (Bridge.comp A₁ : Bridge V) ≠ Bridge.comp A₂) :
    Disjoint A₁ A₂ := by
  obtain ⟨v₁, _, _, rfl⟩ := h₁
  obtain ⟨v₂, _, _, rfl⟩ := h₂
  rcases offCycleComp_eq_or_disjoint (G := G) (D := D) (u := v₁) (v := v₂) with h | h
  · exact absurd (congrArg Bridge.comp h) hne
  · exact h

/-- A walk uses at most one `D`-bridge. -/
theorem UsesBridge.unique {G : SimpleGraph V} {S : Set V} {D : List V} {u v : V}
    {P : G.Walk u v} {B₁ B₂ : Bridge V}
    (hB₁ : IsBridge G S D B₁) (hB₂ : IsBridge G S D B₂)
    (h₁ : UsesBridge G P B₁) (h₂ : UsesBridge G P B₂) : B₁ = B₂ := by
  cases B₁ with
  | comp A₁ =>
    cases B₂ with
    | comp A₂ =>
      obtain ⟨⟨x, hx, hxu, hxv⟩, hall₁⟩ := h₁
      obtain ⟨_, hall₂⟩ := h₂
      have hx₁ : x ∈ A₁ := hall₁ x hx hxu hxv
      have hx₂ : x ∈ A₂ := hall₂ x hx hxu hxv
      by_contra hne
      exact Set.disjoint_left.mp (hB₁.disjoint_of_ne hB₂ hne) hx₁ hx₂
    | chord e₂ =>
      obtain ⟨⟨x, hx, hxu, hxv⟩, _⟩ := h₁
      rcases h₂.1 x hx with rfl | rfl
      · exact absurd rfl hxu
      · exact absurd rfl hxv
  | chord e₁ =>
    cases B₂ with
    | comp A₂ =>
      obtain ⟨⟨x, hx, hxu, hxv⟩, _⟩ := h₂
      rcases h₁.1 x hx with rfl | rfl
      · exact absurd rfl hxu
      · exact absurd rfl hxv
    | chord e₂ =>
      rw [h₁.2, h₂.2]

/-- Two walks using distinct bridges and having disjoint endpoint sets are vertex-disjoint:
as in Section 5.2, "their inner vertices belong to different bridges, and the four selected
endpoints are distinct." -/
theorem disjoint_support_of_usesDistinctBridges {G : SimpleGraph V} {S : Set V} {D : List V}
    {u₁ v₁ u₂ v₂ : V} {Q : G.Walk u₁ v₁} {R : G.Walk u₂ v₂}
    {B₁ B₂ : Bridge V} (hB₁ : IsBridge G S D B₁) (hB₂ : IsBridge G S D B₂) (hne : B₁ ≠ B₂)
    (hQ : UsesBridge G Q B₁) (hR : UsesBridge G R B₂)
    (hu₁D : u₁ ∈ D) (hv₁D : v₁ ∈ D) (hu₂D : u₂ ∈ D) (hv₂D : v₂ ∈ D)
    (hends : ∀ x, (x = u₁ ∨ x = v₁) → (x = u₂ ∨ x = v₂) → False) :
    Q.support.Disjoint R.support := by
  intro x hxQ hxR
  by_cases h1 : x = u₁ ∨ x = v₁
  · by_cases h2 : x = u₂ ∨ x = v₂
    · exact hends x h1 h2
    · push Not at h2
      cases B₂ with
      | chord e₂ => exact (hR.1 x hxR).elim h2.1 h2.2
      | comp A₂ =>
        obtain ⟨v₂₀, _, _, rfl⟩ := hB₂
        have hxA₂ := hR.2 x hxR h2.1 h2.2
        rcases h1 with rfl | rfl
        · exact hxA₂.1 hu₁D
        · exact hxA₂.1 hv₁D
  · push Not at h1
    cases B₁ with
    | chord e₁ => exact (hQ.1 x hxQ).elim h1.1 h1.2
    | comp A₁ =>
      have hxA₁ := hQ.2 x hxQ h1.1 h1.2
      by_cases h2 : x = u₂ ∨ x = v₂
      · obtain ⟨v₁₀, _, _, rfl⟩ := hB₁
        rcases h2 with rfl | rfl
        · exact hxA₁.1 hu₂D
        · exact hxA₁.1 hv₂D
      · push Not at h2
        cases B₂ with
        | chord e₂ => exact (hR.1 x hxR).elim h2.1 h2.2
        | comp A₂ =>
          have hxA₂ := hR.2 x hxR h2.1 h2.2
          exact Set.disjoint_left.mp (hB₁.disjoint_of_ne hB₂ hne) hxA₁ hxA₂

private theorem walk_init_of_not_nil {G : SimpleGraph V} {a v : V} (q : G.Walk a v)
    (hnil : ¬ q.Nil) :
    ∃ (c : V) (q₀ : G.Walk a c), G.Adj c v ∧ q.support = q₀.support ++ [v] := by
  induction q with
  | nil => exact absurd Walk.Nil.nil hnil
  | @cons p' m _ h w' ih =>
    cases w' with
    | nil => exact ⟨p', .nil, h, rfl⟩
    | cons h' w'' =>
      obtain ⟨c, q₀, hadj, hsupp⟩ := ih (by simp)
      refine ⟨c, Walk.cons h q₀, hadj, ?_⟩
      simp only [Walk.support_cons, hsupp, List.cons_append]

private theorem walk_reach_offCycle {G : SimpleGraph V} {D : List V} {a c : V} (w : G.Walk a c)
    (hw : ∀ z ∈ w.support, z ∉ D) :
    ∀ x ∈ w.support, x ∈ offCycleComp G D a := by
  induction w with
  | nil =>
    intro x hx
    simp only [Walk.support_nil, List.mem_singleton] at hx
    subst hx
    exact mem_offCycleComp_self (hw _ (by simp))
  | @cons p' m _ h w' ih =>
    have hp' : p' ∉ D := hw p' (by simp)
    have hm : m ∉ D := hw m (by simp)
    have ih' := ih (fun z hz => hw z (List.mem_cons_of_mem _ hz))
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact mem_offCycleComp_self hp'
    · have hmx := ih' x hx
      have hadj_pm : (offCycleGraph G D).Adj p' m := ⟨h, hp', hm⟩
      exact ⟨hmx.1, hadj_pm.reachable.trans hmx.2⟩

/-- Every inner vertex of a `D`-path `P : G.Walk u v` is reachable in `G - V(D)` from its first
inner vertex, and `u, v` are adjacent to inner vertices of `P`. -/
private theorem isTPath_inner_connected {G : SimpleGraph V} {S : Set V} {D : List V} {u v : V}
    {P : G.Walk u v} (hG : IsSupportedOn G S) (hP : IsTPath G D P)
    {w₀ : V} (hw₀ : w₀ ∈ P.support) (hw₀u : w₀ ≠ u) (hw₀v : w₀ ≠ v) :
    w₀ ∈ S ∧ w₀ ∉ D ∧
      (∀ x ∈ P.support, x ≠ u → x ≠ v → x ∈ offCycleComp G D w₀) ∧
      (∃ a ∈ offCycleComp G D w₀, G.Adj a u) ∧
      (∃ b ∈ offCycleComp G D w₀, G.Adj b v) := by
  obtain ⟨hpath, huD, hvD, hinner⟩ := hP
  have hnd := hpath.support_nodup
  cases P with
  | nil => exact absurd (List.mem_singleton.mp hw₀) hw₀u
  | @cons _ a _ hadj₁ rest =>
    cases rest with
    | nil =>
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hw₀
      rcases hw₀ with rfl | rfl
      · exact absurd rfl hw₀u
      · exact absurd rfl hw₀v
    | @cons _ b _ hadj₂ rest' =>
      obtain ⟨c, q₀, hadj_cv, hq_supp⟩ :=
        walk_init_of_not_nil (Walk.cons hadj₂ rest') (by simp)
      have hP_supp : (Walk.cons hadj₁ (Walk.cons hadj₂ rest')).support =
          u :: (q₀.support ++ [v]) := by
        simp only [Walk.support_cons, ← hq_supp]
      rw [hP_supp, List.nodup_cons, List.mem_append, List.mem_singleton, not_or,
        List.nodup_append] at hnd
      have hq₀_off : ∀ z ∈ q₀.support, z ∉ D := by
        intro z hz
        have hzu : z ≠ u := by intro h; subst h; exact hnd.1.1 hz
        have hzv : z ≠ v := by intro h; subst h; exact hnd.2.2.2 z hz z (by simp) rfl
        have hzP : z ∈ (Walk.cons hadj₁ (Walk.cons hadj₂ rest')).support := by
          rw [hP_supp]
          exact List.mem_cons_of_mem _ (List.mem_append_left _ hz)
        exact (hinner z hzP hzu hzv).1
      have hreach_q₀ := walk_reach_offCycle q₀ hq₀_off
      have haS : a ∈ S := hG hadj₁.symm
      have haD : a ∉ D := hq₀_off a q₀.start_mem_support
      have hw₀_q₀ : w₀ ∈ q₀.support := by
        rw [hP_supp, List.mem_cons, List.mem_append, List.mem_singleton] at hw₀
        exact (hw₀.resolve_left hw₀u).resolve_right hw₀v
      have hw₀_comp : w₀ ∈ offCycleComp G D a := hreach_q₀ w₀ hw₀_q₀
      have hcomp_eq : offCycleComp G D w₀ = offCycleComp G D a :=
        offCycleComp_eq_of_mem hw₀_comp
      refine ⟨offCycleComp_subset_supp hG haS hw₀_comp, hw₀_comp.1, ?_, ?_, ?_⟩
      · intro x hx hxu hxv
        rw [hcomp_eq]
        rw [hP_supp, List.mem_cons, List.mem_append, List.mem_singleton] at hx
        exact hreach_q₀ x ((hx.resolve_left hxu).resolve_right hxv)
      · rw [hcomp_eq]
        exact ⟨a, mem_offCycleComp_self haD, hadj₁.symm⟩
      · rw [hcomp_eq]
        exact ⟨c, hreach_q₀ c q₀.end_mem_support, hadj_cv⟩

/-- Every `D`-path `P : G.Walk u v` between distinct non-consecutive cycle vertices uses a `D`-bridge
`B`, and `u, v` are attachments of `B`. -/
theorem IsTPath.exists_bridge {G : SimpleGraph V} {S : Set V} {D : List V} {u v : V}
    {P : G.Walk u v} (hG : IsSupportedOn G S) (hP : IsTPath G D P) (huv : u ≠ v)
    (hnotCyc : ¬ PlaneEmbedding.IsCycleEdge D u v) :
    ∃ B : Bridge V, IsBridge G S D B ∧ UsesBridge G P B ∧
      IsBridgeAttachment G D B u ∧ IsBridgeAttachment G D B v := by
  by_cases hinner : ∃ x ∈ P.support, x ≠ u ∧ x ≠ v
  · obtain ⟨w₀, hw₀, hw₀u, hw₀v⟩ := hinner
    obtain ⟨hw₀S, hw₀D, hall, ⟨a, ha, hau⟩, ⟨b, hb, hbv⟩⟩ :=
      isTPath_inner_connected hG hP hw₀ hw₀u hw₀v
    refine ⟨.comp (offCycleComp G D w₀), ⟨w₀, hw₀S, hw₀D, rfl⟩,
      ⟨⟨w₀, hw₀, hw₀u, hw₀v⟩, hall⟩, ⟨hP.2.1, a, ha, hau⟩, ⟨hP.2.2.1, b, hb, hbv⟩⟩
  · push Not at hinner
    have hadj : G.Adj u v := by
      have hnd := hP.1.support_nodup
      cases P with
      | nil => exact absurd rfl huv
      | @cons _ w _ h rest =>
        cases rest with
        | nil => exact h
        | cons h' rest' =>
          have hwu : w ≠ u := (G.ne_of_adj h).symm
          have hwv : w = v := hinner w (by simp) hwu
          subst hwv
          exfalso
          simp only [Walk.support_cons, List.nodup_cons] at hnd
          exact hnd.2.1 (Walk.end_mem_support _)
    refine ⟨.chord s(u, v), ⟨u, v, rfl, hP.2.1, hP.2.2.1, hadj, hnotCyc⟩,
      ⟨fun x hx => by_contra fun h => ?_, rfl⟩,
      ⟨hP.2.1, Sym2.mem_mk_left u v⟩, ⟨hP.2.2.1, Sym2.mem_mk_right u v⟩⟩
    push Not at h
    exact h.2 (hinner x hx h.1)

/-- In a crossing `(Q, R)` of `D`, neither `Q` nor `R` has endpoints that form a cycle edge of `D`. -/
theorem IsCrossing.not_isCycleEdge_ends {G : SimpleGraph V} {D : List V} (hnd : D.Nodup)
    {u₁ v₁ u₂ v₂ : V} {Q : G.Walk u₁ v₁} {R : G.Walk u₂ v₂}
    (hcr : IsCrossing G D Q R) :
    u₁ ≠ v₁ ∧ u₂ ≠ v₂ ∧
      ¬ PlaneEmbedding.IsCycleEdge D u₁ v₁ ∧ ¬ PlaneEmbedding.IsCycleEdge D u₂ v₂ := by
  have halt₁ : Alternate D u₁ v₁ u₂ v₂ := hcr.alternate
  have halt₂ : Alternate D u₂ v₂ v₁ u₁ := halt₁.comm
  have hu₂v₂ : u₂ ≠ v₂ := halt₁.ne hnd
  have hu₁v₁ : u₁ ≠ v₁ := (halt₂.ne hnd).symm
  have hnot : ∀ {a b c d : V}, Alternate D a b c d → ¬ PlaneEmbedding.IsCycleEdge D a b := by
    intro a b c d ⟨k, L₁, L₂, hrot, hc, hd⟩ hcyc
    rw [← isCycleEdge_rotate (k := k), hrot] at hcyc
    have hnd' : (a :: L₁ ++ b :: L₂).Nodup := hrot ▸ (List.nodup_rotate.mpr hnd)
    rw [isCycleEdge_cons_append_cons_iff hnd'] at hcyc
    rcases hcyc with rfl | rfl
    · exact List.not_mem_nil hc
    · exact List.not_mem_nil hd
  exact ⟨hu₁v₁, hu₂v₂, hnot halt₁, hnot halt₂⟩

/-- **Characterizing when a crossing uses distinct bridges (Section 5.3 / Lemma 4 link).**
A crossing `(Q, R)` of `D` in `G` uses distinct `D`-bridges if and only if no walk in `G - V(D)`
connects an inner vertex of `Q` to an inner vertex of `R`. -/
theorem IsCrossing.usesDistinctBridges_iff {G : SimpleGraph V} {S : Set V} {D : List V}
    (hG : IsSupportedOn G S) (hnd : D.Nodup)
    {u₁ v₁ u₂ v₂ : V} {Q : G.Walk u₁ v₁} {R : G.Walk u₂ v₂}
    (hcr : IsCrossing G D Q R) :
    UsesDistinctBridges G S D Q R ↔
      ¬ ∃ x ∈ Q.support, x ≠ u₁ ∧ x ≠ v₁ ∧
        ∃ y ∈ R.support, y ≠ u₂ ∧ y ≠ v₂ ∧ (offCycleGraph G D).Reachable x y := by
  obtain ⟨hu₁v₁, hu₂v₂, hnot₁, hnot₂⟩ := IsCrossing.not_isCycleEdge_ends hnd hcr
  obtain ⟨B₁, hB₁, hQ_B₁, -, -⟩ := IsTPath.exists_bridge hG hcr.2.1 hu₁v₁ hnot₁
  obtain ⟨B₂, hB₂, hR_B₂, -, -⟩ := IsTPath.exists_bridge hG hcr.2.2.1 hu₂v₂ hnot₂
  constructor
  · rintro ⟨B₁', B₂', hB₁', hB₂', hne, hQ', hR'⟩ ⟨x, hxQ, hxu₁, hxv₁, y, hxR, hxu₂, hxv₂, hreach⟩
    have e₁ := UsesBridge.unique hB₁ hB₁' hQ_B₁ hQ'
    have e₂ := UsesBridge.unique hB₂ hB₂' hR_B₂ hR'
    subst e₁; subst e₂
    cases B₁ with
    | chord e₁ => exact (hQ_B₁.1 x hxQ).elim hxu₁ hxv₁
    | comp A₁ =>
      cases B₂ with
      | chord e₂ => exact (hR_B₂.1 y hxR).elim hxu₂ hxv₂
      | comp A₂ =>
        obtain ⟨v₁₀, _, _, rfl⟩ := hB₁
        obtain ⟨v₂₀, _, _, rfl⟩ := hB₂
        have hx₁ : x ∈ offCycleComp G D v₁₀ := hQ_B₁.2 x hxQ hxu₁ hxv₁
        have hy₂ : y ∈ offCycleComp G D v₂₀ := hR_B₂.2 y hxR hxu₂ hxv₂
        have hy₁ : y ∈ offCycleComp G D v₁₀ := ⟨hy₂.1, hx₁.2.trans hreach⟩
        have heq : offCycleComp G D v₁₀ = offCycleComp G D v₂₀ := by
          rw [← offCycleComp_eq_of_mem hy₁, ← offCycleComp_eq_of_mem hy₂]
        exact hne (congrArg Bridge.comp heq)
  · intro hno
    refine ⟨B₁, B₂, hB₁, hB₂, ?_, hQ_B₁, hR_B₂⟩
    intro heq
    subst heq
    cases B₁ with
    | chord e =>
      have : s(u₁, v₁) = s(u₂, v₂) := hQ_B₁.2.symm.trans hR_B₂.2
      rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcr.2.2.2 Q.start_mem_support R.start_mem_support
      · exact hcr.2.2.2 Q.start_mem_support R.end_mem_support
    | comp A =>
      obtain ⟨⟨x, hxQ, hxu₁, hxv₁⟩, hallQ⟩ := hQ_B₁
      obtain ⟨⟨y, hyR, hyu₂, hyv₂⟩, hallR⟩ := hR_B₂
      obtain ⟨v₀, _, _, rfl⟩ := hB₁
      have hxA := hallQ x hxQ hxu₁ hxv₁
      have hyA := hallR y hyR hyu₂ hyv₂
      exact hno ⟨x, hxQ, hxu₁, hxv₁, y, hyR, hyu₂, hyv₂, hxA.2.symm.trans hyA.2⟩

/-- Conversely, any two distinct attachments `p ≠ q` of a `D`-bridge `B` are joined by a `D`-path
using `B` (and avoiding `IsCycleEdge D p q` when `p, q` are non-consecutive on `D`). -/
theorem exists_isTPath_of_bridge_attachments {G : SimpleGraph V} {S : Set V} {D : List V}
    {B : Bridge V} (hB : IsBridge G S D B) {p q : V}
    (hp : IsBridgeAttachment G D B p) (hq : IsBridgeAttachment G D B q) (hpq : p ≠ q) :
    ∃ P : G.Walk p q, IsTPath G D P ∧ UsesBridge G P B := by
  classical
  cases B with
  | chord e =>
    obtain ⟨u, v, rfl, huD, hvD, hadj, _⟩ := hB
    have hp_uv : p = u ∨ p = v := Sym2.mem_iff.mp hp.2
    have hq_uv : q = u ∨ q = v := Sym2.mem_iff.mp hq.2
    have h_ord : (p = u ∧ q = v) ∨ (p = v ∧ q = u) := by
      rcases hp_uv with rfl | rfl <;> rcases hq_uv with rfl | rfl
      · exact absurd rfl hpq
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hpq
    have hadj_pq : G.Adj p q := by
      rcases h_ord with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm
    have he_eq : s(u, v) = s(p, q) := by
      rcases h_ord with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    refine ⟨hadj_pq.toWalk, ⟨Walk.IsPath.of_adj hadj_pq, hp.1, hq.1, fun x hx h1 h2 => ?_⟩,
      ⟨fun x hx => ?_, he_eq⟩⟩
    · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.mem_nil_iff, or_false] at hx
      exact hx.elim (fun h => absurd h h1) (fun h => absurd h h2)
    · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.mem_nil_iff, or_false] at hx
      exact hx
  | comp A =>
    obtain ⟨v₀, _, hv₀D, rfl⟩ := hB
    obtain ⟨hpD, a, haA, hadj_ap⟩ := hp
    obtain ⟨hqD, b, hbA, hadj_bq⟩ := hq
    have hreach : (offCycleGraph G D).Reachable a b := haA.2.symm.trans hbA.2
    obtain ⟨w₀⟩ := hreach
    set w₁ := (w₀.bypass).mapLe (offCycleGraph_le G D)
    have hw₁_path : w₁.IsPath := w₀.bypass_isPath.mapLe (offCycleGraph_le G D)
    have hw₁_in : ∀ x ∈ w₁.support, x ∈ offCycleComp G D v₀ := by
      intro x hx
      rw [HP25.support_mapLe] at hx
      have hx' := w₀.support_bypass_subset_support hx
      have hsub : ∀ {y z : V} (w : (offCycleGraph G D).Walk y z),
          y ∈ offCycleComp G D v₀ → ∀ x ∈ w.support, x ∈ offCycleComp G D v₀ := by
        intro y z w hy
        induction w with
        | nil =>
          intro x hx
          simp only [Walk.support_nil, List.mem_singleton] at hx
          exact hx ▸ hy
        | @cons y' m z' h w' ih =>
          have hm : m ∈ offCycleComp G D v₀ :=
            ⟨h.2.2, hy.2.trans (Adj.reachable h)⟩
          intro x hx
          simp only [Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hy
          · exact ih hm x hx
      exact hsub w₀ haA x hx'
    have hp_not_in : p ∉ w₁.support := fun h => (hw₁_in p h).1 hpD
    have hq_not_in : q ∉ w₁.support := fun h => (hw₁_in q h).1 hqD
    set w₂ : G.Walk p b := Walk.cons hadj_ap.symm w₁
    have hw₂_path : w₂.IsPath := hw₁_path.cons hp_not_in
    set P : G.Walk p q := w₂.concat hadj_bq
    have hP_path : P.IsPath := by
      have hrev : P.reverse.IsPath := by
        have hrev_eq : P.reverse = Walk.cons hadj_bq.symm w₂.reverse := by
          simp [P, Walk.reverse_concat]
        rw [hrev_eq]
        refine hw₂_path.reverse.cons ?_
        rw [Walk.support_reverse, List.mem_reverse]
        simp only [w₂, Walk.support_cons, List.mem_cons, not_or]
        exact ⟨hpq.symm, hq_not_in⟩
      simpa using hrev.reverse
    have hP_supp : ∀ x ∈ P.support, x = p ∨ x = q ∨ x ∈ w₁.support := by
      intro x hx
      simp only [P, w₂, Walk.support_concat, Walk.support_cons, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | hx) | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hx)
      · exact Or.inr (Or.inl rfl)
    have ha_supp : a ∈ P.support := by
      simp [P, w₂, Walk.support_concat]
    have hap : a ≠ p := by intro h; subst h; exact haA.1 hpD
    have haq : a ≠ q := by intro h; subst h; exact haA.1 hqD
    refine ⟨P, ⟨hP_path, hpD, hqD, fun x hx hxp hxq => ?_⟩,
      ⟨⟨a, ha_supp, hap, haq⟩, fun x hx hxp hxq => ?_⟩⟩
    · have hxA := hw₁_in x ((hP_supp x hx).resolve_left hxp |>.resolve_left hxq)
      exact ⟨hxA.1, hxA.1⟩
    · exact hw₁_in x ((hP_supp x hx).resolve_left hxp |>.resolve_left hxq)

/-! ### 4. Candidate endpoint pairs and their count (Section 5.1) -/

variable {α : Type*}

/-- Generate cyclic distance-`d` pairs `(t[i], t[(i + d) % h])` from an attachment list
`t = [t_0, ..., t_{h-1}]`, omitting loops (`t[i] = t[(i + d) % h]`).
Section 5.1 of the note: "For a bridge with attachment list $t_0,t_1,\ldots,t_{h-1}$, we generate
the pairs $\{t_i,t_{i+1}\}$, $\{t_i,t_{i+2}\}$ with indices modulo $h$, and omit pairs whose two
elements are equal. Duplicates may be kept." -/
def stepCandidates [DecidableEq α] (d : ℕ) (t : List α) : List (α × α) :=
  ((List.range t.length).filterMap fun i =>
    if h : 0 < t.length then
      let a := t[i % t.length]'(Nat.mod_lt _ h)
      let b := t[(i + d) % t.length]'(Nat.mod_lt _ h)
      if a = b then none else some (a, b)
    else none)

/-- All candidate endpoint pairs (cyclic distance 1 and cyclic distance 2, omitting loops) of an
attachment list `t`. -/
def attachmentCandidates [DecidableEq α] (t : List α) : List (α × α) :=
  stepCandidates 1 t ++ stepCandidates 2 t

theorem length_stepCandidates_le [DecidableEq α] (d : ℕ) (t : List α) :
    (stepCandidates d t).length ≤ t.length := by
  unfold stepCandidates
  exact (List.length_filterMap_le _ _).trans (by simp)

/-- Section 5.1 of the note: "There are at most twice as many candidates as attachments." -/
theorem length_attachmentCandidates_le [DecidableEq α] (t : List α) :
    (attachmentCandidates t).length ≤ 2 * t.length := by
  unfold attachmentCandidates
  rw [List.length_append, Nat.two_mul]
  exact Nat.add_le_add (length_stepCandidates_le 1 t) (length_stepCandidates_le 2 t)

theorem mem_stepCandidates_iff [DecidableEq α] {d : ℕ} {t : List α} {p : α × α} :
    p ∈ stepCandidates d t ↔
      ∃ (h : 0 < t.length) (i : ℕ) (hi : i < t.length),
        t[i]'hi ≠ t[(i + d) % t.length]'(Nat.mod_lt _ h) ∧
        p = (t[i]'hi, t[(i + d) % t.length]'(Nat.mod_lt _ h)) := by
  unfold stepCandidates
  simp only [List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    have hpos : 0 < t.length := by omega
    simp only [hpos, ↓reduceDIte] at h
    split_ifs at h with heq
    simp only [Option.some.injEq] at h
    have hmod : i % t.length = i := Nat.mod_eq_of_lt hi
    refine ⟨hpos, i, hi, ?_, ?_⟩
    · intro e
      apply heq
      simpa [hmod] using e
    · rw [← h]
      simp [hmod]
  · rintro ⟨hpos, i, hi, hne, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp only [hpos, ↓reduceDIte]
    have hmod : i % t.length = i := Nat.mod_eq_of_lt hi
    simp [hmod, hne]

theorem mem_attachmentCandidates_iff [DecidableEq α] {t : List α} {p : α × α} :
    p ∈ attachmentCandidates t ↔ p ∈ stepCandidates 1 t ∨ p ∈ stepCandidates 2 t :=
  List.mem_append

/-- A candidate interval `(l, r, γ)` with `l < r`, where `γ` is its bridge identifier
(Section 5.2 of the note: "Number the vertices of $D$ as $0,\ldots,c-1$ in cyclic order. We
represent a candidate as a triple $(l,r,\gamma)$, $l<r$, where $l$ and $r$ are the numbers of its
two attachments and $\gamma$, its *color*, is the identifier of its bridge."). -/
structure Candidate where
  /-- Left endpoint index on `D`. -/
  l : ℕ
  /-- Right endpoint index on `D`. -/
  r : ℕ
  /-- Bridge identifier (color). -/
  γ : ℕ
  deriving DecidableEq, Repr

/-- Convert the candidate endpoint pairs of an attachment index list `t : List ℕ` for bridge `γ`
into `Candidate` intervals `(min a b, max a b, γ)`. -/
def candidatesOfIndices (γ : ℕ) (t : List ℕ) : List Candidate :=
  (attachmentCandidates t).map fun p => ⟨min p.1 p.2, max p.1 p.2, γ⟩

theorem length_candidatesOfIndices_le (γ : ℕ) (t : List ℕ) :
    (candidatesOfIndices γ t).length ≤ 2 * t.length := by
  simp only [candidatesOfIndices, List.length_map]
  exact length_attachmentCandidates_le t

theorem mem_candidatesOfIndices_lt {γ : ℕ} {t : List ℕ} {I : Candidate}
    (h : I ∈ candidatesOfIndices γ t) :
    I.l < I.r ∧ I.γ = γ ∧ (I.l ∈ t ∧ I.r ∈ t) := by
  simp only [candidatesOfIndices, List.mem_map] at h
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
  have hstep : ∃ (hpos : 0 < t.length) (d i : ℕ) (hi : i < t.length),
      t[i]'hi ≠ t[(i + d) % t.length]'(Nat.mod_lt _ hpos) ∧
      (a, b) = (t[i]'hi, t[(i + d) % t.length]'(Nat.mod_lt _ hpos)) := by
    rcases mem_attachmentCandidates_iff.mp hab with h1 | h2
    · obtain ⟨hpos, i, hi, hne, heq⟩ := mem_stepCandidates_iff.mp h1
      exact ⟨hpos, 1, i, hi, hne, heq⟩
    · obtain ⟨hpos, i, hi, hne, heq⟩ := mem_stepCandidates_iff.mp h2
      exact ⟨hpos, 2, i, hi, hne, heq⟩
  obtain ⟨hpos, d, i, hi, hne, heq⟩ := hstep
  injection heq with ha hb
  subst ha hb
  dsimp only
  refine ⟨by omega, rfl, ?_⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · simp [Nat.min_eq_left (le_of_lt hlt), Nat.max_eq_right (le_of_lt hlt)]
  · simp [Nat.min_eq_right (le_of_lt hgt), Nat.max_eq_left (le_of_lt hgt)]

end GraphMinor.Crossing
