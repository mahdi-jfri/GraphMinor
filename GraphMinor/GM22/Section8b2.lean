module

public import GraphMinor.GM22.Section8b1
public import GraphMinor.GM14.Section6
public import GraphMinor.GM14.Section8
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM11.Theorem61
import GraphMinor.GM14.RigidSegregation

/-!
# Graph Minors XXII, Section 8 (Part b2: Claims 2 and 3 of Theorem 8.3)

This file proves Claims (2) and (3) of Theorem (8.3) of Robertson and Seymour,
*Graph Minors. XXII. Irrelevant Vertices in Linkage Problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (page 560).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM14.Whitney

universe u v w

variable {α : Type u} {β : Type v}
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-! ## 1. General Separations of Order at Most 2 in a Subdivision of a Simple 3-Connected Graph -/

namespace SubDataSepGeneral

variable {G G₀ : Graph α β} {P : β → Graph α β}

/-- Along any walk `W` from `a` to `b`, if `a ∈ verts G A` and `b ∉ verts G A`, some vertex on `W`
other than `b` belongs to `bdry G A`. -/
theorem exists_bdry_of_walk {A : Set β} {a b : α} (W : GraphWalk G a b)
    (ha : a ∈ verts G A) (hb : b ∉ verts G A) :
    ∃ z ∈ W.support, z ≠ b ∧ z ∈ bdry G A := by
  induction W with
  | nil _ => exact (hb ha).elim
  | @cons u v w g hlink rest ih =>
    by_cases hv : v ∈ verts G A
    · obtain ⟨z, hz, hzb, hbd⟩ := ih hv hb
      exact ⟨z, by simp [GraphWalk.support, hz], hzb, hbd⟩
    · have hgA : g ∉ A := fun hg => hv ⟨g, hg, u, hlink.symm⟩
      have hu_out : u ∈ verts G (E(G) \ A) := ⟨g, ⟨hlink.edge_mem, hgA⟩, v, hlink⟩
      exact ⟨u, by simp [GraphWalk.support], fun h => hb (h ▸ ha), ha, hu_out⟩

/-- Every edge of `G` incident with an internal vertex `x ∈ V(P e) \ V(G₀)` belongs to `E(P e)`. -/
theorem inc_mem_path_of_notMem_V₀ (h : SubData G G₀ P) {e g : β} {x : α}
    (he : e ∈ E(G₀)) (hxP : x ∈ V(P e)) (hx₀ : x ∉ V(G₀)) (hg : g ∈ E(G)) (hinc : G.Inc g x) :
    g ∈ E(P e) := by
  rw [h.eunion] at hg
  obtain ⟨f, hf, hgf⟩ := mem_iUnion₂.mp hg
  by_cases hfe : f = e
  · exact hfe ▸ hgf
  · obtain ⟨_, _, -, hp, -, -⟩ := h.path f hf
    obtain ⟨y, hy⟩ := hinc
    have hxPf : x ∈ V(P f) := ((hp.le.isLink_iff hgf).mpr hy).left_mem
    exact (hx₀ ((h.disj e he f hf (Ne.symm hfe)).2 ⟨hxP, hxPf⟩)).elim

/-- Every vertex in `bdry G A` belongs to `V(G)`. -/
theorem bdry_subset_V (A : Set β) : bdry G A ⊆ V(G) := by
  rintro x ⟨_, g, ⟨hg, _⟩, y, hlink⟩
  exact hlink.left_mem

/-- For any `SubData G G₀ P`, `E(G₀)`, `V(G)`, and `bdry G A` are finite. -/
theorem finite_V (h : SubData G G₀ P) : V(G).Finite := by
  have hfinV₀ : V(G₀).Finite := h.finite_V₀
  have : Finite V(G₀) := hfinV₀.to_subtype
  have hfinE₀ : E(G₀).Finite := by
    have hex : ∀ e : E(G₀), ∃ u v : V(G₀), G₀.IsLink e.1 u.1 v.1 := by
      intro e
      obtain ⟨u, v, hl, -⟩ := h.path e.1 e.2
      exact ⟨⟨u, hl.left_mem⟩, ⟨v, hl.right_mem⟩, hl⟩
    choose u v hlink using hex
    have hinj : Function.Injective (fun e : E(G₀) => (u e, v e)) := by
      intro e₁ e₂ heq
      have h1 : (u e₁).1 = (u e₂).1 := congrArg (fun p => p.1.1) heq
      have h2 : (v e₁).1 = (v e₂).1 := congrArg (fun p => p.2.1) heq
      apply Subtype.ext
      exact h.simple.1.2 e₁.1 e₁.2 e₂.1 e₂.2 (u e₁).1 (v e₁).1 (hlink e₁)
        (h1 ▸ h2 ▸ hlink e₂)
    exact Finite.of_injective _ hinj
  rw [h.vunion]
  refine hfinV₀.union (hfinE₀.biUnion fun e he => ?_)
  obtain ⟨_, _, -, ⟨_, W, _, hV, _⟩, -⟩ := h.path e he
  rw [hV]
  exact W.support.toFinset.finite_toSet.subset fun x hx => List.mem_toFinset.mpr hx

theorem finite_bdry (h : SubData G G₀ P) (A : Set β) : (bdry G A).Finite :=
  (finite_V h).subset (bdry_subset_V A)

/-- If `x ∈ V(G)` is not in `V(P e)`, no edge of `E(P e)` is incident with `x` in `G`. -/
theorem not_inc_of_notMem_path (h : SubData G G₀ P) {e g : β} {x : α}
    (he : e ∈ E(G₀)) (hx : x ∉ V(P e)) (hg : g ∈ E(P e)) : ¬ G.Inc g x := by
  obtain ⟨_, _, -, hp, -, -⟩ := h.path e he
  rintro ⟨y, hy⟩
  exact hx (((hp.le.isLink_iff hg).mpr hy).left_mem)

/-- In a simple 3-connected graph `G₀`, for any edge `e₁ ∈ E(G₀)` there exist three distinct edges
in `E(G₀) \ {e₁}`. -/
theorem exists_three_edges_outside (h : SubData G G₀ P) {e₁ : β} (he₁ : e₁ ∈ E(G₀)) :
    ∃ a₁ a₂ a₃ : β, a₁ ∈ E(G₀) \ {e₁} ∧ a₂ ∈ E(G₀) \ {e₁} ∧ a₃ ∈ E(G₀) \ {e₁} ∧
      a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ := by
  obtain ⟨u₁, v₁, hl₁, -, -, -⟩ := h.path e₁ he₁
  have h4 := h.simple.2.1
  have hfin := h.finite_V₀
  have hne : (V(G₀) \ {u₁, v₁}).Nonempty := by
    by_contra hemp
    have hsub : V(G₀) ⊆ {u₁, v₁} := fun x hx => by
      by_contra hx_not
      exact hemp ⟨x, hx, hx_not⟩
    have hle := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_insert_le u₁ {v₁})
    rw [Set.ncard_singleton] at hle
    omega
  obtain ⟨x, hxV₀, hx_not⟩ := hne
  obtain ⟨a₁, a₂, a₃, h12, h13, h23, hi₁, hi₂, hi₃⟩ :=
    IsSimpleThreeConnected.exists_three_edges h.simple hxV₀
  have hnot_e₁ : ∀ {a : β}, G₀.Inc a x → a ∈ E(G₀) \ {e₁} := by
    rintro a ⟨y, hlink⟩
    refine ⟨hlink.edge_mem, ?_⟩
    rintro rfl
    rcases G₀.eq_or_eq_of_isLink_of_isLink hlink hl₁ with rfl | rfl
    · exact hx_not (Or.inl rfl)
    · exact hx_not (Or.inr rfl)
  exact ⟨a₁, a₂, a₃, hnot_e₁ hi₁, hnot_e₁ hi₂, hnot_e₁ hi₃, h12, h13, h23⟩

/-- It is impossible to have a set `B₁ ⊆ E(G)` disjoint from `E(P e₁)` (`e₁ ∈ E(G₀)`) such that
`B₁.Nonempty`, `(E(G) \ (B₁ ∪ E(P e₁))).Nonempty`, and both `B₁` and `B₁ ∪ E(P e₁)` have boundary
in `V(G₀)` of size `≤ 2`. -/
theorem not_both_sep_of_union_path (h : SubData G G₀ P) {e₁ : β} (he₁ : e₁ ∈ E(G₀))
    {B₁ : Set β} (hB₁ : B₁ ⊆ E(G)) (hdisj : Disjoint B₁ E(P e₁))
    (hne₁ : B₁.Nonempty) (hne₂ : (E(G) \ (B₁ ∪ E(P e₁))).Nonempty)
    (hbd₁ : bdry G B₁ ⊆ V(G₀)) (hc₁ : (bdry G B₁).ncard ≤ 2)
    (hbd₂ : bdry G (B₁ ∪ E(P e₁)) ⊆ V(G₀)) (hc₂ : (bdry G (B₁ ∪ E(P e₁))).ncard ≤ 2) :
    False := by
  have hPe₁_sub : E(P e₁) ⊆ E(G) := by
    intro g hg
    rw [h.eunion]
    exact mem_iUnion₂.mpr ⟨e₁, he₁, hg⟩
  obtain ⟨_, _, -, -, hPe₁_ne, -⟩ := h.path e₁ he₁
  have hne₁' : (E(G) \ B₁).Nonempty := by
    obtain ⟨g, hg⟩ := hPe₁_ne
    exact ⟨g, hPe₁_sub hg, disjoint_right.mp hdisj hg⟩
  have hB₂_sub : B₁ ∪ E(P e₁) ⊆ E(G) := union_subset hB₁ hPe₁_sub
  have hne₂_left : (B₁ ∪ E(P e₁)).Nonempty := hne₁.mono subset_union_left
  obtain ⟨f₁, hf₁, hsep₁⟩ := h.sep hB₁ hbd₁ hc₁ hne₁ hne₁'
  obtain ⟨f₂, hf₂, hsep₂⟩ := h.sep hB₂_sub hbd₂ hc₂ hne₂_left hne₂
  have hB₁_eq : B₁ = E(P f₁) := by
    rcases hsep₁ with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨g₁, hg₁⟩ := hPe₁_ne
      have hg₁_in : g₁ ∈ E(P f₁) := h1 ▸ ⟨hPe₁_sub hg₁, disjoint_right.mp hdisj hg₁⟩
      have hf₁_eq : f₁ = e₁ := by
        by_contra hne
        exact disjoint_left.mp (h.disj f₁ hf₁ e₁ he₁ hne).1 hg₁_in hg₁
      subst hf₁_eq
      obtain ⟨g₂, hg₂E, hg₂_not⟩ := hne₂
      have hg₂_in : g₂ ∈ E(P f₁) := h1 ▸ ⟨hg₂E, fun h => hg₂_not (Or.inl h)⟩
      exact hg₂_not (Or.inr hg₂_in)
  have hB₂_compl_eq : E(G) \ (B₁ ∪ E(P e₁)) = E(P f₂) := by
    rcases hsep₂ with h2 | h2
    · exfalso
      obtain ⟨g₁, hg₁⟩ := hPe₁_ne
      have hg₁_in : g₁ ∈ E(P f₂) := h2 ▸ Or.inr hg₁
      have hf₂_eq : f₂ = e₁ := by
        by_contra hne
        exact disjoint_left.mp (h.disj f₂ hf₂ e₁ he₁ hne).1 hg₁_in hg₁
      subst hf₂_eq
      obtain ⟨g₀, hg₀⟩ := hne₁
      have hg₀_in : g₀ ∈ E(P f₂) := h2 ▸ Or.inl hg₀
      exact disjoint_left.mp hdisj hg₀ hg₀_in
    · exact h2
  obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h12, h13, h23⟩ := exists_three_edges_outside h he₁
  have hmem_f : ∀ a ∈ E(G₀) \ {e₁}, a = f₁ ∨ a = f₂ := by
    rintro a ⟨ha, ha_ne⟩
    obtain ⟨_, _, -, -, ⟨g, hg⟩, -⟩ := h.path a ha
    have hgE : g ∈ E(G) := by
      rw [h.eunion]
      exact mem_iUnion₂.mpr ⟨a, ha, hg⟩
    have hg_not_e₁ : g ∉ E(P e₁) :=
      disjoint_left.mp (h.disj a ha e₁ he₁ ha_ne).1 hg
    by_cases hgB₁ : g ∈ B₁
    · left
      rw [hB₁_eq] at hgB₁
      by_contra hne
      exact disjoint_left.mp (h.disj a ha f₁ hf₁ hne).1 hg hgB₁
    · right
      have hg_in : g ∈ E(P f₂) := hB₂_compl_eq ▸ ⟨hgE, not_or.mpr ⟨hgB₁, hg_not_e₁⟩⟩
      by_contra hne
      exact disjoint_left.mp (h.disj a ha f₂ hf₂ hne).1 hg hg_in
  rcases hmem_f a₁ ha₁ with h1 | h1 <;>
    rcases hmem_f a₂ ha₂ with h2 | h2 <;>
    rcases hmem_f a₃ ha₃ with h3 | h3
  · exact h12 (h1.trans h2.symm)
  · exact h12 (h1.trans h2.symm)
  · exact h13 (h1.trans h3.symm)
  · exact h23 (h2.trans h3.symm)
  · exact h23 (h2.trans h3.symm)
  · exact h13 (h1.trans h3.symm)
  · exact h12 (h1.trans h2.symm)
  · exact h12 (h1.trans h2.symm)

/-- If `e ∈ E(G₀)` has ends `u, v` and `bdry G A ∩ (V(P e) \ V(G₀)) = {w}`, then removing `E(P e)`
from `A` and adding `E(P e)` to `A` move `w` to `{u, v}` without increasing the boundary size. -/
theorem move_internal_bdry (h : SubData G G₀ P) {A : Set β} (hA : A ⊆ E(G))
    {e : β} (he : e ∈ E(G₀)) {w : α} (hw : bdry G A ∩ (V(P e) \ V(G₀)) = {w}) :
    ∃ u v : α, G₀.IsLink e u v ∧
      bdry G (A \ E(P e)) ⊆ (bdry G A \ (V(P e) \ V(G₀))) ∪ {u} ∧
      bdry G (A ∪ E(P e)) ⊆ (bdry G A \ (V(P e) \ V(G₀))) ∪ {v} := by
  obtain ⟨u, v, hl, ⟨hle, W, hs, hV, hE⟩, _, hcap⟩ := h.path e he
  have hw_mem : w ∈ bdry G A ∧ w ∈ V(P e) \ V(G₀) := by
    have : w ∈ bdry G A ∩ (V(P e) \ V(G₀)) := hw.symm ▸ mem_singleton w
    exact this
  have hwP : w ∈ V(P e) := hw_mem.2.1
  have hwW : w ∈ W.support := by rwa [hV] at hwP
  obtain ⟨W₁, W₂, hW_eq⟩ := W.exists_append_of_mem hwW
  have hs' : (W₁.append W₂).IsSimple := hW_eq ▸ hs
  have hsp := GM09.isSimple_of_append hs'
  have hnd_V : (W₁.support ++ W₂.support.tail).Nodup := by
    have h1 : (W₁.append W₂).support.Nodup := hs'
    rwa [GraphWalk.support_append] at h1
  have hd_V := List.nodup_append.mp hnd_V
  have hmemE : ∀ {g : β}, g ∈ W.edges → g ∈ E(G) := fun {g} hg =>
    hle.edgeSet_mono (by rw [hE]; exact hg)
  have hincG : ∀ {g x}, (P e).Inc g x → G.Inc g x := fun ⟨y, hy⟩ => ⟨y, hy.mono hle⟩
  have hW₁_pure : ∀ e₁ ∈ W₁.edges, ∀ e₂ ∈ W₁.edges, e₁ ∈ A ↔ e₂ ∈ A := by
    refine walk_pure W₁ hsp.1 fun x hx hxu hxw e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
    have hxW : x ∈ W.support := by
      rw [hW_eq, GraphWalk.mem_support_append]
      exact Or.inl hx
    have hxv : x ≠ v := by
      rintro rfl
      have hv₂ : x ∈ W₂.support := W₂.end_mem_support
      rw [W₂.support_eq_cons] at hv₂
      rcases List.mem_cons.mp hv₂ with rfl | hv_tail
      · exact hxw rfl
      · exact hd_V.2.2 x hx x hv_tail rfl
    have hx_not_V₀ : x ∉ V(G₀) := by
      intro hx₀
      have hm : x ∈ V(P e) ∩ V(G₀) := ⟨hV ▸ hxW, hx₀⟩
      rw [hcap] at hm
      exact hm.elim hxu hxv
    have hx_not_bd : x ∉ bdry G A := by
      intro hbd
      have : x ∈ bdry G A ∩ (V(P e) \ V(G₀)) := ⟨hbd, hV ▸ hxW, hx_not_V₀⟩
      rw [hw] at this
      exact hxw this
    have he₁W : e₁ ∈ W.edges := by rw [hW_eq, GraphWalk.edges_append]; exact List.mem_append_left _ he₁
    have he₂W : e₂ ∈ W.edges := by rw [hW_eq, GraphWalk.edges_append]; exact List.mem_append_left _ he₂
    constructor <;> intro h₁ <;> by_contra h₂
    · exact hx_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
    · exact hx_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩
  have hW₂_pure : ∀ e₁ ∈ W₂.edges, ∀ e₂ ∈ W₂.edges, e₁ ∈ A ↔ e₂ ∈ A := by
    refine walk_pure W₂ hsp.2 fun x hx hxw hxv e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
    have hxW : x ∈ W.support := by
      rw [hW_eq, GraphWalk.mem_support_append]
      exact Or.inr hx
    have hxu : x ≠ u := by
      rintro rfl
      have hu₁ : x ∈ W₁.support := W₁.start_mem_support
      rw [W₂.support_eq_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx_tail
      · exact hxw rfl
      · exact hd_V.2.2 x hu₁ x hx_tail rfl
    have hx_not_V₀ : x ∉ V(G₀) := by
      intro hx₀
      have hm : x ∈ V(P e) ∩ V(G₀) := ⟨hV ▸ hxW, hx₀⟩
      rw [hcap] at hm
      exact hm.elim hxu hxv
    have hx_not_bd : x ∉ bdry G A := by
      intro hbd
      have : x ∈ bdry G A ∩ (V(P e) \ V(G₀)) := ⟨hbd, hV ▸ hxW, hx_not_V₀⟩
      rw [hw] at this
      exact hxw this
    have he₁W : e₁ ∈ W.edges := by rw [hW_eq, GraphWalk.edges_append]; exact List.mem_append_right _ he₁
    have he₂W : e₂ ∈ W.edges := by rw [hW_eq, GraphWalk.edges_append]; exact List.mem_append_right _ he₂
    constructor <;> intro h₁ <;> by_contra h₂
    · exact hx_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
    · exact hx_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩
  have huw : u ≠ w := fun h => hw_mem.2.2 (h ▸ hl.left_mem)
  have hvw : v ≠ w := fun h => hw_mem.2.2 (h ▸ hl.right_mem)
  obtain ⟨gu, hgu₁, hiu⟩ := exists_edge_at_start W₁ huw
  obtain ⟨gv, hgv₂_rev, hiv⟩ := exists_edge_at_start W₂.reverse hvw
  have hgv₂ : gv ∈ W₂.edges := by
    rw [GraphWalk.edges_reverse] at hgv₂_rev
    exact List.mem_reverse.mp hgv₂_rev
  have hgu_Pe : gu ∈ E(P e) := by
    rw [hE, hW_eq, GraphWalk.edges_append]
    exact List.mem_append_left _ hgu₁
  have hgv_Pe : gv ∈ E(P e) := by
    rw [hE, hW_eq, GraphWalk.edges_append]
    exact List.mem_append_right _ hgv₂
  have hnot_iff : ¬ (gu ∈ A ↔ gv ∈ A) := by
    intro hiff
    obtain ⟨⟨f₁, hf₁A, hif₁⟩, f₂, ⟨hf₂E, hf₂A⟩, hif₂⟩ := hw_mem.1
    have hf₁_Pe : f₁ ∈ E(P e) :=
      inc_mem_path_of_notMem_V₀ h he hw_mem.2.1 hw_mem.2.2 (hA hf₁A) hif₁
    have hf₂_Pe : f₂ ∈ E(P e) :=
      inc_mem_path_of_notMem_V₀ h he hw_mem.2.1 hw_mem.2.2 hf₂E hif₂
    have hall : ∀ g ∈ E(P e), g ∈ A ↔ gu ∈ A := by
      intro g hg
      rw [hE, hW_eq, mem_ofPred_eq, GraphWalk.edges_append] at hg
      rcases List.mem_append.mp hg with hg₁ | hg₂
      · exact hW₁_pure g hg₁ gu hgu₁
      · exact (hW₂_pure g hg₂ gv hgv₂).trans hiff.symm
    exact hf₂A ((hall f₂ hf₂_Pe).mpr ((hall f₁ hf₁_Pe).mp hf₁A))
  have hstep : ∀ (u' v' : α) (gu' gv' : β),
      G₀.IsLink e u' v' → ({u', v'} : Set α) = {u, v} →
      gu' ∈ E(P e) → gv' ∈ E(P e) → G.Inc gu' u' → G.Inc gv' v' →
      gu' ∈ A → gv' ∉ A →
      bdry G (A \ E(P e)) ⊆ (bdry G A \ (V(P e) \ V(G₀))) ∪ {u'} ∧
      bdry G (A ∪ E(P e)) ⊆ (bdry G A \ (V(P e) \ V(G₀))) ∪ {v'} := by
    intro u' v' gu' gv' hl' hpair hgu' hgv' hiu' hiv' hgu'A hgv'A
    have hPe_sub : E(P e) ⊆ E(G) := fun g hg => hle.edgeSet_mono hg
    refine ⟨?_, ?_⟩
    · intro x hx
      by_cases hxu' : x = u'
      · exact Or.inr hxu'
      · left
        have hxG : x ∈ V(G) := bdry_subset_V _ hx
        have hx_not_int : x ∉ V(P e) \ V(G₀) := by
          rintro ⟨hxP, hx₀⟩
          obtain ⟨⟨g, ⟨hgA, hgPe⟩, hig⟩, -⟩ := hx
          exact hgPe (inc_mem_path_of_notMem_V₀ h he hxP hx₀ (hA hgA) hig)
        refine ⟨?_, hx_not_int⟩
        obtain ⟨⟨g₁, ⟨hg₁A, _⟩, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
        refine ⟨⟨g₁, hg₁A, hig₁⟩, g₂, ⟨hg₂E, fun hg₂A => hg₂_not ⟨hg₂A, fun hg₂Pe => ?_⟩⟩, hig₂⟩
        have hxP : x ∈ V(P e) := ((hle.isLink_iff hg₂Pe).mpr hig₂.choose_spec).left_mem
        have hxV₀ : x ∈ V(G₀) := by_contra fun hx₀ => hx_not_int ⟨hxP, hx₀⟩
        have hx_uv : x ∈ ({u', v'} : Set α) := hpair.symm ▸ (hcap ▸ ⟨hxP, hxV₀⟩)
        have hxv' : x = v' := hx_uv.resolve_left hxu'
        subst hxv'
        have hgeq : g₂ = gv' := h.eq_of_end he hl'.right_mem hg₂Pe hgv' hig₂ hiv'
        exact hgv'A (hgeq ▸ hg₂A)
    · intro x hx
      by_cases hxv' : x = v'
      · exact Or.inr hxv'
      · left
        have hx_not_int : x ∉ V(P e) \ V(G₀) := by
          rintro ⟨hxP, hx₀⟩
          obtain ⟨-, g, ⟨hgE, hg_not⟩, hig⟩ := hx
          exact hg_not (Or.inr (inc_mem_path_of_notMem_V₀ h he hxP hx₀ hgE hig))
        refine ⟨?_, hx_not_int⟩
        obtain ⟨⟨g₁, hg₁_in, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
        refine ⟨⟨g₁, ?_, hig₁⟩, g₂, ⟨hg₂E, fun hg₂A => hg₂_not (Or.inl hg₂A)⟩, hig₂⟩
        rcases hg₁_in with hg₁A | hg₁Pe
        · exact hg₁A
        · have hxP : x ∈ V(P e) := ((hle.isLink_iff hg₁Pe).mpr hig₁.choose_spec).left_mem
          have hxV₀ : x ∈ V(G₀) := by_contra fun hx₀ => hx_not_int ⟨hxP, hx₀⟩
          have hx_uv : x ∈ ({u', v'} : Set α) := hpair.symm ▸ (hcap ▸ ⟨hxP, hxV₀⟩)
          have hxu' : x = u' := hx_uv.resolve_right hxv'
          subst hxu'
          have hgeq : g₁ = gu' := h.eq_of_end he hl'.left_mem hg₁Pe hgu' hig₁ hiu'
          exact hgeq ▸ hgu'A
  by_cases hguA : gu ∈ A
  · have hgvA : gv ∉ A := fun h => hnot_iff ⟨fun _ => h, fun _ => hguA⟩
    exact ⟨u, v, hl, (hstep u v gu gv hl rfl hgu_Pe hgv_Pe (hincG hiu) (hincG hiv) hguA hgvA).1,
      (hstep u v gu gv hl rfl hgu_Pe hgv_Pe (hincG hiu) (hincG hiv) hguA hgvA).2⟩
  · have hgvA : gv ∈ A := by_contra fun h => hnot_iff ⟨fun h1 => (hguA h1).elim, fun h2 => (h h2).elim⟩
    exact ⟨v, u, hl.symm,
      (hstep v u gv gu hl.symm (pair_comm v u) hgv_Pe hgu_Pe (hincG hiv) (hincG hiu) hgvA hguA).1,
      (hstep v u gv gu hl.symm (pair_comm v u) hgv_Pe hgu_Pe (hincG hiv) (hincG hiu) hgvA hguA).2⟩

/-- For any `A ⊆ E(G)` with `(bdry G A).ncard ≤ 2`, `A.Nonempty`, and `(E(G) \ A).Nonempty`,
`bdry G A` is contained in `V(P e)` for some `e ∈ E(G₀)`. -/
theorem bdry_subset_path (h : SubData G G₀ P) {A : Set β} (hA : A ⊆ E(G))
    (hc : (bdry G A).ncard ≤ 2) (hne : A.Nonempty) (hne' : (E(G) \ A).Nonempty) :
    ∃ e ∈ E(G₀), bdry G A ⊆ V(P e) := by
  by_cases hbd₀ : bdry G A ⊆ V(G₀)
  · obtain ⟨e, he, heq | heq⟩ := h.sep hA hbd₀ hc hne hne'
    · refine ⟨e, he, ?_⟩
      intro x hx
      obtain ⟨⟨g, hgA, y, hlink⟩, -⟩ := hx
      rw [heq] at hgA
      obtain ⟨_, _, -, hp, -, -⟩ := h.path e he
      exact ((hp.le.isLink_iff hgA).mpr hlink).left_mem
    · refine ⟨e, he, ?_⟩
      intro x hx
      obtain ⟨-, g, hgA, y, hlink⟩ := hx
      rw [heq] at hgA
      obtain ⟨_, _, -, hp, -, -⟩ := h.path e he
      exact ((hp.le.isLink_iff hgA).mpr hlink).left_mem
  · obtain ⟨w₁, hw₁_bd, hw₁_not₀⟩ := not_subset.mp hbd₀
    have hw₁_V : w₁ ∈ V(G) := bdry_subset_V A hw₁_bd
    rw [h.vunion] at hw₁_V
    have hw₁_union : w₁ ∈ ⋃ e ∈ E(G₀), V(P e) := hw₁_V.resolve_left hw₁_not₀
    obtain ⟨e₁, he₁, hw₁_Pe₁⟩ := mem_iUnion₂.mp hw₁_union
    refine ⟨e₁, he₁, ?_⟩
    by_contra hnot_sub
    obtain ⟨z, hz_bd, hz_not_Pe₁⟩ := not_subset.mp hnot_sub
    have hzw₁ : z ≠ w₁ := fun h => hz_not_Pe₁ (h ▸ hw₁_Pe₁)
    have hbd_eq : bdry G A = {w₁, z} := by
      have hsub : ({w₁, z} : Set α) ⊆ bdry G A := by
        rintro x (rfl | rfl)
        · exact hw₁_bd
        · exact hz_bd
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by rw [Set.ncard_pair hzw₁.symm]; exact hc) (finite_bdry h A)).symm
    have hex_A' : ∃ (A' : Set β) (u' : α),
        A' ⊆ E(G) ∧ u' ∈ V(G₀) ∧ bdry G A' ⊆ {w₁, u'} ∧ w₁ ∈ bdry G A' ∧
        (A' \ E(P e₁)).Nonempty ∧ (E(G) \ (A' ∪ E(P e₁))).Nonempty := by
      by_cases hz₀ : z ∈ V(G₀)
      · refine ⟨A, z, hA, hz₀, hbd_eq.subset, hw₁_bd, ?_, ?_⟩
        · obtain ⟨⟨g, hgA, hig⟩, -⟩ := hz_bd
          exact ⟨g, hgA, fun hgP => not_inc_of_notMem_path h he₁ hz_not_Pe₁ hgP hig⟩
        · obtain ⟨-, g, ⟨hgE, hgA⟩, hig⟩ := hz_bd
          exact ⟨g, hgE, not_or.mpr ⟨hgA, fun hgP => not_inc_of_notMem_path h he₁ hz_not_Pe₁ hgP hig⟩⟩
      · have hz_V : z ∈ V(G) := bdry_subset_V A hz_bd
        rw [h.vunion] at hz_V
        obtain ⟨e₂, he₂, hz_Pe₂⟩ := mem_iUnion₂.mp (hz_V.resolve_left hz₀)
        have he12 : e₁ ≠ e₂ := fun heq => hz_not_Pe₁ (heq ▸ hz_Pe₂)
        have hdisj12 : Disjoint E(P e₁) E(P e₂) := (h.disj e₁ he₁ e₂ he₂ he12).1
        have hPe₂_sub : E(P e₂) ⊆ E(G) := fun g hg => by
          rw [h.eunion]; exact mem_iUnion₂.mpr ⟨e₂, he₂, hg⟩
        obtain ⟨_, _, -, -, ⟨g₂, hg₂_Pe₂⟩, -⟩ := h.path e₂ he₂
        have hz_inter : bdry G A ∩ (V(P e₂) \ V(G₀)) = {z} := by
          ext x
          rw [hbd_eq]
          simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
          constructor
          · exact fun ⟨hx, hxP, hx₀⟩ => hx.resolve_left (fun hxw =>
              hx₀ ((h.disj e₁ he₁ e₂ he₂ he12).2 ⟨hxw ▸ hw₁_Pe₁, hxP⟩))
          · rintro rfl
            exact ⟨Or.inr rfl, hz_Pe₂, hz₀⟩
        obtain ⟨u₂, v₂, hl₂, hs₁, hs₂⟩ := move_internal_bdry h hA he₂ hz_inter
        have hdiff₂ : bdry G A \ (V(P e₂) \ V(G₀)) = {w₁} := by
          ext x
          rw [hbd_eq]
          simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
          constructor
          · exact fun ⟨hx, hnot⟩ => hx.resolve_right (fun hxz => hnot (hxz ▸ ⟨hz_Pe₂, hz₀⟩))
          · rintro rfl
            exact ⟨Or.inl rfl, fun ⟨hwP₂, _⟩ =>
              hw₁_not₀ ((h.disj e₁ he₁ e₂ he₂ he12).2 ⟨hw₁_Pe₁, hwP₂⟩)⟩
        rw [hdiff₂] at hs₁ hs₂
        obtain ⟨⟨gw₁, hgw₁A, higw₁⟩, fw₁, ⟨hfw₁E, hfw₁A⟩, hifw₁⟩ := hw₁_bd
        have hgw₁_Pe₁ : gw₁ ∈ E(P e₁) :=
          inc_mem_path_of_notMem_V₀ h he₁ hw₁_Pe₁ hw₁_not₀ (hA hgw₁A) higw₁
        have hfw₁_Pe₁ : fw₁ ∈ E(P e₁) :=
          inc_mem_path_of_notMem_V₀ h he₁ hw₁_Pe₁ hw₁_not₀ hfw₁E hifw₁
        have hw₁_in_diff : w₁ ∈ bdry G (A \ E(P e₂)) :=
          ⟨⟨gw₁, ⟨hgw₁A, disjoint_left.mp hdisj12 hgw₁_Pe₁⟩, higw₁⟩,
            fw₁, ⟨hfw₁E, fun h => hfw₁A h.1⟩, hifw₁⟩
        have hw₁_in_union : w₁ ∈ bdry G (A ∪ E(P e₂)) :=
          ⟨⟨gw₁, Or.inl hgw₁A, higw₁⟩, fw₁,
            ⟨hfw₁E, not_or.mpr ⟨hfw₁A, disjoint_left.mp hdisj12 hfw₁_Pe₁⟩⟩, hifw₁⟩
        by_cases hrem : (E(G) \ ((A ∪ E(P e₂)) ∪ E(P e₁))).Nonempty
        · refine ⟨A ∪ E(P e₂), v₂, union_subset hA hPe₂_sub, hl₂.right_mem, hs₂, hw₁_in_union,
            ⟨g₂, Or.inr hg₂_Pe₂, disjoint_right.mp hdisj12 hg₂_Pe₂⟩, hrem⟩
        · refine ⟨A \ E(P e₂), u₂, sdiff_subset.trans hA, hl₂.left_mem, hs₁, hw₁_in_diff, ?_,
            ⟨g₂, hPe₂_sub hg₂_Pe₂, not_or.mpr ⟨fun h => h.2 hg₂_Pe₂, disjoint_right.mp hdisj12 hg₂_Pe₂⟩⟩⟩
          obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h12, h13, _⟩ := exists_three_edges_outside h he₁
          have hex_a : ∃ a ∈ E(G₀) \ {e₁}, a ≠ e₂ := by
            by_cases ha₁_eq : a₁ = e₂
            · exact ⟨a₂, ha₂, fun h2 => h12 (ha₁_eq.trans h2.symm)⟩
            · exact ⟨a₁, ha₁, ha₁_eq⟩
          obtain ⟨a, ⟨ha, ha_ne₁⟩, ha_ne₂⟩ := hex_a
          obtain ⟨_, _, -, -, ⟨ga, hga⟩, -⟩ := h.path a ha
          have hgaE : ga ∈ E(G) := by rw [h.eunion]; exact mem_iUnion₂.mpr ⟨a, ha, hga⟩
          have hga_not₁ : ga ∉ E(P e₁) := disjoint_left.mp (h.disj a ha e₁ he₁ ha_ne₁).1 hga
          have hga_not₂ : ga ∉ E(P e₂) := disjoint_left.mp (h.disj a ha e₂ he₂ ha_ne₂).1 hga
          have hgaA : ga ∈ A := by
            by_contra hgaA
            exact hrem ⟨ga, hgaE, not_or.mpr ⟨not_or.mpr ⟨hgaA, hga_not₂⟩, hga_not₁⟩⟩
          exact ⟨ga, ⟨hgaA, hga_not₂⟩, hga_not₁⟩
    obtain ⟨A', u', hA', hu'₀, hbdA', hw₁A', hB₁_ne, hB₂_ne⟩ := hex_A'
    have hw₁_inter' : bdry G A' ∩ (V(P e₁) \ V(G₀)) = {w₁} := by
      ext x
      simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · exact fun ⟨hx, _, hx₀⟩ => (hbdA' hx).resolve_right (fun hxu => hx₀ (hxu ▸ hu'₀))
      · rintro rfl
        exact ⟨hw₁A', hw₁_Pe₁, hw₁_not₀⟩
    obtain ⟨u₁', v₁', hl₁', hsub₁', hsub₂'⟩ := move_internal_bdry h hA' he₁ hw₁_inter'
    have hdiff_sub' : bdry G A' \ (V(P e₁) \ V(G₀)) ⊆ {u'} := by
      rintro x ⟨hx, hx_not⟩
      exact (hbdA' hx).resolve_left (fun hxw => hx_not (hxw ▸ ⟨hw₁_Pe₁, hw₁_not₀⟩))
    have hs₁' : bdry G (A' \ E(P e₁)) ⊆ {u', u₁'} :=
      hsub₁'.trans (union_subset_union_left _ hdiff_sub')
    have hs₂' : bdry G (A' ∪ E(P e₁)) ⊆ {u', v₁'} :=
      hsub₂'.trans (union_subset_union_left _ hdiff_sub')
    have hbd₁_V₀ : bdry G (A' \ E(P e₁)) ⊆ V(G₀) := by
      refine hs₁'.trans ?_
      rintro x (rfl | rfl)
      · exact hu'₀
      · exact hl₁'.left_mem
    have hc₁ : (bdry G (A' \ E(P e₁))).ncard ≤ 2 :=
      (Set.ncard_le_ncard hs₁' (Set.toFinite _)).trans (Set.ncard_insert_le _ _ |>.trans (by simp))
    have hbd₂_V₀ : bdry G (A' ∪ E(P e₁)) ⊆ V(G₀) := by
      refine hs₂'.trans ?_
      rintro x (rfl | rfl)
      · exact hu'₀
      · exact hl₁'.right_mem
    have hc₂ : (bdry G (A' ∪ E(P e₁))).ncard ≤ 2 :=
      (Set.ncard_le_ncard hs₂' (Set.toFinite _)).trans (Set.ncard_insert_le _ _ |>.trans (by simp))
    have hB₂_eq : A' \ E(P e₁) ∪ E(P e₁) = A' ∪ E(P e₁) := sdiff_union_self
    have hB₂_ne' : (E(G) \ (A' \ E(P e₁) ∪ E(P e₁))).Nonempty := hB₂_eq.symm ▸ hB₂_ne
    exact (not_both_sep_of_union_path h he₁ (sdiff_subset.trans hA') disjoint_sdiff_left
      hB₁_ne hB₂_ne' hbd₁_V₀ hc₁ (hB₂_eq ▸ hbd₂_V₀) (hB₂_eq ▸ hc₂)).elim

/-- If `bdry G A ⊆ V(P e)` (`e ∈ E(G₀)`), then `A ⊆ E(P e)` or `E(G) \ A ⊆ E(P e)`. -/
theorem subset_or_compl_subset_path (h : SubData G G₀ P) {A : Set β} (hA : A ⊆ E(G))
    {e : β} (he : e ∈ E(G₀)) (hbd : bdry G A ⊆ V(P e)) :
    A ⊆ E(P e) ∨ E(G) \ A ⊆ E(P e) := by
  by_contra! hnot
  obtain ⟨u, v, hl, ⟨hle, _, _, _, _⟩, _, hcap⟩ := h.path e he
  have hB₁_ne : (A \ E(P e)).Nonempty := not_subset.mp hnot.1
  have hB₂_ne : (E(G) \ (A \ E(P e) ∪ E(P e))).Nonempty := by
    rw [sdiff_union_self]
    obtain ⟨g, ⟨hgE, hgA⟩, hgP⟩ := not_subset.mp hnot.2
    exact ⟨g, hgE, not_or.mpr ⟨hgA, hgP⟩⟩
  have hbd_B₁ : bdry G (A \ E(P e)) ⊆ {u, v} := by
    intro x hx
    rw [← hcap]
    have hxP : x ∈ V(P e) := by
      by_contra hxP
      obtain ⟨⟨g₁, ⟨hg₁A, _⟩, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
      have hg₂A : g₂ ∉ A := fun hg₂A =>
        hg₂_not ⟨hg₂A, fun hg₂P => not_inc_of_notMem_path h he hxP hg₂P hig₂⟩
      exact hxP (hbd ⟨⟨g₁, hg₁A, hig₁⟩, g₂, ⟨hg₂E, hg₂A⟩, hig₂⟩)
    refine ⟨hxP, ?_⟩
    by_contra hx₀
    obtain ⟨⟨g₁, ⟨hg₁A, hg₁P⟩, hig₁⟩, -⟩ := hx
    exact hg₁P (inc_mem_path_of_notMem_V₀ h he hxP hx₀ (hA hg₁A) hig₁)
  have hbd_B₂ : bdry G (A ∪ E(P e)) ⊆ {u, v} := by
    intro x hx
    rw [← hcap]
    have hxP : x ∈ V(P e) := by
      by_contra hxP
      obtain ⟨⟨g₁, hg₁_in, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
      have hg₁A : g₁ ∈ A := hg₁_in.resolve_right fun hg₁P =>
        not_inc_of_notMem_path h he hxP hg₁P hig₁
      exact hxP (hbd ⟨⟨g₁, hg₁A, hig₁⟩, g₂, ⟨hg₂E, fun hg₂A => hg₂_not (Or.inl hg₂A)⟩, hig₂⟩)
    refine ⟨hxP, ?_⟩
    by_contra hx₀
    obtain ⟨-, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
    exact hg₂_not (Or.inr (inc_mem_path_of_notMem_V₀ h he hxP hx₀ hg₂E hig₂))
  have huv_V₀ : ({u, v} : Set α) ⊆ V(G₀) := by
    rintro x (rfl | rfl)
    · exact hl.left_mem
    · exact hl.right_mem
  have hc₁ : (bdry G (A \ E(P e))).ncard ≤ 2 :=
    (Set.ncard_le_ncard hbd_B₁ (Set.toFinite _)).trans (Set.ncard_insert_le _ _ |>.trans (by simp))
  have hc₂ : (bdry G (A ∪ E(P e))).ncard ≤ 2 :=
    (Set.ncard_le_ncard hbd_B₂ (Set.toFinite _)).trans (Set.ncard_insert_le _ _ |>.trans (by simp))
  have hB₂_eq : A \ E(P e) ∪ E(P e) = A ∪ E(P e) := sdiff_union_self
  exact not_both_sep_of_union_path h he (sdiff_subset.trans hA) disjoint_sdiff_left
    hB₁_ne hB₂_ne (hbd_B₁.trans huv_V₀) hc₁
    (hB₂_eq ▸ hbd_B₂.trans huv_V₀) (hB₂_eq ▸ hc₂)

/-- Associativity of `GraphWalk.append`. -/
theorem walk_append_assoc {H : Graph α β} {a b c d : α}
    (W₁ : GraphWalk H a b) (W₂ : GraphWalk H b c) (W₃ : GraphWalk H c d) :
    (W₁.append W₂).append W₃ = W₁.append (W₂.append W₃) := by
  induction W₁ with
  | nil _ => rfl
  | cons hlk rest ih => exact congrArg (GraphWalk.cons hlk) (ih W₂)

/-- Decomposing a walk at one of its edges. -/
theorem exists_decomp_of_mem_edges {H : Graph α β} {a b : α} (W : GraphWalk H a b)
    {g : β} (hg : g ∈ W.edges) :
    ∃ (x₀ y₀ : α) (hl : H.IsLink g x₀ y₀) (W₁ : GraphWalk H a x₀) (W₂ : GraphWalk H y₀ b),
      W = W₁.append (GraphWalk.cons hl W₂) := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at hg
  | @cons u v w f hlink rest ih =>
    simp only [GraphWalk.edges, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨u, v, hlink, .nil hlink.left_mem, rest, rfl⟩
    · obtain ⟨x₀, y₀, hl, W₁, W₂, rfl⟩ := ih hg
      exact ⟨x₀, y₀, hl, .cons hlink W₁, W₂, rfl⟩

/-- When `A ⊆ E(P e)` is nonempty and `(bdry G A).ncard ≤ 2`, `A` is the edge set of a subpath `Q`
of `P e` between the two distinct vertices of `bdry G A`. -/
theorem sep_of_subset_path (h : SubData G G₀ P) {e : β} (he : e ∈ E(G₀))
    {A : Set β} (hA : A ⊆ E(P e)) (hc : (bdry G A).ncard ≤ 2) (hne : A.Nonempty) :
    ∃ (x y : α) (Q : Graph α β),
      x ≠ y ∧ bdry G A = {x, y} ∧ Q ≤ P e ∧
      IsGraphPathWithEnds G Q x y ∧ A = E(Q) ∧ verts G A = V(Q) := by
  obtain ⟨u, v, hl, ⟨hle, W, hs, hV, hE⟩, _, hcap⟩ := h.path e he
  have hA_G : A ⊆ E(G) := hA.trans hle.edgeSet_mono
  obtain ⟨g₀, hg₀A⟩ := hne
  have hg₀W : g₀ ∈ W.edges := by
    have : g₀ ∈ E(P e) := hA hg₀A
    rwa [hE] at this
  obtain ⟨x₀, y₀, hl₀, W₁, W₂, hW_eq⟩ := exists_decomp_of_mem_edges W hg₀W
  have hsupp_eq : W.support = W₁.support ++ W₂.support := by
    rw [hW_eq, GraphWalk.support_append]
    rfl
  have hnd_12 : (W₁.support ++ W₂.support).Nodup := hsupp_eq ▸ hs
  have hd_12 := List.nodup_append.mp hnd_12
  obtain ⟨fu, hfuE, hfu_not, hifu⟩ := h.exists_other_edge hl
  obtain ⟨fv, hfvE, hfv_not, hifv⟩ := h.exists_other_edge hl.symm
  have hu_out : u ∈ verts G (E(G) \ A) := ⟨fu, ⟨hfuE, fun h => hfu_not (hA h)⟩, hifu⟩
  have hv_out : v ∈ verts G (E(G) \ A) := ⟨fv, ⟨hfvE, fun h => hfv_not (hA h)⟩, hifv⟩
  have hx₀_in : x₀ ∈ verts G A := ⟨g₀, hg₀A, y₀, hl₀.mono hle⟩
  have hy₀_in : y₀ ∈ verts G A := ⟨g₀, hg₀A, x₀, (hl₀.mono hle).symm⟩
  have hex_x : ∃ x ∈ W₁.support, x ∈ bdry G A := by
    by_cases hu_in : u ∈ verts G A
    · exact ⟨u, W₁.start_mem_support, hu_in, hu_out⟩
    · obtain ⟨W₁G, hsupp₁, _⟩ := W₁.reverse.exists_transfer (G' := G)
        (fun _ _ _ _ hlk => hlk.mono hle)
        (fun z hz => hle.vertexSet_mono (W₁.reverse.mem_vertexSet_of_mem_support hz))
      obtain ⟨x, hxG, _, hxbd⟩ := exists_bdry_of_walk W₁G hx₀_in hu_in
      rw [hsupp₁, GraphWalk.support_reverse, List.mem_reverse] at hxG
      exact ⟨x, hxG, hxbd⟩
  have hex_y : ∃ y ∈ W₂.support, y ∈ bdry G A := by
    by_cases hv_in : v ∈ verts G A
    · exact ⟨v, W₂.end_mem_support, hv_in, hv_out⟩
    · obtain ⟨W₂G, hsupp₂, _⟩ := W₂.exists_transfer (G' := G)
        (fun _ _ _ _ hlk => hlk.mono hle)
        (fun z hz => hle.vertexSet_mono (W₂.mem_vertexSet_of_mem_support hz))
      obtain ⟨y, hyG, _, hybd⟩ := exists_bdry_of_walk W₂G hy₀_in hv_in
      rw [hsupp₂] at hyG
      exact ⟨y, hyG, hybd⟩
  obtain ⟨x, hxW₁, hx_bd⟩ := hex_x
  obtain ⟨y, hyW₂, hy_bd⟩ := hex_y
  have hxy : x ≠ y := fun heq => hd_12.2.2 x hxW₁ y hyW₂ heq
  have hbd_eq : bdry G A = {x, y} := by
    have hsub : ({x, y} : Set α) ⊆ bdry G A := by
      rintro z (rfl | rfl)
      · exact hx_bd
      · exact hy_bd
    exact (Set.eq_of_subset_of_ncard_le hsub
      (by rw [Set.ncard_pair hxy]; exact hc) (finite_bdry h A)).symm
  obtain ⟨W_ux, W_xx₀, hW₁_eq⟩ := W₁.exists_append_of_mem hxW₁
  obtain ⟨W_y₀y, W_yv, hW₂_eq⟩ := W₂.exists_append_of_mem hyW₂
  let W_mid : GraphWalk (P e) x y := W_xx₀.append (GraphWalk.cons hl₀ W_y₀y)
  have hW_full : W = W_ux.append (W_mid.append W_yv) := by
    dsimp [W_mid]
    rw [hW_eq, hW₁_eq, hW₂_eq, walk_append_assoc]
    exact congrArg (W_ux.append ·) (walk_append_assoc W_xx₀ (GraphWalk.cons hl₀ W_y₀y) W_yv).symm
  have hs_full : (W_ux.append (W_mid.append W_yv)).IsSimple := hW_full ▸ hs
  have hs_ux : W_ux.IsSimple := (GM09.isSimple_of_append hs_full).1
  have hs_mid_yv : (W_mid.append W_yv).IsSimple := (GM09.isSimple_of_append hs_full).2
  have hs_mid : W_mid.IsSimple := (GM09.isSimple_of_append hs_mid_yv).1
  have hs_yv : W_yv.IsSimple := (GM09.isSimple_of_append hs_mid_yv).2
  have hnd_ux_rest : (W_ux.support ++ (W_mid.append W_yv).support.tail).Nodup := by
    have h1 : (W_ux.append (W_mid.append W_yv)).support.Nodup := hs_full
    rwa [GraphWalk.support_append] at h1
  have hd_ux_rest := List.nodup_append.mp hnd_ux_rest
  have hnd_mid_yv : (W_mid.support ++ W_yv.support.tail).Nodup := by
    have h1 : (W_mid.append W_yv).support.Nodup := hs_mid_yv
    rwa [GraphWalk.support_append] at h1
  have hd_mid_yv := List.nodup_append.mp hnd_mid_yv
  have hmemE : ∀ {g : β}, g ∈ W.edges → g ∈ E(G) := fun {g} hg =>
    hle.edgeSet_mono (by rw [hE]; exact hg)
  have hincG : ∀ {g z}, (P e).Inc g z → G.Inc g z := fun ⟨w, hw⟩ => ⟨w, hw.mono hle⟩
  have hmid_pure : ∀ e₁ ∈ W_mid.edges, ∀ e₂ ∈ W_mid.edges, e₁ ∈ A ↔ e₂ ∈ A := by
    refine walk_pure W_mid hs_mid fun z hz hzx hzy e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
    have hz_not_bd : z ∉ bdry G A := by
      rw [hbd_eq]
      exact not_or.mpr ⟨hzx, hzy⟩
    have he₁W : e₁ ∈ W.edges := by
      rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append]
      exact List.mem_append_right _ (List.mem_append_left _ he₁)
    have he₂W : e₂ ∈ W.edges := by
      rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append]
      exact List.mem_append_right _ (List.mem_append_left _ he₂)
    constructor <;> intro h₁ <;> by_contra h₂
    · exact hz_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
    · exact hz_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩
  have hg₀_mid : g₀ ∈ W_mid.edges := by
    dsimp [W_mid]
    rw [GraphWalk.edges_append]
    exact List.mem_append_right _ List.mem_cons_self
  have hmid_sub_A : ∀ a ∈ W_mid.edges, a ∈ A :=
    fun a ha => (hmid_pure a ha g₀ hg₀_mid).mpr hg₀A
  have hux_disj_A : ∀ a ∈ W_ux.edges, a ∉ A := by
    intro a ha
    have hux_ne : u ≠ x := by
      rintro rfl
      have hlen0 := GraphWalk.IsSimple.length_eq_zero hs_ux
      exact List.ne_nil_of_mem ha (List.length_eq_zero_iff.mp hlen0)
    have huy : u ≠ y := by
      rintro rfl
      exact hd_12.2.2 u W₁.start_mem_support u hyW₂ rfl
    have hu_not_bd : u ∉ bdry G A := by
      rw [hbd_eq]
      exact not_or.mpr ⟨hux_ne, huy⟩
    have hu_not_in : u ∉ verts G A := fun hu_in => hu_not_bd ⟨hu_in, hu_out⟩
    obtain ⟨gu, hgu, hiu⟩ := exists_edge_at_start W_ux hux_ne
    have hgu_not_A : gu ∉ A := fun h => hu_not_in ⟨gu, h, hincG hiu⟩
    have hux_pure : ∀ e₁ ∈ W_ux.edges, ∀ e₂ ∈ W_ux.edges, e₁ ∈ A ↔ e₂ ∈ A := by
      refine walk_pure W_ux hs_ux fun z hz hzu hzx e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
      have hzy : z ≠ y := by
        rintro rfl
        have hy_rest : z ∈ (W_mid.append W_yv).support := by
          rw [GraphWalk.mem_support_append]
          exact Or.inl W_mid.end_mem_support
        rw [(W_mid.append W_yv).support_eq_cons] at hy_rest
        rcases List.mem_cons.mp hy_rest with rfl | hy_tail
        · exact hzx rfl
        · exact hd_ux_rest.2.2 z hz z hy_tail rfl
      have hz_not_bd : z ∉ bdry G A := by
        rw [hbd_eq]
        exact not_or.mpr ⟨hzx, hzy⟩
      have he₁W : e₁ ∈ W.edges := by
        rw [hW_full, GraphWalk.edges_append]
        exact List.mem_append_left _ he₁
      have he₂W : e₂ ∈ W.edges := by
        rw [hW_full, GraphWalk.edges_append]
        exact List.mem_append_left _ he₂
      constructor <;> intro h₁ <;> by_contra h₂
      · exact hz_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
      · exact hz_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩
    exact fun haA => hgu_not_A ((hux_pure a ha gu hgu).mp haA)
  have hyv_disj_A : ∀ a ∈ W_yv.edges, a ∉ A := by
    intro a ha
    have hyv_ne : y ≠ v := by
      rintro rfl
      have hlen0 := GraphWalk.IsSimple.length_eq_zero hs_yv
      exact List.ne_nil_of_mem ha (List.length_eq_zero_iff.mp hlen0)
    have hxv : x ≠ v := by
      rintro rfl
      exact hd_12.2.2 x hxW₁ x W₂.end_mem_support rfl
    have hv_not_bd : v ∉ bdry G A := by
      rw [hbd_eq]
      exact not_or.mpr ⟨Ne.symm hxv, Ne.symm hyv_ne⟩
    have hv_not_in : v ∉ verts G A := fun hv_in => hv_not_bd ⟨hv_in, hv_out⟩
    obtain ⟨gv, hgv_rev, hiv⟩ := exists_edge_at_start W_yv.reverse hyv_ne.symm
    have hgv : gv ∈ W_yv.edges := by
      rw [GraphWalk.edges_reverse] at hgv_rev
      exact List.mem_reverse.mp hgv_rev
    have hgv_not_A : gv ∉ A := fun h => hv_not_in ⟨gv, h, hincG hiv⟩
    have hyv_pure : ∀ e₁ ∈ W_yv.edges, ∀ e₂ ∈ W_yv.edges, e₁ ∈ A ↔ e₂ ∈ A := by
      refine walk_pure W_yv hs_yv fun z hz hzy hzv e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
      have hzx : z ≠ x := by
        rintro rfl
        have hx_mid : z ∈ W_mid.support := W_mid.start_mem_support
        rw [W_yv.support_eq_cons] at hz
        rcases List.mem_cons.mp hz with rfl | hz_tail
        · exact hzy rfl
        · exact hd_mid_yv.2.2 z hx_mid z hz_tail rfl
      have hz_not_bd : z ∉ bdry G A := by
        rw [hbd_eq]
        exact not_or.mpr ⟨hzx, hzy⟩
      have he₁W : e₁ ∈ W.edges := by
        rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append]
        exact List.mem_append_right _ (List.mem_append_right _ he₁)
      have he₂W : e₂ ∈ W.edges := by
        rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append]
        exact List.mem_append_right _ (List.mem_append_right _ he₂)
      constructor <;> intro h₁ <;> by_contra h₂
      · exact hz_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
      · exact hz_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩
    exact fun haA => hgv_not_A ((hyv_pure a ha gv hgv).mp haA)
  let Q : Graph α β := walkSubgraph W_mid
  have hQ_le_Pe : Q ≤ P e := walkSubgraph_le W_mid
  have hQ_path : IsGraphPathWithEnds G Q x y :=
    (isGraphPathWithEnds_walkSubgraph hs_mid).of_le (hQ_le_Pe.trans hle)
  have hA_eq_EQ : A = E(Q) := by
    rw [edgeSet_walkSubgraph]
    ext a
    simp only [mem_ofPred_eq]
    constructor
    · intro haA
      have haW : a ∈ W.edges := by
        have : a ∈ E(P e) := hA haA
        rwa [hE] at this
      rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append] at haW
      rcases List.mem_append.mp haW with hux | hrest
      · exact (hux_disj_A a hux haA).elim
      · rcases List.mem_append.mp hrest with hmid | hyv
        · exact hmid
        · exact (hyv_disj_A a hyv haA).elim
    · exact fun ha => hmid_sub_A a ha
  have hverts_eq_VQ : verts G A = V(Q) := by
    rw [hA_eq_EQ, edgeSet_walkSubgraph, vertexSet_walkSubgraph]
    ext z
    simp only [verts, mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, hia⟩
      have haQ : a ∈ E(Q) := by rw [edgeSet_walkSubgraph]; exact ha
      exact inc_mem_support W_mid ha (h.inc_path hle (hQ_le_Pe.edgeSet_mono haQ) hia)
    · intro hz
      by_cases hzx : z = x
      · subst hzx
        obtain ⟨a, ha, hia⟩ := exists_edge_at_start W_mid hxy
        exact ⟨a, ha, hincG hia⟩
      · by_cases hzy : z = y
        · subst hzy
          obtain ⟨a, ha_rev, hia⟩ := exists_edge_at_start W_mid.reverse hxy.symm
          rw [GraphWalk.edges_reverse] at ha_rev
          exact ⟨a, List.mem_reverse.mp ha_rev, hincG hia⟩
        · obtain ⟨a, ha, _, _, _, hia, _⟩ := exists_two_edges_at_inner W_mid hs_mid hz hzx hzy
          exact ⟨a, ha, hincG hia⟩
  exact ⟨x, y, Q, hxy, hbd_eq, hQ_le_Pe, hQ_path, hA_eq_EQ, hverts_eq_VQ⟩

/-- **General 2-Separation Theorem for Subdivisions of Simple 3-Connected Graphs**:
For any `A ⊆ E(G)` with `(bdry G A).ncard ≤ 2`, `A.Nonempty`, and `(E(G) \ A).Nonempty`, either
`A` or `E(G) \ A` is the edge set of a subpath `Q` of some subdivision path `P e` (`e ∈ E(G₀)`)
joining the two vertices of `bdry G A`. -/
theorem sep_general (h : SubData G G₀ P) {A : Set β} (hA : A ⊆ E(G))
    (hc : (bdry G A).ncard ≤ 2) (hne : A.Nonempty) (hne' : (E(G) \ A).Nonempty) :
    ∃ (e : β) (x y : α) (Q : Graph α β),
      e ∈ E(G₀) ∧ x ≠ y ∧ bdry G A = {x, y} ∧ Q ≤ P e ∧
      IsGraphPathWithEnds G Q x y ∧
      ((A = E(Q) ∧ verts G A = V(Q)) ∨
       (E(G) \ A = E(Q) ∧ verts G (E(G) \ A) = V(Q))) := by
  obtain ⟨e, he, hbd_Pe⟩ := bdry_subset_path h hA hc hne hne'
  rcases subset_or_compl_subset_path h hA he hbd_Pe with hsub | hsub
  · obtain ⟨x, y, Q, hxy, hbd_eq, hQ_le, hQ_path, hAE, hAV⟩ :=
      sep_of_subset_path h he hsub hc hne
    exact ⟨e, x, y, Q, he, hxy, hbd_eq, hQ_le, hQ_path, Or.inl ⟨hAE, hAV⟩⟩
  · have hc' : (bdry G (E(G) \ A)).ncard ≤ 2 := by rwa [bdry_compl hA]
    obtain ⟨x, y, Q, hxy, hbd_eq, hQ_le, hQ_path, hAE, hAV⟩ :=
      sep_of_subset_path h he hsub hc' hne'
    rw [bdry_compl hA] at hbd_eq
    exact ⟨e, x, y, Q, he, hxy, hbd_eq, hQ_le, hQ_path, Or.inr ⟨hAE, hAV⟩⟩

/-- Every vertex of a subdivision of a simple 3-connected graph is incident with an edge. -/
theorem exists_inc_of_mem_V (h : SubData G G₀ P) {x : α} (hx : x ∈ V(G)) :
    ∃ g ∈ E(G), G.Inc g x := by
  have hex_P : ∃ e ∈ E(G₀), x ∈ V(P e) := by
    rw [h.vunion] at hx
    rcases hx with hx₀ | hxP
    · obtain ⟨e, _, _, _, _, _, ⟨y, hl⟩, _, _⟩ :=
        IsSimpleThreeConnected.exists_three_edges h.simple hx₀
      obtain ⟨u, v, hlu, _, _, hcap⟩ := h.path e hl.edge_mem
      have hx_uv : x = u ∨ x = v := G₀.eq_or_eq_of_isLink_of_isLink hl hlu
      have hx_cap : x ∈ V(P e) ∩ V(G₀) := by
        rw [hcap]
        exact hx_uv
      exact ⟨e, hl.edge_mem, hx_cap.1⟩
    · obtain ⟨e, he, hxP⟩ := mem_iUnion₂.mp hxP
      exact ⟨e, he, hxP⟩
  obtain ⟨e, he, hxP⟩ := hex_P
  obtain ⟨u, v, hl, ⟨hle, W, hs, hV, hE⟩, ⟨g₀, hg₀⟩, _⟩ := h.path e he
  have huv : u ≠ v := by
    rintro rfl
    have hlen0 := GraphWalk.IsSimple.length_eq_zero hs
    have hg₀W : g₀ ∈ W.edges := by rwa [hE] at hg₀
    exact List.ne_nil_of_mem hg₀W (List.length_eq_zero_iff.mp hlen0)
  have hxW : x ∈ W.support := by rwa [hV] at hxP
  by_cases hxu : x = u
  · subst hxu
    obtain ⟨g, hg, w, hlk⟩ := exists_edge_at_start W huv
    have hgP : g ∈ E(P e) := by rw [hE]; exact hg
    exact ⟨g, hle.edgeSet_mono hgP, w, hlk.mono hle⟩
  · by_cases hxv : x = v
    · subst hxv
      obtain ⟨g, hg_rev, w, hlk⟩ := exists_edge_at_start W.reverse huv.symm
      rw [GraphWalk.edges_reverse] at hg_rev
      have hgP : g ∈ E(P e) := by rw [hE]; exact List.mem_reverse.mp hg_rev
      exact ⟨g, hle.edgeSet_mono hgP, w, hlk.mono hle⟩
    · obtain ⟨g, hg, _, _, _, ⟨w, hlk⟩, _⟩ := exists_two_edges_at_inner W hs hxW hxu hxv
      have hgP : g ∈ E(P e) := by rw [hE]; exact hg
      exact ⟨g, hle.edgeSet_mono hgP, w, hlk.mono hle⟩

end SubDataSepGeneral

/-! ## 2. Tangle Orientation of Path Separations -/

/-- Left side of the canonical hypergraph separation of `Γ.toHypergraph` induced by an edge set
`E₀ ⊆ Γ.E`. -/
noncomputable def drawingEdgeSepA (Γ : Drawing S) (E₀ : Set (Set S)) : Hypergraph S (Set S) where
  vertexSet := verts Γ.toGraph E₀
  edgeSet := E₀ ∩ Γ.E
  Inc e v := Γ.toHypergraph.Inc e v ∧ e ∈ E₀
  vertex_mem_of_inc e _ h := ⟨e, h.2, inc_of_mem_closure h.1.1 h.1.2.2 h.1.2.1⟩
  edge_mem_of_inc _ _ h := ⟨h.2, h.1.1⟩
  vertexSet_finite := Γ.finite_V.subset (fun _ ⟨_, _, _, hl⟩ => hl.left_mem)
  edgeSet_finite := Γ.finite_edges.subset inter_subset_right

/-- Right side of the canonical hypergraph separation of `Γ.toHypergraph` induced by an edge set
`E₀ ⊆ Γ.E`. -/
noncomputable def drawingEdgeSepB (Γ : Drawing S) (E₀ : Set (Set S)) : Hypergraph S (Set S) where
  vertexSet := (Γ.V \ verts Γ.toGraph E₀) ∪ verts Γ.toGraph (Γ.E \ E₀)
  edgeSet := Γ.E \ E₀
  Inc e v := Γ.toHypergraph.Inc e v ∧ e ∉ E₀
  vertex_mem_of_inc e _ h :=
    Or.inr ⟨e, ⟨h.1.1, h.2⟩, inc_of_mem_closure h.1.1 h.1.2.2 h.1.2.1⟩
  edge_mem_of_inc _ _ h := ⟨h.1.1, h.2⟩
  vertexSet_finite :=
    Γ.finite_V.subset (union_subset sdiff_subset (fun _ ⟨_, _, _, hl⟩ => hl.left_mem))
  edgeSet_finite := Γ.finite_edges.subset sdiff_subset

omit [T2Space S] in
theorem drawingEdgeSepA_le (Γ : Drawing S) (E₀ : Set (Set S)) :
    drawingEdgeSepA Γ E₀ ≤ Γ.toHypergraph where
  vertexSet_subset := fun _ ⟨_, _, _, hl⟩ => hl.left_mem
  edgeSet_subset := inter_subset_right
  ends_eq e he := by
    ext v
    exact ⟨fun h => ⟨h, he.1⟩, fun h => h.1⟩

omit [T2Space S] in
theorem drawingEdgeSepB_le (Γ : Drawing S) (E₀ : Set (Set S)) :
    drawingEdgeSepB Γ E₀ ≤ Γ.toHypergraph where
  vertexSet_subset := union_subset sdiff_subset (fun _ ⟨_, _, _, hl⟩ => hl.left_mem)
  edgeSet_subset := sdiff_subset
  ends_eq e he := by
    ext v
    exact ⟨fun h => ⟨h, he.2⟩, fun h => h.1⟩

omit [T2Space S] in
theorem isSeparation_drawingEdgeSep (Γ : Drawing S) (E₀ : Set (Set S)) :
    Γ.toHypergraph.IsSeparation (drawingEdgeSepA Γ E₀) (drawingEdgeSepB Γ E₀) := by
  rw [isSeparation_iff_of_le (drawingEdgeSepA_le Γ E₀) (drawingEdgeSepB_le Γ E₀)]
  refine ⟨?_, ?_, ?_⟩
  · change verts Γ.toGraph E₀ ∪ ((Γ.V \ verts Γ.toGraph E₀) ∪ verts Γ.toGraph (Γ.E \ E₀)) = Γ.V
    have hs1 : verts Γ.toGraph E₀ ⊆ Γ.V := fun _ ⟨_, _, _, hl⟩ => hl.left_mem
    have hs2 : verts Γ.toGraph (Γ.E \ E₀) ⊆ Γ.V := fun _ ⟨_, _, _, hl⟩ => hl.left_mem
    rw [← Set.union_assoc, union_sdiff_self, union_eq_self_of_subset_left hs1,
      union_eq_self_of_subset_right hs2]
  · change (E₀ ∩ Γ.E) ∪ (Γ.E \ E₀) = Γ.E
    rw [Set.inter_comm, inter_union_sdiff]
  · change (E₀ ∩ Γ.E) ∩ (Γ.E \ E₀) = ∅
    ext e
    simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false, not_and]
    exact fun h1 _ h2 => h2 h1.1

omit [T2Space S] in
theorem inter_vertexSet_drawingEdgeSep (Γ : Drawing S) (E₀ : Set (Set S)) :
    (drawingEdgeSepA Γ E₀ ∩ drawingEdgeSepB Γ E₀).vertexSet = bdry Γ.toGraph E₀ := by
  change verts Γ.toGraph E₀ ∩ ((Γ.V \ verts Γ.toGraph E₀) ∪ verts Γ.toGraph (Γ.E \ E₀)) =
    verts Γ.toGraph E₀ ∩ verts Γ.toGraph (Γ.E \ E₀)
  ext x
  simp only [mem_inter_iff, mem_union, mem_sdiff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.resolve_left (fun h => h.2 h1)⟩,
    fun ⟨h1, h2⟩ => ⟨h1, Or.inr h2⟩⟩

omit [T2Space S] in
/-- For a simple walk `W` from `x` to `y` with `bdry Γ.toGraph {g | g ∈ W.edges} ⊆ {x, y}`, every
suffix `W₂` (`W = W₁.append W₂`, `W₂ : GraphWalk Γ.toGraph u y`) has
`bdry Γ.toGraph {g | g ∈ W₂.edges} ⊆ {u, y}`. -/
theorem suffix_bdry_subset {Γ : Drawing S} {x u y : S}
    (W₁ : GraphWalk Γ.toGraph x u) (W₂ : GraphWalk Γ.toGraph u y)
    (hs : (W₁.append W₂).IsSimple)
    (hbd : bdry Γ.toGraph {g | g ∈ (W₁.append W₂).edges} ⊆ {x, y}) :
    bdry Γ.toGraph {g | g ∈ W₂.edges} ⊆ {u, y} := by
  have hnd : (W₁.support ++ W₂.support.tail).Nodup := by
    have h1 : (W₁.append W₂).support.Nodup := hs
    rwa [GraphWalk.support_append] at h1
  have hd := List.nodup_append.mp hnd
  intro z ⟨⟨g₁, hg₁, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩
  have hzW₂ : z ∈ W₂.support := inc_mem_support W₂ hg₁ hig₁
  by_contra hz_not
  have hzu : z ≠ u := fun h => hz_not (Or.inl h)
  have hzy : z ≠ y := fun h => hz_not (Or.inr h)
  have hz_tail : z ∈ W₂.support.tail := by
    rw [W₂.support_eq_cons] at hzW₂
    exact (List.mem_cons.mp hzW₂).resolve_left hzu
  have hg₂_not₁ : g₂ ∉ W₁.edges := by
    intro hg₂_1
    have hzW₁ : z ∈ W₁.support := inc_mem_support W₁ hg₂_1 hig₂
    exact hd.2.2 z hzW₁ z hz_tail rfl
  have hg₁_full : g₁ ∈ (W₁.append W₂).edges := by
    rw [GraphWalk.edges_append]
    exact List.mem_append_right _ hg₁
  have hg₂_not_full : g₂ ∉ (W₁.append W₂).edges := by
    rw [GraphWalk.edges_append]
    exact fun h => (List.mem_append.mp h).elim hg₂_not₁ hg₂_not
  have hz_xy : z ∈ ({x, y} : Set S) :=
    hbd ⟨⟨g₁, hg₁_full, hig₁⟩, g₂, ⟨hg₂E, hg₂_not_full⟩, hig₂⟩
  rcases hz_xy with rfl | rfl
  · exact hd.2.2 z W₁.start_mem_support z hz_tail rfl
  · exact hzy rfl

omit [T2Space S] in
/-- Along any walk `W : GraphWalk Γ.toGraph u y` whose every suffix `W_b` (`W = W_a.append W_b`)
has boundary `⊆ {start of W_b, y}`, the separation `(drawingEdgeSepA, drawingEdgeSepB)` of `W.edges`
belongs to the tangle `T` (when `4 ≤ ord`). -/
theorem walk_edgeSep_mem_tangle {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph ord T) (hord : 4 ≤ ord)
    {u y : S} (W : GraphWalk Γ.toGraph u y)
    (hsuff : ∀ ⦃w : S⦄ (W_a : GraphWalk Γ.toGraph u w) (W_b : GraphWalk Γ.toGraph w y),
      W = W_a.append W_b → bdry Γ.toGraph {g | g ∈ W_b.edges} ⊆ {w, y}) :
    (drawingEdgeSepA Γ {g | g ∈ W.edges}, drawingEdgeSepB Γ {g | g ∈ W.edges}) ∈ T := by
  induction W with
  | @nil u hu =>
    have hemp : {g : Set S | g ∈ (GraphWalk.nil hu : GraphWalk Γ.toGraph u u).edges} = ∅ := by
      ext g; simp [GraphWalk.edges]
    rw [hemp]
    have hsep := isSeparation_drawingEdgeSep Γ ∅
    have hbd_emp : bdry Γ.toGraph ∅ = ∅ := by
      ext z; simp [bdry, verts]
    have hord0 : separationOrder (drawingEdgeSepA Γ ∅) (drawingEdgeSepB Γ ∅) < ord := by
      rw [separationOrder, inter_vertexSet_drawingEdgeSep, hbd_emp, Set.ncard_empty]
      omega
    rcases hT.axiom1 hsep hord0 with h | h
    · exact h
    · exfalso
      refine hT.axiom3 h ?_
      change (Γ.V \ verts Γ.toGraph ∅) ∪ verts Γ.toGraph (Γ.E \ ∅) = Γ.V
      have hv0 : verts Γ.toGraph ∅ = ∅ := by ext z; simp [verts]
      have hsub : verts Γ.toGraph (Γ.E \ ∅) ⊆ Γ.V := fun _ ⟨_, _, _, hl⟩ => hl.left_mem
      rw [hv0, sdiff_empty, union_eq_self_of_subset_right hsub]
  | @cons u v y e hlink rest ih =>
    have hrest_mem : (drawingEdgeSepA Γ {g | g ∈ rest.edges},
        drawingEdgeSepB Γ {g | g ∈ rest.edges}) ∈ T :=
      ih fun w W_a W_b h_eq =>
        hsuff (GraphWalk.cons hlink W_a) W_b (by rw [h_eq]; rfl)
    have hends_sub : Γ.toHypergraph.ends e ⊆ {u, v} := by
      intro z hz
      have hinc : Γ.toGraph.Inc e z := inc_of_mem_closure hz.1 hz.2.2 hz.2.1
      obtain ⟨w, hlk⟩ := hinc
      exact Γ.toGraph.eq_or_eq_of_isLink_of_isLink hlk hlink
    have he_size : edgeSize Γ.toHypergraph e < ord := by
      have hle : (Γ.toHypergraph.ends e).ncard ≤ 2 :=
        (Set.ncard_le_ncard hends_sub (Set.toFinite _)).trans
          (Set.ncard_insert_le u {v} |>.trans (by simp))
      unfold edgeSize
      omega
    have hKe_mem : (edgeHypergraph Γ.toHypergraph e, Γ.toHypergraph.deleteEdges {e}) ∈ T :=
      (GM10.theorem_2_7_proof (by omega) hT.isSeparation hT.order_lt hT.axiom1 hT.axiom2).mp
        hT e hlink.edge_mem he_size
    let A₀ := drawingEdgeSepA Γ {g | g ∈ rest.edges}
    let B₀ := drawingEdgeSepB Γ {g | g ∈ rest.edges}
    let Ke := edgeHypergraph Γ.toHypergraph e
    let De := Γ.toHypergraph.deleteEdges {e}
    have hbd_rest : bdry Γ.toGraph {g | g ∈ rest.edges} ⊆ {v, y} :=
      hsuff (GraphWalk.cons hlink (.nil hlink.right_mem)) rest rfl
    have hinter_sub : ((A₀ ∪ Ke) ∩ (B₀ ∩ De)).vertexSet ⊆ {u, v, y} := by
      intro z ⟨hzA, hzB, _⟩
      rcases hzA with hzA₀ | hzKe
      · have hz_bd : z ∈ bdry Γ.toGraph {g | g ∈ rest.edges} := by
          rw [← inter_vertexSet_drawingEdgeSep]
          exact ⟨hzA₀, hzB⟩
        rcases hbd_rest hz_bd with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rcases hends_sub hzKe with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    have hord_union : separationOrder (A₀ ∪ Ke) (B₀ ∩ De) < ord := by
      have hle : ((A₀ ∪ Ke) ∩ (B₀ ∩ De)).vertexSet.ncard ≤ 3 :=
        (Set.ncard_le_ncard hinter_sub (Set.toFinite _)).trans
          ((Set.ncard_insert_le u {v, y}).trans
            (Nat.add_le_add_right ((Set.ncard_insert_le v {y}).trans (by simp)) 1))
      unfold separationOrder
      omega
    have hunion_mem : (A₀ ∪ Ke, B₀ ∩ De) ∈ T :=
      GM10.theorem_2_2_proof hT hrest_mem hKe_mem hord_union
    let E₁ : Set (Set S) := {g | g ∈ (GraphWalk.cons hlink rest).edges}
    have hbd₁ : bdry Γ.toGraph E₁ ⊆ {u, y} :=
      hsuff (.nil hlink.left_mem) (GraphWalk.cons hlink rest) rfl
    have hord₁ : separationOrder (drawingEdgeSepA Γ E₁) (drawingEdgeSepB Γ E₁) < ord := by
      rw [separationOrder, inter_vertexSet_drawingEdgeSep]
      have hle : (bdry Γ.toGraph E₁).ncard ≤ 2 :=
        (Set.ncard_le_ncard hbd₁ (Set.toFinite _)).trans
          (Set.ncard_insert_le u {y} |>.trans (by simp))
      omega
    have hE₁_sub : (drawingEdgeSepA Γ E₁).edgeSet ⊆ (A₀ ∪ Ke).edgeSet := by
      rintro g ⟨hg, hgE⟩
      simp only [E₁, GraphWalk.edges, List.mem_cons, mem_ofPred_eq] at hg
      rcases hg with rfl | hg_rest
      · exact Or.inr (mem_singleton g)
      · exact Or.inl ⟨hg_rest, hgE⟩
    exact GraphMinor.GM10.theorem_2_9_proof hT hunion_mem (isSeparation_drawingEdgeSep Γ E₁) hord₁
      (Or.inr (Or.inr ⟨by omega, hE₁_sub⟩))

omit [T2Space S] in
/-- Any separation `(A, B)` of `Γ.toHypergraph` of order `< ord` (`4 ≤ ord`) whose left-hand edge
set `A.edgeSet` is contained in the edge set `E(Q)` of a path `Q` (`IsGraphPathWithEnds Γ.toGraph Q x y`)
with `bdry Γ.toGraph E(Q) ⊆ {x, y}` belongs to the tangle `T`. -/
theorem path_sep_mem_tangle {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph ord T) (hord : 4 ≤ ord)
    {x y : S} {Q : Graph S (Set S)} (hQ : IsGraphPathWithEnds Γ.toGraph Q x y)
    (hbd : bdry Γ.toGraph E(Q) ⊆ {x, y})
    {A B : Hypergraph S (Set S)} (hsep : Γ.toHypergraph.IsSeparation A B)
    (hAB_ord : separationOrder A B < ord) (hAE : A.edgeSet ⊆ E(Q)) :
    (A, B) ∈ T := by
  obtain ⟨hle, W, hs, _, hE⟩ := hQ
  obtain ⟨W_Γ, hsupp, hedges⟩ := W.exists_transfer (G' := Γ.toGraph)
    (fun _ _ _ _ hlk => hlk.mono hle)
    (fun z hz => hle.vertexSet_mono (W.mem_vertexSet_of_mem_support hz))
  have hs_Γ : W_Γ.IsSimple := by
    change W_Γ.support.Nodup
    rw [hsupp]
    exact hs
  have hEQ : E(Q) = {g | g ∈ W_Γ.edges} := by
    rw [hE, hedges]
  have hbd_W : bdry Γ.toGraph {g | g ∈ W_Γ.edges} ⊆ {x, y} := hEQ ▸ hbd
  have hmem_EQ : (drawingEdgeSepA Γ E(Q), drawingEdgeSepB Γ E(Q)) ∈ T := by
    rw [hEQ]
    exact walk_edgeSep_mem_tangle hT hord W_Γ fun w W_a W_b h_eq =>
      suffix_bdry_subset W_a W_b (h_eq ▸ hs_Γ) (h_eq ▸ hbd_W)
  have hA_sub : A.edgeSet ⊆ (drawingEdgeSepA Γ E(Q)).edgeSet :=
    fun e he => ⟨hAE he, hsep.left_le.edgeSet_subset he⟩
  exact GraphMinor.GM10.theorem_2_9_proof hT hmem_EQ hsep hAB_ord (Or.inr (Or.inr ⟨by omega, hA_sub⟩))

/-! ## 3. Rigidity of `Γ` in `Δ₀` -/

/-- For an `O`-arc `F ⊆ Δ₀` inside a closed disc `Δ₀` in a sphere `S`, `F` bounds two closed discs
`Δ₁, Δ₂` in `S` such that `Δ₁ ⊆ Δ₀` (and `Δ₁` is the unique closed disc in `Δ₀` bounded by `F`)
and `subBd Δ₀ ⊆ Δ₂`. -/
theorem sphere_oArc_discs_in_Δ₀ (hS : IsSphere S) {Δ₀ F : Set S}
    (hΔ₀ : IsClosedDisc Δ₀) (hF_sub : F ⊆ Δ₀) (hF : IsOArc F) :
    ∃ Δ₁ Δ₂ : Set S,
      Δ₁ ≠ Δ₂ ∧ IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      discBd Δ₁ = F ∧ discBd Δ₂ = F ∧ subBd Δ₁ = F ∧ subBd Δ₂ = F ∧
      Δ₁ ∪ Δ₂ = univ ∧ Δ₁ ∩ Δ₂ = F ∧
      closure (univ \ Δ₁) = Δ₂ ∧ closure (univ \ Δ₂) = Δ₁ ∧
      Δ₁ ⊆ Δ₀ ∧ subBd Δ₀ ⊆ Δ₂ ∧
      (∀ Δ : Set S, IsClosedDisc Δ → subBd Δ = F → Δ = Δ₁ ∨ Δ = Δ₂) ∧
      (∀ Δ : Set S, Δ ⊆ Δ₀ → IsClosedDisc Δ → subBd Δ = F → Δ = Δ₁) := by
  obtain ⟨hS_surf, _⟩ := GM11.IsSphere.isClosedSurface hS
  obtain ⟨D₁, D₂, hne, hD₁, hD₂, hb₁, hb₂, hcup, hcap, -, huniq⟩ := sphere_disc S hS F hF
  obtain ⟨Δ₁, ⟨hΔ₁_sub, hΔ₁_disc, hΔ₁_bd, -⟩, hΔ₁_uniq⟩ := disc_oArc Δ₀ F hΔ₀ hF_sub hF
  have hout : ∀ {A B : Set S}, IsClosedDisc A → IsClosedDisc B → discBd B = F →
      A ∪ B = univ → A ∩ B = F → closure (univ \ A) = B := by
    intro A B hA hB hbB hu hi
    apply Subset.antisymm
    · refine closure_minimal (fun x hx => (hu.ge (mem_univ x)).resolve_left hx.2) hB.isClosed
    · refine (IsClosedDisc.subset_closure_discInt hB).trans (closure_mono fun x hx => ?_)
      refine ⟨mem_univ x, fun hxA => hx.2 ?_⟩
      rw [hbB, ← hi]
      exact ⟨hxA, hx.1⟩
  have hsubBd : ∀ {D : Set S}, IsClosedDisc D → discBd D = F → subBd D = F :=
    fun hD hb => (IsClosedDisc.subBd_eq_discBd hS_surf hD).trans hb
  have hdiscBd : ∀ {D : Set S}, IsClosedDisc D → subBd D = F → discBd D = F :=
    fun hD hb => (IsClosedDisc.subBd_eq_discBd hS_surf hD).symm.trans hb
  have hbd_in_out : ∀ {A B : Set S}, A ⊆ Δ₀ → IsClosedDisc B → closure (univ \ A) = B →
      subBd Δ₀ ⊆ B := by
    intro A B hA hB hcl
    have h1 : univ \ Δ₀ ⊆ univ \ A := sdiff_subset_sdiff Subset.rfl hA
    have h2 : closure (univ \ Δ₀) ⊆ B := hcl ▸ closure_mono h1
    rw [subBd_eq_frontier, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
    exact inter_subset_right.trans h2
  have hcup' : D₂ ∪ D₁ = univ := by rw [Set.union_comm, hcup]
  have hcap' : D₂ ∩ D₁ = F := by rw [Set.inter_comm, hcap]
  have hcl12 := hout hD₁ hD₂ hb₂ hcup hcap
  have hcl21 := hout hD₂ hD₁ hb₁ hcup' hcap'
  rcases huniq Δ₁ hΔ₁_disc hΔ₁_bd with h_eq | h_eq
  · subst h_eq
    refine ⟨Δ₁, D₂, hne, hD₁, hD₂, hb₁, hb₂, hsubBd hD₁ hb₁, hsubBd hD₂ hb₂, hcup, hcap,
      hcl12, hcl21, hΔ₁_sub, hbd_in_out hΔ₁_sub hD₂ hcl12,
      fun Δ hΔ hb => huniq Δ hΔ (hdiscBd hΔ hb),
      fun Δ hsub hΔ hb => hΔ₁_uniq Δ hsub hΔ (hdiscBd hΔ hb)⟩
  · subst h_eq
    refine ⟨Δ₁, D₁, hne.symm, hD₂, hD₁, hb₂, hb₁, hsubBd hD₂ hb₂, hsubBd hD₁ hb₁, hcup', hcap',
      hcl21, hcl12, hΔ₁_sub, hbd_in_out hΔ₁_sub hD₁ hcl21,
      fun Δ hΔ hb => (huniq Δ hΔ (hdiscBd hΔ hb)).symm,
      fun Δ hsub hΔ hb => hΔ₁_uniq Δ hsub hΔ (hdiscBd hΔ hb)⟩

/-- In a closed disc `Δ` with `subBd Δ = F` and `F ∩ Γ.U ⊆ Γ.V`, every vertex of `Γ` in `Δ \ F`
belongs to `verts Γ.toGraph {e ∈ Γ.E | e ⊆ Δ}` (when `SubData Γ.toGraph G₀ P`). -/
theorem mem_verts_inter_of_mem_diff_bd {Γ : Drawing S} {G₀ : Graph S (Set S)}
    {P : Set S → Graph S (Set S)} (hS : IsClosedSurface S)
    (hsd : SubData Γ.toGraph G₀ P) {Δ F : Set S} (hΔ : IsClosedDisc Δ)
    (hbd : subBd Δ = F) (hF_norm : F ∩ Γ.U ⊆ Γ.V) {v : S} (hvV : v ∈ Γ.V) (hvΔ : v ∈ Δ \ F) :
    v ∈ verts Γ.toGraph {e ∈ Γ.E | e ⊆ Δ} := by
  obtain ⟨g, hgE, hig⟩ := SubDataSepGeneral.exists_inc_of_mem_V hsd hvV
  have hvc : v ∈ closure g := mem_closure_of_inc hig
  have hOpen : IsOpen (Δ \ F) := hbd ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS hΔ).1.1
  obtain ⟨y, hy_open, hyg⟩ := mem_closure_iff.mp hvc (Δ \ F) hOpen hvΔ
  have hgΔ : g ⊆ Δ :=
    edge_subset_of_inter_nonempty hΔ.isClosed (hbd ▸ hF_norm) hgE ⟨y, hyg, hy_open.1⟩
  exact ⟨g, ⟨hgE, hgΔ⟩, hig⟩

/-- Under the hypotheses of Theorem (8.3) with `4 ≤ ord` and a closed disc `Δ₀` satisfying
`PiSet ⊆ subBd Δ₀`, `Γ` is rigid in `Δ₀`. -/
theorem isRigidIn_Δ₀_8_3
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀) (hPi_bd : PiSet ⊆ subBd Δ₀) :
    IsRigidIn Γ Δ₀ := by
  obtain ⟨hS_surf, hS_conn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  obtain ⟨G₀, P_sub, hsd⟩ := exists_subData h83.hyp_i.2
  have hPi_V : PiSet ⊆ Γ.V := h83.hyp_iii.1.trans h83.hyp_ii.1.1
  have hT : IsTangle Γ.toHypergraph ord T := h83.hyp_iv.2.1.1.2.1
  intro F hF_sub hF_oarc hF_norm hF_card
  obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, _, _, hsb₁, hsb₂, _, hcap, _, hcl21, hΔ₁_sub, hbd₀_Δ₂, -, -⟩ :=
    sphere_oArc_discs_in_Δ₀ h83.hyp_i.1 hΔ₀ hF_sub hF_oarc
  let A_E : Set (Set S) := {e ∈ Γ.E | e ⊆ Δ₁}
  have hA_E_sub : A_E ⊆ E(Γ.toGraph) := fun _ he => he.1
  have hinter_E : (Γ.interSet Δ₁).E = A_E := by
    change (Γ.span _ _).E = _
    rw [Γ.span_E]
    ext e
    simp only [A_E, mem_inter_iff, mem_ofPred_eq]
    tauto
  obtain ⟨hinter_V, hinter_U⟩ := interSet_V_and_U hΔ₁.isClosed (hsb₁ ▸ hF_norm)
  refine ⟨Δ₁, hΔ₁_sub, hΔ₁, hsb₁, ?_⟩
  by_cases hAE_ne : A_E.Nonempty
  · right
    have hPi_diff_ne : (PiSet \ (F ∩ Γ.V)).Nonempty := by
      by_contra hemp
      have hsub : PiSet ⊆ F ∩ Γ.V := fun x hx => by
        by_contra hx_not
        exact hemp ⟨x, hx, hx_not⟩
      have hle := (Set.ncard_le_ncard hsub (Γ.finite_V.subset inter_subset_right)).trans hF_card
      have h4 := h83.hyp_iii.2
      omega
    obtain ⟨p₀, hp₀_Pi, hp₀_not⟩ := hPi_diff_ne
    have hp₀_V : p₀ ∈ Γ.V := hPi_V hp₀_Pi
    have hp₀_not_F : p₀ ∉ F := fun hpF => hp₀_not ⟨hpF, hp₀_V⟩
    have hp₀_Δ₂ : p₀ ∈ Δ₂ \ F := ⟨hbd₀_Δ₂ (hPi_bd hp₀_Pi), hp₀_not_F⟩
    obtain ⟨g_out, ⟨hg_out_E, hg_out_Δ₂⟩, _⟩ :=
      mem_verts_inter_of_mem_diff_bd hS_surf hsd hΔ₂ hsb₂ hF_norm hp₀_V hp₀_Δ₂
    have hg_out_not_AE : g_out ∉ A_E := by
      intro ⟨_, hg_Δ₁⟩
      obtain ⟨z, hz⟩ := hg_out_E.1
      have hzF : z ∈ F := hcap ▸ ⟨hg_Δ₁ hz, hg_out_Δ₂ hz⟩
      have hzU : z ∈ Γ.U := (hg_out_E.2.1 hz).1
      exact (hg_out_E.2.1 hz).2 (hF_norm ⟨hzF, hzU⟩)
    have hcompl_ne : (E(Γ.toGraph) \ A_E).Nonempty := ⟨g_out, hg_out_E, hg_out_not_AE⟩
    have hbd_AE_sub : bdry Γ.toGraph A_E ⊆ F ∩ Γ.V := by
      rintro z ⟨⟨e₁, ⟨he₁E, he₁Δ₁⟩, hie₁⟩, e₂, ⟨he₂E, he₂_not⟩, hie₂⟩
      have hzV : z ∈ Γ.V := hie₁.vertex_mem
      have hzΔ₁ : z ∈ Δ₁ := hΔ₁.isClosed.closure_subset_iff.mpr he₁Δ₁ (mem_closure_of_inc hie₁)
      have hzF : z ∈ F := by
        by_contra hz_not_F
        have hOpen₁ : IsOpen (Δ₁ \ F) :=
          hsb₁ ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS_surf hΔ₁).1.1
        obtain ⟨y, hy_open, hye₂⟩ :=
          mem_closure_iff.mp (mem_closure_of_inc hie₂) (Δ₁ \ F) hOpen₁ ⟨hzΔ₁, hz_not_F⟩
        have he₂Δ₁ : e₂ ⊆ Δ₁ :=
          edge_subset_of_inter_nonempty hΔ₁.isClosed (hsb₁ ▸ hF_norm) he₂E ⟨y, hye₂, hy_open.1⟩
        exact he₂_not ⟨he₂E, he₂Δ₁⟩
      exact ⟨hzF, hzV⟩
    have hbd_AE_card : (bdry Γ.toGraph A_E).ncard ≤ 2 :=
      (Set.ncard_le_ncard hbd_AE_sub (Γ.finite_V.subset inter_subset_right)).trans hF_card
    obtain ⟨e₀, x, y, Q, _, hxy, hbd_eq, _, hQ_path, hcases⟩ :=
      SubDataSepGeneral.sep_general hsd hA_E_sub hbd_AE_card hAE_ne hcompl_ne
    have hFV_eq : F ∩ Γ.V = {x, y} := by
      have hsub : ({x, y} : Set S) ⊆ F ∩ Γ.V := hbd_eq ▸ hbd_AE_sub
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by rw [Set.ncard_pair hxy]; exact hF_card)
        (Γ.finite_V.subset inter_subset_right)).symm
    rcases hcases with ⟨hAE_eq, hAV_eq⟩ | ⟨hcompl_eq, _⟩
    · refine ⟨x, y, hxy, hFV_eq, ?_⟩
      obtain ⟨hle_Q, W_Q, hs_Q, hV_Q, hE_Q⟩ := hQ_path
      have hP_V : (Γ.interSet Δ₁).V = V(Q) := by
        rw [hinter_V, ← hAV_eq]
        ext z
        constructor
        · rintro ⟨hzV, hzΔ₁⟩
          by_cases hzF : z ∈ F
          · have hz_xy : z ∈ bdry Γ.toGraph A_E := by
              rw [hbd_eq, ← hFV_eq]
              exact ⟨hzF, hzV⟩
            exact hz_xy.1
          · exact mem_verts_inter_of_mem_diff_bd hS_surf hsd hΔ₁ hsb₁ hF_norm hzV ⟨hzΔ₁, hzF⟩
        · rintro ⟨g, ⟨hgE, hgΔ₁⟩, hig⟩
          exact ⟨hig.vertex_mem, hΔ₁.isClosed.closure_subset_iff.mpr hgΔ₁ (mem_closure_of_inc hig)⟩
      have hP_E : (Γ.interSet Δ₁).E = E(Q) := hinter_E.trans hAE_eq
      have hP_sub : (Γ.interSet Δ₁).IsSubdrawing Γ := Γ.span_isSubdrawing _ _
      obtain ⟨W_P, hsupp_P, hedges_P⟩ := W_Q.exists_transfer (G' := (Γ.interSet Δ₁).toGraph)
        (fun _ _ _ _ hlk => (hP_sub.isLink_iff (hP_E.symm ▸ hlk.edge_mem)).mpr (hlk.mono hle_Q))
        (fun z hz => by
          change z ∈ (Γ.interSet Δ₁).V
          rw [hP_V, hV_Q]
          exact hz)
      have hs_P : W_P.IsSimple := by
        change W_P.support.Nodup
        rw [hsupp_P]
        exact hs_Q
      exact ⟨W_P, hs_P, by rw [hP_V, hV_Q, hsupp_P], by rw [hP_E, hE_Q, hedges_P]⟩
    · exfalso
      have hfr₂ : frontier Δ₂ = F := by rw [← subBd_eq_frontier, hsb₂]
      have hsep₂ : Γ.toHypergraph.IsSeparation
          ((PaintingOrDrawing.drawing Γ).inter Δ₂)
          ((PaintingOrDrawing.drawing Γ).interOutside Δ₂) :=
        GM11.isSeparation_inter (Γ := PaintingOrDrawing.drawing Γ) hΔ₂.isClosed
          (by rw [hfr₂]; exact hF_norm)
      have hinter₂_sub :
          ((PaintingOrDrawing.drawing Γ).inter Δ₂ ∩
            (PaintingOrDrawing.drawing Γ).interOutside Δ₂).vertexSet ⊆ F ∩ Γ.V := by
        intro z hz
        rw [← hfr₂]
        exact GM11.inter_outside_subset (Γ := PaintingOrDrawing.drawing Γ) hz
      have hord₂_le : separationOrder
          ((PaintingOrDrawing.drawing Γ).inter Δ₂)
          ((PaintingOrDrawing.drawing Γ).interOutside Δ₂) ≤ 2 :=
        (Set.ncard_le_ncard hinter₂_sub (Γ.finite_V.subset inter_subset_right)).trans hF_card
      have hE₂_sub : ((PaintingOrDrawing.drawing Γ).inter Δ₂).edgeSet ⊆ E(Q) := by
        rw [← hcompl_eq]
        rintro g ⟨hgE, hgΔ₂⟩
        refine ⟨hgE, fun ⟨_, hgΔ₁⟩ => ?_⟩
        obtain ⟨z, hz⟩ := hgE.1
        have hzF : z ∈ F := hcap ▸ ⟨hgΔ₁ hz, hgΔ₂ hz⟩
        exact (hgE.2.1 hz).2 (hF_norm ⟨hzF, (hgE.2.1 hz).1⟩)
      have hbd_Q : bdry Γ.toGraph E(Q) ⊆ {x, y} := by
        rw [← hcompl_eq, bdry_compl hA_E_sub, hbd_eq]
      have hmem₂ :
          ((PaintingOrDrawing.drawing Γ).inter Δ₂,
            (PaintingOrDrawing.drawing Γ).interOutside Δ₂) ∈ T :=
        path_sep_mem_tangle hT hord hQ_path hbd_Q hsep₂ (by omega) hE₂_sub
      have hPi_in₂ : PiSet ⊆ ((PaintingOrDrawing.drawing Γ).inter Δ₂).vertexSet :=
        fun z hz => ⟨hPi_V hz, hbd₀_Δ₂ (hPi_bd hz)⟩
      exact h83.hyp_iv.2.2 _ _ hmem₂ (by omega) hPi_in₂
  · left
    rw [not_nonempty_iff_eq_empty] at hAE_ne
    rintro z ⟨hzΔ₁, hzU⟩
    by_contra hz_not_F
    by_cases hzV : z ∈ Γ.V
    · have hz_verts :=
        mem_verts_inter_of_mem_diff_bd hS_surf hsd hΔ₁ hsb₁ hF_norm hzV ⟨hzΔ₁, hz_not_F⟩
      change z ∈ verts Γ.toGraph A_E at hz_verts
      rw [hAE_ne] at hz_verts
      rcases hz_verts with ⟨_, hg, _⟩
      exact hg
    · obtain ⟨g, hgE, hzg⟩ := Γ.exists_edge_of_mem hzU hzV
      have hgΔ₁ : g ⊆ Δ₁ :=
        edge_subset_of_inter_nonempty hΔ₁.isClosed (hsb₁ ▸ hF_norm) hgE ⟨z, hzg, hzΔ₁⟩
      have hg_AE : g ∈ A_E := ⟨hgE, hgΔ₁⟩
      rw [hAE_ne] at hg_AE
      exact hg_AE

/-! ## Section 4: Claims (2) and (3) of Theorem 8.3 -/

/-- Under the hypotheses of (8.3), the embedded graph of $\Gamma$ is a subgraph of $J \setminus W$
and hence of $J$. -/
theorem Γ_le_J_8_3
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star) :
    Γ.toEmbeddedGraph ιV ιE ≤ J.deleteVerts W ∧ Γ.toEmbeddedGraph ιV ιE ≤ J := by
  have hle_JW : Γ.toEmbeddedGraph ιV ιE ≤ J.deleteVerts W := by
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx_GW : x ∈ V(R_G.G.toGraph.deleteVerts W) := h83.Γ_le.vertexSet_mono hx
      rw [vertexSet_deleteVerts] at hx_GW ⊢
      refine ⟨?_, hx_GW.2⟩
      rw [h83.hyp_v.2, vertexSet_induce]
      exact Or.inl (Or.inr hx)
    · intro e x y hlk
      have hlk_GW := hlk.mono h83.Γ_le
      rw [deleteVerts_isLink] at hlk_GW ⊢
      refine ⟨?_, hlk_GW.2.1, hlk_GW.2.2⟩
      rw [h83.hyp_v.2, induce_isLink]
      exact ⟨hlk_GW.1, Or.inl (Or.inr hlk.left_mem), Or.inl (Or.inr hlk.right_mem)⟩
  exact ⟨hle_JW, hle_JW.trans deleteVerts_le⟩

/-- **Claim (2)** in the proof of Theorem (8.3) (Graph Minors XXII, Section 8, page 560):
"(2) We may choose the function $\alpha$ and the discs $D(A)$ ($A \in \mathcal{A}$) to satisfy (1)
and in addition such that
- $\alpha(v) = v$ for each $v \in Z \cap V(\Gamma)$, and
- for each $A \in \mathcal{A}$, $\text{bd}(D(A))$ is $\Gamma$-normal, and
  $\Gamma \cap D(A) = \Gamma \cap A$, and $\text{bd}(D(A)) \cap V(\Gamma) = \bar{\pi}(A)$." -/
theorem lemma_8_3_claim_2
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀)
    (hΓ_Δ₀ : Γ.U ⊆ Δ₀) (hbd_Δ₀ : subBd Δ₀ ∩ Γ.U = PiSet)
    (e_C_Δ₀ : C₀.U ≃ₜ subBd Δ₀)
    (he_C_Δ₀ : ∀ y : C₀.U, y.1 ∈ PiSet → (e_C_Δ₀ y).1 = y.1) :
    ∃ (α_map : α → S) (D : Graph α β → Set S),
      (∀ v ∈ Z, α_map v ∈ Δ₀) ∧
      (∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ D A ⊆ Δ₀) ∧
      (∀ p ∈ PiSet, α_map (ιV p) = p) ∧
      (∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), α_map v ∈ subBd (D A)) ∧
      (∀ v ∈ Z, ∀ A ∈ 𝒜, α_map v ∈ D A → v ∈ Set.range (πA A)) ∧
      (∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' →
        D A ∩ D A' = α_map '' (Set.range (πA A) ∩ Set.range (πA A'))) ∧
      (∀ A ∈ 𝒜,
        D A ∩ subBd Δ₀ = α_map '' (Set.range (πA A) ∩ (ιV '' PiSet))) ∧
      (∀ v ∈ Z, ∀ v' ∈ Z, v ≠ v' → α_map v ≠ α_map v') ∧
      (∀ v ∈ Γ.V, ιV v ∈ Z → α_map (ιV v) = v) ∧
      (∀ v ∈ Z, α_map v ∈ Γ.U ↔ v ∈ ιV '' Γ.V) ∧
      (∀ A ∈ 𝒜,
        subBd (D A) ∩ Γ.U = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} ∧
        (Γ.interSet (D A)).V = {v ∈ Γ.V | ιV v ∈ V(A)} ∧
        (Γ.interSet (D A)).E = {e ∈ Γ.E | ιE e ∈ E(A)} ∧
        (Γ.interSet (D A)).toEmbeddedGraph ιV ιE = (Γ.toEmbeddedGraph ιV ιE) ⊓ A) := by
  classical
  obtain ⟨α₀, D₀, hα₀_Δ₀, hD₀, hα₀_Pi, hα₀_bdA, hα₀_inA, hD₀_inter, hD₀_bdΔ₀, hα₀_inj_ne⟩ :=
    lemma_8_3_claim_1 h83 hΔ₀ e_C_Δ₀ he_C_Δ₀
  have hα₀_inj : ∀ v ∈ Z, ∀ v' ∈ Z, α₀ v = α₀ v' → v = v' := by
    intro v hv v' hv' heq
    by_contra hne
    exact hα₀_inj_ne v hv v' hv' hne heq
  have hPi_bd : PiSet ⊆ subBd Δ₀ := by
    rw [← hbd_Δ₀]
    exact inter_subset_left
  have hrigid : GM14.IsRigidIn Γ Δ₀ := isRigidIn_Δ₀_8_3 h83 hord hΔ₀ hPi_bd
  obtain ⟨hS_surf, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have hbd_Δ₀_eq : subBd Δ₀ = discBd Δ₀ := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS_surf hΔ₀]
  have hPi_V : PiSet ⊆ Γ.V := h83.hyp_iii.1.trans h83.hyp_ii.1.1
  have hΓ_bd : Γ.U ∩ subBd Δ₀ ⊆ Γ.V := by
    rw [Set.inter_comm, hbd_Δ₀]
    exact hPi_V
  have hΓ_V_Pi : Γ.V ∩ subBd Δ₀ = PiSet := by
    apply Subset.antisymm
    · intro x ⟨hxV, hxbd⟩
      rw [← hbd_Δ₀]
      exact ⟨hxbd, Γ.V_subset_U hxV⟩
    · intro x hxPi
      refine ⟨hPi_V hxPi, ?_⟩
      rw [← hbd_Δ₀] at hxPi
      exact hxPi.1
  have hπ_eq_Z : ∀ A ∈ 𝒜, Set.range (πA A) = Z ∩ V(A) :=
    fun A hA => (h83.hyp_vii A hA).2.2
  have hZdiv : IsZDivision J (Z ∪ W) 𝒜 := h83.hyp_vi.2.2.1
  obtain ⟨hΓ_le_JW, hΓ_le_J⟩ := Γ_le_J_8_3 h83
  have hΓ_not_W : ∀ v ∈ Γ.V, ιV v ∉ W := by
    intro v hv
    have hv_JW : ιV v ∈ V(J.deleteVerts W) := hΓ_le_JW.vertexSet_mono ⟨v, hv, rfl⟩
    rw [vertexSet_deleteVerts] at hv_JW
    exact hv_JW.2
  have hseg_edge : ∀ e ∈ Γ.E, ∃ A ∈ 𝒜, ιE e ∈ E(A) := by
    intro e he
    have heJ : ιE e ∈ E(J) := hΓ_le_J.edgeSet_mono ⟨e, he, rfl⟩
    have hEu := congrArg Graph.edgeSet hZdiv.2.2.1
    rw [edgeSet_subgraphSUnion hZdiv.2.1] at hEu
    rw [← hEu] at heJ
    rcases mem_iUnion₂.mp heJ with ⟨A, hA, heA⟩
    exact ⟨A, hA, heA⟩
  have hseg_vertex : ∀ v ∈ Γ.V, ∃ A ∈ 𝒜, ιV v ∈ V(A) := by
    intro v hv
    have hvJ : ιV v ∈ V(J) := hΓ_le_J.vertexSet_mono ⟨v, hv, rfl⟩
    have hVu : (⋃ A ∈ 𝒜, V(A)) = V(J) := congrArg Graph.vertexSet hZdiv.2.2.1
    rw [← hVu] at hvJ
    rcases mem_iUnion₂.mp hvJ with ⟨A, hA, hvA⟩
    exact ⟨A, hA, hvA⟩
  have hinc_J : ∀ e ∈ Γ.E, ∀ v ∈ Γ.V, v ∈ closure e → J.Inc (ιE e) (ιV v) := by
    intro e he v hv hve
    obtain ⟨w, hlk⟩ := inc_of_mem_closure he hve hv
    have hlk_emb : (Γ.toEmbeddedGraph ιV ιE).IsLink (ιE e) (ιV v) (ιV w) :=
      ⟨e, v, w, hlk, rfl, rfl, rfl⟩
    exact ⟨ιV w, hlk_emb.mono hΓ_le_J⟩
  have hA_v_of_e : ∀ A ∈ 𝒜, ∀ e ∈ Γ.E, ιE e ∈ E(A) → ∀ v ∈ Γ.V, v ∈ closure e →
      ιV v ∈ V(A) := by
    intro A hA e he heA v hv hve
    obtain ⟨y, hy⟩ := hinc_J e he v hv hve
    exact (((hZdiv.2.1 A hA).isLink_iff heA).mpr hy).left_mem
  let Vs : Graph α β → Set S := fun A => {v | v ∈ Γ.V ∧ ιV v ∈ V(A)}
  let Es : Graph α β → Set (Set S) := fun A => {e | e ∈ Γ.E ∧ ιE e ∈ E(A)}
  let Pd : Graph α β → Drawing S := fun A => Γ.span (Vs A) (Es A)
  let X₀ : Graph α β → Set S := fun A => {v | v ∈ Γ.V ∧ ιV v ∈ Set.range (πA A)}
  have hPs : ∀ A, (Pd A).IsSubdrawing Γ := fun A => Γ.span_isSubdrawing _ _
  have hPE : ∀ A, (Pd A).E = Es A := fun A => by
    change (Γ.span (Vs A) (Es A)).E = _
    rw [Γ.span_E]
    exact inter_eq_left.mpr fun e he => he.1
  have hPV : ∀ A ∈ 𝒜, (Pd A).V = Vs A := by
    intro A hA
    apply Subset.antisymm
    · rintro v (⟨hv, -⟩ | hv)
      · exact hv
      · obtain ⟨e, ⟨he, -⟩, hve, hvV⟩ := mem_iUnion₂.mp hv
        exact ⟨hvV, hA_v_of_e A hA e he.1 he.2 v hvV hve⟩
    · intro v hv
      exact Or.inl ⟨hv, hv.1⟩
  have hPXs : ∀ A ∈ 𝒜, X₀ A ⊆ (Pd A).V := by
    intro A hA v hv
    rw [hPV A hA]
    refine ⟨hv.1, ?_⟩
    have hvZ : ιV v ∈ Z ∩ V(A) := hπ_eq_Z A hA ▸ hv.2
    exact hvZ.2
  have hXc : ∀ A ∈ 𝒜, (X₀ A).ncard ≤ 3 := by
    intro A hA
    rw [← ιV.injective.injOn.ncard_image]
    have hsub : ιV '' (X₀ A) ⊆ Set.range (πA A) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hv.2
    have hfin : (Set.range (πA A)).Finite := Set.finite_range (πA A)
    have hle1 : (ιV '' (X₀ A)).ncard ≤ (Set.range (πA A)).ncard :=
      Set.ncard_le_ncard hsub hfin
    have hle2 : (Set.range (πA A)).ncard ≤ πLen A := by
      calc (Set.range (πA A)).ncard = (πA A '' Set.univ).ncard := by rw [Set.image_univ]
        _ ≤ (Set.univ : Set (Fin (πLen A))).ncard := Set.ncard_image_le Set.finite_univ
        _ = πLen A := by simp
    exact (hle1.trans hle2).trans (h83.hyp_vii A hA).1
  have hout : ∀ A ∈ 𝒜, ∀ v ∈ (Pd A).V, v ∉ X₀ A →
      v ∉ subBd Δ₀ ∧ ∀ e ∈ Γ.E, v ∈ closure e → e ∈ (Pd A).E := by
    intro A hA v hv hvX
    rw [hPV A hA] at hv
    have hoth : ∀ A₁ ∈ 𝒜, ιV v ∈ V(A₁) → A₁ = A := by
      intro A₁ hA₁ h₁
      by_contra hne
      have hinter := (hZdiv.2.2.2 A hA A₁ hA₁ (Ne.symm hne)).2 ⟨hv.2, h₁⟩
      rcases hinter with hvZ | hvW
      · exact hvX ⟨hv.1, (hπ_eq_Z A hA).symm ▸ ⟨hvZ, hv.2⟩⟩
      · exact hΓ_not_W v hv.1 hvW
    refine ⟨fun hb => ?_, fun e he hve => ?_⟩
    · have hvPi : v ∈ PiSet := hbd_Δ₀ ▸ ⟨hb, Γ.V_subset_U hv.1⟩
      have hvZ : ιV v ∈ Z := h83.hyp_vi.2.1 ⟨v, hvPi, rfl⟩
      exact hvX ⟨hv.1, (hπ_eq_Z A hA).symm ▸ ⟨hvZ, hv.2⟩⟩
    · obtain ⟨A₁, hA₁, he₁⟩ := hseg_edge e he
      have h₂ := hoth A₁ hA₁ (hA_v_of_e A₁ hA₁ e he he₁ v hv.1 hve)
      subst h₂
      rw [hPE]
      exact ⟨he, he₁⟩
  have hparts : ∀ i : 𝒜, ∃ ψ ψ', PH (Pd i.1).U (ψ '' (Pd i.1).U) ψ ψ' ∧
      MapsTo ψ (Pd i.1).U (D₀ i.1) ∧
      (∀ z ∈ (Pd i.1).U, ψ z ∈ subBd (D₀ i.1) → z ∈ X₀ i.1) ∧
      ∀ x ∈ X₀ i.1, ψ x = α₀ (ιV x) := by
    rintro ⟨A, hA⟩
    refine exists_part_map (g := fun x => α₀ (ιV x)) hΔ₀ hbd_Δ₀_eq hΓ_Δ₀ hΓ_bd hrigid (hPs A)
      (hPXs A hA) (hXc A hA) (hout A hA) (hD₀ A hA).1 (hD₀ A hA).2 ?_ ?_
    · intro x hx y hy h
      have hxZ : ιV x ∈ Z := ((hπ_eq_Z A hA).subset hx.2).1
      have hyZ : ιV y ∈ Z := ((hπ_eq_Z A hA).subset hy.2).1
      exact ιV.injective (hα₀_inj (ιV x) hxZ (ιV y) hyZ h)
    · intro x hx
      exact hα₀_bdA A hA (ιV x) hx.2
  choose ψ ψ' hparts_spec using hparts
  have h₁ := fun i : 𝒜 => (hparts_spec i).1
  have h₂ := fun i : 𝒜 => (hparts_spec i).2.1
  have h₃ := fun i : 𝒜 => (hparts_spec i).2.2.1
  have h₄ := fun i : 𝒜 => (hparts_spec i).2.2.2
  clear hparts_spec
  have hPU_V : ∀ A ∈ 𝒜, ∀ z ∈ (Pd A).U, z ∈ Γ.V → z ∈ Vs A := by
    intro A hA z hz hzV
    rw [← hPV A hA]
    by_contra hn
    obtain ⟨e, he, hze⟩ := (Pd A).exists_edge_of_mem hz hn
    exact GM11.edge_notMem_V ((hPs A).2 he) hze hzV
  have hcross : ∀ i j : 𝒜, i ≠ j → ∀ z ∈ (Pd i.1).U, ψ i z ∈ D₀ j.1 →
      z ∈ X₀ i.1 ∧ ιV z ∈ Set.range (πA j.1) := by
    intro i j hij z hz hzj
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have h_in_inter : ψ i z ∈ D₀ i.1 ∩ D₀ j.1 := ⟨h₂ i hz, hzj⟩
    rw [hD₀_inter i.1 i.2 j.1 j.2 hne] at h_in_inter
    obtain ⟨q, ⟨hqi, hqj⟩, hq⟩ := h_in_inter
    have hb : ψ i z ∈ subBd (D₀ i.1) := by
      rw [← hq]
      exact hα₀_bdA i.1 i.2 q hqi
    have hzX := h₃ i z hz hb
    refine ⟨hzX, ?_⟩
    have he : α₀ (ιV z) = α₀ q := by rw [← h₄ i z hzX, hq]
    have hzZ : ιV z ∈ Z := ((hπ_eq_Z i.1 i.2).subset hzX.2).1
    have hqZ : q ∈ Z := ((hπ_eq_Z i.1 i.2).subset hqi).1
    rw [hα₀_inj (ιV z) hzZ q hqZ he]
    exact hqj
  have hclosedB : ∀ i : 𝒜, IsClosed (ψ i '' (Pd i.1).U) := by
    intro i
    have hc : IsCompact (Pd i.1).U :=
      hΔ₀.isCompact.of_isClosed_subset (Pd i.1).isClosed_U ((hPs i.1).U_subset.trans hΓ_Δ₀)
    exact (h₁ i).image_isClosed hc subset_rfl (Pd i.1).isClosed_U
  have hfin : Finite 𝒜 := hZdiv.1.to_subtype
  have hnS : Nonempty S := hΔ₀.isPathConnected.nonempty.to_type
  obtain ⟨Φ, Φ', hΦ, hEq, -⟩ := exists_glue (A := fun i : 𝒜 => (Pd i.1).U)
    (B := fun i : 𝒜 => ψ i '' (Pd i.1).U) (f := ψ) (f' := ψ') (fun i => (Pd i.1).isClosed_U)
    hclosedB h₁
    (by
      intro i j x hxi hxj
      by_cases hij : i = j
      · rw [hij]
      have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hxV : x ∈ Γ.V := by
        by_contra hn
        obtain ⟨e, he, hxe⟩ := (Pd i.1).exists_edge_of_mem hxi fun h => hn ((hPs i.1).1 h)
        obtain ⟨f, hf, hxf⟩ := (Pd j.1).exists_edge_of_mem hxj fun h => hn ((hPs j.1).1 h)
        have heq := Γ.edge_eq_of_mem ((hPs i.1).2 he) ((hPs j.1).2 hf) hxe hxf
        rw [hPE] at he hf
        subst heq
        exact disjoint_left.mp (hZdiv.2.2.2 i.1 i.2 j.1 j.2 hne).1 he.2 hf.2
      have hi := hPU_V i.1 i.2 x hxi hxV
      have hj := hPU_V j.1 j.2 x hxj hxV
      have hinter := (hZdiv.2.2.2 i.1 i.2 j.1 j.2 hne).2 ⟨hi.2, hj.2⟩
      have hxZ : ιV x ∈ Z := hinter.resolve_right (hΓ_not_W x hxV)
      have hxiX : x ∈ X₀ i.1 := ⟨hxV, (hπ_eq_Z i.1 i.2).symm ▸ ⟨hxZ, hi.2⟩⟩
      have hxjX : x ∈ X₀ j.1 := ⟨hxV, (hπ_eq_Z j.1 j.2).symm ▸ ⟨hxZ, hj.2⟩⟩
      rw [h₄ i x hxiX, h₄ j x hxjX])
    (by
      rintro i j y ⟨z, hz, rfl⟩ ⟨z', hz', hzz⟩
      by_cases hij : i = j
      · subst hij
        rfl
      have hiz : ψ i z ∈ D₀ j.1 := hzz ▸ h₂ j hz'
      have hjz : ψ j z' ∈ D₀ i.1 := hzz.symm ▸ h₂ i hz
      obtain ⟨hX, _⟩ := hcross i j hij z hz hiz
      obtain ⟨hX', _⟩ := hcross j i (Ne.symm hij) z' hz' hjz
      have h₅ : α₀ (ιV z) = α₀ (ιV z') := by
        rw [← h₄ i z hX, ← h₄ j z' hX', hzz]
      have hzZ : ιV z ∈ Z := ((hπ_eq_Z i.1 i.2).subset hX.2).1
      have hz'Z : ιV z' ∈ Z := ((hπ_eq_Z j.1 j.2).subset hX'.2).1
      have h₆ := ιV.injective (hα₀_inj (ιV z) hzZ (ιV z') hz'Z h₅)
      rw [(h₁ i).left hz, ← hzz, (h₁ j).left hz']
      exact h₆)
  have hcover : (⋃ i : 𝒜, (Pd i.1).U) = Γ.U := by
    apply subset_antisymm (iUnion_subset fun i : 𝒜 => (hPs i.1).U_subset)
    intro z hz
    by_cases hzV : z ∈ Γ.V
    · obtain ⟨A, hA, h⟩ := hseg_vertex z hzV
      refine mem_iUnion.mpr ⟨⟨A, hA⟩, (Pd A).V_subset_U ?_⟩
      rw [hPV A hA]
      exact ⟨hzV, h⟩
    · obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hz hzV
      obtain ⟨A, hA, h⟩ := hseg_edge e he
      have heP : e ∈ (Pd A).E := by
        rw [hPE]
        exact ⟨he, h⟩
      exact mem_iUnion.mpr ⟨⟨A, hA⟩, (Pd A).closure_subset_U heP (subset_closure hze)⟩
  rw [hcover] at hΦ
  have hHc : IsCompact Γ.U := hΔ₀.isCompact.of_isClosed_subset Γ.isClosed_U hΓ_Δ₀
  let H' := mapD hΦ hHc Γ subset_rfl
  let φ := mapIso hΦ hHc Γ subset_rfl
  have hφv : ∀ v : V(Γ.toGraph), (φ.vertexEquiv v).1 = Φ v.1 := fun v => mapIso_vertex hΦ hHc Γ _ v
  have hφe : ∀ e : E(Γ.toGraph), (φ.edgeEquiv e).1 = Φ '' e.1 := fun e => mapIso_edge hΦ hHc Γ _ e
  have hΦi : ∀ (i : 𝒜) {z}, z ∈ (Pd i.1).U → Φ z = ψ i z := fun i {z} hz => hEq i hz
  have hsome : ∀ z ∈ Γ.U, ∃ i : 𝒜, z ∈ (Pd i.1).U := fun z hz =>
    mem_iUnion.mp (hcover.symm ▸ hz)
  have hΦX : ∀ A ∈ 𝒜, ∀ v ∈ X₀ A, Φ v = α₀ (ιV v) := by
    intro A hA v hv
    have h₅ : v ∈ (Pd A).U := (Pd A).V_subset_U (hPXs A hA hv)
    rw [hΦi ⟨A, hA⟩ h₅]
    exact h₄ ⟨A, hA⟩ v hv
  have hbdα : ∀ {i : 𝒜} {w}, w ∈ D₀ i.1 → w ∈ subBd Δ₀ → w ∈ subBd (D₀ i.1) :=
    fun {i w} h₅ h₆ => ⟨subset_closure h₅, closure_mono (show univ \ Δ₀ ⊆ univ \ D₀ i.1 from
      fun y hy => ⟨hy.1, fun h => hy.2 ((hD₀ i.1 i.2).2 h)⟩) h₆.2⟩
  have hbdV : ∀ z ∈ Γ.U, Φ z ∈ subBd Δ₀ → ∃ A ∈ 𝒜, z ∈ X₀ A := by
    intro z hz hb
    obtain ⟨i, hi⟩ := hsome z hz
    have h₅ : ψ i z ∈ D₀ i.1 := h₂ i hi
    rw [hΦi i hi] at hb
    exact ⟨i.1, i.2, h₃ i z hi (hbdα h₅ hb)⟩
  have hH'Δ₀ : H'.U ⊆ Δ₀ := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := hsome z hz
    rw [hΦi i hi]
    exact (hD₀ i.1 i.2).2 (h₂ i hi)
  have hH'bd : H'.U ∩ subBd Δ₀ ⊆ H'.V := by
    rintro _ ⟨⟨z, hz, rfl⟩, hb⟩
    obtain ⟨A, -, hzX⟩ := hbdV z hz hb
    exact mem_image_of_mem Φ hzX.1
  have hV_bd_eq : Γ.V ∩ subBd Δ₀ = H'.V ∩ subBd Δ₀ := by
    apply subset_antisymm
    · rintro v ⟨hv, hb⟩
      have hvPi : v ∈ PiSet := hbd_Δ₀ ▸ ⟨hb, Γ.V_subset_U hv⟩
      obtain ⟨A, hA, hvA⟩ := hseg_vertex v hv
      have hvZ : ιV v ∈ Z := h83.hyp_vi.2.1 ⟨v, hvPi, rfl⟩
      have hvX : v ∈ X₀ A := ⟨hv, (hπ_eq_Z A hA).symm ▸ ⟨hvZ, hvA⟩⟩
      have h₆ := hΦX A hA v hvX
      rw [hα₀_Pi v hvPi] at h₆
      exact ⟨⟨v, hv, h₆⟩, hb⟩
    · rintro _ ⟨⟨v, hv, rfl⟩, hb⟩
      have hvU : v ∈ Γ.U := Γ.V_subset_U hv
      obtain ⟨A, hA, hvX⟩ := hbdV v hvU hb
      have h₅ := hΦX A hA v hvX
      have h_in_D₀ : Φ v ∈ D₀ A ∩ subBd Δ₀ := by
        refine ⟨?_, hb⟩
        exact subBd_subset_of subset_rfl (hD₀ A hA).1.isClosed (h₅.symm ▸ hα₀_bdA A hA (ιV v) hvX.2)
      rw [hD₀_bdΔ₀ A hA] at h_in_D₀
      obtain ⟨q, ⟨hqA, p, hpPi, rfl⟩, hq_eq⟩ := h_in_D₀
      have hvZ : ιV v ∈ Z := ((hπ_eq_Z A hA).subset hvX.2).1
      have hpZ : ιV p ∈ Z := h83.hyp_vi.2.1 ⟨p, hpPi, rfl⟩
      have hvp : v = p := ιV.injective (hα₀_inj (ιV p) hpZ (ιV v) hvZ (hq_eq.trans h₅)).symm
      subst hvp
      rw [h₅, hα₀_Pi v hpPi]
      exact ⟨hv, (hbd_Δ₀.symm ▸ hpPi).1⟩
  have hφ_bd : ∀ v : V(Γ.toGraph), v.1 ∈ subBd Δ₀ → (φ.vertexEquiv v).1 = v.1 := by
    intro v hvbd
    have hvPi : v.1 ∈ PiSet := hbd_Δ₀ ▸ ⟨hvbd, Γ.V_subset_U v.2⟩
    obtain ⟨A, hA, hvA⟩ := hseg_vertex v.1 v.2
    have hvZ : ιV v.1 ∈ Z := h83.hyp_vi.2.1 ⟨v.1, hvPi, rfl⟩
    have hvX : v.1 ∈ X₀ A := ⟨v.2, (hπ_eq_Z A hA).symm ▸ ⟨hvZ, hvA⟩⟩
    rw [hφv v, hΦX A hA v.1 hvX, hα₀_Pi v.1 hvPi]
  have h_ii : ∀ A ∈ 𝒜,
      H'.U ∩ subBd (D₀ A) = {w | ∃ v : V(Γ.toGraph), (φ.vertexEquiv v).1 = w ∧ ιV v.1 ∈ Set.range (πA A)} ∧
      (∀ v : V(Γ.toGraph), (φ.vertexEquiv v).1 ∈ D₀ A ↔ ιV v.1 ∈ V(A)) ∧
      (∀ e : E(Γ.toGraph), (φ.edgeEquiv e).1 ⊆ D₀ A ↔ ιE e.1 ∈ E(A)) := by
    intro A hA
    let i₀ : 𝒜 := ⟨A, hA⟩
    have hdiskSub : subBd (D₀ A) ⊆ D₀ A := subBd_subset_of subset_rfl (hD₀ A hA).1.isClosed
    refine ⟨?_, fun v => ?_, fun e => ?_⟩
    · apply subset_antisymm
      · rintro _ ⟨⟨z, hz, rfl⟩, hb⟩
        obtain ⟨i, hi⟩ := hsome z hz
        have hzb : ψ i z ∈ subBd (D₀ A) := hΦi i hi ▸ hb
        have hzX : z ∈ X₀ A := by
          by_cases hii : i = i₀
          · have hs : i.1 = A := congrArg Subtype.val hii
            exact hs ▸ h₃ i z hi (hs.symm ▸ hzb)
          · obtain ⟨h₅, h₆⟩ := hcross i i₀ hii z hi (hdiskSub hzb)
            exact ⟨h₅.1, h₆⟩
        exact ⟨⟨z, hzX.1⟩, hφv _, hzX.2⟩
      · rintro _ ⟨v, rfl, hv⟩
        rw [hφv, hΦX A hA v.1 ⟨v.2, hv⟩]
        refine ⟨?_, hα₀_bdA A hA (ιV v.1) hv⟩
        rw [← hΦX A hA v.1 ⟨v.2, hv⟩]
        exact mem_image_of_mem Φ (Γ.V_subset_U v.2)
    · rw [hφv]
      have hvU : v.1 ∈ Γ.U := Γ.V_subset_U v.2
      constructor
      · intro h₅
        obtain ⟨i, hi⟩ := hsome v.1 hvU
        by_cases hii : i = i₀
        · have hs : i.1 = A := congrArg Subtype.val hii
          have hi' : v.1 ∈ (Pd A).U := hs ▸ hi
          exact (hPU_V A hA v.1 hi' v.2).2
        · have h₆ : ψ i v.1 ∈ D₀ i₀.1 := hΦi i hi ▸ h₅
          have h_in_range := (hcross i i₀ hii v.1 hi h₆).2
          exact ((hπ_eq_Z A hA).subset h_in_range).2
      · intro h₅
        have h₆ : v.1 ∈ (Pd A).U := (Pd A).V_subset_U (by
          rw [hPV A hA]
          exact ⟨v.2, h₅⟩)
        rw [hΦi i₀ h₆]
        exact h₂ i₀ h₆
    · rw [hφe]
      have heH : e.1 ∈ Γ.E := e.2
      obtain ⟨z, hz⟩ := heH.1
      constructor
      · intro h₅
        obtain ⟨A₁, hA₁, h₆⟩ := hseg_edge e.1 heH
        by_cases hii : A₁ = A
        · exact hii ▸ h₆
        · have heP : e.1 ∈ (Pd A₁).E := by
            rw [hPE]
            exact ⟨heH, h₆⟩
          have hzU : z ∈ (Pd A₁).U := (Pd A₁).closure_subset_U heP (subset_closure hz)
          have h₇ : ψ ⟨A₁, hA₁⟩ z ∈ D₀ A := hΦi ⟨A₁, hA₁⟩ hzU ▸ h₅ (mem_image_of_mem Φ hz)
          have h₈ := hcross ⟨A₁, hA₁⟩ i₀ (fun h => hii (congrArg Subtype.val h)) z hzU h₇
          exact absurd h₈.1.1 (GM11.edge_notMem_V heH hz)
      · rintro h₅ _ ⟨y, hy, rfl⟩
        have heP : e.1 ∈ (Pd A).E := by
          rw [hPE]
          exact ⟨heH, h₅⟩
        have hyU : y ∈ (Pd A).U := (Pd A).closure_subset_U heP (subset_closure hy)
        rw [hΦi i₀ hyU]
        exact h₂ i₀ hyU
  obtain ⟨ψ_h, hψΔ₀, hψV, hψE, _, hψHU, _, hψ_bd⟩ :=
    GM14.theorem_6_4_proof hΔ₀ hbd_Δ₀_eq hΓ_Δ₀ hH'Δ₀ hΓ_bd hH'bd hV_bd_eq φ hφ_bd hrigid
  let α_map : α → S := fun x => ψ_h.symm (α₀ x)
  let D : Graph α β → Set S := fun A => ψ_h.symm '' D₀ A
  have hψ_symm_bd : ∀ y ∈ subBd Δ₀, ψ_h.symm y = y := fun y hy =>
    ψ_h.symm_apply_eq.mpr (hψ_bd y hy).symm
  have hD_disc : ∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ D A ⊆ Δ₀ := by
    intro A hA
    refine ⟨?_, ?_⟩
    · rcases (hD₀ A hA).1 with ⟨φ_d⟩
      exact ⟨φ_d.trans (ψ_h.symm.image (D₀ A))⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyΔ₀ : y ∈ ψ_h '' Δ₀ := hψΔ₀.symm ▸ (hD₀ A hA).2 hy
      obtain ⟨x, hxΔ₀, rfl⟩ := hyΔ₀
      simpa using hxΔ₀
  have hbd_D_img : ∀ A, subBd (D A) = ψ_h.symm '' subBd (D₀ A) :=
    fun A => (image_subBd ψ_h.symm (D₀ A)).symm
  refine ⟨α_map, D, ?_, hD_disc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hyΔ₀ : α₀ v ∈ ψ_h '' Δ₀ := hψΔ₀.symm ▸ hα₀_Δ₀ v hv
    obtain ⟨x, hxΔ₀, hxy⟩ := hyΔ₀
    change ψ_h.symm (α₀ v) ∈ Δ₀
    rw [← hxy, ψ_h.symm_apply_apply]
    exact hxΔ₀
  · intro p hp
    have hp_bd : p ∈ subBd Δ₀ := (hbd_Δ₀.symm ▸ hp).1
    change ψ_h.symm (α₀ (ιV p)) = p
    rw [hα₀_Pi p hp, hψ_symm_bd p hp_bd]
  · intro A hA v hv
    rw [hbd_D_img A]
    exact ⟨α₀ v, hα₀_bdA A hA v hv, rfl⟩
  · intro v hv A hA h_in
    obtain ⟨y, hyD₀, hy_eq⟩ := h_in
    have hy_val : α₀ v = y := ψ_h.symm.injective hy_eq.symm
    exact hα₀_inA v hv A hA (hy_val ▸ hyD₀)
  · intro A hA A' hA' hne
    change ψ_h.symm '' D₀ A ∩ ψ_h.symm '' D₀ A' = _
    rw [← image_inter ψ_h.symm.injective, hD₀_inter A hA A' hA' hne, ← image_comp]
    rfl
  · intro A hA
    have hbd_symm : subBd Δ₀ = ψ_h.symm '' subBd Δ₀ := by
      ext y
      simp only [mem_image]
      exact ⟨fun hy => ⟨y, hy, hψ_symm_bd y hy⟩,
        fun ⟨z, hz, hzy⟩ => by rwa [← hzy, hψ_symm_bd z hz]⟩
    change ψ_h.symm '' D₀ A ∩ subBd Δ₀ = _
    rw [hbd_symm, ← image_inter ψ_h.symm.injective, hD₀_bdΔ₀ A hA, ← image_comp]
    rfl
  · intro v hv v' hv' hne heq
    exact hα₀_inj_ne v hv v' hv' hne (ψ_h.symm.injective heq)
  · intro v hv hvZ
    obtain ⟨A, hA, hvA⟩ := hseg_vertex v hv
    have hvX : v ∈ X₀ A := ⟨hv, (hπ_eq_Z A hA).symm ▸ ⟨hvZ, hvA⟩⟩
    change ψ_h.symm (α₀ (ιV v)) = v
    rw [← hΦX A hA v hvX, ← hφv ⟨v, hv⟩, ← hψV ⟨v, hv⟩, ψ_h.symm_apply_apply]
  · intro v hvZ
    constructor
    · intro h_in_U
      have hα₀_in_H' : α₀ v ∈ H'.U := by
        rw [← hψHU]
        exact ⟨α_map v, h_in_U, ψ_h.apply_symm_apply (α₀ v)⟩
      obtain ⟨z, hzU, hz_eq⟩ := hα₀_in_H'
      obtain ⟨i, hi⟩ := hsome z hzU
      have hψiz_eq : ψ i z = α₀ v := (hΦi i hi).symm.trans hz_eq
      have h_in_D₀ : α₀ v ∈ D₀ i.1 := hψiz_eq ▸ h₂ i hi
      have hv_range : v ∈ Set.range (πA i.1) := hα₀_inA v hvZ i.1 i.2 h_in_D₀
      have hψiz_bd : ψ i z ∈ subBd (D₀ i.1) := hψiz_eq ▸ hα₀_bdA i.1 i.2 v hv_range
      have hzX : z ∈ X₀ i.1 := h₃ i z hi hψiz_bd
      have h_α_eq : α₀ (ιV z) = α₀ v := (h₄ i z hzX).symm.trans hψiz_eq
      have hzZ : ιV z ∈ Z := ((hπ_eq_Z i.1 i.2).subset hzX.2).1
      have hv_eq : ιV z = v := hα₀_inj (ιV z) hzZ v hvZ h_α_eq
      exact ⟨z, hzX.1, hv_eq⟩
    · rintro ⟨x, hxV, rfl⟩
      obtain ⟨A, hA, hxA⟩ := hseg_vertex x hxV
      have hxX : x ∈ X₀ A := ⟨hxV, (hπ_eq_Z A hA).symm ▸ ⟨hvZ, hxA⟩⟩
      have h_eq : α_map (ιV x) = x := by
        change ψ_h.symm (α₀ (ιV x)) = x
        rw [← hΦX A hA x hxX, ← hφv ⟨x, hxV⟩, ← hψV ⟨x, hxV⟩, ψ_h.symm_apply_apply]
      rw [h_eq]
      exact Γ.V_subset_U hxV
  · intro A hA
    obtain ⟨hbd_A, hV_A, hE_A⟩ := h_ii A hA
    have hbd_inter : subBd (D A) ∩ Γ.U = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} := by
      ext x
      simp only [hbd_D_img A, mem_inter_iff, mem_image, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨y, hybd, rfl⟩, hxU⟩
        have hyH'U : y ∈ H'.U := by
          rw [← hψHU]
          exact ⟨ψ_h.symm y, hxU, ψ_h.apply_symm_apply y⟩
        have hy_in : y ∈ H'.U ∩ subBd (D₀ A) := ⟨hyH'U, hybd⟩
        rw [hbd_A] at hy_in
        obtain ⟨v, rfl, hv_bar⟩ := hy_in
        rw [← hψV v, ψ_h.symm_apply_apply]
        exact ⟨v.2, hv_bar⟩
      · rintro ⟨hxV, hx_bar⟩
        refine ⟨⟨ψ_h x, ?_, ψ_h.symm_apply_apply x⟩, Γ.V_subset_U hxV⟩
        have hxH' : ψ_h x ∈ H'.U ∩ subBd (D₀ A) := by
          rw [hbd_A]
          exact ⟨⟨x, hxV⟩, (hψV ⟨x, hxV⟩).symm, hx_bar⟩
        exact hxH'.2
    have hV_mem_iff : ∀ v ∈ Γ.V, v ∈ D A ↔ ιV v ∈ V(A) := by
      intro v hvV
      have h1 := (hV_A ⟨v, hvV⟩).symm
      have h2 : ψ_h v = (φ.vertexEquiv ⟨v, hvV⟩).1 := hψV ⟨v, hvV⟩
      rw [h1, ← h2]
      exact ⟨fun ⟨y, hy, hy_eq⟩ => by rwa [← hy_eq, ψ_h.apply_symm_apply],
        fun h => ⟨ψ_h v, h, ψ_h.symm_apply_apply v⟩⟩
    have hE_sub_iff : ∀ e ∈ Γ.E, e ⊆ D A ↔ ιE e ∈ E(A) := by
      intro e heE
      have h1 := (hE_A ⟨e, heE⟩).symm
      have h2 : ψ_h '' e = (φ.edgeEquiv ⟨e, heE⟩).1 := hψE ⟨e, heE⟩
      rw [h1, ← h2]
      constructor
      · rintro hsub _ ⟨x, hxe, rfl⟩
        obtain ⟨y, hy, hy_eq⟩ := hsub hxe
        rwa [← hy_eq, ψ_h.apply_symm_apply]
      · intro hsub x hxe
        exact ⟨ψ_h x, hsub (mem_image_of_mem ψ_h hxe), ψ_h.symm_apply_apply x⟩
    have hinter_E : (Γ.interSet (D A)).E = {e ∈ Γ.E | ιE e ∈ E(A)} := by
      change (Γ.span _ _).E = _
      rw [Γ.span_E]
      ext e
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨⟨heE, he_sub⟩, _⟩ => ⟨heE, (hE_sub_iff e heE).mp he_sub⟩,
        fun ⟨heE, heA⟩ => ⟨⟨heE, (hE_sub_iff e heE).mpr heA⟩, heE⟩⟩
    have hinter_V : (Γ.interSet (D A)).V = {v ∈ Γ.V | ιV v ∈ V(A)} := by
      change (Γ.span (Γ.V ∩ D A) {e ∈ Γ.E | e ⊆ D A}).V = _
      have hV_cap : Γ.V ∩ D A = {v ∈ Γ.V | ιV v ∈ V(A)} := by
        ext v
        simp only [mem_inter_iff, mem_ofPred_eq]
        exact and_congr_right (hV_mem_iff v)
      apply Subset.antisymm
      · rintro v (⟨hv, -⟩ | hv)
        · rwa [← hV_cap]
        · obtain ⟨e, ⟨⟨heE, he_sub⟩, -⟩, hve, hvV⟩ := mem_iUnion₂.mp hv
          have hvD : v ∈ D A := (hD_disc A hA).1.isClosed.closure_subset_iff.mpr he_sub hve
          rw [← hV_cap]
          exact ⟨hvV, hvD⟩
      · intro v hv
        rw [← hV_cap] at hv
        exact Or.inl ⟨hv, hv.1⟩
    refine ⟨hbd_inter, hinter_V, hinter_E, ?_⟩
    have hsub_inter : (Γ.interSet (D A)).IsSubdrawing Γ := Γ.span_isSubdrawing _ _
    have hA_le_J : A ≤ J := hZdiv.2.1 A hA
    ext x y
    · simp only [Drawing.toEmbeddedGraph, Graph.vertexSet_inf, hinter_V, mem_image,
        mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨v, ⟨hvV, hvA⟩, rfl⟩
        exact ⟨⟨v, hvV, rfl⟩, hvA⟩
      · rintro ⟨⟨v, hvV, rfl⟩, hvA⟩
        exact ⟨v, ⟨hvV, hvA⟩, rfl⟩
    · simp only [Drawing.toEmbeddedGraph, inf_isLink]
      constructor
      · rintro ⟨e₀, x₀, y₀, hlk, rfl, rfl, rfl⟩
        have he₀_mem : e₀ ∈ (Γ.interSet (D A)).E := hlk.edge_mem
        have hlk_Γ : Γ.toGraph.IsLink e₀ x₀ y₀ := (hsub_inter.isLink_iff he₀_mem).mp hlk
        rw [hinter_E] at he₀_mem
        have hlk_emb : (Γ.toEmbeddedGraph ιV ιE).IsLink (ιE e₀) (ιV x₀) (ιV y₀) :=
          ⟨e₀, x₀, y₀, hlk_Γ, rfl, rfl, rfl⟩
        have hlk_J : J.IsLink (ιE e₀) (ιV x₀) (ιV y₀) := hlk_emb.mono hΓ_le_J
        exact ⟨hlk_emb, (hA_le_J.isLink_iff he₀_mem.2).mpr hlk_J⟩
      · rintro ⟨⟨e₀, x₀, y₀, hlk_Γ, rfl, rfl, rfl⟩, hlk_A⟩
        have he₀_mem : e₀ ∈ (Γ.interSet (D A)).E := by
          rw [hinter_E]
          exact ⟨hlk_Γ.edge_mem, hlk_A.edge_mem⟩
        exact ⟨e₀, x₀, y₀, (hsub_inter.isLink_iff he₀_mem).mpr hlk_Γ, rfl, rfl, rfl⟩

/-- **Claim (3)** in the proof of Theorem (8.3) (Graph Minors XXII, Section 8, page 560):
"(3) $Z \subseteq \Delta_0$ and $Z \cap \text{bd}(\Delta_0) = \Pi$; and for each
$A \in \mathcal{A}$ there exists a closed disc $D(A) \subseteq \Delta_0$, such that
- for each $A \in \mathcal{A}$, $\text{bd}(D(A))$ is $\Gamma$-normal and
  $\text{bd}(D(A)) \cap \text{bd}(\Delta_0) \subseteq \Pi$,
- for each $A \in \mathcal{A}$, $\Gamma \cap D(A) = \Gamma \cap A$, and
  $\text{bd}(D(A)) \cap V(\Gamma) = \bar{\pi}(A)$,
- for all distinct $A, A' \in \mathcal{A}$,
  $D(A) \cap D(A') = \bar{\pi}(A) \cap \bar{\pi}(A')$." -/
theorem lemma_8_3_claim_3
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀)
    (hΓ_Δ₀ : Γ.U ⊆ Δ₀) (hbd_Δ₀ : subBd Δ₀ ∩ Γ.U = PiSet)
    (e_C_Δ₀ : C₀.U ≃ₜ subBd Δ₀)
    (he_C_Δ₀ : ∀ y : C₀.U, y.1 ∈ PiSet → (e_C_Δ₀ y).1 = y.1) :
    ∃ (α_map : α → S) (D : Graph α β → Set S),
      α_map '' Z ⊆ Δ₀ ∧
      (α_map '' Z) ∩ subBd Δ₀ = PiSet ∧
      (∀ p ∈ PiSet, α_map (ιV p) = p) ∧
      (∀ v ∈ Γ.V, ιV v ∈ Z → α_map (ιV v) = v) ∧
      (∀ v ∈ Z, α_map v ∈ Γ.U ↔ v ∈ ιV '' Γ.V) ∧
      InjOn α_map Z ∧
      (∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ D A ⊆ Δ₀) ∧
      (∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U ⊆ Γ.V ∧ subBd (D A) ∩ subBd Δ₀ ⊆ PiSet) ∧
      (∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), α_map v ∈ subBd (D A)) ∧
      (∀ v ∈ Z, ∀ A ∈ 𝒜, α_map v ∈ D A → v ∈ Set.range (πA A)) ∧
      (∀ A ∈ 𝒜,
        subBd (D A) ∩ Γ.U = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} ∧
        subBd (D A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} ∧
        (Γ.interSet (D A)).V = {v ∈ Γ.V | ιV v ∈ V(A)} ∧
        (Γ.interSet (D A)).E = {e ∈ Γ.E | ιE e ∈ E(A)} ∧
        (Γ.interSet (D A)).toEmbeddedGraph ιV ιE = (Γ.toEmbeddedGraph ιV ιE) ⊓ A) ∧
      (∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' →
        D A ∩ D A' = α_map '' (Set.range (πA A) ∩ Set.range (πA A'))) ∧
      (∀ A ∈ 𝒜,
        D A ∩ subBd Δ₀ = α_map '' (Set.range (πA A) ∩ (ιV '' PiSet))) := by
  obtain ⟨α_map, D, hα_Δ₀, hD, hα_Pi, hα_bdA, hα_inA, hD_inter, hD_bdΔ₀,
      hα_inj_ne, hα_ΓV, hα_ΓU, hA_props⟩ :=
    lemma_8_3_claim_2 h83 hord hΔ₀ hΓ_Δ₀ hbd_Δ₀ e_C_Δ₀ he_C_Δ₀
  have hinj : InjOn α_map Z := by
    intro v hv v' hv' heq
    by_contra hne
    exact hα_inj_ne v hv v' hv' hne heq
  have hπ_eq_Z : ∀ A ∈ 𝒜, Set.range (πA A) = Z ∩ V(A) :=
    fun A hA => (h83.hyp_vii A hA).2.2
  have hZdiv : IsZDivision J (Z ∪ W) 𝒜 := h83.hyp_vi.2.2.1
  have hZ_in_A : ∀ v ∈ Z, ∃ A ∈ 𝒜, v ∈ Set.range (πA A) := by
    intro v hvZ
    have hvJ : v ∈ V(J) := (h83.hyp_vi.1 hvZ).1
    have hVu : (⋃ A ∈ 𝒜, V(A)) = V(J) := congrArg Graph.vertexSet hZdiv.2.2.1
    rw [← hVu] at hvJ
    obtain ⟨A, hA, hvA⟩ := mem_iUnion₂.mp hvJ
    exact ⟨A, hA, (hπ_eq_Z A hA).symm ▸ ⟨hvZ, hvA⟩⟩
  refine ⟨α_map, D, ?_, ?_, hα_Pi, hα_ΓV, hα_ΓU, hinj, hD, ?_, hα_bdA, hα_inA, ?_, hD_inter, hD_bdΔ₀⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hα_Δ₀ v hv
  · apply Subset.antisymm
    · rintro _ ⟨⟨v, hvZ, rfl⟩, hbd⟩
      obtain ⟨A, hA, hvA⟩ := hZ_in_A v hvZ
      have h_in_D : α_map v ∈ D A ∩ subBd Δ₀ :=
        ⟨subBd_subset_of subset_rfl (hD A hA).1.isClosed (hα_bdA A hA v hvA), hbd⟩
      rw [hD_bdΔ₀ A hA] at h_in_D
      obtain ⟨q, ⟨_, p, hpPi, rfl⟩, hq_eq⟩ := h_in_D
      rw [← hq_eq, hα_Pi p hpPi]
      exact hpPi
    · intro p hpPi
      have hpZ : ιV p ∈ Z := h83.hyp_vi.2.1 ⟨p, hpPi, rfl⟩
      refine ⟨⟨ιV p, hpZ, hα_Pi p hpPi⟩, ?_⟩
      exact (hbd_Δ₀.symm ▸ hpPi).1
  · intro A hA
    obtain ⟨hbd_U, _, _, _⟩ := hA_props A hA
    refine ⟨?_, ?_⟩
    · rw [hbd_U]
      exact fun v hv => hv.1
    · intro x ⟨hx_bdA, hx_bdΔ₀⟩
      have hx_in : x ∈ D A ∩ subBd Δ₀ :=
        ⟨subBd_subset_of subset_rfl (hD A hA).1.isClosed hx_bdA, hx_bdΔ₀⟩
      rw [hD_bdΔ₀ A hA] at hx_in
      obtain ⟨q, ⟨_, p, hpPi, rfl⟩, rfl⟩ := hx_in
      rw [hα_Pi p hpPi]
      exact hpPi
  · intro A hA
    obtain ⟨hbd_U, hV_A, hE_A, hG_A⟩ := hA_props A hA
    have hbd_V : subBd (D A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} := by
      have hsub : subBd (D A) ∩ Γ.V = (subBd (D A) ∩ Γ.U) ∩ Γ.V := by
        rw [Set.inter_assoc, inter_eq_self_of_subset_right Γ.V_subset_U]
      rw [hsub, hbd_U]
      ext v
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h.1⟩⟩
    exact ⟨hbd_U, hbd_V, hV_A, hE_A, hG_A⟩

end GraphMinor.GM22
