module

public import GraphMinor.GM05.SeriesParallelDefs
public import GraphMinor.Minor.Model
import GraphMinor.GM01.Basic
import GraphMinor.Minor.Basic

/-!
# Passing from a multigraph to its simple shadow

Choose one edge between each pair of distinct adjacent vertices and discard
loops. Singleton branch sets give a minor model of the simple shadow. If the
ambient edge type is empty, use an isomorphism of edgeless graphs instead.
This permits the mesh proof of Graph Minors V, (1.6), to apply to multigraphs.
-/

public section

namespace GraphMinor.GM05

open Graph SimpleGraph Set GM01

variable {α β : Type*}

/-- Taking the simple shadow preserves the subgraph order. -/
theorem simpleShadow_mono {H G : Graph α β} (h : H ≤ G) : simpleShadow H ≤ simpleShadow G :=
  ⟨h.vertexSet_mono, fun _ _ hadj ↦ ⟨hadj.1, Graph.Adj.mono h hadj.2⟩⟩

/-- Loops and parallel copies do not change connectivity. Thus components
may be represented by the connected components of the simple shadow. -/
theorem graphConnected_iff_simpleShadow_connected (G : Graph α β) :
    GraphConnected G ↔ (simpleShadow G).Connected := by
  rw [← graphConnected_toGraph_iff]
  constructor
  · rintro ⟨hne, hreach⟩
    have lift : ∀ {x y}, Relation.ReflTransGen G.Adj x y →
        Relation.ReflTransGen (toGraph (simpleShadow G)).Adj x y := by
      intro x y hxy
      induction hxy with
      | refl => exact .refl
      | @tail y z hxy hyz ih =>
        by_cases he : y = z
        · subst z
          exact ih
        · exact .tail ih ((adj_toGraph _ _ _).mpr ⟨he, hyz⟩)
    exact ⟨hne, fun x hx y hy ↦ lift (hreach x hx y hy)⟩
  · rintro ⟨hne, hreach⟩
    have lift : ∀ {x y}, Relation.ReflTransGen (toGraph (simpleShadow G)).Adj x y →
        Relation.ReflTransGen G.Adj x y := by
      intro x y hxy
      induction hxy with
      | refl => exact .refl
      | tail hxy hyz ih => exact .tail ih (((adj_toGraph _ _ _).mp hyz).2)
    exact ⟨hne, fun x hx y hy ↦ lift (hreach x hx y hy)⟩

/-- Deleting loops and merging parallel edges produces a minor with the
same vertices. -/
theorem simpleShadow_isIsoMinor (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) : IsIsoMinor (toGraph (simpleShadow G)) G := by
  classical
  let H := toGraph (simpleShadow G)
  cases isEmpty_or_nonempty β with
  | inl hβ =>
    let : IsEmpty β := hβ
    have hno : ∀ e, e ∈ E(H) → False := by
      intro e he
      obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
      have hAdj : G.Adj x y := hxy.2.2
      obtain ⟨f, hf⟩ := hAdj
      exact isEmptyElim f
    let φ : Iso H G := {
      vertexEquiv := Equiv.refl _
      edgeEquiv := {
        toFun := fun e ↦ (hno e.1 e.2).elim
        invFun := fun e ↦ isEmptyElim e.1
        left_inv := fun e ↦ (hno e.1 e.2).elim
        right_inv := fun e ↦ isEmptyElim e.1 }
      isLink_iff := fun e _ _ ↦ (hno e.1 e.2).elim }
    exact φ.isIsoMinor_left (.refl G)
  | inr hβ =>
    let : Nonempty β := hβ
    have hex : ∀ e : Sym2 α, ∃ f : β,
        ∀ x y, H.IsLink e x y → G.IsLink f x y := by
      intro e
      by_cases he : e ∈ E(H)
      · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
        obtain ⟨f, hf⟩ := (show G.Adj x y from hxy.2.2)
        refine ⟨f, ?_⟩
        intro z w hzw
        have hp : s(x, y) = s(z, w) := hxy.1.symm.trans hzw.1
        rcases Sym2.eq_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hf
        · exact hf.symm
      · refine ⟨Classical.choice hβ, fun x y hxy ↦ ?_⟩
        exact (he hxy.edge_mem).elim
    choose ηe hηe using hex
    have hm : IsMinorModel H G (fun v ↦ {v}) ηe := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv
        exact singleton_nonempty v
      · intro v hv x hx
        exact hx ▸ hv
      · intro e he
        obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
        exact (hηe e x y hxy).edge_mem
      · intro v hv u hu hne
        exact disjoint_singleton.mpr hne
      · intro e he f hf hef
        obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
        obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet hf
        have h₁ := hηe e x y hxy
        have h₂ := hηe f z w hzw
        rw [← hef] at h₂
        have hp := h₁.isLink_iff_sym2_eq.mp h₂
        exact hxy.1.trans (hp.trans hzw.1.symm)
      · intro v hv e he
        constructor
        · rintro ⟨u, hlink⟩
          exact ⟨v, rfl, (hηe e v u hlink).inc_left⟩
        · rintro ⟨x, rfl, hx⟩
          obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet he
          rcases hx.eq_or_eq_of_isLink (hηe e a b hab) with rfl | rfl
          · exact hab.inc_left
          · exact hab.inc_right
      · intro v hv e he
        constructor
        · intro hloop
          exact (hloop.2.1 rfl).elim
        · intro hall
          obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet he
          have hne : a ≠ b := hab.2.1
          have hlink := hηe e a b hab
          have ha : a = v := hall a hlink.inc_left
          have hb : b = v := hall b hlink.inc_right
          exact (hne (ha.trans hb.symm)).elim
      · intro v hv
        refine ⟨Graph.noEdge {v} β, ?_, rfl, ?_⟩
        · rw [Graph.noEdge_le_iff]
          exact singleton_subset_iff.mpr hv
        · refine ⟨singleton_nonempty v, ?_⟩
          intro x hx y hy
          have hxv : x = v := hx
          have hyv : y = v := hy
          subst x
          subst y
          exact .refl
    exact isIsoMinor_of_isMinorModel H G hV (finite_edgeSet_of_finite_verts hV)
      hV hE (fun v ↦ {v}) ηe hm

end GraphMinor.GM05
