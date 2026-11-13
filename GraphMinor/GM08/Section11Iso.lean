module

public import GraphMinor.GM08.Section11Cells

/-!
# An isomorphism as a pair of maps

For the proof of Graph Minors VIII, (11.2) we move between a graph `G` and the graph of its drawing
`Γ`. Here an isomorphism `a : Iso G H` is read as a map `a.fv` on vertices and a map `a.fe` on
edges, with junk values off `V(G)` and `E(G)`. A walk of `H` between images of vertices of `G`
gives a sequence of links of `G` (`Iso.reflTransGen_of_walk`).
-/

public section

namespace GraphMinor

open Set Graph Surface

variable {α β γ δ : Type*} {G : Graph α β} {H : Graph γ δ}

namespace Iso

variable (a : Iso G H) [Nonempty γ] [Nonempty δ]

open Classical in
/-- The vertex map of an isomorphism. -/
noncomputable def fv (v : α) : γ :=
  if h : v ∈ V(G) then (a.vertexEquiv ⟨v, h⟩).1 else Classical.arbitrary γ

open Classical in
/-- The edge map of an isomorphism. -/
noncomputable def fe (e : β) : δ :=
  if h : e ∈ E(G) then (a.edgeEquiv ⟨e, h⟩).1 else Classical.arbitrary δ

variable {a}

theorem fv_of_mem {v : α} (h : v ∈ V(G)) : a.fv v = (a.vertexEquiv ⟨v, h⟩).1 := by
  classical
  simp only [fv, dite_eq_left h]

theorem fe_of_mem {e : β} (h : e ∈ E(G)) : a.fe e = (a.edgeEquiv ⟨e, h⟩).1 := by
  classical
  simp only [fe, dite_eq_left h]

theorem fv_mem {v : α} (h : v ∈ V(G)) : a.fv v ∈ V(H) := by
  rw [fv_of_mem h]; exact (a.vertexEquiv _).2

theorem fe_mem {e : β} (h : e ∈ E(G)) : a.fe e ∈ E(H) := by
  rw [fe_of_mem h]; exact (a.edgeEquiv _).2

theorem fv_injOn : InjOn a.fv V(G) := by
  intro x hx y hy hxy
  rw [fv_of_mem hx, fv_of_mem hy] at hxy
  have := a.vertexEquiv.injective (Subtype.ext hxy)
  exact congrArg Subtype.val this

theorem fe_injOn : InjOn a.fe E(G) := by
  intro x hx y hy hxy
  rw [fe_of_mem hx, fe_of_mem hy] at hxy
  have := a.edgeEquiv.injective (Subtype.ext hxy)
  exact congrArg Subtype.val this

theorem exists_fv {s : γ} (hs : s ∈ V(H)) : ∃ v ∈ V(G), a.fv v = s := by
  obtain ⟨v, hv⟩ := a.vertexEquiv.surjective ⟨s, hs⟩
  exact ⟨v.1, v.2, by rw [fv_of_mem v.2, hv]⟩

theorem exists_fe {f : δ} (hf : f ∈ E(H)) : ∃ e ∈ E(G), a.fe e = f := by
  obtain ⟨e, he⟩ := a.edgeEquiv.surjective ⟨f, hf⟩
  exact ⟨e.1, e.2, by rw [fe_of_mem e.2, he]⟩

theorem isLink_iff' {e : β} {x y : α} (he : e ∈ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.IsLink e x y ↔ H.IsLink (a.fe e) (a.fv x) (a.fv y) := by
  rw [fe_of_mem he, fv_of_mem hx, fv_of_mem hy]
  exact a.isLink_iff ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩

theorem isLink_fv {e : β} {x y : α} (h : G.IsLink e x y) : H.IsLink (a.fe e) (a.fv x) (a.fv y) :=
  (isLink_iff' h.edge_mem h.left_mem h.right_mem).mp h

theorem exists_isLink {f : δ} {p q : γ} (h : H.IsLink f p q) :
    ∃ e x y, G.IsLink e x y ∧ a.fe e = f ∧ a.fv x = p ∧ a.fv y = q := by
  obtain ⟨e, he, rfl⟩ := exists_fe (a := a) h.edge_mem
  obtain ⟨x, hx, rfl⟩ := exists_fv (a := a) h.left_mem
  obtain ⟨y, hy, rfl⟩ := exists_fv (a := a) h.right_mem
  exact ⟨e, x, y, (isLink_iff' he hx hy).mpr h, rfl, rfl, rfl⟩

theorem inc_iff' {e : β} {x : α} (he : e ∈ E(G)) (hx : x ∈ V(G)) :
    G.Inc e x ↔ H.Inc (a.fe e) (a.fv x) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, isLink_fv hy⟩
  · rintro ⟨q, hq⟩
    obtain ⟨y, hy, rfl⟩ := exists_fv (a := a) hq.right_mem
    exact ⟨y, (isLink_iff' he hx hy).mpr hq⟩

/-- A walk of `H` between images of vertices of `G`, inside a set `Z` and avoiding a set `Eb` of
edges, gives a chain of links of `G` between vertices mapped into `Z` by edges not mapped into
`Eb`. -/
theorem reflTransGen_of_walk {Z : Set γ} {Eb : Set δ} {p q : γ} (W : GraphWalk H p q)
    (hZ : ∀ z ∈ W.support, z ∈ Z) (hE : ∀ f ∈ W.edges, f ∉ Eb) {x y : α} (hx : x ∈ V(G))
    (hy : y ∈ V(G)) (hxp : a.fv x = p) (hyq : a.fv y = q) :
    Relation.ReflTransGen (fun u w => a.fv u ∈ Z ∧ a.fv w ∈ Z ∧
      ∃ e, a.fe e ∉ Eb ∧ G.IsLink e u w) x y := by
  induction W generalizing x with
  | nil hv =>
    subst hxp
    have : x = y := fv_injOn hx hy hyq.symm
    subst this
    exact .refl
  | @cons u w' v' f hl rest ih =>
    subst hxp
    obtain ⟨w, hw, rfl⟩ := exists_fv (a := a) hl.right_mem
    obtain ⟨e, he, rfl⟩ := exists_fe (a := a) hl.edge_mem
    have hl' : G.IsLink e x w := (isLink_iff' he hx hw).mpr hl
    refine Relation.ReflTransGen.head ⟨hZ _ (by simp), hZ _ ?_, e, hE _ (by simp), hl'⟩
      (ih (fun z hz => hZ z (by simp [hz])) (fun f hf => hE f (by simp [hf])) hw rfl hyq)
    simp [GraphWalk.start_mem_support]

end Iso

/-- If any two points of `Z` are joined by a chain of links of `G'` inside `Z`, then `Z` is the
vertex set of a connected subgraph of `G'`. -/
theorem exists_graphConnected_of_reflTransGen {G' : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G'))
    (hne : Z.Nonempty)
    (h : ∀ x ∈ Z, ∀ y ∈ Z, Relation.ReflTransGen
      (fun u w => u ∈ Z ∧ w ∈ Z ∧ G'.Adj u w) x y) :
    ∃ K ≤ G', V(K) = Z ∧ GraphConnected K := by
  refine ⟨G'.induce Z, induce_le hZ, rfl, hne, fun x hx y hy => ?_⟩
  refine Relation.ReflTransGen.mono ?_ x y (h x hx y hy)
  rintro u w ⟨hu, hw, e, hl⟩
  exact ⟨e, hl, hu, hw⟩

end GraphMinor
