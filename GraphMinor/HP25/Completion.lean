module

public import GraphMinor.HP25.WebSplit
import GraphMinor.HP25.Prop22
import GraphMinor.HP25.Prop31
import GraphMinor.HP25.Prop32
import GraphMinor.HP25.Prop34
import GraphMinor.HP25.CycleEdges

/-!
# Maximally crossless graphs on a vertex set, and their completions

The proof of Lemma 4.3 (Humeau and Pous, pages 13–15) works by induction on the number of vertices,
and applies the induction hypothesis to subgraphs. We therefore work with graphs on a vertex set `S`
(`IsSupportedOn G S`), as for webs (`IsWebOn`):

* `IsMaxCrosslessOn G S C`: `G` on `S` is maximally `C`-crossless (Definition 2.4, page 7), where
  the edge extensions only add edges between vertices of `S`;
* `IsMaxCrosslessOn.eq_of_le`: a maximally crossless graph is equal to every crossless graph on the
  same vertex set that contains it;
* `exists_maxCrosslessOn`: a crossless graph on a finite set has a maximally crossless supergraph on
  the same set (add edges as long as the frame stays crossless);
* `IsMaxCrosslessOn.isWebOn_three`: the base case of Lemma 4.3, frames of length three;
* `IsMaxCrosslessOn.eq_sup_of_pieces`: if `G` is maximally crossless, splits along a path `l` into
  two sides, and each side lies in a web on that side with the matching frame in which `l` is still
  induced, then `G` is the union of the two webs, and so a web by Proposition 3.1.

The last statement is how both cases of the proof of Lemma 4.3 conclude: the paper applies the
induction hypothesis to the sides, which it shows to be maximally crossless; we apply it to
maximally crossless supergraphs of the sides and recover `G` from its maximality.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V}

/-- `G` on the vertex set `S` is *maximally `C`-crossless* (Definition 2.4, page 7: "The graph $G$
is *maximally $T$-crossless* when $T$ is crossless and in any edge extension of $G$, $T$ crossed"),
where an edge extension adds an edge between two vertices of `S`. -/
@[expose] def IsMaxCrosslessOn (G : SimpleGraph V) (S : Set V) (C : List V) : Prop :=
  IsSupportedOn G S ∧ ¬ IsCrossed G C ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v → IsCrossed (G ⊔ edge u v) C

/-- On all the vertices, this is `IsMaximallyCrossless`. -/
theorem isMaxCrosslessOn_univ_iff {C : List V} :
    IsMaxCrosslessOn G univ C ↔ IsMaximallyCrossless G C :=
  ⟨fun h => ⟨h.2.1, fun u v huv hn => h.2.2 u trivial v trivial huv hn⟩,
    fun h => ⟨fun _ _ _ => trivial, h.1, fun u _ v _ huv hn => h.2 u v huv hn⟩⟩

/-- A maximally crossless graph on `S` equals every crossless graph on `S` that contains it. -/
theorem IsMaxCrosslessOn.eq_of_le {S : Set V} {C : List V} {G' : SimpleGraph V}
    (h : IsMaxCrosslessOn G S C) (hle : G ≤ G') (hs : IsSupportedOn G' S)
    (hc : ¬ IsCrossed G' C) : G = G' := by
  refine le_antisymm hle fun u v huv => ?_
  by_contra hn
  refine hc ((h.2.2 u (hs huv) v (hs huv.symm) (G'.ne_of_adj huv) hn).mono ?_)
  exact sup_le hle ((edge_le_iff G').mpr (Or.inr huv))

/-- **Completions.** A `C`-crossless graph on a finite vertex set `S` is contained in a maximally
`C`-crossless graph on `S`. -/
theorem exists_maxCrosslessOn [Finite V] {S : Set V} {C : List V} (hs : IsSupportedOn G S)
    (hc : ¬ IsCrossed G C) : ∃ G', G ≤ G' ∧ IsMaxCrosslessOn G' S C := by
  let s : Set (SimpleGraph V) := {G' | G ≤ G' ∧ IsSupportedOn G' S ∧ ¬ IsCrossed G' C}
  obtain ⟨G', ⟨hle, hs', hc'⟩, hmax⟩ := Set.Finite.exists_maximal (s := s) (Set.toFinite s)
    ⟨G, le_rfl, hs, hc⟩
  refine ⟨G', hle, hs', hc', fun u hu v hv huv hn => ?_⟩
  by_contra hnc
  have hs'' : IsSupportedOn (G' ⊔ edge u v) S := by
    intro a b hab
    rcases hab with hab | hab
    · exact hs' hab
    · rcases (edge_adj u v a b).mp hab with ⟨⟨rfl, -⟩ | ⟨rfl, -⟩, -⟩
      · exact hu
      · exact hv
  have := hmax ⟨hle.trans le_sup_left, hs'', hnc⟩ le_sup_left
  exact hn (this (Or.inr ((edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩)))

/-- A tuple of at most three vertices is never crossed: a crossing needs four positions. -/
theorem not_isCrossed_of_length_le_three {C : List V} (h3 : C.length ≤ 3) : ¬ IsCrossed G C := by
  rintro ⟨a, b, c, d, Q, R, ⟨i, r, j, s, hir, hrj, hjs, -, -, -, hs⟩, -⟩
  have := (List.getElem?_eq_some_iff.mp hs).1
  omega

/-- **The base case of Lemma 4.3.** A maximally crossless graph on `S` whose frame is a triangle of
`S` is a web: it is complete on `S`, since no tuple of three vertices is crossed, and so a web by
Proposition 2.2. -/
theorem IsMaxCrosslessOn.isWebOn_three {S : Set V} {a b c : V}
    (h : IsMaxCrosslessOn G S [a, b, c]) (hC : IsCycleList G [a, b, c])
    (hCS : ∀ v ∈ [a, b, c], v ∈ S) : IsWebOn G S [a, b, c] := by
  have hnd := hC.2.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  refine isWebOn_three_iff.mpr ⟨⟨hCS a (by simp), hCS b (by simp), hCS c (by simp), hnd.1.1,
    hnd.2.1, hnd.1.2⟩, fun x y => ⟨fun hxy => ⟨h.1 hxy, h.1 hxy.symm, G.ne_of_adj hxy⟩,
    fun ⟨hx, hy, hxy⟩ => ?_⟩⟩
  by_contra hn
  exact not_isCrossed_of_length_le_three (by simp) (h.2.2 x hx y hy hxy hn)

/-! ### Frames and their edges -/

/-- The frame of a web is a cycle of the web. -/
theorem IsWebOn.isCycleList {S : Set V} {C : List V} (h : IsWebOn G S C) : IsCycleList G C := by
  obtain ⟨-, -, -, -, ⟨hC, -⟩, -⟩ := h
  exact hC

/-- Consecutive vertices of a cycle are adjacent. -/
theorem IsCycleList.adj_of_isCycleEdge {C : List V} (hC : IsCycleList G C) {u v : V}
    (h : IsCycleEdge C u v) : G.Adj u v := by
  obtain ⟨p, hp, he⟩ := h
  have := hC.2.2 p hp
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact this
  · exact this.symm

/-- Consecutive entries of a beginning of a cycle are adjacent. -/
theorem IsCycleList.adj_of_isListEdge {X Y : List V} (hC : IsCycleList G (X ++ Y)) {u v : V}
    (h : IsListEdge X u v) : G.Adj u v := by
  cases X with
  | nil => simp [IsListEdge] at h
  | cons x X =>
    refine hC.adj_of_isCycleEdge (isCycleEdge_of_isListEdge (t := X ++ Y) ?_)
    have := h.append_left (l₂ := Y ++ [x])
    simpa using this

/-- The rotation of `a A b B` that starts at `b`. -/
theorem rotate_cons_append_cons (a b : V) (A B : List V) :
    (a :: A ++ b :: B).rotate (A.length + 1) = b :: B ++ a :: A := by
  rw [List.rotate_eq_drop_append_take (by simp)]
  simp

/-! ### Concluding from two sides -/

/-- **The union of two webs glued along an induced path.** Let `C` be a rotation of `a A b B`,
`S₁ ∪ S₂ = S` with `S₁ ∩ S₂` the path `l = a m b`, `W₁` a web on `S₁` with frame `a A b m⁻¹` and
`W₂` a web on `S₂` with frame `b B a m`, with `l` induced in both. Then `W₁ ⊔ W₂` is a web on `S`
with frame `C`: it is the web composition of `W₁` and `W₂` along `l` (Proposition 3.1). -/
theorem isWebOn_sup_of_pieces {S : Set V} {C : List V}
    {a b : V} {m A B : List V} {k : ℕ} {S₁ S₂ : Set V} {W₁ W₂ : SimpleGraph V}
    (hrot : C.rotate k = a :: A ++ b :: B) (hU : S₁ ∪ S₂ = S)
    (hI : S₁ ∩ S₂ = {v | v ∈ a :: m ++ [b]})
    (h₁ : IsWebOn W₁ S₁ (a :: A ++ b :: m.reverse)) (h₂ : IsWebOn W₂ S₂ (b :: B ++ a :: m))
    (hind₁ : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], W₁.Adj u v → IsListEdge (a :: m ++ [b]) u v)
    (hind₂ : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], W₂.Adj u v →
      IsListEdge (a :: m ++ [b]) u v) :
    IsWebOn (W₁ ⊔ W₂) S C := by
  set l := a :: m ++ [b] with hl
  have hs₁ := h₁.1
  have hs₂ := h₂.1
  have mem_l : ∀ {v}, v ∈ S₁ → v ∈ S₂ → v ∈ l := fun {v} h1 h2 => by
    have : v ∈ S₁ ∩ S₂ := ⟨h1, h2⟩
    rw [hI] at this
    exact this
  -- the edges of `l` are frame edges of both webs
  have hl₁ : ∀ u v, IsListEdge l u v → W₁.Adj u v := by
    intro u v huv
    have hC := h₁.isCycleList.rotate (A.length + 1)
    rw [rotate_cons_append_cons] at hC
    have e : b :: m.reverse ++ a :: A = (b :: m.reverse ++ [a]) ++ A := by simp
    rw [e] at hC
    refine hC.adj_of_isListEdge ?_
    have := huv.reverse
    simpa [hl] using this
  have hl₂ : ∀ u v, IsListEdge l u v → W₂.Adj u v := by
    intro u v huv
    have hC := h₂.isCycleList.rotate (B.length + 1)
    rw [rotate_cons_append_cons] at hC
    have e : a :: m ++ b :: B = l ++ B := by simp [hl]
    rw [e] at hC
    exact hC.adj_of_isListEdge huv
  have hr₁ : restrict (W₁ ⊔ W₂) S₁ = W₁ := by
    ext u v
    constructor
    · rintro ⟨huv | huv, hu, hv⟩
      · exact huv
      · exact hl₁ u v (hind₂ u (mem_l hu (hs₂ huv)) v (mem_l hv (hs₂ huv.symm)) huv)
    · intro huv
      exact ⟨Or.inl huv, hs₁ huv, hs₁ huv.symm⟩
  have hr₂ : restrict (W₁ ⊔ W₂) S₂ = W₂ := by
    ext u v
    constructor
    · rintro ⟨huv | huv, hu, hv⟩
      · exact hl₂ u v (hind₁ u (mem_l (hs₁ huv) hu) v (mem_l (hs₁ huv.symm) hv) huv)
      · exact huv
    · intro huv
      exact ⟨Or.inr huv, hs₂ huv, hs₂ huv.symm⟩
  have hsupp : IsSupportedOn (W₁ ⊔ W₂) S := by
    rintro u v (huv | huv)
    · exact hU ▸ Or.inl (hs₁ huv)
    · exact hU ▸ Or.inr (hs₂ huv)
  have hcomp : IsWebComposition (W₁ ⊔ W₂) S C l := by
    refine ⟨a, b, m, A, B, k, S₁, S₂, rfl, hrot, hsupp, hU, hI, ?_, ?_, ?_, ?_⟩
    · rintro u hu v hv (huv | huv)
      · exact Or.inr (hs₁ huv.symm)
      · exact Or.inl (hs₂ huv)
    · rintro u hu v hv (huv | huv)
      · exact hind₁ u hu v hv huv
      · exact hind₂ u hu v hv huv
    · rw [hr₁]; exact h₁
    · rw [hr₂]; exact h₂
  exact prop_3_1 hcomp

/-- **Two sides in two webs.** Let `G` be maximally `C`-crossless on `S`, where `C` is a rotation of
`a A b B`. Let `S` be covered by `S₁` and `S₂`, meeting in the path `l = a m b`, with every edge of
`G` inside `S₁` or inside `S₂`. Let `W₁` be a web on `S₁` with frame `a A b m⁻¹` and `W₂` a web on
`S₂` with frame `b B a m` in which `l` is induced, containing the subgraphs of `G` induced on `S₁` and
`S₂`. Then `G = W₁ ⊔ W₂`, and `G` is a web on `S` with frame `C`: the union is the web composition of
`W₁` and `W₂` along `l`, a web by Proposition 3.1, so `C` is crossless in it by Proposition 3.2, and
it contains `G`. -/
theorem IsMaxCrosslessOn.eq_sup_of_pieces {S : Set V} {C : List V} (h : IsMaxCrosslessOn G S C)
    {a b : V} {m A B : List V} {k : ℕ} {S₁ S₂ : Set V} {W₁ W₂ : SimpleGraph V}
    (hrot : C.rotate k = a :: A ++ b :: B) (hU : S₁ ∪ S₂ = S)
    (hI : S₁ ∩ S₂ = {v | v ∈ a :: m ++ [b]})
    (hG : ∀ u v, G.Adj u v → (u ∈ S₁ ∧ v ∈ S₁) ∨ (u ∈ S₂ ∧ v ∈ S₂))
    (h₁ : IsWebOn W₁ S₁ (a :: A ++ b :: m.reverse)) (h₂ : IsWebOn W₂ S₂ (b :: B ++ a :: m))
    (hle₁ : restrict G S₁ ≤ W₁) (hle₂ : restrict G S₂ ≤ W₂)
    (hind₁ : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], W₁.Adj u v → IsListEdge (a :: m ++ [b]) u v)
    (hind₂ : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], W₂.Adj u v →
      IsListEdge (a :: m ++ [b]) u v) :
    G = W₁ ⊔ W₂ ∧ IsWebOn G S C := by
  have hweb := isWebOn_sup_of_pieces hrot hU hI h₁ h₂ hind₁ hind₂
  have hsupp : IsSupportedOn (W₁ ⊔ W₂) S := hweb.1
  have hle : G ≤ W₁ ⊔ W₂ := by
    intro u v huv
    rcases hG u v huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inl (hle₁ ⟨huv, hu, hv⟩)
    · exact Or.inr (hle₂ ⟨huv, hu, hv⟩)
  have heq := h.eq_of_le hle hsupp hweb.not_isCrossed
  exact ⟨heq, heq ▸ hweb⟩

end GraphMinor.HP25
