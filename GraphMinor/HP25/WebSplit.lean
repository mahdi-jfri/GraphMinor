module

public import GraphMinor.HP25.Split
public import GraphMinor.HP25.WebPath
import GraphMinor.HP25.Prop23

/-!
# Web compositions, and splitting a web along an induced path

Humeau and Pous, arXiv:2505.16431v2, Section 3.3 (page 8): "Let $G$ and $H$ be two webs and let $P$
and $P'$ be subpaths of their respective frames of the same length. If $P$ and $P'$ are induced
paths in $G$ and $H$, respectively, we call *web composition* of $G$ and $H$ along $P$ and $P'$ the
path composition of $G$ and $H$ along $P$ and $P'$."

We work with graphs on a vertex set inside a fixed type `V`, so the two webs are the subgraphs of
`G` induced by two vertex sets `S₁` and `S₂` that meet exactly in the vertices of the path `P`
(`IsWebComposition`). Edge composition (Section 3.1) is the case where `P` is one edge.

The main result is `WebData.split`: a web splits into two webs along an induced path of its rib
between non-consecutive frame vertices with no inner vertex on the frame. The ribs come from
`PlaneEmbedding.IsRibEmbedding.split`; each clique vertex goes with the side that holds its
triangle. This is the last step of the proof of Proposition 3.6 (page 12): "Adding back the clique
vertices of $G$ on their respective triangles, the resulting pair of webs generate $G$ by taking
their web composition along $P$."
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-! ### Ribs only see their own edges -/

namespace PlaneEmbedding

variable {H : SimpleGraph V} {R : Set V}

/-- A plane embedding of `G` on `R` is one of every graph with the same edges inside `R`. -/
def congr (φ : PlaneEmbedding G R) (h : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v ↔ H.Adj u v) :
    PlaneEmbedding H R where
  pt := φ.pt
  line := φ.line
  finite := φ.finite
  injOn := φ.injOn
  line_comm := φ.line_comm
  isLine := fun u hu v hv huv => φ.isLine u hu v hv ((h u hu v hv).mpr huv)
  inter := fun u hu v hv u' hu' v' hv' h1 h2 hne =>
    φ.inter u hu v hv u' hu' v' hv' ((h u hu v hv).mpr h1) ((h u' hu' v' hv').mpr h2) hne
  avoid := fun u hu v hv huv w hw => φ.avoid u hu v hv ((h u hu v hv).mpr huv) w hw

theorem congr_U (φ : PlaneEmbedding G R) (h : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v ↔ H.Adj u v) :
    (φ.congr h).U = φ.U := by
  ext z
  simp only [U, mem_union, mem_iUnion]
  refine or_congr Iff.rfl ⟨fun ⟨u, hu, v, hv, huv, hz⟩ => ⟨u, hu, v, hv, (h u hu v hv).mpr huv, hz⟩,
    fun ⟨u, hu, v, hv, huv, hz⟩ => ⟨u, hu, v, hv, (h u hu v hv).mp huv, hz⟩⟩

end PlaneEmbedding

/-- A rib only depends on the edges inside its vertex set. -/
theorem IsRibOn.congr {H : SimpleGraph V} {R : Set V} {C : List V} (hG : IsRibOn G R C)
    (h : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v ↔ H.Adj u v) : IsRibOn H R C := by
  obtain ⟨hC, hCR, φ, hφ⟩ := hG
  have hT : ∀ a b c, IsTriangleOn G R a b c ↔ IsTriangleOn H R a b c := by
    intro a b c
    constructor
    · rintro ⟨ha, hb, hc, hab, hbc, hac⟩
      exact ⟨ha, hb, hc, (h a ha b hb).mp hab, (h b hb c hc).mp hbc, (h a ha c hc).mp hac⟩
    · rintro ⟨ha, hb, hc, hab, hbc, hac⟩
      exact ⟨ha, hb, hc, (h a ha b hb).mpr hab, (h b hb c hc).mpr hbc, (h a ha c hc).mpr hac⟩
  refine ⟨⟨hC.1, hC.2.1, fun p hp => ?_⟩, hCR, φ.congr h, ?_⟩
  · exact (h _ (hCR _ (List.of_mem_zip hp).1) _
      (hCR _ (List.mem_rotate.mp (List.of_mem_zip hp).2))).mp (hC.2.2 p hp)
  have hF : (φ.congr h).faces = φ.faces := by
    simp only [PlaneEmbedding.faces, PlaneEmbedding.congr_U]
  refine ⟨fun r hr hb => ?_, fun r hr hb => ?_, fun a b c habc => ?_⟩
  · rw [hF] at hr
    exact hφ.1 r hr hb
  · rw [hF] at hr
    obtain ⟨a, b, c, habc, hfr⟩ := hφ.2.1 r hr hb
    exact ⟨a, b, c, (hT a b c).mp habc, hfr⟩
  · obtain ⟨r, hr, hb, hfr⟩ := hφ.2.2 a b c ((hT a b c).mpr habc)
    exact ⟨r, hF ▸ hr, hb, hfr⟩

/-! ### An induced path holds no triangle -/

theorem IsListEdge.idxOf [DecidableEq V] {l : List V} {u v : V} (hnd : l.Nodup)
    (h : IsListEdge l u v) : l.idxOf u + 1 = l.idxOf v ∨ l.idxOf v + 1 = l.idxOf u := by
  obtain ⟨p, hp, he⟩ := h
  obtain ⟨i, hi, h1, h2⟩ := mem_zip_tail_iff.mp (show (p.1, p.2) ∈ l.zip l.tail from hp)
  have e1 : l.idxOf p.1 = i := by rw [← h1]; exact hnd.idxOf_getElem _ _
  have e2 : l.idxOf p.2 = i + 1 := by rw [← h2]; exact hnd.idxOf_getElem _ _
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (by rw [e1, e2])
  · exact Or.inr (by rw [e1, e2])

/-- Three pairwise adjacent vertices are never all on an induced path. -/
theorem not_triangle_of_induced {l : List V} (hnd : l.Nodup)
    (hind : ∀ u ∈ l, ∀ v ∈ l, G.Adj u v → IsListEdge l u v) {a b c : V} (ha : a ∈ l)
    (hb : b ∈ l) (hc : c ∈ l) (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) : False := by
  classical
  have h1 := (hind a ha b hb hab).idxOf hnd
  have h2 := (hind b hb c hc hbc).idxOf hnd
  have h3 := (hind a ha c hc hac).idxOf hnd
  omega

/-! ### Web compositions -/

/-- **Web composition** (Section 3.3, page 8): "Let $G$ and $H$ be two webs and let $P$ and $P'$ be
subpaths of their respective frames of the same length. If $P$ and $P'$ are induced paths in $G$
and $H$, respectively, we call *web composition* of $G$ and $H$ along $P$ and $P'$ the path
composition of $G$ and $H$ along $P$ and $P'$." Proposition 3.1 (page 8) gives the frame of the
result: "The web composition along $P$ and $P'$ of two webs $G$ and $H$ with respective frames
$P_GP$ and $P_HP'$, is a web with frame $P_G\overline{P_H}$."

Here `G` on the vertex set `S`, with frame `C`, is the web composition along the path `l = a m b`
of the webs induced on `S₁` and `S₂`: the two sets cover `S` and meet exactly in the vertices of `l`,
every edge of `G` lies inside `S₁` or inside `S₂`, `l` is an induced path of `G`, `C` is (up to
rotation) `a A b B`, and the two webs have frames `a A b m⁻¹` and `b B a m`. Edge composition
(Section 3.1, page 7) is the case `l = [a, b]`. -/
@[expose] def IsWebComposition (G : SimpleGraph V) (S : Set V) (C l : List V) : Prop :=
  ∃ (a b : V) (m A B : List V) (k : ℕ) (S₁ S₂ : Set V),
    l = a :: m ++ [b] ∧ C.rotate k = a :: A ++ b :: B ∧ IsSupportedOn G S ∧
    S₁ ∪ S₂ = S ∧ S₁ ∩ S₂ = {v | v ∈ l} ∧
    (∀ u ∈ S₁, ∀ v ∈ S₂, G.Adj u v → u ∈ S₂ ∨ v ∈ S₁) ∧
    (∀ u ∈ l, ∀ v ∈ l, G.Adj u v → IsListEdge l u v) ∧
    IsWebOn (restrict G S₁) S₁ (a :: A ++ b :: m.reverse) ∧
    IsWebOn (restrict G S₂) S₂ (b :: B ++ a :: m)

/-! ### Splitting a web -/

namespace WebData

variable {S : Set V} {C : List V} {R : Set V} {tri : V → Set V}

/-- One side of the split: the rib vertices of the side and the clique vertices whose triangle lies
in it form a web. -/
theorem side_web (W : WebData G S C R tri) {R₁ : Set V} {C₁ : List V} (hR₁ : R₁ ⊆ R)
    (hrib : IsRibOn G R₁ C₁) :
    IsWebOn (restrict G (R₁ ∪ {x | x ∈ S \ R ∧ tri x ⊆ R₁}))
      (R₁ ∪ {x | x ∈ S \ R ∧ tri x ⊆ R₁}) C₁ := by
  set S₁ := R₁ ∪ {x | x ∈ S \ R ∧ tri x ⊆ R₁} with hS₁
  have hclique : ∀ x ∈ S₁, x ∉ R₁ → x ∈ S \ R ∧ tri x ⊆ R₁ := by
    rintro x (hx | hx) hxR
    · exact absurd hx hxR
    · exact hx
  refine ⟨fun x y h => h.2.1, R₁, tri, subset_union_left,
    hrib.congr fun u hu v hv => ⟨fun h => ⟨h, Or.inl hu, Or.inl hv⟩, fun h => h.1⟩,
    fun x hx => ?_⟩
  obtain ⟨hxS, hxt⟩ := hclique x hx.1 hx.2
  refine ⟨?_, fun y => ?_⟩
  · obtain ⟨a, b, c, ⟨ha, hb, hc, hab, hbc, hac⟩, he⟩ := W.tri_spec x hxS
    have hm : ∀ v ∈ ({a, b, c} : Set V), v ∈ R₁ := fun v hv => hxt (he ▸ hv)
    refine ⟨a, b, c, ⟨hm a (by simp), hm b (by simp), hm c (by simp), ?_, ?_, ?_⟩, he⟩
    · exact ⟨hab, Or.inl (hm a (by simp)), Or.inl (hm b (by simp))⟩
    · exact ⟨hbc, Or.inl (hm b (by simp)), Or.inl (hm c (by simp))⟩
    · exact ⟨hac, Or.inl (hm a (by simp)), Or.inl (hm c (by simp))⟩
  constructor
  · rintro ⟨h, -, hy⟩
    rcases (W.adj_iff x hxS y).mp h with h | ⟨hyS, hyx, hyt⟩
    · exact Or.inl h
    · refine Or.inr ⟨⟨hy, fun hyR => hyS.2 (hR₁ hyR)⟩, hyx, hyt⟩
  · rintro (h | ⟨⟨hy, hyR⟩, hyx, hyt⟩)
    · exact ⟨(W.adj_iff x hxS y).mpr (Or.inl h), hx.1, Or.inl (hxt h)⟩
    · have hyS := (hclique y hy hyR).1
      exact ⟨(W.adj_iff x hxS y).mpr (Or.inr ⟨hyS, hyx, hyt⟩), hx.1, hy⟩

/-- **Splitting a web along an induced path of its rib.** Let `C` be, up to rotation, `a A b B`,
with `a`, `b` not consecutive on `C`, and let `a m b` be an induced path of the rib with no inner
vertex on `C`. Then the web is the web composition along `a m b` of two webs with frames `a A b m⁻¹`
and `b B a m`. -/
theorem split (W : WebData G S C R tri) {k : ℕ} {a b : V} {A B m : List V}
    (hrot : C.rotate k = a :: A ++ b :: B) (hab : ¬ PlaneEmbedding.IsCycleEdge C a b)
    (hl : IsPathList G R (a :: m ++ [b])) (hmC : ∀ v ∈ m, v ∉ C)
    (hind : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], G.Adj u v →
      IsListEdge (a :: m ++ [b]) u v) :
    IsWebComposition G S C (a :: m ++ [b]) := by
  obtain ⟨hC, hCR, φ, hφ⟩ := W.rib
  obtain ⟨R₁, R₂, hU, hI, hX, hrib₁, hrib₂⟩ := hφ.split hC hCR hrot hab hl hmC hind
  have hR₁ : R₁ ⊆ R := fun v hv => hU ▸ Or.inl hv
  have hR₂ : R₂ ⊆ R := fun v hv => hU ▸ Or.inr hv
  -- the vertices of a triangle of the rib lie on one side
  have htri : ∀ x ∈ S \ R, (tri x ⊆ R₁ ∨ tri x ⊆ R₂) ∧ ¬ (tri x ⊆ R₁ ∧ tri x ⊆ R₂) := by
    intro x hx
    obtain ⟨a', b', c', ⟨ha, hb, hc, hab', hbc', hac'⟩, he⟩ := W.tri_spec x hx
    have hside : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v → u ∈ R₁ → u ∉ R₂ → v ∈ R₁ := by
      intro u hu v hv huv hu1 hu2
      have hv' : v ∈ R₁ ∪ R₂ := hU ▸ hv
      rcases hv' with h | h
      · exact h
      · exact (hX u hu1 v h huv).resolve_left hu2
    have hside' : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v → u ∈ R₂ → u ∉ R₁ → v ∈ R₂ := by
      intro u hu v hv huv hu1 hu2
      have hv' : v ∈ R₁ ∪ R₂ := hU ▸ hv
      rcases hv' with h | h
      · exact ((hX v h u hu1 huv.symm).resolve_right hu2)
      · exact h
    have hboth : ¬ (a' ∈ R₁ ∩ R₂ ∧ b' ∈ R₁ ∩ R₂ ∧ c' ∈ R₁ ∩ R₂) := by
      rintro ⟨h1, h2, h3⟩
      rw [hI] at h1 h2 h3
      exact not_triangle_of_induced hl.1 hind h1 h2 h3 hab' hbc' hac'
    rw [he]
    refine ⟨?_, fun ⟨h1, h2⟩ => hboth ⟨⟨h1 (by simp), h2 (by simp)⟩, ⟨h1 (by simp), h2 (by simp)⟩,
      ⟨h1 (by simp), h2 (by simp)⟩⟩⟩
    have hm : ∀ v ∈ R, v ∈ R₁ ∨ v ∈ R₂ := fun v hv => by rw [← hU] at hv; exact hv
    by_cases h1 : a' ∈ R₁ ∧ a' ∉ R₂
    · left
      rintro v (rfl | rfl | rfl)
      · exact h1.1
      · exact hside a' ha v hb hab' h1.1 h1.2
      · exact hside a' ha v hc hac' h1.1 h1.2
    by_cases h2 : a' ∈ R₂ ∧ a' ∉ R₁
    · right
      rintro v (rfl | rfl | rfl)
      · exact h2.1
      · exact hside' a' ha v hb hab' h2.1 h2.2
      · exact hside' a' ha v hc hac' h2.1 h2.2
    have ha12 : a' ∈ R₁ ∧ a' ∈ R₂ := by
      rcases hm a' ha with h | h
      · exact ⟨h, by by_contra h'; exact h1 ⟨h, h'⟩⟩
      · exact ⟨by by_contra h'; exact h2 ⟨h, h'⟩, h⟩
    by_cases h3 : b' ∈ R₁ ∧ b' ∉ R₂
    · left
      rintro v (rfl | rfl | rfl)
      · exact ha12.1
      · exact h3.1
      · exact hside b' hb v hc hbc' h3.1 h3.2
    by_cases h4 : b' ∈ R₂ ∧ b' ∉ R₁
    · right
      rintro v (rfl | rfl | rfl)
      · exact ha12.2
      · exact h4.1
      · exact hside' b' hb v hc hbc' h4.1 h4.2
    have hb12 : b' ∈ R₁ ∧ b' ∈ R₂ := by
      rcases hm b' hb with h | h
      · exact ⟨h, by by_contra h'; exact h3 ⟨h, h'⟩⟩
      · exact ⟨by by_contra h'; exact h4 ⟨h, h'⟩, h⟩
    rcases hm c' hc with h | h
    · left
      rintro v (rfl | rfl | rfl)
      · exact ha12.1
      · exact hb12.1
      · exact h
    · right
      rintro v (rfl | rfl | rfl)
      · exact ha12.2
      · exact hb12.2
      · exact h
  refine ⟨a, b, m, A, B, k, R₁ ∪ {x | x ∈ S \ R ∧ tri x ⊆ R₁},
    R₂ ∪ {x | x ∈ S \ R ∧ tri x ⊆ R₂}, rfl, hrot, W.supp, ?_, ?_, ?_, hind,
    W.side_web hR₁ hrib₁, W.side_web hR₂ hrib₂⟩
  · ext v
    constructor
    · rintro ((h | h) | (h | h))
      · exact W.sub (hR₁ h)
      · exact h.1.1
      · exact W.sub (hR₂ h)
      · exact h.1.1
    · intro hv
      by_cases hvR : v ∈ R
      · rcases (show v ∈ R₁ ∪ R₂ from hU ▸ hvR) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · rcases (htri v ⟨hv, hvR⟩).1 with h | h
        · exact Or.inl (Or.inr ⟨⟨hv, hvR⟩, h⟩)
        · exact Or.inr (Or.inr ⟨⟨hv, hvR⟩, h⟩)
  · rw [← hI]
    ext v
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact ⟨h1, h2⟩
      · exact absurd (hR₁ h1) h2.1.2
      · exact absurd (hR₂ h2) h1.1.2
      · exact absurd ⟨h1.2, h2.2⟩ (htri v h1.1).2
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inl h1, Or.inl h2⟩
  · -- no edge between the two sides, apart from the path
    rintro u (hu | ⟨huS, hut⟩) v (hv | ⟨hvS, hvt⟩) huv
    · rcases hX u hu v hv huv with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · -- `u` is a rib vertex adjacent to the clique vertex `v`, so `u` is on the triangle of `v`
      rcases (W.adj_iff v hvS u).mp huv.symm with h | ⟨h, -⟩
      · exact Or.inl (Or.inl (hvt h))
      · exact absurd (hR₁ hu) h.2
    · rcases (W.adj_iff u huS v).mp huv with h | ⟨h, -⟩
      · exact Or.inr (Or.inl (hut h))
      · exact absurd (hR₂ hv) h.2
    · rcases (W.adj_iff u huS v).mp huv with h | ⟨h, -, he⟩
      · exact absurd (W.tri_subset huS h) hvS.2
      · exact Or.inr (Or.inr ⟨hvS, he ▸ hut⟩)

end WebData

end GraphMinor.HP25
