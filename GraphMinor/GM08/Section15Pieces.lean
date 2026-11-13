module

public import GraphMinor.GM08.Section15Strong

/-!
# Graph Minors VIII, printed (15.1): pieces drawn in a disc

The trains of the proof of the printed (15.1) in `Section15PrintedFinal.lean` use pieces of the
following kind: a part of the graph drawn in a closed disc of a
sphere, meeting the boundary of the disc in at most two vertices (its attachments), together with
some padding vertices that are isolated in the piece. Fact E
(`le_tubularPrintedWidth_of_disc`) frames such a piece with printed width more than its index.

This file restates Fact E for a piece cut out of a graft that is drawn in the sphere
(`le_tubularPrintedWidth_of_piece`). The drawing of the piece is the part of the drawing of the
graft spanned by its vertices and edges.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-- In an infinite set `C`, with a finite set `F` and a part `P ⊆ F ∩ C` of at most two points,
there are two distinct points of `C` whose common points with `F` are exactly `P`. -/
theorem exists_pair_of_infinite {Z : Type*} {C F P : Set Z} (hC : C.Infinite) (hF : F.Finite)
    (hPF : P ⊆ F) (hPC : P ⊆ C) (hP : P.ncard ≤ 2) :
    ∃ p ∈ C, ∃ q ∈ C, p ≠ q ∧ ∀ x ∈ F, x ∈ ({p, q} : Set Z) ↔ x ∈ P := by
  have hfin : P.Finite := hF.subset hPF
  have hinf : (C \ F).Infinite := hC.sdiff hF
  rcases Nat.lt_or_ge P.ncard 1 with h0 | h1
  · have hPe : P = ∅ := (ncard_eq_zero hfin).mp (by omega)
    obtain ⟨p, hp⟩ := hinf.nonempty
    obtain ⟨q, ⟨hq, hqp⟩⟩ := (hinf.diff (finite_singleton p)).nonempty
    refine ⟨p, hp.1, q, hq.1, fun h => hqp (h ▸ rfl), fun x hx => ?_⟩
    rw [hPe]
    simp only [mem_insert_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
    rintro (rfl | rfl)
    exacts [hp.2 hx, hq.2 hx]
  rcases Nat.lt_or_ge P.ncard 2 with h1' | h2
  · obtain ⟨a, rfl⟩ := ncard_eq_one.mp (show P.ncard = 1 by omega)
    obtain ⟨q, hq⟩ := hinf.nonempty
    have haF : a ∈ F := hPF rfl
    refine ⟨a, hPC rfl, q, hq.1, fun h => hq.2 (h ▸ haF), fun x hx => ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (h | rfl)
      · exact h
      · exact absurd hx hq.2
    · exact Or.inl
  · obtain ⟨a, b, hab, rfl⟩ := ncard_eq_two.mp (show P.ncard = 2 by omega)
    exact ⟨a, hPC (.inl rfl), b, hPC (.inr rfl), hab, fun x _ => Iff.rfl⟩

/-- The boundary of a closed disc is infinite. -/
theorem IsClosedDisc.infinite_discBd {Z : Type*} [TopologicalSpace Z] [T2Space Z] {B : Set Z}
    (hB : IsClosedDisc B) : (discBd B).Infinite := by
  have hO := hB.isOArc_discBd
  obtain ⟨p, q, -, hp, hq, -, hpq, -⟩ := hO.exists_three
  exact hO.isPreconnected.infinite_of_nontrivial ⟨p, hp, q, hq, hpq⟩

/-- **Fact E for a piece of a drawn graft.** Let the graph of `X` be drawn in a sphere by `Γ`,
through the bijection `φ`, `ψ`. Take vertices `Vp` and edges `Ep` of `X`, with the ends of the
edges in `Vp`, drawn in a closed disc `B`. Suppose the edges miss the boundary of `B`, and the
vertices on the boundary form a set `att` of at most two vertices. Add a set `W` of padding
vertices of `X` outside `Vp`. Then the graft with graph `Vp ∪ W` and edges `Ep`, and with roots
`W ∪ att`, is tubular of printed width at least its index plus one.

The drawing of the piece is the part of `Γ` spanned by the images of `Vp` and `Ep`. The two
points of `le_tubularPrintedWidth_of_disc` are the images of `att`, completed by points of the
boundary that are not images of vertices (`exists_pair_of_infinite`). -/
theorem le_tubularPrintedWidth_of_piece {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ConnectedSpace Z] (hZ : IsClosedSurface Z) (hsph : IsSphere Z) {X : Graft α β}
    {Γ : Drawing Z} {φ : α → Z} {ψ : β → Set Z} (hb : IsGraphBij X.G Γ.toGraph φ ψ)
    {B : Set Z} (hB : IsClosedDisc B) {Vp att W : Set α} {Ep : Set β}
    (hVp : Vp ⊆ V(X.G)) (hEp : Ep ⊆ E(X.G))
    (hends : ∀ e ∈ Ep, ∀ x y, X.G.IsLink e x y → x ∈ Vp)
    (hattV : att ⊆ Vp) (hatt2 : att.ncard ≤ 2)
    (hVB : ∀ x ∈ Vp, φ x ∈ B) (hEB : ∀ e ∈ Ep, closure (ψ e) ⊆ B)
    (hVbd : ∀ x ∈ Vp, φ x ∈ discBd B → x ∈ att) (hattbd : ∀ x ∈ att, φ x ∈ discBd B)
    (hEbd : ∀ e ∈ Ep, Disjoint (ψ e) (discBd B))
    (hWV : W ⊆ V(X.G)) (hWp : Disjoint W Vp)
    (Y : Graft α β) (hYG : Y.G = subOf X.G (Vp ∪ W) Ep) (hYT : Y.T = W ∪ att) :
    IsTubularGraft Y ∧ ((Y.T.ncard + 1 : ℕ) : ℕ∞) ≤ tubularPrintedWidth Y := by
  classical
  -- the two points on the boundary
  have hFfin : (φ '' V(X.G)).Finite := X.finite_G.1.image φ
  obtain ⟨p, hp, q, hq, hpq, hpqF⟩ := exists_pair_of_infinite (IsClosedDisc.infinite_discBd hB) hFfin
    (P := φ '' att) (image_mono (hattV.trans hVp))
    (by rintro _ ⟨x, hx, rfl⟩; exact hattbd x hx)
    ((ncard_image_le (X.finite_G.1.subset (hattV.trans hVp))).trans hatt2)
  have hpq' : ∀ x ∈ V(X.G), φ x ∈ ({p, q} : Set Z) ↔ x ∈ att := by
    intro x hx
    rw [hpqF _ (mem_image_of_mem φ hx)]
    exact hb.bijV.injOn.mem_image_iff (hattV.trans hVp) hx
  -- the drawing of the piece
  set Γ₀ := Γ.span (φ '' Vp) (ψ '' Ep) with hΓ₀
  have hψE : ∀ e ∈ Ep, ψ e ∈ Γ.E := fun e he => hb.bijE.mapsTo (hEp he)
  have hφV : ∀ x ∈ Vp, φ x ∈ Γ.V := fun x hx => hb.bijV.mapsTo (hVp hx)
  have hends' : ∀ e ∈ Ep, closure (ψ e) ∩ Γ.V ⊆ φ '' Vp := by
    intro e he z hz
    obtain ⟨x, y, hxy⟩ : ∃ x y, X.G.IsLink e x y := exists_isLink_of_mem_edgeSet (hEp he)
    have hl := (hb.isLink e (hEp he) x hxy.left_mem y hxy.right_mem).mp hxy
    have hz' : z ∈ ({φ x, φ y} : Set Z) := hl.2.2.2 ▸ hz
    rcases hz' with rfl | rfl
    · exact mem_image_of_mem φ (hends e he x y hxy)
    · exact mem_image_of_mem φ (hends e he y x hxy.symm)
  have hV₀ : Γ₀.V = φ '' Vp := by
    rw [Drawing.span_V]
    apply Subset.antisymm
    · refine union_subset inter_subset_left (iUnion₂_subset fun e' he' => ?_)
      obtain ⟨⟨e, he, rfl⟩, -⟩ := he'
      exact hends' e he
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact Or.inl ⟨mem_image_of_mem φ hx, hφV x hx⟩
  have hE₀ : Γ₀.E = ψ '' Ep := by
    rw [Drawing.span_E]
    exact inter_eq_left.mpr (by rintro _ ⟨e, he, rfl⟩; exact hψE e he)
  have hU₀ : ∀ z ∈ Γ₀.U, z ∈ φ '' Vp ∨ ∃ e ∈ Ep, z ∈ closure (ψ e) := by
    intro z hz
    rw [Drawing.span_U] at hz
    rcases hz with hz | hz
    · exact Or.inl (hV₀ ▸ hz)
    · obtain ⟨e', ⟨⟨e, he, rfl⟩, -⟩, hz⟩ := mem_iUnion₂.mp hz
      exact Or.inr ⟨e, he, hz⟩
  have hU : Γ₀.U ⊆ B := by
    intro z hz
    rcases hU₀ z hz with ⟨x, hx, rfl⟩ | ⟨e, he, hz⟩
    · exact hVB x hx
    · exact hEB e he hz
  have hbd : Γ₀.U ∩ discBd B ⊆ Γ₀.V := by
    rintro z ⟨hz, hzb⟩
    rcases hU₀ z hz with hz' | ⟨e, he, hz'⟩
    · exact hV₀ ▸ hz'
    · have hzV : z ∈ Γ.V := by
        by_contra hzV
        have : z ∈ closure (ψ e) \ Γ.V := ⟨hz', hzV⟩
        rw [Γ.closure_diff_V (hψE e he)] at this
        exact disjoint_left.mp (hEbd e he) this hzb
      exact hV₀ ▸ hends' e he ⟨hz', hzV⟩
  have hVbd' : Γ₀.V ∩ discBd B ⊆ {p, q} := by
    rintro z ⟨hz, hzb⟩
    rw [hV₀] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (hpq' x (hVp hx)).mpr (hVbd x hx hzb)
  -- the bijection for the piece without its padding
  have hVW : Vp ∪ W ⊆ V(X.G) := union_subset hVp hWV
  have hle1 : Y.G.deleteVerts W ≤ X.G := by
    rw [hYG]
    exact deleteVerts_le.trans (subOf_le X.G hVW Ep)
  have hle2 : Γ₀.toGraph ≤ Γ.toGraph := by
    have hs := Drawing.span_isSubdrawing Γ (φ '' Vp) (ψ '' Ep)
    exact { vertexSet_mono := hs.1, isLink_mono := fun _ _ _ hl => (hs.isLink_iff hl.1).1 hl }
  have hbij : IsGraphBij (Y.G.deleteVerts W) Γ₀.toGraph φ ψ := by
    refine hb.restrict hle1 hle2 (fun x hx => ?_) (fun e he => ?_)
    · rw [vertexSet_deleteVerts, hYG, subOf_vertexSet]
      change x ∈ (Vp ∪ W) \ W ↔ φ x ∈ Γ₀.V
      rw [hV₀, hb.bijV.injOn.mem_image_iff hVp hx]
      constructor
      · rintro ⟨h | h, hW⟩
        exacts [h, absurd h hW]
      · exact fun h => ⟨.inl h, fun hW => disjoint_left.mp hWp hW h⟩
    · change e ∈ E(Y.G.deleteVerts W) ↔ ψ e ∈ Γ₀.E
      rw [hE₀, hb.bijE.injOn.mem_image_iff hEp he, edgeSet_deleteVerts]
      constructor
      · rintro ⟨x, y, hxy, -, -⟩
        rw [hYG, subOf_isLink] at hxy
        exact hxy.1
      · intro he'
        obtain ⟨x, y, hxy⟩ : ∃ x y, X.G.IsLink e x y := exists_isLink_of_mem_edgeSet he
        have hx := hends e he' x y hxy
        have hy := hends e he' y x hxy.symm
        refine ⟨x, y, ?_, fun hW => disjoint_left.mp hWp hW hx,
          fun hW => disjoint_left.mp hWp hW hy⟩
        rw [hYG, subOf_isLink]
        exact ⟨he', hxy, .inl hx, .inl hy⟩
  have hWY : W ⊆ V(Y.G) := by
    rw [hYG, subOf_vertexSet]
    exact subset_union_right
  have hWiso : ∀ e x y, Y.G.IsLink e x y → x ∉ W := by
    intro e x y h hW
    rw [hYG, subOf_isLink] at h
    exact disjoint_left.mp hWp hW (hends e h.1 x y h.2.1)
  have hT : ∀ v ∈ V(Y.G), v ∈ Y.T ↔ v ∈ W ∨ φ v ∈ ({p, q} : Set Z) := by
    intro v hv
    have hvX : v ∈ V(X.G) := by
      rw [hYG, subOf_vertexSet] at hv
      exact hVW hv
    rw [hYT, mem_union, hpq' v hvX]
  exact le_tubularPrintedWidth_of_disc hZ hsph hB hp hq hpq Y hWY hWiso Γ₀ hU hbd hVbd' hbij hT

end GraphMinor.GM08
