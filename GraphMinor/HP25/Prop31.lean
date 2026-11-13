module

public import GraphMinor.HP25.WebSplit
import GraphMinor.HP25.Glue
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.SurfaceGraph

/-!
# Proposition 3.1: web composition

Humeau and Pous, arXiv:2505.16431v2, page 8. "**Proposition 3.1.** The web composition along $P$
and $P'$ of two webs $G$ and $H$ with respective frames $P_GP$ and $P_HP'$, is a web with frame
$P_G\overline{P_H}$."

The paper's proof: "Let $R_G$ and $R_H$ be the ribs of $G$ and $H$, respectively, and $R$ the web
composition of $R_G$ and $R_H$ along $P$ and $P'$. We prove that $R$ is a rib." It then draws the
two ribs with outer faces on two polygons that meet exactly in the path, takes the union of the
drawings, and reads off the faces. "Adding back the clique vertices of $G$ and $H$ on their
respective triangles gives a web".

We follow it. The two ribs are glued in `isRibOn_glue`. We differ from the paper here: instead of
the cited fact that "Any planar graph admits a plane embedding for which the outer face is sent
exactly onto a given prescribed polygon of the plane (see [11])", we move each drawing by a
homeomorphism of closed discs (Schoenflies, `exists_sideMatch`) onto one half of the closed unit
disc cut by a diameter. The path is sent onto the diameter, line by line in the same way for both
drawings (`exists_pathMatch`). The union and its faces are in `HP25/Glue.lean`. The clique vertices
are added back in `prop_3_1`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface Metric

local notation "𝕀" => unitInterval

variable {V : Type*} {G : SimpleGraph V}

namespace PlaneEmbedding

variable {R : Set V} (φ : PlaneEmbedding G R)

/-- A cycle `x X y Y` splits into the paths `x X y` and `y Y x`, whose images meet only at the
points of `x` and `y`. -/
theorem two_paths_inter {x y : V} {X Y : List V} (hC : IsCycleList G (x :: X ++ y :: Y))
    (hR : ∀ v ∈ x :: X ++ y :: Y, v ∈ R) :
    IsPathList G R (x :: X ++ [y]) ∧ IsPathList G R (y :: Y ++ [x]) ∧
      φ.pathImage (x :: X ++ [y]) ∩ φ.pathImage (y :: Y ++ [x]) = {φ.pt x, φ.pt y} := by
  have hne : x :: X ++ y :: Y ≠ [] := by simp
  obtain ⟨h1, h2, -, h4⟩ := φ.cycleImage_split hC hR hne (k := X.length + 1) (by omega) (by simp)
  have e1 : (x :: X ++ y :: Y ++ [x]).take (X.length + 1 + 1) = x :: X ++ [y] := by
    simp [List.take_append]
  have e2 : (x :: X ++ y :: Y ++ [x]).drop (X.length + 1) = y :: Y ++ [x] := by simp
  have e3 : (x :: X ++ y :: Y)[X.length + 1]'(by simp) = y := by simp [List.getElem_append_right]
  have e4 : (x :: X ++ y :: Y).head hne = x := by simp
  simp only [e4] at h1 h2 h4
  simp only [e1, e2, e3] at h1 h2 h4
  exact ⟨h1, h2, h4⟩

end PlaneEmbedding

theorem IsPathList.mono {R R' : Set V} {l : List V} (h : IsPathList G R l) (hR : R ⊆ R') :
    IsPathList G R' l :=
  ⟨h.1, h.2.1, fun x hx => hR (h.2.2 x hx)⟩

/-- A rib with a rotated frame. -/
theorem IsRibOn.of_rotate {R : Set V} {C : List V} {k : ℕ} (h : IsRibOn G R (C.rotate k)) :
    IsRibOn G R C := by
  obtain ⟨hC, hCR, φ, h1, h2, h3⟩ := h
  refine ⟨⟨by simpa using hC.1, List.nodup_rotate.mp hC.2.1, fun p hp => hC.2.2 p ?_⟩,
    fun x hx => hCR x (List.mem_rotate.mpr hx), φ, fun r hr hb => ?_, h2, h3⟩
  · rw [zip_rotate_rotate, List.mem_rotate]
    exact hp
  · rw [h1 r hr hb, φ.cycleImage_rotate]

/-- **Gluing two ribs** (the rib part of the proof of Proposition 3.1). Let `G` on `R₁` be a rib with
frame `a A b m⁻¹` and `G` on `R₂` a rib with frame `b B a m`, where `R₁ ∩ R₂` is the path
`P = a m b`, `P` is induced, and every edge of `G` on `R₁ ∪ R₂` lies in `R₁` or in `R₂`. Then `G` on
`R₁ ∪ R₂` is a rib with frame `a A b B`. -/
theorem isRibOn_glue {R₁ R₂ : Set V} {a b : V} {A B m : List V}
    (h₁ : IsRibOn G R₁ (a :: A ++ b :: m.reverse)) (h₂ : IsRibOn G R₂ (b :: B ++ a :: m))
    (hinter : R₁ ∩ R₂ = {v | v ∈ a :: m ++ [b]})
    (hind : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], G.Adj u v → IsListEdge (a :: m ++ [b]) u v)
    (hedge : ∀ u ∈ R₁ ∪ R₂, ∀ v ∈ R₁ ∪ R₂, G.Adj u v →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂)) :
    IsRibOn G (R₁ ∪ R₂) (a :: A ++ b :: B) := by
  classical
  obtain ⟨hC₁, hC₁R, φ₁, hφ₁⟩ := h₁
  obtain ⟨hC₂, hC₂R, φ₂, hφ₂⟩ := h₂
  -- the two halves of each frame
  obtain ⟨hA₁, hl₁', hi₁⟩ := φ₁.two_paths_inter hC₁ hC₁R
  obtain ⟨hB₂, hl₂, hi₂⟩ := φ₂.two_paths_inter hC₂ hC₂R
  have hrev : (b :: m.reverse ++ [a]).reverse = a :: m ++ [b] := by simp
  have hl₁ : IsPathList G R₁ (a :: m ++ [b]) := hrev ▸ hl₁'.reverse
  have hP₁ : φ₁.pathImage (b :: m.reverse ++ [a]) = φ₁.pathImage (a :: m ++ [b]) := by
    rw [← φ₁.pathImage_reverse, hrev]
  -- `A` is not empty: otherwise `ab` is an edge, so `P = ab` and the frame `a b` is too short
  have hA : A ≠ [] := by
    rintro rfl
    have hab : G.Adj a b := by simpa using hA₁.2.1
    have he := (hind a (by simp) b (by simp) hab).idxOf hl₁.1
    have i1 : (a :: m ++ [b]).idxOf a = 0 := by simp
    have i2 : (a :: m ++ [b]).idxOf b = m.length + 1 := by
      have := hl₁.1.idxOf_getElem (m.length + 1) (by simp)
      simpa using this
    rw [i1, i2] at he
    have hm : m = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hm
    have := hC₁.1
    simp at this
  -- the vertices of `A` are not on `P`, so not in `R₂`
  have hAl : ∀ v ∈ A, v ∉ a :: m ++ [b] := by
    intro v hv hvl
    have hnd := hC₁.2.1
    rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff,
      or_false] at hvl
    rcases hvl with rfl | hvm | rfl
    · exact hnd.1 (List.mem_append_left _ hv)
    · exact hnd.2.2.2 v hv v (by simp [hvm]) rfl
    · exact hnd.2.2.2 v hv v (by simp) rfl
  have hdisj : ∀ v ∈ A, v ∉ B := by
    intro v hv hvB
    have : v ∈ R₁ ∩ R₂ := ⟨hC₁R v (by simp [hv]), hC₂R v (by simp [hvB])⟩
    rw [hinter] at this
    exact hAl v hv this
  have hab : a ≠ b := by
    have hnd := hl₁.1
    rw [List.cons_append, List.nodup_cons] at hnd
    exact fun h => hnd.1 (by simp [h])
  have hCyc : IsCycleList G (a :: A ++ b :: B) :=
    isCycleList_of_two_paths (hA₁.mono subset_union_left) (hB₂.mono subset_union_right) hdisj hab
      (Or.inl hA)
  -- arcs on the frame images
  obtain ⟨c₁, hc₁, hrc₁, hc₁0, hc₁1⟩ := (by
    have := φ₁.isLine_pathImage (x := a) (l := A ++ [b]) (by simp) (by simpa using hA₁)
    rw [List.getLast_append_singleton] at this
    exact this.exists_arc :
    ∃ c : 𝕀 → ℂ, IsArcMap c ∧ range c = φ₁.pathImage (a :: A ++ [b]) ∧ c 0 = φ₁.pt a ∧
      c 1 = φ₁.pt b)
  obtain ⟨d₁, hd₁, hrd₁, hd₁0, hd₁1⟩ := (by
    have := φ₁.isLine_pathImage (x := a) (l := m ++ [b]) (by simp) (by simpa using hl₁)
    rw [List.getLast_append_singleton] at this
    exact this.exists_arc :
    ∃ d : 𝕀 → ℂ, IsArcMap d ∧ range d = φ₁.pathImage (a :: m ++ [b]) ∧ d 0 = φ₁.pt a ∧
      d 1 = φ₁.pt b)
  obtain ⟨c₂, hc₂, hrc₂, hc₂0, hc₂1⟩ := (by
    have := φ₂.isLine_pathImage (x := b) (l := B ++ [a]) (by simp) (by simpa using hB₂)
    rw [List.getLast_append_singleton] at this
    exact this.symm.exists_arc :
    ∃ c : 𝕀 → ℂ, IsArcMap c ∧ range c = φ₂.pathImage (b :: B ++ [a]) ∧ c 0 = φ₂.pt a ∧
      c 1 = φ₂.pt b)
  -- the path drawn by `φ₁` matched with the path drawn by `φ₂`
  obtain ⟨κ, hκc, hκi, hκim, hκpt, hκl⟩ :=
    PlaneEmbedding.exists_pathMatch φ₁ φ₂ a (m ++ [b]) (by simpa using hl₁) (by simpa using hl₂)
  have hmem₁ : ∀ t, d₁ t ∈ φ₁.pathImage (a :: m ++ [b]) := fun t => hrd₁ ▸ mem_range_self t
  have hd₂ : IsArcMap (κ ∘ d₁) :=
    ⟨hκc.comp_continuous hd₁.1 hmem₁, fun s t h => hd₁.2 (hκi (hmem₁ s) (hmem₁ t) h)⟩
  have hrd₂ : range (κ ∘ d₁) = φ₂.pathImage (a :: m ++ [b]) := by
    rw [range_comp, hrd₁]
    exact hκim
  have hd₂0 : (κ ∘ d₁) 0 = φ₂.pt a := by
    simp only [Function.comp_apply, hd₁0]
    exact hκpt a (by simp)
  have hd₂1 : (κ ∘ d₁) 1 = φ₂.pt b := by
    simp only [Function.comp_apply, hd₁1]
    exact hκpt b (by simp)
  -- the arcs meet only at their ends
  have hm₁ : ∀ s t, c₁ s = d₁ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t h
    have hz : c₁ s ∈ ({φ₁.pt a, φ₁.pt b} : Set ℂ) := by
      rw [← hi₁, hP₁]
      exact ⟨hrc₁ ▸ mem_range_self s, h ▸ hrd₁ ▸ mem_range_self t⟩
    rcases hz with hz | hz
    · exact Or.inl ⟨hc₁.2 (hz.trans hc₁0.symm), hd₁.2 ((h.symm.trans hz).trans hd₁0.symm)⟩
    · exact Or.inr ⟨hc₁.2 (hz.trans hc₁1.symm), hd₁.2 ((h.symm.trans hz).trans hd₁1.symm)⟩
  have hm₂ : ∀ s t, c₂ s = (κ ∘ d₁) t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t h
    have hz : c₂ s ∈ ({φ₂.pt b, φ₂.pt a} : Set ℂ) := by
      rw [← hi₂]
      exact ⟨hrc₂ ▸ mem_range_self s, h ▸ hrd₂ ▸ mem_range_self t⟩
    rcases hz with hz | hz
    · exact Or.inr ⟨hc₂.2 (hz.trans hc₂1.symm), hd₂.2 ((h.symm.trans hz).trans hd₂1.symm)⟩
    · exact Or.inl ⟨hc₂.2 (hz.trans hc₂0.symm), hd₂.2 ((h.symm.trans hz).trans hd₂0.symm)⟩
  -- the two halves of the unit disc
  obtain ⟨a₁, a₂, cut⟩ := exists_cut_unit
  obtain ⟨ψ₁, χ₁, m₁, hψc₁, hψd₁⟩ := exists_sideMatch hc₁ hd₁ cut.arc_a cut.arc_e
    (by rw [hd₁0, hc₁0]) (by rw [hd₁1, hc₁1]) cut.a_zero.symm cut.a_one.symm hm₁ cut.a_eq_e
  obtain ⟨ψ₂, χ₂, m₂, hψc₂, hψd₂⟩ := exists_sideMatch hc₂ hd₂ cut.arc_b cut.arc_e
    (by rw [hd₂0, hc₂0]) (by rw [hd₂1, hc₂1]) cut.b_zero.symm cut.b_one.symm hm₂ cut.symm.a_eq_e
  have hF₁ : φ₁.cycleImage (a :: A ++ b :: m.reverse) = range c₁ ∪ range d₁ := by
    rw [φ₁.cycleImage_two_paths, hP₁, hrc₁, hrd₁]
  have hF₂ : φ₂.cycleImage (b :: B ++ a :: m) = range c₂ ∪ range (κ ∘ d₁) := by
    rw [φ₂.cycleImage_two_paths, hrc₂, hrd₂]
  have himg : ∀ {ψ : ℂ → ℂ} {c c' : 𝕀 → ℂ}, (∀ s, ψ (c s) = c' s) → ψ '' range c = range c' := by
    intro ψ c c' h
    rw [← range_comp]
    exact congrArg range (funext h)
  -- the two maps agree on the path
  have hEq : ∀ z ∈ φ₁.pathImage (a :: m ++ [b]), ψ₁ z = ψ₂ (κ z) := by
    intro z hz
    rw [← hrd₁] at hz
    obtain ⟨t, rfl⟩ := hz
    rw [hψd₁]
    exact (hψd₂ t).symm
  have g : Glue φ₁ φ₂ (a :: A ++ b :: m.reverse) (b :: B ++ a :: m) (a :: m ++ [b]) a₁ a₂
      unitDiameter ψ₁ χ₁ ψ₂ χ₂ := {
    rib₁ := hφ₁
    rib₂ := hφ₂
    cyc₁ := hC₁
    cyc₂ := hC₂
    sub₁ := hC₁R
    sub₂ := hC₂R
    inter := hinter
    path₁ := hl₁
    path₂ := hl₂
    ind := hind
    edge := hedge
    cut := cut
    m₁ := by rw [hF₁]; exact m₁
    m₂ := by rw [hF₂]; exact m₂
    bd₁ := by rw [hF₁, image_union, himg hψc₁, himg hψd₁]; rfl
    bd₂ := by rw [hF₂, image_union, himg hψc₂, himg hψd₂]; rfl
    pe₁ := by rw [← hrd₁, himg hψd₁]
    pe₂ := by rw [← hrd₂, himg hψd₂]
    agree_pt := fun x hx => by
      rw [hEq _ (φ₁.pt_mem_pathImage hl₁ (by simp) hx)]
      exact congrArg ψ₂ (hκpt x hx)
    agree_line := fun u v huv => by
      obtain ⟨p, hp, he⟩ := huv
      have hline : ∀ {R' : Set V} (φ : PlaneEmbedding G R'), φ.line u v = φ.line p.1 p.2 := by
        intro R' φ
        rcases Sym2.eq_iff.mp he with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]
        · rw [e1, e2, φ.line_comm]
      have hsub : φ₁.line p.1 p.2 ⊆ φ₁.pathImage (a :: m ++ [b]) :=
        φ₁.line_subset_pathImage ⟨p, hp, rfl⟩
      rw [hline φ₁, hline φ₂, image_congr (fun z hz => hEq z (hsub hz)), ← image_image ψ₂ κ,
        hκl p hp] }
  have hframe : g.emb.cycleImage (a :: A ++ b :: B) = sphere (0 : ℂ) 1 := by
    rw [PlaneEmbedding.cycleImage_two_paths, g.pathImage_eq₁ (fun x hx => hA₁.2.2 x hx),
      g.pathImage_eq₂ hB₂, ← hrc₁, ← hrc₂, himg hψc₁, himg hψc₂, cut.union]
  refine ⟨hCyc, fun x hx => ?_, g.emb, g.isRibEmbedding hframe⟩
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hx | rfl | hx
  · exact Or.inl (hC₁R _ (by simp))
  · exact Or.inl (hC₁R x (by simp [hx]))
  · exact Or.inl (hC₁R _ (by simp))
  · exact Or.inr (hC₂R x (by simp [hx]))

/-- **Proposition 3.1** (Humeau and Pous, page 8). "The web composition along $P$ and $P'$ of two
webs $G$ and $H$ with respective frames $P_GP$ and $P_HP'$, is a web with frame
$P_G\overline{P_H}$." Here the web composition is `IsWebComposition G S C l`: the webs on `S₁` and
`S₂` have frames `a A b m⁻¹` and `b B a m`, and `C` is a rotation of `a A b B`. -/
theorem prop_3_1 {S : Set V} {C l : List V} (h : IsWebComposition G S C l) : IsWebOn G S C := by
  classical
  obtain ⟨a, b, m, A, B, k, S₁, S₂, rfl, hrot, hsupp, hU, hI, hno, hind, hH, hK⟩ := h
  obtain ⟨-, R₁, tri₁, hR₁, hrib₁, hcl₁⟩ := hH
  obtain ⟨-, R₂, tri₂, hR₂, hrib₂, hcl₂⟩ := hK
  -- "Let $R_G$ and $R_H$ be the ribs of $G$ and $H$"
  have hrib₁' : IsRibOn G R₁ (a :: A ++ b :: m.reverse) :=
    hrib₁.congr fun u hu v hv => ⟨fun h => h.1, fun h => ⟨h, hR₁ hu, hR₁ hv⟩⟩
  have hrib₂' : IsRibOn G R₂ (b :: B ++ a :: m) :=
    hrib₂.congr fun u hu v hv => ⟨fun h => h.1, fun h => ⟨h, hR₂ hu, hR₂ hv⟩⟩
  have hlR₁ : ∀ v ∈ a :: m ++ [b], v ∈ R₁ := fun v hv => hrib₁.2.1 v (by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse,
      List.mem_nil_iff, or_false] at hv ⊢
    tauto)
  have hlR₂ : ∀ v ∈ a :: m ++ [b], v ∈ R₂ := fun v hv => hrib₂.2.1 v (by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff,
      or_false] at hv ⊢
    tauto)
  have mem_l : ∀ {v}, v ∈ S₁ → v ∈ S₂ → v ∈ a :: m ++ [b] := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := ⟨h1, h2⟩
    rw [hI] at this
    exact this
  have hinter : R₁ ∩ R₂ = {v | v ∈ a :: m ++ [b]} := by
    ext v
    exact ⟨fun h => mem_l (hR₁ h.1) (hR₂ h.2), fun hv => ⟨hlR₁ v hv, hlR₂ v hv⟩⟩
  have hedge : ∀ u ∈ R₁ ∪ R₂, ∀ v ∈ R₁ ∪ R₂, G.Adj u v →
      (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂) := by
    rintro u (hu | hu) v (hv | hv) huv
    · exact Or.inl ⟨hu, hv⟩
    · rcases hno u (hR₁ hu) v (hR₂ hv) huv with h | h
      · exact Or.inr ⟨hlR₂ u (mem_l (hR₁ hu) h), hv⟩
      · exact Or.inl ⟨hu, hlR₁ v (mem_l h (hR₂ hv))⟩
    · rcases hno v (hR₁ hv) u (hR₂ hu) huv.symm with h | h
      · exact Or.inr ⟨hu, hlR₂ v (mem_l (hR₁ hv) h)⟩
      · exact Or.inl ⟨hlR₁ u (mem_l h (hR₂ hu)), hv⟩
    · exact Or.inr ⟨hu, hv⟩
  -- "We prove that $R$ is a rib."
  have hrib : IsRibOn G (R₁ ∪ R₂) C := by
    have := isRibOn_glue hrib₁' hrib₂' hinter hind hedge
    rw [← hrot] at this
    exact this.of_rotate
  -- "Adding back the clique vertices of $G$ and $H$ on their respective triangles gives a web"
  have hnd : (a :: m ++ [b]).Nodup := by
    obtain ⟨hC₁, hC₁R, φ₁, -⟩ := hrib₁'
    have h := (φ₁.two_paths_inter hC₁ hC₁R).2.1.1
    have hr : (b :: m.reverse ++ [a]).reverse = a :: m ++ [b] := by simp
    rw [← hr]
    exact List.nodup_reverse.mpr h
  have hnot : ∀ x y, x ∈ S₁ \ R₁ → y ∈ S₂ \ R₂ → tri₁ x ≠ tri₂ y := by
    intro x y hx hy he
    obtain ⟨⟨p, q, r, hT, hx3⟩, -⟩ := hcl₁ x hx
    obtain ⟨⟨p', q', r', hT', hy3⟩, -⟩ := hcl₂ y hy
    have hin : ∀ z ∈ ({p, q, r} : Set V), z ∈ a :: m ++ [b] := by
      intro z hz
      have h1 : z ∈ R₁ := by
        rcases hz with rfl | rfl | rfl
        · exact hT.1
        · exact hT.2.1
        · exact hT.2.2.1
      have h2 : z ∈ R₂ := by
        rw [← hx3, he, hy3] at hz
        rcases hz with rfl | rfl | rfl
        · exact hT'.1
        · exact hT'.2.1
        · exact hT'.2.2.1
      exact mem_l (hR₁ h1) (hR₂ h2)
    exact not_triangle_of_induced hnd hind (hin p (by simp)) (hin q (by simp)) (hin r (by simp))
      hT.2.2.2.1.1 hT.2.2.2.2.1.1 hT.2.2.2.2.2.1
  have hRS : R₁ ∪ R₂ ⊆ S₁ ∪ S₂ := union_subset_union hR₁ hR₂
  refine ⟨hsupp, R₁ ∪ R₂, fun x => if x ∈ S₁ then tri₁ x else tri₂ x, hU ▸ hRS, hrib,
    fun x hx => ?_⟩
  obtain ⟨hxS, hxR⟩ := hx
  have hxS' : x ∈ S₁ ∪ S₂ := hU ▸ hxS
  by_cases hx1 : x ∈ S₁
  · have hx2 : x ∉ S₂ := fun h => hxR (Or.inl (hlR₁ x (mem_l hx1 h)))
    simp only [hx1, ↓reduceIte]
    obtain ⟨⟨p, q, r, hT, he⟩, hadj⟩ := hcl₁ x ⟨hx1, fun h => hxR (Or.inl h)⟩
    refine ⟨⟨p, q, r, ⟨Or.inl hT.1, Or.inl hT.2.1, Or.inl hT.2.2.1, hT.2.2.2.1.1,
      hT.2.2.2.2.1.1, hT.2.2.2.2.2.1⟩, he⟩, fun y => ⟨fun hxy => ?_, ?_⟩⟩
    · have hyS : y ∈ S₁ ∪ S₂ := hU ▸ hsupp hxy.symm
      have hy1 : y ∈ S₁ := by
        rcases hyS with h | h
        · exact h
        · exact (hno x hx1 y h hxy).resolve_left hx2
      rcases (hadj y).mp ⟨hxy, hx1, hy1⟩ with h | ⟨⟨-, hyR₁⟩, hyx, hyt⟩
      · exact Or.inl h
      · refine Or.inr ⟨⟨hU ▸ hyS, ?_⟩, hyx, by simp only [hy1, ↓reduceIte]; exact hyt⟩
        rintro (h | h)
        · exact hyR₁ h
        · exact hyR₁ (hlR₁ y (mem_l hy1 (hR₂ h)))
    · rintro (h | ⟨⟨hyS, hyR⟩, hyx, hyt⟩)
      · exact ((hadj y).mpr (Or.inl h)).1
      · by_cases hy1 : y ∈ S₁
        · simp only [hy1, ↓reduceIte] at hyt
          exact ((hadj y).mpr (Or.inr ⟨⟨hy1, fun h => hyR (Or.inl h)⟩, hyx, hyt⟩)).1
        · simp only [hy1, ↓reduceIte] at hyt
          have hy2 : y ∈ S₂ := (hU ▸ hyS : y ∈ S₁ ∪ S₂).resolve_left hy1
          exact absurd hyt.symm (hnot x y ⟨hx1, fun h => hxR (Or.inl h)⟩
            ⟨hy2, fun h => hyR (Or.inr h)⟩)
  · have hx2 : x ∈ S₂ := hxS'.resolve_left hx1
    simp only [hx1, ↓reduceIte]
    obtain ⟨⟨p, q, r, hT, he⟩, hadj⟩ := hcl₂ x ⟨hx2, fun h => hxR (Or.inr h)⟩
    refine ⟨⟨p, q, r, ⟨Or.inr hT.1, Or.inr hT.2.1, Or.inr hT.2.2.1, hT.2.2.2.1.1,
      hT.2.2.2.2.1.1, hT.2.2.2.2.2.1⟩, he⟩, fun y => ⟨fun hxy => ?_, ?_⟩⟩
    · have hyS : y ∈ S₁ ∪ S₂ := hU ▸ hsupp hxy.symm
      have hy2 : y ∈ S₂ := by
        rcases hyS with h | h
        · exact (hno y h x hx2 hxy.symm).resolve_right hx1
        · exact h
      rcases (hadj y).mp ⟨hxy, hx2, hy2⟩ with h | ⟨⟨-, hyR₂⟩, hyx, hyt⟩
      · exact Or.inl h
      · have hy1 : y ∉ S₁ := fun h => hyR₂ (hlR₂ y (mem_l h hy2))
        refine Or.inr ⟨⟨hU ▸ hyS, ?_⟩, hyx, by simp only [hy1, ↓reduceIte]; exact hyt⟩
        rintro (h | h)
        · exact hy1 (hR₁ h)
        · exact hyR₂ h
    · rintro (h | ⟨⟨hyS, hyR⟩, hyx, hyt⟩)
      · exact ((hadj y).mpr (Or.inl h)).1
      · by_cases hy1 : y ∈ S₁
        · simp only [hy1, ↓reduceIte] at hyt
          exact absurd hyt (hnot y x ⟨hy1, fun h => hyR (Or.inl h)⟩
            ⟨hx2, fun h => hxR (Or.inr h)⟩)
        · simp only [hy1, ↓reduceIte] at hyt
          have hy2 : y ∈ S₂ := (hU ▸ hyS : y ∈ S₁ ∪ S₂).resolve_left hy1
          exact ((hadj y).mpr (Or.inr ⟨⟨hy2, fun h => hyR (Or.inr h)⟩, hyx, hyt⟩)).1

end GraphMinor.HP25
