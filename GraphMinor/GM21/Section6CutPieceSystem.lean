module

public import GraphMinor.GM21.Section6CutAssemble
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM21.Section6SidePieces
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, (6.3), claim (2): the presentation from pieces of the supports

This file turns a list of pieces `P_1, …, P_{r₂}` of the old supports, with sides, into the
presentation of claim (2) of the proof of (6.3) (page 28 of the preprint). The new support
over `P_i` is `cutPiece ψ F P_i (a-side) (b-side)`: the lift of `P_i`, together with the point over
`a` (and over `b`) on the side of `P_i`, so that a piece `{a}` gets one of the two points over `a`.

The conditions on the pieces (`isPresentation_of_pieces`) are of three kinds:
* geometry in `Σ`: each `P_i` is a support inside `F_{τ i}*` meeting `F` only in its ends; the
  pieces of `F_j*` hold all vertices and spaces of `F_j*`; two pieces meet only in `a` or `b`, and
  pieces through `a` (or `b`) are on different sides there, both sides being used;
* lifts: the lift of `P_i` holds no point over `a` other than the one on its side (this is where
  `exists_sides_at` is used);
* graphs: the edges of `μ(P_i)` are on the sides of `P_i`; the copies of the graphs `μ(P_i)` are
  disjoint; and every copy of a vertex of `μ(P_i)` is the copy of the vertex in some piece.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM21.Split

universe u v

variable {α : Type u} {β : Type v} {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
  {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

/-- The new support over a piece `P`: its lift, with the point `pa` over `a` and the point `pb` over
`b` if `P` holds `a` or `b`. -/
def cutPiece (ψ : S' → S) (F P : Set S) (pa pb : S') : Set S' :=
  lift ψ F P ∪ (ψ ⁻¹' P ∩ {pa, pb})

open Classical in
/-- The sides of a unit of `Σ'`: those of the piece holding it. -/
noncomputable def pieceColor {r₂ : ℕ} (K : Fin r₂ → Set S') (col : Fin r₂ → Bool × Bool)
    (x : BoundaryUnit S') : Bool × Bool :=
  if h : ∃ i, x.toSet.Nonempty ∧ x.toSet ⊆ K i then col h.choose else (false, false)

omit [TopologicalSpace S'] in
theorem pieceColor_eq {r₂ : ℕ} {K : Fin r₂ → Set S'} (col : Fin r₂ → Bool × Bool)
    (hK : Pairwise (fun i i' => Disjoint (K i) (K i'))) {x : BoundaryUnit S'} {i : Fin r₂}
    (hne : x.toSet.Nonempty) (hx : x.toSet ⊆ K i) : pieceColor K col x = col i := by
  have h : ∃ i, x.toSet.Nonempty ∧ x.toSet ⊆ K i := ⟨i, hne, hx⟩
  unfold pieceColor
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨-, hx'⟩ := h.choose_spec
  by_contra hc
  have hii : h.choose ≠ i := fun he => hc (by rw [he])
  obtain ⟨z, hz⟩ := hne
  exact disjoint_left.mp (hK hii) (hx' hz) (hx hz)

section system

variable {r₂ : ℕ} {P : Fin r₂ → Set S} {col : Fin r₂ → Bool × Bool} {am ap bm bp : S'}

/-- The new support over `P_i` meets the points over `a` only in the point on its side. -/
theorem cutPiece_inter_a (hF : IsProperLineInSurface F a b) (hpb : ψ ⁻¹' {b} = {bm, bp})
    (hsideA : ∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {a} ⊆ {cond (col i).1 ap am}) (i : Fin r₂) :
    cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm) ∩ ψ ⁻¹' {a} ⊆
      {cond (col i).1 ap am} := by
  rintro z ⟨hz | ⟨-, hz | hz⟩, hza⟩
  · exact hsideA i ⟨hz, hza⟩
  · exact hz
  · exfalso
    have hz' : ψ z = b := by
      rw [mem_singleton_iff.mp hz]
      cases (col i).2
      · exact show bm ∈ ψ ⁻¹' {b} from hpb ▸ Or.inl rfl
      · exact show bp ∈ ψ ⁻¹' {b} from hpb ▸ Or.inr rfl
    exact hF.ne (hza.symm.trans hz')

/-- The new support over `P_i` meets the points over `b` only in the point on its side. -/
theorem cutPiece_inter_b (hF : IsProperLineInSurface F a b) (hpa : ψ ⁻¹' {a} = {am, ap})
    (hsideB : ∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {b} ⊆ {cond (col i).2 bp bm}) (i : Fin r₂) :
    cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm) ∩ ψ ⁻¹' {b} ⊆
      {cond (col i).2 bp bm} := by
  rintro z ⟨hz | ⟨-, hz | hz⟩, hzb⟩
  · exact hsideB i ⟨hz, hzb⟩
  · exfalso
    have hz' : ψ z = a := by
      rw [hz]
      cases (col i).1
      · exact show am ∈ ψ ⁻¹' {a} from hpa ▸ Or.inl rfl
      · exact show ap ∈ ψ ⁻¹' {a} from hpa ▸ Or.inr rfl
    exact hF.ne (hz'.symm.trans hzb)
  · exact hz

/-- The new supports: `ψ` is one to one on each, and maps it onto the piece. -/
theorem cutPiece_props (hS : IsSurface S) (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂)
    (hF : IsProperLineInSurface F a b) (hpa : ψ ⁻¹' {a} = {am, ap})
    (hpb : ψ ⁻¹' {b} = {bm, bp}) {Γ : Drawing S}
    (hPsup : ∀ i, ∃ u w, SupportHasEnds Γ (P i) u w ∧ P i ∩ F ⊆ {u, w})
    (hsideA : ∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {a} ⊆ {cond (col i).1 ap am})
    (hsideB : ∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {b} ⊆ {cond (col i).2 bp bm}) (i : Fin r₂) :
    lift ψ F (P i) ⊆ cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm) ∧
      cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm) ⊆ ψ ⁻¹' P i ∧
      InjOn ψ (cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm)) ∧
      ψ '' cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm) = P i := by
  obtain ⟨u, w, hsup, hPF'⟩ := hPsup i
  obtain ⟨hinjL, hLsub, hLsup⟩ := h.lift_piece hS hsup hPF'
  have hPbd : P i ⊆ bd S := GM21.Supports.subset_bd_of_isSupportOfDrawing ⟨u, w, hsup⟩
  have hψpa : ψ (cond (col i).1 ap am) = a := by
    cases (col i).1
    · exact show am ∈ ψ ⁻¹' {a} from hpa ▸ Or.inl rfl
    · exact show ap ∈ ψ ⁻¹' {a} from hpa ▸ Or.inr rfl
  have hψpb : ψ (cond (col i).2 bp bm) = b := by
    cases (col i).2
    · exact show bm ∈ ψ ⁻¹' {b} from hpb ▸ Or.inl rfl
    · exact show bp ∈ ψ ⁻¹' {b} from hpb ▸ Or.inr rfl
  have hsub : cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm) ⊆ ψ ⁻¹' P i :=
    union_subset hLsub inter_subset_left
  have hFab : ∀ x ∈ P i, x ∈ F → x = a ∨ x = b := fun x hx hxF => by
    have : x ∈ F ∩ bd S := ⟨hxF, hPbd hx⟩
    rw [hF.inter_bd_eq] at this
    exact this
  refine ⟨subset_union_left, hsub, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxF : ψ x ∈ F
    · rcases hFab _ (hsub hx) hxF with hxa | hxb
      · have h1 := cutPiece_inter_a hF hpb hsideA i
          ⟨hx, hxa⟩
        have h2 := cutPiece_inter_a hF hpb hsideA i
          ⟨hy, show ψ y = a from hxy ▸ hxa⟩
        exact (mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm
      · have h1 := cutPiece_inter_b hF hpa hsideB i
          ⟨hx, hxb⟩
        have h2 := cutPiece_inter_b hF hpa hsideB i
          ⟨hy, show ψ y = b from hxy ▸ hxb⟩
        exact (mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm
    · exact h.injOn_compl hxF (show ψ y ∉ F from hxy ▸ hxF) hxy
  · apply Subset.antisymm (image_subset_iff.mpr hsub)
    intro x hx
    by_cases hxF : x ∈ F
    · rcases hFab x hx hxF with rfl | rfl
      · exact ⟨_, Or.inr ⟨show ψ _ ∈ P i by rw [hψpa]; exact hx, Or.inl rfl⟩, hψpa⟩
      · exact ⟨_, Or.inr ⟨show ψ _ ∈ P i by rw [hψpb]; exact hx, Or.inr rfl⟩, hψpb⟩
    · obtain ⟨z, rfl⟩ := h.cutting.2.1 x
      exact ⟨z, Or.inl (hLsup ⟨hx, hxF⟩), rfl⟩

omit [TopologicalSpace S'] in
theorem cond_injective {T : Type*} {m p : T} (hmp : m ≠ p) {c c' : Bool}
    (h : cond c p m = cond c' p m) : c = c' := by
  cases c <;> cases c' <;> simp_all [eq_comm]

open Classical in
omit [TopologicalSpace S'] in
theorem decide_cond_eq {T : Type*} {m p : T} (hmp : m ≠ p) (c : Bool) :
    c = decide (cond c p m = p) := by
  cases c <;> simp [hmp]

open Classical in
/-- **The presentation of claim (2) from a system of pieces.** The new supports are the sets
`cutPiece ψ F (P i) …`, the vertex names are `cutName`, and the graphs over the pieces are the copies
of `μ(P_i)` on the sides of `P_i`. -/
theorem isPresentation_of_pieces {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b)
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) (hFU : F ∩ Γ.U ⊆ {a, b}) [ConnectedSpace S'] {Γ' : Drawing S'}
    (hU : Γ'.U = ψ ⁻¹' Γ.U) (hV : Γ'.V = ψ ⁻¹' Γ.V)
    (hE : ∀ e' ∈ Γ'.E, ∃ e ∈ Γ.E, e' = ψ ⁻¹' e)
    (hΓ' : Γ'.IsProper) (hcuff : ∀ C ∈ cuffs S', 2 ≤ (Γ'.V ∩ C).ncard)
    (hpa : ψ ⁻¹' {a} = {am, ap}) (hamp : am ≠ ap) (hpb : ψ ⁻¹' {b} = {bm, bp}) (hbmp : bm ≠ bp)
    (cb : Bool) {Apf Bpf : Set S}
    (hlink : ∀ e ∈ Γ.E, ∃ u w, u ≠ w ∧ closure e ∩ Γ.V = {u, w})
    (hApf : ∃ j, Apf ⊆ F_star j) (hBpf : ∃ j, Bpf ⊆ F_star j) {τ : Fin r₂ → Fin r}
    (hPsup : ∀ i, ∃ u w, SupportHasEnds Γ (P i) u w ∧ P i ∩ F ⊆ {u, w})
    (hPF : ∀ i, P i ⊆ F_star (τ i))
    (hPint : ∀ i i', i ≠ i' → P i ∩ P i' ⊆ {a, b})
    (hsideA : ∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {a} ⊆ {cond (col i).1 ap am})
    (hsideB : ∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {b} ⊆ {cond (col i).2 bp bm})
    (hdiffA : ∀ i i', i ≠ i' → a ∈ P i → a ∈ P i' → (col i).1 ≠ (col i').1)
    (hdiffB : ∀ i i', i ≠ i' → b ∈ P i → b ∈ P i' → (col i).2 ≠ (col i').2)
    (hbothA : ∀ c, ∃ i, a ∈ P i ∧ (col i).1 = c) (hbothB : ∀ c, ∃ i, b ∈ P i ∧ (col i).2 = c)
    (hPV : ∀ v ∈ Γ.V ∩ bd S, ∃ i, v ∈ P i)
    (hPs : ∀ j, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j → ∃ i, s ⊆ P i)
    (hcol : ∀ i, ∀ e ∈ (supportGraph G Γ μ (P i)).edgeSet,
      (e ∈ cutEdges G Γ μ ψ ιE Apf ap ↔ (col i).1 = true) ∧
        (e ∈ cutEdges G Γ μ ψ ιE Bpf bp ↔ (col i).2 = true))
    (hcover : (split2 G (μ (.vertex a)).vertexSet (cutEdges G Γ μ ψ ιE Apf ap) (splitB μ a b cb)
        (cutEdges G Γ μ ψ ιE Bpf bp)).vertexSet ⊆
      cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp '' Γ'.V ∪
        ⋃ i, nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i) ''
          (supportGraph G Γ μ (P i)).vertexSet)
    (hdisjH : Pairwise (fun i i' =>
      Disjoint (nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i) ''
          (supportGraph G Γ μ (P i)).vertexSet)
        (nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i') ''
          (supportGraph G Γ μ (P i')).vertexSet))) :
    IsPresentation (split2 G (μ (.vertex a)).vertexSet (cutEdges G Γ μ ψ ιE Apf ap)
        (splitB μ a b cb) (cutEdges G Γ μ ψ ιE Bpf bp)) Γ'
      (subOn (split2 G (μ (.vertex a)).vertexSet (cutEdges G Γ μ ψ ιE Apf ap)
        (splitB μ a b cb) (cutEdges G Γ μ ψ ιE Bpf bp))
        (cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp '' Γ'.V) (ιE '' Γ.E))
      (cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp)
      (fun e' => ιE (ψ '' e')) r₂
      (fun i => cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm))
      (fun i => isoImage (nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i)) id
        (supportGraph G Γ μ (P i)))
      (fun x => isoImage (nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb)
          (pieceColor (fun i => cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm))
            col x)) id (μ (unitMap ψ x))) (q ∘ τ) := by
  have hS := hP.is_surface
  set K : Fin r₂ → Set S' := fun i => cutPiece ψ F (P i) (cond (col i).1 ap am)
    (cond (col i).2 bp bm) with hKdef
  have hprops := fun i => cutPiece_props (col := col) hS h hF hpa hpb hPsup hsideA hsideB i
  have himg : ∀ i, ψ '' K i = P i := fun i => (hprops i).2.2.2
  have hψpa : ∀ c : Bool, ψ (cond c ap am) = a := fun c => by
    cases c
    · exact show am ∈ ψ ⁻¹' {a} from hpa ▸ Or.inl rfl
    · exact show ap ∈ ψ ⁻¹' {a} from hpa ▸ Or.inr rfl
  have hψpb : ∀ c : Bool, ψ (cond c bp bm) = b := fun c => by
    cases c
    · exact show bm ∈ ψ ⁻¹' {b} from hpb ▸ Or.inl rfl
    · exact show bp ∈ ψ ⁻¹' {b} from hpb ▸ Or.inr rfl
  -- The new supports are supports of `Γ'`.
  have hKsup : ∀ i, IsSupportOfDrawing Γ' (K i) := fun i => by
    obtain ⟨u, w, hsup, hPF'⟩ := hPsup i
    exact h.isSupport_of_lift hS hF hV hsup hPF' (hprops i).1 (hprops i).2.1 (hprops i).2.2.1
      (himg i)
  -- Two new supports are disjoint: a common point lies over `a` or `b`, on both sides.
  have hKdisj : Pairwise (fun i i' => Disjoint (K i) (K i')) := by
    intro i i' hii
    refine disjoint_left.mpr fun x hx hx' => ?_
    have hxP : ψ x ∈ P i := (hprops i).2.1 hx
    have hxP' : ψ x ∈ P i' := (hprops i').2.1 hx'
    rcases hPint i i' hii ⟨hxP, hxP'⟩ with hxa | hxb
    · have h1 := mem_singleton_iff.mp (cutPiece_inter_a hF hpb hsideA i ⟨hx, hxa⟩)
      have h2 := mem_singleton_iff.mp (cutPiece_inter_a hF hpb hsideA i' ⟨hx', hxa⟩)
      exact hdiffA i i' hii (hxa ▸ hxP) (hxa ▸ hxP') (cond_injective hamp (h1.symm.trans h2))
    · have h1 := mem_singleton_iff.mp (cutPiece_inter_b hF hpa hsideB i ⟨hx, hxb⟩)
      have h2 := mem_singleton_iff.mp (cutPiece_inter_b hF hpa hsideB i' ⟨hx', hxb⟩)
      exact hdiffB i i' hii (hxb ▸ hxP) (hxb ▸ hxP') (cond_injective hbmp (h1.symm.trans h2))
  -- The new supports hold every vertex of `Γ'` on the boundary.
  have hKV : Γ'.V ∩ bd S' ⊆ ⋃ i, K i := by
    rintro x ⟨hxV, hxbd⟩
    have hψV : ψ x ∈ Γ.V := by rw [hV] at hxV; exact hxV
    rw [h.bd_eq hS hF] at hxbd
    by_cases hxF : ψ x ∈ F
    · rcases mem_ends_of_mem_line hFU hxF hψV with hxa | hxb
      · obtain ⟨i, hai, hci⟩ := hbothA (decide (x = ap))
        refine mem_iUnion.mpr ⟨i, Or.inr ⟨show ψ x ∈ P i by rw [hxa]; exact hai, Or.inl ?_⟩⟩
        rw [hci]
        rcases eq_or_eq_of_map hpa hxa with rfl | rfl
        · simp [hamp]
        · simp
      · obtain ⟨i, hbi, hci⟩ := hbothB (decide (x = bp))
        refine mem_iUnion.mpr ⟨i, Or.inr ⟨show ψ x ∈ P i by rw [hxb]; exact hbi, Or.inr ?_⟩⟩
        rw [hci]
        rcases eq_or_eq_of_map hpb hxb with rfl | rfl
        · simp [hbmp]
        · simp
    · have hxbd' : ψ x ∈ bd S := hxbd.resolve_right hxF
      obtain ⟨i, hi⟩ := hPV _ ⟨hψV, hxbd'⟩
      obtain ⟨u, w, hsup, hPF'⟩ := hPsup i
      exact mem_iUnion.mpr ⟨i, Or.inl ((h.lift_piece hS hsup hPF').2.2 ⟨hi, hxF⟩)⟩
  have hres := isPresentation_cut hP h hF habV hU hV hE hΓ' hcuff (K := K) (τ := τ) (col := col)
    hKsup hKdisj (fun i => (hprops i).2.2.1) (fun i => (himg i).symm ▸ hPF i) hKV
    (fun j s hs hsj => by
      obtain ⟨i, hi⟩ := hPs j s hs hsj
      exact ⟨i, (himg i).symm ▸ hi⟩)
    (fun i => (himg i).symm ▸ hcol i)
    (cutName_injOn hP h hF habV hFU hV hpa hamp hpb hbmp cb)
    (fun u _ => ⟨_, rfl⟩)
    (fun i u hu => cutName_eq hP hF habV hV cb hu.1 (col i)
      (fun hua => by
        rw [mem_singleton_iff.mp (cutPiece_inter_a hF hpb hsideA i ⟨hu.2, hua⟩)]
        exact decide_cond_eq hamp _)
      (fun hub => by
        rw [mem_singleton_iff.mp (cutPiece_inter_b hF hpa hsideB i ⟨hu.2, hub⟩)]
        exact decide_cond_eq hbmp _))
    (fun e he u hu => inc_cutName_iff hP h hF habV hFU hV hpa hamp hpb hbmp cb hlink hApf hBpf he
      hu)
    (fun e he w hw => mem_image_cutName_of_inc hP h hF habV hFU hV hpa hamp hpb hbmp cb hlink
      hApf hBpf he hw)
    (cu := pieceColor K col)
    (fun i u hu => pieceColor_eq col hKdisj (singleton_nonempty u)
      (singleton_subset_iff.mpr hu.2))
    (fun i s hs hsK => by
      obtain ⟨x, hx, rfl⟩ := hs
      exact pieceColor_eq col hKdisj ⟨x, mem_connectedComponentIn hx⟩ hsK)
    (by simp only [himg]; exact hcover) (by simp only [himg]; exact hdisjH)
  simp only [himg] at hres
  exact hres

end system

end CutLine
end GM21
end GraphMinor
