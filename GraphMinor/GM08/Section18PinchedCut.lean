module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18SlitCut
import GraphMinor.GM08.Section18PinchedSides
import GraphMinor.GM08.Section18LineLift
import GraphMinor.GM08.Section18LineCut
import GraphMinor.GM08.Section18CutSum
import GraphMinor.GM08.Section18CutBoundary
import GraphMinor.GM08.Section18CutCounting
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.CutIArc
import GraphMinor.Surface.CutLift
import GraphMinor.Surface.Cuffs

/-!
# The pinched cut

Let `Z` be a circle in a connected surface `R` that meets the boundary at
exactly one point `p`. We cut `R` along `Z`. Near `p` the circle looks like two
arcs that leave one boundary point, so `p` gets three points over it, and every
other point of `Z` gets two.

No earlier tool cuts along such a circle: `cutOArc` needs a circle off the
boundary, and `cutIArc` needs a line with two different ends on the boundary.
So we cut in three steps. Split `Z` at `p` and two more points `m₁, m₂` into a
line `A` from `p` to `m₁`, a line `M` from `m₂` to `m₁`, and a line `N` from `p`
to `m₂`.

1. Cut along `M`, which misses the boundary (`exists_slit_cut`). This adds a
   cuff over `M`, and raises `g` by one.
2. Cut along the lift of `A`. Its ends lie over `p` and over `m₁`, so on the old
   boundary and on the new cuff. These are different cuffs, so the cut lowers
   `g` by one (`cutIArc`).
3. Cut along the lift of `N` (`cutIArc`). Either every piece has smaller `g`,
   or one piece is a closed disc and the other is a copy of the surface. In the
   second case each piece holds a point over `p`.

The point `p` is an end of both `A` and `N`, so it has three points over it.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

open Classical in
/-- Over one point, a line that maps one to one onto `N` holds one point if
the point is in `N`, and none otherwise. -/
theorem ncard_preimage_inter_of_bijOn {Y R : Type w} {ψ : Y → R} {L : Set Y} {N : Set R}
    (hb : BijOn ψ L N) (x : R) :
    (ψ ⁻¹' {x} ∩ L).ncard = if x ∈ N then 1 else 0 := by
  split_ifs with hx
  · obtain ⟨y, hy, rfl⟩ := hb.surjOn hx
    refine ncard_eq_one.mpr ⟨y, ?_⟩
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzL⟩
      exact hb.injOn hzL hy hz
    · rintro rfl
      exact ⟨rfl, hy⟩
  · convert ncard_empty Y
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
      not_and]
    rintro rfl hzL
    exact hx (hb.mapsTo hzL)

/-- **Lifting a line whose inside misses the cut and the boundary.** After a
cut along a closed set `F`, a line `N` whose inner points miss `bd R ∪ F` and
whose ends lie on `bd R ∪ F` lifts to a proper line `L`, which maps one to one
onto `N` and holds every lift of an inner point of `N`. -/
theorem exists_proper_lift {Y R : Type w} [TopologicalSpace Y] [TopologicalSpace R]
    (hY : IsSurface Y) (hR : IsSurface R) {φ : Y → R} {F N : Set R} {s t : R}
    (hφ : GM19.IsCutMap φ F) (hF : IsClosed F) (hN : IsLineWithEnds N s t)
    (hoff : Disjoint (N \ {s, t}) (bd R ∪ F)) (hs : s ∈ bd R ∪ F) (ht : t ∈ bd R ∪ F) :
    ∃ x y : Y, ∃ L : Set Y, φ x = s ∧ φ y = t ∧ IsLineWithEnds L x y ∧ BijOn φ L N ∧
      L ∩ bd Y = {x, y} ∧ φ ⁻¹' N ⊆ L ∪ bd Y := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  have : T2Space R := hR.2.1
  have hbd : φ ⁻¹' (bd R ∪ F) = bd Y := (isCutAlongSet_of_cutMap hR hY hF hφ).preimage_bd
  obtain ⟨x, y, hx, hy, hL, hbij, hdiff⟩ :=
    exists_line_closure_lift_of_cutMap hφ hF hN (hoff.mono_right subset_union_right)
  refine ⟨x, y, _, hx, hy, hL, hbij, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨hzL, hzb⟩
      by_contra hz
      have hz' : z ∈ φ ⁻¹' (N \ {s, t}) := hdiff ▸ ⟨hzL, hz⟩
      exact disjoint_left.mp hoff hz' (hbd ▸ hzb : z ∈ φ ⁻¹' (bd R ∪ F))
    · rintro (rfl | rfl)
      · exact ⟨hL.left_mem, hbd ▸ (show φ z ∈ bd R ∪ F by rw [hx]; exact hs)⟩
      · exact ⟨hL.right_mem, hbd ▸ (show φ z ∈ bd R ∪ F by rw [hy]; exact ht)⟩
  · intro z hz
    by_cases hst : φ z ∈ ({s, t} : Set R)
    · refine Or.inr (hbd ▸ ?_)
      rcases hst with h | h
      · exact (show φ z ∈ bd R ∪ F by rw [h]; exact hs)
      · exact (show φ z ∈ bd R ∪ F by rw [mem_singleton_iff.mp h]; exact ht)
    · exact Or.inl (subset_closure ⟨hz, hst⟩)

/-- **The pinched cut.** Let `Z` be a circle in a connected surface `R` that
meets the boundary only at `p`. There is a cut along `Z` with three points over
`p` and two over every other point of `Z`. Either it lowers the measure, or it
has a piece `D` that is a closed disc, its complement is connected, and both
`D` and its complement hold points over `p`. In that case every other point of
`Z` has a point over it in `D` and one in the complement. -/
theorem exists_pinched_cut {R : Type w} [TopologicalSpace R] [ConnectedSpace R] (hR : IsSurface R)
    {Z : Set R} {p : R} (hZ : IsOArc Z) (hZp : Z ∩ bd R = {p}) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ρ : T → R), IsSurface T ∧ GM19.IsCutMap ρ Z ∧
      (ρ ⁻¹' {p}).ncard = 3 ∧ (∀ z ∈ Z, z ≠ p → (ρ ⁻¹' {z}).ncard = 2) ∧
      (surfaceComplexity T < surfaceComplexity R ∨
        ∃ D : Set T, IsClopen D ∧ IsClosedDisc D ∧ ConnectedSpace (Dᶜ : Set T) ∧
          (D ∩ ρ ⁻¹' {p}).Nonempty ∧ (Dᶜ ∩ ρ ⁻¹' {p}).Nonempty ∧
          ∀ z ∈ Z, z ≠ p → (∃ w ∈ D, ρ w = z) ∧ (∃ w ∈ Dᶜ, ρ w = z)) := by
  classical
  have : T2Space R := hR.2.1
  have hpZb : p ∈ Z ∩ bd R := hZp.symm ▸ rfl
  have hpZ : p ∈ Z := hpZb.1
  have hpb : p ∈ bd R := hpZb.2
  have hZbd : ∀ z ∈ Z, z ∈ bd R → z = p := fun z hz hzb => (hZp ▸ ⟨hz, hzb⟩ : z ∈ ({p} : Set R))
  -- a second point `m₁` of `Z`
  obtain ⟨m₁, hm₁Z, hm₁p⟩ : ∃ m₁ ∈ Z, m₁ ≠ p := by
    obtain ⟨a, b, -, ha, hb, -, hab, -, -⟩ := hZ.exists_three
    by_cases hap : a = p
    · exact ⟨b, hb, fun h => hab (hap.trans h.symm)⟩
    · exact ⟨a, ha, hap⟩
  obtain ⟨A, B, hA, hB, hAB, hAiB⟩ := hZ.lines hpZ hm₁Z hm₁p.symm
  -- a third point `m₂`, inside `B`
  obtain ⟨m₂, hm₂B, hm₂p, hm₂m₁⟩ : ∃ m₂ ∈ B, m₂ ≠ p ∧ m₂ ≠ m₁ := by
    obtain ⟨f, h0, h1⟩ := hB
    have hh : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    refine ⟨f ⟨1 / 2, hh⟩, (f _).2, fun h => ?_, fun h => ?_⟩
    · have := f.injective (Subtype.ext (h.trans h0.symm))
      have h' := congrArg Subtype.val this
      norm_num at h'
    · have := f.injective (Subtype.ext (h.trans h1.symm))
      have h' := congrArg Subtype.val this
      norm_num at h'
  obtain ⟨N, M, hN, hM, hNM, hNiM⟩ := hB.split hm₂B hm₂p hm₂m₁
  have hNB : N ⊆ B := hNM ▸ subset_union_left
  have hMB : M ⊆ B := hNM ▸ subset_union_right
  have hBZ : B ⊆ Z := hAB ▸ subset_union_right
  have hAZ : A ⊆ Z := hAB ▸ subset_union_left
  have hm₁M : m₁ ∈ M := hM.right_mem
  have hm₂M : m₂ ∈ M := hM.left_mem
  have hm₂N : m₂ ∈ N := hN.right_mem
  have hpN : p ∈ N := hN.left_mem
  have hpA : p ∈ A := hA.left_mem
  have hm₁A : m₁ ∈ A := hA.right_mem
  have hAB' : ∀ z ∈ A, z ∈ B → z = p ∨ z = m₁ := fun z hzA hzB => by
    have h : z ∈ A ∩ B := ⟨hzA, hzB⟩
    rw [hAiB] at h
    exact h
  have hNM' : ∀ z ∈ N, z ∈ M → z = m₂ := fun z hzN hzM => by
    have h : z ∈ N ∩ M := ⟨hzN, hzM⟩
    rw [hNiM] at h
    exact h
  have hpM : p ∉ M := fun h => hm₂p (hNM' p hpN h).symm
  have hm₁N : m₁ ∉ N := fun h => hm₂m₁ (hNM' m₁ h hm₁M).symm
  have hMbd : Disjoint M (bd R) := disjoint_left.mpr fun z hzM hzb =>
    hpM (hZbd z (hBZ (hMB hzM)) hzb ▸ hzM)
  have hMc : IsClosed M := hM.isCompact.isClosed
  have hAc : IsClosed A := hA.isCompact.isClosed
  -- step 1: the slit along `M`
  obtain ⟨Y, tY, φ, hY, hYc, hφ, hφ2, hφ1, hMO, a, b, c, ⟨eR⟩, ⟨eY⟩⟩ :=
    exists_slit_cut hR hM hm₂m₁ hMbd
  let := tY
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  have hbdY : φ ⁻¹' (bd R ∪ M) = bd Y := (isCutAlongSet_of_cutMap hR hY hMc hφ).preimage_bd
  -- step 2: the cut along the lift of `A`
  have hoffA : Disjoint (A \ {p, m₁}) (bd R ∪ M) := by
    refine disjoint_left.mpr fun z hz hzbM => hz.2 ?_
    rcases hzbM with hzb | hzM
    · exact Or.inl (hZbd z (hAZ hz.1) hzb)
    · rcases hAB' z hz.1 (hMB hzM) with h | h
      · exact Or.inl h
      · exact Or.inr h
  obtain ⟨x₁, y₁, L₁, hx₁, hy₁, hL₁, hbL₁, hL₁bd, hL₁cov⟩ :=
    exists_proper_lift hY hR hφ hMc hA hoffA (Or.inl hpb) (Or.inr hm₁M)
  have hx₁b : x₁ ∈ bd Y := by
    have h : x₁ ∈ L₁ ∩ bd Y := by rw [hL₁bd]; exact Or.inl rfl
    exact h.2
  have hy₁b : y₁ ∈ bd Y := by
    have h : y₁ ∈ L₁ ∩ bd Y := by rw [hL₁bd]; exact Or.inr rfl
    exact h.2
  have hxy₁ : x₁ ≠ y₁ := fun h => hm₁p (hy₁ ▸ hx₁ ▸ congrArg φ h).symm
  have hcuffs₁ : connectedComponentIn (bd Y) x₁ ≠ connectedComponentIn (bd Y) y₁ :=
    connectedComponentIn_bd_ne_of_map hφ.1 (isClosed_bd R) hMc hMbd.symm
      (fun z hz => (hbdY ▸ hz : z ∈ φ ⁻¹' (bd R ∪ M))) hx₁b hy₁b
      (by rw [hx₁]; exact hpb) (by rw [hy₁]; exact hm₁M)
  obtain ⟨T₂, t₂, ψ₂, hT₂, hcut₂, hdist₂, -, X₁, X₁', hd₁, -, hX₁l, hX₁'l, hb₁, hb₁'⟩ :=
    cutIArc Y L₁ x₁ y₁ hY hYc hxy₁ hL₁bd hL₁
  let := t₂
  obtain ⟨hT₂c, a', b', c', ⟨eY'⟩, ⟨eT₂⟩⟩ := hdist₂ hcuffs₁
  have : CompactSpace T₂ := hT₂.1
  have : T2Space T₂ := hT₂.2.1
  have hgT₂ : surfaceComplexity T₂ = surfaceComplexity R := by
    have h1 := connectedSurfaceComplexity_eq ⟨eY⟩
    rw [connectedSurfaceComplexity_eq ⟨eY'⟩] at h1
    rw [surfaceComplexity_eq_connected, surfaceComplexity_eq_connected,
      connectedSurfaceComplexity_eq ⟨eT₂⟩, connectedSurfaceComplexity_eq ⟨eR⟩]
    omega
  have hL₁c : IsClosed L₁ := hL₁.isCompact.isClosed
  have hφ₂ : GM19.IsCutMap (φ ∘ ψ₂) (M ∪ A) :=
    IsCutMap.comp hφ (GM19.IsCutting.isCutMap hcut₂) hL₁c (fun z hz => hbL₁.mapsTo hz) hL₁cov
  -- step 3: the cut along the lift of `N`
  have hMAc : IsClosed (M ∪ A) := hMc.union hAc
  have hoffN : Disjoint (N \ {p, m₂}) (bd R ∪ (M ∪ A)) := by
    refine disjoint_left.mpr fun z hz hzb => hz.2 ?_
    rcases hzb with hzb | hzM | hzA
    · exact Or.inl (hZbd z (hBZ (hNB hz.1)) hzb)
    · exact Or.inr (hNM' z hz.1 hzM)
    · rcases hAB' z hzA (hNB hz.1) with h | h
      · exact Or.inl h
      · exact absurd (h ▸ hz.1) hm₁N
  obtain ⟨x₂, y₂, L₂, hx₂, hy₂, hL₂, hbL₂, hL₂bd, hL₂cov⟩ :=
    exists_proper_lift hT₂ hR hφ₂ hMAc hN hoffN (Or.inl hpb) (Or.inr (Or.inl hm₂M))
  have hxy₂ : x₂ ≠ y₂ := fun h => hm₂p (hy₂ ▸ hx₂ ▸ congrArg (φ ∘ ψ₂) h).symm
  obtain ⟨T₃, t₃, ψ₃, hT₃, hcut₃, hdist₃, hsame₃, X, X', hdX, hun, hX, hX', hbX, hbX'⟩ :=
    cutIArc T₂ L₂ x₂ y₂ hT₂ hT₂c hxy₂ hL₂bd hL₂
  let := t₃
  have : CompactSpace T₃ := hT₃.1
  have hL₂c : IsClosed L₂ := hL₂.isCompact.isClosed
  have hZeq : M ∪ A ∪ N = Z := by
    rw [← hAB, ← hNM]
    ext z
    simp only [mem_union]
    tauto
  have hρ : GM19.IsCutMap ((φ ∘ ψ₂) ∘ ψ₃) Z := hZeq ▸
    IsCutMap.comp hφ₂ (GM19.IsCutting.isCutMap hcut₃) hL₂c (fun z hz => hbL₂.mapsTo hz) hL₂cov
  -- the number of points over each point
  have hcount : ∀ x, (((φ ∘ ψ₂) ∘ ψ₃) ⁻¹' {x}).ncard =
      (if x ∈ M \ {m₂, m₁} then 2 else 1) + (if x ∈ A then 1 else 0) +
        (if x ∈ N then 1 else 0) := by
    intro x
    have hf₁ : (φ ⁻¹' {x}).Finite := hφ.2.2.2.1 x
    have hf₂ : ((φ ∘ ψ₂) ⁻¹' {x}).Finite := hφ₂.2.2.2.1 x
    have e₃ : ((φ ∘ ψ₂) ∘ ψ₃) ⁻¹' {x} = ψ₃ ⁻¹' ((φ ∘ ψ₂) ⁻¹' {x}) := rfl
    have e₂ : (φ ∘ ψ₂) ⁻¹' {x} = ψ₂ ⁻¹' (φ ⁻¹' {x}) := rfl
    rw [e₃, IsCutting.ncard_preimage hcut₃ hf₂, ncard_preimage_inter_of_bijOn hbL₂, e₂,
      IsCutting.ncard_preimage hcut₂ hf₁, ncard_preimage_inter_of_bijOn hbL₁]
    congr 2
    split_ifs with h
    · exact hφ2 x h
    · exact hφ1 x h
  refine ⟨T₃, t₃, (φ ∘ ψ₂) ∘ ψ₃, hT₃, hρ, ?_, ?_, ?_⟩
  · have hpM' : p ∉ M \ {m₂, m₁} := fun h => hpM h.1
    rw [hcount]
    simp only [hpM', hpA, hpN, ↓reduceIte]
  · intro z hz hzp
    rw [hcount]
    by_cases hzA : z ∈ A
    · have hzN : z ∉ N := fun hzN => by
        rcases hAB' z hzA (hNB hzN) with h | h
        · exact hzp h
        · exact hm₁N (h ▸ hzN)
      have hzM : z ∉ M \ {m₂, m₁} := fun hzM => by
        rcases hAB' z hzA (hMB hzM.1) with h | h
        · exact hzp h
        · exact hzM.2 (Or.inr h)
      simp only [hzM, hzA, hzN, ↓reduceIte]
    · by_cases hzN : z ∈ N
      · have hzM : z ∉ M \ {m₂, m₁} := fun hzM => hzM.2 (Or.inl (hNM' z hzN hzM.1))
        simp only [hzM, hzA, hzN, ↓reduceIte]
      · have hzB : z ∈ B := by
          rw [← hAB] at hz
          exact hz.resolve_left hzA
        have hzM : z ∈ M := by
          rw [← hNM] at hzB
          exact hzB.resolve_left hzN
        have hzM' : z ∈ M \ {m₂, m₁} := ⟨hzM, by
          rintro (h | h)
          · exact hzN (h ▸ hm₂N)
          · exact hzA (h ▸ hm₁A)⟩
        simp only [hzM', hzA, hzN, ↓reduceIte]
  -- the measure
  have : Nonempty T₃ := ⟨(hcut₃.2.1 x₂).choose⟩
  by_cases hc : connectedComponentIn (bd T₂) x₂ = connectedComponentIn (bd T₂) y₂
  · rcases hsame₃ hc with hsimp | ⟨K₁, K₂, hK, hcomps, ⟨e₁⟩, -⟩
    · left
      have := surfaceComplexity_lt_of_cutIsSimpler hsimp
      omega
    · right
      obtain ⟨eX⟩ := hX
      obtain ⟨eX'⟩ := hX'
      rcases cut_comps hcut₃ hT₃ (isPreconnected_of_isLine ⟨eX⟩) (isPreconnected_of_isLine ⟨eX'⟩)
          hun (eX 0).2 (eX' 0).2 with hconn |
        ⟨W₁, W₂, -, hW, hXW, hX'W, hW₁, hW₂, hU, hdis, hc₁, hc₂⟩
      · exfalso
        have h1 : K₁ ∈ spaceComponents T₃ := hcomps ▸ (Or.inl rfl)
        have h2 : K₂ ∈ spaceComponents T₃ := hcomps ▸ (Or.inr rfl)
        rw [Surface.spaceComponents_eq] at h1 h2
        obtain ⟨a, rfl⟩ := h1
        obtain ⟨b, rfl⟩ := h2
        exact hK ((PreconnectedSpace.connectedComponent_eq_univ a).trans
          (PreconnectedSpace.connectedComponent_eq_univ b).symm)
      have hK₁ : K₁ ∈ ({W₁, W₂} : Set (Set T₃)) := hW ▸ hcomps ▸ (Or.inl rfl)
      have hdisc : IsClosedDisc K₁ := ⟨e₁.symm⟩
      have hW₁c : W₁ᶜ = W₂ := by
        ext z
        refine ⟨fun hz => (hU.symm ▸ mem_univ z : z ∈ W₁ ∪ W₂).resolve_left hz,
          fun hz hz₁ => disjoint_left.mp hdis hz₁ hz⟩
      have hW₂c : W₂ᶜ = W₁ := by rw [← hW₁c, compl_compl]
      -- each point of `Z` other than `p` has a lift in `W₁` and one in `W₂`
      have hsides : ∀ z ∈ Z, z ≠ p → (∃ w ∈ W₁, ((φ ∘ ψ₂) ∘ ψ₃) w = z) ∧
          (∃ w ∈ W₂, ((φ ∘ ψ₂) ∘ ψ₃) w = z) := by
        have : T2Space T₃ := hT₃.2.1
        have hcm₂ : GM19.IsCutMap ψ₂ L₁ := GM19.IsCutting.isCutMap hcut₂
        have hcm₃ : GM19.IsCutMap ψ₃ L₂ := GM19.IsCutting.isCutMap hcut₃
        have hbdρ : ∀ w, ((φ ∘ ψ₂) ∘ ψ₃) w ∈ Z → w ∈ bd T₃ := fun w hw => hρ.2.2.2.2 hw
        -- the single lifts of `m₁` and `m₂` in `Y`
        obtain ⟨m₁', hm₁'⟩ := ncard_eq_one.mp (hφ1 m₁ (fun h => h.2 (Or.inr rfl)))
        obtain ⟨m₂', hm₂'⟩ := ncard_eq_one.mp (hφ1 m₂ (fun h => h.2 (Or.inl rfl)))
        have hq₁ : ∀ w, φ w = m₁ → w = m₁' := fun w hw => by
          have h : w ∈ φ ⁻¹' {m₁} := hw
          rw [hm₁'] at h
          exact h
        have hq₂ : ∀ w, φ w = m₂ → w = m₂' := fun w hw => by
          have h : w ∈ φ ⁻¹' {m₂} := hw
          rw [hm₂'] at h
          exact h
        have hφm₁ : φ m₁' = m₁ := by
          have h : m₁' ∈ φ ⁻¹' {m₁} := by rw [hm₁']; rfl
          exact h
        have hφm₂ : φ m₂' = m₂ := by
          have h : m₂' ∈ φ ⁻¹' {m₂} := by rw [hm₂']; rfl
          exact h
        have hm₁'M : m₁' ∈ φ ⁻¹' M := show φ m₁' ∈ M from hφm₁ ▸ hm₁M
        have hm₂'M : m₂' ∈ φ ⁻¹' M := show φ m₂' ∈ M from hφm₂ ▸ hm₂M
        have hm₁₂' : m₂' ≠ m₁' := fun h => hm₂m₁ (by rw [← hφm₂, ← hφm₁, h])
        obtain ⟨M₁, M₂, hM₁, hM₂, hMun, hMint⟩ := hMO.lines hm₂'M hm₁'M hm₁₂'
        have hM₁M : M₁ ⊆ φ ⁻¹' M := hMun ▸ subset_union_left
        have hM₂M : M₂ ⊆ φ ⁻¹' M := hMun ▸ subset_union_right
        -- a lift to `T₃` of a line of `Y` over `M`
        have hliftM : ∀ {Mi : Set Y}, IsLineWithEnds Mi m₂' m₁' → Mi ⊆ φ ⁻¹' M →
            ∃ (Mh : Set T₃) (e₂ e₁ : T₃), IsLineWithEnds Mh e₂ e₁ ∧ ψ₂ (ψ₃ e₂) = m₂' ∧
              ψ₂ (ψ₃ e₁) = m₁' ∧ BijOn (ψ₂ ∘ ψ₃) Mh Mi ∧
              (∀ z ∈ M, ∃ w ∈ Mh, ((φ ∘ ψ₂) ∘ ψ₃) w = z) := by
          intro Mi hMi hMiM
          have hoff₁ : Disjoint (Mi \ {m₂', m₁'}) L₁ := by
            refine disjoint_left.mpr fun w hw hwL => hw.2 (Or.inr (hq₁ w ?_))
            rcases hAB' (φ w) (hbL₁.mapsTo hwL) (hMB (hMiM hw.1)) with h | h
            · exact absurd (h ▸ hMiM hw.1) hpM
            · exact h
          obtain ⟨u₂, u₁, hu₂, hu₁, hMl, hMb, hMd⟩ :=
            exists_line_closure_lift_of_cutMap hcm₂ hL₁c hMi hoff₁
          have hoff₂ : Disjoint (closure (ψ₂ ⁻¹' (Mi \ {m₂', m₁'})) \ {u₂, u₁}) L₂ := by
            refine disjoint_left.mpr fun w hw hwL => ?_
            have hw' : w ∈ ψ₂ ⁻¹' (Mi \ {m₂', m₁'}) := hMd ▸ hw
            have hN' : φ (ψ₂ w) ∈ N := hbL₂.mapsTo hwL
            have hM' : φ (ψ₂ w) ∈ M := hMiM hw'.1
            exact hw'.2 (Or.inl (hq₂ (ψ₂ w) (hNM' _ hN' hM')))
          obtain ⟨e₂, e₁, he₂, he₁, hMhl, hMhb, -⟩ :=
            exists_line_closure_lift_of_cutMap hcm₃ hL₂c hMl hoff₂
          refine ⟨_, e₂, e₁, hMhl, by rw [he₂, hu₂], by rw [he₁, hu₁], hMb.comp hMhb, ?_⟩
          intro z hz
          have himg : φ '' Mi = M :=
            hM.eq_of_subset ((line_isPreconnected hMi).image _ hφ.1.continuousOn)
              (image_subset_iff.mpr hMiM) ⟨m₂', hMi.left_mem, hφm₂⟩ ⟨m₁', hMi.right_mem, hφm₁⟩
          obtain ⟨y, hy, rfl⟩ := himg.symm ▸ hz
          obtain ⟨w, hw, hwy⟩ := (hMb.comp hMhb).surjOn hy
          exact ⟨w, hw, by
            change φ ((ψ₂ ∘ ψ₃) w) = φ y
            rw [hwy]⟩
        obtain ⟨P₁, e₂, e₁, hP₁, he₂, he₁, hbP₁, hsP₁⟩ := hliftM hM₁ hM₁M
        obtain ⟨P₂, f₂, f₁, hP₂, hf₂, hf₁, hbP₂, hsP₂⟩ := hliftM hM₂ hM₂M
        -- a point with two lifts has no third one
        have htwo : ∀ x, (((φ ∘ ψ₂) ∘ ψ₃) ⁻¹' {x}).ncard = 2 → ∀ a b c : T₃,
            ((φ ∘ ψ₂) ∘ ψ₃) a = x → ((φ ∘ ψ₂) ∘ ψ₃) b = x → ((φ ∘ ψ₂) ∘ ψ₃) c = x → a ≠ b →
            c = a ∨ c = b := by
          intro x h2 a b c ha hb hc hab
          have he : (((φ ∘ ψ₂) ∘ ψ₃) ⁻¹' {x}).encard ≤ 2 := by
            rw [← (hρ.2.2.2.1 x).cast_ncard_eq, h2]
            rfl
          exact eq_or_of_encard_le_two he ha hb hc hab
        have hm₂A : m₂ ∉ A := fun h => by
          rcases hAB' m₂ h (hNB hm₂N) with h' | h'
          · exact hm₂p h'
          · exact hm₂m₁ h'
        have hc₂ : (((φ ∘ ψ₂) ∘ ψ₃) ⁻¹' {m₂}).ncard = 2 := by
          have h1 : m₂ ∉ M \ {m₂, m₁} := fun h => h.2 (Or.inl rfl)
          rw [hcount]
          simp only [h1, hm₂A, hm₂N, ↓reduceIte]
        have hc₁ : (((φ ∘ ψ₂) ∘ ψ₃) ⁻¹' {m₁}).ncard = 2 := by
          have h1 : m₁ ∉ M \ {m₂, m₁} := fun h => h.2 (Or.inr rfl)
          rw [hcount]
          simp only [h1, hm₁A, hm₁N, ↓reduceIte]
        -- the two points over `m₂`
        obtain ⟨yX, hyX, hyXe⟩ := hbX.surjOn hL₂.right_mem
        obtain ⟨yX', hyX', hyXe'⟩ := hbX'.surjOn hL₂.right_mem
        have hρyX : ((φ ∘ ψ₂) ∘ ψ₃) yX = m₂ := by
          change (φ ∘ ψ₂) (ψ₃ yX) = m₂
          rw [hyXe, hy₂]
        have hρyX' : ((φ ∘ ψ₂) ∘ ψ₃) yX' = m₂ := by
          change (φ ∘ ψ₂) (ψ₃ yX') = m₂
          rw [hyXe', hy₂]
        have hyXX : yX ≠ yX' := fun h => disjoint_left.mp hdX hyX (h ▸ hyX')
        have hρe₂ : ((φ ∘ ψ₂) ∘ ψ₃) e₂ = m₂ := by
          change φ (ψ₂ (ψ₃ e₂)) = m₂
          rw [he₂, hφm₂]
        have hρf₂ : ((φ ∘ ψ₂) ∘ ψ₃) f₂ = m₂ := by
          change φ (ψ₂ (ψ₃ f₂)) = m₂
          rw [hf₂, hφm₂]
        -- the lines over `M` lie in the boundary
        have hPbd : ∀ {P : Set T₃} {Mi : Set Y}, BijOn (ψ₂ ∘ ψ₃) P Mi → Mi ⊆ φ ⁻¹' M →
            P ⊆ bd T₃ := fun hb hMi x hx =>
          hbdρ x (hBZ (hMB (hMi (hb.mapsTo hx))))
        -- the two lines over `M` leave `m₂` at different points
        have hthree : ∀ {R : Set T₃}, IsLine R → BijOn ψ₃ R L₂ → e₂ ∈ R → e₂ = f₂ → False := by
          intro R hRl hbR heR hef
          obtain ⟨r₀, hr₀, r₁, hr₁, hr₀e, hr₁e, hRe⟩ :=
            isLineWithEnds_of_bijOn hcut₃.1 (isLine_isCompact hRl) hL₂ hbR
          have he₂r : e₂ = r₁ := by
            refine hbR.injOn heR hr₁ (hbL₂.injOn (hbR.mapsTo heR) hL₂.right_mem ?_ ▸ hr₁e.symm)
            change φ (ψ₂ (ψ₃ e₂)) = (φ ∘ ψ₂) y₂
            rw [he₂, hφm₂, hy₂]
          subst he₂r
          have hRbd : R ⊆ bd T₃ := fun x hx => hbdρ x (hBZ (hNB (hbL₂.mapsTo (hbR.mapsTo hx))))
          have hJ : IsOArc (connectedComponentIn (bd T₃) e₂) :=
            (cuff_statement.{w} T₃ hT₃).2.2 _ ⟨e₂, hRbd heR, rfl⟩
          have hsub : ∀ {P : Set T₃} {u v : T₃}, IsLineWithEnds P u v → P ⊆ bd T₃ → e₂ ∈ P →
              P ⊆ connectedComponentIn (bd T₃) e₂ := fun hP hPb he =>
            (line_isPreconnected hP).subset_connectedComponentIn he hPb
          have hP₂' : IsLineWithEnds P₂ e₂ f₁ := hef ▸ hP₂
          have hR' : IsLineWithEnds R e₂ r₀ := hRe.symm
          -- a point of a line over `M` that lies over `m₂'` or over `m₁'` is an end
          have hend : ∀ {P : Set T₃} {Mi : Set Y} {a b : T₃}, BijOn (ψ₂ ∘ ψ₃) P Mi →
              a ∈ P → b ∈ P → ψ₂ (ψ₃ a) = ψ₂ (ψ₃ b) → a = b := fun hb ha hb' h =>
            hb.injOn ha hb' h
          have hoffR : ∀ {P : Set T₃} {Mi : Set Y} {e : T₃}, BijOn (ψ₂ ∘ ψ₃) P Mi →
              Mi ⊆ φ ⁻¹' M → e ∈ P → ψ₂ (ψ₃ e) = m₂' → ∀ x ∈ P, x ∈ R → x = e := by
            intro P Mi e hb hMi he hee x hxP hxR
            have hN' : φ (ψ₂ (ψ₃ x)) ∈ N := hbL₂.mapsTo (hbR.mapsTo hxR)
            have hM' : φ (ψ₂ (ψ₃ x)) ∈ M := hMi (hb.mapsTo hxP)
            exact hb.injOn hxP he ((hq₂ _ (hNM' _ hN' hM')).trans hee.symm)
          refine false_of_three_lines hJ hP₁ hP₂' hR' (hsub hP₁ (hPbd hbP₁ hM₁M) hP₁.left_mem)
            (hsub hP₂' (hPbd hbP₂ hM₂M) hP₂'.left_mem) (hsub hR' hRbd hR'.left_mem) ?_
            (hoffR hbP₁ hM₁M hP₁.left_mem he₂) (hoffR hbP₂ hM₂M hP₂'.left_mem (hef ▸ hf₂))
          intro x hx₁ hx₂
          have hx : ψ₂ (ψ₃ x) ∈ M₁ ∩ M₂ := ⟨hbP₁.mapsTo hx₁, hbP₂.mapsTo hx₂⟩
          rw [hMint] at hx
          rcases hx with hx | hx
          · exact Or.inl (hend hbP₁ hx₁ hP₁.left_mem (hx.trans he₂.symm))
          · exact Or.inr ⟨hend hbP₁ hx₁ hP₁.right_mem (hx.trans he₁.symm),
              hend hbP₂ hx₂ hP₂.right_mem (hx.trans hf₁.symm)⟩
        -- so one line over `M` lies in `W₁` and the other in `W₂`
        have hMsides : ∃ (Pa Pb : Set T₃) (ga gb : T₃), Pa ⊆ W₁ ∧ Pb ⊆ W₂ ∧ ga ∈ Pa ∧ gb ∈ Pb ∧
            ((φ ∘ ψ₂) ∘ ψ₃) ga = m₁ ∧ ((φ ∘ ψ₂) ∘ ψ₃) gb = m₁ ∧
            (∀ z ∈ M, ∃ w ∈ Pa, ((φ ∘ ψ₂) ∘ ψ₃) w = z) ∧
            (∀ z ∈ M, ∃ w ∈ Pb, ((φ ∘ ψ₂) ∘ ψ₃) w = z) := by
          have hρe₁ : ((φ ∘ ψ₂) ∘ ψ₃) e₁ = m₁ := by
            change φ (ψ₂ (ψ₃ e₁)) = m₁
            rw [he₁, hφm₁]
          have hρf₁ : ((φ ∘ ψ₂) ∘ ψ₃) f₁ = m₁ := by
            change φ (ψ₂ (ψ₃ f₁)) = m₁
            rw [hf₁, hφm₁]
          have hin : ∀ {P : Set T₃} {u v : T₃} {W : Set T₃}, IsLineWithEnds P u v → IsClopen W →
              u ∈ W → P ⊆ W := fun hP hW hu =>
            (line_isPreconnected hP).subset_isClopen hW ⟨_, hP.left_mem, hu⟩
          rcases htwo m₂ hc₂ yX yX' e₂ hρyX hρyX' hρe₂ hyXX with h | h
          · have hf : f₂ = yX' := by
              rcases htwo m₂ hc₂ yX yX' f₂ hρyX hρyX' hρf₂ hyXX with h' | h'
              · exact absurd (h.trans h'.symm) fun he => hthree ⟨eX⟩ hbX (h ▸ hyX) he
              · exact h'
            exact ⟨P₁, P₂, e₁, f₁, hin hP₁ hW₁ (h ▸ hXW hyX), hin hP₂ hW₂ (hf ▸ hX'W hyX'),
              hP₁.right_mem, hP₂.right_mem, hρe₁, hρf₁, hsP₁, hsP₂⟩
          · have hf : f₂ = yX := by
              rcases htwo m₂ hc₂ yX yX' f₂ hρyX hρyX' hρf₂ hyXX with h' | h'
              · exact h'
              · exact absurd (h.trans h'.symm) fun he => hthree ⟨eX'⟩ hbX' (h ▸ hyX') he
            exact ⟨P₂, P₁, f₁, e₁, hin hP₂ hW₁ (hf ▸ hXW hyX), hin hP₁ hW₂ (h ▸ hX'W hyX'),
              hP₂.right_mem, hP₁.right_mem, hρf₁, hρe₁, hsP₂, hsP₁⟩
        obtain ⟨Pa, Pb, ga, gb, hPa, hPb, hga, hgb, hρga, hρgb, hsPa, hsPb⟩ := hMsides
        -- a lift to `T₃` of a line of `T₂` over `A`
        have hliftA : ∀ {Xa : Set T₂}, IsLine Xa → BijOn ψ₂ Xa L₁ →
            ∃ (Ah : Set T₃) (c : T₃), IsPreconnected Ah ∧ c ∈ Ah ∧ ψ₃ c ∈ Xa ∧
              ((φ ∘ ψ₂) ∘ ψ₃) c = m₁ ∧ (∀ z ∈ A, ∃ w ∈ Ah, ((φ ∘ ψ₂) ∘ ψ₃) w = z) := by
          intro Xa hXa hbXa
          obtain ⟨a₀, ha₀, a₁, ha₁, ha₀e, ha₁e, hXl⟩ :=
            isLineWithEnds_of_bijOn hcut₂.1 (isLine_isCompact hXa) hL₁ hbXa
          have hoff : Disjoint (Xa \ {a₀, a₁}) L₂ := by
            refine disjoint_left.mpr fun w hw hwL => ?_
            have hN' : φ (ψ₂ w) ∈ N := hbL₂.mapsTo hwL
            rcases hAB' _ (hbL₁.mapsTo (hbXa.mapsTo hw.1)) (hNB hN') with h | h
            · have h1 : ψ₂ w = x₁ := hbL₁.injOn (hbXa.mapsTo hw.1) hL₁.left_mem (h.trans hx₁.symm)
              exact hw.2 (Or.inl (hbXa.injOn hw.1 ha₀ (h1.trans ha₀e.symm)))
            · exact hm₁N (h ▸ hN')
          obtain ⟨c₀, c₁, -, hc₁e, hAl, hAb, -⟩ :=
            exists_line_closure_lift_of_cutMap hcm₃ hL₂c hXl hoff
          refine ⟨_, c₁, line_isPreconnected hAl, hAl.right_mem, hc₁e ▸ ha₁, ?_, ?_⟩
          · change φ (ψ₂ (ψ₃ c₁)) = m₁
            rw [hc₁e, ha₁e, hy₁]
          · intro z hz
            obtain ⟨w, hw, rfl⟩ := hbL₁.surjOn hz
            obtain ⟨w', hw', rfl⟩ := hbXa.surjOn hw
            obtain ⟨w'', hw'', rfl⟩ := hAb.surjOn hw'
            exact ⟨w'', hw'', rfl⟩
        obtain ⟨Ah, c, hAh, hc, hcX, hρc, hsAh⟩ := hliftA hX₁l hb₁
        obtain ⟨Ah', c', hAh', hc', hcX', hρc', hsAh'⟩ := hliftA hX₁'l hb₁'
        have hcc : c ≠ c' := fun h => disjoint_left.mp hd₁ hcX (h ▸ hcX')
        have hgg : ga ≠ gb := fun h => disjoint_left.mp hdis (hPa hga) (h ▸ hPb hgb)
        have hAsides : (∀ z ∈ A, ∃ w ∈ W₁, ((φ ∘ ψ₂) ∘ ψ₃) w = z) ∧
            (∀ z ∈ A, ∃ w ∈ W₂, ((φ ∘ ψ₂) ∘ ψ₃) w = z) := by
          have hin : ∀ {P : Set T₃} {u : T₃} {W : Set T₃}, IsPreconnected P → IsClopen W →
              u ∈ P → u ∈ W → ∀ z ∈ A, (∃ w ∈ P, ((φ ∘ ψ₂) ∘ ψ₃) w = z) →
                ∃ w ∈ W, ((φ ∘ ψ₂) ∘ ψ₃) w = z := fun hP hW hu huW z _ ⟨w, hw, hwz⟩ =>
            ⟨w, hP.subset_isClopen hW ⟨_, hu, huW⟩ hw, hwz⟩
          rcases htwo m₁ hc₁ ga gb c hρga hρgb hρc hgg with h | h
          · have h' : c' = gb := by
              rcases htwo m₁ hc₁ ga gb c' hρga hρgb hρc' hgg with h' | h'
              · exact absurd (h.trans h'.symm) hcc
              · exact h'
            exact ⟨fun z hz => hin hAh hW₁ hc (h ▸ hPa hga) z hz (hsAh z hz),
              fun z hz => hin hAh' hW₂ hc' (h' ▸ hPb hgb) z hz (hsAh' z hz)⟩
          · have h' : c' = ga := by
              rcases htwo m₁ hc₁ ga gb c' hρga hρgb hρc' hgg with h' | h'
              · exact h'
              · exact absurd (h.trans h'.symm) hcc
            exact ⟨fun z hz => hin hAh' hW₁ hc' (h' ▸ hPa hga) z hz (hsAh' z hz),
              fun z hz => hin hAh hW₂ hc (h ▸ hPb hgb) z hz (hsAh z hz)⟩
        intro z hz _
        rw [← hZeq] at hz
        rcases hz with (hzM | hzA) | hzN
        · obtain ⟨w, hw, hwz⟩ := hsPa z hzM
          obtain ⟨w', hw', hwz'⟩ := hsPb z hzM
          exact ⟨⟨w, hPa hw, hwz⟩, ⟨w', hPb hw', hwz'⟩⟩
        · exact ⟨hAsides.1 z hzA, hAsides.2 z hzA⟩
        · obtain ⟨w, hw, rfl⟩ := hbL₂.surjOn hzN
          obtain ⟨w₁, hw₁, hw₁e⟩ := hbX.surjOn hw
          obtain ⟨w₂, hw₂, hw₂e⟩ := hbX'.surjOn hw
          exact ⟨⟨w₁, hXW hw₁, by change (φ ∘ ψ₂) (ψ₃ w₁) = _; rw [hw₁e]⟩,
            ⟨w₂, hX'W hw₂, by change (φ ∘ ψ₂) (ψ₃ w₂) = _; rw [hw₂e]⟩⟩
      obtain ⟨w, hwX, hw⟩ := hbX.surjOn hL₂.left_mem
      obtain ⟨w', hwX', hw'⟩ := hbX'.surjOn hL₂.left_mem
      have hwp : w ∈ ((φ ∘ ψ₂) ∘ ψ₃) ⁻¹' {p} := by
        change φ (ψ₂ (ψ₃ w)) = p
        rw [hw]
        exact hx₂
      have hwp' : w' ∈ ((φ ∘ ψ₂) ∘ ψ₃) ⁻¹' {p} := by
        change φ (ψ₂ (ψ₃ w')) = p
        rw [hw']
        exact hx₂
      rcases hK₁ with rfl | rfl
      · refine ⟨K₁, hW₁, hdisc, hW₁c ▸ hc₂, ⟨w, hXW hwX, hwp⟩, ⟨w', ?_, hwp'⟩, ?_⟩
        · rw [hW₁c]
          exact hX'W hwX'
        · intro z hz hzp
          rw [hW₁c]
          exact hsides z hz hzp
      · refine ⟨K₁, hW₂, hdisc, hW₂c ▸ hc₁, ⟨w', hX'W hwX', hwp'⟩, ⟨w, ?_, hwp⟩, ?_⟩
        · rw [hW₂c]
          exact hXW hwX
        · intro z hz hzp
          rw [hW₂c]
          exact (hsides z hz hzp).symm
  · left
    obtain ⟨hT₃c, a'', b'', c'', ⟨eT₂'⟩, ⟨eT₃⟩⟩ := hdist₃ hc
    rw [← hgT₂, surfaceComplexity_eq_connected, surfaceComplexity_eq_connected,
      connectedSurfaceComplexity_eq ⟨eT₃⟩, connectedSurfaceComplexity_eq ⟨eT₂'⟩]
    omega

end GraphMinor.GM08
