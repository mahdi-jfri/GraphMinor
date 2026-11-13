module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM19.CutMap
public import GraphMinor.GM07.CutStages
import GraphMinor.GM08.Section18X2Tools
import GraphMinor.GM08.Section18SurroundSides
import GraphMinor.GM08.Section18X3Cut
import GraphMinor.GM08.Section18X1Cut
import GraphMinor.GM08.Section18DiscPiece
import GraphMinor.GM08.Section18CutCount
import GraphMinor.GM08.Section6
import GraphMinor.GM12.Section3MeetingLoopSchismatic
import GraphMinor.GM07.Section8
import GraphMinor.Surface.Classification
import GraphMinor.Surface.Cuffs

/-!
# The disc case of the cut along two circles that meet at one point

Let `A₁, A₂` be circles that meet only at `u`, miss the boundary, and surround
different cuffs `C₁, C₂`. Cut along `A₁ ∪ A₂`. Suppose the cut surface splits
into three open and closed connected pieces: `W` around `C₁`, a closed disc
`D`, and `K`. We show that `K` is a cylinder.

The circle `A₂` has two sides: the cut along `A₂` (`exists_surround_sides`)
gives a cylinder side `Y₂ = ψ'(W')`, which holds `C₂`, and a far side `O₂`.
Each piece maps into one side (`image_subset_or_of_clopen`).

* `W` holds a lift of `C₁`, which is off `Y₂`. So `W` maps into `O₂`.
* The boundary of `D` is one circle, and it holds a lift of `u`. So `D` holds
  no lift of `C₂`, and `K` holds them all. So `K` maps into `Y₂`.
* If `D` also mapped into `Y₂`, then `W` would cover `O₂ \ Y₂`, whose closure
  holds `A₂`. But `W` covers only `u` on `A₂`. So `D` maps into `O₂`.
* So each point of `A₂ \ {u}` has a lift in `D` and one in `K`, and it has
  only two. Points of `A₁ \ {u}` have no lift in `K` (they are off `Y₂`, since
  `A₁` is not planar in `Σ + Ĉ₂`), and one lift in `W`. The point `u` has
  three lifts off `W`, and both `D` and `K` hold one. So `D` or `K` holds
  exactly one lift of `u`, and the cut map is one to one on that piece.
* If it is one to one on `D`, the boundary of the disc gives a planar circle in
  `A₁ ∪ A₂`, which is `A₁` or `A₂`. Neither is planar.
* If it is one to one on `K`, then `K` is a cylinder
  (`nonempty_cylinder_of_cut_piece`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

variable {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]

/-- The boundary of an open closed disc `D` in a surface is `D ∩ bd T`, and it
is connected. -/
theorem isConnected_inter_bd_of_disc {D : Set T} (hDo : IsOpen D) (hD : IsClosedDisc D) :
    IsConnected (D ∩ bd T) := by
  have hdiscBd : discBd D = D ∩ bd T := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      exact ⟨z'.2, (mem_bd_sub hDo).mp hz'⟩
    · rintro ⟨hzD, hzb⟩
      exact ⟨⟨z, hzD⟩, (mem_bd_sub hDo).mpr hzb, rfl⟩
  rw [← hdiscBd]
  exact GM07.IsOArc.isConnected hD.isOArc_discBd

/-- A point with exactly two lifts, one in `P` and one outside `P`, has only one
lift in `P`. -/
theorem subsingleton_of_two {θ : T → S} {P : Set T} {z : S} (hfin : (θ ⁻¹' {z}).Finite)
    (h2 : (θ ⁻¹' {z}).ncard = 2) {w : T} (hw : θ w = z) (hwP : w ∉ P) :
    (θ ⁻¹' {z} ∩ P).Subsingleton := by
  rintro a ⟨ha, haP⟩ b ⟨hb, hbP⟩
  by_contra hab
  have hsub : ({a, b, w} : Set T) ⊆ θ ⁻¹' {z} := by
    rintro x (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hw
  have h3 : ({a, b, w} : Set T).ncard = 3 := by
    rw [ncard_insert_of_notMem, ncard_pair]
    · exact fun h => hwP (h ▸ hbP)
    · rintro (h | h)
      · exact hab h
      · exact hwP (h ▸ haP)
  have := ncard_le_ncard hsub hfin
  omega

/-- **The disc case of the `X₂` cut.** -/
theorem nonempty_cylinder_of_x2_disc [ConnectedSpace S] (hS : IsSurface S)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (h3 : 3 ≤ surfaceComplexity S)
    {A₁ A₂ C₁ C₂ : Set S} {u : S} (hA₁ : IsOArc A₁) (hA₂ : IsOArc A₂) (h12 : A₁ ∩ A₂ = {u})
    (hoff : Disjoint (A₁ ∪ A₂) (bd S)) (hsur₁ : GM07.SurroundsCuff A₁ C₁)
    (hsur₂ : GM07.SurroundsCuff A₂ C₂) (hC : C₁ ≠ C₂) (hT : IsSurface T) {θ : T → S}
    (hθ : GM19.IsCutMap θ (A₁ ∪ A₂)) (hcutF : GM07.IsCutAlongSet (A₁ ∪ A₂) θ)
    {W D K : Set T} (hW : IsClopen W) (hD : IsClopen D) (hK : IsClopen K) [ConnectedSpace W]
    [ConnectedSpace D] [ConnectedSpace K] (hDK : Disjoint D K) (hDKW : D ∪ K = Wᶜ)
    (hDdisc : IsClosedDisc D) (hWA₂ : ∀ z ∈ W, θ z ∈ A₂ → θ z = u)
    (hWC₁ : ∃ z ∈ W, θ z ∈ C₁) (hWbd : ∀ z ∈ W, θ z ∈ bd S → θ z ∈ C₁)
    (hWA₁ : ∀ a ∈ A₁, ∃ z ∈ W, θ z = a)
    (hc₂ : ∀ z ∈ A₁ ∪ A₂, z ≠ u → (θ ⁻¹' {z}).ncard = 2)
    (hu₃ : (θ ⁻¹' {u} ∩ Wᶜ).ncard = 3) (hDu : (D ∩ θ ⁻¹' {u}).Nonempty)
    (hKu : (K ∩ θ ⁻¹' {u}).Nonempty) :
    Nonempty (K ≃ₜ SurfaceModel 0 0 2) := by
  have : T2Space S := hS.2.1
  have : CompactSpace T := hT.1
  have : T2Space T := hT.2.1
  have hoff₁ : Disjoint A₁ (bd S) := hoff.mono_left subset_union_left
  have hoff₂ : Disjoint A₂ (bd S) := hoff.mono_left subset_union_right
  have huu : u ∈ A₁ ∩ A₂ := by rw [h12]; rfl
  have hA₁c : IsClosed A₁ := hA₁.isCompact.isClosed
  have hA₂c : IsClosed A₂ := hA₂.isCompact.isClosed
  have hFc : IsClosed (A₁ ∪ A₂) := hA₁c.union hA₂c
  have hθc : Continuous θ := hθ.1
  have hbdT : θ ⁻¹' (bd S ∪ (A₁ ∪ A₂)) = bd T := hcutF.preimage_bd
  have hCbd : ∀ {C : Set S}, C ∈ cuffs S → C ⊆ bd S := fun hC => by
    rw [← sUnion_cuffs]
    exact subset_sUnion_of_mem hC
  have hC₁₂ : Disjoint C₁ C₂ := disjoint_of_mem_cuffs hsur₁.1 hsur₂.1 hC
  -- the two sides of `A₂`
  obtain ⟨T', t', ψ', W', hT', hcut', hs', -⟩ :=
    exists_surround_sides hS hncyl h3 hA₂ hoff₂ hsur₂
  let := t'
  have : CompactSpace T' := hT'.1
  have : T2Space T' := hT'.2.1
  set Y₂ := ψ' '' W'
  set O₂ := ψ' '' W'ᶜ
  have hY₂c : IsClosed Y₂ := (hs'.isClopen.isClosed.isCompact.image hcut'.1).isClosed
  have hO₂c : IsClosed O₂ := (hs'.isClopen.compl.isClosed.isCompact.image hcut'.1).isClosed
  have hcov : Y₂ ∪ O₂ = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨t, rfl⟩ := hcut'.2.1 x
    by_cases ht : t ∈ W'
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨t, ht, rfl⟩
  have hint : Y₂ ∩ O₂ ⊆ A₂ := by
    rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    by_contra h
    have : b = a := hcut'.2.2.1 (show ψ' b ∈ A₂ᶜ by rw [hab]; exact h) h hab
    exact hb (this ▸ ha)
  have hside : ∀ Q : Set T, IsClopen Q → ConnectedSpace Q → θ '' Q ⊆ Y₂ ∨ θ '' Q ⊆ O₂ :=
    fun Q hQ _ => image_subset_or_of_clopen hT hθc hY₂c hO₂c hcov
      (fun x hx => Or.inr (hint hx)) hQ (fun z _ hz => hθ.2.2.2.2 hz)
  -- `A₁ \ {u}` is off `Y₂`
  have hA₁Y₂ : ∀ a ∈ A₁, a ≠ u → a ∉ Y₂ := by
    have hB : IsPreconnected (A₁ \ {u}) := isPreconnected_oArc_sdiff_singleton hA₁ u
    have hBA : Disjoint (A₁ \ {u}) A₂ := disjoint_left.mpr fun z hz hzA =>
      hz.2 (by have h : z ∈ A₁ ∩ A₂ := ⟨hz.1, hzA⟩; rw [h12] at h; exact h)
    have hsub : A₁ ⊆ A₂ ∪ closure (A₁ \ {u}) := fun z hz => by
      by_cases hzu : z = u
      · exact Or.inl (hzu ▸ huu.2)
      · exact Or.inr (subset_closure ⟨hz, hzu⟩)
    have hfar := preimage_subset_compl_of_planar hS hT' hncyl hcut' hs' hsur₂.1 hA₁ hsur₁
      (Ne.symm hC) hB hBA hsub
    rintro a ha hau ⟨w, hw, rfl⟩
    exact hfar ⟨ha, hau⟩ hw
  have hC₂O₂ : ∀ c ∈ C₂, c ∉ O₂ := by
    rintro c hc ⟨w, hw, rfl⟩
    exact hw (hs'.cuff_sub hc)
  have hC₁Y₂ : ∀ c ∈ C₁, c ∉ Y₂ := by
    rintro c hc ⟨w, hw, rfl⟩
    exact disjoint_left.mp hC₁₂ hc (hs'.bd_sub w hw (hCbd hsur₁.1 hc))
  -- `W` maps into `O₂`
  have hWO : θ '' W ⊆ O₂ := by
    refine (hside W hW inferInstance).resolve_left fun h => ?_
    obtain ⟨z, hzW, hzC⟩ := hWC₁
    exact hC₁Y₂ _ hzC (h ⟨z, hzW, rfl⟩)
  -- `D` holds no lift of `C₂`
  have hDC₂ : ∀ y ∈ D, θ y ∉ C₂ := by
    intro y hyD hyC
    obtain ⟨q, hqD, hq⟩ := hDu
    have hqb : q ∈ bd T := hθ.2.2.2.2 (show θ q ∈ A₁ ∪ A₂ by rw [hq]; exact Or.inl huu.1)
    have hyb : y ∈ bd T := by rw [← hbdT]; exact Or.inl (hCbd hsur₂.1 hyC)
    have hconn := (isConnected_inter_bd_of_disc hD.isOpen hDdisc).isPreconnected.image θ
      hθc.continuousOn
    have hfinC := (cuff_statement S hS).2.1
    set G₂ : Set S := (A₁ ∪ A₂) ∪ ⋃₀ (cuffs S \ {C₂})
    have hG₂c : IsClosed G₂ := hFc.union ((hfinC.sdiff).isClosed_sUnion fun C hC =>
      ((cuff_statement S hS).2.2 C hC.1).isCompact.isClosed)
    have hC₂c : IsClosed C₂ := ((cuff_statement S hS).2.2 C₂ hsur₂.1).isCompact.isClosed
    have hsub : θ '' (D ∩ bd T) ⊆ C₂ ∪ G₂ := by
      rintro _ ⟨z, hz, rfl⟩
      have hz2 : z ∈ θ ⁻¹' (bd S ∪ (A₁ ∪ A₂)) := by rw [hbdT]; exact hz.2
      rcases hz2 with hzb | hzF
      · rw [← sUnion_cuffs] at hzb
        obtain ⟨C, hC, hzC⟩ := hzb
        by_cases hCC : C = C₂
        · exact Or.inl (hCC ▸ hzC)
        · exact Or.inr (Or.inr ⟨C, ⟨hC, hCC⟩, hzC⟩)
      · exact Or.inr (Or.inl hzF)
    have hdis : C₂ ∩ G₂ = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro z ⟨hzC, hzF | ⟨C, ⟨hC', hCC⟩, hzC'⟩⟩
      · exact disjoint_left.mp hoff hzF (hCbd hsur₂.1 hzC)
      · exact disjoint_left.mp (disjoint_of_mem_cuffs hsur₂.1 hC' (Ne.symm hCC)) hzC hzC'
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hconn) C₂ G₂ hC₂c hG₂c hsub
        (by rw [hdis, inter_empty]) with h | h
    · have : u ∈ C₂ := hq ▸ h ⟨q, ⟨hqD, hqb⟩, rfl⟩
      exact disjoint_left.mp hoff (Or.inl huu.1) (hCbd hsur₂.1 this)
    · have : θ y ∈ G₂ := h ⟨y, ⟨hyD, hyb⟩, rfl⟩
      exact (eq_empty_iff_forall_notMem.mp hdis) _ ⟨hyC, this⟩
  -- every lift of `C₂` is in `K`
  have hCK : θ ⁻¹' C₂ ⊆ K := by
    intro y hy
    have hyW : y ∉ W := fun hyW =>
      disjoint_left.mp hC₁₂ (hWbd y hyW (hCbd hsur₂.1 hy)) hy
    have hy' : y ∈ D ∪ K := hDKW ▸ hyW
    exact hy'.resolve_left fun hyD => hDC₂ y hyD hy
  -- `K` maps into `Y₂`
  have hKY : θ '' K ⊆ Y₂ := by
    refine (hside K hK inferInstance).resolve_right fun h => ?_
    obtain ⟨c, hc⟩ := (GM07.IsOArc.isConnected ((cuff_statement S hS).2.2 C₂ hsur₂.1)).nonempty
    obtain ⟨y, rfl⟩ := hθ.2.1 c
    exact hC₂O₂ _ hc (h ⟨y, hCK hc, rfl⟩)
  -- every point of `A₂` is a limit of points that only one side covers
  have hclO : ∀ z ∈ A₂, z ∈ closure (O₂ \ Y₂) := by
    intro z hz
    obtain ⟨-, Y', -, -, hY'W, -, hbY'⟩ := hs'.lifts
    obtain ⟨y', hy', rfl⟩ := hbY'.surjOn hz
    have := hs'.connected_compl
    have h := mem_closure_image_sdiff hT' (GM19.IsCutting.isCutMap hcut') hs'.isClopen.compl
      (hY'W hy')
    rwa [compl_compl] at h
  have hclY : ∀ z ∈ A₂, z ∈ closure (Y₂ \ O₂) := by
    intro z hz
    obtain ⟨a, b, hab, hpair⟩ := ncard_eq_two.mp (hcut'.2.2.2.1 z hz)
    have ha : ψ' a = z := (show a ∈ ψ' ⁻¹' {z} from hpair ▸ Or.inl rfl)
    have hb : ψ' b = z := (show b ∈ ψ' ⁻¹' {z} from hpair ▸ Or.inr rfl)
    have : ∃ y ∈ W', ψ' y = z := by
      by_contra hno
      push_neg at hno
      have haW : a ∈ W'ᶜ := fun h => hno a h ha
      have hbW : b ∈ W'ᶜ := fun h => hno b h hb
      exact hab (hs'.injOn_compl haW hbW (ha.trans hb.symm))
    obtain ⟨y, hyW, rfl⟩ := this
    have := hs'.connected
    exact mem_closure_image_sdiff hT' (GM19.IsCutting.isCutMap hcut') hs'.isClopen hyW
  have hlift : ∀ x : T, x ∈ W ∨ x ∈ D ∨ x ∈ K := fun x => by
    by_cases hx : x ∈ W
    · exact Or.inl hx
    · exact Or.inr (hDKW ▸ hx : x ∈ D ∪ K)
  have hWimc : IsClosed (θ '' W) := (hW.isClosed.isCompact.image hθc).isClosed
  obtain ⟨z₀, hz₀, hz₀u⟩ : ∃ z ∈ A₂, z ≠ u := by
    obtain ⟨a, b, -, ha, hb, -, hab, -, -⟩ := hA₂.exists_three
    by_cases hau : a = u
    · exact ⟨b, hb, fun h => hab (hau.trans h.symm)⟩
    · exact ⟨a, ha, hau⟩
  -- `D` maps into `O₂`
  have hDO : θ '' D ⊆ O₂ := by
    refine (hside D hD inferInstance).resolve_left fun hDY => ?_
    have hsub : O₂ \ Y₂ ⊆ θ '' W := by
      rintro s ⟨-, hsY⟩
      obtain ⟨y, rfl⟩ := hθ.2.1 s
      rcases hlift y with h | h | h
      · exact ⟨y, h, rfl⟩
      · exact absurd (hDY ⟨y, h, rfl⟩) hsY
      · exact absurd (hKY ⟨y, h, rfl⟩) hsY
    obtain ⟨w, hw, hwz⟩ := closure_minimal hsub hWimc (hclO z₀ hz₀)
    exact hz₀u (hwz ▸ hWA₂ w hw (hwz ▸ hz₀))
  -- each point of `A₂ \ {u}` has a lift in `D` and one in `K`
  have hzK : ∀ z ∈ A₂, ∃ k ∈ K, θ k = z := by
    intro z hz
    have hsub : Y₂ \ O₂ ⊆ θ '' K := by
      rintro s ⟨-, hsO⟩
      obtain ⟨y, rfl⟩ := hθ.2.1 s
      rcases hlift y with h | h | h
      · exact absurd (hWO ⟨y, h, rfl⟩) hsO
      · exact absurd (hDO ⟨y, h, rfl⟩) hsO
      · exact ⟨y, h, rfl⟩
    exact closure_minimal hsub (hK.isClosed.isCompact.image hθc).isClosed (hclY z hz)
  have hzD : ∀ z ∈ A₂, z ≠ u → ∃ d ∈ D, θ d = z := by
    intro z hz hzu
    have hsub : O₂ \ Y₂ ⊆ θ '' W ∪ θ '' D := by
      rintro s ⟨-, hsY⟩
      obtain ⟨y, rfl⟩ := hθ.2.1 s
      rcases hlift y with h | h | h
      · exact Or.inl ⟨y, h, rfl⟩
      · exact Or.inr ⟨y, h, rfl⟩
      · exact absurd (hKY ⟨y, h, rfl⟩) hsY
    rcases closure_minimal hsub (hWimc.union (hD.isClosed.isCompact.image hθc).isClosed)
        (hclO z hz) with ⟨w, hw, hwz⟩ | h
    · exact absurd (hwz ▸ hWA₂ w hw (hwz ▸ hz)) (fun h => hzu (hwz ▸ h))
    · exact h
  -- the lifts of `u` off `W`
  have hfinu : (θ ⁻¹' {u}).Finite := hθ.2.2.2.1 u
  have hsplit : θ ⁻¹' {u} ∩ Wᶜ = (θ ⁻¹' {u} ∩ D) ∪ (θ ⁻¹' {u} ∩ K) := by
    rw [← inter_union_distrib_left, hDKW]
  have hcount : (θ ⁻¹' {u} ∩ D).ncard + (θ ⁻¹' {u} ∩ K).ncard = 3 := by
    rw [← hu₃, hsplit, ncard_union_eq (disjoint_of_subset_left inter_subset_right
      (disjoint_of_subset_right inter_subset_right hDK)) (hfinu.subset inter_subset_left)
      (hfinu.subset inter_subset_left)]
  have hD1 : 1 ≤ (θ ⁻¹' {u} ∩ D).ncard := by
    obtain ⟨q, hqD, hq⟩ := hDu
    exact Nat.one_le_iff_ne_zero.mpr (ncard_ne_zero_of_mem ⟨hq, hqD⟩ (hfinu.subset inter_subset_left))
  have hK1 : 1 ≤ (θ ⁻¹' {u} ∩ K).ncard := by
    obtain ⟨q, hqK, hq⟩ := hKu
    exact Nat.one_le_iff_ne_zero.mpr (ncard_ne_zero_of_mem ⟨hq, hqK⟩ (hfinu.subset inter_subset_left))
  -- one to one on a piece that holds one lift of `u`
  have hinj : ∀ P : Set T, (∀ z ∈ A₂, z ≠ u → ∃ y ∉ P, θ y = z) →
      (∀ a ∈ A₁, a ≠ u → ∃ y ∉ P, θ y = a) → (θ ⁻¹' {u} ∩ P).ncard ≤ 1 → InjOn θ P := by
    intro P hP₂ hP₁ hPu a ha b hb hab
    set x := θ a
    have hsub : (θ ⁻¹' {x} ∩ P).Subsingleton := by
      by_cases hxF : x ∈ A₁ ∪ A₂
      · by_cases hxu : x = u
        · rw [hxu]
          have hf : (θ ⁻¹' {u} ∩ P).Finite := hfinu.subset inter_subset_left
          have := hf.to_subtype
          exact ncard_le_one_iff_subsingleton.mp hPu
        · have hfin : (θ ⁻¹' {x}).Finite := hθ.2.2.2.1 x
          rcases hxF with hx | hx
          · obtain ⟨y, hyP, hy⟩ := hP₁ x hx hxu
            exact subsingleton_of_two hfin (hc₂ x (Or.inl hx) hxu) hy hyP
          · obtain ⟨y, hyP, hy⟩ := hP₂ x hx hxu
            exact subsingleton_of_two hfin (hc₂ x (Or.inr hx) hxu) hy hyP
      · rintro c ⟨hc, -⟩ d ⟨hd, -⟩
        exact hθ.2.2.1 (show θ c ∉ A₁ ∪ A₂ by rw [hc]; exact hxF)
          (show θ d ∉ A₁ ∪ A₂ by rw [hd]; exact hxF) (hc.trans hd.symm)
    exact hsub ⟨rfl, ha⟩ ⟨hab.symm, hb⟩
  rcases (show (θ ⁻¹' {u} ∩ K).ncard ≤ 1 ∨ (θ ⁻¹' {u} ∩ D).ncard ≤ 1 by omega) with hKu1 | hDu1
  · -- `K` is a cylinder
    have hinjK : InjOn θ K := hinj K
      (fun z hz hzu => by
        obtain ⟨d, hd, hdz⟩ := hzD z hz hzu
        exact ⟨d, disjoint_left.mp hDK hd, hdz⟩)
      (fun a ha hau => by
        obtain ⟨w, hw, hwa⟩ := hWA₁ a ha
        exact ⟨w, fun hwK => hA₁Y₂ a ha hau (hwa ▸ hKY ⟨w, hwK, rfl⟩), hwa⟩) hKu1
    have hKF : θ '' K ∩ (A₁ ∪ A₂) ⊆ A₂ := by
      rintro x ⟨hxK, hx | hx⟩
      · by_cases hxu : x = u
        · exact hxu ▸ huu.2
        · exact absurd (hKY hxK) (hA₁Y₂ x hx hxu)
      · exact hx
    exact nonempty_cylinder_of_cut_piece hS hA₂ hoff₂ hsur₂ subset_union_right hcutF
      (fun x hx y hy h => hθ.2.2.1 hx hy h) hK hinjK hKF hCK
  · -- `D` would give a planar circle
    exfalso
    have hinjD : InjOn θ D := hinj D
      (fun z hz hzu => by
        obtain ⟨k, hk, hkz⟩ := hzK z hz
        exact ⟨k, fun hkD => disjoint_left.mp hDK hkD hk, hkz⟩)
      (fun a ha _ => by
        obtain ⟨w, hw, hwa⟩ := hWA₁ a ha
        exact ⟨w, fun hwD => (hDKW ▸ (Or.inl hwD : w ∈ D ∪ K) : w ∈ Wᶜ) hw, hwa⟩) hDu1
    obtain ⟨q, hqD, hq⟩ := hDu
    obtain ⟨Z, hZF, hZ, hZp⟩ := exists_planar_oArc_of_disc_piece hS hFc hoff hcutF hD.isOpen
      hDdisc hinjD ⟨q, hqD, show θ q ∈ A₁ ∪ A₂ from by rw [show θ q = u from hq]; exact Or.inl huu.1⟩
    rcases eq_or_eq_of_oArc_subset hA₁ hA₂ hZ
        (GM12.oArc_subset_meeting_circle_or hA₁ hA₂ h12 hZ hZF) with rfl | rfl
    · exact hsur₁.2.2 hZp
    · exact hsur₂.2.2 hZp

end GraphMinor.GM08
