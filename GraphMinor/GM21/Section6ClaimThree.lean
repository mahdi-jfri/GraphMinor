module

public import GraphMinor.GM21.Section4
import GraphMinor.GM21.Section6Side
import GraphMinor.GM11.Defs
import GraphMinor.GM07.Section8
import GraphMinor.GM12.Section3CircleInclusion
import GraphMinor.GM14.Section6c
import GraphMinor.GM07.Section2Base

/-!
# Graph Minors XXI, (6.3), claim (3): a line between two cuffs does not separate

Claim (3) of the proof of (6.3) (page 29 of the preprint) says: "there is a proper line $F$
with ends vertices of $\Gamma$ in different cuffs, and with no internal point in $U(\Gamma)$. But then
$F$ does not separate $\Sigma$, contrary to (2)."

This file proves the second sentence (`not_isSide_of_ends_in_different_cuffs`): a proper line whose
ends lie in different cuffs is not the common part `Σ₁ ∩ Σ₂` of two surfaces `Σ₁, Σ₂` with
`Σ₁ ∪ Σ₂ = Σ`. The cuff `C` at one end `a` minus `a` is connected and misses `F`, so it lies in one
side, say `Σ₁`. Then `C ∪ F` lies in one cuff of `Σ₁`, which is an `O`-arc. An `O`-arc that contains
the `O`-arc `C` equals it (`GM12.oArc_eq_of_subset`), so `F ⊆ C ⊆ bd(Σ)`, which is false for the
inside points of the proper line `F`.

The same argument shows that when both ends of `F` lie in one cuff `C`, the two arcs of `C \ {a, b}`
lie on different sides (`cuff_inter_sides`). Claim (4) and the last step of the proof of (6.3) use
this.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace ClaimThree

open Set Topology GraphMinor.Surface GraphMinor.GM21.Side

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- No side of a proper line `F` contains a whole cuff `C` through an end `a` of `F`: the cuff of
`Σ₁` through `a` would contain `C ∪ F`, so it would equal `C`, and `F ⊆ C ⊆ bd(Σ)`. -/
theorem false_of_cuff_subset_side (hS : IsSurface S) {S₁ S₂ F : Set S} {a b : S}
    (hS₁ : IsSurface S₁) (hS₂ : IsSurface S₂) (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F)
    (hF : IsProperLineInSurface F a b) {C : Set S} (hC : C ∈ cuffs S) (haC : a ∈ C)
    (hCS : C ⊆ S₁) : False := by
  have hFS : F ⊆ S₁ := hint ▸ inter_subset_left
  have haF : a ∈ F := hF.1.left_mem
  have hCO : IsOArc C := (cuff_statement S hS).2.2 C hC
  have hCbd : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  -- The set `C ∪ F`, read in `Σ₁`, is connected and lies in `bd(Σ₁)`.
  set Z : Set S₁ := Subtype.val ⁻¹' (C ∪ F) with hZ
  have hZimg : Subtype.val '' Z = C ∪ F := by
    rw [hZ, Subtype.image_preimage_coe, inter_eq_right.mpr (union_subset hCS hFS)]
  have hZconn : IsPreconnected Z := by
    have hpre : IsPreconnected (C ∪ F) :=
      hCO.isPreconnected.union a haC haF (GM07.IsLineWithEnds.isConnected hF.1).isPreconnected
    rw [← hZimg] at hpre
    exact (IsInducing.subtypeVal.isPreconnected_image).mp hpre
  have hZbd : Z ⊆ bd S₁ := fun x hx =>
    (mem_bd_side_iff' hS hS₁ hS₂ hun hint hF.1).mpr (by
      rcases hx with h | h
      · exact Or.inr (hCbd h)
      · exact Or.inl h)
  let a₁ : S₁ := ⟨a, hFS haF⟩
  have ha₁ : a₁ ∈ Z := Or.inr haF
  set K : Set S₁ := connectedComponentIn (bd S₁) a₁
  have hK : K ∈ cuffs S₁ := ⟨a₁, hZbd ha₁, rfl⟩
  have hZK : Z ⊆ K := hZconn.subset_connectedComponentIn ha₁ hZbd
  have hKO : IsOArc (Subtype.val '' K) := by
    obtain ⟨φ⟩ := (cuff_statement S₁ hS₁).2.2 K hK
    exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage K)⟩
  have hCK : C ⊆ Subtype.val '' K := fun x hx =>
    ⟨⟨x, hCS hx⟩, hZK (Or.inl hx), rfl⟩
  have hFC : F ⊆ C := by
    rw [GM12.oArc_eq_of_subset hCO hKO hCK]
    exact fun x hx => ⟨⟨x, hFS hx⟩, hZK (Or.inr hx), rfl⟩
  obtain ⟨y, hyF, hyab⟩ := GM14.IsLineWithEnds.nonempty_sdiff_pair hF.1
  exact disjoint_left.mp hF.2.2.2 ⟨hyF, hyab⟩ (hCbd (hFC hyF))

/-- **Graph Minors XXI, proof of (6.3), claim (3), second step** (page 29 of the preprint):
"there is a proper line $F$ with ends vertices of $\Gamma$ in different cuffs ... But then $F$ does
not separate $\Sigma$". A proper line whose ends lie in different cuffs is not `Σ₁ ∩ Σ₂` for
surfaces `Σ₁, Σ₂` with `Σ₁ ∪ Σ₂ = Σ`. -/
theorem not_isSide_of_ends_in_different_cuffs (hS : IsSurface S) {S₁ S₂ F : Set S} {a b : S}
    (hS₁ : IsSurface S₁) (hS₂ : IsSurface S₂) (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F)
    (hF : IsProperLineInSurface F a b) {C : Set S} (hC : C ∈ cuffs S) (haC : a ∈ C)
    (hbC : b ∉ C) : False := by
  have hCO : IsOArc C := (cuff_statement S hS).2.2 C hC
  have hCbd : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hFbd : F ∩ bd S = {a, b} := hF.inter_bd_eq
  have hdis : Disjoint (C \ {a}) F := disjoint_left.mpr fun x hx hxF => by
    have : x ∈ F ∩ bd S := ⟨hxF, hCbd hx.1⟩
    rw [hFbd] at this
    rcases this with rfl | rfl
    · exact hx.2 rfl
    · exact hbC hx.1
  have hc₁ := isClosed_of_isSurface hS₁
  have hc₂ := isClosed_of_isSurface hS₂
  have hpre : IsPreconnected (C \ {a}) := (isPathConnected_oArc_diff hCO haC).isConnected.isPreconnected
  have hclos : ∀ T : Set S, IsClosed T → F ⊆ T → C \ {a} ⊆ T → C ⊆ T := fun T _ hFT hCT x hx => by
    by_cases hxa : x = a
    · exact hxa ▸ hFT hF.1.left_mem
    · exact hCT ⟨hx, hxa⟩
  rcases subset_or_disjoint_side hc₁ hc₂ hun hint hpre hdis with h₁ | h₁
  · exact false_of_cuff_subset_side hS hS₁ hS₂ hun hint hF hC haC
      (hclos S₁ hc₁ (hint ▸ inter_subset_left) h₁)
  · exact false_of_cuff_subset_side hS hS₂ hS₁ (by rw [union_comm, hun]) (by rw [inter_comm, hint])
      hF hC haC (hclos S₂ hc₂ (hint ▸ inter_subset_right) (subset_two_of_disjoint hun h₁))

/-- **The two arcs of a cuff at a separating line.** Let `F` be a proper line with ends `a, b` in one
cuff `C`, and let `Σ₁, Σ₂` be its sides. Then `C \ {a, b}` consists of two arcs `B₁, B₂`, each of
which with `a, b` added is a line with ends `a, b`, and `C ∩ Σ₁ = B₁ ∪ {a, b}`,
`C ∩ Σ₂ = B₂ ∪ {a, b}`. Each arc is connected and misses `F`, so it lies on one side, and the two
arcs cannot lie on the same side by `false_of_cuff_subset_side`. -/
theorem cuff_inter_sides (hS : IsSurface S) {S₁ S₂ F : Set S} {a b : S}
    (hS₁ : IsSurface S₁) (hS₂ : IsSurface S₂) (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F)
    (hF : IsProperLineInSurface F a b) {C : Set S} (hC : C ∈ cuffs S) (haC : a ∈ C)
    (hbC : b ∈ C) :
    ∃ B₁ B₂ : Set S, C \ {a, b} = B₁ ∪ B₂ ∧ Disjoint B₁ B₂ ∧
      IsLineWithEnds (B₁ ∪ {a, b}) a b ∧ IsLineWithEnds (B₂ ∪ {a, b}) a b ∧
      C ∩ S₁ = B₁ ∪ {a, b} ∧ C ∩ S₂ = B₂ ∪ {a, b} := by
  have hCO : IsOArc C := (cuff_statement S hS).2.2 C hC
  have hCbd : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hFbd : F ∩ bd S = {a, b} := hF.inter_bd_eq
  have hab : a ≠ b := hF.ne
  obtain ⟨B₁, B₂, hcomp, hdisj, hun', hl₁, hl₂⟩ := GM07.Net.oArc_components_diff_pair hCO haC hbC hab
  have hc₁ := isClosed_of_isSurface hS₁
  have hc₂ := isClosed_of_isSurface hS₂
  have hFS₁ : F ⊆ S₁ := hint ▸ inter_subset_left
  have hFS₂ : F ⊆ S₂ := hint ▸ inter_subset_right
  have haF : a ∈ F := hF.1.left_mem
  have hbF : b ∈ F := hF.1.right_mem
  have hsub : ∀ B ∈ componentsIn (C \ {a, b}), IsPreconnected B ∧ B ⊆ C \ {a, b} := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨isPreconnected_connectedComponentIn, connectedComponentIn_subset _ _⟩
  have hdisF : ∀ B ⊆ C \ {a, b}, Disjoint B F := fun B hB => disjoint_left.mpr fun x hx hxF => by
    have : x ∈ F ∩ bd S := ⟨hxF, hCbd (hB hx).1⟩
    rw [hFbd] at this
    exact (hB hx).2 this
  have hside : ∀ B ∈ componentsIn (C \ {a, b}), B ⊆ S₁ ∧ Disjoint B S₂ ∨ B ⊆ S₂ ∧ Disjoint B S₁ := by
    intro B hB
    obtain ⟨hBp, hBs⟩ := hsub B hB
    have hBF := hdisF B hBs
    have hoff : ∀ {T T' : Set S}, B ⊆ T → T ∩ T' = F → Disjoint B T' := fun hBT hTT' =>
      disjoint_left.mpr fun x hx hxT' => disjoint_left.mp hBF hx (hTT' ▸ ⟨hBT hx, hxT'⟩)
    rcases subset_or_disjoint_side hc₁ hc₂ hun hint hBp hBF with h | h
    · exact Or.inl ⟨h, hoff h hint⟩
    · have h₂ := subset_two_of_disjoint hun h
      exact Or.inr ⟨h₂, hoff h₂ (by rw [inter_comm, hint])⟩
  have hB₁ : B₁ ∈ componentsIn (C \ {a, b}) := hcomp ▸ Or.inl rfl
  have hB₂ : B₂ ∈ componentsIn (C \ {a, b}) := hcomp ▸ Or.inr rfl
  have hCeq : C = B₁ ∪ B₂ ∪ {a, b} := by
    rw [← hun']
    ext x
    by_cases hx : x ∈ ({a, b} : Set S)
    · exact ⟨fun _ => Or.inr hx, fun _ => by rcases hx with rfl | rfl; exacts [haC, hbC]⟩
    · exact ⟨fun h => Or.inl ⟨h, hx⟩, fun h => h.elim (fun h => h.1) (fun h => (hx h).elim)⟩
  have hsame : ∀ {T T' : Set S}, IsSurface T → IsSurface T' → T ∪ T' = univ → T ∩ T' = F →
      B₁ ⊆ T → B₂ ⊆ T → False := fun hT hT' hTT hTT' h₁ h₂ =>
    false_of_cuff_subset_side hS hT hT' hTT hTT' hF hC haC (by
      rw [hCeq]
      have hFT : F ⊆ _ := hTT' ▸ inter_subset_left
      refine union_subset (union_subset h₁ h₂) ?_
      rintro x (rfl | rfl)
      exacts [hFT haF, hFT hbF])
  have hinter : ∀ {Bi Bj T : Set S}, C \ {a, b} = Bi ∪ Bj → Bi ⊆ T → Disjoint Bj T → F ⊆ T →
      C ∩ T = Bi ∪ {a, b} := by
    intro Bi Bj T hCij hBi hBj hFT
    ext x
    constructor
    · rintro ⟨hxC, hxT⟩
      by_cases hx : x ∈ ({a, b} : Set S)
      · exact Or.inr hx
      · rcases (hCij ▸ (⟨hxC, hx⟩ : x ∈ C \ {a, b}) : x ∈ Bi ∪ Bj) with h | h
        · exact Or.inl h
        · exact (disjoint_left.mp hBj h hxT).elim
    · rintro (h | h)
      · exact ⟨(hCij ▸ (Or.inl h : x ∈ Bi ∪ Bj) : x ∈ C \ {a, b}).1, hBi h⟩
      · rcases h with rfl | h
        · exact ⟨haC, hFT haF⟩
        · rw [mem_singleton_iff.mp h]
          exact ⟨hbC, hFT hbF⟩
  have hun₂ : S₂ ∪ S₁ = univ := by rw [union_comm, hun]
  have hint₂ : S₂ ∩ S₁ = F := by rw [inter_comm, hint]
  rcases hside B₁ hB₁ with ⟨h₁, d₁⟩ | ⟨h₁, d₁⟩ <;> rcases hside B₂ hB₂ with ⟨h₂, d₂⟩ | ⟨h₂, d₂⟩
  · exact (hsame hS₁ hS₂ hun hint h₁ h₂).elim
  · exact ⟨B₁, B₂, hun', hdisj, hl₁, hl₂, hinter hun' h₁ d₂ hFS₁,
      hinter (by rw [hun', union_comm]) h₂ d₁ hFS₂⟩
  · exact ⟨B₂, B₁, by rw [hun', union_comm], hdisj.symm, hl₂, hl₁,
      hinter (by rw [hun', union_comm]) h₂ d₁ hFS₁, hinter hun' h₁ d₂ hFS₂⟩
  · exact (hsame hS₂ hS₁ hun₂ hint₂ h₁ h₂).elim

end ClaimThree
end GM21
end GraphMinor
