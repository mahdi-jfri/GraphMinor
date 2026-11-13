module

public import GraphMinor.GM21.Section6LastTools
public import GraphMinor.GM19.Defs2
import GraphMinor.GM19.Perimeter
import GraphMinor.GM19.RadialExists
import GraphMinor.GM21.Section6ClaimThreeFind
import GraphMinor.GM11.GlueDiscs
import GraphMinor.GM16.LineImageEmbedding
import GraphMinor.GM17.CliqueChord
import GraphMinor.GM17.RegionFrontier
import GraphMinor.Surface.ArcDisc
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.DiscGrow

/-!
# Graph Minors XXI, (6.3), the last step: the disc of a jump

The last step of the proof of (6.3) (page 29 of the preprint): "every $\Sigma$-jump $J$ is
homotopic in $\hat{\Sigma}$ to the lines in $bd(\Sigma)$ joining the ends of $J$". We prove the form
we use. Here `Σ` has one cuff `C`, and `Σ̂` is `Σ` with a closed disc `R` pasted on `C`.

Let `U` be a line in `Σ` with ends `x ≠ u` in `C` and no other point in `bd(Σ)`, and let `W` be a
closed set that meets `U` only at `x, u`. Suppose that every proper line `F` with ends `x, u` that
meets `U ∪ W` only at its ends cuts off a closed disc `E ⊆ Σ` with `F ⊆ bd(E) ⊆ F ∪ bd(Σ)` (by claims
(2) and (4), this holds unless the bound of (6.3) already holds). Then `U` and a line `B ⊆ C` with
ends `x, u` bound a closed disc `Q ⊇ R` in `Σ̂` (`exists_disc_of_line`).

The proof takes the line `F` next to `U` and the disc `P` between them (`exists_parallel_disc`), and
the disc `E` of `F`. In `Σ̂`, `X = R ∪ E` is a closed disc with boundary `F ∪ B`, where `B` is the rest
of `C` after `bd(E) ∩ C`. The disc `P` lies inside `X` or meets it only in `F`. In the first case
`Q = closure(X \ P)`, and in the second `Q = X ∪ P`.

First, some facts on the capped surface.
* `disc_inter_bd_subset`: a closed disc in `Σ` meets `bd(Σ)` only in its boundary, since the inside
  of the disc is open in `Σ̂` and every point of `bd(Σ)` is a limit of points of a pasted disc.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Topology GraphMinor.Surface GraphMinor.GM19

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]

/-- The image of a closed disc of `Σ` in `Σ̂` is a closed disc, with the image of its boundary as
boundary. -/
theorem emb_isClosedDisc (cap : IsCappedSurface S Shat) {E : Set S}
    (hE : IsClosedDisc E) :
    IsClosedDisc (cap.emb '' E) ∧ discBd (cap.emb '' E) = cap.emb '' discBd E := by
  have : T2Space Shat := cap.isSurface.2.1
  exact GM11.isClosedDisc_image hE cap.isEmbedding.continuous.continuousOn
    cap.isEmbedding.injective.injOn

/-- A closed disc of `Σ` meets `bd(Σ)` only in its boundary. -/
theorem disc_inter_bd_subset (hS : IsSurface S) (cap : IsCappedSurface S Shat) {E : Set S}
    (hE : IsClosedDisc E) : E ∩ bd S ⊆ discBd E := by
  have : T2Space S := hS.2.1
  have : T2Space Shat := cap.isSurface.2.1
  have hman : ∀ y : Shat, IsManifoldPoint y := cap.isSurface.2.2
  rintro z ⟨hzE, hzb⟩
  by_contra hz
  obtain ⟨hE', hbd'⟩ := emb_isClosedDisc cap hE
  have hint : cap.emb z ∈ discInt (cap.emb '' E) := by
    refine ⟨mem_image_of_mem _ hzE, ?_⟩
    rw [hbd']
    rintro ⟨y, hy, hyz⟩
    exact hz (cap.isEmbedding.injective hyz ▸ hy)
  have hΘ : connectedComponentIn (bd S) z ∈ cuffs S := ⟨z, hzb, rfl⟩
  have hzR : cap.emb z ∈ closure (cap.cuffDisc (connectedComponentIn (bd S) z)) := by
    have := cap.cuffDisc_bd _ hΘ
    refine discBd_subset _ ?_
    rw [this]
    exact mem_image_of_mem _ (mem_connectedComponentIn hzb)
  obtain ⟨w, hwO, hwD⟩ := mem_closure_iff.1 hzR _ (isOpen_discInt hman hE') hint
  obtain ⟨y, -, rfl⟩ := hwO.1
  exact cap.notMem_range hΘ hwD (mem_range_self y)

/-- A set identity for the boundaries of glued discs: removing the inside of `F` from
`F ∪ U ∪ B` leaves `U ∪ B`, when `U` holds the ends of `F` and `U, B` meet `F` only at its ends. -/
theorem union_sdiff_line {T : Type} {F U B : Set T} {x u : T} (hx : x ∈ U) (hu : u ∈ U)
    (hUF : U ∩ F ⊆ {x, u}) (hBF : B ∩ F ⊆ {x, u}) :
    (F ∪ U ∪ B) \ (F \ {x, u}) = U ∪ B := by
  ext z
  constructor
  · rintro ⟨(hz | hz) | hz, hzn⟩
    · have hzxu : z ∈ ({x, u} : Set T) := by
        by_contra h
        exact hzn ⟨hz, h⟩
      rcases hzxu with rfl | h
      · exact Or.inl hx
      · exact Or.inl (mem_singleton_iff.mp h ▸ hu)
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨Or.inl (Or.inr hz), fun h => h.2 (hUF ⟨hz, h.1⟩)⟩
    · exact ⟨Or.inr hz, fun h => h.2 (hBF ⟨hz, h.1⟩)⟩

/-- **The disc of a jump** (Graph Minors XXI, proof of (6.3), page 29 of the preprint: "every
$\Sigma$-jump $J$ is homotopic in $\hat{\Sigma}$ to the lines in $bd(\Sigma)$ joining the ends of
$J$"). Let `Σ` have the one cuff `C`, and let `R` be the closed disc pasted on `C` in `Σ̂`. Let `U`
be a line with ends `x ≠ u` in `C` and no other point in `bd(Σ)`, and let `W` be a closed set that
meets `U` only at `x, u`. If every proper line with ends `x, u` that meets `U ∪ W` only at its ends
cuts off a closed disc, then the image of `U` and a line `B` of the image of `C` with ends `x, u`
bound a closed disc `Q ⊇ R` of `Σ̂`. -/
theorem exists_disc_of_line (hS : IsSurface S) (cap : IsCappedSurface S Shat) {C : Set S}
    (hC : C ∈ cuffs S) (hbd : bd S = C) {U W : Set S} {x u : S} (hU : IsLineWithEnds U x u)
    (hW : IsClosed W) (hUW : U ∩ W ⊆ {x, u}) (hUb : U ∩ bd S ⊆ {x, u}) (hx : x ∈ C) (hu : u ∈ C)
    (hxu : x ≠ u)
    (hgood : ∀ F : Set S, IsProperLineInSurface F x u → F ∩ (U ∪ W) ⊆ {x, u} →
      ∃ E : Set S, IsClosedDisc E ∧ F ⊆ discBd E ∧ discBd E ⊆ F ∪ bd S) :
    ∃ Q B : Set Shat, IsClosedDisc Q ∧ closure (cap.cuffDisc C) ⊆ Q ∧
      IsLineWithEnds B (cap.emb x) (cap.emb u) ∧ B ⊆ cap.emb '' C ∧
      discBd Q = cap.emb '' U ∪ B := by
  classical
  have : T2Space S := hS.2.1
  have : T2Space Shat := cap.isSurface.2.1
  have hman : ∀ y : Shat, IsManifoldPoint y := cap.isSurface.2.2
  set e := cap.emb with he_def
  have hinj : Function.Injective e := cap.isEmbedding.injective
  set R := closure (cap.cuffDisc C) with hR_def
  have hR : IsClosedDisc R := cap.cuffDisc_closedDisc C hC
  have hRbd : discBd R = e '' C := cap.cuffDisc_bd C hC
  have hxb : x ∈ bd S := hbd ▸ hx
  have hub : u ∈ bd S := hbd ▸ hu
  -- The line `F` next to `U`, the disc `P` between them, and the disc `E` of `F`.
  obtain ⟨F, P, hFp, hFU, hP, hPbd, hPW⟩ :=
    exists_parallel_disc hS hU hW hUW hUb hxb hub hxu
  have hFP : F ⊆ P := fun z hz => discBd_subset P (hPbd ▸ Or.inl hz)
  obtain ⟨E, hE, hFE, hEbd⟩ := hgood F hFp (by
    rintro z ⟨hzF, hzU | hzW⟩
    · exact hFU.subset ⟨hzF, hzU⟩
    · exact hPW ⟨hFP hzF, Or.inl hzW⟩)
  -- The rest `A` of the boundary of `E` is a line in `C`.
  obtain ⟨hA, hFA, hFAun⟩ := IsOArc.line_compl hE.isOArc_discBd hFp.1 hFE hxu
  set A := discBd E \ (F \ {x, u}) with hA_def
  have hFb : F ∩ bd S ⊆ {x, u} := fun z hz => by
    by_contra h
    exact disjoint_left.1 hFp.2.2.2 ⟨hz.1, h⟩ hz.2
  have hAC : A ⊆ C := by
    rintro z ⟨hz, hzn⟩
    rcases hEbd hz with hzF | hzb
    · have hzxu : z ∈ ({x, u} : Set S) := by
        by_contra h
        exact hzn ⟨hzF, h⟩
      rcases hzxu with rfl | h
      · exact hx
      · exact mem_singleton_iff.mp h ▸ hu
    · exact hbd ▸ hzb
  have hEC : E ∩ C ⊆ A := by
    rintro z ⟨hzE, hzC⟩
    refine ⟨disc_inter_bd_subset hS cap hE ⟨hzE, hbd ▸ hzC⟩, fun h => h.2 ?_⟩
    exact hFb ⟨h.1, hbd ▸ hzC⟩
  -- The images in `Σ̂`.
  have hFl := GM16.isLineWithEnds_image_embedding cap.isEmbedding hFp.1
  have hAl := GM16.isLineWithEnds_image_embedding cap.isEmbedding hA
  have hUl := GM16.isLineWithEnds_image_embedding cap.isEmbedding hU
  obtain ⟨hE', hE'bd⟩ := emb_isClosedDisc cap hE
  obtain ⟨hP', hP'bd⟩ := emb_isClosedDisc cap hP
  have hxy' : e x ≠ e u := fun h => hxu (hinj h)
  have himg_pair : e '' {x, u} = {e x, e u} := by rw [image_pair]
  -- Images of intersections.
  have himg_inter : ∀ X Y : Set S, e '' X ∩ e '' Y = e '' (X ∩ Y) := fun X Y =>
    (image_inter hinj).symm
  -- `R ∩ E' = A'`.
  have hRE : R ∩ e '' E = e '' A := by
    refine Subset.antisymm ?_ ?_
    · rintro w ⟨hwR, z, hzE, rfl⟩
      have hzC : z ∈ C := ClaimThree.mem_of_emb_mem_closure_cuffDisc hS cap hC hwR
      exact mem_image_of_mem e (hEC ⟨hzE, hzC⟩)
    · rintro w ⟨z, hzA, rfl⟩
      refine ⟨discBd_subset R ?_, mem_image_of_mem e (discBd_subset E hzA.1)⟩
      rw [hRbd]
      exact mem_image_of_mem e (hAC hzA)
  have hA'R : e '' A ⊆ discBd R := hRbd ▸ image_mono hAC
  have hA'E : e '' A ⊆ discBd (e '' E) := hE'bd ▸ image_mono sdiff_subset
  obtain ⟨hX, hXbd⟩ := disc_union R (e '' E) (e '' A) (e x) (e u) hR hE' hAl hRE hA'R hA'E
  -- The rest `B` of the image of `C`.
  have hCO : IsOArc (e '' C) := hRbd ▸ hR.isOArc_discBd
  obtain ⟨hBl, hAB, hABun⟩ := IsOArc.line_compl hCO hAl (image_mono hAC) hxy'
  set B := e '' C \ (e '' A \ {e x, e u}) with hB_def
  have hBC : B ⊆ e '' C := sdiff_subset
  have hFA' : e '' F ∩ e '' A = {e x, e u} := by rw [himg_inter, hFA, himg_pair]
  have hFC : F ∩ C ⊆ {x, u} := fun z hz => hFb ⟨hz.1, hbd ▸ hz.2⟩
  have hBF : B ∩ e '' F ⊆ {e x, e u} := by
    rintro w ⟨hwB, hwF⟩
    obtain ⟨z, hzC, rfl⟩ := hBC hwB
    obtain ⟨z', hz'F, hz'⟩ := hwF
    rw [← hinj hz'] at hzC
    rw [← hz', ← himg_pair]
    exact mem_image_of_mem e (hFC ⟨hz'F, hzC⟩)
  have hXbd' : discBd (R ∪ e '' E) = e '' F ∪ B := by
    rw [hXbd, hRbd, hE'bd, ← hFAun, image_union]
    ext w
    constructor
    · rintro ⟨hw | hw | hw, hwn⟩
      · exact Or.inr ⟨hw, hwn⟩
      · exact Or.inl hw
      · have hwxu : w ∈ ({e x, e u} : Set Shat) := by
          by_contra h
          exact hwn ⟨hw, h⟩
        rcases hwxu with rfl | h
        · exact Or.inl (mem_image_of_mem e hFp.1.left_mem)
        · exact Or.inl (mem_singleton_iff.mp h ▸ mem_image_of_mem e hFp.1.right_mem)
    · rintro (hw | hw)
      · exact ⟨Or.inr (Or.inl hw), fun h => h.2 (hFA' ▸ ⟨hw, h.1⟩)⟩
      · exact ⟨Or.inl hw.1, hw.2⟩
  -- `P'` lies inside `X` or meets it only in `F'`.
  have hF'P' : e '' F ⊆ discBd (e '' P) := hP'bd ▸ image_mono (hPbd ▸ subset_union_left)
  have hpre : IsPreconnected (e '' P \ e '' F) := GM17.Painting.isPreconnected_disc_diff hP' hF'P'
  have hPC : e '' P ∩ e '' C ⊆ {e x, e u} := by
    rw [himg_inter, ← himg_pair]
    exact image_mono fun z hz => hPW ⟨hz.1, Or.inr (hbd ▸ hz.2)⟩
  have hdisj : Disjoint (e '' P \ e '' F) (discBd (R ∪ e '' E)) := by
    rw [hXbd']
    refine disjoint_left.2 fun w hw hw' => hw.2 ?_
    rcases hw' with hwF | hwB
    · exact hwF
    · have := hPC ⟨hw.1, hBC hwB⟩
      rcases this with rfl | h
      · exact mem_image_of_mem e hFp.1.left_mem
      · exact mem_singleton_iff.mp h ▸ mem_image_of_mem e hFp.1.right_mem
  have hF'X : e '' F ⊆ R ∪ e '' E := fun w hw =>
    Or.inr (image_mono (hFE.trans (discBd_subset E)) hw)
  -- Shared facts for the boundaries.
  have hUF' : e '' U ∩ e '' F ⊆ {e x, e u} := by
    rw [himg_inter, inter_comm, hFU, himg_pair]
  have hU'C : e '' U ∩ e '' C ⊆ {e x, e u} := by
    rw [himg_inter, ← himg_pair]
    exact image_mono fun z hz => hUb ⟨hz.1, hbd ▸ hz.2⟩
  have hxU' : e x ∈ e '' U := mem_image_of_mem e hU.left_mem
  have huU' : e u ∈ e '' U := mem_image_of_mem e hU.right_mem
  have hP'bd' : discBd (e '' P) = e '' F ∪ e '' U := by rw [hP'bd, hPbd, image_union]
  rcases GM17.disc_dichotomy hman hX hpre hdisj with hin | hout
  · -- `P'` lies inside `X`: take `Q = closure (X \ P')`.
    have hsub : e '' P ⊆ R ∪ e '' E := by
      intro w hw
      by_cases hwF : w ∈ e '' F
      · exact hF'X hwF
      · exact hin ⟨hw, hwF⟩
    have hmeet : discBd (e '' P) ∩ discBd (R ∪ e '' E) = e '' F := by
      rw [hP'bd', hXbd']
      refine Subset.antisymm ?_ fun w hw => ⟨Or.inl hw, Or.inl hw⟩
      rintro w ⟨hw | hw, hw' | hw'⟩
      · exact hw
      · exact hw
      · exact hw'
      · have := hU'C ⟨hw, hBC hw'⟩
        rcases this with rfl | h
        · exact mem_image_of_mem e hFp.1.left_mem
        · exact mem_singleton_iff.mp h ▸ mem_image_of_mem e hFp.1.right_mem
    obtain ⟨hQ, hQbd, -⟩ := disc_difference (e '' P) (R ∪ e '' E) (e '' F) (e x) (e u) hP' hX hsub
      hFl hmeet
    refine ⟨_, B, hQ, ?_, hBl, hBC, ?_⟩
    · -- `R` minus the two ends lies in `X \ P'`, and `R` is the closure of its inside.
      intro w hw
      have hsubR : discInt R ⊆ (R ∪ e '' E) \ e '' P := by
        rintro v ⟨hvR, hvbd⟩
        refine ⟨Or.inl hvR, fun hvP => hvbd ?_⟩
        obtain ⟨z, hzP, rfl⟩ := hvP
        have hzC : z ∈ C := ClaimThree.mem_of_emb_mem_closure_cuffDisc hS cap hC hvR
        rw [hRbd]
        exact mem_image_of_mem e hzC
      exact closure_mono hsubR (hR.subset_closure_discInt hw)
    · rw [hQbd, hP'bd', hXbd']
      have : e '' F ∪ e '' U ∪ (e '' F ∪ B) = e '' F ∪ e '' U ∪ B := by
        ext w
        simp only [mem_union]
        tauto
      rw [this]
      exact union_sdiff_line hxU' huU' hUF' (fun w hw => hBF hw)
  · -- `P'` meets `X` only in `F'`: take `Q = X ∪ P'`.
    have hmeet : (R ∪ e '' E) ∩ e '' P = e '' F := by
      refine Subset.antisymm ?_ fun w hw => ⟨hF'X hw, image_mono hFP hw⟩
      rintro w ⟨hwX, hwP⟩
      by_contra hwF
      exact disjoint_left.1 hout ⟨hwP, hwF⟩ hwX
    have hF'Xbd : e '' F ⊆ discBd (R ∪ e '' E) := hXbd' ▸ subset_union_left
    obtain ⟨hQ, hQbd⟩ := disc_union (R ∪ e '' E) (e '' P) (e '' F) (e x) (e u) hX hP' hFl hmeet
      hF'Xbd hF'P'
    refine ⟨_, B, hQ, fun w hw => Or.inl (Or.inl hw), hBl, hBC, ?_⟩
    rw [hQbd, hXbd', hP'bd']
    have : e '' F ∪ B ∪ (e '' F ∪ e '' U) = e '' F ∪ e '' U ∪ B := by
      ext w
      simp only [mem_union]
      tauto
    rw [this]
    exact union_sdiff_line hxU' huU' hUF' (fun w hw => hBF hw)

end LastStep
end GM21
end GraphMinor
