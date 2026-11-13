module

public import GraphMinor.GM21.Section6LastJumpDisc
public import GraphMinor.GM21.Section6LastFlat
public import GraphMinor.GM21.Section6LastCover
public import GraphMinor.GM21.CuffSpaces
import GraphMinor.GM07.CylinderCap
import GraphMinor.GM07.CuffForest
import GraphMinor.GM19.Perimeter
import GraphMinor.GM19.RadialExists
import GraphMinor.GM21.Section6ClaimThreeFind
import GraphMinor.GM21.Section6Exhaustive

/-!
# Graph Minors XXI, (6.3), the last step: a disc around the drawing in `Σ̂`

Here `Σ` has one cuff, and every good line cuts off a closed disc of `Σ` (as in
`LastStep.disc_or_le`). We work in the capped surface `Σ̂`, where `R` is the closure of the pasted
disc. The paper says (page 29 of the preprint): "It follows that every $O$-arc in $R \cup U(\Gamma)$
is null-homotopic in $\hat{\Sigma}$. By theorem (11.10) of [5] there is a closed disc
$\Delta \subseteq \hat{\Sigma}$ with $R \cup U(\Gamma) \subseteq \Delta$". We follow this.

* Each jump `J` of `Γ` gives a line `U_J` (`jumpLine_spec`) and a closed disc `Q_J ⊇ R` bounded by
  `U_J` and a line of `bd(R)` (`exists_disc_of_line`). These form an `IsJumpDiscs` family.
* By claim (4), each jump is homotopic to the line of `bd(R)`, so `R ∪ U(Γ)` is flat, and VII (11.10)
  gives the closed disc `X` with `R ∪ U(Γ) ⊆ X` (`IsJumpDiscs.exists_disc`, `Section6LastFlat.lean`).

`exists_disc_around_drawing` is the result.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Topology Function GraphMinor.Surface GraphMinor.GM19 Hypergraph

universe u v

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {L : Hypergraph α β}
  {Shat : Type} [TopologicalSpace Shat]

/-- **A disc around `R ∪ U(Γ)`** (Graph Minors XXI, proof of (6.3), page 29 of the preprint): "there
is a closed disc $\Delta \subseteq \hat{\Sigma}$ with $R \cup U(\Gamma) \subseteq \Delta$". Let `Σ`
have one cuff `bd(Σ)`, let `Σ̂` not be a sphere, and let every good line cut off a closed disc. Then
there is a closed disc `X` of `Σ̂` with `R ∪ U(Γ) ⊆ X`. -/
theorem exists_disc_around_drawing [ConnectedSpace S]
    (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (cap : IsCappedSurface S Shat) (hns : ¬ IsSphere Shat)
    (hC : bd S ∈ cuffs S)
    (hgood : ∀ (F : Set S) (x u : S), IsProperLineInSurface F x u → x ∈ Γ.V → u ∈ Γ.V →
      F ∩ Γ.U ⊆ {x, u} → ∃ E : Set S, IsClosedDisc E ∧ F ⊆ discBd E ∧ discBd E ⊆ F ∪ bd S) :
    ∃ X : Set Shat, IsClosedDisc X ∧ closure (cap.cuffDisc (bd S)) ⊆ X ∧
      cap.emb '' Γ.U ⊆ X := by
  classical
  have hS := hP.is_surface
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : T2Space Shat := cap.isSurface.2.1
  have : ConnectedSpace Shat := cap.connected
  have hT := cap.isClosedSurface
  have hiso := hP.drawing_iso
  have hprop := hP.is_proper_drawing
  have hK := IsExhaustiveLinkage.isLinkage hP hL
  have hdeg := IsExhaustiveLinkage.ncard_incidentEdges_eq_two hP hL
  have h2 : ∀ e ∈ Γ_sub.edgeSet, (Γ_sub.ends e).ncard = 2 := fun e he => hK.ends_ncard_eq_two he
  have hemb := cap.isEmbedding
  have hinj := hemb.injective
  set R := closure (cap.cuffDisc (bd S)) with hR_def
  have hR : IsClosedDisc R := cap.cuffDisc_closedDisc _ hC
  have hRbd : discBd R = cap.emb '' bd S := cap.cuffDisc_bd _ hC
  have hembR : ∀ {z : S}, cap.emb z ∈ R → z ∈ bd S := fun hz =>
    ClaimThree.mem_of_emb_mem_closure_cuffDisc hS cap hC hz
  have hCR : ∀ {z : S}, z ∈ bd S → cap.emb z ∈ R := fun hz =>
    discBd_subset R (hRbd ▸ mem_image_of_mem _ hz)
  set B0 := ιV '' (Γ.V ∩ bd S)
  have hterm_bd : ∀ J ∈ jumpSet Γ_sub B0, ∀ z ∈ Γ.V, ιV z ∈ terminals J → z ∈ bd S := by
    intro J hJ z hz hzt
    obtain ⟨z', hz', hzz'⟩ := terminals_subset_of_mem_jumpSet hJ hzt
    rw [← hiso.ιV_injOn hz'.1 hz hzz']
    exact hz'.2
  have hU_sub : ∀ J : Hypergraph α β, jumpLine Γ ιE J ⊆ Γ.U := by
    intro J z hz
    obtain ⟨e, he, -, hze⟩ := mem_jumpLine.1 hz
    exact closure_minimal (fun y hy => (he.2.1 hy).1) Γ.isClosed_U hze
  -- The disc of each jump.
  have hex : ∀ J ∈ jumpSet Γ_sub B0, ∃ (x y : S) (Qs Bs : Set Shat), x ∈ Γ.V ∧ y ∈ Γ.V ∧
      x ∈ bd S ∧ y ∈ bd S ∧ x ≠ y ∧ terminals J = {ιV x, ιV y} ∧
      IsLineWithEnds (jumpLine Γ ιE J) x y ∧ IsClosedDisc Qs ∧ R ⊆ Qs ∧
      IsLineWithEnds Bs (cap.emb x) (cap.emb y) ∧ Bs ⊆ cap.emb '' bd S ∧
      discBd Qs = cap.emb '' jumpLine Γ ιE J ∪ Bs := by
    intro J hJ
    obtain ⟨x, hxV, y, hyV, hxy, hterm, hline, -⟩ :=
      jumpLine_spec hiso h2 hJ.1 hJ.2.1 (edgeSet_nonempty_of_mem_jumpSet hJ)
    have hxC : x ∈ bd S := hterm_bd J hJ x hxV (by rw [hterm]; exact Or.inl rfl)
    have hyC : y ∈ bd S := hterm_bd J hJ y hyV (by rw [hterm]; exact Or.inr rfl)
    have hpair : ∀ z ∈ Γ.V, ιV z ∈ terminals J → z ∈ ({x, y} : Set S) := by
      intro z hz hzt
      rw [hterm] at hzt
      rcases hzt with h | h
      · exact Or.inl (hiso.ιV_injOn hz hxV h)
      · exact Or.inr (hiso.ιV_injOn hz hyV (mem_singleton_iff.1 h))
    have hUW : jumpLine Γ ιE J ∩ otherPart Γ ιV ιE J ⊆ {x, y} := fun z hz =>
      hpair z (jumpLine_inter_otherPart_subset hdeg hiso hJ hz).1
        (jumpLine_inter_otherPart_subset hdeg hiso hJ hz).2
    have hUb : jumpLine Γ ιE J ∩ bd S ⊆ {x, y} := fun z hz =>
      hpair z (jumpLine_inter_bd_subset hprop hiso hJ hz).1
        (jumpLine_inter_bd_subset hprop hiso hJ hz).2
    have hcov := U_subset_jumpLine_union hiso h2 hJ.1 hJ.2.1 (edgeSet_nonempty_of_mem_jumpSet hJ)
    obtain ⟨Qs, Bs, hQ, hRQ, hB, hBC, hQbd⟩ := exists_disc_of_line hS cap hC rfl hline
      isClosed_otherPart hUW hUb hxC hyC hxy fun F hF hFW =>
        hgood F x y hF hxV hyV fun z hz => hFW ⟨hz.1, hcov hz.2⟩
    exact ⟨x, y, Qs, Bs, hxV, hyV, hxC, hyC, hxy, hterm, hline, hQ, hRQ, hB, hBC, hQbd⟩
  choose! xf yf Qf Bf hxV hyV hxC hyC hxy hterm hline hQ hRQ hB hBC hQbd using hex
  have hfin : (jumpSet Γ_sub B0).Finite := jumpSet_finite hdeg
  set I := hfin.toFinset
  have hI : ∀ {J}, J ∈ I ↔ J ∈ jumpSet Γ_sub B0 := fun {J} => hfin.mem_toFinset
  have hpair' : ∀ J ∈ jumpSet Γ_sub B0, ∀ z ∈ Γ.V, ιV z ∈ terminals J →
      cap.emb z ∈ ({cap.emb (xf J), cap.emb (yf J)} : Set Shat) := by
    intro J hJ z hz hzt
    rw [hterm J hJ] at hzt
    rcases hzt with h | h
    · exact Or.inl (congrArg cap.emb (hiso.ιV_injOn hz (hxV J hJ) h))
    · exact Or.inr (congrArg cap.emb (hiso.ιV_injOn hz (hyV J hJ) (mem_singleton_iff.1 h)))
  have hJD : IsJumpDiscs R I (fun J => cap.emb '' jumpLine Γ ιE J) Qf Bf (cap.emb ∘ xf)
      (cap.emb ∘ yf) := by
    refine ⟨fun J hJ => GM07.image_line hemb (hline J (hI.1 hJ)),
      fun J hJ h => hxy J (hI.1 hJ) (hinj h), fun J hJ => ?_,
      fun J hJ => by rw [hRbd]; exact mem_image_of_mem _ (hxC J (hI.1 hJ)),
      fun J hJ => by rw [hRbd]; exact mem_image_of_mem _ (hyC J (hI.1 hJ)),
      fun J hJ => hQ J (hI.1 hJ), fun J hJ => hRQ J (hI.1 hJ), fun J hJ => hB J (hI.1 hJ),
      fun J hJ => by rw [hRbd]; exact hBC J (hI.1 hJ), fun J hJ => hQbd J (hI.1 hJ),
      fun J hJ K hK hJK => ?_⟩
    · have hJ' := hI.1 hJ
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨⟨z, hz, rfl⟩, hzR⟩
        obtain ⟨hzV, hzt⟩ := jumpLine_inter_bd_subset hprop hiso hJ' ⟨hz, hembR hzR⟩
        exact hpair' J hJ' z hzV hzt
      · rintro _ (h | h)
        · rw [h]
          exact ⟨mem_image_of_mem _ (hline J hJ').left_mem, hCR (hxC J hJ')⟩
        · rw [mem_singleton_iff.1 h]
          exact ⟨mem_image_of_mem _ (hline J hJ').right_mem, hCR (hyC J hJ')⟩
    · have hJ' := hI.1 hJ
      have hK' := hI.1 hK
      rintro _ ⟨⟨z, hz, rfl⟩, ⟨z', hz', hzz'⟩⟩
      rw [hinj hzz'] at hz'
      obtain ⟨hzV, hzt⟩ := jumpLine_inter_otherPart_subset hdeg hiso hJ'
        ⟨hz, jumpLine_subset_otherPart hdeg hJ' hK' hJK hz'⟩
      exact hCR (hterm_bd J hJ' z hzV hzt)
  obtain ⟨X, hX, hRX, hUJX⟩ := hJD.exists_disc cap.isSurface hT hns hR
  -- `X` holds `U(Γ)`.
  have hUX : cap.emb '' Γ.U ⊆ X := by
    rintro _ ⟨z, hz, rfl⟩
    rcases U_subset_bd_union_jumpLine hdeg hiso hK hz with hzb | hzJ
    · exact hRX (hCR hzb)
    · obtain ⟨J, hJ, hzJ⟩ := mem_iUnion₂.1 hzJ
      exact hUJX J (hI.2 hJ) (mem_image_of_mem _ hzJ)
  exact ⟨X, hX, hRX, hUX⟩

end LastStep
end GM21
end GraphMinor
