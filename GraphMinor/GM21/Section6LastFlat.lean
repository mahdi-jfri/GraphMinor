module

public import GraphMinor.GM21.Section6LastTools
import GraphMinor.GM06.RegionLocal
import GraphMinor.GM07.FlatEdges
import GraphMinor.GM07.Section11
import GraphMinor.GM07.Section11c
import GraphMinor.GM11.FlatCover
import GraphMinor.GM11.Solid
import GraphMinor.Surface.DiscArcs

/-!
# Graph Minors XXI, (6.3), the last step: the disc around `R ∪ U(Γ)` from VII (11.10)

The paper says (page 29 of the preprint): "From (4), it follows in particular that every
$\Sigma$-jump $J$ is homotopic in $\hat{\Sigma}$ to the lines in $bd(\Sigma)$ joining the ends of $J$.
Let $R$ be the closure in $\hat{\Sigma}$ of $\hat{\Sigma} \setminus \Sigma$ ... It follows that every
$O$-arc in $R \cup U(\Gamma)$ is null-homotopic in $\hat{\Sigma}$. By theorem (11.10) of [5] there is
a closed disc $\Delta \subseteq \hat{\Sigma}$ with $R \cup U(\Gamma) \subseteq \Delta$."

We work in a closed connected surface `T` that is not a sphere (the capped surface `Σ̂`), with a closed
disc `R` (the pasted disc). Each index `j` gives a line `U j` (a jump) with ends `x j ≠ y j` in `bd(R)`
and no other point in `R`, and a closed disc `Q j` whose boundary is `U j` together with a line `B j`
of `bd(R)` with the same ends (`IsJumpDiscs`). The disc `Q j` comes from claim (4).

* `exists_line_homotopy`: inside `Q j`, the jump `U j` is homotopic to `B j` with its ends fixed. This
  is the paper's "every $\Sigma$-jump $J$ is homotopic in $\hat{\Sigma}$ to the lines in
  $bd(\Sigma)$ joining the ends of $J$".
* `IsJumpDiscs.isFlat`: these homotopies, together, deform `Z = R ∪ ⋃ U j` into `R` with `R` fixed.
  So every closed curve in `Z` is homotopic to one in the disc `R`, and is null-homotopic. This is
  "every $O$-arc in $R \cup U(\Gamma)$ is null-homotopic", for all closed curves at once.
* `IsJumpDiscs.isSolid`: `Z` is closed and locally arc-wise connected.
* `IsJumpDiscs.exists_disc`: by VII (11.10) (`GM07.theorem_11_10_proof`), `Z` is all of `T` or lies
  in a closed disc. It is not all of `T`, since the outside of a closed disc of a surface that is not
  a sphere is not flat (`GM11.not_flat_compl_disc`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Topology GraphMinor.Surface GraphMinor.GM11 Metric unitInterval

variable {T : Type} [TopologicalSpace T] [T2Space T] {ι : Type*}

/-- The discs of the jumps, in the capped surface: lines `U j` with ends `x j ≠ y j` in `bd(R)`, and
closed discs `Q j` with boundary `U j ∪ B j`, where `B j` is a line of `bd(R)` with ends `x j, y j`.
Two of the lines meet only in `R`. -/
structure IsJumpDiscs (R : Set T) (M : Finset ι) (U Q B : ι → Set T) (x y : ι → T) : Prop where
  line : ∀ j ∈ M, IsLineWithEnds (U j) (x j) (y j)
  ne : ∀ j ∈ M, x j ≠ y j
  inter_R : ∀ j ∈ M, U j ∩ R = {x j, y j}
  x_mem : ∀ j ∈ M, x j ∈ discBd R
  y_mem : ∀ j ∈ M, y j ∈ discBd R
  disc : ∀ j ∈ M, IsClosedDisc (Q j)
  R_sub : ∀ j ∈ M, R ⊆ Q j
  arc : ∀ j ∈ M, IsLineWithEnds (B j) (x j) (y j)
  arc_sub : ∀ j ∈ M, B j ⊆ discBd R
  bd_eq : ∀ j ∈ M, discBd (Q j) = U j ∪ B j
  pair : ∀ j ∈ M, ∀ k ∈ M, j ≠ k → U j ∩ U k ⊆ R

omit [T2Space T] in
/-- **A jump is homotopic to the line of the cuff.** Two paths `ℓ, β` with the same ends in a closed
disc `Q` are homotopic in `Q` with the ends fixed: in a chart of `Q`, move along straight lines. -/
theorem exists_line_homotopy {Q : Set T} (hQ : IsClosedDisc Q) {a b : T} {ℓ β : I → T}
    (hℓ : Continuous ℓ) (hβ : Continuous β) (hℓQ : ∀ t, ℓ t ∈ Q) (hβQ : ∀ t, β t ∈ Q)
    (hℓ0 : ℓ 0 = a) (hℓ1 : ℓ 1 = b) (hβ0 : β 0 = a) (hβ1 : β 1 = b) :
    ∃ H : I × I → T, Continuous H ∧ (∀ t, H (t, 0) = ℓ t) ∧ (∀ t, H (t, 1) = β t) ∧
      (∀ s, H (0, s) = a) ∧ (∀ s, H (1, s) = b) := by
  obtain ⟨h, g, c⟩ := hQ.exists_isChart
  let m : I × I → ℂ := fun p => (1 - (p.2 : ℝ)) • h (ℓ p.1) + (p.2 : ℝ) • h (β p.1)
  have hm : ∀ p, m p ∈ closedBall (0 : ℂ) 1 := fun p =>
    convex_closedBall (0 : ℂ) 1 (c.hm (hℓQ p.1)) (c.hm (hβQ p.1)) (by linarith [p.2.2.2])
      p.2.2.1 (by ring)
  have hmc : Continuous m := by
    have h1 : Continuous fun t => h (ℓ t) := c.hc.comp_continuous hℓ hℓQ
    have h2 : Continuous fun t => h (β t) := c.hc.comp_continuous hβ hβQ
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
      (h1.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_snd).smul (h2.comp continuous_fst))
  refine ⟨fun p => g (m p), c.gc.comp_continuous hmc hm, fun t => ?_, fun t => ?_,
    fun s => ?_, fun s => ?_⟩
  · simp only [m, Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
    exact c.gh (hℓQ t)
  · simp only [m, Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]
    exact c.gh (hβQ t)
  · simp only [m, hℓ0, hβ0, ← add_smul, sub_add_cancel, one_smul]
    rw [c.gh (hℓ0 ▸ hℓQ 0)]
  · simp only [m, hℓ1, hβ1, ← add_smul, sub_add_cancel, one_smul]
    rw [c.gh (hℓ1 ▸ hℓQ 1)]

omit [T2Space T] in
/-- A closed curve in a closed disc is null-homotopic. -/
theorem null_of_subset_disc {R : Set T} (hR : IsClosedDisc R) (φ : C(Circle, T))
    (hφ : ∀ θ, φ θ ∈ R) : ClosedCurveIsNullHomotopicIn univ φ := by
  obtain ⟨h, g, c⟩ := hR.exists_isChart
  let m : Circle × I → ℂ := fun p => (1 - (p.2 : ℝ)) • h (φ p.1)
  have hm : ∀ p, m p ∈ closedBall (0 : ℂ) 1 := fun p => by
    have := c.hm (hφ p.1)
    rw [mem_closedBall_zero_iff] at this ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [p.2.2.2])]
    nlinarith [p.2.2.1, p.2.2.2, norm_nonneg (h (φ p.1))]
  have hmc : Continuous m :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
      ((c.hc.comp_continuous φ.continuous hφ).comp continuous_fst)
  refine ⟨g 0, trivial, ⟨fun p => g (m p), c.gc.comp_continuous hmc hm⟩, fun _ => trivial,
    fun θ => ?_, fun θ => ?_⟩
  · change g ((1 - ((0 : I) : ℝ)) • h (φ θ)) = φ θ
    rw [Icc.coe_zero, sub_zero, one_smul, c.gh (hφ θ)]
  · change g ((1 - ((1 : I) : ℝ)) • h (φ θ)) = g 0
    rw [Icc.coe_one, sub_self, zero_smul]

omit [T2Space T] in
/-- Points of a set `X` near `x` are joined to `x` in `X` near `x`, if `X` is locally path-connected
in itself. -/
theorem locJoin_of_locallyPathConnected {X : Set T} [LocallyPathConnectedSpace X] {x : T}
    (hx : x ∈ X) : LocJoin X x := by
  intro A hA hxA
  have hV : IsOpen ((↑) ⁻¹' A : Set X) := hA.preimage continuous_subtype_val
  have hP := hV.pathComponentIn (⟨x, hx⟩ : X)
  obtain ⟨N, hN, hNe⟩ := isOpen_induced_iff.1 hP
  have hxN : (⟨x, hx⟩ : X) ∈ (↑) ⁻¹' N := by
    rw [hNe]; exact mem_pathComponentIn_self hxA
  refine ⟨N, hN, hxN, fun y hy => ?_⟩
  have hyP : (⟨y, hy.1⟩ : X) ∈ pathComponentIn ((↑) ⁻¹' A : Set X) ⟨x, hx⟩ := by
    rw [← hNe]; exact hy.2
  obtain ⟨γ, hγ⟩ := hyP
  refine ⟨γ.map continuous_subtype_val, fun t => ⟨(γ t).2, hγ t⟩⟩

section Flat

variable {R : Set T} {M : Finset ι} {U Q B : ι → Set T} {x y : ι → T}

/-- `R` with the jumps. -/
def jumpUnion (R : Set T) (M : Finset ι) (U : ι → Set T) : Set T := R ∪ ⋃ j ∈ M, U j

namespace IsJumpDiscs

variable (h : IsJumpDiscs R M U Q B x y)
include h

/-- `R ∪ ⋃ U j` is closed. -/
theorem isClosed_jumpUnion (hR : IsClosedDisc R) : IsClosed (jumpUnion R M U) :=
  hR.isClosed.union (isClosed_biUnion_finset fun j hj => (h.line j hj).isCompact.isClosed)

/-- **Every closed curve in `R ∪ U(Γ)` is null-homotopic.** The homotopies of the jumps onto the
lines of `bd(R)` (`exists_line_homotopy`) fit together to deform `R ∪ ⋃ U j` into `R`, keeping `R`
fixed. -/
theorem isFlat (hR : IsClosedDisc R) : IsFlat (jumpUnion R M U) := by
  classical
  -- The parametrizations and homotopies of the jumps.
  have hex : ∀ j ∈ M, ∃ (ℓ : I → T) (ℓ' : T → I) (H : I × I → T), Continuous ℓ ∧
      ContinuousOn ℓ' (U j) ∧ (∀ z ∈ U j, ℓ (ℓ' z) = z) ∧ (∀ t, ℓ' (ℓ t) = t) ∧
      ℓ 0 = x j ∧ ℓ 1 = y j ∧ Continuous H ∧ (∀ t, H (t, 0) = ℓ t) ∧ (∀ t, H (t, 1) ∈ R) ∧
      (∀ s, H (0, s) = x j) ∧ (∀ s, H (1, s) = y j) := by
    intro j hj
    obtain ⟨f, hf0, hf1⟩ := h.line j hj
    obtain ⟨b, hb0, hb1⟩ := h.arc j hj
    have hUQ : U j ⊆ Q j := fun z hz =>
      Surface.discBd_subset _ (by rw [h.bd_eq j hj]; exact Or.inl hz)
    have hBQ : B j ⊆ Q j := fun z hz =>
      Surface.discBd_subset _ (by rw [h.bd_eq j hj]; exact Or.inr hz)
    obtain ⟨H, hHc, hH0, hH1, hHa, hHb⟩ := exists_line_homotopy (h.disc j hj)
      (continuous_subtype_val.comp f.continuous) (continuous_subtype_val.comp b.continuous)
      (fun t => hUQ (f t).2) (fun t => hBQ (b t).2) hf0 hf1 hb0 hb1
    let ℓ' : T → I := fun z => if hz : z ∈ U j then f.symm ⟨z, hz⟩ else 0
    have hℓ' : ContinuousOn ℓ' (U j) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (U j).domRestrict ℓ' = f.symm := by
        funext z
        change (if hz : z.1 ∈ U j then f.symm ⟨z.1, hz⟩ else 0) = f.symm z
        simp only [z.2, ↓reduceDIte, Subtype.coe_eta]
      rw [this]
      exact f.symm.continuous
    refine ⟨fun t => (f t).1, ℓ', H, continuous_subtype_val.comp f.continuous, hℓ',
      fun z hz => ?_, fun t => ?_, hf0, hf1, hHc, hH0,
      fun t => by rw [hH1]; exact Surface.discBd_subset R (h.arc_sub j hj (b t).2), hHa, hHb⟩
    · change (f (if hz : z ∈ U j then f.symm ⟨z, hz⟩ else 0)).1 = z
      simp only [hz, ↓reduceDIte, Homeomorph.apply_symm_apply]
    · change (if hz : (f t).1 ∈ U j then f.symm ⟨(f t).1, hz⟩ else 0) = t
      simp only [(f t).2, ↓reduceDIte, Subtype.coe_eta, Homeomorph.symm_apply_apply]
  obtain ⟨z₀, -⟩ := hR.nonempty_discInt
  have : Nonempty T := ⟨z₀⟩
  choose! ℓ ℓ' H hℓc hℓ'c hℓℓ' hℓ'ℓ hℓ0 hℓ1 hHc hH0 hH1 hHa hHb using hex
  -- The deformation along one jump.
  let G : ι → T × I → T := fun j p => H j (ℓ' j p.1, p.2)
  -- At an end, it stays put.
  have hGend : ∀ j ∈ M, ∀ z ∈ U j, z ∈ R → ∀ s, G j (z, s) = z := by
    intro j hj z hz hzR s
    have : z ∈ ({x j, y j} : Set T) := h.inter_R j hj ▸ ⟨hz, hzR⟩
    rcases this with rfl | hzy
    · change H j (ℓ' j (x j), s) = x j
      rw [← hℓ0 j hj, hℓ'ℓ j hj, hHa j hj, hℓ0 j hj]
    · rw [mem_singleton_iff] at hzy
      subst hzy
      change H j (ℓ' j (y j), s) = y j
      rw [← hℓ1 j hj, hℓ'ℓ j hj, hHb j hj, hℓ1 j hj]
  -- The whole deformation.
  let D : T × I → T := fun p =>
    if hp : ∃ j ∈ M, p.1 ∈ U j ∧ p.1 ∉ R then G hp.choose p else p.1
  have hDR : ∀ z ∈ R, ∀ s, D (z, s) = z := by
    intro z hz s
    have : ¬ ∃ j ∈ M, z ∈ U j ∧ z ∉ R := fun ⟨_, _, _, h'⟩ => h' hz
    exact dite_eq_right_iff.2 fun hp => (this hp).elim
  have hDU : ∀ j ∈ M, ∀ z ∈ U j, ∀ s, D (z, s) = G j (z, s) := by
    intro j hj z hz s
    by_cases hzR : z ∈ R
    · rw [hDR z hzR, hGend j hj z hz hzR]
    · have hp : ∃ k ∈ M, z ∈ U k ∧ z ∉ R := ⟨j, hj, hz, hzR⟩
      have hspec := hp.choose_spec
      have hk : hp.choose = j := by
        by_contra hne
        exact hzR (h.pair _ hspec.1 j hj hne ⟨hspec.2.1, hz⟩)
      change (if hp : ∃ j ∈ M, z ∈ U j ∧ z ∉ R then G hp.choose (z, s) else z) = G j (z, s)
      simp only [hp, ↓reduceDIte, hk]
  -- Continuity on each piece, and so on the union.
  have hGc : ∀ j ∈ M, ContinuousOn (G j) (U j ×ˢ univ) := fun j hj =>
    (hHc j hj).comp_continuousOn
      (((hℓ'c j hj).comp continuousOn_fst fun p hp => hp.1).prodMk continuousOn_snd)
  have hDc : ContinuousOn D (jumpUnion R M U ×ˢ univ) := by
    have hpiece : ∀ s : Finset ι, s ⊆ M →
        ContinuousOn D ((R ∪ ⋃ j ∈ s, U j) ×ˢ (univ : Set I)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _
        simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty]
        exact (continuous_fst.continuousOn).congr fun p hp => hDR p.1 hp.1 p.2
      | insert k s hks ih =>
        intro hsub
        have hkM : k ∈ M := hsub (Finset.mem_insert_self k s)
        have heq : (R ∪ ⋃ j ∈ insert k s, U j) ×ˢ (univ : Set I) =
            ((R ∪ ⋃ j ∈ s, U j) ×ˢ univ) ∪ (U k ×ˢ univ) := by
          rw [Finset.set_biUnion_insert, ← union_prod]
          congr 1
          rw [Set.union_comm (U k), Set.union_assoc]
        rw [heq]
        refine (ih fun j hj => hsub (Finset.mem_insert_of_mem hj)).union_of_isClosed
          ((hGc k hkM).congr fun p hp => hDU k hkM p.1 hp.1 p.2) ?_ ?_
        · exact (hR.isClosed.union (isClosed_biUnion_finset fun j hj =>
            (h.line j (hsub (Finset.mem_insert_of_mem hj))).isCompact.isClosed)).prod isClosed_univ
        · exact (h.line k hkM).isCompact.isClosed.prod isClosed_univ
    exact hpiece M subset_rfl
  -- Every closed curve in the union deforms into `R`.
  intro φ hφ
  have hmem : ∀ θ, φ θ ∈ jumpUnion R M U := fun θ => hφ (mem_range_self θ)
  have hDin : ∀ z ∈ jumpUnion R M U, D (z, 0) = z ∧ D (z, 1) ∈ R := by
    intro z hz
    rcases hz with hzR | hzU
    · exact ⟨hDR z hzR 0, by rw [hDR z hzR 1]; exact hzR⟩
    · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 hzU
      rw [hDU j hj z hzj, hDU j hj z hzj]
      exact ⟨(hH0 j hj _).trans (hℓℓ' j hj z hzj), hH1 j hj _⟩
  let ψ : C(Circle × I, T) := ⟨fun p => D (φ p.1, p.2),
    hDc.comp_continuous (φ.continuous.prodMap continuous_id) fun p => ⟨hmem p.1, trivial⟩⟩
  let φ₁ : C(Circle, T) := ⟨fun θ => D (φ θ, 1), ψ.continuous.comp
    (continuous_id.prodMk continuous_const)⟩
  obtain ⟨c, -, hc⟩ := null_of_subset_disc hR φ₁ fun θ => (hDin _ (hmem θ)).2
  refine ⟨c, trivial, GM07.closedCurvesHomotopicIn_trans' ⟨ψ, fun _ => trivial, fun θ => ?_,
    fun _ => rfl⟩ hc⟩
  exact (hDin _ (hmem θ)).1

/-- `R ∪ ⋃ U j` is solid: closed and locally arc-wise connected. -/
theorem isSolid (hR : IsClosedDisc R) : IsSolid (jumpUnion R M U) := by
  classical
  refine ⟨isLocallyArcConnected_of_locJoin fun z hz A hA hzA => ?_, h.isClosed_jumpUnion hR⟩
  -- A neighbourhood for each piece: from the piece if `z` is in it, else the complement.
  have hpiece : ∀ X : Set T, IsClosed X → (z ∈ X → LocJoin X z) →
      ∃ N, IsOpen N ∧ z ∈ N ∧ ∀ w ∈ X ∩ N, JoinedIn (X ∩ A) z w := by
    intro X hX hJ
    by_cases hzX : z ∈ X
    · exact hJ hzX A hA hzA
    · exact ⟨Xᶜ, hX.isOpen_compl, hzX, fun w hw => (hw.2 hw.1).elim⟩
  have : LocallyPathConnectedSpace R := GM06.locallyPathConnectedSpace_of_isClosedDiscSpace hR
  obtain ⟨NR, hNRo, hzNR, hNR⟩ := hpiece R hR.isClosed fun hzR =>
    locJoin_of_locallyPathConnected hzR
  have hline : ∀ j ∈ M, ∃ N, IsOpen N ∧ z ∈ N ∧ ∀ w ∈ U j ∩ N, JoinedIn (U j ∩ A) z w := by
    intro j hj
    obtain ⟨f, -, -⟩ := h.line j hj
    have hr : range (Subtype.val ∘ f) = U j := by
      ext w
      exact ⟨fun ⟨t, ht⟩ => ht ▸ (f t).2, fun hw => ⟨f.symm ⟨w, hw⟩, by simp⟩⟩
    refine hpiece (U j) (h.line j hj).isCompact.isClosed fun hzU => ?_
    rw [← hr] at hzU ⊢
    exact locJoin_range (continuous_subtype_val.comp f.continuous) hzU
  choose! N hNo hzN hN using hline
  refine ⟨NR ∩ ⋂ j ∈ M, N j, hNRo.inter (isOpen_biInter_finset fun j hj => hNo j hj),
    ⟨hzNR, mem_iInter₂.2 fun j hj => hzN j hj⟩, fun w ⟨hw, hwN⟩ => ?_⟩
  have hmono : ∀ X ⊆ jumpUnion R M U, JoinedIn (X ∩ A) z w → JoinedIn (jumpUnion R M U ∩ A) z w :=
    fun X hX hj => hj.mono (inter_subset_inter_left A hX)
  rcases hw with hwR | hwU
  · exact hmono R subset_union_left (hNR w ⟨hwR, hwN.1⟩)
  · obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.1 hwU
    exact hmono (U j) (subset_union_right.trans' (subset_biUnion_of_mem (u := U) hj))
      (hN j hj w ⟨hwj, mem_iInter₂.1 hwN.2 j hj⟩)

/-- **The disc `Δ ⊇ R ∪ U(Γ)`** (Graph Minors XXI, proof of (6.3), page 29 of the preprint): "By
theorem (11.10) of [5] there is a closed disc $\Delta \subseteq \hat{\Sigma}$ with
$R \cup U(\Gamma) \subseteq \Delta$." -/
theorem exists_disc [ConnectedSpace T] (hS : IsSurface T) (hT : IsClosedSurface T)
    (hns : ¬ IsSphere T) (hR : IsClosedDisc R) :
    ∃ X, IsClosedDisc X ∧ R ⊆ X ∧ ∀ j ∈ M, U j ⊆ X := by
  rcases GM07.theorem_11_10_proof hS (h.isSolid hR) (h.isFlat hR) with huniv | ⟨X, hX, hZX⟩
  · have hf := h.isFlat hR
    rw [huniv] at hf
    exact (not_flat_compl_disc hT hns hR (subset_univ _) (GM07.IsFlat.flat hf)).elim
  · exact ⟨X, hX, subset_union_left.trans hZX, fun j hj =>
      (subset_biUnion_of_mem (u := U) hj).trans (subset_union_right.trans hZX)⟩

end IsJumpDiscs

end Flat

end LastStep
end GM21
end GraphMinor
