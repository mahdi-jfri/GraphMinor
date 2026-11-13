module

public import GraphMinor.GM08.Defs6to18
public import GraphMinor.GM12.Section3MeetingDiscs
import GraphMinor.GM08.Section6CoverSphere

@[expose] public section

/-!
# Graph Minors VIII, Section 6: Foundations on a Disc

Formalization of Section 6 ((6.2)–(6.7)) of Robertson and Seymour,
*Graph Minors. VIII. A Kuratowski theorem for general surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288 (pages 263–267).
-/

namespace GraphMinor
namespace GM08

open Set Topology Surface

universe u

variable {S : Type u} [TopologicalSpace S]

local notation "𝕀" => unitInterval

/-- Strengthening of `Surface.exists_disc_cover` (`GraphMinor/Surface/DiscGrow.lean`) that also
records `discBd D' ⊆ discBd D ∪ P`. -/
theorem exists_disc_cover_with_bd [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {Y P : Set S}
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    (hPY : P ⊆ Y) (hP : IsOArc P) {x y : S} (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y)
    (n : ℕ) : ∀ (D : Set S) (F : Set (Set S)), D ⊆ Y → IsClosedDisc D → x ∈ D → y ∈ D → F.Finite →
      F.ncard ≤ n → (∀ J ∈ F, IsPreconnected J) → ⋃₀ F = P \ D →
      ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ P ⊆ D' ∧ discBd D' ⊆ discBd D ∪ P := by
  obtain ⟨φ⟩ := id hP
  let j : Circle → S := fun w => (φ w).1
  have hjc : Continuous j := continuous_subtype_val.comp φ.continuous
  have hji : Function.Injective j := fun _ _ h => φ.injective (Subtype.ext h)
  have hjemb : IsEmbedding j := (hjc.isClosedEmbedding hji).isEmbedding
  have hjr : range j = P := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (φ w).2
    · intro hz
      exact ⟨φ.symm ⟨z, hz⟩, by simp [j]⟩
  induction n with
  | zero =>
    intro D F hDY hD hxD hyD hF hc _ h2
    have hF0 : F = ∅ := (Set.ncard_eq_zero hF).mp (Nat.le_zero.mp hc)
    rw [hF0, sUnion_empty] at h2
    exact ⟨D, hDY, hD, subset_rfl, sdiff_eq_empty.mp h2.symm, subset_union_left⟩
  | succ n ih =>
    intro D F hDY hD hxD hyD hF hc h1 h2
    by_cases hsub : P ⊆ D
    · exact ⟨D, hDY, hD, subset_rfl, hsub, subset_union_left⟩
    obtain ⟨z, hzP, hzD⟩ := not_subset.mp hsub
    rw [← hjr] at hzP
    obtain ⟨z', rfl⟩ := hzP
    have hx' : x ∈ range j := hjr ▸ hx
    have hy' : y ∈ range j := hjr ▸ hy
    obtain ⟨x', rfl⟩ := hx'
    obtain ⟨y', rfl⟩ := hy'
    have hT : IsClosed (j ⁻¹' D) := hD.isClosed.preimage hjc
    obtain ⟨a, b, hab, hcov, ha0, ha1, hamid, hzr⟩ := exists_circle_chord hT (z := z') (x := x')
      (y := y') hzD hxD hyD fun h => hxy (congrArg j h)
    let ℓ : 𝕀 → S := fun r => j (a r)
    have hℓ : IsArcMap ℓ := ⟨hjc.comp hab.1.1, hji.comp hab.1.2⟩
    have hℓP : range ℓ ⊆ P := by
      rintro _ ⟨r, rfl⟩
      exact hjr ▸ mem_range_self _
    have hmeet : ∀ r, ℓ r ∈ D → r = 0 ∨ r = 1 := fun r hr => by
      by_contra hcon
      push Not at hcon
      exact hamid r hcon.1 hcon.2 hr
    have hbdend : ∀ r₀ : 𝕀, ℓ r₀ ∈ D → r₀ ∈ closure (Ioo (0 : 𝕀) 1) → ℓ r₀ ∈ discBd D := by
      intro r₀ h3 h4
      by_contra hcon
      have hopen := (hD.isOpen_discInt hman).preimage hℓ.1
      obtain ⟨r, hr1, hr2⟩ := mem_closure_iff.mp h4 _ hopen ⟨h3, hcon⟩
      rcases hmeet r hr1.1 with rfl | rfl
      · exact lt_irrefl _ hr2.1
      · exact lt_irrefl _ hr2.2
    have hcl : closure (Ioo (0 : 𝕀) 1) = Icc 0 1 := closure_Ioo zero_ne_one
    obtain ⟨D₁, hD₁Y, hD₁, hDD₁, hℓD₁, hbdD₁⟩ := exists_disc_of_chord hman hDY hD H hℓ
      (hℓP.trans hPY) (hbdend 0 ha0 (hcl ▸ ⟨le_rfl, zero_le_one⟩))
      (hbdend 1 ha1 (hcl ▸ ⟨zero_le_one, le_rfl⟩)) hmeet
    classical
    let F₁ : Set (Set S) := {J ∈ F | Disjoint J D₁}
    have hF₁sub : F₁ ⊆ F := fun J hJ => hJ.1
    have hF₁fin : F₁.Finite := hF.subset hF₁sub
    obtain ⟨J₀, hJ₀, hzJ₀⟩ : j z' ∈ ⋃₀ F := by
      rw [h2]
      exact ⟨hjr ▸ mem_range_self _, hzD⟩
    have hzD₁ : j z' ∈ D₁ := by
      obtain ⟨r, rfl⟩ := hzr
      exact hℓD₁ ⟨r, rfl⟩
    have hJ₀F₁ : J₀ ∉ F₁ := fun h => Set.disjoint_left.mp h.2 hzJ₀ hzD₁
    have hcount : F₁.ncard ≤ n := by
      have h5 : F₁.ncard < F.ncard := Set.ncard_lt_ncard
        ⟨hF₁sub, fun h => hJ₀F₁ (h hJ₀)⟩ hF
      omega
    have hU : ⋃₀ F₁ = P \ D₁ := by
      ext w
      constructor
      · rintro ⟨J, hJ, hw⟩
        have h6 : w ∈ P \ D := h2 ▸ mem_sUnion_of_mem hw hJ.1
        exact ⟨h6.1, fun h => Set.disjoint_left.mp hJ.2 hw h⟩
      · rintro ⟨hwP, hwD₁⟩
        have hwD : w ∉ D := fun h => hwD₁ (hDD₁ h)
        obtain ⟨J, hJ, hwJ⟩ : w ∈ ⋃₀ F := by
          rw [h2]
          exact ⟨hwP, hwD⟩
        have hJP : J ⊆ P \ D := by
          rw [← h2]
          exact subset_sUnion_of_mem hJ
        refine ⟨J, ⟨hJ, ?_⟩, hwJ⟩
        have hJ'p : IsPreconnected (j ⁻¹' J) := by
          rw [← hjemb.isInducing.isPreconnected_image,
            image_preimage_eq_of_subset (by rw [hjr]; exact hJP.trans sdiff_subset)]
          exact h1 J hJ
        have hJℓ : Disjoint J (range ℓ) := by
          rw [Set.disjoint_left]
          rintro v hv ⟨r, rfl⟩
          have hvend : r ≠ 0 ∧ r ≠ 1 := by
            constructor
            · rintro rfl
              exact (hJP hv).2 ha0
            · rintro rfl
              exact (hJP hv).2 ha1
          have hw' : w ∈ range j := hjr ▸ hwP
          obtain ⟨w', rfl⟩ := hw'
          have hsep := hJ'p (range b)ᶜ (range a)ᶜ (isCompact_range hab.2.1).isClosed.isOpen_compl
            (isCompact_range hab.1.1).isClosed.isOpen_compl ?_ ?_ ?_
          · obtain ⟨u, -, h7, h8⟩ := hsep
            have : u ∈ range a ∪ range b := hcov ▸ mem_univ u
            exact this.elim h8 h7
          · intro u hu
            by_cases hua : u ∈ range a
            · refine .inl ?_
              obtain ⟨s, rfl⟩ := hua
              rintro ⟨t, ht⟩
              have hs01 : s ≠ 0 ∧ s ≠ 1 := by
                constructor
                · rintro rfl
                  exact (hJP hu).2 ha0
                · rintro rfl
                  exact (hJP hu).2 ha1
              rcases hab.5 s t ht.symm with ⟨h9, -⟩ | ⟨h9, -⟩
              · exact hs01.1 h9
              · exact hs01.2 h9
            · exact .inr hua
          · refine ⟨a r, hv, ?_⟩
            rintro ⟨t, ht⟩
            rcases hab.5 r t ht.symm with ⟨h9, -⟩ | ⟨h9, -⟩
            · exact hvend.1 h9
            · exact hvend.2 h9
          · refine ⟨w', hwJ, ?_⟩
            rintro ⟨t, ht⟩
            exact hwD₁ (hℓD₁ ⟨t, by show j (a t) = j w'; rw [ht]⟩)
        have hJbd : Disjoint J (discBd D₁) := by
          rw [Set.disjoint_left]
          intro v hv hv'
          rcases hbdD₁ hv' with h7 | h7
          · exact (hJP hv).2 (discBd_subset D h7)
          · exact Set.disjoint_left.mp hJℓ hv h7
        rcases hD₁.side hman (h1 J hJ) hJbd with h7 | h7
        · exact absurd (h7 hwJ).1 hwD₁
        · exact h7
    obtain ⟨D', h3, h4, h5, h6, h7⟩ := ih D₁ F₁ hD₁Y hD₁ (hDD₁ hxD) (hDD₁ hyD) hF₁fin hcount
      (fun J hJ => h1 J hJ.1) hU
    refine ⟨D', h3, h4, hDD₁.trans h5, h6, ?_⟩
    refine h7.trans (union_subset ?_ subset_union_right)
    exact hbdD₁.trans (union_subset_union_right _ hℓP)

/-- If `F₂ \ F₁` is a finite union of preconnected sets and `D` is a closed disc with boundary `F₁`,
then `F₂ \ D` is also a finite union of preconnected sets. -/
theorem finConn_diff_disc_of_finConn_diff_bd [T2Space S] (hman : ∀ x : S, IsManifoldPoint x)
    {D F₁ F₂ : Set S} (hD : IsClosedDisc D) (hb : discBd D = F₁) (hfin : FinConn (F₂ \ F₁)) :
    FinConn (F₂ \ D) := by
  obtain ⟨K, hKfin, hKconn, hKunion⟩ := hfin
  classical
  let K' : Set (Set S) := {J ∈ K | Disjoint J D}
  refine ⟨K', hKfin.subset (fun _ h => h.1), fun J hJ => hKconn J hJ.1, ?_⟩
  ext w
  constructor
  · rintro ⟨J, ⟨hJK, hJD⟩, hwJ⟩
    have hw : w ∈ F₂ \ F₁ := hKunion ▸ mem_sUnion_of_mem hwJ hJK
    exact ⟨hw.1, Set.disjoint_left.mp hJD hwJ⟩
  · rintro ⟨hwF₂, hwD⟩
    have hwF₁ : w ∉ F₁ := fun h => hwD (discBd_subset D (hb.symm ▸ h))
    have hw : w ∈ ⋃₀ K := hKunion.symm ▸ ⟨hwF₂, hwF₁⟩
    obtain ⟨J, hJK, hwJ⟩ := hw
    have hJsub : J ⊆ F₂ \ F₁ := hKunion ▸ subset_sUnion_of_mem hJK
    have hJbd : Disjoint J (discBd D) := by
      rw [hb]
      exact Set.disjoint_left.mpr fun x hx hxF₁ => (hJsub hx).2 hxF₁
    rcases hD.side hman (hKconn J hJK) hJbd with hin | hout
    · exact absurd (hin hwJ).1 hwD
    · exact ⟨J, ⟨hJK, hout⟩, hwJ⟩

/-- On a sphere `S`, the boundary `discBd D'` of any closed disc `D'` is contained in the closure
of `D'ᶜ`, and `D'ᶜ` equals `discInt Δ_other` for the complementary closed disc `Δ_other`. -/
theorem exists_compl_eq_discInt_of_sphere
    (hsph : IsSphere S)
    {D' : Set S} (hD' : IsClosedDisc D') :
    ∃ Δ' : Set S, IsClosedDisc Δ' ∧ discBd Δ' = discBd D' ∧ D'ᶜ = discInt Δ' := by
  obtain ⟨Δ₁, Δ₂, _, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, _, huniq⟩ :=
    sphere_disc S hsph (discBd D') hD'.isOArc_discBd
  rcases huniq D' hD' rfl with rfl | rfl
  · refine ⟨Δ₂, hΔ₂, hb₂.trans hb₁.symm, ?_⟩
    ext x
    constructor
    · intro hx
      have hxu : x ∈ D' ∪ Δ₂ := hcup ▸ mem_univ x
      rcases hxu with h1 | h2
      · exact absurd h1 hx
      · refine ⟨h2, fun hb => hx ?_⟩
        rw [hb₂, ← hcap] at hb
        exact hb.1
    · rintro ⟨hx2, hxb⟩ hx1
      apply hxb
      rw [hb₂, ← hcap]
      exact ⟨hx1, hx2⟩
  · refine ⟨Δ₁, hΔ₁, hb₁.trans hb₂.symm, ?_⟩
    ext x
    constructor
    · intro hx
      have hxu : x ∈ Δ₁ ∪ D' := hcup ▸ mem_univ x
      rcases hxu with h1 | h2
      · refine ⟨h1, fun hb => hx ?_⟩
        rw [hb₁, ← hcap] at hb
        exact hb.2
      · exact absurd h2 hx
    · rintro ⟨hx1, hxb⟩ hx2
      apply hxb
      rw [hb₁, ← hcap]
      exact ⟨hx1, hx2⟩

theorem discBd_subset_closure_compl
    (hsph : IsSphere S)
    {D' : Set S} (hD' : IsClosedDisc D') :
    discBd D' ⊆ closure (D'ᶜ) := by
  obtain ⟨Δ', hΔ', hbΔ', hcompl⟩ := exists_compl_eq_discInt_of_sphere hsph hD'
  rw [hcompl, ← hbΔ']
  exact (discBd_subset Δ').trans hΔ'.subset_closure_discInt

/-- Given a closed disc `D'` on a sphere `S` with `z ∉ D'`, the component of `(discBd D')ᶜ`
containing `z` equals `D'ᶜ`. -/
theorem connectedComponentIn_compl_discBd_eq_compl [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {D' : Set S} (hD' : IsClosedDisc D') {z : S} (hz : z ∉ D') :
    connectedComponentIn ((discBd D')ᶜ) z = D'ᶜ := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hopen_int : IsOpen (discInt D') := hD'.isOpen_discInt hman
  have hopen_compl : IsOpen (D'ᶜ) := hD'.isClosed.isOpen_compl
  have hdisj : Disjoint (discInt D') (D'ᶜ) :=
    Set.disjoint_left.mpr fun x hx hx' => hx' hx.1
  have hcover : (discBd D')ᶜ ⊆ discInt D' ∪ D'ᶜ := fun x hx => by
    by_cases hxD : x ∈ D'
    · exact Or.inl ⟨hxD, hx⟩
    · exact Or.inr hxD
  have hz_mem : z ∈ (discBd D')ᶜ := fun h => hz (discBd_subset D' h)
  have hsub1 : connectedComponentIn ((discBd D')ᶜ) z ⊆ D'ᶜ := by
    rcases isPreconnected_connectedComponentIn.subset_or_subset hopen_int hopen_compl hdisj
      ((connectedComponentIn_subset _ _).trans hcover) with h | h
    · exact absurd (h (mem_connectedComponentIn hz_mem)).1 hz
    · exact h
  refine Subset.antisymm hsub1 ?_
  obtain ⟨Δ', hΔ', _, hcompl⟩ := exists_compl_eq_discInt_of_sphere hsph hD'
  have hconn : IsPreconnected (D'ᶜ) := hcompl ▸ hΔ'.isPreconnected_discInt
  exact hconn.subset_connectedComponentIn hz fun x hx hb => hx (discBd_subset D' hb)

/-- Closed-disc form of (6.2): under the hypotheses of (6.2), there is a closed disc `D' ⊆ {z}ᶜ`
containing `F₁ ∪ F₂` with `discBd D' ⊆ F₁ ∪ F₂`. -/
theorem exists_disc_cover_sphere [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {F₁ F₂ : Set S} (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    (hcard : (F₁ ∩ F₂).Nontrivial)
    {z : S} (hz : z ∉ F₁ ∪ F₂) :
    ∃ D' : Set S, IsClosedDisc D' ∧ z ∉ D' ∧ F₁ ∪ F₂ ⊆ D' ∧ discBd D' ⊆ F₁ ∪ F₂ := by
  exact exists_disc_cover_sphere_unrestricted hS hsph hF₁ hF₂ hcard hz

/-- **(6.2)** Let `S` be a sphere and let `F₁, F₂` be O-arcs of `S` with `|F₁ ∩ F₂| ≥ 2`.
Let `z ∈ S - (F₁ ∪ F₂)`. Then there is an O-arc `F₃ ⊆ F₁ ∪ F₂` such that the component of
`S - F₃` which contains `z` contains no point of `F₁ ∪ F₂`.
(GM VIII Section 6, page 264.) -/
theorem theorem_6_2_proof [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {F₁ F₂ : Set S} (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    (hcard : (F₁ ∩ F₂).Nontrivial)
    {z : S} (hz : z ∉ F₁ ∪ F₂) :
    ∃ F₃ : Set S, IsOArc F₃ ∧ F₃ ⊆ F₁ ∪ F₂ ∧
      Disjoint (connectedComponentIn (F₃ᶜ) z) (F₁ ∪ F₂) := by
  obtain ⟨D', hD', hzD', hsubD', hbdD'⟩ :=
    exists_disc_cover_sphere hS hsph hF₁ hF₂ hcard hz
  refine ⟨discBd D', hD'.isOArc_discBd, hbdD', ?_⟩
  rw [connectedComponentIn_compl_discBd_eq_compl hS hsph hD' hzD']
  exact Set.disjoint_left.mpr fun x hxD' hxF => hxD' (hsubD' hxF)

/-- If `¬ (F₁ ∩ F₂).Nontrivial` for an O-arc `F₂`, then `F₂ \ F₁` is preconnected. -/
theorem isPreconnected_diff_of_not_nontrivial_inter {F₁ F₂ : Set S}
    (hF₂ : IsOArc F₂) (hnot : ¬ (F₁ ∩ F₂).Nontrivial) :
    IsPreconnected (F₂ \ F₁) := by
  by_cases hne : (F₁ ∩ F₂).Nonempty
  · obtain ⟨u, hu⟩ := hne
    have heq : F₂ \ F₁ = F₂ \ {u} := by
      ext x
      simp only [mem_sdiff, mem_singleton_iff]
      refine ⟨fun ⟨hx₂, hx₁⟩ => ⟨hx₂, fun h => hx₁ (h ▸ hu.1)⟩, fun ⟨hx₂, hxu⟩ => ⟨hx₂, ?_⟩⟩
      intro hx₁
      exact hxu (Set.not_nontrivial_iff.mp hnot ⟨hx₁, hx₂⟩ hu)
    rw [heq]
    exact (GM12.isPathConnected_oArc_diff hF₂ hu.2).isConnected.isPreconnected
  · have heq : F₂ \ F₁ = F₂ := by
      ext x
      simp only [mem_sdiff, and_iff_left_iff_imp]
      intro hx₂ hx₁
      exact hne ⟨x, hx₁, hx₂⟩
    rw [heq]
    exact hF₂.isPreconnected

/-- On a sphere `S`, if `D₁', D₂'` are closed discs with `z₁ ∉ D₁'`, `z₂ ∉ D₂'`, and `F` is an
O-arc contained in `D₁' ∩ D₂'` such that `z₁` and `z₂` lie in distinct components of `Fᶜ`, then
`discBd D₁' ∩ discBd D₂' ⊆ F`. -/
theorem inter_discBd_subset_of_distinct_components [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {D₁' D₂' F : Set S} (hD₁' : IsClosedDisc D₁') (hD₂' : IsClosedDisc D₂') (hF : IsOArc F)
    {z₁ z₂ : S} (hz₁ : z₁ ∉ D₁') (hz₂ : z₂ ∉ D₂')
    (hFD₁ : F ⊆ D₁') (hFD₂ : F ⊆ D₂')
    (hsep : connectedComponentIn (Fᶜ) z₁ ≠ connectedComponentIn (Fᶜ) z₂) :
    discBd D₁' ∩ discBd D₂' ⊆ F := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  intro x ⟨hx₁, hx₂⟩
  by_contra hxF
  have hopenF : IsOpen (Fᶜ) := hF.isCompact.isClosed.isOpen_compl
  have hopenC : IsOpen (connectedComponentIn (Fᶜ) x) := hopenF.connectedComponentIn
  have hxC : x ∈ connectedComponentIn (Fᶜ) x := mem_connectedComponentIn hxF
  have hcl₁ : x ∈ closure (D₁'ᶜ) := discBd_subset_closure_compl hsph hD₁' hx₁
  have hcl₂ : x ∈ closure (D₂'ᶜ) := discBd_subset_closure_compl hsph hD₂' hx₂
  obtain ⟨w₁, hw₁C, hw₁D⟩ := mem_closure_iff.mp hcl₁ _ hopenC hxC
  obtain ⟨w₂, hw₂C, hw₂D⟩ := mem_closure_iff.mp hcl₂ _ hopenC hxC
  obtain ⟨Δ₁', hΔ₁', _, hcompl₁⟩ := exists_compl_eq_discInt_of_sphere hsph hD₁'
  obtain ⟨Δ₂', hΔ₂', _, hcompl₂⟩ := exists_compl_eq_discInt_of_sphere hsph hD₂'
  have hconn₁ : IsPreconnected (D₁'ᶜ) := hcompl₁ ▸ hΔ₁'.isPreconnected_discInt
  have hconn₂ : IsPreconnected (D₂'ᶜ) := hcompl₂ ▸ hΔ₂'.isPreconnected_discInt
  have hsub₁ : D₁'ᶜ ⊆ Fᶜ := fun y hy hyF => hy (hFD₁ hyF)
  have hsub₂ : D₂'ᶜ ⊆ Fᶜ := fun y hy hyF => hy (hFD₂ hyF)
  have hz₁w₁ : z₁ ∈ connectedComponentIn (Fᶜ) w₁ :=
    hconn₁.subset_connectedComponentIn hw₁D hsub₁ hz₁
  have hz₂w₂ : z₂ ∈ connectedComponentIn (Fᶜ) w₂ :=
    hconn₂.subset_connectedComponentIn hw₂D hsub₂ hz₂
  have heq₁ : connectedComponentIn (Fᶜ) x = connectedComponentIn (Fᶜ) z₁ :=
    (connectedComponentIn_eq hw₁C).trans (connectedComponentIn_eq hz₁w₁)
  have heq₂ : connectedComponentIn (Fᶜ) x = connectedComponentIn (Fᶜ) z₂ :=
    (connectedComponentIn_eq hw₂C).trans (connectedComponentIn_eq hz₂w₂)
  exact hsep (heq₁.symm.trans heq₂)

/-- Closed-disc form of (6.3): under the hypotheses of (6.3), there exist closed discs `D₁', D₂'`
with `z₁ ∉ D₁'`, `z₂ ∉ D₂'`, `F₁ ∪ F₂ ⊆ D₁'`, `F₁ ∪ F₂ ⊆ D₂'`,
`discBd D₁' ∪ discBd D₂' ⊆ F₁ ∪ F₂`, and `discBd D₁' ∩ discBd D₂' ⊆ F₁ ∩ F₂`. -/
theorem exists_two_disc_covers_sphere [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {F₁ F₂ : Set S} (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    {z₁ z₂ : S} (hz₁ : z₁ ∉ F₁ ∪ F₂) (hz₂ : z₂ ∉ F₁ ∪ F₂)
    (hsep₁ : connectedComponentIn (F₁ᶜ) z₁ ≠ connectedComponentIn (F₁ᶜ) z₂)
    (hsep₂ : connectedComponentIn (F₂ᶜ) z₁ ≠ connectedComponentIn (F₂ᶜ) z₂) :
    ∃ D₁' D₂' : Set S, IsClosedDisc D₁' ∧ IsClosedDisc D₂' ∧
      z₁ ∉ D₁' ∧ z₂ ∉ D₂' ∧ F₁ ∪ F₂ ⊆ D₁' ∧ F₁ ∪ F₂ ⊆ D₂' ∧
      discBd D₁' ∪ discBd D₂' ⊆ F₁ ∪ F₂ ∧
      discBd D₁' ∩ discBd D₂' ⊆ F₁ ∩ F₂ := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hex : ∃ D₁' D₂' : Set S, IsClosedDisc D₁' ∧ IsClosedDisc D₂' ∧
      z₁ ∉ D₁' ∧ z₂ ∉ D₂' ∧ F₁ ∪ F₂ ⊆ D₁' ∧ F₁ ∪ F₂ ⊆ D₂' ∧
      discBd D₁' ⊆ F₁ ∪ F₂ ∧ discBd D₂' ⊆ F₁ ∪ F₂ := by
    by_cases hcard : (F₁ ∩ F₂).Nontrivial
    · obtain ⟨D₁', hD₁', hz₁D, hsub₁, hbd₁⟩ :=
        exists_disc_cover_sphere hS hsph hF₁ hF₂ hcard hz₁
      obtain ⟨D₂', hD₂', hz₂D, hsub₂, hbd₂⟩ :=
        exists_disc_cover_sphere hS hsph hF₁ hF₂ hcard hz₂
      exact ⟨D₁', D₂', hD₁', hD₂', hz₁D, hz₂D, hsub₁, hsub₂, hbd₁, hbd₂⟩
    · have hconn : IsPreconnected (F₂ \ F₁) :=
        isPreconnected_diff_of_not_nontrivial_inter hF₂ hcard
      obtain ⟨Δ₁₁, hΔ₁₁, hb₁₁, hz₁Δ₁₁⟩ := GM11.exists_disc_missing hS hsph hF₁
        isPreconnected_singleton (Set.disjoint_singleton_left.mpr fun h => hz₁ (Or.inl h))
      obtain ⟨Δ₁₂, hΔ₁₂, hb₁₂, hz₂Δ₁₂⟩ := GM11.exists_disc_missing hS hsph hF₁
        isPreconnected_singleton (Set.disjoint_singleton_left.mpr fun h => hz₂ (Or.inl h))
      obtain ⟨Δ₂₁, hΔ₂₁, hb₂₁, hz₁Δ₂₁⟩ := GM11.exists_disc_missing hS hsph hF₂
        isPreconnected_singleton (Set.disjoint_singleton_left.mpr fun h => hz₁ (Or.inr h))
      obtain ⟨Δ₂₂, hΔ₂₂, hb₂₂, hz₂Δ₂₂⟩ := GM11.exists_disc_missing hS hsph hF₂
        isPreconnected_singleton (Set.disjoint_singleton_left.mpr fun h => hz₂ (Or.inr h))
      have hz₁_not_11 : z₁ ∉ Δ₁₁ := Set.disjoint_right.mp hz₁Δ₁₁ rfl
      have hz₂_not_12 : z₂ ∉ Δ₁₂ := Set.disjoint_right.mp hz₂Δ₁₂ rfl
      have hz₁_not_21 : z₁ ∉ Δ₂₁ := Set.disjoint_right.mp hz₁Δ₂₁ rfl
      have hz₂_not_22 : z₂ ∉ Δ₂₂ := Set.disjoint_right.mp hz₂Δ₂₂ rfl
      have hdis_bd : Disjoint (F₂ \ F₁) (discBd Δ₁₁) := by
        rw [hb₁₁]
        exact disjoint_sdiff_left
      rcases hΔ₁₁.side hman hconn hdis_bd with hin | hout
      · have hF₂_sub : F₂ ⊆ Δ₁₁ := fun x hx => by
          by_cases hx₁ : x ∈ F₁
          · exact discBd_subset Δ₁₁ (hb₁₁ ▸ hx₁)
          · exact (hin ⟨hx, hx₁⟩).1
        have hF₁_sub_22 : F₁ ⊆ Δ₂₂ := by
          have hcomp₁ : connectedComponentIn (F₁ᶜ) z₁ = Δ₁₁ᶜ :=
            hb₁₁ ▸ connectedComponentIn_compl_discBd_eq_compl hS hsph hΔ₁₁ hz₁_not_11
          have hcomp₂ : connectedComponentIn (F₂ᶜ) z₂ = Δ₂₂ᶜ :=
            hb₂₂ ▸ connectedComponentIn_compl_discBd_eq_compl hS hsph hΔ₂₂ hz₂_not_22
          have hsub_c : Δ₁₁ᶜ ⊆ connectedComponentIn (F₂ᶜ) z₁ := by
            rw [← hcomp₁]
            exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
              (mem_connectedComponentIn fun h => hz₁ (Or.inl h))
              (hcomp₁ ▸ fun x hx hx₂ => hx (hF₂_sub hx₂))
          have hdis_c : Disjoint (connectedComponentIn (F₂ᶜ) z₁) (connectedComponentIn (F₂ᶜ) z₂) :=
            Set.disjoint_left.mpr fun x hx₁ hx₂ =>
              hsep₂ ((connectedComponentIn_eq hx₁).trans (connectedComponentIn_eq hx₂).symm)
          have hcompl_sub : Δ₁₁ᶜ ⊆ Δ₂₂ := fun x hx => by
            by_contra hx₂₂
            exact Set.disjoint_left.mp hdis_c (hsub_c hx) (hcomp₂.symm ▸ hx₂₂)
          rw [← hb₁₁]
          exact (discBd_subset_closure_compl hsph hΔ₁₁).trans
            (closure_minimal hcompl_sub hΔ₂₂.isClosed)
        exact ⟨Δ₁₁, Δ₂₂, hΔ₁₁, hΔ₂₂, hz₁_not_11, hz₂_not_22,
          union_subset (hb₁₁ ▸ discBd_subset Δ₁₁) hF₂_sub,
          union_subset hF₁_sub_22 (hb₂₂ ▸ discBd_subset Δ₂₂),
          hb₁₁ ▸ subset_union_left, hb₂₂ ▸ subset_union_right⟩
      · have hF₂_sub : F₂ ⊆ Δ₁₂ := by
          have hcomp₁₁ : connectedComponentIn (F₁ᶜ) z₁ = Δ₁₁ᶜ :=
            hb₁₁ ▸ connectedComponentIn_compl_discBd_eq_compl hS hsph hΔ₁₁ hz₁_not_11
          have hcomp₁₂ : connectedComponentIn (F₁ᶜ) z₂ = Δ₁₂ᶜ :=
            hb₁₂ ▸ connectedComponentIn_compl_discBd_eq_compl hS hsph hΔ₁₂ hz₂_not_12
          have hdis_c : Disjoint (connectedComponentIn (F₁ᶜ) z₁) (connectedComponentIn (F₁ᶜ) z₂) :=
            Set.disjoint_left.mpr fun x hx₁ hx₂ =>
              hsep₁ ((connectedComponentIn_eq hx₁).trans (connectedComponentIn_eq hx₂).symm)
          intro x hx
          by_cases hx₁ : x ∈ F₁
          · exact discBd_subset Δ₁₂ (hb₁₂ ▸ hx₁)
          · have hx_not_11 : x ∈ Δ₁₁ᶜ := Set.disjoint_left.mp hout ⟨hx, hx₁⟩
            by_contra hx₁₂
            exact Set.disjoint_left.mp hdis_c (hcomp₁₁.symm ▸ hx_not_11) (hcomp₁₂.symm ▸ hx₁₂)
        have hF₁_sub_21 : F₁ ⊆ Δ₂₁ := by
          have hcomp₁ : connectedComponentIn (F₁ᶜ) z₂ = Δ₁₂ᶜ :=
            hb₁₂ ▸ connectedComponentIn_compl_discBd_eq_compl hS hsph hΔ₁₂ hz₂_not_12
          have hcomp₂ : connectedComponentIn (F₂ᶜ) z₁ = Δ₂₁ᶜ :=
            hb₂₁ ▸ connectedComponentIn_compl_discBd_eq_compl hS hsph hΔ₂₁ hz₁_not_21
          have hsub_c : Δ₁₂ᶜ ⊆ connectedComponentIn (F₂ᶜ) z₂ := by
            rw [← hcomp₁]
            exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
              (mem_connectedComponentIn fun h => hz₂ (Or.inl h))
              (hcomp₁ ▸ fun x hx hx₂ => hx (hF₂_sub hx₂))
          have hdis_c : Disjoint (connectedComponentIn (F₂ᶜ) z₂) (connectedComponentIn (F₂ᶜ) z₁) :=
            Set.disjoint_left.mpr fun x hx₂ hx₁ =>
              hsep₂.symm ((connectedComponentIn_eq hx₂).trans (connectedComponentIn_eq hx₁).symm)
          have hcompl_sub : Δ₁₂ᶜ ⊆ Δ₂₁ := fun x hx => by
            by_contra hx₂₁
            exact Set.disjoint_left.mp hdis_c (hsub_c hx) (hcomp₂.symm ▸ hx₂₁)
          rw [← hb₁₂]
          exact (discBd_subset_closure_compl hsph hΔ₁₂).trans
            (closure_minimal hcompl_sub hΔ₂₁.isClosed)
        exact ⟨Δ₂₁, Δ₁₂, hΔ₂₁, hΔ₁₂, hz₁_not_21, hz₂_not_12,
          union_subset hF₁_sub_21 (hb₂₁ ▸ discBd_subset Δ₂₁),
          union_subset (hb₁₂ ▸ discBd_subset Δ₁₂) hF₂_sub,
          hb₂₁ ▸ subset_union_right, hb₁₂ ▸ subset_union_left⟩
  obtain ⟨D₁', D₂', hD₁', hD₂', hz₁D, hz₂D, hsub₁, hsub₂, hbd₁, hbd₂⟩ := hex
  refine ⟨D₁', D₂', hD₁', hD₂', hz₁D, hz₂D, hsub₁, hsub₂, union_subset hbd₁ hbd₂, ?_⟩
  exact subset_inter
    (inter_discBd_subset_of_distinct_components hS hsph hD₁' hD₂' hF₁ hz₁D hz₂D
      (subset_union_left.trans hsub₁) (subset_union_left.trans hsub₂) hsep₁)
    (inter_discBd_subset_of_distinct_components hS hsph hD₁' hD₂' hF₂ hz₁D hz₂D
      (subset_union_right.trans hsub₁) (subset_union_right.trans hsub₂) hsep₂)

/-- **(6.3)** Let `S` be a sphere and let `F₁, F₂` be O-arcs in `S`. Let `z₁, z₂ ∈ S - (F₁ ∪ F₂)`,
and be in distinct components of `S - Fᵢ` (`i = 1, 2`). Then there are O-arcs `F₃, F₄` in `S` such
that
(i) `F₃ ∪ F₄ ⊆ F₁ ∪ F₂`, `F₃ ∩ F₄ ⊆ F₁ ∩ F₂`,
(ii) the component of `S - F₃` which contains `z₁` contains no point of `F₁ ∪ F₂`,
(iii) the component of `S - F₄` which contains `z₂` contains no point of `F₁ ∪ F₂`.
(GM VIII Section 6, page 264.) -/
theorem theorem_6_3_proof [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {F₁ F₂ : Set S} (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    {z₁ z₂ : S} (hz₁ : z₁ ∉ F₁ ∪ F₂) (hz₂ : z₂ ∉ F₁ ∪ F₂)
    (hsep₁ : connectedComponentIn (F₁ᶜ) z₁ ≠ connectedComponentIn (F₁ᶜ) z₂)
    (hsep₂ : connectedComponentIn (F₂ᶜ) z₁ ≠ connectedComponentIn (F₂ᶜ) z₂) :
    ∃ F₃ F₄ : Set S, IsOArc F₃ ∧ IsOArc F₄ ∧
      F₃ ∪ F₄ ⊆ F₁ ∪ F₂ ∧ F₃ ∩ F₄ ⊆ F₁ ∩ F₂ ∧
      Disjoint (connectedComponentIn (F₃ᶜ) z₁) (F₁ ∪ F₂) ∧
      Disjoint (connectedComponentIn (F₄ᶜ) z₂) (F₁ ∪ F₂) := by
  obtain ⟨D₁', D₂', hD₁', hD₂', hz₁D, hz₂D, hsub₁, hsub₂, hbd_union, hbd_inter⟩ :=
    exists_two_disc_covers_sphere hS hsph hF₁ hF₂ hz₁ hz₂ hsep₁ hsep₂
  refine ⟨discBd D₁', discBd D₂', hD₁'.isOArc_discBd, hD₂'.isOArc_discBd,
    hbd_union, hbd_inter, ?_, ?_⟩
  · rw [connectedComponentIn_compl_discBd_eq_compl hS hsph hD₁' hz₁D]
    exact Set.disjoint_left.mpr fun x hxD hxF => hxD (hsub₁ hxF)
  · rw [connectedComponentIn_compl_discBd_eq_compl hS hsph hD₂' hz₂D]
    exact Set.disjoint_left.mpr fun x hxD hxF => hxD (hsub₂ hxF)

/-!
### Inside discs and sphere charts for (6.4)–(6.7)
-/

/-- Coordinates embedding a closed disc `Δ ⊆ S` into the sphere `OnePoint EuclideanPlane`
avoiding `∞`. -/
structure SphereDiscChart (Δ : Set S) (f : S → OnePoint EuclideanPlane)
    (f' : OnePoint EuclideanPlane → S) : Prop where
  fc : ContinuousOn f Δ
  f'c : ContinuousOn f' (f '' Δ)
  f'f : LeftInvOn f' f Δ
  ff' : LeftInvOn f f' (f '' Δ)
  infty_notMem : (OnePoint.infty : OnePoint EuclideanPlane) ∉ f '' Δ

theorem exists_sphereDiscChart {Δ : Set S} (hΔ : IsClosedDisc Δ) :
    ∃ f f', SphereDiscChart Δ f f' := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  obtain ⟨s', hs', hl⟩ := exists_inv_of_compact (isCompact_closedBall (0 : ℂ) 1)
    isOpenEmbedding_sph.continuous isOpenEmbedding_sph.injective.injOn
  let f : S → OnePoint EuclideanPlane := fun x => sph (h x)
  let f' : OnePoint EuclideanPlane → S := fun p => g (s' p)
  have hfΔ : f '' Δ = sph '' Metric.closedBall 0 1 := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨h x, c.hm hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨g z, c.gm hz, by show sph (h (g z)) = sph z; rw [c.hg hz]⟩
  have hf'f : LeftInvOn f' f Δ := fun x hx => by
    show g (s' (sph (h x))) = x
    rw [hl (c.hm hx), c.gh hx]
  have hff' : LeftInvOn f f' (f '' Δ) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hf'f hx]
  refine ⟨f, f', isOpenEmbedding_sph.continuous.comp_continuousOn c.hc, ?_, hf'f, hff', ?_⟩
  · rw [hfΔ]
    refine c.gc.comp hs' ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [hl hz]
    exact hz
  · rintro ⟨x, -, hx⟩
    exact sph_ne_infty (h x) hx

namespace SphereDiscChart

variable {Δ : Set S} {f : S → OnePoint EuclideanPlane} {f' : OnePoint EuclideanPlane → S}

theorem f'_subset (sc : SphereDiscChart Δ f f') {Z : Set (OnePoint EuclideanPlane)}
    (hZ : Z ⊆ f '' Δ) : f' '' Z ⊆ Δ := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hZ hp
  rw [sc.f'f hx]
  exact hx

theorem f'_f (sc : SphereDiscChart Δ f f') {X : Set S} (hX : X ⊆ Δ) :
    f' '' (f '' X) = X :=
  (sc.f'f.mono hX).image_image

theorem f_f' (sc : SphereDiscChart Δ f f') {Z : Set (OnePoint EuclideanPlane)}
    (hZ : Z ⊆ f '' Δ) : f '' (f' '' Z) = Z :=
  (sc.ff'.mono hZ).image_image

theorem injOn_f (sc : SphereDiscChart Δ f f') : InjOn f Δ := sc.f'f.injOn

theorem injOn_f' (sc : SphereDiscChart Δ f f') : InjOn f' (f '' Δ) := sc.ff'.injOn

theorem f_sdiff (sc : SphereDiscChart Δ f f') {X Y : Set S} (hX : X ⊆ Δ) (hY : Y ⊆ Δ) :
    f '' (X \ Y) = f '' X \ f '' Y := by
  ext p
  constructor
  · rintro ⟨x, ⟨hx, hxY⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    obtain rfl := sc.injOn_f (hY hy) (hX hx) he
    exact hxY hy
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun h => hn ⟨x, h, rfl⟩⟩, rfl⟩

theorem disc_f (sc : SphereDiscChart Δ f f') {D : Set S} (hD : D ⊆ Δ) (hd : IsClosedDisc D) :
    IsClosedDisc (f '' D) ∧ discBd (f '' D) = f '' discBd D :=
  hd.image (sc.fc.mono hD) (sc.f'c.mono (image_mono hD)) (sc.f'f.mono hD)

theorem discInt_f (sc : SphereDiscChart Δ f f') {D : Set S} (hD : D ⊆ Δ) (hd : IsClosedDisc D) :
    discInt (f '' D) = f '' discInt D := by
  rw [discInt, (sc.disc_f hD hd).2, ← sc.f_sdiff hD ((discBd_subset D).trans hD)]
  rfl

theorem oArc_f (sc : SphereDiscChart Δ f f') {F : Set S} (hF : F ⊆ Δ) (ho : IsOArc F) :
    IsOArc (f '' F) :=
  ho.image (sc.fc.mono hF) (sc.f'c.mono (image_mono hF)) (sc.f'f.mono hF)

theorem oArc_f' (sc : SphereDiscChart Δ f f') {Z : Set (OnePoint EuclideanPlane)}
    (hZ : Z ⊆ f '' Δ) (ho : IsOArc Z) : IsOArc (f' '' Z) :=
  ho.image (sc.f'c.mono hZ) (sc.fc.mono (sc.f'_subset hZ)) (sc.ff'.mono hZ)

theorem finConn_f (sc : SphereDiscChart Δ f f') {X : Set S} (hX : X ⊆ Δ) (hfin : FinConn X) :
    FinConn (f '' X) := by
  obtain ⟨K, hKfin, hKconn, hKunion⟩ := hfin
  refine ⟨(fun J => f '' J) '' K, hKfin.image _, ?_, ?_⟩
  · rintro _ ⟨J, hJK, rfl⟩
    have hJΔ : J ⊆ Δ := (subset_sUnion_of_mem hJK).trans (hKunion.symm ▸ hX)
    exact (hKconn J hJK).image f (sc.fc.mono hJΔ)
  · rw [sUnion_image, ← hKunion]
    ext p
    simp only [mem_iUnion, mem_image, exists_prop, mem_sUnion]
    constructor
    · rintro ⟨J, hJK, x, hxJ, rfl⟩
      exact ⟨x, ⟨J, hJK, hxJ⟩, rfl⟩
    · rintro ⟨x, ⟨J, hJK, hxJ⟩, rfl⟩
      exact ⟨J, hJK, x, hxJ, rfl⟩

theorem isInsideDisc_f'_of_infty_notMem (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {E' : Set (OnePoint EuclideanPlane)} (hE' : IsClosedDisc E')
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ E') (hbd : discBd E' ⊆ f '' Δ) :
    E' ⊆ f '' Δ ∧ IsInsideDisc Δ (f' '' discBd E') (f' '' E') ∧
      f '' (f' '' E') = E' ∧ f '' (f' '' discBd E') = discBd E' := by
  have hS' : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have : ConnectedSpace (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).2
  have hman' : ∀ p : OnePoint EuclideanPlane, IsManifoldPoint p :=
    fun p => (hS'.2.2 p).isManifoldPoint
  let F₃ : Set S := f' '' discBd E'
  have hF₃Δ : F₃ ⊆ Δ := sc.f'_subset hbd
  have hF₃ : IsOArc F₃ := sc.oArc_f' hbd hE'.isOArc_discBd
  have hfF₃ : f '' F₃ = discBd E' := sc.f_f' hbd
  obtain ⟨D₃, hD₃, _⟩ := disc_oArc Δ F₃ hΔ hF₃Δ hF₃
  obtain ⟨hd₃, hbd₃⟩ := sc.disc_f hD₃.1 hD₃.2.1
  rw [hD₃.2.2.1, hfF₃] at hbd₃
  have hnotcov : E' ∪ f '' D₃ ≠ univ := by
    intro hu
    have hmem : (OnePoint.infty : OnePoint EuclideanPlane) ∈ E' ∪ f '' D₃ := hu ▸ mem_univ _
    rcases hmem with h1 | h2
    · exact hinf h1
    · exact sc.infty_notMem (image_mono hD₃.1 h2)
  have heq : E' = f '' D₃ :=
    GM12.eq_of_discBd_eq_of_union_ne_univ hman' hE' hd₃ hbd₃.symm hnotcov
  have hE'Δ : E' ⊆ f '' Δ := heq ▸ image_mono hD₃.1
  have hf'E' : f' '' E' = D₃ := by
    rw [heq, sc.f'_f hD₃.1]
  refine ⟨hE'Δ, hf'E'.symm ▸ hD₃, sc.f_f' hE'Δ, hfF₃⟩

end SphereDiscChart

theorem subset_of_discInt_meets_sphere
    {D₁' D₂' : Set (OnePoint EuclideanPlane)}
    (hD₁' : IsClosedDisc D₁') (hD₂' : IsClosedDisc D₂')
    (hbd : Disjoint (discInt D₁') (discBd D₂'))
    (hne : (D₁' ∩ discInt D₂').Nonempty) :
    D₁' ⊆ D₂' ∧ discInt D₁' ⊆ discInt D₂' := by
  have hS' : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hman' : ∀ p : OnePoint EuclideanPlane, IsManifoldPoint p :=
    fun p => (hS'.2.2 p).isManifoldPoint
  rcases hD₂'.side hman' hD₁'.isPreconnected_discInt hbd with hin | hout
  · refine ⟨?_, hin⟩
    exact hD₁'.subset_closure_discInt.trans
      (closure_minimal (hin.trans (discInt_subset D₂')) hD₂'.isClosed)
  · obtain ⟨w, hw₁, hw₂⟩ := hne
    have hwcl : w ∈ closure (discInt D₁') := hD₁'.subset_closure_discInt hw₁
    obtain ⟨u, hu₂, hu₁⟩ := mem_closure_iff.mp hwcl _ (hD₂'.isOpen_discInt hman') hw₂
    exact absurd hu₂.1 (Set.disjoint_left.mp hout hu₁)

theorem discInt_mono_of_closedDisc {Δ D₁ D₂ : Set S} (hΔ : IsClosedDisc Δ)
    (hD₁Δ : D₁ ⊆ Δ) (hD₁ : IsClosedDisc D₁) (hD₁₂ : D₁ ⊆ D₂) (hD₂Δ : D₂ ⊆ Δ)
    (hD₂ : IsClosedDisc D₂) : discInt D₁ ⊆ discInt D₂ := by
  have hS' : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hman' : ∀ p : OnePoint EuclideanPlane, IsManifoldPoint p :=
    fun p => (hS'.2.2 p).isManifoldPoint
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  have hsub' : discInt (f '' D₁) ⊆ discInt (f '' D₂) :=
    discInt_mono hman' (sc.disc_f hD₁Δ hD₁).1 (image_mono hD₁₂)
  rw [sc.discInt_f hD₁Δ hD₁, sc.discInt_f hD₂Δ hD₂] at hsub'
  rw [← sc.f'_f ((discInt_subset D₁).trans hD₁Δ), ← sc.f'_f ((discInt_subset D₂).trans hD₂Δ)]
  exact image_mono hsub'

theorem side_of_closedDisc {Δ D C : Set S} (hΔ : IsClosedDisc Δ)
    (hDΔ : D ⊆ Δ) (hCΔ : C ⊆ Δ) (hD : IsClosedDisc D) (hC : IsPreconnected C)
    (hbd : Disjoint C (discBd D)) : C ⊆ discInt D ∨ Disjoint C D := by
  have hS' : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hman' : ∀ p : OnePoint EuclideanPlane, IsManifoldPoint p :=
    fun p => (hS'.2.2 p).isManifoldPoint
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  have hC' : IsPreconnected (f '' C) := hC.image f (sc.fc.mono hCΔ)
  have hbd' : Disjoint (f '' C) (discBd (f '' D)) := by
    rw [(sc.disc_f hDΔ hD).2]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hxC, rfl⟩ ⟨y, hyD, he⟩
    obtain rfl := sc.injOn_f (hDΔ (discBd_subset D hyD)) (hCΔ hxC) he
    exact Set.disjoint_left.mp hbd hxC hyD
  rcases (sc.disc_f hDΔ hD).1.side hman' hC' hbd' with hin | hout
  · left
    rw [sc.discInt_f hDΔ hD] at hin
    rw [← sc.f'_f hCΔ, ← sc.f'_f ((discInt_subset D).trans hDΔ)]
    exact image_mono hin
  · right
    exact Set.disjoint_left.mpr fun x hxC hxD =>
      Set.disjoint_left.mp hout (mem_image_of_mem f hxC) (mem_image_of_mem f hxD)

theorem subset_of_discInt_meets {Δ D₁ D₂ : Set S} (hΔ : IsClosedDisc Δ)
    (hD₁Δ : D₁ ⊆ Δ) (hD₂Δ : D₂ ⊆ Δ) (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (hbd : Disjoint (discInt D₁) (discBd D₂)) (hne : (D₁ ∩ discInt D₂).Nonempty) :
    D₁ ⊆ D₂ ∧ discInt D₁ ⊆ discInt D₂ := by
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  have hbd' : Disjoint (discInt (f '' D₁)) (discBd (f '' D₂)) := by
    rw [sc.discInt_f hD₁Δ hD₁, (sc.disc_f hD₂Δ hD₂).2]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx₁, rfl⟩ ⟨y, hy₂, he⟩
    obtain rfl := sc.injOn_f (hD₂Δ (discBd_subset D₂ hy₂)) (hD₁Δ hx₁.1) he
    exact Set.disjoint_left.mp hbd hx₁ hy₂
  obtain ⟨w, hw₁, hw₂⟩ := hne
  have hne' : (f '' D₁ ∩ discInt (f '' D₂)).Nonempty := by
    rw [sc.discInt_f hD₂Δ hD₂]
    exact ⟨f w, mem_image_of_mem f hw₁, mem_image_of_mem f hw₂⟩
  obtain ⟨hsub, hint⟩ :=
    subset_of_discInt_meets_sphere (sc.disc_f hD₁Δ hD₁).1 (sc.disc_f hD₂Δ hD₂).1 hbd' hne'
  rw [sc.discInt_f hD₁Δ hD₁, sc.discInt_f hD₂Δ hD₂] at hint
  refine ⟨?_, ?_⟩
  · rw [← sc.f'_f hD₁Δ, ← sc.f'_f hD₂Δ]
    exact image_mono hsub
  · rw [← sc.f'_f ((discInt_subset D₁).trans hD₁Δ), ← sc.f'_f ((discInt_subset D₂).trans hD₂Δ)]
    exact image_mono hint

theorem insideDisc_unique {Δ F D₁ D₂ : Set S} (hΔ : IsClosedDisc Δ)
    (h₁ : IsInsideDisc Δ F D₁) (h₂ : IsInsideDisc Δ F D₂) : D₁ = D₂ := by
  have hFΔ : F ⊆ Δ := h₁.2.2.1 ▸ (discBd_subset D₁).trans h₁.1
  have hF : IsOArc F := h₁.2.2.1 ▸ h₁.2.1.isOArc_discBd
  obtain ⟨D₀, _, huniq⟩ := disc_oArc Δ F hΔ hFΔ hF
  exact (huniq D₁ h₁.1 h₁.2.1 h₁.2.2.1).trans (huniq D₂ h₂.1 h₂.2.1 h₂.2.2.1).symm

theorem insideOArc_iff_mem_discInt {Δ F D : Set S} (hΔ : IsClosedDisc Δ)
    (hD : IsInsideDisc Δ F D) {x : S} : InsideOArc Δ F x ↔ x ∈ discInt D :=
  ⟨fun ⟨_, hD', hx⟩ => insideDisc_unique hΔ hD' hD ▸ hx, fun hx => ⟨D, hD, hx⟩⟩

theorem oArcEncloses_iff_subset {Δ F D X : Set S} (hΔ : IsClosedDisc Δ)
    (hD : IsInsideDisc Δ F D) : OArcEncloses Δ F X ↔ X ⊆ D := by
  constructor
  · intro h x hx
    by_cases hxF : x ∈ F
    · exact discBd_subset D (hD.2.2.1 ▸ hxF)
    · exact ((insideOArc_iff_mem_discInt hΔ hD).mp (h x ⟨hx, hxF⟩)).1
  · intro h x ⟨hxX, hxF⟩
    exact (insideOArc_iff_mem_discInt hΔ hD).mpr ⟨h hxX, hD.2.2.1 ▸ hxF⟩

theorem insideDisc_subset_of_oArcEncloses {Δ F₁ F₂ D₁ D₂ : Set S} (hΔ : IsClosedDisc Δ)
    (hD₁ : IsInsideDisc Δ F₁ D₁) (hD₂ : IsInsideDisc Δ F₂ D₂)
    (henc : OArcEncloses Δ F₁ F₂) : D₂ ⊆ D₁ ∧ discInt D₂ ⊆ discInt D₁ := by
  have hF₂D₁ : F₂ ⊆ D₁ := (oArcEncloses_iff_subset hΔ hD₁).mp henc
  have hF₂ : IsOArc F₂ := hD₂.2.2.1 ▸ hD₂.2.1.isOArc_discBd
  obtain ⟨D₂', hD₂', _⟩ := disc_oArc D₁ F₂ hD₁.2.1 hF₂D₁ hF₂
  have hD₂'Δ : D₂' ⊆ Δ := hD₂'.1.trans hD₁.1
  obtain ⟨D₀, _, huniq⟩ := disc_oArc Δ F₂ hΔ (hF₂D₁.trans hD₁.1) hF₂
  have heq : D₂ = D₂' :=
    (huniq D₂ hD₂.1 hD₂.2.1 hD₂.2.2.1).trans (huniq D₂' hD₂'Δ hD₂'.2.1 hD₂'.2.2.1).symm
  have hsub : D₂ ⊆ D₁ := heq ▸ hD₂'.1
  exact ⟨hsub, discInt_mono_of_closedDisc hΔ hD₂.1 hD₂.2.1 hsub hD₁.1 hD₁.2.1⟩

theorem oArcEncloses_trans {Δ F₁ F₂ X : Set S} (hΔ : IsClosedDisc Δ)
    (hF₁Δ : F₁ ⊆ Δ) (hF₂Δ : F₂ ⊆ Δ) (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    (h₁₂ : OArcEncloses Δ F₁ F₂) (h₂X : OArcEncloses Δ F₂ X) :
    OArcEncloses Δ F₁ X := by
  obtain ⟨D₁, hD₁, _⟩ := disc_oArc Δ F₁ hΔ hF₁Δ hF₁
  obtain ⟨D₂, hD₂, _⟩ := disc_oArc Δ F₂ hΔ hF₂Δ hF₂
  rw [oArcEncloses_iff_subset hΔ hD₁]
  exact ((oArcEncloses_iff_subset hΔ hD₂).mp h₂X).trans
    (insideDisc_subset_of_oArcEncloses hΔ hD₁ hD₂ h₁₂).1

theorem edgesInsideOArc_mono_of_oArcEncloses {D : Drawing S} {Δ F₁ F₂ : Set S}
    (hΔ : IsClosedDisc Δ) (hF₁Δ : F₁ ⊆ Δ) (hF₂Δ : F₂ ⊆ Δ) (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    (henc : OArcEncloses Δ F₁ F₂) :
    edgesInsideOArc D Δ F₂ ⊆ edgesInsideOArc D Δ F₁ := by
  obtain ⟨D₁, hD₁, _⟩ := disc_oArc Δ F₁ hΔ hF₁Δ hF₁
  obtain ⟨D₂, hD₂, _⟩ := disc_oArc Δ F₂ hΔ hF₂Δ hF₂
  have hint := (insideDisc_subset_of_oArcEncloses hΔ hD₁ hD₂ henc).2
  rintro e ⟨heE, he₂⟩
  refine ⟨heE, fun x hx => ?_⟩
  rw [insideOArc_iff_mem_discInt hΔ hD₁]
  exact hint ((insideOArc_iff_mem_discInt hΔ hD₂).mp (he₂ x hx))

theorem isCRing_of_uncross {D : Drawing S} {Δ : Set S}
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ F₃ F₄ : Set S}
    (hF₁ : IsCRing C₁ F₁) (hF₂ : IsCRing C₂ F₂)
    (hF₃ : IsOArc F₃) (hF₄ : IsOArc F₄)
    (hbu : F₃ ∪ F₄ ⊆ F₁ ∪ F₂) (hbi : F₃ ∩ F₄ ⊆ F₁ ∩ F₂)
    (henc₃ : OArcEncloses Δ F₃ C₁.U) (henc₄ : OArcEncloses Δ F₄ C₂.U) :
    IsCRing C₁ F₃ ∧ IsCRing C₂ F₄ := by
  have hF₁₂Δ : F₁ ∪ F₂ ⊆ Δ := union_subset hF₁.1 hF₂.1
  have hF₃Δ : F₃ ⊆ Δ := subset_union_left.trans (hbu.trans hF₁₂Δ)
  have hF₄Δ : F₄ ⊆ Δ := subset_union_right.trans (hbu.trans hF₁₂Δ)
  have hnorm₁₂ : D.IsNormal (F₁ ∪ F₂) := fun x ⟨hxF, hxU⟩ =>
    hxF.elim (fun h => hF₁.2.2.1 ⟨h, hxU⟩) (fun h => hF₂.2.2.1 ⟨h, hxU⟩)
  have hnorm₃ : D.IsNormal F₃ := fun x ⟨hxF, hxU⟩ => hnorm₁₂ ⟨hbu (Or.inl hxF), hxU⟩
  have hnorm₄ : D.IsNormal F₄ := fun x ⟨hxF, hxU⟩ => hnorm₁₂ ⟨hbu (Or.inr hxF), hxU⟩
  have hle₃ : circuitRho C₁ ≤ (D.V ∩ F₃).ncard :=
    Nat.sInf_le ⟨F₃, hF₃Δ, hF₃, hnorm₃, henc₃, rfl⟩
  have hle₄ : circuitRho C₂ ≤ (D.V ∩ F₄).ncard :=
    Nat.sInf_le ⟨F₄, hF₄Δ, hF₄, hnorm₄, henc₄, rfl⟩
  have hfin : ∀ A : Set S, (D.V ∩ A).Finite := fun _ => D.finite_V.subset inter_subset_left
  have hsum₃₄ : (D.V ∩ F₃).ncard + (D.V ∩ F₄).ncard =
      ((D.V ∩ F₃) ∪ (D.V ∩ F₄)).ncard + ((D.V ∩ F₃) ∩ (D.V ∩ F₄)).ncard :=
    (Set.ncard_union_add_ncard_inter (D.V ∩ F₃) (D.V ∩ F₄) (hfin F₃) (hfin F₄)).symm
  have hsum₁₂ : ((D.V ∩ F₁) ∪ (D.V ∩ F₂)).ncard + ((D.V ∩ F₁) ∩ (D.V ∩ F₂)).ncard =
      (D.V ∩ F₁).ncard + (D.V ∩ F₂).ncard :=
    Set.ncard_union_add_ncard_inter (D.V ∩ F₁) (D.V ∩ F₂) (hfin F₁) (hfin F₂)
  have hsub_u : (D.V ∩ F₃) ∪ (D.V ∩ F₄) ⊆ (D.V ∩ F₁) ∪ (D.V ∩ F₂) := by
    rintro x (⟨hxV, hx⟩ | ⟨hxV, hx⟩)
    · rcases hbu (Or.inl hx) with h | h
      · exact Or.inl ⟨hxV, h⟩
      · exact Or.inr ⟨hxV, h⟩
    · rcases hbu (Or.inr hx) with h | h
      · exact Or.inl ⟨hxV, h⟩
      · exact Or.inr ⟨hxV, h⟩
  have hsub_i : (D.V ∩ F₃) ∩ (D.V ∩ F₄) ⊆ (D.V ∩ F₁) ∩ (D.V ∩ F₂) := by
    rintro x ⟨⟨hxV, hx₃⟩, ⟨_, hx₄⟩⟩
    exact ⟨⟨hxV, (hbi ⟨hx₃, hx₄⟩).1⟩, ⟨hxV, (hbi ⟨hx₃, hx₄⟩).2⟩⟩
  have hle_u : ((D.V ∩ F₃) ∪ (D.V ∩ F₄)).ncard ≤ ((D.V ∩ F₁) ∪ (D.V ∩ F₂)).ncard :=
    Set.ncard_le_ncard hsub_u ((hfin F₁).union (hfin F₂))
  have hle_i : ((D.V ∩ F₃) ∩ (D.V ∩ F₄)).ncard ≤ ((D.V ∩ F₁) ∩ (D.V ∩ F₂)).ncard :=
    Set.ncard_le_ncard hsub_i ((hfin F₁).inter_of_left _)
  have hrho₁ := hF₁.2.2.2.2
  have hrho₂ := hF₂.2.2.2.2
  have hcard₃ : (D.V ∩ F₃).ncard = circuitRho C₁ := by omega
  have hcard₄ : (D.V ∩ F₄).ncard = circuitRho C₂ := by omega
  exact ⟨⟨hF₃Δ, hF₃, hnorm₃, henc₃, hcard₃⟩, ⟨hF₄Δ, hF₄, hnorm₄, henc₄, hcard₄⟩⟩

/-- If `F₁` is a `C₁`-ring and `F₂` is a `C₂`-ring that also encloses `C₁`, and `F₂ \ F₁` is a
finite union of connected sets, then there is a `C₁`-ring `F₃ ⊆ F₁ ∪ F₂` enclosed by both `F₁`
and `F₂`. -/
theorem exists_cRing_enclosed_of_oArcEncloses {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hF₁ : IsCRing C₁ F₁) (hF₂ : IsCRing C₂ F₂)
    (henc₂ : OArcEncloses Δ F₂ C₁.U) :
    ∃ F₃ : Set S, IsCRing C₁ F₃ ∧ OArcEncloses Δ F₁ F₃ ∧ OArcEncloses Δ F₂ F₃ := by
  have hS' : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have : ConnectedSpace (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).2
  have hsph' : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D₁, hD₁, _⟩ := disc_oArc Δ F₁ hΔ hF₁.1 hF₁.2.1
  obtain ⟨D₂, hD₂, _⟩ := disc_oArc Δ F₂ hΔ hF₂.1 hF₂.2.1
  obtain ⟨z₁, hz₁⟩ := C₁.isInside.2.1.nonempty_discInt
  have hC₁D₁ : C₁.ins ⊆ D₁ ∧ discInt C₁.ins ⊆ discInt D₁ :=
    insideDisc_subset_of_oArcEncloses hΔ hD₁ C₁.isInside hF₁.2.2.2.1
  have hC₁D₂ : C₁.ins ⊆ D₂ ∧ discInt C₁.ins ⊆ discInt D₂ :=
    insideDisc_subset_of_oArcEncloses hΔ hD₂ C₁.isInside henc₂
  have hz₁D₁ : z₁ ∈ discInt D₁ := hC₁D₁.2 hz₁
  have hz₁D₂ : z₁ ∈ discInt D₂ := hC₁D₂.2 hz₁
  let z₁' : OnePoint EuclideanPlane := f z₁
  let z₂' : OnePoint EuclideanPlane := OnePoint.infty
  have hF₁' : IsOArc (f '' F₁) := sc.oArc_f hF₁.1 hF₁.2.1
  have hF₂' : IsOArc (f '' F₂) := sc.oArc_f hF₂.1 hF₂.2.1
  obtain ⟨hd₁', hbd₁'⟩ := sc.disc_f hD₁.1 hD₁.2.1
  obtain ⟨hd₂', hbd₂'⟩ := sc.disc_f hD₂.1 hD₂.2.1
  rw [hD₁.2.2.1] at hbd₁'
  rw [hD₂.2.2.1] at hbd₂'
  have hz₁'_int₁ : z₁' ∈ discInt (f '' D₁) :=
    (sc.discInt_f hD₁.1 hD₁.2.1).symm ▸ mem_image_of_mem f hz₁D₁
  have hz₁'_int₂ : z₁' ∈ discInt (f '' D₂) :=
    (sc.discInt_f hD₂.1 hD₂.2.1).symm ▸ mem_image_of_mem f hz₁D₂
  have hz₁'_not : z₁' ∉ f '' F₁ ∪ f '' F₂ := by
    rintro (h | h)
    · exact hz₁'_int₁.2 (hbd₁' ▸ h)
    · exact hz₁'_int₂.2 (hbd₂' ▸ h)
  have hz₂'_not_D₁ : z₂' ∉ f '' D₁ := fun h => sc.infty_notMem (image_mono hD₁.1 h)
  have hz₂'_not_D₂ : z₂' ∉ f '' D₂ := fun h => sc.infty_notMem (image_mono hD₂.1 h)
  have hz₂'_not : z₂' ∉ f '' F₁ ∪ f '' F₂ := by
    rintro (h | h)
    · exact hz₂'_not_D₁ (discBd_subset (f '' D₁) (hbd₁' ▸ h))
    · exact hz₂'_not_D₂ (discBd_subset (f '' D₂) (hbd₂' ▸ h))
  have hsep₁ : connectedComponentIn ((f '' F₁)ᶜ) z₁' ≠ connectedComponentIn ((f '' F₁)ᶜ) z₂' := by
    intro heq
    have hcomp := hbd₁' ▸ connectedComponentIn_compl_discBd_eq_compl hS' hsph' hd₁' hz₂'_not_D₁
    have hz₁'_mem : z₁' ∈ (f '' D₁)ᶜ := hcomp ▸ heq ▸ mem_connectedComponentIn
      (fun h => hz₁'_not (Or.inl h))
    exact hz₁'_mem hz₁'_int₁.1
  have hsep₂ : connectedComponentIn ((f '' F₂)ᶜ) z₁' ≠ connectedComponentIn ((f '' F₂)ᶜ) z₂' := by
    intro heq
    have hcomp := hbd₂' ▸ connectedComponentIn_compl_discBd_eq_compl hS' hsph' hd₂' hz₂'_not_D₂
    have hz₁'_mem : z₁' ∈ (f '' D₂)ᶜ := hcomp ▸ heq ▸ mem_connectedComponentIn
      (fun h => hz₁'_not (Or.inr h))
    exact hz₁'_mem hz₁'_int₂.1
  obtain ⟨D₁', D₂', hD₁', hD₂', hz₁'D, hz₂'D, hsub₁, hsub₂, hbd_u, hbd_i⟩ :=
    exists_two_disc_covers_sphere hS' hsph' hF₁' hF₂' hz₁'_not hz₂'_not hsep₁ hsep₂
  obtain ⟨E₁', hE₁', hbE₁', hcompl₁⟩ := exists_compl_eq_discInt_of_sphere hsph' hD₁'
  have hz₁'E₁ : z₁' ∈ discInt E₁' := hcompl₁ ▸ hz₁'D
  have hdis_E₁_F : Disjoint (discInt E₁') (f '' F₁ ∪ f '' F₂) := by
    rw [← hcompl₁]
    exact Set.disjoint_left.mpr fun p hpD hpF => hpD (hsub₁ hpF)
  have hE₁_sub₁ : E₁' ⊆ f '' D₁ :=
    (subset_of_discInt_meets_sphere hE₁' hd₁'
      (hbd₁' ▸ hdis_E₁_F.mono_right subset_union_left)
      ⟨z₁', hz₁'E₁.1, hz₁'_int₁⟩).1
  have hE₁_sub₂ : E₁' ⊆ f '' D₂ :=
    (subset_of_discInt_meets_sphere hE₁' hd₂'
      (hbd₂' ▸ hdis_E₁_F.mono_right subset_union_right)
      ⟨z₁', hz₁'E₁.1, hz₁'_int₂⟩).1
  have hinf_E₁ : (OnePoint.infty : OnePoint EuclideanPlane) ∉ E₁' :=
    fun h => hz₂'_not_D₁ (hE₁_sub₁ h)
  have hbd_E₁_Δ : discBd E₁' ⊆ f '' Δ :=
    hbE₁' ▸ (subset_union_left.trans hbd_u).trans
      (union_subset (image_mono hF₁.1) (image_mono hF₂.1))
  have hbd_D₂_Δ : discBd D₂' ⊆ f '' Δ :=
    (subset_union_right.trans hbd_u).trans
      (union_subset (image_mono hF₁.1) (image_mono hF₂.1))
  obtain ⟨_, hD₃_ins, hfD₃, hfF₃⟩ :=
    sc.isInsideDisc_f'_of_infty_notMem hΔ hE₁' hinf_E₁ hbd_E₁_Δ
  obtain ⟨_, hD₄_ins, hfD₄, hfF₄⟩ :=
    sc.isInsideDisc_f'_of_infty_notMem hΔ hD₂' hz₂'D hbd_D₂_Δ
  let F₃ : Set S := f' '' discBd E₁'
  let F₄ : Set S := f' '' discBd D₂'
  have hF₃_oArc : IsOArc F₃ := sc.oArc_f' hbd_E₁_Δ hE₁'.isOArc_discBd
  have hF₄_oArc : IsOArc F₄ := sc.oArc_f' hbd_D₂_Δ hD₂'.isOArc_discBd
  have hbu : F₃ ∪ F₄ ⊆ F₁ ∪ F₂ := by
    rw [← sc.f'_f (union_subset hF₁.1 hF₂.1), image_union, ← image_union]
    exact image_mono (hbE₁' ▸ hbd_u)
  have hbi : F₃ ∩ F₄ ⊆ F₁ ∩ F₂ := by
    rintro x ⟨⟨p, hp₁, rfl⟩, ⟨q, hq₂, he⟩⟩
    obtain rfl := sc.injOn_f' (hbd_D₂_Δ hq₂) (hbd_E₁_Δ hp₁) he
    have hq : q ∈ f '' F₁ ∩ f '' F₂ := hbd_i ⟨hbE₁' ▸ hp₁, hq₂⟩
    rw [← sc.f'_f hF₁.1, ← sc.f'_f hF₂.1]
    exact ⟨mem_image_of_mem f' hq.1, mem_image_of_mem f' hq.2⟩
  have hC₁_sub_E₁ : f '' C₁.ins ⊆ E₁' := by
    obtain ⟨hdC₁, _⟩ := sc.disc_f C₁.isInside.1 C₁.isInside.2.1
    have hdis_C₁ : Disjoint (discInt (f '' C₁.ins)) (discBd E₁') := by
      rw [sc.discInt_f C₁.isInside.1 C₁.isInside.2.1, hbE₁']
      refine Set.disjoint_left.mpr fun p hp hpbd => ?_
      rcases hbd_u (Or.inl hpbd) with h1 | h2
      · obtain ⟨x, hxC, rfl⟩ := hp
        obtain ⟨y, hyF, he⟩ := h1
        obtain rfl := sc.injOn_f (hF₁.1 hyF) (C₁.isInside.1 hxC.1) he
        exact (hC₁D₁.2 hxC).2 (hD₁.2.2.1 ▸ hyF)
      · obtain ⟨x, hxC, rfl⟩ := hp
        obtain ⟨y, hyF, he⟩ := h2
        obtain rfl := sc.injOn_f (hF₂.1 hyF) (C₁.isInside.1 hxC.1) he
        exact (hC₁D₂.2 hxC).2 (hD₂.2.2.1 ▸ hyF)
    exact (subset_of_discInt_meets_sphere hdC₁ hE₁' hdis_C₁
      ⟨z₁', mem_image_of_mem f hz₁.1, hz₁'E₁⟩).1
  have henc₃ : OArcEncloses Δ F₃ C₁.U := by
    rw [oArcEncloses_iff_subset hΔ hD₃_ins]
    have hC₁_sub : C₁.ins ⊆ f' '' E₁' := by
      rw [← sc.f'_f C₁.isInside.1]
      exact image_mono hC₁_sub_E₁
    exact (C₁.isInside.2.2.1 ▸ discBd_subset C₁.ins).trans hC₁_sub
  have henc₄₂ : OArcEncloses Δ F₄ F₂ := by
    rw [oArcEncloses_iff_subset hΔ hD₄_ins, ← sc.f'_f hF₂.1]
    exact image_mono (subset_union_right.trans hsub₂)
  have henc₄ : OArcEncloses Δ F₄ C₂.U :=
    oArcEncloses_trans hΔ (sc.f'_subset hbd_D₂_Δ) hF₂.1 hF₄_oArc hF₂.2.1 henc₄₂ hF₂.2.2.2.1
  obtain ⟨hCR₃, _⟩ := isCRing_of_uncross hF₁ hF₂ hF₃_oArc hF₄_oArc hbu hbi henc₃ henc₄
  refine ⟨F₃, hCR₃, ?_, ?_⟩
  · rw [oArcEncloses_iff_subset hΔ hD₁]
    have hsub : f' '' E₁' ⊆ D₁ := by
      rw [← sc.f'_f hD₁.1]
      exact image_mono hE₁_sub₁
    exact (hD₃_ins.2.2.1 ▸ discBd_subset (f' '' E₁')).trans hsub
  · rw [oArcEncloses_iff_subset hΔ hD₂]
    have hsub : f' '' E₁' ⊆ D₂ := by
      rw [← sc.f'_f hD₂.1]
      exact image_mono hE₁_sub₂
    exact (hD₃_ins.2.2.1 ▸ discBd_subset (f' '' E₁')).trans hsub

/-- **(6.4)** Let `D` be a drawing in a disc `Δ`, and let `C₁, C₂` be circuits of `D`.
Let `Fᵢ` be a `Cᵢ`-ring (`i = 1, 2`), such that some point of `C₁` is inside `F₂`, and no point
of `F₂` is inside `C₁`. Then there is a `C₁`-ring enclosed by both `F₁` and `F₂`.
(GM VIII Section 6, page 264.) -/
theorem theorem_6_4_proof {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hF₁ : IsCRing C₁ F₁) (hF₂ : IsCRing C₂ F₂)
    (hin : ∃ x ∈ C₁.U, InsideOArc Δ F₂ x)
    (hout : ∀ x ∈ F₂, ¬ InsideOArc Δ C₁.U x) :
    ∃ F₃ : Set S, IsCRing C₁ F₃ ∧ OArcEncloses Δ F₁ F₃ ∧ OArcEncloses Δ F₂ F₃ := by
  obtain ⟨D₂, hD₂, _⟩ := disc_oArc Δ F₂ hΔ hF₂.1 hF₂.2.1
  have hdis_C₁F₂ : Disjoint (discInt C₁.ins) (discBd D₂) := by
    rw [hD₂.2.2.1]
    exact Set.disjoint_left.mpr fun x hxC₁ hxF₂ =>
      hout x hxF₂ ((insideOArc_iff_mem_discInt hΔ C₁.isInside).mpr hxC₁)
  obtain ⟨x₀, hx₀C₁, hx₀F₂⟩ := hin
  have hx₀D₂ : x₀ ∈ discInt D₂ := (insideOArc_iff_mem_discInt hΔ hD₂).mp hx₀F₂
  have hx₀ins : x₀ ∈ C₁.ins := discBd_subset C₁.ins (C₁.isInside.2.2.1 ▸ hx₀C₁)
  have hC₁D₂ : C₁.ins ⊆ D₂ ∧ discInt C₁.ins ⊆ discInt D₂ :=
    subset_of_discInt_meets hΔ C₁.isInside.1 hD₂.1 C₁.isInside.2.1 hD₂.2.1 hdis_C₁F₂
      ⟨x₀, hx₀ins, hx₀D₂⟩
  have henc₂ : OArcEncloses Δ F₂ C₁.U := by
    rw [oArcEncloses_iff_subset hΔ hD₂]
    exact (C₁.isInside.2.2.1 ▸ discBd_subset C₁.ins).trans hC₁D₂.1
  exact exists_cRing_enclosed_of_oArcEncloses hΔ hF₁ hF₂ henc₂

/-- **(6.5)** Let `D` be a drawing in a disc `Δ`, and let `C₁, C₂` be circuits of `D`.
Let `Fᵢ` be a `Cᵢ`-ring (`i = 1, 2`), such that `F₁` and `C₂` bound disjoint open discs, and
`F₂` and `C₁` bound disjoint open discs. Then there is a `C₁`-ring `F₃` and a `C₂`-ring `F₄`
such that `F₁` encloses `F₃`, `F₂` encloses `F₄`, and `F₃` and `F₄` bound disjoint open discs.
(GM VIII Section 6, page 265.) -/
theorem theorem_6_5_proof {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hF₁ : IsCRing C₁ F₁) (hF₂ : IsCRing C₂ F₂)
    (hdis₁ : BoundDisjointOpenDiscs Δ F₁ C₂.U)
    (hdis₂ : BoundDisjointOpenDiscs Δ F₂ C₁.U) :
    ∃ F₃ F₄ : Set S, IsCRing C₁ F₃ ∧ IsCRing C₂ F₄ ∧
      OArcEncloses Δ F₁ F₃ ∧ OArcEncloses Δ F₂ F₄ ∧
      BoundDisjointOpenDiscs Δ F₃ F₄ := by
  have hS' : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have : ConnectedSpace (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).2
  have hsph' : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D₁, hD₁, _⟩ := disc_oArc Δ F₁ hΔ hF₁.1 hF₁.2.1
  obtain ⟨D₂, hD₂, _⟩ := disc_oArc Δ F₂ hΔ hF₂.1 hF₂.2.1
  obtain ⟨z₁, hz₁⟩ := C₁.isInside.2.1.nonempty_discInt
  obtain ⟨z₂, hz₂⟩ := C₂.isInside.2.1.nonempty_discInt
  have hC₁D₁ : C₁.ins ⊆ D₁ ∧ discInt C₁.ins ⊆ discInt D₁ :=
    insideDisc_subset_of_oArcEncloses hΔ hD₁ C₁.isInside hF₁.2.2.2.1
  have hC₂D₂ : C₂.ins ⊆ D₂ ∧ discInt C₂.ins ⊆ discInt D₂ :=
    insideDisc_subset_of_oArcEncloses hΔ hD₂ C₂.isInside hF₂.2.2.2.1
  have hz₁D₁ : z₁ ∈ discInt D₁ := hC₁D₁.2 hz₁
  have hz₂D₂ : z₂ ∈ discInt D₂ := hC₂D₂.2 hz₂
  let z₁' : OnePoint EuclideanPlane := f z₁
  let z₂' : OnePoint EuclideanPlane := f z₂
  obtain ⟨hd₁', hbd₁'⟩ := sc.disc_f hD₁.1 hD₁.2.1
  obtain ⟨hd₂', hbd₂'⟩ := sc.disc_f hD₂.1 hD₂.2.1
  obtain ⟨hdC₁, _⟩ := sc.disc_f C₁.isInside.1 C₁.isInside.2.1
  obtain ⟨hdC₂, _⟩ := sc.disc_f C₂.isInside.1 C₂.isInside.2.1
  rw [hD₁.2.2.1] at hbd₁'
  rw [hD₂.2.2.1] at hbd₂'
  have hdis_C₁_D₂ : Disjoint (discInt (f '' C₁.ins)) (f '' D₂) := by
    by_contra hcon
    rw [Set.not_disjoint_iff] at hcon
    obtain ⟨p, hpC₁, hpD₂⟩ := hcon
    have hman' : ∀ q : OnePoint EuclideanPlane, IsManifoldPoint q :=
      fun q => (hS'.2.2 q).isManifoldPoint
    obtain ⟨q, hq₁, hq₂⟩ := mem_closure_iff.mp (hd₂'.subset_closure_discInt hpD₂) _
      (hdC₁.isOpen_discInt hman') hpC₁
    rw [sc.discInt_f hD₂.1 hD₂.2.1] at hq₂
    rw [sc.discInt_f C₁.isInside.1 C₁.isInside.2.1] at hq₁
    obtain ⟨x, hx₂, rfl⟩ := hq₂
    obtain ⟨y, hy₁, he⟩ := hq₁
    obtain rfl := sc.injOn_f (hD₂.1 hx₂.1) (C₁.isInside.1 hy₁.1) he.symm
    exact Set.disjoint_left.mp hdis₂
      ((insideOArc_iff_mem_discInt hΔ hD₂).mpr hx₂)
      ((insideOArc_iff_mem_discInt hΔ C₁.isInside).mpr hy₁)
  have hdis_C₂_D₁ : Disjoint (discInt (f '' C₂.ins)) (f '' D₁) := by
    by_contra hcon
    rw [Set.not_disjoint_iff] at hcon
    obtain ⟨p, hpC₂, hpD₁⟩ := hcon
    have hman' : ∀ q : OnePoint EuclideanPlane, IsManifoldPoint q :=
      fun q => (hS'.2.2 q).isManifoldPoint
    obtain ⟨q, hq₂, hq₁⟩ := mem_closure_iff.mp (hd₁'.subset_closure_discInt hpD₁) _
      (hdC₂.isOpen_discInt hman') hpC₂
    rw [sc.discInt_f hD₁.1 hD₁.2.1] at hq₁
    rw [sc.discInt_f C₂.isInside.1 C₂.isInside.2.1] at hq₂
    obtain ⟨x, hx₁, rfl⟩ := hq₁
    obtain ⟨y, hy₂, he⟩ := hq₂
    obtain rfl := sc.injOn_f (hD₁.1 hx₁.1) (C₂.isInside.1 hy₂.1) he.symm
    exact Set.disjoint_left.mp hdis₁
      ((insideOArc_iff_mem_discInt hΔ hD₁).mpr hx₁)
      ((insideOArc_iff_mem_discInt hΔ C₂.isInside).mpr hy₂)
  have hz₁'_intC₁ : z₁' ∈ discInt (f '' C₁.ins) :=
    (sc.discInt_f C₁.isInside.1 C₁.isInside.2.1).symm ▸ mem_image_of_mem f hz₁
  have hz₂'_intC₂ : z₂' ∈ discInt (f '' C₂.ins) :=
    (sc.discInt_f C₂.isInside.1 C₂.isInside.2.1).symm ▸ mem_image_of_mem f hz₂
  have hz₁'_int₁ : z₁' ∈ discInt (f '' D₁) :=
    (sc.discInt_f hD₁.1 hD₁.2.1).symm ▸ mem_image_of_mem f hz₁D₁
  have hz₂'_int₂ : z₂' ∈ discInt (f '' D₂) :=
    (sc.discInt_f hD₂.1 hD₂.2.1).symm ▸ mem_image_of_mem f hz₂D₂
  have hz₁'_not_D₂ : z₁' ∉ f '' D₂ := Set.disjoint_left.mp hdis_C₁_D₂ hz₁'_intC₁
  have hz₂'_not_D₁ : z₂' ∉ f '' D₁ := Set.disjoint_left.mp hdis_C₂_D₁ hz₂'_intC₂
  have hz₁'_not : z₁' ∉ f '' F₁ ∪ f '' F₂ := by
    rintro (h | h)
    · exact hz₁'_int₁.2 (hbd₁' ▸ h)
    · exact hz₁'_not_D₂ (discBd_subset (f '' D₂) (hbd₂' ▸ h))
  have hz₂'_not : z₂' ∉ f '' F₁ ∪ f '' F₂ := by
    rintro (h | h)
    · exact hz₂'_not_D₁ (discBd_subset (f '' D₁) (hbd₁' ▸ h))
    · exact hz₂'_int₂.2 (hbd₂' ▸ h)
  have hsep₁ : connectedComponentIn ((f '' F₁)ᶜ) z₁' ≠ connectedComponentIn ((f '' F₁)ᶜ) z₂' := by
    intro heq
    have hcomp := hbd₁' ▸ connectedComponentIn_compl_discBd_eq_compl hS' hsph' hd₁' hz₂'_not_D₁
    have hz₁'_mem : z₁' ∈ (f '' D₁)ᶜ := hcomp ▸ heq ▸ mem_connectedComponentIn
      (fun h => hz₁'_not (Or.inl h))
    exact hz₁'_mem hz₁'_int₁.1
  have hsep₂ : connectedComponentIn ((f '' F₂)ᶜ) z₁' ≠ connectedComponentIn ((f '' F₂)ᶜ) z₂' := by
    intro heq
    have hcomp := hbd₂' ▸ connectedComponentIn_compl_discBd_eq_compl hS' hsph' hd₂' hz₁'_not_D₂
    have hz₂'_mem : z₂' ∈ (f '' D₂)ᶜ := hcomp ▸ heq.symm ▸ mem_connectedComponentIn
      (fun h => hz₂'_not (Or.inr h))
    exact hz₂'_mem hz₂'_int₂.1
  have hF₁' : IsOArc (f '' F₁) := sc.oArc_f hF₁.1 hF₁.2.1
  have hF₂' : IsOArc (f '' F₂) := sc.oArc_f hF₂.1 hF₂.2.1
  obtain ⟨D₁', D₂', hD₁', hD₂', hz₁'D, hz₂'D, hsub₁, hsub₂, hbd_u, hbd_i⟩ :=
    exists_two_disc_covers_sphere hS' hsph' hF₁' hF₂' hz₁'_not hz₂'_not hsep₁ hsep₂
  obtain ⟨E₁', hE₁', hbE₁', hcompl₁⟩ := exists_compl_eq_discInt_of_sphere hsph' hD₁'
  obtain ⟨E₂', hE₂', hbE₂', hcompl₂⟩ := exists_compl_eq_discInt_of_sphere hsph' hD₂'
  have hz₁'E₁ : z₁' ∈ discInt E₁' := hcompl₁ ▸ hz₁'D
  have hz₂'E₂ : z₂' ∈ discInt E₂' := hcompl₂ ▸ hz₂'D
  have hdis_E₁_F : Disjoint (discInt E₁') (f '' F₁ ∪ f '' F₂) := by
    rw [← hcompl₁]
    exact Set.disjoint_left.mpr fun p hpD hpF => hpD (hsub₁ hpF)
  have hdis_E₂_F : Disjoint (discInt E₂') (f '' F₁ ∪ f '' F₂) := by
    rw [← hcompl₂]
    exact Set.disjoint_left.mpr fun p hpD hpF => hpD (hsub₂ hpF)
  have hE₁_sub₁ : E₁' ⊆ f '' D₁ ∧ discInt E₁' ⊆ discInt (f '' D₁) :=
    subset_of_discInt_meets_sphere hE₁' hd₁'
      (hbd₁' ▸ hdis_E₁_F.mono_right subset_union_left)
      ⟨z₁', hz₁'E₁.1, hz₁'_int₁⟩
  have hE₂_sub₂ : E₂' ⊆ f '' D₂ ∧ discInt E₂' ⊆ discInt (f '' D₂) :=
    subset_of_discInt_meets_sphere hE₂' hd₂'
      (hbd₂' ▸ hdis_E₂_F.mono_right subset_union_right)
      ⟨z₂', hz₂'E₂.1, hz₂'_int₂⟩
  have hdis_E₁_E₂ : Disjoint (discInt E₁') (discInt E₂') := by
    have hman' : ∀ q : OnePoint EuclideanPlane, IsManifoldPoint q :=
      fun q => (hS'.2.2 q).isManifoldPoint
    have hbd_E₂_D₁ : Disjoint (discInt E₂') (discBd (f '' D₁)) :=
      hbd₁' ▸ hdis_E₂_F.mono_right subset_union_left
    rcases hd₁'.side hman' hE₂'.isPreconnected_discInt hbd_E₂_D₁ with hin | hout
    · exact absurd (hin hz₂'E₂).1 hz₂'_not_D₁
    · exact Set.disjoint_left.mpr fun p hp₁ hp₂ =>
        Set.disjoint_left.mp hout hp₂ (hE₁_sub₁.2 hp₁).1
  have hinf_E₁ : (OnePoint.infty : OnePoint EuclideanPlane) ∉ E₁' :=
    fun h => sc.infty_notMem (image_mono hD₁.1 (hE₁_sub₁.1 h))
  have hinf_E₂ : (OnePoint.infty : OnePoint EuclideanPlane) ∉ E₂' :=
    fun h => sc.infty_notMem (image_mono hD₂.1 (hE₂_sub₂.1 h))
  have hbd_E₁_Δ : discBd E₁' ⊆ f '' Δ :=
    hbE₁' ▸ (subset_union_left.trans hbd_u).trans
      (union_subset (image_mono hF₁.1) (image_mono hF₂.1))
  have hbd_E₂_Δ : discBd E₂' ⊆ f '' Δ :=
    hbE₂' ▸ (subset_union_right.trans hbd_u).trans
      (union_subset (image_mono hF₁.1) (image_mono hF₂.1))
  obtain ⟨_, hD₃_ins, hfD₃, hfF₃⟩ :=
    sc.isInsideDisc_f'_of_infty_notMem hΔ hE₁' hinf_E₁ hbd_E₁_Δ
  obtain ⟨_, hD₄_ins, hfD₄, hfF₄⟩ :=
    sc.isInsideDisc_f'_of_infty_notMem hΔ hE₂' hinf_E₂ hbd_E₂_Δ
  let F₃ : Set S := f' '' discBd E₁'
  let F₄ : Set S := f' '' discBd E₂'
  have hF₃_oArc : IsOArc F₃ := sc.oArc_f' hbd_E₁_Δ hE₁'.isOArc_discBd
  have hF₄_oArc : IsOArc F₄ := sc.oArc_f' hbd_E₂_Δ hE₂'.isOArc_discBd
  have hbu : F₃ ∪ F₄ ⊆ F₁ ∪ F₂ := by
    rw [← sc.f'_f (union_subset hF₁.1 hF₂.1), image_union, ← image_union]
    exact image_mono (hbE₁' ▸ hbE₂' ▸ hbd_u)
  have hbi : F₃ ∩ F₄ ⊆ F₁ ∩ F₂ := by
    rintro x ⟨⟨p, hp₁, rfl⟩, ⟨q, hq₂, he⟩⟩
    obtain rfl := sc.injOn_f' (hbd_E₂_Δ hq₂) (hbd_E₁_Δ hp₁) he
    have hq : q ∈ f '' F₁ ∩ f '' F₂ := hbd_i ⟨hbE₁' ▸ hp₁, hbE₂' ▸ hq₂⟩
    rw [← sc.f'_f hF₁.1, ← sc.f'_f hF₂.1]
    exact ⟨mem_image_of_mem f' hq.1, mem_image_of_mem f' hq.2⟩
  have hC₁_sub_E₁ : f '' C₁.ins ⊆ E₁' := by
    have hdis_C₁ : Disjoint (discInt (f '' C₁.ins)) (discBd E₁') := by
      rw [sc.discInt_f C₁.isInside.1 C₁.isInside.2.1, hbE₁']
      refine Set.disjoint_left.mpr fun p hp hpbd => ?_
      rcases hbd_u (Or.inl hpbd) with h1 | h2
      · obtain ⟨x, hxC, rfl⟩ := hp
        obtain ⟨y, hyF, he⟩ := h1
        obtain rfl := sc.injOn_f (hF₁.1 hyF) (C₁.isInside.1 hxC.1) he
        exact (hC₁D₁.2 hxC).2 (hD₁.2.2.1 ▸ hyF)
      · exact Set.disjoint_left.mp hdis_C₁_D₂
          ((sc.discInt_f C₁.isInside.1 C₁.isInside.2.1).symm ▸ hp)
          (discBd_subset (f '' D₂) (hbd₂' ▸ h2))
    exact (subset_of_discInt_meets_sphere hdC₁ hE₁' hdis_C₁
      ⟨z₁', mem_image_of_mem f hz₁.1, hz₁'E₁⟩).1
  have hC₂_sub_E₂ : f '' C₂.ins ⊆ E₂' := by
    have hdis_C₂ : Disjoint (discInt (f '' C₂.ins)) (discBd E₂') := by
      rw [sc.discInt_f C₂.isInside.1 C₂.isInside.2.1, hbE₂']
      refine Set.disjoint_left.mpr fun p hp hpbd => ?_
      rcases hbd_u (Or.inr hpbd) with h1 | h2
      · exact Set.disjoint_left.mp hdis_C₂_D₁
          ((sc.discInt_f C₂.isInside.1 C₂.isInside.2.1).symm ▸ hp)
          (discBd_subset (f '' D₁) (hbd₁' ▸ h1))
      · obtain ⟨x, hxC, rfl⟩ := hp
        obtain ⟨y, hyF, he⟩ := h2
        obtain rfl := sc.injOn_f (hF₂.1 hyF) (C₂.isInside.1 hxC.1) he
        exact (hC₂D₂.2 hxC).2 (hD₂.2.2.1 ▸ hyF)
    exact (subset_of_discInt_meets_sphere hdC₂ hE₂' hdis_C₂
      ⟨z₂', mem_image_of_mem f hz₂.1, hz₂'E₂⟩).1
  have henc₃ : OArcEncloses Δ F₃ C₁.U := by
    rw [oArcEncloses_iff_subset hΔ hD₃_ins]
    have hC₁_sub : C₁.ins ⊆ f' '' E₁' := by
      rw [← sc.f'_f C₁.isInside.1]
      exact image_mono hC₁_sub_E₁
    exact (C₁.isInside.2.2.1 ▸ discBd_subset C₁.ins).trans hC₁_sub
  have henc₄ : OArcEncloses Δ F₄ C₂.U := by
    rw [oArcEncloses_iff_subset hΔ hD₄_ins]
    have hC₂_sub : C₂.ins ⊆ f' '' E₂' := by
      rw [← sc.f'_f C₂.isInside.1]
      exact image_mono hC₂_sub_E₂
    exact (C₂.isInside.2.2.1 ▸ discBd_subset C₂.ins).trans hC₂_sub
  obtain ⟨hCR₃, hCR₄⟩ := isCRing_of_uncross hF₁ hF₂ hF₃_oArc hF₄_oArc hbu hbi henc₃ henc₄
  refine ⟨F₃, F₄, hCR₃, hCR₄, ?_, ?_, ?_⟩
  · rw [oArcEncloses_iff_subset hΔ hD₁]
    have hsub : f' '' E₁' ⊆ D₁ := by
      rw [← sc.f'_f hD₁.1]
      exact image_mono hE₁_sub₁.1
    exact (hD₃_ins.2.2.1 ▸ discBd_subset (f' '' E₁')).trans hsub
  · rw [oArcEncloses_iff_subset hΔ hD₂]
    have hsub : f' '' E₂' ⊆ D₂ := by
      rw [← sc.f'_f hD₂.1]
      exact image_mono hE₂_sub₂.1
    exact (hD₄_ins.2.2.1 ▸ discBd_subset (f' '' E₂')).trans hsub
  · refine Set.disjoint_left.mpr fun x hx₃ hx₄ => ?_
    have hx₃' : x ∈ discInt (f' '' E₁') := (insideOArc_iff_mem_discInt hΔ hD₃_ins).mp hx₃
    have hx₄' : x ∈ discInt (f' '' E₂') := (insideOArc_iff_mem_discInt hΔ hD₄_ins).mp hx₄
    have hfx₃ : f x ∈ discInt E₁' := by
      rw [← hfD₃, sc.discInt_f hD₃_ins.1 hD₃_ins.2.1]
      exact mem_image_of_mem f hx₃'
    have hfx₄ : f x ∈ discInt E₂' := by
      rw [← hfD₄, sc.discInt_f hD₄_ins.1 hD₄_ins.2.1]
      exact mem_image_of_mem f hx₄'
    exact Set.disjoint_left.mp hdis_E₁_E₂ hfx₃ hfx₄

/-- **(6.6)** Let `D` be a drawing in a disc `Δ`, and let `C` be a circuit of `D`.
If `F₁, F₂` are minimal `C`-rings then `Γ(F₁) = Γ(F₂)`.
(GM VIII Section 6, page 266.) -/
theorem theorem_6_6_proof {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hF₁ : IsMinimalCRing C F₁) (hF₂ : IsMinimalCRing C F₂) :
    edgesInsideOArc D Δ F₁ = edgesInsideOArc D Δ F₂ := by
  obtain ⟨F₃, hCR₃, henc₁, henc₂⟩ :=
    exists_cRing_enclosed_of_oArcEncloses hΔ hF₁.1 hF₂.1 hF₂.1.2.2.2.1
  have hsub₁ : edgesInsideOArc D Δ F₃ ⊆ edgesInsideOArc D Δ F₁ :=
    edgesInsideOArc_mono_of_oArcEncloses hΔ hF₁.1.1 hCR₃.1 hF₁.1.2.1 hCR₃.2.1 henc₁
  have hsub₂ : edgesInsideOArc D Δ F₃ ⊆ edgesInsideOArc D Δ F₂ :=
    edgesInsideOArc_mono_of_oArcEncloses hΔ hF₂.1.1 hCR₃.1 hF₂.1.2.1 hCR₃.2.1 henc₂
  have heq₁ : edgesInsideOArc D Δ F₃ = edgesInsideOArc D Δ F₁ :=
    hsub₁.eq_of_not_ssubset (hF₁.2 F₃ hCR₃)
  have heq₂ : edgesInsideOArc D Δ F₃ = edgesInsideOArc D Δ F₂ :=
    hsub₂.eq_of_not_ssubset (hF₂.2 F₃ hCR₃)
  exact heq₁.symm.trans heq₂

/-- Removing at most one point from an O-arc leaves a preconnected set. -/
theorem isPreconnected_oArc_sdiff_singleton {F : Set S} (hF : IsOArc F) (a : S) :
    IsPreconnected (F \ {a}) := by
  obtain ⟨φ⟩ := hF
  by_cases ha : a ∈ F
  · obtain ⟨t, ht⟩ : ∃ t : Circle, (φ t).1 = a := ⟨φ.symm ⟨a, ha⟩, by simp⟩
    let ψ : ℝ → S := fun θ => (φ (t * Circle.exp θ)).1
    have hψ_cont : Continuous ψ :=
      continuous_subtype_val.comp
        (φ.continuous.comp (continuous_const.mul Circle.exp.continuous))
    have himg : ψ '' Ioo (0 : ℝ) (2 * Real.pi) = F \ {a} := by
      ext x
      constructor
      · rintro ⟨θ, ⟨hθ0, hθ2⟩, rfl⟩
        refine ⟨(φ (t * Circle.exp θ)).2, fun hxa => ?_⟩
        have heq : φ (t * Circle.exp θ) = φ t := Subtype.ext (hxa.trans ht.symm)
        have hmul := φ.injective heq
        have hexp : Circle.exp θ = Circle.exp 0 := by
          have : t * Circle.exp θ = t * 1 := by simpa using hmul
          simpa using mul_left_cancel this
        obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
        have hm0 : (0 : ℝ) < m := by
          by_contra hc
          rw [not_lt] at hc
          nlinarith [Real.pi_pos]
        have hm1 : (m : ℝ) < 1 := by
          by_contra hc
          rw [not_lt] at hc
          nlinarith [Real.pi_pos]
        have hm_int : (0 : ℤ) < m ∧ m < 1 := ⟨Int.cast_pos.mp hm0, by exact_mod_cast hm1⟩
        omega
      · rintro ⟨hxF, hxa⟩
        let s : Circle := φ.symm ⟨x, hxF⟩
        have hsx : (φ s).1 = x := by simp [s]
        have hst : s ≠ t := fun h => hxa (hsx.symm.trans (by rw [h, ht]))
        obtain ⟨θ, hθ0, hθ2, hsθ⟩ :=
          exists_angle_near t s 0 le_rfl Real.pi_pos.le
        rw [neg_zero] at hθ0
        rw [sub_zero] at hθ2
        have hne0 : θ ≠ 0 := by
          rintro rfl
          apply hst
          rw [hsθ, Circle.exp_zero, mul_one]
        have hne2 : θ ≠ 2 * Real.pi := by
          rintro rfl
          apply hst
          rw [hsθ, Circle.exp_two_pi, mul_one]
        exact ⟨θ, ⟨lt_of_le_of_ne hθ0 hne0.symm, lt_of_le_of_ne hθ2 hne2⟩,
          by simp [ψ, ← hsθ, hsx]⟩
    rw [← himg]
    exact isPreconnected_Ioo.image ψ hψ_cont.continuousOn
  · have hF_eq : F \ {a} = range (fun t : Circle => (φ t).1) := by
      ext x
      constructor
      · rintro ⟨hx, _⟩
        exact ⟨φ.symm ⟨x, hx⟩, by simp⟩
      · rintro ⟨t, rfl⟩
        exact ⟨(φ t).2, fun h => ha (h ▸ (φ t).2)⟩
    rw [hF_eq]
    exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)

/-- If `F` is an O-arc and `F ∩ A` is finite of cardinality at most 1, then `F \ A` is
preconnected. -/
theorem isPreconnected_oArc_sdiff_of_ncard_le_one {F A : Set S} (hF : IsOArc F)
    (hfin : (F ∩ A).Finite) (hle : (F ∩ A).ncard ≤ 1) :
    IsPreconnected (F \ A) := by
  have heq : F \ A = F \ (F ∩ A) := by ext x; simp
  rw [heq]
  rcases (Set.ncard_le_one_iff_eq hfin).mp hle with hemp | ⟨a, ha⟩
  · rw [hemp, sdiff_empty]
    obtain ⟨φ⟩ := hF
    have hF_eq : F = range (fun t : Circle => (φ t).1) := by
      ext x
      exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩, fun ⟨t, ht⟩ => ht ▸ (φ t).2⟩
    rw [hF_eq]
    exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)
  · rw [ha]
    exact isPreconnected_oArc_sdiff_singleton hF a

/-- In a drawing nest `N`, the circuits are pairwise disjoint. -/
theorem DrawingNest.pairwise_disjoint_circuits {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {r s : ℕ} (N : DrawingNest D Δ r s) :
    Pairwise (fun i j : Fin s => Disjoint (N.circuit i).U (N.circuit j).U) := by
  have hlt : ∀ {i j : Fin s}, i < j → Disjoint (N.circuit i).U (N.circuit j).U := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    have hin : InsideOArc Δ (N.circuit j).U x := N.inside_of_lt hij x hxi
    have hx_int := (insideOArc_iff_mem_discInt hΔ (N.circuit j).isInside).mp hin
    exact hx_int.2 ((N.circuit j).isInside.2.2.1 ▸ hxj)
  intro i j hij
  rcases lt_trichotomy i j with h | rfl | h
  · exact hlt h
  · exact absurd rfl hij
  · exact (hlt h).symm

/-- For `i ≤ j` in a drawing nest `N`, `(N.circuit i).ins ⊆ (N.circuit j).ins` and
`discInt (N.circuit i).ins ⊆ discInt (N.circuit j).ins`. -/
theorem DrawingNest.insideDisc_subset_of_le {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {r s : ℕ} (N : DrawingNest D Δ r s) {i j : Fin s} (hij : i ≤ j) :
    (N.circuit i).ins ⊆ (N.circuit j).ins ∧
      discInt (N.circuit i).ins ⊆ discInt (N.circuit j).ins := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · have henc : OArcEncloses Δ (N.circuit j).U (N.circuit i).U :=
      fun x hx => N.inside_of_lt hlt x hx.1
    exact insideDisc_subset_of_oArcEncloses hΔ (N.circuit j).isInside (N.circuit i).isInside henc
  · exact ⟨Subset.rfl, Subset.rfl⟩

/-- First case of the proof of **(6.7)** (page 266): if `C₁, C₂` are bosses, `Fᵢ` is a `Cᵢ`-ring,
and some point of `F₂` is inside `C₁`, then `F₁` encloses `F₂`. -/
theorem oArcEncloses_of_isBoss_meets_inside {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hB₁ : IsBoss D Δ C₁) (hB₂ : IsBoss D Δ C₂)
    (hF₁ : IsCRing C₁ F₁) (hF₂ : IsCRing C₂ F₂)
    (hin : ∃ y ∈ F₂, InsideOArc Δ C₁.U y) :
    OArcEncloses Δ F₁ F₂ := by
  classical
  let k := (D.V ∩ discBd Δ).ncard
  have hk : 0 < k := Nat.zero_lt_of_lt hB₁.rho_lt
  obtain ⟨N₁, hN₁⟩ := hB₁.exists_nest
  have hC₀ : N₁.circuit ⟨0, hk⟩ = C₁ := hN₁ hk
  obtain ⟨D₁, hD₁, _⟩ := disc_oArc Δ F₁ hΔ hF₁.1 hF₁.2.1
  -- Step 1: Some radial path of `N₁` is disjoint from `F₁`, so some point of `C₁^k` is inside `F₁`.
  have hp_ex : ∃ p : Fin (1 + circuitRho C₁), Disjoint (N₁.radialPath p ∩ D.V) F₁ := by
    by_contra! hall
    have hchoose : ∀ p, ∃ x, x ∈ N₁.radialPath p ∩ D.V ∧ x ∈ D.V ∩ F₁ := by
      intro p
      obtain ⟨x, hx₁, hx₂⟩ := Set.not_disjoint_iff.mp (hall p)
      exact ⟨x, hx₁, hx₁.2, hx₂⟩
    choose g hg using hchoose
    have hginj : Function.Injective g := by
      intro p q hpq
      by_contra hne
      exact Set.disjoint_left.mp (N₁.pairwise_disjoint_paths hne) (hg p).1 (hpq ▸ (hg q).1)
    have hsub : range g ⊆ D.V ∩ F₁ := by
      rintro _ ⟨p, rfl⟩
      exact (hg p).2
    have hfin₁ : (D.V ∩ F₁).Finite := D.finite_V.subset inter_subset_left
    have hle := Set.ncard_le_ncard hsub hfin₁
    rw [Set.ncard_range_of_injective hginj, Nat.card_eq_fintype_card, Fintype.card_fin,
      hF₁.2.2.2.2] at hle
    omega
  obtain ⟨p₀, hp₀⟩ := hp_ex
  have hp₀_dis : Disjoint (N₁.radialPath p₀) (discBd D₁) := by
    rw [hD₁.2.2.1]
    refine Set.disjoint_left.mpr fun x hxp hxF₁ => ?_
    have hxV : x ∈ D.V := hF₁.2.2.1 ⟨hxF₁, N₁.radialPath_sub_U p₀ hxp⟩
    exact Set.disjoint_left.mp hp₀ ⟨hxp, hxV⟩ hxF₁
  obtain ⟨u₀, hu₀p, hu₀C⟩ := N₁.meets_inner p₀ hk
  rw [hC₀] at hu₀C
  have hu₀_not_F₁ : u₀ ∉ F₁ :=
    fun h => Set.disjoint_left.mp hp₀_dis hu₀p (hD₁.2.2.1 ▸ h)
  have hu₀_int : u₀ ∈ discInt D₁ :=
    (insideOArc_iff_mem_discInt hΔ hD₁).mp (hF₁.2.2.2.1 u₀ ⟨hu₀C, hu₀_not_F₁⟩)
  have hp₀_sub : N₁.radialPath p₀ ⊆ discInt D₁ := by
    rcases side_of_closedDisc hΔ hD₁.1 (N₁.radialPath_sub_disc p₀) hD₁.2.1
      (N₁.isPreconnected_radialPath p₀) hp₀_dis with hsub | hdis
    · exact hsub
    · exact absurd hu₀_int.1 (Set.disjoint_left.mp hdis hu₀p)
  let ik : Fin k := ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩
  obtain ⟨w, hwp, hwCk⟩ := N₁.meets_outer p₀ hk
  have hw_int₁ : w ∈ discInt D₁ := hp₀_sub hwp
  -- Step 2: Some circuit `C₁^j` meets `F₁ ∪ F₂` in at most 1 point.
  have hj_ex : ∃ j : Fin k, ((N₁.circuit j).U ∩ (F₁ ∪ F₂)).ncard ≤ 1 := by
    by_contra! hall
    have hfin_j : ∀ j : Fin k, ((N₁.circuit j).U ∩ (F₁ ∪ F₂)).Finite := by
      intro j
      refine D.finite_V.subset fun x ⟨hxC, hxF⟩ => ?_
      rcases hxF with hx1 | hx2
      · exact hF₁.2.2.1 ⟨hx1, (N₁.circuit j).U_sub_drawing hxC⟩
      · exact hF₂.2.2.1 ⟨hx2, (N₁.circuit j).U_sub_drawing hxC⟩
    have htwo : ∀ j : Fin k, ∃ a b : S,
        a ∈ (N₁.circuit j).U ∩ (F₁ ∪ F₂) ∧ b ∈ (N₁.circuit j).U ∩ (F₁ ∪ F₂) ∧ a ≠ b :=
      fun j => (Set.one_lt_ncard_iff (hfin_j j)).mp (hall j)
    choose a b ha hb hab using htwo
    let g : Fin k × Bool → S := fun jb => if jb.2 then a jb.1 else b jb.1
    have hmem : ∀ jb : Fin k × Bool, g jb ∈ (N₁.circuit jb.1).U ∩ (F₁ ∪ F₂) := by
      rintro ⟨j, _ | _⟩ <;> [exact hb j; exact ha j]
    have hginj : Function.Injective g := by
      rintro ⟨j₁, b₁⟩ ⟨j₂, b₂⟩ heq
      have hj_eq : j₁ = j₂ := by
        by_contra hne
        exact Set.disjoint_left.mp (N₁.pairwise_disjoint_circuits hΔ hne)
          (hmem (j₁, b₁)).1 (heq ▸ (hmem (j₂, b₂)).1)
      subst hj_eq
      cases b₁ <;> cases b₂
      · rfl
      · exact absurd heq.symm (hab j₁)
      · exact absurd heq (hab j₁)
      · rfl
    have hsub : range g ⊆ (D.V ∩ F₁) ∪ (D.V ∩ F₂) := by
      rintro _ ⟨jb, rfl⟩
      rcases (hmem jb).2 with hx1 | hx2
      · exact Or.inl ⟨hF₁.2.2.1 ⟨hx1, (N₁.circuit jb.1).U_sub_drawing (hmem jb).1⟩, hx1⟩
      · exact Or.inr ⟨hF₂.2.2.1 ⟨hx2, (N₁.circuit jb.1).U_sub_drawing (hmem jb).1⟩, hx2⟩
    have hfin_u : ((D.V ∩ F₁) ∪ (D.V ∩ F₂)).Finite :=
      (D.finite_V.subset inter_subset_left).union (D.finite_V.subset inter_subset_left)
    have hle1 := Set.ncard_le_ncard hsub hfin_u
    have hle2 := Set.ncard_union_le (D.V ∩ F₁) (D.V ∩ F₂)
    rw [Set.ncard_range_of_injective hginj, Nat.card_eq_fintype_card, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool] at hle1
    have hrho₁ := hF₁.2.2.2.2
    have hrho₂ := hF₂.2.2.2.2
    have hlt₁ : circuitRho C₁ < k := hB₁.rho_lt
    have hlt₂ : circuitRho C₂ < k := hB₂.rho_lt
    omega
  obtain ⟨j, hj⟩ := hj_ex
  let Cj := N₁.circuit j
  have hfin_u : (Cj.U ∩ (F₁ ∪ F₂)).Finite := by
    refine D.finite_V.subset fun x ⟨hxC, hxF⟩ => ?_
    rcases hxF with hx1 | hx2
    · exact hF₁.2.2.1 ⟨hx1, Cj.U_sub_drawing hxC⟩
    · exact hF₂.2.2.1 ⟨hx2, Cj.U_sub_drawing hxC⟩
  -- Step 3: `Cj` encloses `F₂`.
  have hsub_F₂Cj : F₂ ∩ Cj.U ⊆ Cj.U ∩ (F₁ ∪ F₂) :=
    fun _ ⟨hxF₂, hxC⟩ => ⟨hxC, Or.inr hxF₂⟩
  have hfin_F₂Cj : (F₂ ∩ Cj.U).Finite := hfin_u.subset hsub_F₂Cj
  have hle_F₂Cj : (F₂ ∩ Cj.U).ncard ≤ 1 :=
    (Set.ncard_le_ncard hsub_F₂Cj hfin_u).trans hj
  have hprec_F₂ : IsPreconnected (F₂ \ Cj.U) :=
    isPreconnected_oArc_sdiff_of_ncard_le_one hF₂.2.1 hfin_F₂Cj hle_F₂Cj
  have hC₁_sub_Cj : C₁.ins ⊆ Cj.ins ∧ discInt C₁.ins ⊆ discInt Cj.ins := by
    rw [← hC₀]
    exact N₁.insideDisc_subset_of_le hΔ (Nat.zero_le j.1)
  obtain ⟨y₀, hy₀F₂, hy₀C₁⟩ := hin
  have hy₀_int : y₀ ∈ discInt Cj.ins :=
    hC₁_sub_Cj.2 ((insideOArc_iff_mem_discInt hΔ C₁.isInside).mp hy₀C₁)
  have hy₀_sdiff : y₀ ∈ F₂ \ Cj.U :=
    ⟨hy₀F₂, fun h => hy₀_int.2 (Cj.isInside.2.2.1 ▸ h)⟩
  have hdis_F₂Cj : Disjoint (F₂ \ Cj.U) (discBd Cj.ins) := by
    rw [Cj.isInside.2.2.1]
    exact disjoint_sdiff_self_left
  have hF₂_sub_Cj : F₂ \ Cj.U ⊆ discInt Cj.ins := by
    rcases side_of_closedDisc hΔ Cj.isInside.1 (sdiff_subset.trans hF₂.1) Cj.isInside.2.1
      hprec_F₂ hdis_F₂Cj with hsub | hdis
    · exact hsub
    · exact absurd hy₀_int.1 (Set.disjoint_left.mp hdis hy₀_sdiff)
  have henc_Cj_F₂ : OArcEncloses Δ Cj.U F₂ :=
    fun x hx => (insideOArc_iff_mem_discInt hΔ Cj.isInside).mpr (hF₂_sub_Cj hx)
  -- Step 4: `F₁` encloses `Cj`.
  have hsub_CjF₁ : Cj.U ∩ F₁ ⊆ Cj.U ∩ (F₁ ∪ F₂) :=
    fun _ ⟨hxC, hxF₁⟩ => ⟨hxC, Or.inl hxF₁⟩
  have hfin_CjF₁ : (Cj.U ∩ F₁).Finite := hfin_u.subset hsub_CjF₁
  have hle_CjF₁ : (Cj.U ∩ F₁).ncard ≤ 1 :=
    (Set.ncard_le_ncard hsub_CjF₁ hfin_u).trans hj
  have hprec_Cj : IsPreconnected (Cj.U \ F₁) :=
    isPreconnected_oArc_sdiff_of_ncard_le_one Cj.isOArc_U hfin_CjF₁ hle_CjF₁
  have hdis_CjF₁ : Disjoint (Cj.U \ F₁) (discBd D₁) := by
    rw [hD₁.2.2.1]
    exact disjoint_sdiff_self_left
  have hCj_sub_Ck : Cj.ins ⊆ (N₁.circuit ik).ins ∧
      discInt Cj.ins ⊆ discInt (N₁.circuit ik).ins :=
    N₁.insideDisc_subset_of_le hΔ (Nat.le_sub_one_of_lt j.2)
  have hw_not_Cj : w ∉ discInt Cj.ins :=
    fun hw => (hCj_sub_Ck.2 hw).2 ((N₁.circuit ik).isInside.2.2.1 ▸ hwCk)
  obtain ⟨z₁, hz₁⟩ := C₁.isInside.2.1.nonempty_discInt
  have hC₁_sub_D₁ : C₁.ins ⊆ D₁ ∧ discInt C₁.ins ⊆ discInt D₁ :=
    insideDisc_subset_of_oArcEncloses hΔ hD₁ C₁.isInside hF₁.2.2.2.1
  have hz₁_D₁ : z₁ ∈ D₁ := (hC₁_sub_D₁.2 hz₁).1
  have hz₁_Cj : z₁ ∈ discInt Cj.ins := hC₁_sub_Cj.2 hz₁
  have hCj_sub_D₁ : Cj.U \ F₁ ⊆ discInt D₁ := by
    rcases side_of_closedDisc hΔ hD₁.1 (sdiff_subset.trans Cj.U_sub_disc) hD₁.2.1
      hprec_Cj hdis_CjF₁ with hsub | hdis
    · exact hsub
    · exfalso
      have hdis_int : Disjoint (discInt D₁) (discBd Cj.ins) := by
        rw [Cj.isInside.2.2.1]
        refine Set.disjoint_left.mpr fun x hxD₁ hxCj => ?_
        have hxF₁ : x ∉ F₁ := fun h => hxD₁.2 (hD₁.2.2.1 ▸ h)
        exact Set.disjoint_left.mp hdis ⟨hxCj, hxF₁⟩ hxD₁.1
      have hD₁_sub_Cj := subset_of_discInt_meets hΔ hD₁.1 Cj.isInside.1 hD₁.2.1 Cj.isInside.2.1
        hdis_int ⟨z₁, hz₁_D₁, hz₁_Cj⟩
      exact hw_not_Cj (hD₁_sub_Cj.2 hw_int₁)
  have henc_F₁_Cj : OArcEncloses Δ F₁ Cj.U :=
    fun x hx => (insideOArc_iff_mem_discInt hΔ hD₁).mpr (hCj_sub_D₁ hx)
  exact oArcEncloses_trans hΔ hF₁.1 Cj.U_sub_disc hF₁.2.1 Cj.isOArc_U henc_F₁_Cj henc_Cj_F₂

/-- If `F₃` and `F₄` bound disjoint open discs in `Δ`, then `Γ(F₃)` and `Γ(F₄)` are disjoint. -/
theorem disjoint_edgesInsideOArc_of_boundDisjointOpenDiscs {D : Drawing S} {Δ F₃ F₄ : Set S}
    (hdis : BoundDisjointOpenDiscs Δ F₃ F₄) :
    Disjoint (edgesInsideOArc D Δ F₃) (edgesInsideOArc D Δ F₄) := by
  refine Set.disjoint_left.mpr fun e he₃ he₄ => ?_
  obtain ⟨x, hxe⟩ := he₃.1.1
  exact Set.disjoint_left.mp hdis (he₃.2 x hxe) (he₄.2 x hxe)

/-- Minimal-ring form of **(6.7)**: if `C₁, C₂` are bosses and `F₁, F₂` are minimal `C₁`-, `C₂`-rings
then either `Γ(F₁) ⊆ Γ(F₂)`,
`Γ(F₂) ⊆ Γ(F₁)`, or `Γ(F₁)` and `Γ(F₂)` are disjoint. -/
theorem edgesInsideOArc_trichotomy_of_isBoss {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hB₁ : IsBoss D Δ C₁) (hB₂ : IsBoss D Δ C₂)
    (hF₁ : IsMinimalCRing C₁ F₁) (hF₂ : IsMinimalCRing C₂ F₂) :
    edgesInsideOArc D Δ F₁ ⊆ edgesInsideOArc D Δ F₂ ∨
      edgesInsideOArc D Δ F₂ ⊆ edgesInsideOArc D Δ F₁ ∨
      Disjoint (edgesInsideOArc D Δ F₁) (edgesInsideOArc D Δ F₂) := by
  by_cases hin₂₁ : ∃ y ∈ F₂, InsideOArc Δ C₁.U y
  · have henc := oArcEncloses_of_isBoss_meets_inside hΔ hB₁ hB₂ hF₁.1 hF₂.1 hin₂₁
    exact Or.inr (Or.inl
      (edgesInsideOArc_mono_of_oArcEncloses hΔ hF₁.1.1 hF₂.1.1 hF₁.1.2.1 hF₂.1.2.1 henc))
  · by_cases hin₁₂ : ∃ y ∈ F₁, InsideOArc Δ C₂.U y
    · have henc := oArcEncloses_of_isBoss_meets_inside hΔ hB₂ hB₁ hF₂.1 hF₁.1 hin₁₂
      exact Or.inl
        (edgesInsideOArc_mono_of_oArcEncloses hΔ hF₂.1.1 hF₁.1.1 hF₂.1.2.1 hF₁.1.2.1 henc)
    · push Not at hin₂₁ hin₁₂
      by_cases hdis₂ : BoundDisjointOpenDiscs Δ F₂ C₁.U
      · by_cases hdis₁ : BoundDisjointOpenDiscs Δ F₁ C₂.U
        · obtain ⟨F₃, F₄, hCR₃, hCR₄, henc₁, henc₂, hdis₃₄⟩ :=
            theorem_6_5_proof hΔ hF₁.1 hF₂.1 hdis₁ hdis₂
          have hsub₁ : edgesInsideOArc D Δ F₃ ⊆ edgesInsideOArc D Δ F₁ :=
            edgesInsideOArc_mono_of_oArcEncloses hΔ hF₁.1.1 hCR₃.1 hF₁.1.2.1 hCR₃.2.1 henc₁
          have hsub₂ : edgesInsideOArc D Δ F₄ ⊆ edgesInsideOArc D Δ F₂ :=
            edgesInsideOArc_mono_of_oArcEncloses hΔ hF₂.1.1 hCR₄.1 hF₂.1.2.1 hCR₄.2.1 henc₂
          have heq₁ : edgesInsideOArc D Δ F₃ = edgesInsideOArc D Δ F₁ :=
            hsub₁.eq_of_not_ssubset (hF₁.2 F₃ hCR₃)
          have heq₂ : edgesInsideOArc D Δ F₄ = edgesInsideOArc D Δ F₂ :=
            hsub₂.eq_of_not_ssubset (hF₂.2 F₄ hCR₄)
          exact Or.inr (Or.inr
            (heq₁ ▸ heq₂ ▸ disjoint_edgesInsideOArc_of_boundDisjointOpenDiscs hdis₃₄))
        · obtain ⟨D₁, hD₁, _⟩ := disc_oArc Δ F₁ hΔ hF₁.1.1 hF₁.1.2.1
          obtain ⟨z, hzF₁, hzC₂⟩ := Set.not_disjoint_iff.mp hdis₁
          have hz_D₁ : z ∈ discInt D₁ := (insideOArc_iff_mem_discInt hΔ hD₁).mp hzF₁
          have hz_C₂ : z ∈ discInt C₂.ins := (insideOArc_iff_mem_discInt hΔ C₂.isInside).mp hzC₂
          have hdis_bd : Disjoint (discInt C₂.ins) (discBd D₁) := by
            rw [hD₁.2.2.1]
            exact Set.disjoint_left.mpr fun x hxC₂ hxF₁ =>
              hin₁₂ x hxF₁ ((insideOArc_iff_mem_discInt hΔ C₂.isInside).mpr hxC₂)
          have hC₂_D₁ := subset_of_discInt_meets hΔ C₂.isInside.1 hD₁.1 C₂.isInside.2.1 hD₁.2.1
            hdis_bd ⟨z, hz_C₂.1, hz_D₁⟩
          have henc₁ : OArcEncloses Δ F₁ C₂.U := by
            rw [oArcEncloses_iff_subset hΔ hD₁]
            exact (C₂.isInside.2.2.1 ▸ discBd_subset C₂.ins).trans hC₂_D₁.1
          obtain ⟨F₃, hCR₃, henc₂, henc₁'⟩ :=
            exists_cRing_enclosed_of_oArcEncloses hΔ hF₂.1 hF₁.1 henc₁
          have hsub₂ : edgesInsideOArc D Δ F₃ ⊆ edgesInsideOArc D Δ F₂ :=
            edgesInsideOArc_mono_of_oArcEncloses hΔ hF₂.1.1 hCR₃.1 hF₂.1.2.1 hCR₃.2.1 henc₂
          have hsub₁ : edgesInsideOArc D Δ F₃ ⊆ edgesInsideOArc D Δ F₁ :=
            edgesInsideOArc_mono_of_oArcEncloses hΔ hF₁.1.1 hCR₃.1 hF₁.1.2.1 hCR₃.2.1 henc₁'
          have heq₂ : edgesInsideOArc D Δ F₃ = edgesInsideOArc D Δ F₂ :=
            hsub₂.eq_of_not_ssubset (hF₂.2 F₃ hCR₃)
          exact Or.inr (Or.inl (heq₂ ▸ hsub₁))
      · obtain ⟨D₂, hD₂, _⟩ := disc_oArc Δ F₂ hΔ hF₂.1.1 hF₂.1.2.1
        obtain ⟨z, hzF₂, hzC₁⟩ := Set.not_disjoint_iff.mp hdis₂
        have hz_D₂ : z ∈ discInt D₂ := (insideOArc_iff_mem_discInt hΔ hD₂).mp hzF₂
        have hz_C₁ : z ∈ discInt C₁.ins := (insideOArc_iff_mem_discInt hΔ C₁.isInside).mp hzC₁
        have hdis_bd : Disjoint (discInt C₁.ins) (discBd D₂) := by
          rw [hD₂.2.2.1]
          exact Set.disjoint_left.mpr fun x hxC₁ hxF₂ =>
            hin₂₁ x hxF₂ ((insideOArc_iff_mem_discInt hΔ C₁.isInside).mpr hxC₁)
        have hC₁_D₂ := subset_of_discInt_meets hΔ C₁.isInside.1 hD₂.1 C₁.isInside.2.1 hD₂.2.1
          hdis_bd ⟨z, hz_C₁.1, hz_D₂⟩
        have henc₂ : OArcEncloses Δ F₂ C₁.U := by
          rw [oArcEncloses_iff_subset hΔ hD₂]
          exact (C₁.isInside.2.2.1 ▸ discBd_subset C₁.ins).trans hC₁_D₂.1
        obtain ⟨F₃, hCR₃, henc₁, henc₂'⟩ :=
          exists_cRing_enclosed_of_oArcEncloses hΔ hF₁.1 hF₂.1 henc₂
        have hsub₁ : edgesInsideOArc D Δ F₃ ⊆ edgesInsideOArc D Δ F₁ :=
          edgesInsideOArc_mono_of_oArcEncloses hΔ hF₁.1.1 hCR₃.1 hF₁.1.2.1 hCR₃.2.1 henc₁
        have hsub₂ : edgesInsideOArc D Δ F₃ ⊆ edgesInsideOArc D Δ F₂ :=
          edgesInsideOArc_mono_of_oArcEncloses hΔ hF₂.1.1 hCR₃.1 hF₂.1.2.1 hCR₃.2.1 henc₂'
        have heq₁ : edgesInsideOArc D Δ F₃ = edgesInsideOArc D Δ F₁ :=
          hsub₁.eq_of_not_ssubset (hF₁.2 F₃ hCR₃)
        exact Or.inl (heq₁ ▸ hsub₂)

/-- **(6.7)** Let `D` be a drawing in a disc `Δ`, and let `C₁, C₂` be bosses.
Then either `Δ(C₁) ⊆ Δ(C₂)`, or `Δ(C₂) ⊆ Δ(C₁)`, or `Δ(C₁) ∩ Δ(C₂) = ∅`.
(GM VIII Section 6, page 266.) -/
theorem theorem_6_7_proof {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C₁ C₂ : DiscCircuit D Δ}
    (hB₁ : IsBoss D Δ C₁) (hB₂ : IsBoss D Δ C₂) :
    bossDelta D Δ C₁ ⊆ bossDelta D Δ C₂ ∨
      bossDelta D Δ C₂ ⊆ bossDelta D Δ C₁ ∨
      Disjoint (bossDelta D Δ C₁) (bossDelta D Δ C₂) := by
  by_cases hex₁ : ∃ F₁, IsMinimalCRing C₁ F₁
  · by_cases hex₂ : ∃ F₂, IsMinimalCRing C₂ F₂
    · obtain ⟨F₁, hF₁⟩ := hex₁
      obtain ⟨F₂, hF₂⟩ := hex₂
      have hΔ₁ : bossDelta D Δ C₁ = edgesInsideOArc D Δ F₁ := by
        ext e
        simp only [bossDelta, mem_iUnion]
        constructor
        · rintro ⟨F', hF', he⟩
          rwa [theorem_6_6_proof hΔ hF₁ hF']
        · intro he
          exact ⟨F₁, hF₁, he⟩
      have hΔ₂ : bossDelta D Δ C₂ = edgesInsideOArc D Δ F₂ := by
        ext e
        simp only [bossDelta, mem_iUnion]
        constructor
        · rintro ⟨F', hF', he⟩
          rwa [theorem_6_6_proof hΔ hF₂ hF']
        · intro he
          exact ⟨F₂, hF₂, he⟩
      rw [hΔ₁, hΔ₂]
      exact edgesInsideOArc_trichotomy_of_isBoss hΔ hB₁ hB₂ hF₁ hF₂
    · push Not at hex₂
      have hΔ₂ : bossDelta D Δ C₂ = ∅ := by
        ext e
        simp only [bossDelta, mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
        intro F hF
        exact absurd hF (hex₂ F)
      rw [hΔ₂]
      exact Or.inr (Or.inl (empty_subset _))
  · push Not at hex₁
    have hΔ₁ : bossDelta D Δ C₁ = ∅ := by
      ext e
      simp only [bossDelta, mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      intro F hF
      exact absurd hF (hex₁ F)
    rw [hΔ₁]
    exact Or.inl (empty_subset _)

end GM08
end GraphMinor
