module

public import GraphMinor.Crossing.Statements
import GraphMinor.Crossing.CutSec2Fan

/-!
# Section 8 of the crossing extractor: the maximum two-cut lemma

This file proves Lemma 6 (`Lemma6Statement`) from Section 8 of
`docs/crossing/crossing_extractor.tex`, together with reusable separator and `sourceSide` lemmas
also used in Section 9.
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set Finset

universe u

variable {W : Type u}

/-- If `u ∈ S₀` and no edge of `B` joins `S₀` to `R \ S₀`, then any walk in `R` starting in `S₀`
ends in `S₀`. -/
theorem mem_of_walk_closed {B : SimpleGraph W} {S₀ R : Set W}
    (hclosed : ∀ a ∈ S₀, ∀ b ∈ R, B.Adj a b → b ∈ S₀) :
    ∀ {u v : W} (q : B.Walk u v), (∀ y ∈ q.support, y ∈ R) → u ∈ S₀ → v ∈ S₀
  | _, _, .nil, _, hu => hu
  | u, _, @Walk.cons _ _ _ w _ hadj rest, hsupp, hu => by
    have hwR : w ∈ R := hsupp w (List.mem_cons_of_mem _ (Walk.start_mem_support _))
    have hwS₀ : w ∈ S₀ := hclosed u hu w hwR hadj
    exact mem_of_walk_closed hclosed rest (fun y hy => hsupp y (List.mem_cons_of_mem _ hy)) hwS₀

/-- Under `RootedConn B T x k`, every `z`-`x` separator in `T` (for `z, x ∈ T`) has size at least
`k`. -/
theorem le_card_of_isSeparator_of_rootedConn {B : SimpleGraph W} {T : Set W} {x z : W} {k : ℕ}
    {X : Finset W} (hR : RootedConn B T x k) (hxT : x ∈ T) (hzT : z ∈ T)
    (hsep : IsSeparator B T z x X) : k ≤ X.card := by
  by_contra hlt
  push Not at hlt
  have hX_sub : (X : Set W) ⊆ T \ {x} :=
    fun y hy => ⟨(hsep.1 hy).1, fun h => (hsep.1 hy).2 (Or.inr h)⟩
  have hconn := hR X hX_sub hlt
  have hz_mem : z ∈ T \ X := ⟨hzT, fun hzX => (hsep.1 hzX).2 (Or.inl rfl)⟩
  have hx_mem : x ∈ T \ X := ⟨hxT, fun hxX => (hsep.1 hxX).2 (Or.inr rfl)⟩
  exact hsep.2 (hconn.2 z hz_mem x hx_mem)

/-- Under `RootedConn B T x k`, any `z`-`x` separator of size at most `k` has size `k` and is a
minimum separator. -/
theorem isMinSeparator_of_le_of_rootedConn {B : SimpleGraph W} {T : Set W} {x z : W} {k : ℕ}
    {X : Finset W} (hR : RootedConn B T x k) (hxT : x ∈ T) (hzT : z ∈ T)
    (hsep : IsSeparator B T z x X) (hle : X.card ≤ k) :
    IsMinSeparator B T z x X ∧ X.card = k := by
  have hge := le_card_of_isSeparator_of_rootedConn hR hxT hzT hsep
  have heq : X.card = k := by omega
  refine ⟨⟨hsep, fun X' hsep' => ?_⟩, heq⟩
  have hge' := le_card_of_isSeparator_of_rootedConn hR hxT hzT hsep'
  omega

/-- The target `x` is never in `sourceSide B T x X`. -/
theorem not_mem_sourceSide_self {B : SimpleGraph W} {T : Set W} {x : W} {X : Finset W} :
    x ∉ sourceSide B T x X := by
  rintro ⟨hxT, hxX, hnot_reach⟩
  exact hnot_reach (ReachIn.refl ⟨hxT, hxX⟩)

/-- For a separator `X` of `z` and `x` with `z ∈ T`, `z` belongs to `sourceSide B T x X`. -/
theorem mem_sourceSide_of_isSeparator {B : SimpleGraph W} {T : Set W} {z x : W} {X : Finset W}
    (hzT : z ∈ T) (hsep : IsSeparator B T z x X) : z ∈ sourceSide B T x X :=
  ⟨hzT, fun hzX => (hsep.1 hzX).2 (Or.inl rfl), hsep.2⟩

/-- Any neighbour in `T` of a vertex in `sourceSide B T x X` lies in `sourceSide B T x X` or in
`X`. -/
theorem mem_sourceSide_or_mem_of_adj {B : SimpleGraph W} {T : Set W} {x a b : W} {X : Finset W}
    (ha : a ∈ sourceSide B T x X) (hbT : b ∈ T) (hadj : B.Adj a b) :
    b ∈ sourceSide B T x X ∨ b ∈ X := by
  by_cases hbX : b ∈ X
  · exact Or.inr hbX
  · refine Or.inl ⟨hbT, hbX, fun hreach => ?_⟩
    have ha_TX : a ∈ T \ X := ⟨ha.1, ha.2.1⟩
    have hb_TX : b ∈ T \ X := ⟨hbT, hbX⟩
    exact ha.2.2 ((ReachIn.of_adj hadj ha_TX hb_TX).trans hreach)

open Classical in
/-- Every vertex `p` of a minimum `z`-`x` separator `X` (with `z ∈ T`) has a neighbour in
`sourceSide B T x X`. -/
theorem exists_adj_sourceSide_of_isMinSeparator {B : SimpleGraph W} {T : Set W} {z x p : W}
    {X : Finset W} (hzT : z ∈ T) (hmin : IsMinSeparator B T z x X) (hpX : p ∈ X) :
    ∃ h ∈ sourceSide B T x X, B.Adj h p := by
  by_contra hno
  push Not at hno
  let X' : Finset W := X.erase p
  have hX'_sub : (X' : Set W) ⊆ T \ {z, x} :=
    fun y hy => hmin.1.1 (Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hy)))
  have hX'_sep : IsSeparator B T z x X' := by
    refine ⟨hX'_sub, fun ⟨q, hq⟩ => ?_⟩
    have hclosed : ∀ a ∈ sourceSide B T x X, ∀ b ∈ T \ (X' : Set W),
        B.Adj a b → b ∈ sourceSide B T x X := by
      intro a ha b hb hadj
      rcases mem_sourceSide_or_mem_of_adj ha hb.1 hadj with hbU | hbX
      · exact hbU
      · by_cases hbp : b = p
        · subst hbp
          exact False.elim (hno a ha hadj)
        · exact False.elim (hb.2 (Finset.mem_erase.mpr ⟨hbp, hbX⟩))
    have hxU : x ∈ sourceSide B T x X :=
      mem_of_walk_closed hclosed q hq (mem_sourceSide_of_isSeparator hzT hmin.1)
    exact not_mem_sourceSide_self hxU
  have hle := hmin.2 X' hX'_sep
  have hlt : X'.card < X.card := Finset.card_erase_lt_of_mem hpX
  omega

open Classical in
/-- Core version of Lemma 6 (Section 8) without unused finiteness or support hypotheses. -/
theorem isUnseparable_of_isMaxSourceSeparator {B : SimpleGraph W} {T : Set W} {x z : W}
    {X : Finset W} (hxT : x ∈ T) (hzT : z ∈ T) (hR2 : RootedConn B T x 2)
    (hX_max : IsMaxSourceSeparator B T z x X) (hX_card : X.card = 2) :
    ∀ p ∈ X, IsUnseparable B T p x 2 := by
  intro p hpX
  by_contra hp_sep
  unfold IsUnseparable at hp_sep
  push Not at hp_sep
  rcases hp_sep with ⟨Y, hY_sub, hY_le, hY_nreach⟩
  have hpT : p ∈ T := (hX_max.1.1.1 hpX).1
  have hY_sep : IsSeparator B T p x Y := ⟨hY_sub, hY_nreach⟩
  obtain ⟨_, hY_card⟩ := isMinSeparator_of_le_of_rootedConn hR2 hxT hpT hY_sep hY_le
  let U : Set W := sourceSide B T x X
  let V : Set W := sourceSide B T x Y
  have hzU : z ∈ U := mem_sourceSide_of_isSeparator hzT hX_max.1.1
  have hpV : p ∈ V := mem_sourceSide_of_isSeparator hpT hY_sep
  let J_sep : Finset W := (X ∪ Y).filter (fun w => ¬ (w ∈ U ∨ w ∈ V))
  let M_sep : Finset W := (X ∩ Y) ∪ (X ∪ Y).filter (fun w => w ∈ U ∨ w ∈ V)
  have hdisj_M : Disjoint (X ∩ Y) ((X ∪ Y).filter (fun w => w ∈ U ∨ w ∈ V)) := by
    rw [Finset.disjoint_left]
    intro w hw_inter hw_filt
    rw [Finset.mem_inter] at hw_inter
    rw [Finset.mem_filter] at hw_filt
    rcases hw_filt.2 with hwU | hwV
    · exact hwU.2.1 hw_inter.1
    · exact hwV.2.1 hw_inter.2
  have hsum_card : J_sep.card + M_sep.card = 4 := by
    dsimp only [J_sep, M_sep]
    have hM_card : ((X ∩ Y) ∪ (X ∪ Y).filter (fun w => w ∈ U ∨ w ∈ V)).card =
        (X ∩ Y).card + ((X ∪ Y).filter (fun w => w ∈ U ∨ w ∈ V)).card :=
      Finset.card_union_of_disjoint hdisj_M
    have hfilt := Finset.card_filter_add_card_filter_not (s := X ∪ Y)
      (p := fun w => w ∈ U ∨ w ∈ V)
    have hunion := Finset.card_union_add_card_inter X Y
    omega
  have hX_sub_Tx : (X : Set W) ⊆ T \ {x} :=
    fun w hw => ⟨(hX_max.1.1.1 hw).1, fun h => (hX_max.1.1.1 hw).2 (Or.inr h)⟩
  have hY_sub_Tx : (Y : Set W) ⊆ T \ {x} :=
    fun w hw => ⟨(hY_sub hw).1, fun h => (hY_sub hw).2 (Or.inr h)⟩
  have hXY_sub_Tx : ((X ∪ Y : Finset W) : Set W) ⊆ T \ {x} := by
    rw [Finset.coe_union]
    exact Set.union_subset hX_sub_Tx hY_sub_Tx
  have hM_ge : 2 ≤ M_sep.card := by
    by_cases hUV : (U ∩ V).Nonempty
    · rcases hUV with ⟨u, huU, huV⟩
      have hu_not_XY : u ∉ X ∪ Y := by
        rw [Finset.mem_union, not_or]
        exact ⟨huU.2.1, huV.2.1⟩
      have hM_sub_XY : M_sep ⊆ X ∪ Y :=
        Finset.union_subset (Finset.inter_subset_left.trans Finset.subset_union_left)
          (Finset.filter_subset _ _)
      have hM_sub_ux : (M_sep : Set W) ⊆ T \ {u, x} := by
        intro w hw
        have hw_Tx := hXY_sub_Tx (hM_sub_XY hw)
        refine ⟨hw_Tx.1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun hwu => hu_not_XY (hwu ▸ hM_sub_XY hw), hw_Tx.2⟩
      have hM_sep : IsSeparator B T u x M_sep := by
        refine ⟨hM_sub_ux, fun ⟨q, hq⟩ => ?_⟩
        have hclosed : ∀ a ∈ U ∩ V, ∀ b ∈ T \ (M_sep : Set W), B.Adj a b → b ∈ U ∩ V := by
          intro a ⟨haU, haV⟩ b ⟨hbT, hbM⟩ hadj
          have hb_UX := mem_sourceSide_or_mem_of_adj haU hbT hadj
          have hb_VY := mem_sourceSide_or_mem_of_adj haV hbT hadj
          rcases hb_UX with hbU | hbX
          · rcases hb_VY with hbV | hbY
            · exact ⟨hbU, hbV⟩
            · exfalso
              apply hbM
              rw [Finset.mem_coe, Finset.mem_union, Finset.mem_filter, Finset.mem_union]
              exact Or.inr ⟨Or.inr hbY, Or.inl hbU⟩
          · rcases hb_VY with hbV | hbY
            · exfalso
              apply hbM
              rw [Finset.mem_coe, Finset.mem_union, Finset.mem_filter, Finset.mem_union]
              exact Or.inr ⟨Or.inl hbX, Or.inr hbV⟩
            · exfalso
              apply hbM
              rw [Finset.mem_coe, Finset.mem_union, Finset.mem_inter]
              exact Or.inl ⟨hbX, hbY⟩
        have hxUV : x ∈ U ∩ V := mem_of_walk_closed hclosed q hq ⟨huU, huV⟩
        exact not_mem_sourceSide_self hxUV.1
      exact le_card_of_isSeparator_of_rootedConn hR2 hxT huU.1 hM_sep
    · rw [Set.not_nonempty_iff_eq_empty] at hUV
      obtain ⟨h, hhU, hadj_hp⟩ := exists_adj_sourceSide_of_isMinSeparator hzT hX_max.1 hpX
      have hh_not_V : h ∉ V := fun hhV => by
        have : h ∈ (∅ : Set W) := hUV ▸ ⟨hhU, hhV⟩
        exact this
      have hhY : h ∈ Y := by
        rcases mem_sourceSide_or_mem_of_adj hpV hhU.1 hadj_hp.symm with hhV | hhY
        · exact False.elim (hh_not_V hhV)
        · exact hhY
      have hpM : p ∈ M_sep := by
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_union]
        exact Or.inr ⟨Or.inl hpX, Or.inr hpV⟩
      have hhM : h ∈ M_sep := by
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_union]
        exact Or.inr ⟨Or.inr hhY, Or.inl hhU⟩
      have hph_ne : p ≠ h := fun h_eq => hhU.2.1 (h_eq ▸ hpX)
      have hsub : ({p, h} : Finset W) ⊆ M_sep := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hpM
        · exact hhM
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hph_ne] at hle
      exact hle
  have hJ_le : J_sep.card ≤ 2 := by omega
  have hUV_sub_source : U ∪ V ⊆ sourceSide B T x J_sep := by
    intro w hw
    have hwT : w ∈ T := by
      rcases hw with hwU | hwV
      · exact hwU.1
      · exact hwV.1
    have hw_not_J : w ∉ J_sep := by
      intro hwJ
      rw [Finset.mem_filter] at hwJ
      exact hwJ.2 hw
    refine ⟨hwT, hw_not_J, fun ⟨q, hq⟩ => ?_⟩
    have hclosed : ∀ a ∈ U ∪ V, ∀ b ∈ T \ (J_sep : Set W), B.Adj a b → b ∈ U ∪ V := by
      intro a ha b ⟨hbT, hbJ⟩ hadj
      have hb_all : (b ∈ U ∨ b ∈ V) ∨ (b ∈ X ∨ b ∈ Y) := by
        rcases ha with haU | haV
        · rcases mem_sourceSide_or_mem_of_adj haU hbT hadj with hbU | hbX
          · exact Or.inl (Or.inl hbU)
          · exact Or.inr (Or.inl hbX)
        · rcases mem_sourceSide_or_mem_of_adj haV hbT hadj with hbV | hbY
          · exact Or.inl (Or.inr hbV)
          · exact Or.inr (Or.inr hbY)
      rcases hb_all with hbUV | hbXY
      · exact hbUV
      · by_contra hb_not_UV
        apply hbJ
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_union]
        exact ⟨hbXY, hb_not_UV⟩
    have hxUV : x ∈ U ∪ V := mem_of_walk_closed hclosed q hq hw
    rcases hxUV with hxU | hxV
    · exact not_mem_sourceSide_self hxU
    · exact not_mem_sourceSide_self hxV
  have hz_source_J : z ∈ sourceSide B T x J_sep := hUV_sub_source (Or.inl hzU)
  have hp_source_J : p ∈ sourceSide B T x J_sep := hUV_sub_source (Or.inr hpV)
  have hJ_sub_zx : (J_sep : Set W) ⊆ T \ {z, x} := by
    intro w hw
    have hw_XY : w ∈ X ∪ Y := Finset.filter_subset _ _ hw
    have hw_Tx := hXY_sub_Tx hw_XY
    refine ⟨hw_Tx.1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hwz => hz_source_J.2.1 (hwz ▸ hw), hw_Tx.2⟩
  have hJ_sep : IsSeparator B T z x J_sep := ⟨hJ_sub_zx, hz_source_J.2.2⟩
  obtain ⟨hJ_min, _⟩ := isMinSeparator_of_le_of_rootedConn hR2 hxT hzT hJ_sep hJ_le
  have hpU : p ∈ U := hX_max.2 J_sep hJ_min hp_source_J
  exact hpU.2.1 hpX

/-- **Lemma 6** (Section 8): if `𝓡_2(B, x)` holds and `X` is a maximum-source-side minimum `z`-`x`
separator of size `2`, then no vertex `p ∈ X` can be separated from `x` by at most `2` other
vertices. -/
theorem lemma6_proved : Lemma6Statement :=
  fun _ _ _ _ _ _ _ hxT hzT _ hR2 hX_max hX_card =>
    isUnseparable_of_isMaxSourceSeparator hxT hzT hR2 hX_max hX_card

end GraphMinor.Crossing
