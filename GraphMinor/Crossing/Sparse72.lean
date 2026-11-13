module

public import GraphMinor.Crossing.Statements
import GraphMinor.Crossing.SparseForest
import GraphMinor.Crossing.PlanarEuler
import GraphMinor.Crossing.PlanarFactT
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# Sparsification preserves cleanliness, nonplanarity and crossings (Section 7.2 of the note)

This file proves the two claims of Section 7.2 of `docs/crossing/crossing_extractor.tex`:
* `sec72Count_proved` (`Sec72CountStatement`): the retained graph `sparsifyGraph K D Fs E₀` has at
  most `4N + N + (3N - 5) ≤ 8N - 5` edges.
* `sec72_proved` (`Sec72Statement`): `sparsifyGraph K D Fs E₀` remains clean (by Lemma 5),
  nonplanar (by Euler's planar edge bound), and crossed (by Fact T).
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set

universe u

variable {V W : Type u}

/-! ### Helper lemmas on `forestUnion`, `apex` and `sparsifyGraph` -/

private lemma reachIn_mono_graph {G G' : SimpleGraph W} {T : Set W} {a b : W}
    (hle : G ≤ G') (h : ReachIn G T a b) : ReachIn G' T a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.map (Hom.ofLE hle), fun y hy => hp y (by simpa using hy)⟩

private lemma scanForest_le [DecidableEq W] (G : SimpleGraph W) (σ : List W) :
    scanForest G σ ≤ G := by
  intro a b h
  rcases h with h | h
  · exact h.1
  · exact h.1.symm

private lemma forestUnion_le [DecidableEq W] {G : SimpleGraph W} {T : Set W}
    {Fs : List (SimpleGraph W)} (hFs : IsScanFirstSequence G T Fs) :
    forestUnion Fs ≤ G := by
  induction Fs generalizing G with
  | nil => exact bot_le
  | cons F Fs ih =>
    obtain ⟨⟨σ, _, rfl⟩, hFs'⟩ := hFs
    exact sup_le (scanForest_le G σ) (le_trans (ih hFs') sdiff_le)

private lemma edgeSet_finite_of_isSupportedOn {G : SimpleGraph W} {T : Set W}
    (hT : T.Finite) (hG : HP25.IsSupportedOn G T) : G.edgeSet.Finite := by
  have hsub : G.edgeSet ⊆ (fun p : W × W => s(p.1, p.2)) '' (T ×ˢ T) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeSet] at he
      exact ⟨(u, v), ⟨hG he, hG he.symm⟩, rfl⟩
  exact ((hT.prod hT).image _).subset hsub

private lemma apexVerts_eq_insert (S : Set V) :
    apexVerts S = insert none (some '' S) := by
  ext x
  cases x <;> simp [apexVerts]

private lemma apexVerts_finite {S : Set V} (hS : S.Finite) :
    (apexVerts S).Finite := by
  rw [apexVerts_eq_insert]
  exact (hS.image some).insert none

private lemma apexVerts_ncard {S : Set V} (hS : S.Finite) :
    (apexVerts S).ncard = S.ncard + 1 := by
  rw [apexVerts_eq_insert, Set.ncard_insert_of_notMem (by simp) (hS.image some),
    Set.ncard_image_of_injective S (Option.some_injective V)]

variable [DecidableEq V]

private lemma mem_S_of_mem_cycle {K : SimpleGraph V} {S : Set V} {D : List V}
    (hK : HP25.IsSupportedOn K S) (hD : HP25.IsCycleList K D) :
    ∀ v ∈ D, v ∈ S := by
  intro v hv
  have hidx : D.idxOf v < (D.rotate 1).length := by
    rw [List.length_rotate]
    exact List.idxOf_lt_length_of_mem hv
  let w := (D.rotate 1)[D.idxOf v]'hidx
  have hw : (D.rotate 1)[D.idxOf v]? = some w := List.getElem?_eq_getElem hidx
  have hzip : (D.zip (D.rotate 1))[D.idxOf v]? = some (v, w) :=
    List.getElem?_zip_eq_some.mpr ⟨List.getElem?_idxOf hv, hw⟩
  exact hK (hD.2.2 (v, w) (List.mem_of_getElem? hzip))

private lemma cycle_length_le_ncard {K : SimpleGraph V} {S : Set V} {D : List V}
    (hS : S.Finite) (hK : HP25.IsSupportedOn K S) (hD : HP25.IsCycleList K D) :
    D.length ≤ S.ncard := by
  have hsub : D.toFinset ⊆ hS.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact hS.mem_toFinset.mpr (mem_S_of_mem_cycle hK hD x hx)
  rw [← List.toFinset_card_of_nodup hD.2.1, Set.ncard_eq_toFinset_card S hS]
  exact Finset.card_le_card hsub

private lemma isSupportedOn_apex {K : SimpleGraph V} {S : Set V} {D : List V}
    (hK : HP25.IsSupportedOn K S) (hD : HP25.IsCycleList K D) :
    HP25.IsSupportedOn (apex K D) (apexVerts S) := by
  intro x y hxy
  cases x with
  | none => exact Or.inl rfl
  | some u =>
    cases y with
    | none => exact Or.inr ⟨u, mem_S_of_mem_cycle hK hD u hxy, rfl⟩
    | some v => exact Or.inr ⟨u, hK hxy, rfl⟩

private lemma forestUnion_le_apex_sparsifyGraph {K : SimpleGraph V} {S : Set V} {D : List V}
    {Fs : List (SimpleGraph (Option V))} {E₀ : Set (Sym2 V)}
    (hFs : IsScanFirstSequence (apex K D) (apexVerts S) Fs) :
    forestUnion Fs ≤ apex (sparsifyGraph K D Fs E₀) D := by
  intro x y hxy
  have hadj : (apex K D).Adj x y := forestUnion_le hFs hxy
  cases x with
  | none =>
    cases y with
    | none => exact False.elim hadj
    | some b => exact hadj
  | some a =>
    cases y with
    | none => exact hadj
    | some b => exact ⟨hadj, Or.inl hxy⟩

/-! ### Section 7.2: Edge count of the retained graph -/

/-- **The size of the retained graph** (Section 7.2): "The kept graph has at most
$4N+N+(3N-5)=8N-5$ edges." -/
theorem sec72Count_proved : Sec72CountStatement := by
  intro V _ K S D Fs E₀ hSfin hK hD hspar
  obtain ⟨hFs, hFslen, hE₀sub, hE₀fin, hE₀card⟩ := hspar
  have hKfin : K.edgeSet.Finite := edgeSet_finite_of_isSupportedOn hSfin hK
  have hapex_supp : HP25.IsSupportedOn (apex K D) (apexVerts S) := isSupportedOn_apex hK hD
  have hFU_le : forestUnion Fs ≤ apex K D := forestUnion_le hFs
  have hFU_supp : HP25.IsSupportedOn (forestUnion Fs) (apexVerts S) :=
    fun _ _ h => hapex_supp (hFU_le h)
  have hFU_fin : (forestUnion Fs).edgeSet.Finite :=
    edgeSet_finite_of_isSupportedOn (apexVerts_finite hSfin) hFU_supp
  have hFU_card : (forestUnion Fs).edgeSet.ncard ≤ 4 * S.ncard := by
    have h1 := sec71Count_proved (apex K D) (apexVerts S) Fs S.ncard
      (apexVerts_finite hSfin) (apexVerts_ncard hSfin) hapex_supp hFs
    rwa [hFslen] at h1
  let EF : Set (Sym2 V) := {e ∈ K.edgeSet | Sym2.map some e ∈ (forestUnion Fs).edgeSet}
  let ED_finset : Finset (Sym2 V) := ((D.zip (D.rotate 1)).map (fun p => s(p.1, p.2))).toFinset
  let ED : Set (Sym2 V) := (ED_finset : Set (Sym2 V))
  have hEF_fin : EF.Finite := hKfin.subset (fun _ h => h.1)
  have hED_fin : ED.Finite := Finset.finite_toSet ED_finset
  have hEF_card : EF.ncard ≤ 4 * S.ncard := by
    have hsub : Sym2.map (some : V → Option V) '' EF ⊆ (forestUnion Fs).edgeSet := by
      rintro _ ⟨e, he, rfl⟩
      exact he.2
    calc
      EF.ncard = (Sym2.map (some : V → Option V) '' EF).ncard :=
        (Set.ncard_image_of_injective EF (Sym2.map.injective (Option.some_injective V))).symm
      _ ≤ (forestUnion Fs).edgeSet.ncard := Set.ncard_le_ncard hsub hFU_fin
      _ ≤ 4 * S.ncard := hFU_card
  have hED_card : ED.ncard ≤ S.ncard := by
    calc
      ED.ncard = ED_finset.card := Set.ncard_coe_finset ED_finset
      _ ≤ ((D.zip (D.rotate 1)).map (fun p => s(p.1, p.2))).length :=
        List.toFinset_card_le _
      _ ≤ D.length := by simp
      _ ≤ S.ncard := cycle_length_le_ncard hSfin hK hD
  have hsub_union : (sparsifyGraph K D Fs E₀).edgeSet ⊆ EF ∪ ED ∪ E₀ := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [mem_edgeSet] at he
      obtain ⟨habK, hcases⟩ := he
      rcases hcases with hF | ⟨p, hp, hp_ends⟩ | hE₀
      · exact Or.inl (Or.inl ⟨habK, hF⟩)
      · refine Or.inl (Or.inr ?_)
        simp only [ED, ED_finset, Finset.mem_coe, List.mem_toFinset, List.mem_map]
        refine ⟨p, hp, ?_⟩
        rcases hp_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      · exact Or.inr hE₀
  have h3 : 3 ≤ S.ncard := hD.1.trans (cycle_length_le_ncard hSfin hK hD)
  have hunion_fin : (EF ∪ ED ∪ E₀).Finite := (hEF_fin.union hED_fin).union hE₀fin
  have hle1 : (sparsifyGraph K D Fs E₀).edgeSet.ncard ≤ (EF ∪ ED ∪ E₀).ncard :=
    Set.ncard_le_ncard hsub_union hunion_fin
  have hle2 : (EF ∪ ED ∪ E₀).ncard ≤ (EF ∪ ED).ncard + E₀.ncard :=
    Set.ncard_union_le (EF ∪ ED) E₀
  have hle3 : (EF ∪ ED).ncard ≤ EF.ncard + ED.ncard :=
    Set.ncard_union_le EF ED
  omega

/-! ### Section 7.2: Cleanliness, nonplanarity and crossing preservation -/

omit [DecidableEq V] in
private lemma not_walk_to_outside_of_mem_U {K' : SimpleGraph V} {S U : Set V} {D : List V}
    {X : Finset (Option V)} (hK' : HP25.IsSupportedOn K' S)
    (hUD : U ⊆ S \ {v | v ∈ D})
    (hX : ∀ z ∈ S \ U, (∃ y ∈ U, K'.Adj y z) → some z ∈ X)
    {a b : Option V} (p : (apex K' D).Walk a b)
    (hp : ∀ w ∈ p.support, w ∈ apexVerts S \ (X : Set (Option V)))
    (ha : a ∈ some '' U) (hb : b ∉ some '' U) : False := by
  induction p with
  | nil => exact hb ha
  | @cons a w b haw p' ih =>
    obtain ⟨y, hyU, hy_eq⟩ := ha
    have ha_eq : a = some y := hy_eq.symm
    subst ha_eq
    by_cases hwU : w ∈ some '' U
    · exact ih (fun z hz => hp z (List.mem_cons_of_mem _ hz)) hwU hb
    · have hw_mem : w ∈ apexVerts S \ (X : Set (Option V)) :=
        hp w (List.mem_cons_of_mem _ (Walk.start_mem_support p'))
      cases w with
      | none =>
        exact (hUD hyU).2 haw
      | some z =>
        have hzU : z ∉ U := fun hz => hwU ⟨z, hz, rfl⟩
        have hzS : z ∈ S := hK' haw.symm
        exact hw_mem.2 (hX z ⟨hzS, hzU⟩ ⟨y, hyU, haw⟩)

/-- **The sparsification step** (Section 7.2): "Adding all edges from the apex to the cycle
gives a graph that contains the certificate and is contained in $J$. By Lemma 5, removing at most
three vertices other than $x$ leaves the same components in all three graphs, so the kept graph is
still clean. Its $3N-5$ kept edges of $K$ make it nonplanar by Euler's bound." Fact T then shows
that `D` is still crossed. -/
theorem sec72_proved : Sec72Statement := by
  intro V _ K S D Fs E₀ hSfin hK hD hclean hspar
  obtain ⟨hFs, hFslen, hE₀sub, _, hE₀card⟩ := hspar
  let K' := sparsifyGraph K D Fs E₀
  have hapex_supp : HP25.IsSupportedOn (apex K D) (apexVerts S) := isSupportedOn_apex hK hD
  have hFU_le_K' : forestUnion Fs ≤ apex K' D := forestUnion_le_apex_sparsifyGraph hFs
  -- 1. Cleanliness is preserved by Lemma 5.
  have hclean' : IsClean K' S D := by
    intro X hXsub hXcard
    obtain ⟨hne, hconn⟩ := hclean X hXsub hXcard
    refine ⟨hne, fun a ha b hb => ?_⟩
    have hcard_Fs : X.card < Fs.length := by omega
    have hreach_FU : ReachIn (forestUnion Fs) (apexVerts S \ X) a b :=
      (lemma5_proved (apex K D) (apexVerts S) Fs hapex_supp hFs X hcard_Fs a ha b hb).mp
        (hconn a ha b hb)
    exact reachIn_mono_graph hFU_le_K' hreach_FU
  -- 2. Nonplanarity holds by Euler's bound.
  have h3 : 3 ≤ S.ncard := hD.1.trans (cycle_length_le_ncard hSfin hK hD)
  have hnp : ¬ Nonempty (HP25.PlaneEmbedding K' S) := by
    intro hP
    have heuler : (edgesOn K' S).ncard ≤ 3 * S.ncard - 6 :=
      planar_edge_bound hP h3
    have hE₀_sub_edgesOn : E₀ ⊆ edgesOn K' S := by
      intro e he
      have heK : e ∈ K.edgeSet := hE₀sub he
      induction e using Sym2.ind with
      | _ u v =>
        rw [mem_edgeSet] at heK
        exact mem_edgesOn_iff.mpr
          ⟨hK heK, hK heK.symm, ⟨heK, Or.inr (Or.inr he)⟩⟩
    have hE₀_le : E₀.ncard ≤ (edgesOn K' S).ncard :=
      Set.ncard_le_ncard hE₀_sub_edgesOn (finite_edgesOn hSfin)
    omega
  -- 3. Fact T guarantees that `K'` is still crossed.
  have hcrossed : HP25.IsCrossed K' D := by
    by_contra hnc
    have hK'_supp : HP25.IsSupportedOn K' S := fun _ _ h => hK h.1
    have hD' : HP25.IsCycleList K' D :=
      ⟨hD.1, hD.2.1, fun p hp => ⟨hD.2.2 p hp, Or.inr (Or.inl ⟨p, hp, Or.inl rfl⟩)⟩⟩
    have hDS : ∀ v ∈ D, v ∈ S := mem_S_of_mem_cycle hK hD
    obtain ⟨U, hUD, ⟨u₀, hu₀U⟩, _, hNcard⟩ := fact_T_on hSfin hK'_supp hD' hDS hnc hnp
    let NU : Set V := {z ∈ S \ U | ∃ y ∈ U, K'.Adj y z}
    have hNU_fin : NU.Finite := hSfin.subset (fun _ hz => hz.1.1)
    let X : Finset (Option V) := hNU_fin.toFinset.image some
    have hXsub : (X : Set (Option V)) ⊆ apexVerts S \ {none} := by
      intro w hw
      simp only [X, Finset.coe_image, mem_image] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      have hzNU : z ∈ NU := hNU_fin.mem_toFinset.mp hz
      exact ⟨Or.inr ⟨z, hzNU.1.1, rfl⟩, by simp⟩
    have hXcard : X.card < 4 := by
      have h1 : X.card ≤ hNU_fin.toFinset.card := Finset.card_image_le
      have h2 : hNU_fin.toFinset.card = NU.ncard :=
        (Set.ncard_eq_toFinset_card NU hNU_fin).symm
      dsimp only [NU] at h2
      omega
    have hu₀_mem : some u₀ ∈ apexVerts S \ (X : Set (Option V)) := by
      refine ⟨Or.inr ⟨u₀, (hUD hu₀U).1, rfl⟩, ?_⟩
      simp only [X, Finset.coe_image, mem_image, Option.some.injEq, exists_eq_right]
      exact fun hu₀NU => (hNU_fin.mem_toFinset.mp hu₀NU).1.2 hu₀U
    have hnone_mem : (none : Option V) ∈ apexVerts S \ (X : Set (Option V)) :=
      ⟨Or.inl rfl, by simp [X]⟩
    obtain ⟨p, hp⟩ := (hclean' X hXsub hXcard).2 (some u₀) hu₀_mem none hnone_mem
    refine not_walk_to_outside_of_mem_U hK'_supp hUD (fun z hzS hex => ?_) p hp
      ⟨u₀, hu₀U, rfl⟩ (by simp)
    exact Finset.mem_image_of_mem some (hNU_fin.mem_toFinset.mpr ⟨hzS, hex⟩)
  exact ⟨hclean', hnp, hcrossed⟩

end GraphMinor.Crossing
