module

public import GraphMinor.Crossing.Statements
import GraphMinor.Crossing.CutSec2Fan
import GraphMinor.Crossing.CutSec3

/-!
# Section 4 of the crossing extractor: initial cleaning

This file proves the four statements of Section 4 of `docs/crossing/crossing_extractor.tex`:
* `sec4Discard_proved : Sec4DiscardStatement`
* `sec4Component_proved : Sec4ComponentStatement`
* `sec4Clean_proved : Sec4CleanStatement`
* `sec4EdgeCount_proved : Sec4EdgeCountStatement`
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set Finset

universe u

variable {V : Type u}

/-! ### Part 1: Discarding components not containing `D` (`Sec4DiscardStatement`) -/

private abbrev restrictHom (G : SimpleGraph V) (U : Set V) : HP25.restrict G U →g G where
  toFun := id
  map_rel' h := h.1

private theorem support_map_restrictHom {G : SimpleGraph V} {U : Set V} {a b : V}
    (p : (HP25.restrict G U).Walk a b) :
    (p.map (restrictHom G U)).support = p.support := by
  rw [Walk.support_map]
  exact List.map_id p.support

private theorem lift_walk_to_restrict {G : SimpleGraph V} {U : Set V} :
    ∀ {a b : V} (p : G.Walk a b),
      (∀ y ∈ p.support, y ∈ U) →
      ∃ q : (HP25.restrict G U).Walk a b, q.support = p.support
  | _, _, .nil, _ => ⟨.nil, rfl⟩
  | _, _, @Walk.cons _ _ u w _ hadj rest, hsupp => by
    have huU : u ∈ U := hsupp u (Walk.start_mem_support _)
    have hwU : w ∈ U := hsupp w (List.mem_cons_of_mem _ (Walk.start_mem_support _))
    have hadj' : (HP25.restrict G U).Adj u w := ⟨hadj, huU, hwU⟩
    obtain ⟨q_rest, hq_rest⟩ :=
      lift_walk_to_restrict rest (fun y hy => hsupp y (List.mem_cons_of_mem _ hy))
    refine ⟨.cons hadj' q_rest, ?_⟩
    simp [Walk.support_cons, hq_rest]

private theorem mem_reach_cycle_of_walk {K : SimpleGraph V} {D : List V} :
    ∀ {u v : V} (p : K.Walk u v),
      u ∈ {y | ∃ d ∈ D, ReachIn K Set.univ d y} →
      ∀ y ∈ p.support, y ∈ {y | ∃ d ∈ D, ReachIn K Set.univ d y}
  | _, _, .nil, hu => by
    intro y hy
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    exact hy ▸ hu
  | _, _, @Walk.cons _ _ _ w _ hadj rest, hu => by
    intro y hy
    rw [Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy_rest
    · exact hu
    · rcases hu with ⟨d, hdD, hrd⟩
      have hw : w ∈ {y | ∃ d ∈ D, ReachIn K Set.univ d y} :=
        ⟨d, hdD, hrd.trans (ReachIn.of_adj hadj trivial trivial)⟩
      exact mem_reach_cycle_of_walk rest hw y hy_rest

/-- **Discarding the other components** (Section 4): discarding vertices not reachable from `D`
does not change whether `D` is crossed. -/
theorem sec4Discard_proved : Sec4DiscardStatement := by
  intro V K _ D _ _
  let U : Set V := {y | ∃ d ∈ D, ReachIn K Set.univ d y}
  constructor
  · rintro ⟨a, b, c, d, Q, R, hidx, hQ, hR, hdisj⟩
    have haU : a ∈ U := ⟨a, hQ.2.1, ReachIn.refl trivial⟩
    have hcU : c ∈ U := ⟨c, hR.2.1, ReachIn.refl trivial⟩
    obtain ⟨Q', hQ'_supp⟩ := lift_walk_to_restrict Q (mem_reach_cycle_of_walk Q haU)
    obtain ⟨R', hR'_supp⟩ := lift_walk_to_restrict R (mem_reach_cycle_of_walk R hcU)
    have hQ'_path : Q'.IsPath := by
      rw [Walk.isPath_def, hQ'_supp]
      exact hQ.1.support_nodup
    have hR'_path : R'.IsPath := by
      rw [Walk.isPath_def, hR'_supp]
      exact hR.1.support_nodup
    have hQ'_tpath : HP25.IsTPath (HP25.restrict K U) D Q' := by
      refine ⟨hQ'_path, hQ.2.1, hQ.2.2.1, fun x hx => ?_⟩
      rw [hQ'_supp] at hx
      exact hQ.2.2.2 x hx
    have hR'_tpath : HP25.IsTPath (HP25.restrict K U) D R' := by
      refine ⟨hR'_path, hR.2.1, hR.2.2.1, fun x hx => ?_⟩
      rw [hR'_supp] at hx
      exact hR.2.2.2 x hx
    have hdisj' : Q'.support.Disjoint R'.support := by
      rwa [hQ'_supp, hR'_supp]
    exact ⟨a, b, c, d, Q', R', hidx, hQ'_tpath, hR'_tpath, hdisj'⟩
  · rintro ⟨a, b, c, d, Q, R, hidx, hQ, hR, hdisj⟩
    let Q' : K.Walk a b := Q.map (restrictHom K U)
    let R' : K.Walk c d := R.map (restrictHom K U)
    have hQ'_supp : Q'.support = Q.support := support_map_restrictHom Q
    have hR'_supp : R'.support = R.support := support_map_restrictHom R
    have hQ'_path : Q'.IsPath := by
      rw [Walk.isPath_def, hQ'_supp]
      exact hQ.1.support_nodup
    have hR'_path : R'.IsPath := by
      rw [Walk.isPath_def, hR'_supp]
      exact hR.1.support_nodup
    have hQ'_tpath : HP25.IsTPath K D Q' := by
      refine ⟨hQ'_path, hQ.2.1, hQ.2.2.1, fun x hx => ?_⟩
      rw [hQ'_supp] at hx
      exact hQ.2.2.2 x hx
    have hR'_tpath : HP25.IsTPath K D R' := by
      refine ⟨hR'_path, hR.2.1, hR.2.2.1, fun x hx => ?_⟩
      rw [hR'_supp] at hx
      exact hR.2.2.2 x hx
    have hdisj' : Q'.support.Disjoint R'.support := by
      rwa [hQ'_supp, hR'_supp]
    exact ⟨a, b, c, d, Q', R', hidx, hQ'_tpath, hR'_tpath, hdisj'⟩

/-! ### Part 2: A failed query gives a valid replacement (`Sec4ComponentStatement`) -/

open Classical in
/-- **A failed query gives a replacement** (Section 4): the reachable component `A` of `v` in
`K - X` has no cycle vertex, has boundary `N ⊆ X` of size `≤ 3`, and forms a valid replacement. -/
theorem sec4Component_proved : Sec4ComponentStatement := by
  intro V K S D v X hS_fin hK _ hvS _ hsep hX_card
  let X₀ : Set V := {y | some y ∈ X}
  let A : Set V := {y | ReachIn K (S \ X₀) v y}
  have hv_not_X : some v ∉ X := by
    intro hvX
    exact (hsep.1 hvX).2 (by simp)
  have hnone_not_X : none ∉ X := by
    intro hnX
    exact (hsep.1 hnX).2 (by simp)
  have hv_SX₀ : v ∈ S \ X₀ := ⟨hvS, hv_not_X⟩
  have hvA : v ∈ A := ReachIn.refl hv_SX₀
  have hA_sub_SX₀ : A ⊆ S \ X₀ := fun y hy => hy.mem_right
  have hA_sub_S : A ⊆ S := fun y hy => (hA_sub_SX₀ hy).1
  have hA_not_D : ∀ a ∈ A, a ∉ D := by
    intro a ha haD
    have hreach_va : ReachIn (apex K D) (apexVerts S \ X) (some v) (some a) :=
      reachIn_apex_of_reachIn (T := apexVerts S \ X)
        (fun y hy => ⟨Or.inr ⟨y, hy.1, rfl⟩, hy.2⟩) ha
    have ha_apex : some a ∈ apexVerts S \ X :=
      ⟨Or.inr ⟨a, (hA_sub_SX₀ ha).1, rfl⟩, (hA_sub_SX₀ ha).2⟩
    have hnone_apex : (none : Option V) ∈ apexVerts S \ X :=
      ⟨Or.inl rfl, hnone_not_X⟩
    have hadj_a_none : (apex K D).Adj (some a) none := haD
    exact hsep.2 (hreach_va.trans (ReachIn.of_adj hadj_a_none ha_apex hnone_apex))
  have hnbhd_props : ∀ y ∈ nbhd K A, y ∈ S \ A ∧ some y ∈ X := by
    intro y ⟨hy_not_A, a, haA, hadj⟩
    have hyS : y ∈ S := hK hadj.symm
    have hyX : some y ∈ X := by
      by_contra hy_not_X
      have hy_SX₀ : y ∈ S \ X₀ := ⟨hyS, hy_not_X⟩
      have ha_SX₀ : a ∈ S \ X₀ := hA_sub_SX₀ haA
      exact hy_not_A (haA.trans (ReachIn.of_adj hadj ha_SX₀ hy_SX₀))
    exact ⟨⟨hyS, hy_not_A⟩, hyX⟩
  have hnbhd_fin : (nbhd K A).Finite :=
    hS_fin.subset fun y hy => (hnbhd_props y hy).1.1
  let N : Finset V := hnbhd_fin.toFinset
  have hN_eq : (N : Set V) = nbhd K A := hnbhd_fin.coe_toFinset
  have hN_sub_SA : (N : Set V) ⊆ S \ A := by
    rw [hN_eq]
    exact fun y hy => (hnbhd_props y hy).1
  have hN_card : N.card ≤ 3 := by
    have himg_sub : N.image some ⊆ X := by
      intro z hz
      rw [Finset.mem_image] at hz
      rcases hz with ⟨y, hyN, rfl⟩
      rw [← Finset.mem_coe, hN_eq] at hyN
      exact (hnbhd_props y hyN).2
    have hcard_img : (N.image some).card = N.card :=
      Finset.card_image_of_injective N (Option.some_injective V)
    have hle := Finset.card_le_card himg_sub
    omega
  have hA_conn : IsConnectedOn K A := by
    refine isConnectedOn_of_reachIn hvA fun y hy => ?_
    rcases hy with ⟨p, hp⟩
    have hwalk : ∀ {a b : V} (q : K.Walk a b),
        (∀ z ∈ q.support, z ∈ S \ X₀) → a ∈ A → ∀ z ∈ q.support, z ∈ A := by
      intro a b q
      induction q with
      | nil =>
        intro _ ha z hz
        simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
        exact hz ▸ ha
      | @cons a w b hadj rest ih =>
        intro hsupp ha z hz
        rw [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz_rest
        · exact ha
        · have ha_SX₀ : a ∈ S \ X₀ := hsupp a (Walk.start_mem_support _)
          have hw_SX₀ : w ∈ S \ X₀ :=
            hsupp w (List.mem_cons_of_mem _ (Walk.start_mem_support _))
          have hwA : w ∈ A := ha.trans (ReachIn.of_adj hadj ha_SX₀ hw_SX₀)
          exact ih (fun u hu => hsupp u (List.mem_cons_of_mem _ hu)) hwA z hz_rest
    exact ReachIn.symm ⟨p, hwalk p hp hvA⟩
  have hA_comp : IsComponentIn K A A :=
    ⟨Subset.rfl, hA_conn, fun _ _ _ hb _ => hb⟩
  have hcomp_eq : ∀ C, IsComponentIn K A C → C = A := by
    intro C ⟨hC_sub, ⟨⟨c, hcC⟩, _⟩, hC_closed⟩
    refine Subset.antisymm hC_sub fun a haA => ?_
    obtain ⟨p, hp⟩ := hA_conn.2 c (hC_sub hcC) a haA
    have hwalk : ∀ {u w : V} (q : K.Walk u w),
        (∀ z ∈ q.support, z ∈ A) → u ∈ C → w ∈ C := by
      intro u w q
      induction q with
      | nil => intro _ hu; exact hu
      | @cons u x w hadj rest ih =>
        intro hsupp hu
        have hxA : x ∈ A := hsupp x (List.mem_cons_of_mem _ (Walk.start_mem_support _))
        have hxC : x ∈ C := hC_closed u hu x hxA hadj
        exact ih (fun z hz => hsupp z (List.mem_cons_of_mem _ hz)) hxC
    exact hwalk p hp hcC
  refine ⟨hvA, N, hN_eq, hA_sub_S, hA_not_D, hN_card, hN_sub_SA, ?_, hA_comp⟩
  intro C hC
  rw [hcomp_eq C hC, hN_eq]

/-! ### Part 3: Initial cleaning ends clean (`Sec4CleanStatement`) -/

/-- **Initial cleaning ends clean** (Section 4): when no off-cycle vertex in `S` can be separated
from `none` by at most `3` vertices, the instance `(K, D)` is clean. -/
theorem sec4Clean_proved : Sec4CleanStatement := by
  intro V K S D _ _ hunsep X hX_sub hX_card
  have hnone_not_X : none ∉ X := by
    intro hnone
    exact (hX_sub hnone).2 rfl
  have hnone_mem : (none : Option V) ∈ apexVerts S \ X := ⟨Or.inl rfl, hnone_not_X⟩
  refine isConnectedOn_of_reachIn hnone_mem fun z hz => ?_
  rcases hz.1 with rfl | ⟨v, hvS, rfl⟩
  · exact ReachIn.refl hnone_mem
  · by_cases hvD : v ∈ D
    · have hadj : (apex K D).Adj (some v) none := hvD
      exact ReachIn.of_adj hadj hz hnone_mem
    · have hX_sub_v : (X : Set (Option V)) ⊆ apexVerts S \ {some v, none} := by
        intro y hy
        refine ⟨(hX_sub hy).1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => hz.2 (h ▸ hy), (hX_sub hy).2⟩
      exact hunsep v hvS hvD X hX_sub_v (by omega)

/-! ### Part 4: Size and edge count of a replacement (`Sec4EdgeCountStatement`) -/

open Classical in
/-- **The size of a replacement** (Section 4): every valid replacement deletes at least one vertex
and adds at most three edges. -/
theorem sec4EdgeCount_proved : Sec4EdgeCountStatement := by
  intro V r D hval
  have hdel_ne : r.deleted.Nonempty := by
    rcases hval.2.2.2.2.2.2.1.1 with ⟨v₀, hv₀⟩
    exact ⟨v₀, hval.2.2.2.2.2.1 hv₀⟩
  rcases hdel_ne with ⟨v₀, hv₀⟩
  have hlen : r.boundary.toList.length ≤ 3 := by
    rw [Finset.length_toList]
    exact hval.2.2.1
  have hex : ∃ x y z : V, ∀ a ∈ r.boundary, a = x ∨ a = y ∨ a = z := by
    have hmem : ∀ a ∈ r.boundary, a ∈ r.boundary.toList :=
      fun a ha => Finset.mem_toList.mpr ha
    rcases hL : r.boundary.toList with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩⟩
    · exact ⟨v₀, v₀, v₀, fun a ha => by have := hmem a ha; simp [hL] at this⟩
    · exact ⟨x, v₀, v₀, fun a ha => by
        have := hmem a ha
        simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at this
        exact Or.inl this⟩
    · exact ⟨x, y, v₀, fun a ha => by
        have := hmem a ha
        simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)⟩
    · exact ⟨x, y, z, fun a ha => by
        have := hmem a ha
        simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at this
        exact this⟩
    · rw [hL] at hlen; simp at hlen; omega
  rcases hex with ⟨x, y, z, hxyz⟩
  let E₃ : Finset (Sym2 V) := {s(x, y), s(y, z), s(x, z)}
  have hE₃_card : E₃.card ≤ 3 := by
    dsimp only [E₃]
    have h1 : ({s(x, y), s(y, z), s(x, z)} : Finset (Sym2 V)).card ≤
        ({s(y, z), s(x, z)} : Finset (Sym2 V)).card + 1 := Finset.card_insert_le _ _
    have h2 : ({s(y, z), s(x, z)} : Finset (Sym2 V)).card ≤
        ({s(x, z)} : Finset (Sym2 V)).card + 1 := Finset.card_insert_le _ _
    have h3 : ({s(x, z)} : Finset (Sym2 V)).card = 1 := Finset.card_singleton _
    omega
  have hsub_E₃ : r.newGraph.edgeSet \ r.graph.edgeSet ⊆ (E₃ : Set (Sym2 V)) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Set.mem_sdiff, mem_edgeSet] at he
      rcases he.1 with ⟨hadj_old, -, -⟩ | ⟨ha_bd, hb_bd, hab⟩
      · exact False.elim (he.2 hadj_old)
      · simp only [E₃, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        rcases hxyz a ha_bd with rfl | rfl | rfl <;>
          rcases hxyz b hb_bd with rfl | rfl | rfl
        · exact False.elim (hab rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl Sym2.eq_swap
        · exact False.elim (hab rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr Sym2.eq_swap)
        · exact Or.inr (Or.inl Sym2.eq_swap)
        · exact False.elim (hab rfl)
  have hfin : (r.newGraph.edgeSet \ r.graph.edgeSet).Finite :=
    E₃.finite_toSet.subset hsub_E₃
  have hncard : (r.newGraph.edgeSet \ r.graph.edgeSet).ncard ≤ 3 := by
    have hle := Set.ncard_le_ncard hsub_E₃ E₃.finite_toSet
    rw [Set.ncard_coe_finset] at hle
    omega
  exact ⟨⟨v₀, hv₀⟩, hncard, hfin⟩

end GraphMinor.Crossing
