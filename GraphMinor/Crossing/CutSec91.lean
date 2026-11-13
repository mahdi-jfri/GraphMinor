module

public import GraphMinor.Crossing.Statements
import GraphMinor.Crossing.CutSec2Fan
import GraphMinor.Crossing.CutSec3
import GraphMinor.Crossing.CutSec8

/-!
# Sections 9.1–9.3 of the crossing extractor: trial contractions and restoration replacements

This file proves the first three statements of Section 9 of `docs/crossing/crossing_extractor.tex`:
* `sec91_proved : Sec91Statement`
* `sec92Value_proved : Sec92ValueStatement`
* `sec93_proved : Sec93Statement`
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set Finset

universe u

variable {V : Type u} [DecidableEq V]

/-! ### Part 1: What the contraction guarantees (`Sec91Statement`) -/

omit [DecidableEq V] in
/-- If `IsCycleEdge D u v`, then both `u` and `v` belong to `D`. -/
theorem mem_of_isCycleEdge {D : List V} {u v : V} (he : IsCycleEdge D u v) :
    u ∈ D ∧ v ∈ D := by
  rcases he with ⟨p, hp, h_eq | h_eq⟩
  · subst h_eq
    exact ⟨(List.of_mem_zip hp).1, List.mem_rotate.mp (List.of_mem_zip hp).2⟩
  · subst h_eq
    exact ⟨List.mem_rotate.mp (List.of_mem_zip hp).2, (List.of_mem_zip hp).1⟩

omit [DecidableEq V] in
/-- Under `IsTrialEdge K D u v`, if `u ∈ D` then `v ∈ D`. -/
theorem mem_cycle_right_of_isTrialEdge {K : SimpleGraph V} {D : List V} {u v : V}
    (htrial : IsTrialEdge K D u v) (huD : u ∈ D) : v ∈ D := by
  rcases htrial.2 with hu_not_D | hce
  · exact False.elim (hu_not_D huD)
  · exact (mem_of_isCycleEdge hce).2

/-- For `y ≠ u`, `y ∈ contractCycle D u ↔ y ∈ D`. -/
theorem mem_contractCycle_iff_of_ne {D : List V} {u y : V} (hyu : y ≠ u) :
    y ∈ contractCycle D u ↔ y ∈ D := by
  unfold contractCycle
  split_ifs with huD
  · exact List.mem_erase_of_ne hyu
  · rfl

/-- The contraction map on `Option V` sending `some u` to `some v` and fixing all other vertices. -/
private def contractMap (u v : V) (x : Option V) : Option V :=
  if x = some u then some v else x

@[simp]
private theorem contractMap_none (u v : V) : contractMap u v none = none := by
  simp [contractMap]

@[simp]
private theorem contractMap_some_self (u v : V) : contractMap u v (some u) = some v := by
  simp [contractMap]

private theorem contractMap_some_of_ne {u v y : V} (hyu : y ≠ u) :
    contractMap u v (some y) = some y := by
  simp [contractMap, hyu]

private theorem contractMap_eq_of_ne_some {u v : V} {x : Option V} (hx : x ≠ some u) :
    contractMap u v x = x := by
  simp [contractMap, hx]

private theorem contractMap_ne_some_u {u v : V} (huv : u ≠ v) (x : Option V) :
    contractMap u v x ≠ some u := by
  unfold contractMap
  split_ifs with hx
  · exact fun h => huv (Option.some_injective V h).symm
  · exact hx

private theorem contractMap_mem_apexVerts {S : Set V} {u v : V} (hvS : v ∈ S) (huv : u ≠ v)
    {x : Option V} (hx : x ∈ apexVerts S) :
    contractMap u v x ∈ apexVerts (S \ {u}) := by
  rcases hx with rfl | ⟨y, hyS, rfl⟩
  · exact Or.inl rfl
  · by_cases hyu : y = u
    · subst y
      rw [contractMap_some_self]
      exact Or.inr ⟨v, ⟨hvS, Ne.symm huv⟩, rfl⟩
    · rw [contractMap_some_of_ne hyu]
      exact Or.inr ⟨y, ⟨hyS, hyu⟩, rfl⟩

/-- Any edge of `apex K D` either has both ends mapped to the same vertex by `contractMap u v` or
maps to an edge of `apex (contractGraph K u v) (contractCycle D u)`. -/
private theorem contractMap_adj_or_eq {K : SimpleGraph V} {D : List V} {u v : V}
    (htrial : IsTrialEdge K D u v) {x y : Option V} (hadj : (apex K D).Adj x y) :
    contractMap u v x = contractMap u v y ∨
      (apex (contractGraph K u v) (contractCycle D u)).Adj
        (contractMap u v x) (contractMap u v y) := by
  have huv : u ≠ v := K.ne_of_adj htrial.1
  by_cases h_eq : contractMap u v x = contractMap u v y
  · exact Or.inl h_eq
  · refine Or.inr ?_
    cases x with
    | none =>
      cases y with
      | none => exact False.elim hadj
      | some b =>
        have hbD : b ∈ D := hadj
        by_cases hbu : b = u
        · subst b
          rw [contractMap_none, contractMap_some_self]
          have hvD : v ∈ D := mem_cycle_right_of_isTrialEdge htrial hbD
          exact (mem_contractCycle_iff_of_ne huv.symm).mpr hvD
        · rw [contractMap_none, contractMap_some_of_ne hbu]
          exact (mem_contractCycle_iff_of_ne hbu).mpr hbD
    | some a =>
      cases y with
      | none =>
        have haD : a ∈ D := hadj
        by_cases hau : a = u
        · subst a
          rw [contractMap_some_self, contractMap_none]
          have hvD : v ∈ D := mem_cycle_right_of_isTrialEdge htrial haD
          exact (mem_contractCycle_iff_of_ne huv.symm).mpr hvD
        · rw [contractMap_some_of_ne hau, contractMap_none]
          exact (mem_contractCycle_iff_of_ne hau).mpr haD
      | some b =>
        have hab_K : K.Adj a b := hadj
        by_cases hau : a = u
        · subst a
          have hbu : b ≠ u := (K.ne_of_adj hab_K).symm
          rw [contractMap_some_self, contractMap_some_of_ne hbu] at h_eq ⊢
          have hvb : v ≠ b := fun h => h_eq (congrArg some h)
          exact ⟨hvb, huv.symm, hbu, Or.inr (Or.inl ⟨rfl, hab_K⟩)⟩
        · by_cases hbu : b = u
          · subst b
            rw [contractMap_some_of_ne hau, contractMap_some_self] at h_eq ⊢
            have hav : a ≠ v := fun h => h_eq (congrArg some h)
            exact ⟨hav, hau, huv.symm, Or.inr (Or.inr ⟨rfl, hab_K.symm⟩)⟩
          · rw [contractMap_some_of_ne hau, contractMap_some_of_ne hbu] at h_eq ⊢
            exact ⟨K.ne_of_adj hab_K, hau, hbu, Or.inl hab_K⟩

/-- Every walk of `apex K D` inside `R₀` maps under `contractMap u v` to a walk of
`apex (contractGraph K u v) (contractCycle D u)` inside `contractMap u v '' R₀`. -/
private theorem reachIn_contractMap_of_walk {K : SimpleGraph V} {D : List V} {u v : V}
    (htrial : IsTrialEdge K D u v) {R₀ : Set (Option V)} :
    ∀ {x y : Option V} (q : (apex K D).Walk x y),
      (∀ z ∈ q.support, z ∈ R₀) →
      ReachIn (apex (contractGraph K u v) (contractCycle D u)) (contractMap u v '' R₀)
        (contractMap u v x) (contractMap u v y)
  | x, _, .nil, hsupp =>
    ReachIn.refl ⟨x, hsupp x (Walk.start_mem_support _), rfl⟩
  | x, y, @Walk.cons _ _ _ w _ hadj rest, hsupp => by
    have hxR : contractMap u v x ∈ contractMap u v '' R₀ :=
      ⟨x, hsupp x (Walk.start_mem_support _), rfl⟩
    have hwR : contractMap u v w ∈ contractMap u v '' R₀ :=
      ⟨w, hsupp w (List.mem_cons_of_mem _ (Walk.start_mem_support _)), rfl⟩
    have hrest := reachIn_contractMap_of_walk htrial rest
      (fun z hz => hsupp z (List.mem_cons_of_mem _ hz))
    rcases contractMap_adj_or_eq htrial hadj with h_eq | hadj'
    · rw [h_eq]
      exact hrest
    · exact (ReachIn.of_adj hadj' hxR hwR).trans hrest

/-- Lifting a separator `X` of the contracted apex graph to `X₀ = if some v ∈ X then insert (some u) X else X`
in the old apex graph preserves connectivity of the complement. -/
theorem isConnectedOn_contract_of_isConnectedOn_old {K : SimpleGraph V} {S : Set V} {D : List V}
    {u v : V} (hK : HP25.IsSupportedOn K S) (htrial : IsTrialEdge K D u v)
    {X : Finset (Option V)} (hX_sub : (X : Set (Option V)) ⊆ apexVerts (S \ {u}) \ {none})
    (hconn : IsConnectedOn (apex K D)
      (apexVerts S \ (if some v ∈ X then insert (some u) X else X : Finset (Option V)))) :
    IsConnectedOn (apex (contractGraph K u v) (contractCycle D u)) (apexVerts (S \ {u}) \ X) := by
  let X₀ : Finset (Option V) := if some v ∈ X then insert (some u) X else X
  have hvS : v ∈ S := hK htrial.1.symm
  have huv : u ≠ v := K.ne_of_adj htrial.1
  have hnone_mem : (none : Option V) ∈ apexVerts (S \ {u}) \ X :=
    ⟨Or.inl rfl, fun hnone => (hX_sub hnone).2 rfl⟩
  have hX_sub_X₀ : X ⊆ X₀ := by
    dsimp only [X₀]
    split_ifs <;> [exact Finset.subset_insert _ _; exact Finset.Subset.rfl]
  have himg_sub : contractMap u v '' (apexVerts S \ X₀) ⊆ apexVerts (S \ {u}) \ X := by
    rintro _ ⟨z, ⟨hz_S, hz_not_X₀⟩, rfl⟩
    refine ⟨contractMap_mem_apexVerts hvS huv hz_S, ?_⟩
    by_cases hzu : z = some u
    · subst z
      rw [contractMap_some_self]
      intro hvX
      apply hz_not_X₀
      dsimp only [X₀]
      split_ifs with hvX'
      · exact Finset.mem_insert_self _ _
      · exact False.elim (hvX' hvX)
    · rw [contractMap_eq_of_ne_some hzu]
      exact fun hzX => hz_not_X₀ (hX_sub_X₀ hzX)
  have hinc : ∀ a ∈ apexVerts (S \ {u}) \ X, a ∈ apexVerts S \ X₀ ∧ contractMap u v a = a := by
    intro a ⟨ha_Su, ha_not_X⟩
    have ha_ne_u : a ≠ some u := by
      rcases ha_Su with rfl | ⟨y, ⟨_, hyu⟩, rfl⟩
      · simp
      · exact fun h => hyu (Option.some_injective V h)
    have ha_S : a ∈ apexVerts S := by
      rcases ha_Su with rfl | ⟨y, ⟨hyS, _⟩, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨y, hyS, rfl⟩
    have ha_not_X₀ : a ∉ X₀ := by
      dsimp only [X₀]
      split_ifs with hvX
      · rw [Finset.mem_insert, not_or]
        exact ⟨ha_ne_u, ha_not_X⟩
      · exact ha_not_X
    exact ⟨⟨ha_S, ha_not_X₀⟩, contractMap_eq_of_ne_some ha_ne_u⟩
  refine ⟨⟨none, hnone_mem⟩, fun a ha b hb => ?_⟩
  obtain ⟨ha₀, ha_eq⟩ := hinc a ha
  obtain ⟨hb₀, hb_eq⟩ := hinc b hb
  obtain ⟨q, hq⟩ := hconn.2 a ha₀ b hb₀
  have hreach := reachIn_contractMap_of_walk htrial q hq
  rw [ha_eq, hb_eq] at hreach
  exact hreach.mono himg_sub

open Classical in
/-- **What the contraction guarantees** (Section 9.1): contracting a trial edge of a clean instance
gives `𝓡_3(J, x)`, forces every disconnecting cut of size `≤ 3` to contain `w`, gives `𝓡_2(B, x)`,
and ensures every bad component of `J - {w, p, q}` contains a marker. -/
theorem sec91_proved : Sec91Statement := by
  intro V _ K S D u v _ hK _ hclean htrial
  let J := apex (contractGraph K u v) (contractCycle D u)
  let T := apexVerts (S \ {u})
  have huS : u ∈ S := hK htrial.1
  have hvS : v ∈ S := hK htrial.1.symm
  have huv : u ≠ v := K.ne_of_adj htrial.1
  have hT_sub_T₀ : T ⊆ apexVerts S := by
    rintro x (rfl | ⟨y, ⟨hyS, _⟩, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨y, hyS, rfl⟩
  have hR3 : RootedConn J T none 3 := by
    intro X hX_sub hX_lt
    let X₀ : Finset (Option V) := if some v ∈ X then insert (some u) X else X
    have hX₀_sub : (X₀ : Set (Option V)) ⊆ apexVerts S \ {none} := by
      intro z hz
      dsimp only [X₀] at hz
      split_ifs at hz with hvX
      · rw [Finset.mem_coe, Finset.mem_insert] at hz
        rcases hz with rfl | hzX
        · exact ⟨Or.inr ⟨u, huS, rfl⟩, by simp⟩
        · exact ⟨hT_sub_T₀ (hX_sub hzX).1, (hX_sub hzX).2⟩
      · exact ⟨hT_sub_T₀ (hX_sub hz).1, (hX_sub hz).2⟩
    have hX₀_lt : X₀.card < 4 := by
      dsimp only [X₀]
      split_ifs
      · have hle := Finset.card_insert_le (some u) X
        omega
      · omega
    exact isConnectedOn_contract_of_isConnectedOn_old hK htrial hX_sub (hclean X₀ hX₀_sub hX₀_lt)
  have hmust_v : ∀ X : Finset (Option V), (X : Set (Option V)) ⊆ T \ {none} → X.card ≤ 3 →
      ¬ IsConnectedOn J (T \ X) → some v ∈ X := by
    intro X hX_sub hX_le hnot_conn
    by_contra hv_not_X
    have hX_sub_T₀ : (X : Set (Option V)) ⊆ apexVerts S \ {none} :=
      fun z hz => ⟨hT_sub_T₀ (hX_sub hz).1, (hX_sub hz).2⟩
    have hX_lt : X.card < 4 := by omega
    have hconn₀ := hclean X hX_sub_T₀ hX_lt
    have hconn : IsConnectedOn J (T \ X) := by
      apply isConnectedOn_contract_of_isConnectedOn_old hK htrial hX_sub
      simpa [hv_not_X] using hconn₀
    exact hnot_conn hconn
  have hR2 : RootedConn J (T \ {some v}) none 2 := by
    intro X hX_sub hX_lt
    let X' : Finset (Option V) := insert (some v) X
    have hX'_sub : (X' : Set (Option V)) ⊆ T \ {none} := by
      intro z hz
      rw [Finset.mem_coe, Finset.mem_insert] at hz
      rcases hz with rfl | hzX
      · exact ⟨Or.inr ⟨v, ⟨hvS, huv.symm⟩, rfl⟩, by simp⟩
      · exact ⟨(hX_sub hzX).1.1, (hX_sub hzX).2⟩
    have hX'_lt : X'.card < 3 := by
      dsimp only [X']
      have hle := Finset.card_insert_le (some v) X
      omega
    have hconn := hR3 X' hX'_sub hX'_lt
    have hset_eq : (T \ {some v}) \ (X : Set (Option V)) = T \ (X' : Set (Option V)) := by
      ext z
      simp only [X', Finset.coe_insert, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_insert_iff,
        Finset.mem_coe, not_or]
      tauto
    rwa [hset_eq]
  have hmarker : ∀ (p q : Option V) (Q : Set (Option V)), p ≠ none → q ≠ none →
      IsComponentIn J (T \ {some v, p, q}) Q → none ∉ Q →
      ∃ y ∈ markers K u v, some y ∈ Q := by
    intro p q Q hp_ne hq_ne hQ hnone_not_Q
    by_contra hno_marker
    push Not at hno_marker
    let X₃ : Finset (Option V) := ({some v, p, q} : Finset (Option V)).filter (· ∈ apexVerts S)
    have hX₃_sub : (X₃ : Set (Option V)) ⊆ apexVerts S \ {none} := by
      intro z hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz
      refine ⟨hz.2, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz.1 with rfl | rfl | rfl
      · simp
      · exact hp_ne
      · exact hq_ne
    have hX₃_lt : X₃.card < 4 := by
      have hle0 : X₃.card ≤ ({some v, p, q} : Finset (Option V)).card :=
        Finset.card_filter_le _ _
      have hle1 := Finset.card_insert_le (some v) ({p, q} : Finset (Option V))
      have hle2 := Finset.card_insert_le p ({q} : Finset (Option V))
      have hle3 : ({q} : Finset (Option V)).card = 1 := Finset.card_singleton q
      omega
    have hconn₀ := hclean X₃ hX₃_sub hX₃_lt
    rcases hQ.2.1.1 with ⟨q₀, hq₀Q⟩
    have hQ_sub_T₀ : Q ⊆ apexVerts S \ (X₃ : Set (Option V)) := by
      intro z hzQ
      have hz_T := hQ.1 hzQ
      have hz_S : z ∈ apexVerts S := hT_sub_T₀ hz_T.1
      refine ⟨hz_S, fun hzX₃ => ?_⟩
      rw [Finset.mem_coe, Finset.mem_filter] at hzX₃
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzX₃
      exact hz_T.2 hzX₃.1
    have hnone_mem₀ : (none : Option V) ∈ apexVerts S \ (X₃ : Set (Option V)) :=
      ⟨Or.inl rfl, fun hnone => (hX₃_sub hnone).2 rfl⟩
    obtain ⟨W₀, hW₀⟩ := hconn₀.2 q₀ (hQ_sub_T₀ hq₀Q) none hnone_mem₀
    have hclosed : ∀ a ∈ Q, ∀ b ∈ apexVerts S \ (X₃ : Set (Option V)),
        (apex K D).Adj a b → b ∈ Q := by
      intro a haQ b ⟨hb_S, hb_not_X₃⟩ hadj
      have ha_T := hQ.1 haQ
      have ha_ne_none : a ≠ none := fun h => hnone_not_Q (h ▸ haQ)
      rcases ha_T.1 with rfl | ⟨y, ⟨hyS, hyu⟩, rfl⟩
      · exact False.elim (ha_ne_none rfl)
      · have hyv : y ≠ v := fun h => ha_T.2 (Or.inl (congrArg some h))
        have hb_not_vpq : b ∉ ({some v, p, q} : Set (Option V)) := by
          intro hb_in
          apply hb_not_X₃
          rw [Finset.mem_coe, Finset.mem_filter]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact ⟨hb_in, hb_S⟩
        rcases hb_S with rfl | ⟨z, hzS, rfl⟩
        · have hyD : y ∈ D := hadj
          have hyD' : y ∈ contractCycle D u := (mem_contractCycle_iff_of_ne hyu).mpr hyD
          have hadj_J : J.Adj (some y) none := hyD'
          exact hQ.2.2 (some y) haQ none ⟨Or.inl rfl, hb_not_vpq⟩ hadj_J
        · have hyz_K : K.Adj y z := hadj
          by_cases hzu : z = u
          · subst z
            have hy_marker : y ∈ markers K u v := ⟨hyz_K.symm, hyv⟩
            exact False.elim (hno_marker y hy_marker haQ)
          · have hadj_J : J.Adj (some y) (some z) :=
              ⟨K.ne_of_adj hyz_K, hyu, hzu, Or.inl hyz_K⟩
            exact hQ.2.2 (some y) haQ (some z) ⟨Or.inr ⟨z, ⟨hzS, hzu⟩, rfl⟩, hb_not_vpq⟩ hadj_J
    have hnone_in_Q : none ∈ Q := mem_of_walk_closed hclosed W₀ hW₀ hq₀Q
    exact hnone_not_Q hnone_in_Q
  exact ⟨hR3, hmust_v, hR2, hmarker⟩

/-! ### Part 2: The value of a failed restoration flow (`Sec92ValueStatement`) -/

/-- **The value of a failed restoration flow** (Section 9.2): under `𝓡_2(B, x)`, if `z` can be
separated from `x` by at most `2` vertices, then there is a minimum `z`-`x` separator of size `2`. -/
theorem sec92Value_proved : Sec92ValueStatement := by
  intro W B T x z _ hxT hzT _ _ hR2 hunsep
  unfold IsUnseparable at hunsep
  push Not at hunsep
  rcases hunsep with ⟨X, hX_sub, hX_le, hX_nreach⟩
  exact ⟨X, isMinSeparator_of_le_of_rootedConn hR2 hxT hzT ⟨hX_sub, hX_nreach⟩ hX_le⟩

/-! ### Part 3: Each restoration replacement is valid (`Sec93Statement`) -/

/-- If `IsMaxSourceSeparator J T z x {a, b}`, then `z ∈ T` (since otherwise `∅` would be a smaller
separator). -/
theorem mem_of_isMaxSourceSeparator_pair {W : Type u} [DecidableEq W] {J : SimpleGraph W}
    {T : Set W} {z x a b : W} (hmax : IsMaxSourceSeparator J T z x {a, b}) : z ∈ T := by
  by_contra hz_not_T
  have hsep_empty : IsSeparator J T z x ∅ := by
    refine ⟨by simp, fun ⟨q, hq⟩ => ?_⟩
    have hz_mem := hq z (Walk.start_mem_support _)
    exact hz_not_T hz_mem.1
  have hle := hmax.1.2 ∅ hsep_empty
  have hmem : a ∈ ({a, b} : Finset W) := Finset.mem_insert_self a {b}
  have hpos : 0 < ({a, b} : Finset W).card := Finset.card_pos.mpr ⟨a, hmem⟩
  simp at hle

/-- Core validity of `restoreRecord H S D w z p q` without unused hypotheses. -/
theorem restoreRecord_isValid {H : SimpleGraph V} {S : Set V} {D : List V} {w z p q : V}
    (hH : HP25.IsSupportedOn H S) (hwS : w ∈ S)
    (hR3 : RootedConn (apex H D) (apexVerts S) none 3)
    (hR2 : RootedConn (apex H D) (restoreVerts S w) none 2)
    (hmax : IsMaxSourceSeparator (apex H D) (restoreVerts S w) (some z) none {some p, some q}) :
    (restoreRecord H S D w z p q).IsValid D ∧ z ∈ (restoreRecord H S D w z p q).rep := by
  let B_verts := restoreVerts S w
  let X_pq : Finset (Option V) := {some p, some q}
  let U_opt := sourceSide (apex H D) B_verts none X_pq
  let U : Set V := {y | some y ∈ U_opt}
  have hz_B : some z ∈ B_verts := mem_of_isMaxSourceSeparator_pair hmax
  have hzU : z ∈ U := mem_sourceSide_of_isSeparator hz_B hmax.1.1
  have hU_sub_S : U ⊆ S := by
    intro y hyU
    simpa [apexVerts] using hyU.1.1
  have hU_ne_w : ∀ y ∈ U, y ≠ w := by
    intro y hyU hyw
    exact hyU.1.2 (congrArg some hyw)
  have hU_not_D : ∀ a ∈ U, a ∉ D := by
    intro a haU haD
    have ha_BX : some a ∈ B_verts \ (X_pq : Set (Option V)) := ⟨haU.1, haU.2.1⟩
    have hnone_BX : (none : Option V) ∈ B_verts \ (X_pq : Set (Option V)) := by
      refine ⟨⟨Or.inl rfl, by simp⟩, ?_⟩
      simp [X_pq]
    have hadj : (apex H D).Adj (some a) none := haD
    exact haU.2.2 (ReachIn.of_adj hadj ha_BX hnone_BX)
  have hbd_card : ({w, p, q} : Finset V).card ≤ 3 := by
    have h1 := Finset.card_insert_le w ({p, q} : Finset V)
    have h2 := Finset.card_insert_le p ({q} : Finset V)
    have h3 : ({q} : Finset V).card = 1 := Finset.card_singleton q
    omega
  have hp_B : some p ∈ B_verts \ {some z, none} :=
    hmax.1.1.1 (Finset.mem_insert_self (some p) {some q})
  have hq_B : some q ∈ B_verts \ {some z, none} :=
    hmax.1.1.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self (some q)))
  have hpS : p ∈ S := by
    simpa [apexVerts] using hp_B.1.1
  have hqS : q ∈ S := by
    simpa [apexVerts] using hq_B.1.1
  have hbd_sub : (({w, p, q} : Finset V) : Set V) ⊆ S \ U := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> subst y
    · exact ⟨hwS, fun hwU => hU_ne_w w hwU rfl⟩
    · refine ⟨hpS, fun hpU => hpU.2.1 ?_⟩
      exact Finset.mem_insert_self (some p) {some q}
    · refine ⟨hqS, fun hqU => hqU.2.1 ?_⟩
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (some q))
  have hcomp_bd : ∀ C, IsComponentIn H U C → nbhd H C = ({w, p, q} : Finset V) := by
    intro C hC
    have hnbhd_sub : nbhd H C ⊆ ({w, p, q} : Set V) := by
      intro y ⟨hy_not_C, a, haC, hadj⟩
      have hyS : y ∈ S := hH hadj.symm
      by_cases hyw : y = w
      · exact Or.inl hyw
      · have hy_B : some y ∈ B_verts :=
          ⟨Or.inr ⟨y, hyS, rfl⟩, fun h => hyw (Option.some_injective V h)⟩
        have haU : a ∈ U := hC.1 haC
        have hadj_apex : (apex H D).Adj (some a) (some y) := hadj
        rcases mem_sourceSide_or_mem_of_adj haU hy_B hadj_apex with hyU | hy_pq
        · exact False.elim (hy_not_C (hC.2.2 a haC y hyU hadj))
        · simp only [X_pq, Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at hy_pq
          exact Or.inr hy_pq
    have hnbhd_sub' : nbhd H C ⊆ (({w, p, q} : Finset V) : Set V) := by
      simpa only [Finset.coe_insert, Finset.coe_singleton] using hnbhd_sub
    refine Set.Subset.antisymm hnbhd_sub' ?_
    intro y hy
    have hy_not_C : y ∉ C := fun hyC => (hbd_sub hy).2 (hC.1 hyC)
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    refine ⟨hy_not_C, ?_⟩
    rcases hC.2.1.1 with ⟨c₀, hc₀C⟩
    have hc₀U : c₀ ∈ U := hC.1 hc₀C
    by_contra hno_adj
    push Not at hno_adj
    rcases hy with hy | hy | hy <;> subst y
    · -- Case y = w: {p, q} would separate C from none in J, violating R_3(J, none)
      have hX_sub : (X_pq : Set (Option V)) ⊆ apexVerts S \ {none} := by
        intro x hx
        simp only [X_pq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨Or.inr ⟨p, hpS, rfl⟩, by simp⟩
        · exact ⟨Or.inr ⟨q, hqS, rfl⟩, by simp⟩
      have hX_lt : X_pq.card < 3 := by
        dsimp only [X_pq]
        have hle := Finset.card_insert_le (some p) ({some q} : Finset (Option V))
        have h1 : ({some q} : Finset (Option V)).card = 1 := Finset.card_singleton _
        omega
      have hconn := hR3 X_pq hX_sub hX_lt
      have hc₀_mem : some c₀ ∈ apexVerts S \ (X_pq : Set (Option V)) :=
        ⟨Or.inr ⟨c₀, hU_sub_S hc₀U, rfl⟩, hc₀U.2.1⟩
      have hnone_mem : (none : Option V) ∈ apexVerts S \ (X_pq : Set (Option V)) := by
        refine ⟨Or.inl rfl, ?_⟩
        simp [X_pq]
      obtain ⟨W₀, hW₀⟩ := hconn.2 (some c₀) hc₀_mem none hnone_mem
      have hclosed : ∀ a ∈ some '' C, ∀ b ∈ apexVerts S \ (X_pq : Set (Option V)),
          (apex H D).Adj a b → b ∈ some '' C := by
        rintro _ ⟨a, haC, rfl⟩ b ⟨hb_S, hb_not_pq⟩ hadj
        have haU : a ∈ U := hC.1 haC
        rcases hb_S with rfl | ⟨v', hv'S, rfl⟩
        · exact False.elim (hU_not_D a haU hadj)
        · by_cases hv'C : v' ∈ C
          · exact ⟨v', hv'C, rfl⟩
          · have hv'_bd : v' ∈ ({w, p, q} : Set V) := hnbhd_sub ⟨hv'C, a, haC, hadj⟩
            rcases hv'_bd with hv' | hv' | hv' <;> subst v'
            · exact False.elim (hno_adj a haC hadj)
            · exact False.elim (hb_not_pq (Finset.mem_insert_self (some p) {some q}))
            · exact False.elim (hb_not_pq
                (Finset.mem_insert_of_mem (Finset.mem_singleton_self (some q))))
      have hnone_in : (none : Option V) ∈ some '' C :=
        mem_of_walk_closed hclosed W₀ hW₀ ⟨c₀, hc₀C, rfl⟩
      rcases hnone_in with ⟨_, _, h_eq⟩
      simp at h_eq
    · -- Case y = p: {q} would separate C from none in B, violating R_2(B, none)
      let X_q : Finset (Option V) := {some q}
      have hX_sub : (X_q : Set (Option V)) ⊆ B_verts \ {none} := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_singleton] at hx
        subst x
        exact ⟨hq_B.1, by simp⟩
      have hX_lt : X_q.card < 2 := by simp [X_q]
      have hconn := hR2 X_q hX_sub hX_lt
      have hc₀_mem : some c₀ ∈ B_verts \ (X_q : Set (Option V)) := by
        refine ⟨hc₀U.1, fun h => hc₀U.2.1 ?_⟩
        rw [Finset.mem_coe, Finset.mem_singleton] at h
        rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (some q))
      have hnone_mem : (none : Option V) ∈ B_verts \ (X_q : Set (Option V)) := by
        refine ⟨⟨Or.inl rfl, by simp⟩, ?_⟩
        simp [X_q]
      obtain ⟨W₀, hW₀⟩ := hconn.2 (some c₀) hc₀_mem none hnone_mem
      have hclosed : ∀ a ∈ some '' C, ∀ b ∈ B_verts \ (X_q : Set (Option V)),
          (apex H D).Adj a b → b ∈ some '' C := by
        rintro _ ⟨a, haC, rfl⟩ b ⟨⟨hb_S, hb_ne_w⟩, hb_not_q⟩ hadj
        have haU : a ∈ U := hC.1 haC
        rcases hb_S with rfl | ⟨v', _, rfl⟩
        · exact False.elim (hU_not_D a haU hadj)
        · by_cases hv'C : v' ∈ C
          · exact ⟨v', hv'C, rfl⟩
          · have hv'_bd : v' ∈ ({w, p, q} : Set V) := hnbhd_sub ⟨hv'C, a, haC, hadj⟩
            rcases hv'_bd with hv' | hv' | hv' <;> subst v'
            · exact False.elim (hb_ne_w rfl)
            · exact False.elim (hno_adj a haC hadj)
            · exact False.elim (hb_not_q (Finset.mem_singleton_self (some q)))
      have hnone_in : (none : Option V) ∈ some '' C :=
        mem_of_walk_closed hclosed W₀ hW₀ ⟨c₀, hc₀C, rfl⟩
      rcases hnone_in with ⟨_, _, h_eq⟩
      simp at h_eq
    · -- Case y = q: {p} would separate C from none in B, violating R_2(B, none)
      let X_p : Finset (Option V) := {some p}
      have hX_sub : (X_p : Set (Option V)) ⊆ B_verts \ {none} := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_singleton] at hx
        subst x
        exact ⟨hp_B.1, by simp⟩
      have hX_lt : X_p.card < 2 := by simp [X_p]
      have hconn := hR2 X_p hX_sub hX_lt
      have hc₀_mem : some c₀ ∈ B_verts \ (X_p : Set (Option V)) := by
        refine ⟨hc₀U.1, fun h => hc₀U.2.1 ?_⟩
        rw [Finset.mem_coe, Finset.mem_singleton] at h
        rw [h]
        exact Finset.mem_insert_self (some p) {some q}
      have hnone_mem : (none : Option V) ∈ B_verts \ (X_p : Set (Option V)) := by
        refine ⟨⟨Or.inl rfl, by simp⟩, ?_⟩
        simp [X_p]
      obtain ⟨W₀, hW₀⟩ := hconn.2 (some c₀) hc₀_mem none hnone_mem
      have hclosed : ∀ a ∈ some '' C, ∀ b ∈ B_verts \ (X_p : Set (Option V)),
          (apex H D).Adj a b → b ∈ some '' C := by
        rintro _ ⟨a, haC, rfl⟩ b ⟨⟨hb_S, hb_ne_w⟩, hb_not_p⟩ hadj
        have haU : a ∈ U := hC.1 haC
        rcases hb_S with rfl | ⟨v', _, rfl⟩
        · exact False.elim (hU_not_D a haU hadj)
        · by_cases hv'C : v' ∈ C
          · exact ⟨v', hv'C, rfl⟩
          · have hv'_bd : v' ∈ ({w, p, q} : Set V) := hnbhd_sub ⟨hv'C, a, haC, hadj⟩
            rcases hv'_bd with hv' | hv' | hv' <;> subst v'
            · exact False.elim (hb_ne_w rfl)
            · exact False.elim (hb_not_p (Finset.mem_singleton_self (some p)))
            · exact False.elim (hno_adj a haC hadj)
      have hnone_in : (none : Option V) ∈ some '' C :=
        mem_of_walk_closed hclosed W₀ hW₀ ⟨c₀, hc₀C, rfl⟩
      rcases hnone_in with ⟨_, _, h_eq⟩
      simp at h_eq
  have hrep_eq : {y | y ∈ U ∧ ReachIn H U z y} = {y | ReachIn H U z y} := by
    ext y
    exact ⟨fun h => h.2, fun h => ⟨h.mem_right, h⟩⟩
  have hrep_comp : IsComponentIn H U {y | ReachIn H U z y} := by
    rw [← hrep_eq]
    exact isComponentIn_reachIn hzU
  exact ⟨⟨hU_sub_S, hU_not_D, hbd_card, hbd_sub, hcomp_bd, hrep_comp⟩,
    ReachIn.refl hzU⟩

/-- **Each restoration replacement is valid** (Section 9.3): for a maximum-source-side minimum
two-cut `{p, q}` separating `z` from `x` in `B = J - w`, the replacement record
`restoreRecord H S D w z p q` is valid and has `z` in its recorded component. -/
theorem sec93_proved : Sec93Statement := by
  intro V _ H S D w z p q _ hH _ hwS hR3 hR2 _ _ _ hmax
  exact restoreRecord_isValid hH hwS hR3 hR2 hmax

end GraphMinor.Crossing
