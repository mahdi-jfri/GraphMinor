module

public import GraphMinor.Crossing.Statements
import GraphMinor.Crossing.CutSec2Fan
import GraphMinor.Crossing.CutSec3
import GraphMinor.Crossing.CutSec8
import GraphMinor.Crossing.CutSec91

/-!
# Section 9.4 of the crossing extractor: goodness of boundaries, marker invariant, and Lemma 7

This file proves the remaining three statements of Section 9 of
`docs/crossing/crossing_extractor.tex`:
* `sec94BoundaryGood_proved : Sec94BoundaryGoodStatement`
* `sec94Invariant_proved : Sec94InvariantStatement`
* `lemma7_proved : Lemma7Statement`
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set Finset

universe u

variable {V : Type u} [DecidableEq V]

/-! ### Part 1: Goodness of restoration boundary vertices (`Sec94BoundaryGoodStatement`) -/

omit [DecidableEq V] in
/-- If every disconnecting cut of size `≤ 3` in `apex H D` contains `some w`, and `w ∈ S`, then
`some w` is good in `apex H D`. -/
theorem isGood_of_must_mem {H : SimpleGraph V} {S : Set V} {D : List V} {w : V}
    (hwS : w ∈ S)
    (hmust_w : ∀ X : Finset (Option V), (X : Set (Option V)) ⊆ apexVerts S \ {none} → X.card ≤ 3 →
      ¬ IsConnectedOn (apex H D) (apexVerts S \ X) → some w ∈ X) :
    IsGood (apex H D) (apexVerts S) (some w) none := by
  intro X hX_sub hX_le
  have hw_not_X : some w ∉ X := fun hwX => (hX_sub hwX).2 (Or.inl rfl)
  have hnone_not_X : none ∉ X := fun hnX => (hX_sub hnX).2 (Or.inr rfl)
  have hX_sub' : (X : Set (Option V)) ⊆ apexVerts S \ {none} :=
    fun z hz => ⟨(hX_sub hz).1, fun h => (hX_sub hz).2 (Or.inr h)⟩
  have hconn : IsConnectedOn (apex H D) (apexVerts S \ X) := by
    by_contra hnot_conn
    exact hw_not_X (hmust_w X hX_sub' hX_le hnot_conn)
  have hw_mem : some w ∈ apexVerts S \ (X : Set (Option V)) :=
    ⟨Or.inr ⟨w, hwS, rfl⟩, hw_not_X⟩
  have hnone_mem : (none : Option V) ∈ apexVerts S \ (X : Set (Option V)) :=
    ⟨Or.inl rfl, hnone_not_X⟩
  exact hconn.2 (some w) hw_mem none hnone_mem

/-- If every disconnecting cut of size `≤ 3` in `apex H D` contains `some w`, and `some y` cannot
be separated from `none` by at most `2` vertices in `restoreVerts S w`, then `some y` is good in
`apex H D`. -/
theorem isGood_of_unseparable_restoreVerts {H : SimpleGraph V} {S : Set V} {D : List V} {w y : V}
    (hyS : y ∈ S)
    (hmust_w : ∀ X : Finset (Option V), (X : Set (Option V)) ⊆ apexVerts S \ {none} → X.card ≤ 3 →
      ¬ IsConnectedOn (apex H D) (apexVerts S \ X) → some w ∈ X)
    (hunsep : IsUnseparable (apex H D) (restoreVerts S w) (some y) none 2) :
    IsGood (apex H D) (apexVerts S) (some y) none := by
  intro X hX_sub hX_le
  by_cases hwX : some w ∈ X
  · let X' : Finset (Option V) := X.erase (some w)
    have hX'_sub : (X' : Set (Option V)) ⊆ restoreVerts S w \ {some y, none} := by
      intro z hz
      rw [Finset.mem_coe, Finset.mem_erase] at hz
      have hz_X := hX_sub hz.2
      exact ⟨⟨hz_X.1, hz.1⟩, hz_X.2⟩
    have hX'_le : X'.card ≤ 2 := by
      have hlt : X'.card < X.card := Finset.card_erase_lt_of_mem hwX
      omega
    have hreach := hunsep X' hX'_sub hX'_le
    refine hreach.mono ?_
    intro z ⟨⟨hz_S, hz_ne_w⟩, hz_not_X'⟩
    refine ⟨hz_S, fun hzX => ?_⟩
    by_cases hzw : z = some w
    · exact hz_ne_w hzw
    · exact hz_not_X' (Finset.mem_erase.mpr ⟨hzw, hzX⟩)
  · have hy_not_X : some y ∉ X := fun hyX => (hX_sub hyX).2 (Or.inl rfl)
    have hnone_not_X : none ∉ X := fun hnX => (hX_sub hnX).2 (Or.inr rfl)
    have hX_sub' : (X : Set (Option V)) ⊆ apexVerts S \ {none} :=
      fun z hz => ⟨(hX_sub hz).1, fun h => (hX_sub hz).2 (Or.inr h)⟩
    have hconn : IsConnectedOn (apex H D) (apexVerts S \ X) := by
      by_contra hnot_conn
      exact hwX (hmust_w X hX_sub' hX_le hnot_conn)
    have hy_mem : some y ∈ apexVerts S \ (X : Set (Option V)) :=
      ⟨Or.inr ⟨y, hyS, rfl⟩, hy_not_X⟩
    have hnone_mem : (none : Option V) ∈ apexVerts S \ (X : Set (Option V)) :=
      ⟨Or.inl rfl, hnone_not_X⟩
    exact hconn.2 (some y) hy_mem none hnone_mem

/-- Core version of `Sec94BoundaryGoodStatement` without unused hypotheses. -/
theorem restoreBoundary_isGood {H : SimpleGraph V} {S : Set V} {D : List V} {w z p q : V}
    (hwS : w ∈ S)
    (hmust_w : ∀ X : Finset (Option V), (X : Set (Option V)) ⊆ apexVerts S \ {none} → X.card ≤ 3 →
      ¬ IsConnectedOn (apex H D) (apexVerts S \ X) → some w ∈ X)
    (hR2 : RootedConn (apex H D) (restoreVerts S w) none 2)
    (hpq : p ≠ q)
    (hmax : IsMaxSourceSeparator (apex H D) (restoreVerts S w) (some z) none {some p, some q}) :
    IsGood (apex H D) (apexVerts S) (some w) none ∧ IsGood (apex H D) (apexVerts S) (some p) none ∧
      IsGood (apex H D) (apexVerts S) (some q) none := by
  have hw_good : IsGood (apex H D) (apexVerts S) (some w) none :=
    isGood_of_must_mem hwS hmust_w
  have hz_B : some z ∈ restoreVerts S w := mem_of_isMaxSourceSeparator_pair hmax
  have hnone_B : (none : Option V) ∈ restoreVerts S w := ⟨Or.inl rfl, by simp⟩
  have hpq_ne : (some p : Option V) ≠ some q := fun h => hpq (Option.some_injective V h)
  have hcard : ({some p, some q} : Finset (Option V)).card = 2 := Finset.card_pair hpq_ne
  have hunsep_all :=
    isUnseparable_of_isMaxSourceSeparator hnone_B hz_B hR2 hmax hcard
  have hp_in : some p ∈ ({some p, some q} : Finset (Option V)) :=
    Finset.mem_insert_self (some p) {some q}
  have hq_in : some q ∈ ({some p, some q} : Finset (Option V)) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self (some q))
  have hpS : p ∈ S := by
    simpa [apexVerts] using (hmax.1.1.1 hp_in).1.1
  have hqS : q ∈ S := by
    simpa [apexVerts] using (hmax.1.1.1 hq_in).1.1
  have hp_good : IsGood (apex H D) (apexVerts S) (some p) none :=
    isGood_of_unseparable_restoreVerts hpS hmust_w (hunsep_all (some p) hp_in)
  have hq_good : IsGood (apex H D) (apexVerts S) (some q) none :=
    isGood_of_unseparable_restoreVerts hqS hmust_w (hunsep_all (some q) hq_in)
  exact ⟨hw_good, hp_good, hq_good⟩

/-- **The boundary of a restoration replacement is good** (Section 9.4): at every restoration
replacement, all three boundary vertices `w, p, q` are good in `apex H D`. -/
theorem sec94BoundaryGood_proved : Sec94BoundaryGoodStatement := by
  intro V _ H S D w z p q _ _ _ hwS _ hmust_w hR2 _ _ hpq hmax
  exact restoreBoundary_isGood hwS hmust_w hR2 hpq hmax

/-! ### Part 2: Bad components and preservation across replacements (`Sec94InvariantStatement`) -/

omit [DecidableEq V] in
/-- A good vertex cannot belong to a bad component (a component of `J - X` avoiding `none` for
`|X| ≤ 3`). -/
theorem not_mem_bad_component_of_isGood {H : SimpleGraph V} {S : Set V} {D : List V}
    {X : Finset (Option V)} {Q : Set (Option V)} {y : V}
    (hX_sub : (X : Set (Option V)) ⊆ apexVerts S \ {none}) (hX_le : X.card ≤ 3)
    (hQ : IsComponentIn (apex H D) (apexVerts S \ X) Q) (hnone : none ∉ Q)
    (hgood : IsGood (apex H D) (apexVerts S) (some y) none) :
    some y ∉ Q := by
  intro hyQ
  have hy_not_X : some y ∉ X := (hQ.1 hyQ).2
  have hX_sub_y : (X : Set (Option V)) ⊆ apexVerts S \ {some y, none} := by
    intro z hz
    refine ⟨(hX_sub hz).1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hzy => hy_not_X (hzy ▸ hz), (hX_sub hz).2⟩
  obtain ⟨W₀, hW₀⟩ := hgood X hX_sub_y hX_le
  exact hnone (mem_of_walk_closed hQ.2.2 W₀ hW₀ hyQ)

omit [DecidableEq V] in
/-- After a valid replacement whose boundary vertices are all good, any bad component `Q` of the
new apex graph was already a component of the old apex graph with the same vertex set. -/
theorem isComponentIn_before_of_good_boundary {r : ReplRecord V} {D : List V}
    (hsupp : HP25.IsSupportedOn r.graph r.verts) (hval : r.IsValid D)
    (hbd_good : ∀ b ∈ r.boundary, IsGood (apex r.graph D) (apexVerts r.verts) (some b) none)
    {X : Finset (Option V)} {Q : Set (Option V)}
    (hX_sub : (X : Set (Option V)) ⊆ apexVerts r.newVerts \ {none}) (hX_le : X.card ≤ 3)
    (hQ : IsComponentIn (apex r.newGraph D) (apexVerts r.newVerts \ X) Q) (hnone : none ∉ Q) :
    IsComponentIn (apex r.graph D) (apexVerts r.verts \ X) Q := by
  have hbd_not_Q : ∀ b ∈ r.boundary, some b ∉ Q := by
    intro b hb
    have hb_new : b ∈ r.newVerts := hval.2.2.2.1 hb
    have hb_good_new : IsGood (apex r.newGraph D) (apexVerts r.newVerts) (some b) none :=
      isUnseparable_apex_newGraph hsupp hval hb_new (hbd_good b hb)
    exact not_mem_bad_component_of_isGood hX_sub hX_le hQ hnone hb_good_new
  have hnew_sub_old : apexVerts r.newVerts ⊆ apexVerts r.verts := by
    rintro z (rfl | ⟨y, hy_new, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨y, hy_new.1, rfl⟩
  have hQ_sub_old : Q ⊆ apexVerts r.verts \ (X : Set (Option V)) :=
    fun z hz => ⟨hnew_sub_old (hQ.1 hz).1, (hQ.1 hz).2⟩
  have hadj_old_of_new : ∀ x₁ ∈ Q, ∀ x₂ ∈ Q,
      (apex r.newGraph D).Adj x₁ x₂ → (apex r.graph D).Adj x₁ x₂ := by
    intro x₁ hx₁ x₂ hx₂ hadj
    rcases (hQ.1 hx₁).1 with rfl | ⟨a, _, rfl⟩
    · exact False.elim (hnone hx₁)
    · rcases (hQ.1 hx₂).1 with rfl | ⟨b, _, rfl⟩
      · exact False.elim (hnone hx₂)
      · rcases hadj with ⟨h_old, -, -⟩ | ⟨ha_bd, _, _⟩
        · exact h_old
        · exact False.elim (hbd_not_Q a ha_bd hx₁)
  have hwalk_old : ∀ {u v : Option V} (p : (apex r.newGraph D).Walk u v),
      (∀ z ∈ p.support, z ∈ Q) → ReachIn (apex r.graph D) Q u v := by
    intro u v p
    induction p with
    | nil =>
      intro hsupp_p
      exact ReachIn.refl (hsupp_p _ (Walk.start_mem_support _))
    | @cons u w v hadj rest ih =>
      intro hsupp_p
      have huQ : u ∈ Q := hsupp_p u (Walk.start_mem_support _)
      have hwQ : w ∈ Q := hsupp_p w (List.mem_cons_of_mem _ (Walk.start_mem_support _))
      have hadj_old := hadj_old_of_new u huQ w hwQ hadj
      exact (ReachIn.of_adj hadj_old huQ hwQ).trans
        (ih (fun z hz => hsupp_p z (List.mem_cons_of_mem _ hz)))
  have hQ_conn_old : IsConnectedOn (apex r.graph D) Q := by
    refine ⟨hQ.2.1.1, fun a ha b hb => ?_⟩
    obtain ⟨p, hp⟩ := hQ.2.1.2 a ha b hb
    exact hwalk_old p hp
  refine ⟨hQ_sub_old, hQ_conn_old, fun x₁ hx₁ x₂ hx₂ hadj => ?_⟩
  rcases (hQ.1 hx₁).1 with rfl | ⟨a, ha_new, rfl⟩
  · exact False.elim (hnone hx₁)
  · rcases hx₂.1 with rfl | ⟨b, hb_verts, rfl⟩
    · have hadj_new : (apex r.newGraph D).Adj (some a) none := hadj
      exact hQ.2.2 (some a) hx₁ none ⟨Or.inl rfl, hx₂.2⟩ hadj_new
    · have hab_old : r.graph.Adj a b := hadj
      have hb_not_del : b ∉ r.deleted := by
        intro hb_del
        have ha_bd := ReplRecord.mem_boundary_of_adj_deleted hval hb_del ha_new.2 hab_old.symm
        exact hbd_not_Q a ha_bd hx₁
      have hb_new : b ∈ r.newVerts := ⟨hb_verts, hb_not_del⟩
      have hadj_new : (apex r.newGraph D).Adj (some a) (some b) :=
        Or.inl ⟨hab_old, ha_new.2, hb_not_del⟩
      exact hQ.2.2 (some a) hx₁ (some b) ⟨Or.inr ⟨b, hb_new, rfl⟩, hx₂.2⟩ hadj_new

omit [DecidableEq V] in
/-- `RootedConn (apex H D) (apexVerts S) none (k + 1)` is preserved by any valid replacement `r`. -/
theorem rootedConn_after_of_isValid {r : ReplRecord V} {D : List V} {k : ℕ}
    (hsupp : HP25.IsSupportedOn r.graph r.verts) (hval : r.IsValid D)
    (hR : RootedConn (apex r.graph D) (apexVerts r.verts) none (k + 1)) :
    RootedConn (apex r.newGraph D) (apexVerts r.newVerts) none (k + 1) := by
  intro X hX_sub hX_lt
  have hnone_not_X : none ∉ X := fun hnone => (hX_sub hnone).2 rfl
  have hnone_mem : (none : Option V) ∈ apexVerts r.newVerts \ (X : Set (Option V)) :=
    ⟨Or.inl rfl, hnone_not_X⟩
  refine isConnectedOn_of_reachIn hnone_mem fun z hz => ?_
  rcases hz.1 with rfl | ⟨v, hv_new, rfl⟩
  · exact ReachIn.refl hnone_mem
  · have hunsep_old : IsUnseparable (apex r.graph D) (apexVerts r.verts) (some v) none k := by
      intro Y hY_sub hY_le
      have hY_sub' : (Y : Set (Option V)) ⊆ apexVerts r.verts \ {none} :=
        fun w hw => ⟨(hY_sub hw).1, fun h => (hY_sub hw).2 (Or.inr h)⟩
      have hY_lt : Y.card < k + 1 := by omega
      have hconn := hR Y hY_sub' hY_lt
      have hv_Y : some v ∈ apexVerts r.verts \ (Y : Set (Option V)) :=
        ⟨Or.inr ⟨v, hv_new.1, rfl⟩, fun hvY => (hY_sub hvY).2 (Or.inl rfl)⟩
      have hnone_Y : (none : Option V) ∈ apexVerts r.verts \ (Y : Set (Option V)) :=
        ⟨Or.inl rfl, fun hnY => (hY_sub hnY).2 (Or.inr rfl)⟩
      exact hconn.2 (some v) hv_Y none hnone_Y
    have hunsep_new := isUnseparable_apex_newGraph hsupp hval hv_new hunsep_old
    have hX_sub_v : (X : Set (Option V)) ⊆ apexVerts r.newVerts \ {some v, none} := by
      intro w hw
      refine ⟨(hX_sub hw).1, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun hwv => hz.2 (hwv ▸ hw), (hX_sub hw).2⟩
    exact hunsep_new X hX_sub_v (by omega)

/-- `RootedConn (apex H D) (apexVerts S) none 3` implies
`RootedConn (apex H D) (restoreVerts S w) none 2` whenever `w ∈ S`. -/
theorem rootedConn_restoreVerts_of_rootedConn {H : SimpleGraph V} {S : Set V} {D : List V} {w : V}
    (hwS : w ∈ S) (hR3 : RootedConn (apex H D) (apexVerts S) none 3) :
    RootedConn (apex H D) (restoreVerts S w) none 2 := by
  intro X hX_sub hX_lt
  let X' : Finset (Option V) := insert (some w) X
  have hX'_sub : (X' : Set (Option V)) ⊆ apexVerts S \ {none} := by
    intro z hz
    rw [Finset.mem_coe, Finset.mem_insert] at hz
    rcases hz with rfl | hzX
    · exact ⟨Or.inr ⟨w, hwS, rfl⟩, by simp⟩
    · exact ⟨(hX_sub hzX).1.1, (hX_sub hzX).2⟩
  have hX'_lt : X'.card < 3 := by
    dsimp only [X']
    have hle := Finset.card_insert_le (some w) X
    omega
  have hconn := hR3 X' hX'_sub hX'_lt
  have hset_eq : restoreVerts S w \ (X : Set (Option V)) = apexVerts S \ (X' : Set (Option V)) := by
    ext z
    simp only [restoreVerts, X', Finset.coe_insert, Set.mem_sdiff, Set.mem_singleton_iff,
      Set.mem_insert_iff, Finset.mem_coe, not_or]
    tauto
  rwa [hset_eq]

omit [DecidableEq V] in
/-- If `none ∈ T` and `¬ IsConnectedOn J T`, then there is a component `Q` of `J` in `T` with
`none ∉ Q`. -/
theorem exists_bad_component_of_not_isConnectedOn {J : SimpleGraph (Option V)}
    {T : Set (Option V)} (hnone : none ∈ T) (hnot_conn : ¬ IsConnectedOn J T) :
    ∃ Q : Set (Option V), IsComponentIn J T Q ∧ none ∉ Q := by
  have hex : ∃ z₀ ∈ T, ¬ ReachIn J T z₀ none := by
    by_contra hall
    push Not at hall
    exact hnot_conn (isConnectedOn_of_reachIn hnone hall)
  rcases hex with ⟨z₀, hz₀T, hnot_reach⟩
  refine ⟨{z | z ∈ T ∧ ReachIn J T z₀ z}, isComponentIn_reachIn hz₀T, ?_⟩
  rintro ⟨_, hreach⟩
  exact hnot_reach hreach

omit [DecidableEq V] in
/-- If `Q` is a component of `J` in `T` with `none ∈ T` and `none ∉ Q`, then `¬ IsConnectedOn J T`. -/
theorem not_isConnectedOn_of_bad_component {J : SimpleGraph (Option V)} {T Q : Set (Option V)}
    (hnone_T : none ∈ T) (hQ : IsComponentIn J T Q) (hnone_Q : none ∉ Q) :
    ¬ IsConnectedOn J T := by
  intro hconn
  rcases hQ.2.1.1 with ⟨q₀, hq₀Q⟩
  obtain ⟨W₀, hW₀⟩ := hconn.2 q₀ (hQ.1 hq₀Q) none hnone_T
  exact hnone_Q (mem_of_walk_closed hQ.2.2 W₀ hW₀ hq₀Q)

omit [DecidableEq V] in
/-- The property that every disconnecting cut of size `≤ 3` contains `some w` is preserved by any
valid replacement whose boundary vertices are all good. -/
theorem must_mem_after_of_good_boundary {r : ReplRecord V} {D : List V} {w : V}
    (hsupp : HP25.IsSupportedOn r.graph r.verts) (hval : r.IsValid D)
    (hbd_good : ∀ b ∈ r.boundary, IsGood (apex r.graph D) (apexVerts r.verts) (some b) none)
    (hmust_w : ∀ X : Finset (Option V), (X : Set (Option V)) ⊆ apexVerts r.verts \ {none} →
      X.card ≤ 3 → ¬ IsConnectedOn (apex r.graph D) (apexVerts r.verts \ X) → some w ∈ X) :
    ∀ X : Finset (Option V), (X : Set (Option V)) ⊆ apexVerts r.newVerts \ {none} →
      X.card ≤ 3 → ¬ IsConnectedOn (apex r.newGraph D) (apexVerts r.newVerts \ X) → some w ∈ X := by
  intro X hX_sub hX_le hnot_conn
  have hnone_mem : (none : Option V) ∈ apexVerts r.newVerts \ (X : Set (Option V)) :=
    ⟨Or.inl rfl, fun hn => (hX_sub hn).2 rfl⟩
  obtain ⟨Q, hQ, hnone_Q⟩ := exists_bad_component_of_not_isConnectedOn hnone_mem hnot_conn
  have hQ_old := isComponentIn_before_of_good_boundary hsupp hval hbd_good hX_sub hX_le hQ hnone_Q
  have hnone_old : (none : Option V) ∈ apexVerts r.verts \ (X : Set (Option V)) :=
    ⟨Or.inl rfl, fun hn => (hX_sub hn).2 rfl⟩
  have hnot_conn_old := not_isConnectedOn_of_bad_component hnone_old hQ_old hnone_Q
  have hX_sub_old : (X : Set (Option V)) ⊆ apexVerts r.verts \ {none} := by
    intro z hz
    rcases (hX_sub hz).1 with rfl | ⟨y, hy_new, rfl⟩
    · exact ⟨Or.inl rfl, (hX_sub hz).2⟩
    · exact ⟨Or.inr ⟨y, hy_new.1, rfl⟩, (hX_sub hz).2⟩
  exact hmust_w X hX_sub_old hX_le hnot_conn_old

open Classical in
/-- In the initial contracted graph `contractGraph K u v`, every bad component `Q` of
`apex (contractGraph K u v) (contractCycle D u)` separated from `none` by a set `X` of size `≤ 3`
contains a marker. -/
theorem initial_bad_component_has_marker {K : SimpleGraph V} {S : Set V} {D : List V} {u v : V}
    (hS_fin : S.Finite) (hK : HP25.IsSupportedOn K S) (hD : HP25.IsCycleList K D)
    (hclean : IsClean K S D) (htrial : IsTrialEdge K D u v)
    {X : Finset (Option V)} {Q : Set (Option V)}
    (hX_sub : (X : Set (Option V)) ⊆ apexVerts (S \ {u}) \ {none}) (hX_le : X.card ≤ 3)
    (hQ : IsComponentIn (apex (contractGraph K u v) (contractCycle D u))
      (apexVerts (S \ {u}) \ X) Q)
    (hnone_Q : none ∉ Q) :
    ∃ y ∈ markers K u v, some y ∈ Q := by
  let J₀ := apex (contractGraph K u v) (contractCycle D u)
  let T₀ := apexVerts (S \ {u})
  obtain ⟨_, hmust_v, _, hmarker⟩ := sec91_proved K S D u v hS_fin hK hD hclean htrial
  have hnone_T₀ : (none : Option V) ∈ T₀ \ (X : Set (Option V)) :=
    ⟨Or.inl rfl, fun hn => (hX_sub hn).2 rfl⟩
  have hnot_conn : ¬ IsConnectedOn J₀ (T₀ \ X) :=
    not_isConnectedOn_of_bad_component hnone_T₀ hQ hnone_Q
  have hvX : some v ∈ X := hmust_v X hX_sub hX_le hnot_conn
  let Y : Finset (Option V) := X.erase (some v)
  have hY_len : Y.toList.length ≤ 2 := by
    rw [Finset.length_toList]
    have hlt : Y.card < X.card := Finset.card_erase_lt_of_mem hvX
    omega
  have hY_ne_none : ∀ z ∈ Y.toList, z ≠ none := by
    intro z hz
    rw [Finset.mem_toList] at hz
    exact (hX_sub (Finset.mem_of_mem_erase hz)).2
  have hex_pq : ∃ p q : Option V, p ≠ none ∧ q ≠ none ∧
      (X : Set (Option V)) = {some v, p, q} := by
    have hX_eq : (X : Set (Option V)) = insert (some v) (Y : Set (Option V)) := by
      ext z
      simp only [Y, Finset.mem_coe, Set.mem_insert_iff, Finset.mem_erase]
      by_cases hzv : z = some v
      · subst z; simp [hvX]
      · simp [hzv]
    rcases hL : Y.toList with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
    · refine ⟨some v, some v, by simp, by simp, ?_⟩
      rw [hX_eq]
      ext z
      have hzY : z ∉ Y := by
        intro hz
        have : z ∈ Y.toList := Finset.mem_toList.mpr hz
        simp [hL] at this
      simp [hzY]
    · have hp_ne : p ≠ none := hY_ne_none p (by simp [hL])
      refine ⟨p, some v, hp_ne, by simp, ?_⟩
      rw [hX_eq]
      ext z
      have hzY : z ∈ Y ↔ z = p := by
        rw [← Finset.mem_toList, hL]
        simp
      simp [hzY, or_comm]
    · have hp_ne : p ≠ none := hY_ne_none p (by simp [hL])
      have hq_ne : q ≠ none := hY_ne_none q (by simp [hL])
      refine ⟨p, q, hp_ne, hq_ne, ?_⟩
      rw [hX_eq]
      ext z
      have hzY : z ∈ Y ↔ z = p ∨ z = q := by
        rw [← Finset.mem_toList, hL]
        simp
      simp [hzY]
    · rw [hL] at hY_len; simp at hY_len
  rcases hex_pq with ⟨p, q, hp_ne, hq_ne, hX_set_eq⟩
  rw [hX_set_eq] at hQ
  exact hmarker p q Q hp_ne hq_ne hQ hnone_Q

/-! ### Part 3: Equivalence of `HP25.IsCrossed` and `IsCrossingPair` across replacements -/

omit [DecidableEq V] in
private theorem ne_of_lt_of_getElem?_nodup {D : List V} {i j : ℕ} {u v : V}
    (hnd : D.Nodup) (hij : i < j) (hu : D[i]? = some u) (hv : D[j]? = some v) : u ≠ v := by
  intro h_eq
  subst v
  rw [List.getElem?_eq_some_iff] at hu hv
  rcases hu with ⟨hi, hu_eq⟩
  rcases hv with ⟨hj, hv_eq⟩
  have h_idx_eq : i = j :=
    (hnd.getElem_inj_iff (hi := hi) (hj := hj)).mp (hu_eq.trans hv_eq.symm)
  omega

omit [DecidableEq V] in
private theorem isDPathList_support_of_isTPath {G : SimpleGraph V} {D : List V} {u v : V}
    {W : G.Walk u v} (huv : u ≠ v) (hW : HP25.IsTPath G D W) :
    IsDPathList G D W.support ∧ HasEnds W.support u v := by
  obtain ⟨hpath, hends⟩ := isPathList_support_of_isPath hW.1
  have hlen : 2 ≤ W.support.length := by
    cases W with
    | nil => exact False.elim (huv rfl)
    | @cons _ w _ _ rest =>
      simp only [Walk.support_cons, List.length_cons]
      have hne : rest.support ≠ [] := Walk.support_ne_nil rest
      have hpos : 0 < rest.support.length := List.length_pos_iff.mpr hne
      omega
  refine ⟨⟨hpath, hlen, ?_, ?_, ?_⟩, hends⟩
  · intro a ha
    rw [hends.1, Option.some.injEq] at ha
    exact ha ▸ hW.2.1
  · intro b hb
    rw [hends.2, Option.some.injEq] at hb
    exact hb ▸ hW.2.2.1
  · intro y hy
    obtain ⟨hy_supp, hyu, hyv⟩ := (mem_inner_iff_of_nodup hpath.2.1 hlen hends y).mp hy
    exact (hW.2.2.2 y hy_supp hyu hyv).1

omit [DecidableEq V] in
private theorem exists_isCrossingPair_of_isCrossed {G : SimpleGraph V} {D : List V}
    (hnd : D.Nodup) (hcross : HP25.IsCrossed G D) :
    ∃ L₁ L₂, IsCrossingPair G D L₁ L₂ := by
  rcases hcross with ⟨a, b, c, d, Q, R, ⟨i, r_idx, j, s, hir, hrj, hjs, ha, hc, hb, hd⟩,
    hQ, hR, hdisj⟩
  have hab : a ≠ b := ne_of_lt_of_getElem?_nodup hnd (Nat.lt_trans hir hrj) ha hb
  have hcd : c ≠ d := ne_of_lt_of_getElem?_nodup hnd (Nat.lt_trans hrj hjs) hc hd
  obtain ⟨hQ_dpath, hQ_ends⟩ := isDPathList_support_of_isTPath hab hQ
  obtain ⟨hR_dpath, hR_ends⟩ := isDPathList_support_of_isTPath hcd hR
  exact ⟨Q.support, R.support, hQ_dpath, hR_dpath, hdisj,
    i, r_idx, j, s, hir, hrj, hjs, a, c, b, d, ha, hc, hb, hd,
    Or.inl ⟨Or.inl hQ_ends, Or.inl hR_ends⟩⟩

omit [DecidableEq V] in
private theorem exists_walk_of_isChain :
    ∀ {G : SimpleGraph V} {L : List V} {u v : V},
      L ≠ [] → L.IsChain G.Adj → HasEnds L u v →
      ∃ W : G.Walk u v, W.support = L
  | _, [], _, _, hne, _, _ => False.elim (hne rfl)
  | _, [a], u, v, _, _, hends => by
    have h1 := hends.1
    have h2 := hends.2
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h1 h2
    subst a v
    exact ⟨.nil, rfl⟩
  | G, a :: b :: rest, u, v, _, hch, hends => by
    have h1 := hends.1
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst a
    have hab : G.Adj u b := List.IsChain.rel_head? hch rfl
    have hlast : (b :: rest).getLast? = some v := by
      have h2 := hends.2
      rwa [List.getLast?_cons_cons] at h2
    obtain ⟨W', hW'⟩ := exists_walk_of_isChain (List.cons_ne_nil b rest) hch.tail ⟨rfl, hlast⟩
    refine ⟨.cons hab W', ?_⟩
    simp [Walk.support_cons, hW']

omit [DecidableEq V] in
private theorem exists_tpath_of_isDPathList {G : SimpleGraph V} {D L : List V} {u v : V}
    (hL : IsDPathList G D L) (hends : HasEndsUnordered L u v) :
    ∃ W : G.Walk u v, HP25.IsTPath G D W ∧ ∀ y, y ∈ W.support ↔ y ∈ L := by
  have hforward : ∀ {x y : V}, HasEnds L x y →
      ∃ W : G.Walk x y, HP25.IsTPath G D W ∧ W.support = L := by
    intro x y hxy
    obtain ⟨W, hW_supp⟩ := exists_walk_of_isChain hL.1.1 hL.1.2.2 hxy
    have hW_path : W.IsPath := by
      rw [Walk.isPath_def, hW_supp]
      exact hL.1.2.1
    have hxD : x ∈ D := hL.2.2.1 x hxy.1
    have hyD : y ∈ D := hL.2.2.2.1 y hxy.2
    refine ⟨W, ⟨hW_path, hxD, hyD, fun z hz hzx hzy => ?_⟩, hW_supp⟩
    rw [hW_supp] at hz
    have hz_in : z ∈ inner L :=
      (mem_inner_iff_of_nodup hL.1.2.1 hL.2.1 hxy z).mpr ⟨hz, hzx, hzy⟩
    have hz_not_D := hL.2.2.2.2 z hz_in
    exact ⟨hz_not_D, hz_not_D⟩
  rcases hends with huv | hvu
  · obtain ⟨W, hW, hsupp⟩ := hforward huv
    exact ⟨W, hW, fun y => by rw [hsupp]⟩
  · obtain ⟨W₀, hW₀, hsupp₀⟩ := hforward hvu
    have hrev_path : W₀.reverse.IsPath := by
      rw [Walk.isPath_def, Walk.support_reverse, List.nodup_reverse]
      exact hW₀.1.support_nodup
    refine ⟨W₀.reverse, ⟨hrev_path, hW₀.2.2.1, hW₀.2.1, ?_⟩, ?_⟩
    · intro z hz hzu hzv
      rw [Walk.support_reverse, List.mem_reverse] at hz
      exact hW₀.2.2.2 z hz hzv hzu
    · intro y
      rw [Walk.support_reverse, List.mem_reverse, hsupp₀]

omit [DecidableEq V] in
private theorem isCrossed_of_isCrossingPair {G : SimpleGraph V} {D L₁ L₂ : List V}
    (hcross : IsCrossingPair G D L₁ L₂) : HP25.IsCrossed G D := by
  rcases hcross with ⟨hL₁, hL₂, hdisj, i, r_idx, j, s, hir, hrj, hjs, a, c, b, d,
    ha, hc, hb, hd, hends⟩
  rcases hends with ⟨hends₁, hends₂⟩ | ⟨hends₁, hends₂⟩
  · obtain ⟨Q, hQ, hQ_mem⟩ := exists_tpath_of_isDPathList hL₁ hends₁
    obtain ⟨R, hR, hR_mem⟩ := exists_tpath_of_isDPathList hL₂ hends₂
    have hdisj' : Q.support.Disjoint R.support := by
      rw [List.disjoint_left]
      intro y hyQ hyR
      exact List.disjoint_left.mp hdisj ((hQ_mem y).mp hyQ) ((hR_mem y).mp hyR)
    exact ⟨a, b, c, d, Q, R, ⟨i, r_idx, j, s, hir, hrj, hjs, ha, hc, hb, hd⟩, hQ, hR, hdisj'⟩
  · obtain ⟨Q, hQ, hQ_mem⟩ := exists_tpath_of_isDPathList hL₂ hends₂
    obtain ⟨R, hR, hR_mem⟩ := exists_tpath_of_isDPathList hL₁ hends₁
    have hdisj' : Q.support.Disjoint R.support := by
      rw [List.disjoint_left]
      intro y hyQ hyR
      exact List.disjoint_left.mp hdisj ((hR_mem y).mp hyR) ((hQ_mem y).mp hyQ)
    exact ⟨a, b, c, d, Q, R, ⟨i, r_idx, j, s, hir, hrj, hjs, ha, hc, hb, hd⟩, hQ, hR, hdisj'⟩

/-- Across a valid replacement `r`, `HP25.IsCrossed` is preserved in both directions. -/
theorem isCrossed_iff_of_isValid {r : ReplRecord V} {D : List V}
    (hsupp : HP25.IsSupportedOn r.graph r.verts) (hD_nodup : D.Nodup)
    (hD_verts : ∀ x ∈ D, x ∈ r.verts) (hval : r.IsValid D) :
    HP25.IsCrossed r.graph D ↔ HP25.IsCrossed r.newGraph D := by
  constructor
  · exact isCrossed_newGraph_of_isCrossed hsupp hD_verts hval
  · intro hcross_new
    obtain ⟨L₁, L₂, hpair_new⟩ := exists_isCrossingPair_of_isCrossed hD_nodup hcross_new
    obtain ⟨L₁', L₂', hpair_old⟩ := exists_isCrossingPair_of_newGraph hval hpair_new
    exact isCrossed_of_isCrossingPair hpair_old

/-! ### Part 4: Existence of a maximum-source-side minimum separator on a finite vertex set -/

open Classical in
/-- Given two minimum `z`-`x` separators `X` and `Y`, their join separator `J_sep` is also a
minimum `z`-`x` separator whose `sourceSide` contains `sourceSide B T x X ∪ sourceSide B T x Y`. -/
private theorem exists_join_isMinSeparator {W : Type u} {B : SimpleGraph W} {T : Set W}
    {z x : W} {X Y : Finset W} (hzT : z ∈ T)
    (hX_min : IsMinSeparator B T z x X) (hY_min : IsMinSeparator B T z x Y) :
    ∃ J_sep : Finset W, IsMinSeparator B T z x J_sep ∧
      sourceSide B T x X ∪ sourceSide B T x Y ⊆ sourceSide B T x J_sep := by
  let U : Set W := sourceSide B T x X
  let V_set : Set W := sourceSide B T x Y
  have hzU : z ∈ U := mem_sourceSide_of_isSeparator hzT hX_min.1
  have hzV : z ∈ V_set := mem_sourceSide_of_isSeparator hzT hY_min.1
  let J_sep : Finset W := (X ∪ Y).filter (fun w => ¬ (w ∈ U ∨ w ∈ V_set))
  let M_sep : Finset W := (X ∩ Y) ∪ (X ∪ Y).filter (fun w => w ∈ U ∨ w ∈ V_set)
  have hdisj_M : Disjoint (X ∩ Y) ((X ∪ Y).filter (fun w => w ∈ U ∨ w ∈ V_set)) := by
    rw [Finset.disjoint_left]
    intro w hw_inter hw_filt
    rw [Finset.mem_inter] at hw_inter
    rw [Finset.mem_filter] at hw_filt
    rcases hw_filt.2 with hwU | hwV
    · exact hwU.2.1 hw_inter.1
    · exact hwV.2.1 hw_inter.2
  have hsum_card : J_sep.card + M_sep.card = X.card + Y.card := by
    dsimp only [J_sep, M_sep]
    have hM_card : ((X ∩ Y) ∪ (X ∪ Y).filter (fun w => w ∈ U ∨ w ∈ V_set)).card =
        (X ∩ Y).card + ((X ∪ Y).filter (fun w => w ∈ U ∨ w ∈ V_set)).card :=
      Finset.card_union_of_disjoint hdisj_M
    have hfilt := Finset.card_filter_add_card_filter_not (s := X ∪ Y)
      (p := fun w => w ∈ U ∨ w ∈ V_set)
    have hunion := Finset.card_union_add_card_inter X Y
    omega
  have hXY_sub : ((X ∪ Y : Finset W) : Set W) ⊆ T \ {z, x} := by
    rw [Finset.coe_union]
    exact Set.union_subset hX_min.1.1 hY_min.1.1
  have hM_sub_XY : M_sep ⊆ X ∪ Y :=
    Finset.union_subset (Finset.inter_subset_left.trans Finset.subset_union_left)
      (Finset.filter_subset _ _)
  have hM_sep : IsSeparator B T z x M_sep := by
    refine ⟨fun w hw => hXY_sub (hM_sub_XY hw), fun ⟨q, hq⟩ => ?_⟩
    have hclosed : ∀ a ∈ U ∩ V_set, ∀ b ∈ T \ (M_sep : Set W), B.Adj a b → b ∈ U ∩ V_set := by
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
    have hxUV : x ∈ U ∩ V_set := mem_of_walk_closed hclosed q hq ⟨hzU, hzV⟩
    exact not_mem_sourceSide_self hxUV.1
  have hX_le_M : X.card ≤ M_sep.card := hX_min.2 M_sep hM_sep
  have hJ_le_Y : J_sep.card ≤ Y.card := by omega
  have hUV_sub_J : U ∪ V_set ⊆ sourceSide B T x J_sep := by
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
    have hclosed : ∀ a ∈ U ∪ V_set, ∀ b ∈ T \ (J_sep : Set W), B.Adj a b → b ∈ U ∪ V_set := by
      intro a ha b ⟨hbT, hbJ⟩ hadj
      have hb_all : (b ∈ U ∨ b ∈ V_set) ∨ (b ∈ X ∨ b ∈ Y) := by
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
    have hxUV : x ∈ U ∪ V_set := mem_of_walk_closed hclosed q hq hw
    rcases hxUV with hxU | hxV
    · exact not_mem_sourceSide_self hxU
    · exact not_mem_sourceSide_self hxV
  have hz_J : z ∈ sourceSide B T x J_sep := hUV_sub_J (Or.inl hzU)
  have hJ_sub : (J_sep : Set W) ⊆ T \ {z, x} :=
    fun w hw => hXY_sub (Finset.filter_subset _ _ hw)
  have hJ_sep : IsSeparator B T z x J_sep := ⟨hJ_sub, hz_J.2.2⟩
  have hJ_min : IsMinSeparator B T z x J_sep :=
    ⟨hJ_sep, fun X' hX' => le_trans hJ_le_Y (hY_min.2 X' hX')⟩
  exact ⟨J_sep, hJ_min, hUV_sub_J⟩

open Classical in
/-- On a finite vertex set `T`, the existence of a minimum `z`-`x` separator implies the existence
of a maximum-source-side minimum `z`-`x` separator. -/
private theorem exists_isMaxSourceSeparator_of_isMinSeparator {W : Type u} {B : SimpleGraph W}
    {T : Set W} {z x : W} (hT_fin : T.Finite) (hzT : z ∈ T)
    {X₀ : Finset W} (hX₀ : IsMinSeparator B T z x X₀) :
    ∃ X : Finset W, IsMaxSourceSeparator B T z x X := by
  have hstep : ∀ (n : ℕ) (X : Finset W), IsMinSeparator B T z x X →
      T.ncard - (sourceSide B T x X).ncard ≤ n →
      ∃ X' : Finset W, IsMaxSourceSeparator B T z x X' := by
    intro n
    induction n with
    | zero =>
      intro X hX hle
      by_cases hmax : IsMaxSourceSeparator B T z x X
      · exact ⟨X, hmax⟩
      · unfold IsMaxSourceSeparator at hmax
        push Not at hmax
        obtain ⟨Y, hY_min, hnot_sub⟩ := hmax hX
        obtain ⟨J_sep, hJ_min, hUV_sub⟩ := exists_join_isMinSeparator hzT hX hY_min
        have hssub : sourceSide B T x X ⊂ sourceSide B T x J_sep := by
          refine ⟨(Set.subset_union_left).trans hUV_sub, fun h_eq => hnot_sub ?_⟩
          exact (Set.subset_union_right).trans (hUV_sub.trans h_eq)
        have hJ_fin : (sourceSide B T x J_sep).Finite :=
          hT_fin.subset (fun w hw => hw.1)
        have hlt_ncard : (sourceSide B T x X).ncard < (sourceSide B T x J_sep).ncard :=
          Set.ncard_lt_ncard hssub hJ_fin
        have hle_T : (sourceSide B T x J_sep).ncard ≤ T.ncard :=
          Set.ncard_le_ncard (fun w hw => hw.1) hT_fin
        omega
    | succ m ih =>
      intro X hX hle
      by_cases hmax : IsMaxSourceSeparator B T z x X
      · exact ⟨X, hmax⟩
      · unfold IsMaxSourceSeparator at hmax
        push Not at hmax
        obtain ⟨Y, hY_min, hnot_sub⟩ := hmax hX
        obtain ⟨J_sep, hJ_min, hUV_sub⟩ := exists_join_isMinSeparator hzT hX hY_min
        have hssub : sourceSide B T x X ⊂ sourceSide B T x J_sep := by
          refine ⟨(Set.subset_union_left).trans hUV_sub, fun h_eq => hnot_sub ?_⟩
          exact (Set.subset_union_right).trans (hUV_sub.trans h_eq)
        have hJ_fin : (sourceSide B T x J_sep).Finite :=
          hT_fin.subset (fun w hw => hw.1)
        have hlt_ncard : (sourceSide B T x X).ncard < (sourceSide B T x J_sep).ncard :=
          Set.ncard_lt_ncard hssub hJ_fin
        have hle_T : (sourceSide B T x J_sep).ncard ≤ T.ncard :=
          Set.ncard_le_ncard (fun w hw => hw.1) hT_fin
        exact ih J_sep hJ_min (by omega)
  exact hstep (T.ncard - (sourceSide B T x X₀).ncard) X₀ hX₀ le_rfl

/-! ### Part 5: Restoration steps and runs (`Sec94InvariantStatement` and `Lemma7Statement`) -/

private structure RestoreState (D' : List V) (w : V) (H : SimpleGraph V) (S : Set V) : Prop where
  finite : S.Finite
  supported : HP25.IsSupportedOn H S
  nodup_cycle : D'.Nodup
  cycle_sub : ∀ x ∈ D', x ∈ S
  mem_w : w ∈ S
  r3 : RootedConn (apex H D') (apexVerts S) none 3
  must_w : ∀ X : Finset (Option V), (X : Set (Option V)) ⊆ apexVerts S \ {none} → X.card ≤ 3 →
    ¬ IsConnectedOn (apex H D') (apexVerts S \ X) → some w ∈ X

private theorem restoreState_init {K : SimpleGraph V} {S : Set V} {D : List V} {u v : V}
    (hS_fin : S.Finite) (hK : HP25.IsSupportedOn K S) (hD : HP25.IsCycleList K D)
    (hclean : IsClean K S D) (htrial : IsTrialEdge K D u v) :
    RestoreState (contractCycle D u) v (contractGraph K u v) (S \ {u}) := by
  have hvS : v ∈ S := hK htrial.1.symm
  have huv : u ≠ v := K.ne_of_adj htrial.1
  obtain ⟨hR3, hmust_v, _, _⟩ := sec91_proved K S D u v hS_fin hK hD hclean htrial
  refine ⟨hS_fin.subset Set.sdiff_subset, ?_, ?_, ?_, ⟨hvS, huv.symm⟩, hR3, hmust_v⟩
  · intro a b ⟨_, hau, _, hcases⟩
    rcases hcases with hab | ⟨rfl, _⟩ | ⟨_, hua⟩
    · exact ⟨hK hab, hau⟩
    · exact ⟨hvS, hau⟩
    · exact ⟨hK hua.symm, hau⟩
  · unfold contractCycle
    split_ifs
    · exact hD.2.1.erase u
    · exact hD.2.1
  · intro x hx
    unfold contractCycle at hx
    split_ifs at hx with huD
    · exact ⟨mem_of_mem_cycleList hK hD (List.mem_of_mem_erase hx),
        fun hxu => hD.2.1.not_mem_erase (hxu ▸ hx)⟩
    · exact ⟨mem_of_mem_cycleList hK hD hx, fun hxu => huD (hxu ▸ hx)⟩

private theorem restoreStep_props {D' : List V} {w z : V} {H H' : SimpleGraph V} {S S' : Set V}
    {rec₁ : Option (ReplRecord V)} (st : RestoreState D' w H S)
    (hstep : IsRestoreStep D' w z H S H' S' rec₁) :
    RestoreState D' w H' S' ∧
    (∀ (X : Finset (Option V)) (Q : Set (Option V)),
      (X : Set (Option V)) ⊆ apexVerts S' \ {none} → X.card ≤ 3 →
      IsComponentIn (apex H' D') (apexVerts S' \ X) Q → none ∉ Q →
      IsComponentIn (apex H D') (apexVerts S \ X) Q) ∧
    (S' ⊆ S) ∧
    (∀ y ∈ S', IsGood (apex H D') (apexVerts S) (some y) none →
      IsGood (apex H' D') (apexVerts S') (some y) none) ∧
    (z ∉ S' ∨ IsGood (apex H' D') (apexVerts S') (some z) none) ∧
    (HP25.IsCrossed H D' ↔ HP25.IsCrossed H' D') ∧
    (∀ r ∈ rec₁.toList, r.IsValid D') ∧
    rec₁.toList.length ≤ 1 := by
  rcases hstep with ⟨hskip, hH_eq, hS_eq, hrec_eq⟩ |
    ⟨_, _, _, p, q, hpq, hmax, hrec_eq, hH_eq, hS_eq⟩
  · subst H' S' rec₁
    refine ⟨st, fun _ _ _ _ hQ _ => hQ, Set.Subset.rfl, fun _ _ h => h, ?_, Iff.rfl,
      by simp, by simp⟩
    rcases hskip with hz_not_S | hzD' | hunsep
    · exact Or.inl hz_not_S
    · refine Or.inr fun X hX_sub _ => ?_
      have hzS : z ∈ S := st.cycle_sub z hzD'
      have hz_mem : some z ∈ apexVerts S \ (X : Set (Option V)) :=
        ⟨Or.inr ⟨z, hzS, rfl⟩, fun hzX => (hX_sub hzX).2 (Or.inl rfl)⟩
      have hnone_mem : (none : Option V) ∈ apexVerts S \ (X : Set (Option V)) :=
        ⟨Or.inl rfl, fun hnX => (hX_sub hnX).2 (Or.inr rfl)⟩
      have hadj : (apex H D').Adj (some z) none := hzD'
      exact ReachIn.of_adj hadj hz_mem hnone_mem
    · by_cases hzS : z ∈ S
      · exact Or.inr (isGood_of_unseparable_restoreVerts hzS st.must_w hunsep)
      · exact Or.inl hzS
  · subst H' S' rec₁
    let r := restoreRecord H S D' w z p q
    have hR2 : RootedConn (apex H D') (restoreVerts S w) none 2 :=
      rootedConn_restoreVerts_of_rootedConn st.mem_w st.r3
    obtain ⟨hval, hz_rep⟩ := restoreRecord_isValid st.supported st.mem_w st.r3 hR2 hmax
    obtain ⟨hw_good, hp_good, hq_good⟩ :=
      restoreBoundary_isGood st.mem_w st.must_w hR2 hpq hmax
    have hbd_good : ∀ b ∈ r.boundary, IsGood (apex r.graph D') (apexVerts r.verts) (some b) none := by
      intro b hb
      change b ∈ ({w, p, q} : Finset V) at hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact hw_good
      · exact hp_good
      · exact hq_good
    have hsupp' : HP25.IsSupportedOn r.newGraph r.newVerts := by
      intro a b hadj
      rcases hadj with ⟨hab, ha_not_del, _⟩ | ⟨ha_bd, _, _⟩
      · exact ⟨st.supported hab, ha_not_del⟩
      · exact hval.2.2.2.1 ha_bd
    have hcycle_sub' : ∀ x ∈ D', x ∈ r.newVerts :=
      fun x hx => ⟨st.cycle_sub x hx, fun hx_del => hval.2.1 x hx_del hx⟩
    have hw_mem' : w ∈ r.newVerts :=
      hval.2.2.2.1 (Finset.mem_insert_self w {p, q})
    have hr3' : RootedConn (apex r.newGraph D') (apexVerts r.newVerts) none 3 :=
      rootedConn_after_of_isValid (k := 2) st.supported hval st.r3
    have hmust_w' := must_mem_after_of_good_boundary st.supported hval hbd_good st.must_w
    have hst' : RestoreState D' w r.newGraph r.newVerts :=
      ⟨st.finite.subset Set.sdiff_subset, hsupp', st.nodup_cycle, hcycle_sub', hw_mem',
        hr3', hmust_w'⟩
    have hz_del : z ∈ r.deleted := hval.2.2.2.2.2.1 hz_rep
    have hz_not_new : z ∉ r.newVerts := fun hz_new => hz_new.2 hz_del
    refine ⟨hst',
      fun _ _ hX_sub hX_le hQ hnone =>
        isComponentIn_before_of_good_boundary st.supported hval hbd_good hX_sub hX_le hQ hnone,
      Set.sdiff_subset,
      fun y hy hgood => isUnseparable_apex_newGraph st.supported hval hy hgood,
      Or.inl hz_not_new,
      isCrossed_iff_of_isValid st.supported st.nodup_cycle st.cycle_sub hval,
      ?_, by simp⟩
    intro r' hr'
    simp only [Option.toList_some, List.mem_singleton] at hr'
    exact hr' ▸ hval

private theorem restoreRun_props {D' : List V} {w : V} :
    ∀ (M₁ : List V) {H H' : SimpleGraph V} {S S' : Set V} {recs : List (ReplRecord V)},
      RestoreState D' w H S →
      IsRestoreRun D' w M₁ H S H' S' recs →
      RestoreState D' w H' S' ∧
      (∀ (X : Finset (Option V)) (Q : Set (Option V)),
        (X : Set (Option V)) ⊆ apexVerts S' \ {none} → X.card ≤ 3 →
        IsComponentIn (apex H' D') (apexVerts S' \ X) Q → none ∉ Q →
        IsComponentIn (apex H D') (apexVerts S \ X) Q) ∧
      (S' ⊆ S) ∧
      (∀ y ∈ S', IsGood (apex H D') (apexVerts S) (some y) none →
        IsGood (apex H' D') (apexVerts S') (some y) none) ∧
      (∀ z ∈ M₁, z ∉ S' ∨ IsGood (apex H' D') (apexVerts S') (some z) none) ∧
      (HP25.IsCrossed H D' ↔ HP25.IsCrossed H' D') ∧
      (∀ r ∈ recs, r.IsValid D') ∧
      recs.length ≤ M₁.length
  | [], _, H', _, S', recs, st, ⟨hH, hS, hrecs⟩ => by
    subst hH hS hrecs
    exact ⟨st, fun _ _ _ _ hQ _ => hQ, Set.Subset.rfl, fun _ _ h => h, by simp, Iff.rfl,
      by simp, by simp⟩
  | z :: M', _, _, _, S', _, st, ⟨H₁, S₁, rec₁, recs', hstep, hrun, hrecs_eq⟩ => by
    obtain ⟨st₁, hcomp₁, hsub₁, hgood₁, hz₁, hcross₁, hval₁, hlen₁⟩ :=
      restoreStep_props st hstep
    obtain ⟨st', hcomp', hsub', hgood_all, hgood_M', hcross', hval', hlen'⟩ :=
      restoreRun_props M' st₁ hrun
    refine ⟨st', ?_, hsub'.trans hsub₁,
      fun y hyS' hgood => hgood_all y hyS' (hgood₁ y (hsub' hyS') hgood),
      ?_, hcross₁.trans hcross', ?_, ?_⟩
    · intro X Q hX_sub hX_le hQ hnone
      have hQ₁ := hcomp' X Q hX_sub hX_le hQ hnone
      have hX_sub₁ : (X : Set (Option V)) ⊆ apexVerts S₁ \ {none} := by
        intro x hx
        rcases (hX_sub hx).1 with rfl | ⟨y, hyS', rfl⟩
        · exact ⟨Or.inl rfl, (hX_sub hx).2⟩
        · exact ⟨Or.inr ⟨y, hsub' hyS', rfl⟩, (hX_sub hx).2⟩
      exact hcomp₁ X Q hX_sub₁ hX_le hQ₁ hnone
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hyM'
      · rcases hz₁ with hz_not_S₁ | hz_good₁
        · exact Or.inl fun hzS' => hz_not_S₁ (hsub' hzS')
        · by_cases hyS' : y ∈ S'
          · exact Or.inr (hgood_all y hyS' hz_good₁)
          · exact Or.inl hyS'
      · exact hgood_M' y hyM'
    · intro r hr
      rw [hrecs_eq, List.mem_append] at hr
      rcases hr with hr₁ | hr'
      · exact hval₁ r hr₁
      · exact hval' r hr'
    · rw [hrecs_eq, List.length_append, List.length_cons]
      omega

/-- **Every bad component keeps a marker** (Section 9.4): at any point during a restoration run,
every bad component separated from `none` by at most `3` vertices contains an original marker. -/
theorem sec94Invariant_proved : Sec94InvariantStatement := by
  intro V _ K S D u v M₁ M₂ H S' recs hS_fin hK hD hclean htrial _ _ _ hrun X Q hX_sub hX_le hQ hnone
  have st₀ := restoreState_init hS_fin hK hD hclean htrial
  obtain ⟨_, hcomp, hsub, _, _, _, _, _⟩ := restoreRun_props M₁ st₀ hrun
  have hQ₀ := hcomp X Q hX_sub hX_le hQ hnone
  have hX_sub₀ : (X : Set (Option V)) ⊆ apexVerts (S \ {u}) \ {none} := by
    intro x hx
    rcases (hX_sub hx).1 with rfl | ⟨y, hyS', rfl⟩
    · exact ⟨Or.inl rfl, (hX_sub hx).2⟩
    · exact ⟨Or.inr ⟨y, hsub hyS', rfl⟩, (hX_sub hx).2⟩
  exact initial_bad_component_has_marker hS_fin hK hD hclean htrial hX_sub₀ hX_le hQ₀ hnone

open Classical in
/-- Existence of a restoration step from any `RestoreState` at a marker `z ≠ w`. -/
private theorem exists_restoreStep {D' : List V} {w z : V} {H : SimpleGraph V} {S : Set V}
    (st : RestoreState D' w H S) (hzw : z ≠ w) :
    ∃ (H' : SimpleGraph V) (S' : Set V) (rec₁ : Option (ReplRecord V)),
      IsRestoreStep D' w z H S H' S' rec₁ := by
  by_cases hskip : z ∉ S ∨ z ∈ D' ∨ IsUnseparable (apex H D') (restoreVerts S w) (some z) none 2
  · exact ⟨H, S, none, Or.inl ⟨hskip, rfl, rfl, rfl⟩⟩
  · push Not at hskip
    rcases hskip with ⟨hzS, hzD', hunsep⟩
    let B_verts := restoreVerts S w
    have hB_fin : B_verts.Finite :=
      ((st.finite.image some).insert none).subset Set.sdiff_subset
    have hnone_B : (none : Option V) ∈ B_verts := ⟨Or.inl rfl, by simp⟩
    have hz_B : some z ∈ B_verts :=
      ⟨Or.inr ⟨z, hzS, rfl⟩, fun h => hzw (Option.some_injective V h)⟩
    have hz_ne_none : (some z : Option V) ≠ none := by simp
    have hnot_adj : ¬ (apex H D').Adj (some z) none := hzD'
    have hR2 : RootedConn (apex H D') B_verts none 2 :=
      rootedConn_restoreVerts_of_rootedConn st.mem_w st.r3
    obtain ⟨X₀, hX₀_min, hX₀_card⟩ :=
      sec92Value_proved (apex H D') B_verts none (some z) hB_fin hnone_B hz_B hz_ne_none
        hnot_adj hR2 hunsep
    obtain ⟨X, hX_max⟩ := exists_isMaxSourceSeparator_of_isMinSeparator hB_fin hz_B hX₀_min
    have hX_le : X.card ≤ X₀.card := hX_max.1.2 X₀ hX₀_min.1
    have hX₀_le : X₀.card ≤ X.card := hX₀_min.2 X hX_max.1.1
    have hX_card : X.card = 2 := by omega
    obtain ⟨a, b, hab, hX_eq⟩ := Finset.card_eq_two.mp hX_card
    have ha_B : a ∈ B_verts \ {some z, none} := by
      apply hX_max.1.1.1
      rw [hX_eq]
      exact Finset.mem_insert_self a {b}
    have hb_B : b ∈ B_verts \ {some z, none} := by
      apply hX_max.1.1.1
      rw [hX_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    have ha_ne_none : a ≠ none := fun h => ha_B.2 (Or.inr h)
    have hb_ne_none : b ≠ none := fun h => hb_B.2 (Or.inr h)
    rcases a with _ | p
    · exact False.elim (ha_ne_none rfl)
    · rcases b with _ | q
      · exact False.elim (hb_ne_none rfl)
      · have hpq : p ≠ q := fun h => hab (congrArg some h)
        rw [hX_eq] at hX_max
        let r := restoreRecord H S D' w z p q
        exact ⟨r.newGraph, r.newVerts, some r,
          Or.inr ⟨hzS, hzD', hunsep, p, q, hpq, hX_max, rfl, rfl, rfl⟩⟩

open Classical in
private theorem exists_restoreRun {D' : List V} {w : V} :
    ∀ (M₁ : List V) {H : SimpleGraph V} {S : Set V},
      RestoreState D' w H S → (∀ z ∈ M₁, z ≠ w) →
      ∃ (H' : SimpleGraph V) (S' : Set V) (recs : List (ReplRecord V)),
        IsRestoreRun D' w M₁ H S H' S' recs
  | [], H, S, _, _ => ⟨H, S, [], rfl, rfl, rfl⟩
  | z :: M', H, S, st, hne => by
    have hzw : z ≠ w := hne z List.mem_cons_self
    obtain ⟨H₁, S₁, rec₁, hstep⟩ := exists_restoreStep st hzw
    obtain ⟨st₁, _, _, _, _, _, _, _⟩ := restoreStep_props st hstep
    obtain ⟨H', S', recs', hrun⟩ :=
      exists_restoreRun M' st₁ (fun y hy => hne y (List.mem_cons_of_mem _ hy))
    exact ⟨H', S', rec₁.toList ++ recs', H₁, S₁, rec₁, recs', hstep, hrun, rfl⟩

/-- **Lemma 7** (Section 9.4): restoration returns a clean instance equivalent for crossing
existence to the contracted instance, with valid replacement records and at most `|M|` records. -/
theorem lemma7_proved : Lemma7Statement := by
  intro V _ K S D u v M hS_fin hK hD hclean htrial _ _ hM
  have st₀ := restoreState_init hS_fin hK hD hclean htrial
  have hM_ne_v : ∀ z ∈ M, z ≠ v := fun z hz => ((hM z).mp hz).2
  refine ⟨exists_restoreRun M st₀ hM_ne_v, ?_⟩
  intro H S' recs hrun
  obtain ⟨_, hcomp, hsub, _, hgood_M, hcross, hval, hlen⟩ := restoreRun_props M st₀ hrun
  have hclean' : IsClean H S' (contractCycle D u) := by
    intro X hX_sub hX_lt
    by_contra hnot_conn
    have hnone_mem : (none : Option V) ∈ apexVerts S' \ (X : Set (Option V)) :=
      ⟨Or.inl rfl, fun hn => (hX_sub hn).2 rfl⟩
    obtain ⟨Q, hQ, hnone_Q⟩ := exists_bad_component_of_not_isConnectedOn hnone_mem hnot_conn
    have hX_le : X.card ≤ 3 := by omega
    have hQ₀ := hcomp X Q hX_sub hX_le hQ hnone_Q
    have hX_sub₀ : (X : Set (Option V)) ⊆ apexVerts (S \ {u}) \ {none} := by
      intro x hx
      rcases (hX_sub hx).1 with rfl | ⟨y, hyS', rfl⟩
      · exact ⟨Or.inl rfl, (hX_sub hx).2⟩
      · exact ⟨Or.inr ⟨y, hsub hyS', rfl⟩, (hX_sub hx).2⟩
    obtain ⟨y, hy_marker, hyQ⟩ :=
      initial_bad_component_has_marker hS_fin hK hD hclean htrial hX_sub₀ hX_le hQ₀ hnone_Q
    have hyM : y ∈ M := (hM y).mpr hy_marker
    have hyS' : y ∈ S' := by
      simpa [apexVerts] using (hQ.1 hyQ).1
    rcases hgood_M y hyM with hy_not_S' | hy_good
    · exact hy_not_S' hyS'
    · exact not_mem_bad_component_of_isGood hX_sub hX_le hQ hnone_Q hy_good hyQ
  exact ⟨hclean', hcross, hval, hlen⟩

end GraphMinor.Crossing
