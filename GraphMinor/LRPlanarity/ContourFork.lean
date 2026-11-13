module

public import GraphMinor.LRPlanarity.Statements
public import GraphMinor.LRPlanarity.ContourWord
import GraphMinor.LRPlanarity.ContourTree

/-!
# A nonalternating contour gives a fork coloring

This file proves `ContourForkStatement`, following the opening of Part IV of
`docs/planarity/planarity_test.tex`.

Color a back edge `b = (x, u)` by `L` when its target port comes before the child incidence at
`u` leading to `x` (`contourColor`). Take two back edges `b₁ = (x₁, u₁)` and `b₂ = (x₂, u₂)` with
`u₂` strictly above `u₁`, and both sources below one child `w` of `u₁`. The target port of `b₁`
and both source ports lie in the contour of `u₁`, a contiguous subword. The target port of `b₁`
comes before both source ports when `b₁` is `L`, and after both when `b₁` is `R`. The target port
of `b₂` lies outside that subword. So the two port pairs do not alternate exactly when the color
of `b₁` says which source port comes first (`not_alternating_iff`). Sources that leave the fork
`v` by different outgoing edges come in the order of those edges at `v` (`source_lt_iff`).

Now take distinct outgoing edges `e` and `f` at `v`. Every return `b` of `e` above `low f` meets
a return `c` of `f` at depth `low f`, so the color of `b` is `L` exactly when `e` precedes `f`
at `v`. This gives the fork constraints.

The lemmas `not_alternating_iff` and `source_lt_iff` are also used for the signed contour.
-/

public section

namespace GraphMinor.LRPlanarity.ContourWord

open SearchTree

variable {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)} {order : ContourOrder N}

open Classical in
/-- The event of the local order at `v` for an outgoing edge `e`: the child incidence for a
tree edge, and the source port for a back edge. -/
@[expose] noncomputable def outEvent (T : Forest N) (e : Arc N) : ContourEvent N :=
  if T.TreeEdge e then .child e.2 else .port ⟨e, true⟩

theorem outEvent_mem (hO : ValidContourOrder T G order) {v : Fin N} {e : Arc N}
    (he : T.Outgoing G v e) : outEvent T e ∈ order v := by
  unfold outEvent
  split_ifs with ht
  · rw [mem_order_child hO, ← he.1]
    exact ht
  · rw [mem_order_port hO]
    exact ⟨he.2.resolve_left ht, he.1⟩

theorem outEvent_ne {v : Fin N} {e f : Arc N} (he : T.Outgoing G v e) (hf : T.Outgoing G v f)
    (hef : e ≠ f) : outEvent T e ≠ outEvent T f := by
  unfold outEvent
  split_ifs with h₁ h₂ h₂
  · intro h
    apply hef
    rw [ContourEvent.child.injEq] at h
    exact Prod.ext (he.1.trans hf.1.symm) h
  · simp
  · simp
  · intro h
    apply hef
    rw [ContourEvent.port.injEq, Port.mk.injEq] at h
    exact h.1

/-- The source port of a return of `e` lies in the expansion of the event of `e`. -/
theorem source_mem_expand (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {e b : Arc N}
    (hb : b ∈ T.returns G e) :
    (⟨b, true⟩ : Port N) ∈ expand (subtreeWord T order) (outEvent T e) := by
  obtain ⟨hbb, ⟨heb, rfl⟩ | ⟨ht, hab, _⟩⟩ := hb
  · unfold outEvent
    split_ifs with ht
    · exact absurd ht (not_treeEdge_of_backEdge hT heb)
    · exact List.mem_singleton_self _
  · unfold outEvent
    split_ifs
    exact (mem_subtreeWord hT hO _ _).mpr ⟨hbb, by rw [portHome_source]; exact hab⟩

/-- Part IV, Section 2: "At the lowest common ancestor v of two sources, the order of their
source ports is the order of their distinct outgoing fork edges at v". -/
theorem source_lt_iff (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {v : Fin N}
    {e f b c : Arc N} (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (hef : e ≠ f)
    (hb : b ∈ T.returns G e) (hc : c ∈ T.returns G f) :
    (contourWord T order).idxOf (⟨b, true⟩ : Port N) <
        (contourWord T order).idxOf (⟨c, true⟩ : Port N) ↔
      (order v).idxOf (outEvent T e) < (order v).idxOf (outEvent T f) := by
  obtain ⟨off, hin, -⟩ := idxOf_of_infix (nodup_contourWord hT hO) (subtreeWord_infix hT hO v)
  have hnd := nodup_subtreeWord hT hO v
  have hW := subtreeWord_eq hT hO v
  have hbe := source_mem_expand hT hO hb
  have hcf := source_mem_expand hT hO hc
  have he' := outEvent_mem hO he
  have hf' := outEvent_mem hO hf
  have hbW : (⟨b, true⟩ : Port N) ∈ subtreeWord T order v :=
    hW ▸ List.mem_flatMap.mpr ⟨_, he', hbe⟩
  have hcW : (⟨c, true⟩ : Port N) ∈ subtreeWord T order v :=
    hW ▸ List.mem_flatMap.mpr ⟨_, hf', hcf⟩
  rw [hin _ hbW, hin _ hcW, Nat.add_lt_add_iff_left, hW]
  rw [hW] at hnd
  constructor
  · intro h
    rcases idxOf_lt_or_gt he' (outEvent_ne he hf hef) with h' | h'
    · exact h'
    · exact absurd (idxOf_flatMap_lt hnd hf' he' h' hcf hbe) (Nat.lt_asymm h)
  · intro h
    exact idxOf_flatMap_lt hnd he' hf' h hbe hcf

/-- The color given by a contour: `L` exactly when the target port precedes the child
incidence leading to the source. "We declare a back edge (x,u) to be L if its target token
occurs before the child incidence at u leading to x, and R otherwise." -/
theorem contourColor_eq_left_iff (hT : T.IsDFS G) {b : Arc N} {w : Fin N}
    (hw : T.parent w = some b.2) (hwb : T.Ancestor w b.1) :
    contourColor T order b = .left ↔
      (order b.2).idxOf (.port ⟨b, false⟩) < (order b.2).idxOf (.child w) := by
  unfold contourColor
  split_ifs with h
  · obtain ⟨w', hw', hw'b, hlt⟩ := h
    rw [child_unique hT hw hw' hwb hw'b]
    exact iff_of_true rfl hlt
  · exact iff_of_false (by simp) fun hlt => h ⟨w, hw, hwb, hlt⟩

/-- The four-port comparison of the opening of Part IV. Let `b` and `c` be back edges whose
sources lie below one child `w` of the head of `b`, with the head of `c` strictly higher. Then
their port pairs do not alternate exactly when `b` has color `L` just when its source port comes
first. "The target token of b1 occurs before both source tokens when b1 is L, and after both when
it is R. The target token of b2 is outside the entire interval of the subtree of u1." -/
theorem not_alternating_iff (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {b c : Arc N}
    {w : Fin N} (hb : T.BackEdge G b) (hc : T.BackEdge G c) (hw : T.parent w = some b.2)
    (hwb : T.Ancestor w b.1) (hwc : T.Ancestor w c.1) (hd : T.depth c.2 < T.depth b.2) :
    ¬ AlternatingIndices ((contourWord T order).idxOf ⟨b, true⟩)
        ((contourWord T order).idxOf ⟨b, false⟩) ((contourWord T order).idxOf ⟨c, true⟩)
        ((contourWord T order).idxOf ⟨c, false⟩) ↔
      (contourColor T order b = .left ↔
        (contourWord T order).idxOf (⟨b, true⟩ : Port N) <
          (contourWord T order).idxOf (⟨c, true⟩ : Port N)) := by
  set S := subtreeWord T order b.2 with hSdef
  obtain ⟨off, hin, hout⟩ := idxOf_of_infix (nodup_contourWord hT hO) (subtreeWord_infix hT hO b.2)
  have hnd := nodup_subtreeWord hT hO b.2
  have hS := subtreeWord_eq hT hO b.2
  rw [← hSdef] at hin hout hnd hS
  -- The three ports inside the contour of `b.2`.
  have hs₁ : (⟨b, true⟩ : Port N) ∈ expand (subtreeWord T order) (.child w) :=
    (mem_subtreeWord hT hO w _).mpr ⟨hb, by rw [portHome_source]; exact hwb⟩
  have hs₂ : (⟨c, true⟩ : Port N) ∈ expand (subtreeWord T order) (.child w) :=
    (mem_subtreeWord hT hO w _).mpr ⟨hc, by rw [portHome_source]; exact hwc⟩
  have ht₁ : (⟨b, false⟩ : Port N) ∈ expand (subtreeWord T order) (.port ⟨b, false⟩) :=
    List.mem_singleton_self _
  have hwO : ContourEvent.child w ∈ order b.2 := (mem_order_child hO).mpr hw
  have htO : ContourEvent.port ⟨b, false⟩ ∈ order b.2 := (mem_order_port hO).mpr ⟨hb, portHome_target b⟩
  have hs₁S : (⟨b, true⟩ : Port N) ∈ S := hS ▸ List.mem_flatMap.mpr ⟨_, hwO, hs₁⟩
  have hs₂S : (⟨c, true⟩ : Port N) ∈ S := hS ▸ List.mem_flatMap.mpr ⟨_, hwO, hs₂⟩
  have ht₁S : (⟨b, false⟩ : Port N) ∈ S := hS ▸ List.mem_flatMap.mpr ⟨_, htO, ht₁⟩
  -- The target port of `c` lies outside the contour of `b.2`.
  have ht₂S : (⟨c, false⟩ : Port N) ∉ S := by
    intro h
    have h' := ((mem_subtreeWord hT hO b.2 _).mp h).2
    rw [portHome_target] at h'
    have := depth_le_of_ancestor hT h'
    exact absurd this (Nat.not_le.mpr hd)
  have ht₂ := hout _ ((mem_contourWord hT hO _).mpr hc) ht₂S
  have hlen₁ := List.idxOf_lt_length_of_mem hs₁S
  have hlen₂ := List.idxOf_lt_length_of_mem hs₂S
  have hlen₃ := List.idxOf_lt_length_of_mem ht₁S
  have hne : (contourWord T order).idxOf (⟨b, true⟩ : Port N) ≠
      (contourWord T order).idxOf ⟨c, true⟩ := by
    intro h
    have := (List.idxOf_inj ((mem_contourWord hT hO _).mpr hb)).mp h
    rw [Port.mk.injEq] at this
    rw [this.1] at hd
    exact lt_irrefl _ hd
  rw [hin _ hs₁S, hin _ hs₂S] at hne
  rw [hin _ hs₁S, hin _ hs₂S, hin _ ht₁S]
  have hev : ContourEvent.port ⟨b, false⟩ ≠ ContourEvent.child w := by simp
  rw [contourColor_eq_left_iff hT hw hwb]
  rw [hS] at hnd
  rcases idxOf_lt_or_gt htO hev with h | h
  · have h₁ := idxOf_flatMap_lt hnd htO hwO h ht₁ hs₁
    have h₂ := idxOf_flatMap_lt hnd htO hwO h ht₁ hs₂
    rw [← hS] at h₁ h₂
    simp only [h, true_iff]
    unfold AlternatingIndices
    omega
  · have h₁ := idxOf_flatMap_lt hnd hwO htO h hs₁ ht₁
    have h₂ := idxOf_flatMap_lt hnd hwO htO h hs₂ ht₁
    rw [← hS] at h₁ h₂
    simp only [Nat.lt_asymm h, false_iff]
    unfold AlternatingIndices
    omega

/-- Two colors that are `L` under the same condition are equal. -/
theorem color_eq_of_iff {x y : Color} {P : Prop} (hx : x = .left ↔ P) (hy : y = .left ↔ P) :
    x = y := by
  cases x <;> cases y <;> simp_all

/-- Two colors that are `L` under opposite conditions are different. -/
theorem color_ne_of_iff {x y : Color} {P : Prop} (hx : x = .left ↔ P) (hy : y = .left ↔ ¬ P) :
    x ≠ y := by
  cases x <;> cases y <;> simp_all

/-- The opening of Part IV: in a nonalternating contour, a back edge in `I(e,f)` has color `L`
exactly when `e` precedes `f` at the fork. "For any b in I(e,f), choose a return c in F(f) of
minimum depth. It exists because d(b)>low(f), whereas d(b)<h(w)." -/
theorem contourColor_forkSet (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hNA : Nonalternating (contourWord T order)) {v : Fin N} {e f b : Arc N}
    (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (hef : e ≠ f) (hb : b ∈ T.forkSet G e f) :
    contourColor T order b = .left ↔
      (order v).idxOf (outEvent T e) < (order v).idxOf (outEvent T f) := by
  obtain ⟨hbR, hlow⟩ := hb
  obtain ⟨hbb, hvb, hbv⟩ := returns_spec hbR
  rw [he.1] at hvb hbv
  have hlowf : T.low G f < T.depth f.1 := by rw [hf.1]; omega
  obtain ⟨c, hcR, hcd⟩ := exists_returns_of_low_lt hlowf
  obtain ⟨hcb, hvc, _⟩ := returns_spec hcR
  rw [hf.1] at hvc
  -- The head of `b` is a strict ancestor of `v`; let `w` be its child above `v`.
  obtain ⟨hbv', hne⟩ := head_ancestor_of_returns hT hbR
  rw [he.1] at hbv' hne
  obtain ⟨w, hw, hwv⟩ := exists_child_of_ancestor hbv' hne
  have hd : T.depth c.2 < T.depth b.2 := by omega
  have hbc : b ≠ c := by
    rintro rfl
    exact lt_irrefl _ hd
  have key := (not_alternating_iff hT hO hbb hcb hw (ancestor_trans hwv hvb)
    (ancestor_trans hwv hvc) hd).mp (hNA b c hbc)
  rw [key]
  exact source_lt_iff hT hO he hf hef hbR hcR

end GraphMinor.LRPlanarity.ContourWord

namespace GraphMinor.LRPlanarity

open ContourWord

/-- Part IV, opening: a nonalternating tree contour gives a fork coloring, namely the coloring
by target-before-child comparisons. "Reversing the roles gives the other color to every member
of I(f,e). These are exactly the fork constraints." -/
theorem contourFork_proved : ContourForkStatement := by
  intro N G T order hT hO _ hNA v e f he hf hef
  have hE := fun b (hb : b ∈ T.forkSet G e f) => contourColor_forkSet hT hO hNA he hf hef hb
  have hF := fun b (hb : b ∈ T.forkSet G f e) =>
    contourColor_forkSet hT hO hNA hf he (Ne.symm hef) hb
  refine ⟨fun b hb b' hb' => color_eq_of_iff (hE b hb) (hE b' hb'),
    fun b hb b' hb' => color_eq_of_iff (hF b hb) (hF b' hb'), fun b hb c hc => ?_⟩
  refine color_ne_of_iff (hE b hb) ((hF c hc).trans ?_)
  rcases idxOf_lt_or_gt (outEvent_mem hO he) (outEvent_ne he hf hef) with h | h
  · exact iff_of_false (Nat.lt_asymm h) (not_not.mpr h)
  · exact iff_of_true h (Nat.lt_asymm h)

end GraphMinor.LRPlanarity
