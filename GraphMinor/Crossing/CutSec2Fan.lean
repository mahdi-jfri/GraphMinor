module

public import GraphMinor.Crossing.Statements
import GraphMinor.Menger.SimpleGraph

/-!
# Section 2 of the crossing extractor: clean instances and four-fans

This file proves the equivalence in Section 2 of `docs/crossing/crossing_extractor.tex` between
cleanliness (`IsClean K S D`, that is, `𝓡_4(K + x, x)`) and the existence of a four-fan to `D` from
every off-cycle vertex (`cleanIffFourFan_proved : CleanIffFourFanStatement`), using Menger's theorem
for finite simple graphs (`GraphMinor.Menger.exists_disjointPaths`).

It also provides basic lemmas on `ReachIn`, `IsConnectedOn`, `apex`, and `apexVerts` used across
the separator and restoration files.
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set

universe u

variable {V W : Type*}

/-! ### Basic lemmas on `ReachIn`, `IsConnectedOn`, `apex`, and `apexVerts` -/

theorem ReachIn.refl {G : SimpleGraph W} {T : Set W} {a : W} (ha : a ∈ T) :
    ReachIn G T a a :=
  ⟨.nil, fun y hy => by
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    exact hy ▸ ha⟩

theorem ReachIn.symm {G : SimpleGraph W} {T : Set W} {a b : W} (h : ReachIn G T a b) :
    ReachIn G T b a := by
  rcases h with ⟨p, hp⟩
  refine ⟨p.reverse, fun y hy => hp y ?_⟩
  simpa [Walk.support_reverse] using hy

theorem ReachIn.trans {G : SimpleGraph W} {T : Set W} {a b c : W}
    (h1 : ReachIn G T a b) (h2 : ReachIn G T b c) :
    ReachIn G T a c := by
  rcases h1 with ⟨p, hp⟩
  rcases h2 with ⟨q, hq⟩
  refine ⟨p.append q, fun y hy => ?_⟩
  rw [Walk.mem_support_append_iff] at hy
  exact hy.elim (hp y) (hq y)

theorem ReachIn.mono {G : SimpleGraph W} {T T' : Set W} {a b : W}
    (h : T ⊆ T') (hr : ReachIn G T a b) :
    ReachIn G T' a b := by
  rcases hr with ⟨p, hp⟩
  exact ⟨p, fun y hy => h (hp y hy)⟩

theorem ReachIn.of_adj {G : SimpleGraph W} {T : Set W} {a b : W}
    (hab : G.Adj a b) (ha : a ∈ T) (hb : b ∈ T) :
    ReachIn G T a b := by
  refine ⟨hab.toWalk, fun y hy => ?_⟩
  simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hy
  exact hy.elim (fun h => h ▸ ha) (fun h => h ▸ hb)

theorem ReachIn.mem_left {G : SimpleGraph W} {T : Set W} {a b : W} (h : ReachIn G T a b) :
    a ∈ T := by
  rcases h with ⟨p, hp⟩
  exact hp a p.start_mem_support

theorem ReachIn.mem_right {G : SimpleGraph W} {T : Set W} {a b : W} (h : ReachIn G T a b) :
    b ∈ T := by
  rcases h with ⟨p, hp⟩
  exact hp b p.end_mem_support

theorem isConnectedOn_of_reachIn {G : SimpleGraph W} {T : Set W} {x : W}
    (hx : x ∈ T) (h : ∀ a ∈ T, ReachIn G T a x) :
    IsConnectedOn G T :=
  ⟨⟨x, hx⟩, fun a ha b hb => (h a ha).trans (h b hb).symm⟩

@[simp]
theorem none_mem_apexVerts (S : Set V) : (none : Option V) ∈ apexVerts S :=
  Or.inl rfl

@[simp]
theorem some_mem_apexVerts_iff {S : Set V} {v : V} :
    some v ∈ apexVerts S ↔ v ∈ S := by
  simp [apexVerts]

@[simp]
theorem apex_adj_some_some {G : SimpleGraph V} {D : List V} {a b : V} :
    (apex G D).Adj (some a) (some b) ↔ G.Adj a b :=
  Iff.rfl

@[simp]
theorem apex_adj_some_none {G : SimpleGraph V} {D : List V} {d : V} :
    (apex G D).Adj (some d) none ↔ d ∈ D :=
  Iff.rfl

@[simp]
theorem apex_adj_none_some {G : SimpleGraph V} {D : List V} {d : V} :
    (apex G D).Adj none (some d) ↔ d ∈ D :=
  Iff.rfl

@[simp]
theorem not_apex_adj_none_none {G : SimpleGraph V} {D : List V} :
    ¬ (apex G D).Adj none none :=
  id

theorem support_subset_of_isSupportedOn {K : SimpleGraph V} {S : Set V}
    (hK : HP25.IsSupportedOn K S) {a b : V} (ha : a ∈ S) (p : K.Walk a b) :
    ∀ y ∈ p.support, y ∈ S := by
  induction p with
  | nil =>
    intro y hy
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    exact hy ▸ ha
  | @cons u w b hadj rest ih =>
    have hw : w ∈ S := hK hadj.symm
    intro y hy
    rw [Walk.support_cons, List.mem_cons] at hy
    exact hy.elim (fun h => h ▸ ha) (ih hw y)

theorem mem_of_mem_cycleList {K : SimpleGraph V} {S : Set V} {D : List V}
    (hK : HP25.IsSupportedOn K S) (hD : HP25.IsCycleList K D) {d : V} (hd : d ∈ D) :
    d ∈ S := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  have hlen : (D.rotate 1).length = D.length := by simp
  have hmem : (D[i], (D.rotate 1)[i]'(by omega)) ∈ D.zip (D.rotate 1) := by
    rw [List.mem_iff_getElem]
    refine ⟨i, by simp [hlen, hi], by simp⟩
  exact hK (hD.2.2 _ hmem)

/-- Embedding a walk of `K` into `apex K D` via `some`. -/
abbrev someHom (K : SimpleGraph V) (D : List V) : K →g apex K D where
  toFun := some
  map_rel' h := h

theorem reachIn_apex_of_reachIn {K : SimpleGraph V} {D : List V} {A : Set V}
    {T : Set (Option V)} (hAT : ∀ y ∈ A, some y ∈ T) {a b : V}
    (hr : ReachIn K A a b) :
    ReachIn (apex K D) T (some a) (some b) := by
  rcases hr with ⟨p, hp⟩
  refine ⟨p.map (someHom K D), fun z hz => ?_⟩
  rw [Walk.support_map, List.mem_map] at hz
  rcases hz with ⟨y, hy, rfl⟩
  exact hAT y (hp y hy)

/-! ### Proof of `CleanIffFourFanStatement` -/

/-- If `v ∈ S \ D` has a four-fan to `D` and `X` has size `< 4` with `some v ∉ X` and `none ∉ X`,
then `some v` reaches `none` in `apex K D` avoiding `X`. -/
private theorem reachIn_apex_of_hasFourFan {K : SimpleGraph V} {S : Set V} {D : List V}
    (hK : HP25.IsSupportedOn K S) {v : V} (hvS : v ∈ S)
    (hfan : HasFourFan K D v) {X : Finset (Option V)}
    (hvX : some v ∉ X) (hnoneX : (none : Option V) ∉ X) (hcard : X.card < 4) :
    ReachIn (apex K D) (apexVerts S \ X) (some v) none := by
  classical
  rcases hfan with ⟨e, P, _, heD, _, hdisj⟩
  have hex : ∃ i : Fin 4, ∀ y ∈ (P i).support, some y ∉ X := by
    by_contra hno
    push Not at hno
    choose y hy_supp hy_X using hno
    let f : Fin 4 → X := fun i => ⟨some (y i), hy_X i⟩
    have hf_inj : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hyij : y i = y j := Option.some.inj (congrArg Subtype.val hij)
      have hyv : y i = v := hdisj i j hne (y i) (hy_supp i) (hyij ▸ hy_supp j)
      exact hvX (hyv ▸ hy_X i)
    have hle := Fintype.card_le_of_injective f hf_inj
    simp only [Fintype.card_fin, Fintype.card_coe] at hle
    omega
  rcases hex with ⟨i, hi⟩
  have hsupp_S : ∀ y ∈ (P i).support, y ∈ S :=
    support_subset_of_isSupportedOn hK hvS (P i)
  have hreach_K : ReachIn K {y | y ∈ S ∧ some y ∉ X} v (e i) :=
    ⟨P i, fun y hy => ⟨hsupp_S y hy, hi y hy⟩⟩
  have hreach_e : ReachIn (apex K D) (apexVerts S \ X) (some v) (some (e i)) :=
    reachIn_apex_of_reachIn
      (fun y (hy : y ∈ S ∧ some y ∉ X) =>
        show some y ∈ apexVerts S \ X from ⟨some_mem_apexVerts_iff.mpr hy.1, hy.2⟩)
      hreach_K
  have he_mem : some (e i) ∈ apexVerts S \ X :=
    ⟨some_mem_apexVerts_iff.mpr (hsupp_S (e i) (P i).end_mem_support),
      hi (e i) (P i).end_mem_support⟩
  have hnone_mem : (none : Option V) ∈ apexVerts S \ X := ⟨none_mem_apexVerts S, hnoneX⟩
  exact hreach_e.trans (ReachIn.of_adj (apex_adj_some_none.mpr (heD i)) he_mem hnone_mem)

/-- The off-`v` induced subgraph on `↥S` used to apply Menger's theorem for a four-fan at `v`. -/
private def offVertexGraph (K : SimpleGraph V) (S : Set V) (v : V) : SimpleGraph ↥S where
  Adj a b := K.Adj a.1 b.1 ∧ a.1 ≠ v ∧ b.1 ≠ v
  symm := ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩
  loopless := ⟨fun _ ⟨h1, _, _⟩ => K.loopless.irrefl _ h1⟩

private theorem ne_of_mem_support_offVertexWalk {K : SimpleGraph V} {S : Set V} {v : V}
    {a b : ↥S} (ha : a.1 ≠ v) (w : (offVertexGraph K S v).Walk a b) :
    ∀ x ∈ w.support, x.1 ≠ v := by
  induction w with
  | nil =>
    intro x hx
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx ▸ ha
  | @cons u y b hadj rest ih =>
    intro x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    exact hx.elim (fun h => h ▸ ha) (ih hadj.2.2 x)

/-- Any walk in `apex K D` from `some a` (`a ∈ S \ {v}`) to `z = none` that stays in `apexVerts S \ X`
and avoids `some v` yields a walk in `offVertexGraph K S v` from `⟨a, ha⟩` to a cycle vertex in `D`
avoiding `{y : ↥S | some y.1 ∈ X}`. -/
private theorem exists_offVertexWalk_of_apexWalk {K : SimpleGraph V} {S : Set V} {D : List V}
    (hK : HP25.IsSupportedOn K S) {v : V} {X : Finset (Option V)}
    {w z : Option V} (q : (apex K D).Walk w z) :
    z = none →
    some v ∉ q.support →
    (∀ u ∈ q.support, u ∈ apexVerts S \ X) →
    ∀ (a : V) (ha : a ∈ S), w = some a →
      ∃ (b : ↥S), b.1 ∈ D ∧
        ∃ (w₀ : (offVertexGraph K S v).Walk ⟨a, ha⟩ b),
          ∀ x ∈ w₀.support, some x.1 ∉ X := by
  induction q with
  | nil =>
    intro hz _ _ a _ hw
    cases hw.symm.trans hz
  | @cons w u z hadj rest ih =>
    intro hz hv_not hsupp a ha hw
    subst hw
    have ha_notX : some a ∉ X := (hsupp (some a) (Walk.start_mem_support _)).2
    have hav : a ≠ v := fun h => hv_not (h ▸ Walk.start_mem_support _)
    have hv_rest : some v ∉ rest.support := fun h =>
      hv_not (List.mem_cons_of_mem _ h)
    have hsupp_rest : ∀ x ∈ rest.support, x ∈ apexVerts S \ X := fun x hx =>
      hsupp x (List.mem_cons_of_mem _ hx)
    cases u with
    | none =>
      have haD : a ∈ D := apex_adj_some_none.mp hadj
      refine ⟨⟨a, ha⟩, haD, .nil, fun x hx => ?_⟩
      simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      exact hx ▸ ha_notX
    | some a' =>
      have hadjK : K.Adj a a' := apex_adj_some_some.mp hadj
      have ha'S : a' ∈ S := hK hadjK.symm
      have ha'v : a' ≠ v := fun h =>
        hv_rest (h ▸ Walk.start_mem_support _)
      obtain ⟨b, hbD, w₀, hw₀⟩ :=
        ih hz hv_rest hsupp_rest a' ha'S rfl
      have hadj₀ : (offVertexGraph K S v).Adj ⟨a, ha⟩ ⟨a', ha'S⟩ := ⟨hadjK, hav, ha'v⟩
      refine ⟨b, hbD, .cons hadj₀ w₀, fun x hx => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha_notX
      · exact hw₀ x hx

/-- Embedding `offVertexGraph K S v` into `K`. -/
private abbrev offVertexHom (K : SimpleGraph V) (S : Set V) (v : V) :
    offVertexGraph K S v →g K where
  toFun x := x.1
  map_rel' h := h.1

private theorem not_mem_support_offVertexWalk {K : SimpleGraph V} {S : Set V} {v : V}
    {a b : ↥S} (ha : a.1 ≠ v) (w : (offVertexGraph K S v).Walk a b) :
    v ∉ (w.map (offVertexHom K S v)).support := by
  intro hv
  rw [Walk.support_map, List.mem_map] at hv
  rcases hv with ⟨x, hx, hxv⟩
  exact ne_of_mem_support_offVertexWalk ha w x hx hxv

/-- **Clean instances and four-fans** (Section 2): "Because every vertex of $D$ is adjacent to $x$,
Menger's theorem gives" that `(K, D)` is clean if and only if every vertex `v ∉ V(D)` has a
four-fan to `D`. -/
theorem cleanIffFourFan_proved : CleanIffFourFanStatement := by
  intro V K S D hSfin hK _hD
  constructor
  · intro hclean v hvS hvD
    classical
    have : Finite ↥S := hSfin.to_subtype
    let _ : Fintype ↥S := Fintype.ofFinite ↥S
    let K₀ := offVertexGraph K S v
    let A₀ : Set ↥S := {x : ↥S | K.Adj v x.1}
    let B₀ : Set ↥S := {x : ↥S | x.1 ∈ D}
    have hmenger : HasDisjointPaths K₀ A₀ B₀ 4 := by
      refine Menger.exists_disjointPaths K₀ A₀ B₀ inferInstance 4 fun U₀ hU₀ => ?_
      by_contra hlt
      push Not at hlt
      let U_fin : Finset ↥S := U₀.toFinset
      let X : Finset (Option V) :=
        (U_fin.filter (fun x : ↥S => x.1 ≠ v)).image (fun x : ↥S => some x.1)
      have hX_sub : (X : Set (Option V)) ⊆ apexVerts S \ {none} := by
        intro z hz
        simp only [X, Finset.mem_coe, Finset.mem_image, Finset.mem_filter] at hz
        rcases hz with ⟨y, _, rfl⟩
        exact ⟨some_mem_apexVerts_iff.mpr y.2, by simp⟩
      have hv_notX : some v ∉ X := by
        simp only [X, Finset.mem_image, Finset.mem_filter, Option.some.injEq, not_exists, not_and]
        intro x hx heq
        exact hx.2 heq
      have hX_card : X.card < 4 := by
        have h1 : X.card ≤ (U_fin.filter (fun x : ↥S => x.1 ≠ v)).card := Finset.card_image_le
        have h2 : (U_fin.filter (fun x : ↥S => x.1 ≠ v)).card ≤ U_fin.card :=
          Finset.card_filter_le _ _
        have h3 : U_fin.card = U₀.ncard := by
          rw [Set.ncard_eq_toFinset_card']
        omega
      have hconn := hclean X hX_sub hX_card
      have hv_mem : some v ∈ apexVerts S \ X := ⟨some_mem_apexVerts_iff.mpr hvS, hv_notX⟩
      have hnone_mem : (none : Option V) ∈ apexVerts S \ X :=
        ⟨none_mem_apexVerts S, fun h => (hX_sub h).2 rfl⟩
      obtain ⟨w, hw_supp⟩ := hconn.2 (some v) hv_mem none hnone_mem
      let p := w.bypass
      have hp_path : p.IsPath := w.bypass_isPath
      have hp_supp : ∀ z ∈ p.support, z ∈ apexVerts S \ X :=
        fun z hz => hw_supp z (w.support_bypass_subset_support hz)
      cases hp_eq : p with
      | @cons _ u _ hadj₁ rest =>
        have hnd : (some v :: rest.support).Nodup := by
          rw [← Walk.support_cons hadj₁, ← hp_eq]
          exact hp_path.support_nodup
        have hv_rest : some v ∉ rest.support := (List.nodup_cons.mp hnd).1
        have hsupp_rest : ∀ z ∈ rest.support, z ∈ apexVerts S \ X := by
          intro z hz
          apply hp_supp
          rw [hp_eq, Walk.support_cons]
          exact List.mem_cons_of_mem _ hz
        cases u with
        | none =>
          exact hvD (apex_adj_some_none.mp hadj₁)
        | some a =>
          have hadj_va : K.Adj v a := apex_adj_some_some.mp hadj₁
          have haS : a ∈ S := hK hadj_va.symm
          obtain ⟨b, hbD, w₀, hw₀⟩ :=
            exists_offVertexWalk_of_apexWalk hK rest rfl hv_rest hsupp_rest a haS rfl
          let P₀ : PathFromTo K₀ A₀ B₀ :=
            ⟨⟨a, haS⟩, b, w₀.bypass, w₀.bypass_isPath, hadj_va, hbD⟩
          obtain ⟨x, hx_supp, hx_U₀⟩ := hU₀ P₀
          have hx_w₀ : x ∈ w₀.support := w₀.support_bypass_subset_support hx_supp
          have hxv : x.1 ≠ v :=
            ne_of_mem_support_offVertexWalk (K.ne_of_adj hadj_va).symm w₀ x hx_w₀
          have hx_X : some x.1 ∈ X := by
            simp only [X, U_fin, Finset.mem_image, Finset.mem_filter, Set.mem_toFinset]
            exact ⟨x, ⟨hx_U₀, hxv⟩, rfl⟩
          exact hw₀ x hx_w₀ hx_X
    rcases hmenger with ⟨P₀, hP₀_disj⟩
    let e : Fin 4 → V := fun i => (P₀ i).last.1
    let P : ∀ i : Fin 4, K.Walk v (e i) := fun i =>
      Walk.cons (P₀ i).first_mem ((P₀ i).walk.map (offVertexHom K S v))
    refine ⟨e, P, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      by_contra hne
      have hlast_eq : (P₀ i).last = (P₀ j).last := Subtype.ext hij
      have hmem_i : (P₀ i).last ∈ (P₀ i).walk.support := Walk.end_mem_support _
      have hmem_j : (P₀ i).last ∈ (P₀ j).walk.support := by
        rw [hlast_eq]
        exact Walk.end_mem_support _
      exact Set.disjoint_left.mp (hP₀_disj hne) hmem_i hmem_j
    · intro i
      exact (P₀ i).last_mem
    · intro i
      have hmap_path : ((P₀ i).walk.map (offVertexHom K S v)).IsPath :=
        (P₀ i).isPath.map Subtype.val_injective
      have hv_not : v ∉ ((P₀ i).walk.map (offVertexHom K S v)).support :=
        not_mem_support_offVertexWalk (K.ne_of_adj (P₀ i).first_mem).symm (P₀ i).walk
      exact Walk.IsPath.cons hmap_path hv_not
    · intro i j hij y hyi hyj
      simp only [P, Walk.support_cons, List.mem_cons, Walk.support_map, List.mem_map] at hyi hyj
      rcases hyi with rfl | ⟨xi, hxi, rfl⟩
      · rfl
      · rcases hyj with hvy | ⟨xj, hxj, hxj_eq⟩
        · exact hvy
        · have hxij : xi = xj := Subtype.ext hxj_eq.symm
          exact False.elim (Set.disjoint_left.mp (hP₀_disj hij) hxi (hxij ▸ hxj))
  · intro hfan X hX hcard
    have hnone_mem : (none : Option V) ∈ apexVerts S \ X :=
      ⟨none_mem_apexVerts S, fun h => (hX h).2 rfl⟩
    refine isConnectedOn_of_reachIn hnone_mem fun w hw => ?_
    rcases w with _ | v
    · exact ReachIn.refl hnone_mem
    · have hvS : v ∈ S := some_mem_apexVerts_iff.mp hw.1
      by_cases hvD : v ∈ D
      · exact ReachIn.of_adj (apex_adj_some_none.mpr hvD) hw hnone_mem
      · exact reachIn_apex_of_hasFourFan hK hvS (hfan v hvS hvD) hw.2
          (fun h => (hX h).2 rfl) hcard

end GraphMinor.Crossing
