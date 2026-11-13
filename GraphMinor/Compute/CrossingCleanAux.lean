module

public import GraphMinor.Compute.SpecsCrossingRec
public import GraphMinor.Compute.TwoPathsSep
public import GraphMinor.Compute.Restrict
public import GraphMinor.Crossing.Statements
import GraphMinor.Crossing.CutSec3

/-!
# Auxiliary lemmas for initial cleaning and restoration (Sections 4 and 9.2)

This file provides combinatorial and Word RAM helper lemmas used by the initial cleaning
(`GraphMinor.Compute.CrossingCleanInit`) and restoration (`GraphMinor.Compute.CrossingCleanRestore`)
subprograms of `docs/crossing/crossing_extractor.tex`:

* Frame and instance preservation helpers (`KeepsBelow`, `IsInstanceAt`, `IsSetListAt`,
  `IsRecordsAt`, `IsHistoryFin`, `ContractionsLong`).
* Direct proofs of `Sec4CleanStatement`, `Sec4EdgeCountStatement`, `Sec92ValueStatement`, and
  `Lemma2ApexStatement` (from `Lemma2Statement`), together with preservation of `RootedConn`
  across valid replacements (`rootedConn_newGraph_of_lemma2`).
* Validity of discarding an off-cycle connected component (`replRecord_isValid_of_unreach`) and
  characterization of the neighbourhood of a separator component (`nbhd_eq_sep_filter`).
* Monotonicity of `K.edgeSet.ncard + 3 * S.card` and of the record-length potential
  `(s.arrs a_rec).length + 51 * S.card + 4 * K.edgeSet.ncard` across valid replacements.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

universe u

/-! ### Basic arithmetic on `instSize` and `ArrsOk` -/

theorem instSize_pos (N : ℕ) (G : SimpleGraph (Fin N)) : 0 < instSize N G := by
  unfold instSize; omega

theorem le_instSize_self (N : ℕ) (G : SimpleGraph (Fin N)) : N < instSize N G := by
  unfold instSize; omega

theorem ncard_edgeSet_lt_instSize (N : ℕ) (G : SimpleGraph (Fin N)) :
    G.edgeSet.ncard < instSize N G := by
  unfold instSize; omega

theorem ncard_edgeSet_eq_card_edgeFinset {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← SimpleGraph.coe_edgeFinset G, Set.ncard_coe_finset]

theorem totalAdjEntries_eq_two_mul_ncard {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) :
    totalAdjEntries lists = 2 * G.edgeSet.ncard := by
  classical
  rw [totalAdjEntries_eq_two_mul_card_edgeFinset h, ncard_edgeSet_eq_card_edgeFinset]

/-! ### `KeepsBelow` and `TwoPaths.Keeps` -/

theorem KeepsBelow.refl (r_base a_base : ℕ) (R A : List ℕ) (s : State) :
    KeepsBelow r_base a_base R A s s :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem KeepsBelow.trans {r_base a_base : ℕ} {R A R' A' : List ℕ} {s₀ s₁ s₂ : State}
    (h₁ : KeepsBelow r_base a_base R A s₀ s₁) (h₂ : KeepsBelow r_base a_base R' A' s₁ s₂)
    (hR : ∀ r ∈ R', r < r_base → r ∈ R) (hA : ∀ a ∈ A', a < a_base → a ∈ A) :
    KeepsBelow r_base a_base R A s₀ s₂ :=
  ⟨fun r hr hnr => by
    rw [h₂.1 r hr (fun h => hnr (hR r h hr)), h₁.1 r hr hnr],
   fun a ha hna => by
    rw [h₂.2 a ha (fun h => hna (hA a h ha)), h₁.2 a ha hna]⟩

theorem KeepsBelow.mono {r_base a_base : ℕ} {R A R' A' : List ℕ} {s₀ s₁ : State}
    (h : KeepsBelow r_base a_base R A s₀ s₁)
    (hR : ∀ r ∈ R, r < r_base → r ∈ R') (hA : ∀ a ∈ A, a < a_base → a ∈ A') :
    KeepsBelow r_base a_base R' A' s₀ s₁ :=
  ⟨fun r hr hnr => h.1 r hr (fun hm => hnr (hR r hm hr)),
   fun a ha hna => h.2 a ha (fun hm => hna (hA a hm ha))⟩

theorem KeepsBelow.setReg_ge {r_base a_base : ℕ} {R A : List ℕ} {s₀ s : State}
    (h : KeepsBelow r_base a_base R A s₀ s) {r : Reg} (hr : r_base ≤ r) (v : ℕ) :
    KeepsBelow r_base a_base R A s₀ (s.setReg r v) :=
  ⟨fun r' hr' hnr' => by
    have hne : r' ≠ r := by omega
    rw [State.setReg_regs_ne _ _ hne]
    exact h.1 r' hr' hnr',
   fun a ha hna => h.2 a ha hna⟩

theorem KeepsBelow.setArr_ge {r_base a_base : ℕ} {R A : List ℕ} {s₀ s : State}
    (h : KeepsBelow r_base a_base R A s₀ s) {a : Arr} (ha : a_base ≤ a) (l : List ℕ) :
    KeepsBelow r_base a_base R A s₀ (s.setArr a l) :=
  ⟨fun r hr hnr => h.1 r hr hnr,
   fun a' ha' hna' => by
    have hne : a' ≠ a := by omega
    rw [State.setArr_arrs_ne _ _ hne]
    exact h.2 a' ha' hna'⟩

theorem KeepsBelow.writeArr_ge {r_base a_base : ℕ} {R A : List ℕ} {s₀ s : State}
    (h : KeepsBelow r_base a_base R A s₀ s) {a : Arr} (ha : a_base ≤ a) (i v : ℕ) :
    KeepsBelow r_base a_base R A s₀ (s.writeArr a i v) :=
  h.setArr_ge ha _

theorem KeepsBelow.setArr_mem {r_base a_base : ℕ} {R A : List ℕ} {s₀ s : State}
    (h : KeepsBelow r_base a_base R A s₀ s) {a : Arr} (ha : a ∈ A) (l : List ℕ) :
    KeepsBelow r_base a_base R A s₀ (s.setArr a l) :=
  ⟨fun r hr hnr => h.1 r hr hnr,
   fun a' ha' hna' => by
    have hne : a' ≠ a := fun e => hna' (e ▸ ha)
    rw [State.setArr_arrs_ne _ _ hne]
    exact h.2 a' ha' hna'⟩

theorem KeepsBelow.writeArr_mem {r_base a_base : ℕ} {R A : List ℕ} {s₀ s : State}
    (h : KeepsBelow r_base a_base R A s₀ s) {a : Arr} (ha : a ∈ A) (i v : ℕ) :
    KeepsBelow r_base a_base R A s₀ (s.writeArr a i v) :=
  h.setArr_mem ha _

theorem KeepsBelow.of_keeps {r_base a_base : ℕ} {R A R₀ A₀ : List ℕ} {s₀ s₁ : State}
    (h : TwoPaths.Keeps R A s₀ s₁)
    (hR : ∀ r ∈ R, r_base ≤ r ∨ r ∈ R₀) (hA : ∀ a ∈ A, a_base ≤ a ∨ a ∈ A₀) :
    KeepsBelow r_base a_base R₀ A₀ s₀ s₁ :=
  ⟨fun r hr hnr => h.1 r (fun hm => by
    rcases hR r hm with hge | hmem
    · omega
    · exact hnr hmem),
   fun a ha hna => h.2 a (fun hm => by
    rcases hA a hm with hge | hmem
    · omega
    · exact hna hmem)⟩

/-! ### `IsInstanceAt`, `IsSetListAt`, and `IsRecordsAt` preservation -/

theorem IsInstanceAt.of_arrs_eq_five {N : ℕ} {a : InstArrs} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {s s' : State}
    (h : IsInstanceAt a G S D s)
    (halive : s'.arrs a.alive = s.arrs a.alive)
    (hst : s'.arrs a.st = s.arrs a.st)
    (hen : s'.arrs a.en = s.arrs a.en)
    (hent : s'.arrs a.ent = s.arrs a.ent)
    (hcyc : s'.arrs a.cyc = s.arrs a.cyc) :
    IsInstanceAt a G S D s' := by
  obtain ⟨hsupp, ha, ⟨lists, hadj⟩, hlen, hc⟩ := h
  exact ⟨hsupp, halive.trans ha, ⟨lists, hadj.of_arrs_eq hst hen hent⟩,
    by rw [hent, hlen], hcyc.trans hc⟩

theorem IsInstanceAt.of_keeps_disjoint {N : ℕ} {a : InstArrs} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {s s' : State}
    (h : IsInstanceAt a G S D s)
    (heq : ∀ x ∈ a.list, s'.arrs x = s.arrs x) :
    IsInstanceAt a G S D s' :=
  h.of_arrs_eq_five
    (heq a.alive (by simp [InstArrs.list]))
    (heq a.st (by simp [InstArrs.list]))
    (heq a.en (by simp [InstArrs.list]))
    (heq a.ent (by simp [InstArrs.list]))
    (heq a.cyc (by simp [InstArrs.list]))

theorem IsInstanceAt.length_alive {N : ℕ} {a : InstArrs} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {s : State}
    (h : IsInstanceAt a G S D s) : (s.arrs a.alive).length = N := by
  rw [h.2.1, List.length_ofFn]

theorem IsInstanceAt.length_cyc {N : ℕ} {a : InstArrs} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {s : State}
    (h : IsInstanceAt a G S D s) : (s.arrs a.cyc).length = D.length := by
  rw [h.2.2.2.2, List.length_map]

theorem IsSetListAt.of_arrs_eq {N : ℕ} {x : ℕ} {X : Set (Fin N)} {s s' : State}
    (h : IsSetListAt x X s) (heq : s'.arrs x = s.arrs x) : IsSetListAt x X s' := by
  obtain ⟨l, hnd, hmem, harr⟩ := h
  exact ⟨l, hnd, hmem, heq.trans harr⟩

theorem IsRecordsAt.of_arrs_eq {N : ℕ} {x : ℕ} {recs : List (CrossRecord (Fin N))} {s s' : State}
    (h : IsRecordsAt x recs s) (heq : s'.arrs x = s.arrs x) : IsRecordsAt x recs s' := by
  obtain ⟨ls, hrel, harr⟩ := h
  exact ⟨ls, hrel, heq.trans harr⟩

theorem IsRecBufAt.of_arrs_regs_eq {N : ℕ} {x r : ℕ} {recs : List (CrossRecord (Fin N))}
    {k : ℕ} {s s' : State}
    (h : IsRecBufAt x r recs k s) (harr : s'.arrs x = s.arrs x) (hreg : s'.regs r = s.regs r) :
    IsRecBufAt x r recs k s' := by
  obtain ⟨ls, hrel, ha, hr⟩ := h
  exact ⟨ls, hrel, harr.trans ha, hreg.trans hr⟩

theorem IsRecBufAt.of_keepsBelow {N : ℕ} {x r r_base a_base : ℕ} {R A : List ℕ}
    {recs : List (CrossRecord (Fin N))} {k : ℕ} {s s' : State}
    (h : IsRecBufAt x r recs k s) (hk : KeepsBelow r_base a_base R A s s')
    (hr : r < r_base) (hrR : r ∉ R) (hx : x < a_base) (hxA : x ∉ A) :
    IsRecBufAt x r recs k s' :=
  h.of_arrs_regs_eq (hk.2 x hx hxA) (hk.1 r hr hrR)

theorem IsHistory.trans_aux {V : Type*} [DecidableEq V] :
    ∀ {recs₁ recs₂ : List (CrossRecord V)} {st₁ st₂ st₃ : SimpleGraph V × Set V × List V},
      IsHistory st₁ recs₁ st₂ → IsHistory st₂ recs₂ st₃ → IsHistory st₁ (recs₁ ++ recs₂) st₃
  | [], _, _, _, _, h₁, h₂ => by subst h₁; exact h₂
  | CrossRecord.repl r :: rs, _, (G, S, D), _, _, ⟨hg, hv, hval, hrest⟩, h₂ =>
      ⟨hg, hv, hval, IsHistory.trans_aux hrest h₂⟩
  | CrossRecord.contr r :: rs, _, (G, S, D), _, _, ⟨hg, hv, hc, hval, hrest⟩, h₂ =>
      ⟨hg, hv, hc, hval, IsHistory.trans_aux hrest h₂⟩
  | CrossRecord.del G' S' :: rs, _, (G, S, D), _, _, ⟨h1, h2, h3, h4, h5, hrest⟩, h₂ =>
      ⟨h1, h2, h3, h4, h5, IsHistory.trans_aux hrest h₂⟩

theorem IsHistoryFin.refl {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) : IsHistoryFin G S D [] G S D :=
  rfl

theorem IsHistoryFin.trans {N : ℕ} {G₁ G₂ G₃ : SimpleGraph (Fin N)}
    {S₁ S₂ S₃ : Finset (Fin N)} {D₁ D₂ D₃ : List (Fin N)}
    {recs₁ recs₂ : List (CrossRecord (Fin N))}
    (h₁ : IsHistoryFin G₁ S₁ D₁ recs₁ G₂ S₂ D₂)
    (h₂ : IsHistoryFin G₂ S₂ D₂ recs₂ G₃ S₃ D₃) :
    IsHistoryFin G₁ S₁ D₁ (recs₁ ++ recs₂) G₃ S₃ D₃ :=
  IsHistory.trans_aux h₁ h₂

theorem IsHistoryFin.snoc_repl {N : ℕ} {G₁ G₂ : SimpleGraph (Fin N)}
    {S₁ S₂ S₃ : Finset (Fin N)} {D : List (Fin N)}
    {recs : List (CrossRecord (Fin N))} {r : ReplRecord (Fin N)}
    (h₁ : IsHistoryFin G₁ S₁ D recs G₂ S₂ D)
    (hg : r.graph = G₂) (hv : r.verts = (S₂ : Set (Fin N))) (hval : r.IsValid D)
    (hS₃ : (S₃ : Set (Fin N)) = r.newVerts) :
    IsHistoryFin G₁ S₁ D (recs ++ [CrossRecord.repl r]) r.newGraph S₃ D := by
  refine h₁.trans ⟨hg, hv, hval, ?_⟩
  simp [IsHistory, hS₃]

theorem ContractionsLong.nil {N : ℕ} : ContractionsLong ([] : List (CrossRecord (Fin N))) := by
  intro r hr; simp at hr

theorem ContractionsLong.append_repl {N : ℕ} {recs : List (CrossRecord (Fin N))}
    {r : ReplRecord (Fin N)} (h : ContractionsLong recs) :
    ContractionsLong (recs ++ [CrossRecord.repl r]) := by
  intro c hc
  rw [List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | hc
  · exact h c hc
  · cases hc

/-! ### Cycle and replacement properties -/

theorem isCycleList_mem_supported {V : Type*} {G : SimpleGraph V} {S : Set V} {D : List V}
    (hsupp : HP25.IsSupportedOn G S) (hD : HP25.IsCycleList G D) :
    ∀ d ∈ D, d ∈ S := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  have hlen_rot : (D.rotate 1).length = D.length := List.length_rotate D 1
  have hlen_zip : (D.zip (D.rotate 1)).length = D.length := by simp
  have hmem_zip : (D[i], (D.rotate 1)[i]' (by omega)) ∈ D.zip (D.rotate 1) := by
    have hget : (D.zip (D.rotate 1))[i]' (by omega) = (D[i], (D.rotate 1)[i]' (by omega)) :=
      List.getElem_zip
    rw [← hget]
    exact List.getElem_mem (by omega)
  exact hsupp (hD.2.2 _ hmem_zip)

theorem isCycleList_length_le_fin {N : ℕ} {G : SimpleGraph (Fin N)} {D : List (Fin N)}
    (hD : HP25.IsCycleList G D) : D.length ≤ N := by
  have := hD.2.1.length_le_card
  simpa using this

theorem ReplRecord.isSupportedOn_newGraph {V : Type*} {r : ReplRecord V}
    (hsupp : HP25.IsSupportedOn r.graph r.verts)
    (hbd : (r.boundary : Set V) ⊆ r.verts \ r.deleted) :
    HP25.IsSupportedOn r.newGraph r.newVerts := by
  intro a b hadj
  rcases hadj with ⟨hadj_old, ha, _⟩ | ⟨ha_bd, _, _⟩
  · exact ⟨hsupp hadj_old, ha⟩
  · exact hbd ha_bd

theorem ReplRecord.isCycleList_newGraph {V : Type*} {r : ReplRecord V} {D : List V}
    (hD : HP25.IsCycleList r.graph D) (hval : r.IsValid D) :
    HP25.IsCycleList r.newGraph D := by
  obtain ⟨hlen, hnd, hzip⟩ := hD
  refine ⟨hlen, hnd, fun p hp => ?_⟩
  have hp1 : p.1 ∈ D := List.of_mem_zip hp |>.1
  have hp2 : p.2 ∈ D := by
    have := (List.of_mem_zip hp).2
    rwa [List.mem_rotate] at this
  exact Or.inl ⟨hzip p hp, fun h => hval.2.1 p.1 h hp1, fun h => hval.2.1 p.2 h hp2⟩

/-! ### `ReachIn` and `IsConnectedOn` helpers -/

theorem ReachIn.refl {W : Type*} {G : SimpleGraph W} {T : Set W} {a : W} (ha : a ∈ T) :
    ReachIn G T a a :=
  ⟨.nil, fun y hy => by simp at hy; subst hy; exact ha⟩

theorem ReachIn.symm {W : Type*} {G : SimpleGraph W} {T : Set W} {a b : W}
    (h : ReachIn G T a b) : ReachIn G T b a := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, fun y hy => hp y (by simpa using hy)⟩

theorem ReachIn.trans {W : Type*} {G : SimpleGraph W} {T : Set W} {a b c : W}
    (h₁ : ReachIn G T a b) (h₂ : ReachIn G T b c) : ReachIn G T a c := by
  obtain ⟨p₁, hp₁⟩ := h₁
  obtain ⟨p₂, hp₂⟩ := h₂
  refine ⟨p₁.append p₂, fun y hy => ?_⟩
  rcases List.mem_append.mp (Walk.support_append p₁ p₂ ▸ hy) with h | h
  · exact hp₁ y h
  · exact hp₂ y (List.mem_of_mem_tail h)

theorem ReachIn.mono {W : Type*} {G : SimpleGraph W} {T₁ T₂ : Set W} {a b : W}
    (h : ReachIn G T₁ a b) (hsub : T₁ ⊆ T₂) : ReachIn G T₂ a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun y hy => hsub (hp y hy)⟩

theorem ReachIn.step_right {W : Type*} {G : SimpleGraph W} {T : Set W} {a b c : W}
    (h : ReachIn G T a b) (hadj : G.Adj b c) (hc : c ∈ T) : ReachIn G T a c :=
  ReachIn.trans h ⟨.cons hadj .nil, fun y hy => by
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hy
    rcases hy with rfl | rfl
    · obtain ⟨p, hp⟩ := h; exact hp _ p.end_mem_support
    · exact hc⟩

/-- Every vertex on the support of a walk inside `T` starting at `u` is reachable from `u`
inside `T`. -/
theorem reachIn_of_mem_walk_support {W : Type*} {G : SimpleGraph W} {T : Set W}
    {u w : W} (p : G.Walk u w) (hp : ∀ z ∈ p.support, z ∈ T) :
    ∀ y ∈ p.support, ReachIn G T u y := by
  induction p with
  | nil =>
    intro y hy
    simp only [Walk.support_nil, List.mem_singleton] at hy
    subst hy
    exact ReachIn.refl (hp _ (by simp))
  | cons hab rest ih =>
    intro y hy
    simp only [Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ReachIn.refl (hp _ (by simp))
    · obtain ⟨q, hq⟩ := ih (fun z hz => hp z (by simp [hz])) y hy
      refine ⟨.cons hab q, fun z hz => ?_⟩
      simp only [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hp _ (by simp)
      · exact hq z hz

/-- Characterization of walks from `some a` to `none` in `apex G D` avoiding `some '' T`. -/
theorem reachIn_apex_to_cycle {V : Type*} {G : SimpleGraph V} {S : Set V} {D : List V}
    {T : Set V} {u w : Option V} (p : (apex G D).Walk u w)
    (hsupp : ∀ y ∈ p.support, y ∈ apexVerts S \ (some '' T)) :
    ∀ (a : V), u = some a → w = none →
      ∃ d ∈ D, d ∉ T ∧ ReachIn G (S \ T) a d := by
  induction p with
  | nil =>
    intro a hu hw
    cases hu.symm.trans hw
  | @cons u v w hadj rest ih =>
    intro a hu hw
    subst hu; subst hw
    have ha_mem : some a ∈ apexVerts S \ (some '' T) := hsupp (some a) (by simp)
    have haS : a ∈ S \ T := by
      rcases ha_mem with ⟨ha1, ha2⟩
      simp only [apexVerts, Set.mem_insert_iff, Set.mem_image, reduceCtorEq, false_or,
        Option.some.injEq, exists_eq_right] at ha1 ha2
      exact ⟨ha1, ha2⟩
    cases v with
    | none =>
      have hd : a ∈ D := hadj
      exact ⟨a, hd, haS.2, ReachIn.refl haS⟩
    | some b =>
      have hab : G.Adj a b := hadj
      obtain ⟨d, hdD, hdT, p', hp'⟩ :=
        ih (fun y hy => hsupp y (by simp [hy])) b rfl rfl
      refine ⟨d, hdD, hdT, ⟨.cons hab p', fun y hy => ?_⟩⟩
      simp only [Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact haS
      · exact hp' y hy

theorem reachIn_apex_of_cycle {V : Type*} {G : SimpleGraph V} {S : Set V} {D : List V}
    {T : Set V} :
    ∀ {a d : V} (p : G.Walk a d),
      (∀ y ∈ p.support, y ∈ S \ T) → d ∈ D →
      ReachIn (apex G D) (apexVerts S \ (some '' T)) (some a) none
  | a, _, .nil, hp, hd => by
    have ha : a ∈ S \ T := hp a (by simp)
    have hadj : (apex G D).Adj (some a) none := hd
    refine ⟨.cons hadj .nil, fun y hy => ?_⟩
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨Or.inr ⟨a, ha.1, rfl⟩, fun ⟨z, hz, hzeq⟩ => ha.2 (Option.some.inj hzeq ▸ hz)⟩
    · exact ⟨Or.inl rfl, by simp⟩
  | a, d, @Walk.cons _ _ _ b _ hab rest, hp, hd => by
    have ha : a ∈ S \ T := hp a (by simp)
    obtain ⟨p', hp'⟩ := reachIn_apex_of_cycle rest (fun y hy => hp y (by simp [hy])) hd
    have hadj : (apex G D).Adj (some a) (some b) := hab
    refine ⟨.cons hadj p', fun y hy => ?_⟩
    simp only [Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨Or.inr ⟨a, ha.1, rfl⟩, fun ⟨z, hz, hzeq⟩ => ha.2 (Option.some.inj hzeq ▸ hz)⟩
    · exact hp' y hy

/-! ### Proofs of `Lemma2ApexStatement`, `RootedConn` preservation, `Sec4CleanStatement`,
`Sec4EdgeCountStatement`, and `Sec92ValueStatement` -/

/-- **Lemma 2 for the apex graph** follows from `Lemma2Statement`. -/
theorem lemma2ApexStatement_of : Lemma2ApexStatement.{u} := by
  intro V r D v k hsupp hD hval hv hU X hX hXcard
  let T : Set V := {z | some z ∈ X}
  have hT_sub : T ⊆ r.newVerts := by
    intro z hz
    have hmem := (hX hz).1
    simp only [apexVerts, Set.mem_insert_iff, Set.mem_image, reduceCtorEq, false_or,
      Option.some.injEq, exists_eq_right] at hmem
    exact hmem
  have hX_old : (X : Set (Option V)) ⊆ apexVerts r.verts \ {some v, none} := by
    intro x hx
    rcases hX hx with ⟨hx1, hx2⟩
    refine ⟨?_, hx2⟩
    rcases hx1 with rfl | ⟨z, hz, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, hz.1, rfl⟩
  obtain ⟨p, hp⟩ := hU X hX_old hXcard
  have hp' : ∀ y ∈ p.support, y ∈ apexVerts r.verts \ (some '' T) := by
    intro y hy
    rcases hp y hy with ⟨hy1, hy2⟩
    refine ⟨hy1, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact hy2 hz
  obtain ⟨d, hdD, hdT, hreach_old⟩ := reachIn_apex_to_cycle p hp' v rfl rfl
  have hd_new : d ∈ r.newVerts :=
    ⟨isCycleList_mem_supported hsupp hD d hdD, fun h => hval.2.1 d h hdD⟩
  obtain ⟨q, hq⟩ := lemma2_proved.{u} r D T v d hsupp hval hT_sub hv hd_new hreach_old
  obtain ⟨q_apex, hq_apex⟩ := reachIn_apex_of_cycle q hq hdD
  refine ⟨q_apex, fun y hy => ?_⟩
  rcases hq_apex y hy with ⟨hy1, hy2⟩
  refine ⟨hy1, fun hyX => ?_⟩
  cases y with
  | none => exact (hX hyX).2 (Or.inr rfl)
  | some z => exact hy2 ⟨z, hyX, rfl⟩

/-- `Lemma2Statement` implies that valid replacements preserve `RootedConn` on
`apexVerts S \ (some '' F)` for any retained vertex subset `F ⊆ r.newVerts`. -/
theorem rootedConn_newGraph_of_lemma2
    {V : Type u} {r : ReplRecord V} {D : List V} {F : Set V} {k : ℕ}
    (hsupp : HP25.IsSupportedOn r.graph r.verts) (hD : HP25.IsCycleList r.graph D)
    (hval : r.IsValid D) (hF : F ⊆ r.newVerts)
    (hrc : RootedConn (apex r.graph D) (apexVerts r.verts \ (some '' F)) none k) :
    RootedConn (apex r.newGraph D) (apexVerts r.newVerts \ (some '' F)) none k := by
  intro X hX hXcard
  let T : Set V := F ∪ {z | some z ∈ X}
  have hT_sub : T ⊆ r.newVerts := by
    rintro z (hzF | hzX)
    · exact hF hzF
    · have hmem := (hX hzX).1.1
      simp only [apexVerts, Set.mem_insert_iff, Set.mem_image, reduceCtorEq, false_or,
        Option.some.injEq, exists_eq_right] at hmem
      exact hmem
  have hnone_not_X : none ∉ (X : Set (Option V)) := fun h => (hX h).2 rfl
  have hset_eq : ∀ S' : Set V,
      (apexVerts S' \ (some '' F)) \ (X : Set (Option V)) = apexVerts S' \ (some '' T) := by
    intro S'
    ext y
    cases y with
    | none =>
      simp [apexVerts, hnone_not_X]
    | some z =>
      simp [apexVerts, T, or_iff_not_imp_left]
      tauto
  have hX_old : (X : Set (Option V)) ⊆ (apexVerts r.verts \ (some '' F)) \ {none} := by
    intro y hy
    rcases hX hy with ⟨⟨hy1, hyF⟩, hyn⟩
    refine ⟨⟨?_, hyF⟩, hyn⟩
    rcases hy1 with rfl | ⟨z, hz, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, hz.1, rfl⟩
  have hconn_old := hrc X hX_old hXcard
  rw [hset_eq] at hconn_old ⊢
  have hnone_mem : (none : Option V) ∈ apexVerts r.newVerts \ (some '' T) :=
    ⟨Or.inl rfl, by simp⟩
  have hreach_none : ∀ y ∈ apexVerts r.newVerts \ (some '' T),
      ReachIn (apex r.newGraph D) (apexVerts r.newVerts \ (some '' T)) y none := by
    intro y hy
    cases y with
    | none => exact ReachIn.refl hnone_mem
    | some a =>
      have ha_new : a ∈ r.newVerts := by
        rcases hy.1 with h | ⟨z, hz, hzeq⟩
        · cases h
        · exact Option.some.inj hzeq ▸ hz
      have ha_old_mem : (some a : Option V) ∈ apexVerts r.verts \ (some '' T) :=
        ⟨Or.inr ⟨a, ha_new.1, rfl⟩, hy.2⟩
      have hnone_old_mem : (none : Option V) ∈ apexVerts r.verts \ (some '' T) :=
        ⟨Or.inl rfl, by simp⟩
      obtain ⟨p, hp⟩ := hconn_old.2 (some a) ha_old_mem none hnone_old_mem
      obtain ⟨d, hdD, hdT, hreach_old⟩ := reachIn_apex_to_cycle p hp a rfl rfl
      have hd_new : d ∈ r.newVerts :=
        ⟨isCycleList_mem_supported hsupp hD d hdD, fun h => hval.2.1 d h hdD⟩
      obtain ⟨q, hq⟩ := lemma2_proved.{u} r D T a d hsupp hval hT_sub ha_new hd_new hreach_old
      exact reachIn_apex_of_cycle q hq hdD
  refine ⟨⟨none, hnone_mem⟩, fun y₁ hy₁ y₂ hy₂ => ?_⟩
  exact ReachIn.trans (hreach_none y₁ hy₁) (ReachIn.symm (hreach_none y₂ hy₂))

/-- **Section 4 clean statement**: when no off-cycle vertex of `S` can be separated from `x`
by at most 3 vertices, the instance is clean. -/
theorem sec4CleanStatement_holds : Sec4CleanStatement.{u} := by
  intro V K S D _ _ hU X hX hXcard
  have hnone_mem : (none : Option V) ∈ apexVerts S \ (X : Set (Option V)) :=
    ⟨Or.inl rfl, fun h => (hX h).2 rfl⟩
  have hreach_none : ∀ y ∈ apexVerts S \ (X : Set (Option V)),
      ReachIn (apex K D) (apexVerts S \ (X : Set (Option V))) y none := by
    intro y hy
    cases y with
    | none => exact ReachIn.refl hnone_mem
    | some v =>
      have hvS : v ∈ S := by
        rcases hy.1 with h | ⟨z, hz, hzeq⟩
        · cases h
        · exact Option.some.inj hzeq ▸ hz
      by_cases hvD : v ∈ D
      · have hadj : (apex K D).Adj (some v) none := hvD
        refine ⟨.cons hadj .nil, fun z hz => ?_⟩
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hz
        rcases hz with rfl | rfl
        · exact hy
        · exact hnone_mem
      · have hX_sub : (X : Set (Option V)) ⊆ apexVerts S \ {some v, none} := by
          intro z hz
          refine ⟨(hX hz).1, ?_⟩
          rintro (rfl | rfl)
          · exact hy.2 hz
          · exact (hX hz).2 rfl
        exact hU v hvS hvD X hX_sub (by omega)
  refine ⟨⟨none, hnone_mem⟩, fun y₁ hy₁ y₂ hy₂ => ?_⟩
  exact ReachIn.trans (hreach_none y₁ hy₁) (ReachIn.symm (hreach_none y₂ hy₂))

/-- Any finset `B` of cardinality at most `3` spans at most `3` unordered pairs of distinct
elements, and this set of pairs is finite. -/
theorem ncard_sym2_offDiag_le_three {V : Type*} (B : Finset V) (hB : B.card ≤ 3) :
    {e : Sym2 V | ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ s(a, b) = e}.ncard ≤ 3 ∧
      {e : Sym2 V | ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ s(a, b) = e}.Finite := by
  classical
  set L := B.toList
  have hL_len : L.length ≤ 3 := by simpa [L] using hB
  have hmem : ∀ x, x ∈ B ↔ x ∈ L := fun x => (Finset.mem_toList).symm
  set S_pairs : Set (Sym2 V) := {e : Sym2 V | ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ s(a, b) = e} with hS_def
  rcases hL : L with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · have hemp : S_pairs = ∅ := by
      ext e; simp [S_pairs, hmem, hL]
    rw [hemp]; exact ⟨by simp, Set.finite_empty⟩
  · have hemp : S_pairs = ∅ := by
      ext e
      simp only [S_pairs, hmem, hL, List.mem_singleton, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_exists, not_and]
      rintro a rfl b rfl hne _
      exact hne rfl
    rw [hemp]; exact ⟨by simp, Set.finite_empty⟩
  · have hsub : S_pairs ⊆ (({s(x, y)} : Finset (Sym2 V)) : Set (Sym2 V)) := by
      rintro e ⟨a, ha, b, hb, hne, rfl⟩
      rw [hmem, hL] at ha hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      simp only [Finset.coe_singleton, Set.mem_singleton_iff]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hne rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hne rfl).elim
    refine ⟨?_, (Finset.finite_toSet _).subset hsub⟩
    calc S_pairs.ncard
      _ ≤ (({s(x, y)} : Finset (Sym2 V)) : Set (Sym2 V)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({s(x, y)} : Finset (Sym2 V)).card := Set.ncard_coe_finset _
      _ ≤ 3 := by simp
  · have hrest : rest = [] := by
      rw [hL] at hL_len
      simp only [List.length_cons] at hL_len
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    have hsub : S_pairs ⊆ (({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V)) : Set (Sym2 V)) := by
      rintro e ⟨a, ha, b, hb, hne, rfl⟩
      rw [hmem, hL] at ha hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact (hne rfl).elim
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl Sym2.eq_swap
      · exact (hne rfl).elim
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl Sym2.eq_swap)
      · exact Or.inr (Or.inr Sym2.eq_swap)
      · exact (hne rfl).elim
    have hcard : ({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V)).card ≤ 3 :=
      le_trans (Finset.card_insert_le _ _)
        (Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _) (by simp)) 1)
    refine ⟨?_, (Finset.finite_toSet _).subset hsub⟩
    calc S_pairs.ncard
      _ ≤ (({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V)) : Set (Sym2 V)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V)).card := Set.ncard_coe_finset _
      _ ≤ 3 := hcard

/-- **Section 4 edge-count statement**: every valid replacement deletes at least one vertex and
adds at most three edges. -/
theorem sec4EdgeCountStatement_holds : Sec4EdgeCountStatement.{u} := by
  intro V r D hval
  obtain ⟨_, _, hcard, _, _, hrep⟩ := hval
  obtain ⟨z, hz⟩ := hrep.2.1.1
  have hsub : r.newGraph.edgeSet \ r.graph.edgeSet ⊆
      {e : Sym2 V | ∃ a ∈ r.boundary, ∃ b ∈ r.boundary, a ≠ b ∧ s(a, b) = e} := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rcases he with ⟨hnew, hold⟩
      simp only [SimpleGraph.mem_edgeSet] at hnew hold
      rcases hnew with ⟨hadj, _, _⟩ | ⟨ha, hb, hne⟩
      · exact (hold hadj).elim
      · exact ⟨a, ha, b, hb, hne, rfl⟩
  obtain ⟨hle3, hfin⟩ := ncard_sym2_offDiag_le_three r.boundary hcard
  exact ⟨⟨z, hrep.1 hz⟩, le_trans (Set.ncard_le_ncard hsub hfin) hle3, hfin.subset hsub⟩

/-- **Section 9.2 value statement**: in a graph `B` satisfying `RootedConn B T x 2`, any vertex
`z ∈ T` not adjacent to `x` that is separable from `x` by at most `2` vertices has a minimum
separator of size `2`. -/
theorem sec92ValueStatement_holds : Sec92ValueStatement.{u} := by
  classical
  intro W B T x z _ hx hz _ _ hrc hnotU
  unfold IsUnseparable at hnotU
  push Not at hnotU
  obtain ⟨X, hX_sub, hX_card, hnot_reach⟩ := hnotU
  have hsep : IsSeparator B T z x X := ⟨hX_sub, hnot_reach⟩
  have hno_lt2 : ∀ X' : Finset W, IsSeparator B T z x X' → 2 ≤ X'.card := by
    intro X' hsep'
    by_contra hlt
    have hX'_sub : (X' : Set W) ⊆ T \ {x} := fun y hy =>
      ⟨(hsep'.1 hy).1, fun h => (hsep'.1 hy).2 (Or.inr h)⟩
    have hconn := hrc X' hX'_sub (by omega)
    have hz_mem : z ∈ T \ (X' : Set W) := ⟨hz, fun h => (hsep'.1 h).2 (Or.inl rfl)⟩
    have hx_mem : x ∈ T \ (X' : Set W) := ⟨hx, fun h => (hsep'.1 h).2 (Or.inr rfl)⟩
    exact hsep'.2 (hconn.2 z hz_mem x hx_mem)
  have hge2 := hno_lt2 X hsep
  exact ⟨X, ⟨hsep, fun X' hsep' => by have := hno_lt2 X' hsep'; omega⟩, by omega⟩

/-! ### Phase 1 unreachability replacement and Phase 2 neighbourhood characterization -/

/-- When `v ∈ S` cannot reach any vertex of `D` inside `S`, its reachable component
`A = {y | ReachIn K S v y}` in `K` has empty neighbourhood and defines a valid replacement record
with empty boundary. -/
theorem replRecord_isValid_of_unreach {V : Type*} {K : SimpleGraph V} {S : Set V} {D : List V}
    {v : V} (hsupp : HP25.IsSupportedOn K S) (hv : v ∈ S)
    (hunreach : ∀ d ∈ D, ¬ ReachIn K S d v) :
    let A : Set V := {y | ReachIn K S v y}
    ({ graph := K, verts := S, deleted := A, boundary := ∅, rep := A } : ReplRecord V).IsValid D := by
  intro A
  have hvA : v ∈ A := ReachIn.refl hv
  have hA_sub : A ⊆ S := by
    intro y hy
    obtain ⟨p, hp⟩ := hy
    exact hp y p.end_mem_support
  have hA_closed : ∀ a ∈ A, ∀ b, K.Adj a b → b ∈ A := by
    intro a ha b hadj
    exact ReachIn.step_right ha hadj (hsupp hadj.symm)
  have hA_conn : IsConnectedOn K A := by
    refine ⟨⟨v, hvA⟩, fun a ha b hb => ?_⟩
    have hva : ReachIn K A v a := by
      obtain ⟨p, hp⟩ := ha
      exact ⟨p, fun y hy => reachIn_of_mem_walk_support p hp y hy⟩
    have hvb : ReachIn K A v b := by
      obtain ⟨p, hp⟩ := hb
      exact ⟨p, fun y hy => reachIn_of_mem_walk_support p hp y hy⟩
    exact ReachIn.trans (ReachIn.symm hva) hvb
  refine ⟨hA_sub, ?_, by simp, by simp, ?_, ⟨subset_rfl, hA_conn, fun a ha b _ hadj => hA_closed a ha b hadj⟩⟩
  · intro a ha hdD
    exact hunreach a hdD (ReachIn.symm ha)
  · intro C hC
    ext y
    simp only [Finset.coe_empty, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hyC, a, haC, hadj⟩
    exact hyC (hC.2.2 a haC y (hA_closed a (hC.1 haC) y hadj) hadj)

/-- For `A = {y | ReachIn K (S \ S_sep) v y}` with `K` supported on `S`, the neighbourhood
`nbhd K A` is the set of vertices in `S_sep` that have a neighbour in `A`. -/
theorem nbhd_eq_sep_filter {V : Type*} {K : SimpleGraph V} {S S_sep : Set V} {v : V}
    (hsupp : HP25.IsSupportedOn K S) :
    let A : Set V := {y | ReachIn K (S \ S_sep) v y}
    nbhd K A = {y | y ∈ S_sep ∧ ∃ u ∈ A, K.Adj y u} := by
  intro A
  have hA_sub : A ⊆ S \ S_sep := by
    intro y hy
    obtain ⟨p, hp⟩ := hy
    exact hp y p.end_mem_support
  ext y
  simp only [nbhd, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyA, u, huA, hadj⟩
    have hyS : y ∈ S := hsupp hadj.symm
    have hy_sep : y ∈ S_sep := by
      by_contra hnot
      exact hyA (ReachIn.step_right huA hadj ⟨hyS, hnot⟩)
    exact ⟨hy_sep, u, huA, hadj.symm⟩
  · rintro ⟨hy_sep, u, huA, hadj⟩
    refine ⟨fun hyA => (hA_sub hyA).2 hy_sep, u, huA, hadj.symm⟩

/-! ### Edge count and record encoding length bounds -/

/-- For a valid replacement `r` on `Fin N`, the new edge count plus the deleted edge count is at
most the old edge count plus `3`. -/
theorem ncard_newGraph_add_sdiff_le {N : ℕ} {r : ReplRecord (Fin N)} {D : List (Fin N)}
    (hval : r.IsValid D) :
    r.newGraph.edgeSet.ncard + (r.graph.edgeSet \ r.newGraph.edgeSet).ncard ≤
      r.graph.edgeSet.ncard + 3 := by
  have hadd := (sec4EdgeCountStatement_holds r D hval).2.1
  have h1 : (r.newGraph.edgeSet ∩ r.graph.edgeSet).ncard +
      (r.graph.edgeSet \ r.newGraph.edgeSet).ncard = r.graph.edgeSet.ncard := by
    rw [Set.inter_comm, Set.ncard_inter_add_ncard_sdiff_eq_ncard r.graph.edgeSet r.newGraph.edgeSet
      (Set.toFinite _)]
  have h2 : (r.newGraph.edgeSet \ r.graph.edgeSet).ncard +
      (r.newGraph.edgeSet ∩ r.graph.edgeSet).ncard = r.newGraph.edgeSet.ncard := by
    rw [add_comm, Set.ncard_inter_add_ncard_sdiff_eq_ncard r.newGraph.edgeSet r.graph.edgeSet
      (Set.toFinite _)]
  omega

/-- Each valid replacement on `(K, S)` decreases `S.card` by `r.deleted.ncard ≥ 1` and keeps
`K'.edgeSet.ncard + 3 * S'.card ≤ K.edgeSet.ncard + 3 * S.card`. -/
theorem edge_pot_step {N : ℕ} {G : SimpleGraph (Fin N)} {S S' : Finset (Fin N)}
    {D : List (Fin N)} {r : ReplRecord (Fin N)}
    (hg : r.graph = G) (hv : r.verts = (S : Set (Fin N))) (hval : r.IsValid D)
    (hS' : (S' : Set (Fin N)) = r.newVerts) :
    S'.card + r.deleted.ncard = S.card ∧
      1 ≤ r.deleted.ncard ∧
      r.newGraph.edgeSet.ncard + 3 * S'.card ≤ G.edgeSet.ncard + 3 * S.card := by
  subst hg
  have hne := (sec4EdgeCountStatement_holds r D hval).1
  have hpos : 1 ≤ r.deleted.ncard :=
    Nat.succ_le_of_lt ((Set.ncard_pos (Set.toFinite _)).mpr hne)
  have hcard : S'.card + r.deleted.ncard = S.card := by
    rw [← Set.ncard_coe_finset S', ← Set.ncard_coe_finset S, hS', ReplRecord.newVerts, ← hv]
    exact Set.ncard_sdiff_add_ncard_of_subset hval.1 (Set.toFinite _)
  have hedge := ncard_newGraph_add_sdiff_le hval
  refine ⟨hcard, hpos, by omega⟩

/-- Length of `withLength body`. -/
@[simp]
theorem length_withLength (body : List ℕ) : (withLength body).length = body.length + 1 := by
  simp [withLength]

/-- Length of `E.flatMap encPair`. -/
@[simp]
theorem length_flatMap_encPair {N : ℕ} (E : List (Fin N × Fin N)) :
    (E.flatMap encPair).length = 2 * E.length := by
  induction E with
  | nil => simp
  | cons e rest ih => simp [encPair, ih]; omega

/-- Upper bound on the encoding length of a valid replacement record:
`l.length ≤ 26 + r.deleted.ncard + 4 * (r.graph.edgeSet \ r.newGraph.edgeSet).ncard`. -/
theorem isRecordEnc_repl_length_le {N : ℕ} {r : ReplRecord (Fin N)} {D : List (Fin N)}
    {l : List ℕ} (hval : r.IsValid D) (henc : IsRecordEnc (CrossRecord.repl r) l) :
    l.length ≤ 26 + r.deleted.ncard + 4 * (r.graph.edgeSet \ r.newGraph.edgeSet).ncard := by
  classical
  obtain ⟨B, R, E, hBnd, hBmem, hRnd, hRmem, hEnd, hEmem, rfl⟩ := henc
  have hB_eq : B.toFinset = r.boundary := by ext y; simp [hBmem]
  have hB_len : B.length ≤ 3 := by
    rw [← List.toFinset_card_of_nodup hBnd, hB_eq]
    exact hval.2.2.1
  have hR_sub : (R.toFinset : Set (Fin N)) ⊆ r.deleted := by
    intro y hy
    rw [Finset.mem_coe, List.mem_toFinset, hRmem] at hy
    exact hval.2.2.2.2.2.1 hy
  have hR_len : R.length ≤ r.deleted.ncard := by
    rw [← List.toFinset_card_of_nodup hRnd, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hR_sub (Set.toFinite _)
  let D_edges : Finset (Sym2 (Fin N)) := (r.graph.edgeSet \ r.newGraph.edgeSet).toFinset
  let repPair : Sym2 (Fin N) → Fin N × Fin N := fun e => Classical.choose (Quot.exists_rep e)
  have hrepPair : ∀ e : Sym2 (Fin N), s((repPair e).1, (repPair e).2) = e :=
    fun e => Classical.choose_spec (Quot.exists_rep e)
  let U_pairs : Finset (Fin N × Fin N) :=
    (r.boundary ×ˢ r.boundary) ∪ D_edges.biUnion (fun e => {repPair e, (repPair e).swap})
  have hE_sub : E.toFinset ⊆ U_pairs := by
    intro ⟨a, b⟩ hp
    rw [List.mem_toFinset, hEmem] at hp
    rcases hp with ⟨hadj, ha_or, hb_or⟩
    by_cases hboth : a ∈ r.boundary ∧ b ∈ r.boundary
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr hboth)
    · apply Finset.mem_union_right
      have hdel_ab : a ∈ r.deleted ∨ b ∈ r.deleted := by
        rcases ha_or with ha | ha
        · exact Or.inl (hval.2.2.2.2.2.1 ha)
        · rcases hb_or with hb | hb
          · exact Or.inr (hval.2.2.2.2.2.1 hb)
          · exact (hboth ⟨ha, hb⟩).elim
      have he_mem : s(a, b) ∈ D_edges := by
        rw [Set.mem_toFinset]
        refine ⟨hadj, fun hnew => ?_⟩
        simp only [SimpleGraph.mem_edgeSet, ReplRecord.newGraph, replaceGraph] at hnew
        rcases hnew with ⟨_, ha_nd, hb_nd⟩ | ⟨ha_bd, hb_bd, _⟩
        · rcases hdel_ab with ha | hb
          · exact ha_nd ha
          · exact hb_nd hb
        · exact hboth ⟨ha_bd, hb_bd⟩
      rw [Finset.mem_biUnion]
      refine ⟨s(a, b), he_mem, ?_⟩
      have hsym := (hrepPair s(a, b)).symm
      rw [Sym2.eq_iff] at hsym
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_swap,
        Prod.snd_swap]
      exact hsym
  have hE_len : E.length ≤ 9 + 2 * (r.graph.edgeSet \ r.newGraph.edgeSet).ncard := by
    rw [← List.toFinset_card_of_nodup hEnd]
    have h1 := Finset.card_le_card hE_sub
    have h2 : U_pairs.card ≤ (r.boundary ×ˢ r.boundary).card +
        (D_edges.biUnion (fun e => {repPair e, (repPair e).swap})).card :=
      Finset.card_union_le _ _
    have h3 : (r.boundary ×ˢ r.boundary).card ≤ 9 := by
      rw [Finset.card_product]
      have := hval.2.2.1
      nlinarith
    have h4 : (D_edges.biUnion (fun e => {repPair e, (repPair e).swap})).card ≤ 2 * D_edges.card := by
      calc (D_edges.biUnion (fun e => {repPair e, (repPair e).swap})).card
        _ ≤ ∑ e ∈ D_edges, ({repPair e, (repPair e).swap} : Finset (Fin N × Fin N)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _e ∈ D_edges, 2 := Finset.sum_le_sum (fun e _ => Finset.card_le_two)
        _ = 2 * D_edges.card := by simp [mul_comm]
    have h5 : D_edges.card = (r.graph.edgeSet \ r.newGraph.edgeSet).ncard := by
      rw [← Set.ncard_coe_finset D_edges, Set.coe_toFinset]
    omega
  simp only [length_withLength, List.cons_append, List.length_cons, List.length_append,
    List.length_map, length_flatMap_encPair]
  omega

/-- Coarse bound on the encoding length of any replacement record `r` on `(H, S)`:
`l.length ≤ 26 * instSize N H`. -/
theorem isRecordEnc_repl_length_le_instSize {N : ℕ} {r : ReplRecord (Fin N)}
    {D : List (Fin N)} {l : List ℕ}
    (hval : r.IsValid D)
    (henc : IsRecordEnc (CrossRecord.repl r) l) :
    l.length ≤ 26 * instSize N r.graph := by
  have h1 := isRecordEnc_repl_length_le hval henc
  have hdel : r.deleted.ncard ≤ N := by
    have := Set.ncard_le_ncard (Set.subset_univ r.deleted) (Set.toFinite _)
    simpa using this
  have hdiff : (r.graph.edgeSet \ r.newGraph.edgeSet).ncard ≤ r.graph.edgeSet.ncard :=
    Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)
  unfold instSize
  omega

/-- Each record has a unique encoding length under `IsRecordEnc`. -/
theorem isRecordEnc_length_eq {N : ℕ} {r₀ : CrossRecord (Fin N)} {l₁ l₂ : List ℕ}
    (he₁ : IsRecordEnc r₀ l₁) (he₂ : IsRecordEnc r₀ l₂) : l₁.length = l₂.length := by
  cases r₀ with
  | repl r =>
    obtain ⟨B₁, R₁, E₁, hB1, hBm1, hR1, hRm1, hE1, hEm1, rfl⟩ := he₁
    obtain ⟨B₂, R₂, E₂, hB2, hBm2, hR2, hRm2, hE2, hEm2, rfl⟩ := he₂
    have hBeq : B₁.length = B₂.length := by
      classical
      rw [← List.toFinset_card_of_nodup hB1, ← List.toFinset_card_of_nodup hB2]
      congr 1; ext y; simp [hBm1, hBm2]
    have hReq : R₁.length = R₂.length := by
      classical
      rw [← List.toFinset_card_of_nodup hR1, ← List.toFinset_card_of_nodup hR2]
      congr 1; ext y; simp [hRm1, hRm2]
    have hEeq : E₁.length = E₂.length := by
      classical
      rw [← List.toFinset_card_of_nodup hE1, ← List.toFinset_card_of_nodup hE2]
      congr 1; ext ⟨a, b⟩; simp [hEm1, hEm2]
    simp only [length_withLength, List.cons_append, List.length_cons, List.length_append,
      List.length_map, length_flatMap_encPair, hBeq, hReq, hEeq]
  | contr r =>
    obtain ⟨Nv₁, hN1, hNm1, rfl⟩ := he₁
    obtain ⟨Nv₂, hN2, hNm2, rfl⟩ := he₂
    have hNeq : Nv₁.length = Nv₂.length := by
      classical
      rw [← List.toFinset_card_of_nodup hN1, ← List.toFinset_card_of_nodup hN2]
      congr 1; ext y; simp [hNm1, hNm2]
    simp [hNeq]
  | del G' S' =>
    subst he₁; subst he₂; rfl

theorem forall₂_snoc_inv {α β : Type*} {R : α → β → Prop} :
    ∀ {xs : List α} {x : α} {ys : List β},
      List.Forall₂ R (xs ++ [x]) ys →
      ∃ ys_pre y, List.Forall₂ R xs ys_pre ∧ R x y ∧ ys = ys_pre ++ [y]
  | [], x, ys, h => by
    cases h with
    | cons hx hnil =>
      cases hnil
      exact ⟨[], _, .nil, hx, rfl⟩
  | a :: xs, x, ys, h => by
    cases h with
    | cons ha hrest =>
      obtain ⟨ys_pre, y, hpre, hx, rfl⟩ := forall₂_snoc_inv hrest
      exact ⟨_ :: ys_pre, y, .cons ha hpre, hx, rfl⟩

/-- Appending a single record encoding increases `(s.arrs a_rec).length` by the length of the new
encoding. -/
theorem isRecordsAt_snoc_length {N : ℕ} {a_rec : ℕ} {recs : List (CrossRecord (Fin N))}
    {rec : CrossRecord (Fin N)} {s₁ s₂ : State}
    (h₁ : IsRecordsAt a_rec recs s₁) (h₂ : IsRecordsAt a_rec (recs ++ [rec]) s₂) :
    ∃ l : List ℕ, IsRecordEnc rec l ∧
      (s₂.arrs a_rec).length = (s₁.arrs a_rec).length + l.length := by
  obtain ⟨ls₁, hrel₁, harr₁⟩ := h₁
  obtain ⟨ls₂, hrel₂, harr₂⟩ := h₂
  obtain ⟨ls_pre, l, hpre, henc, rfl⟩ := forall₂_snoc_inv hrel₂
  refine ⟨l, henc, ?_⟩
  have hlen_eq : ls_pre.flatten.length = ls₁.flatten.length := by
    clear harr₁ harr₂ henc hrel₂
    induction hrel₁ generalizing ls_pre with
    | nil =>
      cases hpre
      rfl
    | cons he₁ hrel' ih =>
      cases hpre with
      | cons he₂ hpre' =>
        simp only [List.flatten_cons, List.length_append]
        rw [ih _ hpre', isRecordEnc_length_eq he₂ he₁]
  simp [harr₁, harr₂, hlen_eq]

/-- Across a valid replacement step from `(s₁, G, S)` to `(s₂, r.newGraph, S')`, the record-length
potential `(s.arrs a_rec).length + 51 * S.card + 4 * G.edgeSet.ncard` does not increase. -/
theorem rec_pot_step {N : ℕ} {a_rec : ℕ} {G : SimpleGraph (Fin N)} {S S' : Finset (Fin N)}
    {D : List (Fin N)} {recs : List (CrossRecord (Fin N))} {r : ReplRecord (Fin N)}
    {s₁ s₂ : State}
    (hg : r.graph = G) (hv : r.verts = (S : Set (Fin N))) (hval : r.IsValid D)
    (hS' : (S' : Set (Fin N)) = r.newVerts)
    (hrec₁ : IsRecordsAt a_rec recs s₁)
    (hrec₂ : IsRecordsAt a_rec (recs ++ [CrossRecord.repl r]) s₂) :
    (s₂.arrs a_rec).length + 51 * S'.card + 4 * r.newGraph.edgeSet.ncard ≤
      (s₁.arrs a_rec).length + 51 * S.card + 4 * G.edgeSet.ncard := by
  subst hg
  obtain ⟨hcard, hpos, _⟩ := edge_pot_step rfl hv hval hS'
  have hedge := ncard_newGraph_add_sdiff_le hval
  obtain ⟨l, henc, hlen_rec⟩ := isRecordsAt_snoc_length hrec₁ hrec₂
  have hlen_l := isRecordEnc_repl_length_le hval henc
  omega

end GraphMinor.Compute.Crossing
