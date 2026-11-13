module

public import GraphMinor.Compute.SpecsCrossingRec
public import GraphMinor.Crossing.CutSec2Fan
public import GraphMinor.Crossing.PlanarFactT
public import GraphMinor.Crossing.Sparse72

/-!
# Corrected Lift Interface and Refutation of `LiftRecProgClaim` / `LiftProgClaim`

In `GraphMinor/Compute/SpecsCrossingRec.lean` (and `SpecsCrossing.lean`), `LiftRecProgClaim`
(resp. `LiftProgClaim`) quantifies over arbitrary `recs : List (CrossRecord (Fin N))` and
arbitrary vertex lists `L₁ L₂ : List (Fin N)` assuming only `IsRecBufAt a_rec r_rec recs k s`
and `∃ P, IsLift recs (L₁, L₂) P`, without assuming `IsHistoryFin G S D recs G' S' D'` or
`IsCrossingPair G' D' L₁ L₂`.

Because `IsRecordEnc (CrossRecord.repl r) l` only records edges of `r.graph` whose endpoints both
lie in `r.rep ∪ r.boundary`, an arbitrary list `L₁` that is not a path in `r.newGraph` can have a
consecutive pair `(a, b)` outside `r.rep ∪ r.boundary`; whether `r.graph.Adj a b` holds determines
`usesNewEdge r.graph L₁`, but is invisible in the encoding `l`. Moreover, the time bound of
`LiftRecProgClaim` includes `(recs.length + 1) * (N + 1)`, whereas in any valid history
`IsHistoryFin G S D recs G' S' D'` at most `N` records are replacements or contractions and
each `CrossRecord.del` record takes `O(1)` time.

Accordingly, this file:
* defines the corrected claim `LiftRecHistProgClaim` (adding `IsHistoryFin G S D recs G' S' D'`,
  `ContractionsLong recs`, and `IsCrossingPair G' D' L₁ L₂`, with time bound
  `C * (s.regs r_rec + (N + 1) * (N + 1))`);
* proves `not_liftRecProgClaim : ¬ LiftRecProgClaim` and `not_liftProgClaim : ¬ LiftProgClaim`;
* proves `isCrossed_of_clean_of_isEmpty_planeEmbedding` (Fact T applied to a clean nonplanar
  instance, used in the `YES` branch of the crossing extractor).
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### 1. The corrected lift interface `LiftRecHistProgClaim` -/

/-- Corrected version of `LiftRecProgClaim` (Section 11 of `docs/crossing/crossing_extractor.tex`):
adds the history and crossing-pair invariants (`IsHistoryFin G S D recs G' S' D'`,
`ContractionsLong recs`, `IsCrossingPair G' D' L₁ L₂`) that hold at the call site in the
crossing extractor, and bounds the running time by `C * (s.regs r_rec + (N + 1) * (N + 1))`
(since at most `N` records in a valid history on `Fin N` are replacements or contractions). -/
def LiftRecHistProgClaim : Prop :=
  ∀ (a_rec r_rec a_Q a_R a_base r_base : ℕ),
    ArrsOk [a_rec, a_Q, a_R] a_base → r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ),
      ∀ (w N : ℕ) [DecidableEq (Fin N)]
        (G G' : SimpleGraph (Fin N)) (S S' : Finset (Fin N))
        (D D' : List (Fin N)) (recs : List (CrossRecord (Fin N)))
        (k : ℕ) (L₁ L₂ : List (Fin N)) (s : State),
        wordSize c ((s.arrs a_rec).length + (N + 1) * (N + 1)) ≤ w →
        IsHistoryFin G S D recs G' S' D' →
        ContractionsLong recs →
        IsCrossingPair G' D' L₁ L₂ →
        IsRecBufAt a_rec r_rec recs k s →
        s.arrs a_Q = L₁.map Fin.val →
        s.arrs a_R = L₂.map Fin.val →
        L₁.length ≤ N →
        L₂.length ≤ N →
        ∃ s' t, Exec w P s s' t ∧
          t ≤ C * (s.regs r_rec + (N + 1) * (N + 1)) ∧
          KeepsBelow r_base a_base [] [a_Q, a_R] s s' ∧
          ∃ P', IsLift recs (L₁, L₂) P' ∧
            s'.arrs a_Q = P'.1.map Fin.val ∧
            s'.arrs a_R = P'.2.map Fin.val

/-! ### 2. Counterexample to `LiftRecProgClaim` and `LiftProgClaim` on `Fin 4` -/

/-- Graph `G₁` on `Fin 4`: 4-cycle `0 - 2 - 1 - 3 - 0`. -/
def liftCounterGraph1 : SimpleGraph (Fin 4) where
  Adj a b :=
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨
    (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨
    (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
    (a = 3 ∧ b = 1) ∨ (a = 1 ∧ b = 3)
  symm := ⟨fun _ _ h => by tauto⟩
  loopless := ⟨fun a h => by revert a h; decide⟩

/-- Graph `G₂` on `Fin 4`: path `0 - 2 - 1` with vertex `3` isolated. -/
def liftCounterGraph2 : SimpleGraph (Fin 4) where
  Adj a b :=
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨
    (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)
  symm := ⟨fun _ _ h => by tauto⟩
  loopless := ⟨fun a h => by revert a h; decide⟩

/-- First replacement record on `Fin 4`: `boundary = {0, 1}`, `rep = {2}`, `graph = G₁`. -/
def liftCounterRepl1 : ReplRecord (Fin 4) where
  graph := liftCounterGraph1
  verts := Set.univ
  deleted := {(2 : Fin 4)}
  boundary := {(0 : Fin 4), (1 : Fin 4)}
  rep := {(2 : Fin 4)}

/-- Second replacement record on `Fin 4`: `boundary = {0, 1}`, `rep = {2}`, `graph = G₂`. -/
def liftCounterRepl2 : ReplRecord (Fin 4) where
  graph := liftCounterGraph2
  verts := Set.univ
  deleted := {(2 : Fin 4)}
  boundary := {(0 : Fin 4), (1 : Fin 4)}
  rep := {(2 : Fin 4)}

/-- Boundary list `B = [0, 1]` for the counterexample encoding. -/
def liftCounterB : List (Fin 4) := [0, 1]

/-- Representative list `R = [2]` for the counterexample encoding. -/
def liftCounterR : List (Fin 4) := [2]

/-- Edge list `E` on `rep ∪ boundary = {0, 1, 2}` for the counterexample encoding. -/
def liftCounterE : List (Fin 4 × Fin 4) := [(0, 2), (2, 0), (2, 1), (1, 2)]

/-- Explicit word-list encoding shared by `liftCounterRepl1` and `liftCounterRepl2`. -/
def liftCounterEnc : List ℕ :=
  withLength (0 :: liftCounterB.length :: liftCounterB.map Fin.val ++
    liftCounterR.length :: liftCounterR.map Fin.val ++
    liftCounterE.length :: liftCounterE.flatMap encPair)

/-- First test path `L₁ = [0, 3, 1]` on `Fin 4`. -/
def liftCounterPath1 : List (Fin 4) := [0, 3, 1]

/-- Second test path `L₂ = [0]` on `Fin 4`. -/
def liftCounterPath2 : List (Fin 4) := [0]

/-- Replacement path `Y = [0, 2, 1]` on `Fin 4`. -/
def liftCounterSearch : List (Fin 4) := [0, 2, 1]

private lemma isRecordEnc_liftCounterRepl1 :
    IsRecordEnc (CrossRecord.repl liftCounterRepl1) liftCounterEnc := by
  refine ⟨liftCounterB, liftCounterR, liftCounterE, by decide, ?_, by decide, ?_, by decide, ?_, rfl⟩
  · intro y
    simp [liftCounterB, liftCounterRepl1]
  · intro y
    simp [liftCounterR, liftCounterRepl1]
  · intro a b
    simp only [liftCounterE, liftCounterRepl1, liftCounterGraph1, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
    fin_cases a <;> fin_cases b <;> decide

private lemma isRecordEnc_liftCounterRepl2 :
    IsRecordEnc (CrossRecord.repl liftCounterRepl2) liftCounterEnc := by
  refine ⟨liftCounterB, liftCounterR, liftCounterE, by decide, ?_, by decide, ?_, by decide, ?_, rfl⟩
  · intro y
    simp [liftCounterB, liftCounterRepl2]
  · intro y
    simp [liftCounterR, liftCounterRepl2]
  · intro a b
    simp only [liftCounterE, liftCounterRepl2, liftCounterGraph2, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
    fin_cases a <;> fin_cases b <;> decide

private lemma not_usesNewEdge_counter1 :
    ¬ usesNewEdge liftCounterRepl1.graph liftCounterPath1 := by
  rintro ⟨i, a, b, ha, hb, hnadj⟩
  rcases i with _ | _ | _ | i
  · simp [liftCounterPath1] at ha hb
    subst ha hb
    exact hnadj (by simp [liftCounterRepl1, liftCounterGraph1])
  · simp [liftCounterPath1] at ha hb
    subst ha hb
    exact hnadj (by simp [liftCounterRepl1, liftCounterGraph1])
  · simp [liftCounterPath1] at hb
  · simp [liftCounterPath1] at ha

private lemma not_usesNewEdge_path2 (G : SimpleGraph (Fin 4)) :
    ¬ usesNewEdge G liftCounterPath2 := by
  rintro ⟨i, a, b, ha, hb, _⟩
  rcases i with _ | i
  · simp [liftCounterPath2] at hb
  · simp [liftCounterPath2] at ha

private lemma usesNewEdge_counter2 :
    usesNewEdge liftCounterRepl2.graph liftCounterPath1 := by
  refine ⟨0, 0, 3, rfl, rfl, ?_⟩
  simp [liftCounterRepl2, liftCounterGraph2]

private lemma isLift_counter1 :
    IsLift [CrossRecord.repl liftCounterRepl1] (liftCounterPath1, liftCounterPath2)
      (liftCounterPath1, liftCounterPath2) := by
  refine ⟨(liftCounterPath1, liftCounterPath2), rfl, ?_⟩
  exact Or.inl ⟨not_usesNewEdge_counter1, not_usesNewEdge_path2 _, rfl⟩

private lemma isLift_counter1_eq {P : List (Fin 4) × List (Fin 4)}
    (h : IsLift [CrossRecord.repl liftCounterRepl1] (liftCounterPath1, liftCounterPath2) P) :
    P.1 = liftCounterPath1 := by
  rcases h with ⟨P_mid, hmid, h1⟩
  have hmid_eq : P_mid = (liftCounterPath1, liftCounterPath2) := hmid
  subst hmid_eq
  rcases h1 with ⟨_, _, hP⟩ | ⟨hnew, _⟩ | ⟨_, hnew2, _⟩
  · rw [hP]
  · exact (not_usesNewEdge_counter1 hnew).elim
  · exact (not_usesNewEdge_path2 _ hnew2).elim

private lemma spliceBetween_counter2 :
    ∀ Y : List (Fin 4), spliceBetween liftCounterRepl2.boundary liftCounterPath1 Y = Y := by
  intro Y
  change ([] : List (Fin 4)) ++ Y ++ [] = Y
  simp

private lemma isReplSearchPath_counter2 :
    IsReplSearchPath liftCounterRepl2 liftCounterPath1 liftCounterSearch := by
  refine ⟨0, 1, by decide, by decide, ?_, ⟨rfl, rfl⟩⟩
  refine ⟨by decide, by decide, ?_⟩
  simp only [liftCounterSearch, List.isChain_cons_cons, List.isChain_singleton, and_true]
  refine ⟨?_, ?_⟩
  · refine ⟨by simp [liftCounterRepl2, liftCounterGraph2], ?_, ?_⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · refine ⟨by simp [liftCounterRepl2, liftCounterGraph2], ?_, ?_⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)

private lemma isLift_counter2 :
    IsLift [CrossRecord.repl liftCounterRepl2] (liftCounterPath1, liftCounterPath2)
      (liftCounterSearch, liftCounterPath2) := by
  refine ⟨(liftCounterPath1, liftCounterPath2), rfl, ?_⟩
  exact Or.inr (Or.inl ⟨usesNewEdge_counter2, liftCounterSearch, isReplSearchPath_counter2,
    by rw [spliceBetween_counter2]⟩)

private lemma not_mem_three_of_isLift_counter2 {P : List (Fin 4) × List (Fin 4)}
    (h : IsLift [CrossRecord.repl liftCounterRepl2] (liftCounterPath1, liftCounterPath2) P) :
    (3 : Fin 4) ∉ P.1 := by
  rcases h with ⟨P_mid, hmid, h1⟩
  have hmid_eq : P_mid = (liftCounterPath1, liftCounterPath2) := hmid
  subst hmid_eq
  rcases h1 with ⟨hnot, _⟩ | ⟨_, Y, hY, hP⟩ | ⟨hnot, _⟩
  · exact (hnot usesNewEdge_counter2).elim
  · rw [spliceBetween_counter2 Y] at hP
    rw [hP]
    rcases hY with ⟨p, q, hp, hq, ⟨_, _, hch⟩, hhead, _⟩
    have hp0 : p = 0 := by
      have : firstIn liftCounterRepl2.boundary liftCounterPath1 = some 0 := by decide
      rw [this] at hp
      exact Option.some.inj hp.symm
    have hq1 : q = 1 := by
      have : lastIn liftCounterRepl2.boundary liftCounterPath1 = some 1 := by decide
      rw [this] at hq
      exact Option.some.inj hq.symm
    subst hp0 hq1
    intro h3
    rcases Y with _ | ⟨y₀, Y_tl⟩
    · simp at h3
    · simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      rcases Y_tl with _ | ⟨y₁, Y_tl'⟩
      · simp only [List.mem_singleton] at h3
        revert h3; decide
      · have h_mem_restrict : ∀ x ∈ (0 :: y₁ :: Y_tl' : List (Fin 4)),
            x ∈ liftCounterRepl2.rep ∪ ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) := by
          intro x hx
          have hch_all : ∀ (u : Fin 4) (l : List (Fin 4)),
              (u :: l).IsChain (HP25.restrict liftCounterRepl2.graph
                (liftCounterRepl2.rep ∪ {(0 : Fin 4), (1 : Fin 4)})).Adj →
              u ∈ liftCounterRepl2.rep ∪ {(0 : Fin 4), (1 : Fin 4)} →
              ∀ z ∈ u :: l, z ∈ liftCounterRepl2.rep ∪ {(0 : Fin 4), (1 : Fin 4)} := by
            intro u l
            induction l generalizing u with
            | nil =>
              intro _ hu z hz
              simp only [List.mem_singleton] at hz
              exact hz ▸ hu
            | cons w l' ih =>
              intro hchw hu z hz
              rw [List.isChain_cons_cons] at hchw
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact hu
              · exact ih w hchw.2 hchw.1.2.2 z hz'
          exact hch_all 0 (y₁ :: Y_tl') hch (Or.inr (Or.inl rfl)) x hx
        have h3_in := h_mem_restrict 3 h3
        change (3 : Fin 4) = 2 ∨ (3 : Fin 4) = 0 ∨ (3 : Fin 4) = 1 at h3_in
        revert h3_in; decide
  · exact (hnot usesNewEdge_counter2).elim

/-- `LiftRecProgClaim` is false as stated in `SpecsCrossingRec.lean`: on `Fin 4`, `liftCounterRepl1`
and `liftCounterRepl2` share the same encoding `liftCounterEnc`, yet lifting `([0, 3, 1], [0])`
across `liftCounterRepl1` must keep `3` in `P'.1` while lifting across `liftCounterRepl2` must
remove `3` from `P'.1`. -/
theorem not_liftRecProgClaim : ¬ LiftRecProgClaim := by
  intro hclaim
  have harrs : ArrsOk [0, 1, 2] 3 :=
    ⟨by decide, fun x hx => by simp at hx; omega⟩
  obtain ⟨P, C, c, hP⟩ := hclaim 0 0 1 2 3 1 harrs (by omega)
  let s : State :=
    { regs := fun r => if r = 0 then liftCounterEnc.length else 0
      arrs := fun a =>
        if a = 0 then liftCounterEnc
        else if a = 1 then liftCounterPath1.map Fin.val
        else if a = 2 then liftCounterPath2.map Fin.val
        else [] }
  let w := wordSize c ((s.arrs 0).length + (1 + 1) * (4 + 1))
  have hbuf1 : IsRecBufAt 0 0 [CrossRecord.repl liftCounterRepl1] 0 s :=
    ⟨[liftCounterEnc], List.Forall₂.cons isRecordEnc_liftCounterRepl1 List.Forall₂.nil,
      by simp [s], by simp [s]⟩
  have hbuf2 : IsRecBufAt 0 0 [CrossRecord.repl liftCounterRepl2] 0 s :=
    ⟨[liftCounterEnc], List.Forall₂.cons isRecordEnc_liftCounterRepl2 List.Forall₂.nil,
      by simp [s], by simp [s]⟩
  obtain ⟨s₁, t₁, hex₁, _, _, P₁, hL₁, hQ₁, _⟩ :=
    hP w 4 [CrossRecord.repl liftCounterRepl1] 0 liftCounterPath1 liftCounterPath2 s
      le_rfl hbuf1 (by simp [s]) (by simp [s]) (by decide) (by decide) ⟨_, isLift_counter1⟩
  obtain ⟨s₂, t₂, hex₂, _, _, P₂, hL₂, hQ₂, _⟩ :=
    hP w 4 [CrossRecord.repl liftCounterRepl2] 0 liftCounterPath1 liftCounterPath2 s
      le_rfl hbuf2 (by simp [s]) (by simp [s]) (by decide) (by decide) ⟨_, isLift_counter2⟩
  obtain ⟨rfl, _⟩ := hex₁.deterministic hex₂
  have hP₁_eq : P₁.1 = liftCounterPath1 := isLift_counter1_eq hL₁
  have hmap_eq : P₂.1.map Fin.val = liftCounterPath1.map Fin.val := by
    rw [← hQ₂, hQ₁, hP₁_eq]
  have hP₂_eq : P₂.1 = liftCounterPath1 :=
    List.map_injective_iff.mpr Fin.val_injective hmap_eq
  have h3_mem : (3 : Fin 4) ∈ P₂.1 := by
    rw [hP₂_eq]
    decide
  exact not_mem_three_of_isLift_counter2 hL₂ h3_mem

/-- `LiftProgClaim` is false as stated in `SpecsCrossing.lean` by the same counterexample. -/
theorem not_liftProgClaim : ¬ LiftProgClaim := by
  intro hclaim
  have harrs : ArrsOk [0, 1, 2] 3 :=
    ⟨by decide, fun x hx => by simp at hx; omega⟩
  obtain ⟨P, C, c, hP⟩ := hclaim 0 1 2 3 1 harrs
  let s : State :=
    { regs := fun _ => 0
      arrs := fun a =>
        if a = 0 then liftCounterEnc
        else if a = 1 then liftCounterPath1.map Fin.val
        else if a = 2 then liftCounterPath2.map Fin.val
        else [] }
  let w := wordSize c ((s.arrs 0).length + (1 + 1) * (4 + 1))
  have hrec1 : IsRecordsAt 0 [CrossRecord.repl liftCounterRepl1] s :=
    ⟨[liftCounterEnc], List.Forall₂.cons isRecordEnc_liftCounterRepl1 List.Forall₂.nil, by simp [s]⟩
  have hrec2 : IsRecordsAt 0 [CrossRecord.repl liftCounterRepl2] s :=
    ⟨[liftCounterEnc], List.Forall₂.cons isRecordEnc_liftCounterRepl2 List.Forall₂.nil, by simp [s]⟩
  obtain ⟨s₁, t₁, hex₁, _, _, P₁, hL₁, hQ₁, _⟩ :=
    hP w 4 [CrossRecord.repl liftCounterRepl1] liftCounterPath1 liftCounterPath2 s
      le_rfl hrec1 (by simp [s]) (by simp [s]) (by decide) (by decide) ⟨_, isLift_counter1⟩
  obtain ⟨s₂, t₂, hex₂, _, _, P₂, hL₂, hQ₂, _⟩ :=
    hP w 4 [CrossRecord.repl liftCounterRepl2] liftCounterPath1 liftCounterPath2 s
      le_rfl hrec2 (by simp [s]) (by simp [s]) (by decide) (by decide) ⟨_, isLift_counter2⟩
  obtain ⟨rfl, _⟩ := hex₁.deterministic hex₂
  have hP₁_eq : P₁.1 = liftCounterPath1 := isLift_counter1_eq hL₁
  have hmap_eq : P₂.1.map Fin.val = liftCounterPath1.map Fin.val := by
    rw [← hQ₂, hQ₁, hP₁_eq]
  have hP₂_eq : P₂.1 = liftCounterPath1 :=
    List.map_injective_iff.mpr Fin.val_injective hmap_eq
  have h3_mem : (3 : Fin 4) ∈ P₂.1 := by
    rw [hP₂_eq]
    decide
  exact not_mem_three_of_isLift_counter2 hL₂ h3_mem

/-! ### 3. Fact T consequence for clean nonplanar instances -/

private lemma not_walk_to_outside_of_mem_U {V : Type*} {K : SimpleGraph V} {S U : Set V}
    {D : List V} {X : Finset (Option V)} (hK : HP25.IsSupportedOn K S)
    (hUD : U ⊆ S \ {v | v ∈ D})
    (hX : ∀ z ∈ S \ U, (∃ y ∈ U, K.Adj y z) → some z ∈ X)
    {a b : Option V} (p : (apex K D).Walk a b)
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
        have hzS : z ∈ S := hK haw.symm
        exact hw_mem.2 (hX z ⟨hzS, hzU⟩ ⟨y, hyU, haw⟩)

/-- By Fact T (`fact_T_on`), any clean instance `(K, S, D)` with no plane embedding is crossed on
`D` (the argument for the answer `YES` of `Classify` in Section 6 of
`docs/crossing/crossing_extractor.tex`). -/
theorem isCrossed_of_clean_of_isEmpty_planeEmbedding {V : Type*} [DecidableEq V]
    {K : SimpleGraph V} {S : Set V} {D : List V}
    (hSfin : S.Finite) (hK : HP25.IsSupportedOn K S) (hD : HP25.IsCycleList K D)
    (hclean : IsClean K S D) (hnp : IsEmpty (HP25.PlaneEmbedding K S)) :
    HP25.IsCrossed K D := by
  by_contra hnc
  have hDS : ∀ v ∈ D, v ∈ S := fun v hv => mem_of_mem_cycleList hK hD hv
  have hnp' : ¬ Nonempty (HP25.PlaneEmbedding K S) := not_nonempty_iff.mpr hnp
  obtain ⟨U, hUD, ⟨u₀, hu₀U⟩, _, hNcard⟩ := fact_T_on hSfin hK hD hDS hnc hnp'
  let NU : Set V := {z ∈ S \ U | ∃ y ∈ U, K.Adj y z}
  have hNU_fin : NU.Finite := hSfin.subset (fun _ hz => hz.1.1)
  let X : Finset (Option V) := hNU_fin.toFinset.image some
  have hXsub : (X : Set (Option V)) ⊆ apexVerts S \ {none} := by
    intro w hw
    simp only [X, Finset.coe_image, Set.mem_image] at hw
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
    simp only [X, Finset.coe_image, Set.mem_image, Option.some.injEq, exists_eq_right]
    exact fun hu₀NU => (hNU_fin.mem_toFinset.mp hu₀NU).1.2 hu₀U
  have hnone_mem : (none : Option V) ∈ apexVerts S \ (X : Set (Option V)) :=
    ⟨Or.inl rfl, by simp [X]⟩
  obtain ⟨p, hp⟩ := (hclean X hXsub hXcard).2 (some u₀) hu₀_mem none hnone_mem
  refine not_walk_to_outside_of_mem_U hK hUD (fun z hzS hex => ?_) p hp
    ⟨u₀, hu₀U, rfl⟩ (by simp)
  exact Finset.mem_image_of_mem some (hNU_fin.mem_toFinset.mpr ⟨hzS, hex⟩)

end GraphMinor.Compute.Crossing
