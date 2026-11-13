module

public import GraphMinor.Compute.GM13SocietyOwnerTable

/-!
# Locating the division and writing its loop owners

The simple output starts with the core, then the raw-member list, then the
merged-member list. This program skips the core and raw records by their
stored lengths and queries the merged records for each vertex. Its owner
table covers singleton members as well as members containing edges.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read a member-list header and move the record pointer to its body. -/
def gm13ReadListHeaderProg : Cmd :=
  .seq (.assign 21 (.read 65 (.reg 20)))
    (.seq (.assign 20 (.op .add (.reg 20) (.const 1))) (.assign 22 (.const 0)))

/-- Reading a header uses only its count word. -/
theorem gm13ReadListHeaderProg_exec {w n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (pre suf : List ℕ)
    (hw : pre.length + 1 < 2 ^ w) (hL : L.length < 2 ^ w)
    {s : State} (hin : s.arrs 65 = pre ++ encAlg86PairList L ++ suf)
    (hoff : s.regs 20 = pre.length) :
    ∃ s', Exec w gm13ReadListHeaderProg s s' 9 ∧
      s'.regs 20 = (pre ++ [L.length]).length ∧ s'.regs 21 = L.length ∧
      s'.regs 22 = 0 ∧ s'.arrs = s.arrs ∧
      (∀ r : ℕ, r ≠ 20 → r ≠ 21 → r ≠ 22 → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  let s₁ := s.setReg 21 L.length
  have he₁ : Exec w (.assign 21 (.read 65 (.reg 20))) s s₁ 3 := by
    apply Exec.assign
    apply gm13_read_eval (eval_reg hoff (by omega))
    · rw [hin]
      simp only [encAlg86PairList, List.append_assoc, List.singleton_append]
      rw [List.getElem?_append_right le_rfl, Nat.sub_self]
      rfl
    · exact hL
  let s₂ := s₁.setReg 20 (pre ++ [L.length]).length
  have he₂ : Exec w (.assign 20 (.op .add (.reg 20) (.const 1))) s₁ s₂ 4 := by
    apply Exec.assign
    simpa only [List.length_append, List.length_cons, List.length_nil] using
      eval_add (eval_reg (by simpa [s₁] using hoff) (by omega)) (eval_const hw1) hw
  let s₃ := s₂.setReg 22 0
  have he₃ : Exec w (.assign 22 (.const 0)) s₂ s₃ 2 := .assign (eval_const (by omega))
  refine ⟨s₃, .seq he₁ (.seq he₂ he₃), by simp [s₃, s₂], by simp [s₃, s₂, s₁],
    by simp [s₃], rfl, ?_⟩
  intro r h20 h21 h22
  simp [s₃, s₂, s₁, h20, h21, h22]

/-- Skip the core and raw members, then compute owners in the merged list. -/
def gm13RuralOwnersProg : Cmd :=
  .seq (.assign 20 (.const 1))
    (.seq gm13SkipRecordProg
      (.seq gm13ReadListHeaderProg
        (.seq gm13SkipRecordsLoop
          (.seq gm13ReadListHeaderProg
            (.seq (.assign 26 (.reg 20)) gm13OwnerTableProg)))))

/-- The owner table is computed from the full simple division output. Its
time depends on vertex count times merged-member count, plus raw count. -/
theorem gm13RuralOwnersProg_exec {w n : ℕ}
    (core : Finset (Fin n) × List (Fin n × Fin n))
    (raw div : List (Finset (Fin n) × List (Fin n × Fin n))) (suf : List ℕ)
    (hw : ([0] ++ encAlg86Subgraph core.1 core.2 ++
      encAlg86PairList raw ++ encAlg86PairList div).length < 2 ^ w)
    (hnw : n < 2 ^ w) (hraw : raw.length < 2 ^ w) (hdiv : div.length < 2 ^ w)
    (hw1 : 1 < 2 ^ w) {s : State}
    (hin : s.arrs 65 = [0] ++ encAlg86Subgraph core.1 core.2 ++
      encAlg86PairList raw ++ encAlg86PairList div ++ suf) (hn : s.regs 0 = n) :
    ∃ s' t, Exec w gm13RuralOwnersProg s s' t ∧
      t ≤ 24 * raw.length + n * (32 * div.length + 20) + 48 ∧
      s'.arrs 30 = gm13LoopOwnerTable div ∧
      (∀ a : ℕ, a ≠ 30 → s'.arrs a = s.arrs a) := by
  let pc := [0] ++ encAlg86Subgraph core.1 core.2
  let pr := pc ++ [raw.length]
  let pe := pc ++ encAlg86PairList raw
  let pd := pe ++ [div.length]
  have hlen : (pc ++ encAlg86PairList raw ++ encAlg86PairList div).length < 2 ^ w := hw
  have hc : pc.length < 2 ^ w := by simp only [List.length_append] at hlen; omega
  have hr : (pr ++ raw.flatMap (fun A => encAlg86Subgraph A.1 A.2)).length < 2 ^ w := by
    simp only [pr, encAlg86PairList, List.length_append, List.length_cons, List.length_nil] at hlen ⊢
    omega
  have hd : (pd ++ div.flatMap (fun A => encAlg86Subgraph A.1 A.2)).length < 2 ^ w := by
    simpa only [pd, pe, encAlg86PairList, List.append_assoc] using hlen
  let s₁ := s.setReg 20 1
  have he₁ : Exec w (.assign 20 (.const 1)) s s₁ 2 := .assign (eval_const hw1)
  obtain ⟨s₂, he₂, hoff₂, ha₂, hr₂⟩ := gm13SkipRecordProg_exec (w := w) (s := s₁) core [0]
    (encAlg86PairList raw ++ encAlg86PairList div ++ suf) hc
    (by simpa [s₁, List.append_assoc] using hin) (by simp [s₁]) (by simpa [s₁] using hn)
  obtain ⟨s₃, he₃, hoff₃, hcount₃, hk₃, ha₃, hr₃⟩ :=
    gm13ReadListHeaderProg_exec (w := w) (s := s₂) raw pc (encAlg86PairList div ++ suf)
      (by simp only [encAlg86PairList, List.length_append, List.length_cons, List.length_nil] at hlen; omega)
      hraw (by simpa [ha₂, s₁, pc, List.append_assoc] using hin) hoff₂
  obtain ⟨s₄, t₄, he₄, ht₄, hoff₄, ha₄, hr₄⟩ :=
    gm13SkipRecordsLoop_exec (w := w) (s := s₃) raw pr (encAlg86PairList div ++ suf)
      0 raw.length (Nat.zero_add _) hraw hr
      (by simpa [ha₃, ha₂, s₁, pr, pc, encAlg86PairList, List.append_assoc] using hin)
      hoff₃
      (by rw [hr₃ 0 (by decide) (by decide) (by decide), hr₂ 0 (by decide) (by decide)]; exact hn)
      hcount₃ hk₃ hw1
  have hoff₄' : s₄.regs 20 = pe.length := by
    simpa only [pr, pe, encAlg86PairList, List.append_assoc] using hoff₄
  obtain ⟨s₅, he₅, hoff₅, hcount₅, _, ha₅, hr₅⟩ :=
    gm13ReadListHeaderProg_exec (w := w) (s := s₄) div pe suf
      (by
        simp only [encAlg86PairList, List.length_append, List.length_cons, List.length_nil] at hlen
        dsimp only [pe, encAlg86PairList]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)
      hdiv (by simpa [ha₄, ha₃, ha₂, s₁, pe, pc, List.append_assoc] using hin) hoff₄'
  let s₆ := s₅.setReg 26 pd.length
  have he₆ : Exec w (.assign 26 (.reg 20)) s₅ s₆ 2 :=
    .assign (eval_reg hoff₅ (by simp only [List.length_append] at hd; omega))
  have hn₆ : s₆.regs 0 = n := by
    rw [show s₆.regs 0 = s₅.regs 0 by simp [s₆],
      hr₅ 0 (by decide) (by decide) (by decide), hr₄ 0 (by decide) (by decide) (by decide),
      hr₃ 0 (by decide) (by decide) (by decide), hr₂ 0 (by decide) (by decide)]
    exact hn
  obtain ⟨s₇, t₇, he₇, ht₇, howners, ha₇⟩ := gm13OwnerTableProg_exec (w := w) (s := s₆)
    div pd suf hd hnw hdiv hw1
    (by simpa [s₆, ha₅, ha₄, ha₃, ha₂, s₁, pd, pe, pc, encAlg86PairList,
      List.append_assoc] using hin) hn₆ (by simpa [s₆] using hcount₅) (by simp [s₆])
  refine ⟨s₇, 2 + (17 + (9 + (t₄ + (9 + (2 + t₇))))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ he₇))))),
    by omega, howners, ?_⟩
  intro a ha
  rw [ha₇ a ha]
  simp only [s₆, State.setReg_arrs, ha₅, ha₄, ha₃, ha₂, s₁]

end GraphMinor.Compute
