module

public import GraphMinor.Compute.TwoPathsDriverProg
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.Lemma43Tools

/-!
# The driver of Algorithm 5.1: a solve round

A solve round runs lines 2 to 10 of Algorithm 5.1 (Humeau and Pous, page 18) on the instance in
memory: `findProg` (lines 2 and 5), `sepProg` (line 6), the completion step `comp` (line 9), and,
when the instance is split, it pushes a frame and writes the first subinstance (line 10) with
`childProg 1`. `solveRound_exec` proves that the round either answers (`False` at line 3, `True` at
line 7, or `True` when the completion step finds a crossing) or splits the instance.

The completion step is a parameter: `CompSpec comp c c_w` and `ExtSpec comp ext c c_w` are the two
parts of `CompletionStatement` (`completionStatement_iff`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-! ### The two parts of the interface -/

/-- The first part of `CompletionStatement`: what the completion program `comp` does. -/
def CompSpec (comp : Cmd) (c c_w : ℕ) : Prop :=
  ∀ (N : ℕ) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (lists : Fin N → List ℕ)
    (a b : Fin N) (A B : List (Fin N)) (P : H.Walk a b),
    IsSplitInput H a b A B P →
    ∀ (w : ℕ), wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w →
    ∀ (s : State), InstanceAt H lists a b A B P s → (s.arrs aEnt).length < 2 ^ w →
      ∃ (s' : State) (t : ℕ), Exec w comp s s' t ∧
        (∀ r < 300, r ≠ rFlag → s'.regs r = s.regs r) ∧
        (∀ x < 200, x ≠ aQ → x ≠ aR → x ≠ aF → x ≠ aNewPath → s'.arrs x = s.arrs x) ∧
        (∀ x, isRecordArr x → (s'.arrs x).length ≤ c * (N + H.edgeFinset.card + 1)) ∧
        ((s'.regs rFlag = 1 ∧ CrossingAt H (a :: A ++ b :: B) aQ aR s' ∧
            t ≤ c * P.support.length * (N + H.edgeFinset.card + 1)) ∨
          (s'.regs rFlag = 0 ∧ IsCompletionOutput H a b A B c t s'))

/-- The second part of `CompletionStatement`: what the extraction program `ext` does. -/
def ExtSpec (comp ext : Cmd) (c c_w : ℕ) : Prop :=
  ∀ (N : ℕ) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (lists : Fin N → List ℕ)
    (a b : Fin N) (A B : List (Fin N)) (P : H.Walk a b),
    IsSplitInput H a b A B P →
    ∀ (w : ℕ), wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w →
    ∀ (s₀ s₁ : State) (t₁ : ℕ), InstanceAt H lists a b A B P s₀ →
      (s₀.arrs aEnt).length < 2 ^ w → Exec w comp s₀ s₁ t₁ → s₁.regs rFlag = 0 →
    ∀ (F : List ℕ) (m : List (Fin N)) (P' : (H ⊔ pairGraph N F).Walk a b),
      s₁.arrs aF = F → s₁.arrs aNewPath = P'.support.map Fin.val →
      P'.support = a :: m ++ [b] →
    ∀ (i : ℕ), (i = 1 ∨ i = 2) →
    ∀ (s : State), InstanceAt H lists a b A B P s → (s.arrs aEnt).length < 2 ^ w →
      s.arrs aF = F → s.arrs aNewPath = P'.support.map Fin.val →
      (∀ x, isRecordArr x → s.arrs x = s₁.arrs x) → s.regs rSide = i →
      CrossingAt (subGraph (H ⊔ pairGraph N F) P'.support A i) (subCycle a b A B m i)
        aQin aRin s →
      ∃ (s' : State) (t : ℕ), Exec w ext s s' t ∧
        t ≤ c * P'.support.length * (N + H.edgeFinset.card + 1) ∧
        (∀ r < 300, s'.regs r = s.regs r) ∧
        (∀ x < 300, x ≠ aQ → x ≠ aR → s'.arrs x = s.arrs x) ∧
        CrossingAt H (a :: A ++ b :: B) aQ aR s'

/-- `CompletionStatement` is the existence of a completion program and an extraction program with
the two specifications. -/
theorem completionStatement_iff : CompletionStatement ↔
    ∃ (comp ext : Cmd) (c c_w : ℕ), 0 < c ∧ 0 < c_w ∧ CompSpec comp c c_w ∧
      ExtSpec comp ext c c_w := Iff.rfl

/-! ### What a round keeps -/

/-- `s'` agrees with `s` on the registers `0 … 40` and the arrays `0 … 39`, which hold the input of
the whole program and the number `N` of vertices. -/
def Low (s s' : State) : Prop :=
  (∀ r : ℕ, r ≤ 40 → s'.regs r = s.regs r) ∧ (∀ x : ℕ, x < 40 → s'.arrs x = s.arrs x)

/-- `s'` agrees with `s` on the heap, the heap pointer, and what `Low` keeps. -/
def DKeep (s s' : State) : Prop :=
  s'.regs rHp = s.regs rHp ∧ s'.arrs aHeap = s.arrs aHeap ∧ Low s s'

theorem Low.refl (s : State) : Low s s := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem Low.trans {s₁ s₂ s₃ : State} (h₁ : Low s₁ s₂) (h₂ : Low s₂ s₃) : Low s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), fun x hx => (h₂.2 x hx).trans (h₁.2 x hx)⟩

theorem DKeep.refl (s : State) : DKeep s s := ⟨rfl, rfl, Low.refl s⟩

theorem DKeep.trans {s₁ s₂ s₃ : State} (h₁ : DKeep s₁ s₂) (h₂ : DKeep s₂ s₃) : DKeep s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₁.2.2.trans h₂.2.2⟩

theorem Keeps.low {R A : List ℕ} {s s' : State} (h : Keeps R A s s') (hR : ∀ r ∈ R, 40 < r)
    (hA : ∀ a ∈ A, 40 ≤ a) : Low s s' :=
  ⟨fun r hr => h.1 r (fun hm => by have := hR r hm; omega),
   fun x hx => h.2 x (fun hm => by have := hA x hm; omega)⟩

theorem Keeps.dkeep {R A : List ℕ} {s s' : State} (h : Keeps R A s s')
    (hR : ∀ r ∈ R, 40 < r ∧ r ≠ 120) (hA : ∀ a ∈ A, 40 ≤ a ∧ a ≠ 70) : DKeep s s' :=
  ⟨h.1 rHp (fun hm => (hR _ hm).2 rfl), h.2 aHeap (fun hm => (hA _ hm).2 rfl),
   h.low (fun r hr => (hR r hr).1) (fun a ha => (hA a ha).1)⟩

/-! ### Answers -/

/-- Write the answer `False` and return. -/
def answerFalse : Cmd := .seq (.assign rRes (.const 0)) (.assign rMode (.const 1))

/-- Turn the crossing in `aQ`, `aR` of the rotated cycle into one of the cycle `T` in `aT0`, write
the answer `True` and return. -/
def answerTrue : Cmd := .seq normProg (.seq (.assign rRes (.const 1)) (.assign rMode (.const 1)))

theorem answerFalse_exec {w : ℕ} (hw : 1 < 2 ^ w) (s : State) :
    ∃ s', Exec w answerFalse s s' 4 ∧ DKeep s s' ∧ s'.regs rMode = 1 ∧ s'.regs rRes = 0 ∧
      ∀ x, s'.arrs x = s.arrs x := by
  refine ⟨(s.setReg rRes 0).setReg rMode 1, .seq (.assign (const_eval' (by omega)))
    (.assign (const_eval' hw)), ?_, by simp, by simp, fun _ => rfl⟩
  exact (((Keeps.refl [rRes, rMode] [] s).setReg (by decide) _).setReg (by decide) _).dkeep
    (by decide) (by decide)

theorem answerTrue_exec {N w : ℕ} (H : SimpleGraph (Fin N)) (T : List (Fin N)) (hT : T.Nodup)
    (k : ℕ) (s : State) (hw : 4 * N + 4 < 2 ^ w) (h40 : s.regs 40 = N)
    (hT0 : s.arrs aT0 = T.map Fin.val) (hcr : CrossingAt H (T.rotate k) aQ aR s) :
    ∃ s' t, Exec w answerTrue s s' t ∧ t ≤ 210 + 120 * N ∧ DKeep s s' ∧ s'.regs rMode = 1 ∧
      s'.regs rRes = 1 ∧ CrossingAt H T aQ aR s' := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hcr₁⟩ := normProg_exec H T hT k s hw h40 hT0 hcr
  refine ⟨(s₁.setReg rRes 1).setReg rMode 1, _, .seq hex₁ (.seq (.assign (const_eval' (by omega)))
    (.assign (const_eval' (by omega)))), by simp only [Expr.cost]; omega, ?_, by simp, by simp, ?_⟩
  · exact (((hk₁.mono (R' := rRes :: rMode :: normRegs) (fun r h => List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ h)) (fun _ h => h)).setReg (by decide) _).setReg (by decide) _).dkeep
      (by decide) (by decide)
  · obtain ⟨x, y, z, t, Q, R, h, hQ, hR⟩ := hcr₁
    exact ⟨x, y, z, t, Q, R, h, hQ, hR⟩

/-! ### The split -/

/-- Push the frame of the instance and write the first subinstance. -/
def splitStep : Cmd := .seq pushFrame (childProg 1)

/-- After the separation test found that `P` separates: the completion step, then the answer or
the split. -/
def afterSep (comp : Cmd) : Cmd :=
  .seq comp (.ite (.op .eq (.reg rFlag) (.const 1)) answerTrue splitStep)

/-- After `findProg` found a `C`-path: the separation test, then the answer or `afterSep`. -/
def afterFind (comp : Cmd) : Cmd :=
  .seq sepProg (.ite (.op .eq (.reg rFound) (.const 1)) answerTrue (afterSep comp))

/-- **A solve round**: lines 2 to 10 of Algorithm 5.1 on the instance in memory. -/
def solveRound (comp : Cmd) : Cmd :=
  .seq (copyProg aT0 aCyc)
    (.seq findProg (.ite (.op .eq (.reg rFound) (.const 0)) answerFalse (afterFind comp)))

/-- The local situation after a split: the instance `(H, T)` was rotated to `a A b B` with the
`C`-path `P`, which separates; the completion step ran from a state `s₀` of the instance to the
state `s₁` with flag `0`, and wrote `F` and `P' = a m b`. These are the facts that the rest of the
round, the return rounds and the extraction step use. -/
structure SplitData {N : ℕ} (w : ℕ) (comp : Cmd) (c : ℕ) (H : SimpleGraph (Fin N))
    [DecidableRel H.Adj] (lists : Fin N → List ℕ) (T : List (Fin N)) (s₁ : State) (a b : Fin N)
    (A B m : List (Fin N)) (P : H.Walk a b) (F : List ℕ) (P' : (H ⊔ pairGraph N F).Walk a b) :
    Prop where
  rot : T.rotate (T.idxOf a) = a :: A ++ b :: B
  split : IsSplitInput H a b A B P
  run : ∃ s₀ t₁, InstanceAt H lists a b A B P s₀ ∧ (s₀.arrs aEnt).length < 2 ^ w ∧
    Exec w comp s₀ s₁ t₁
  flag : s₁.regs rFlag = 0
  inst : InstanceAt H lists a b A B P s₁
  arrF : s₁.arrs aF = F
  newEdges : IsNewEdgeList H P'.support F
  newPath : s₁.arrs aNewPath = P'.support.map Fin.val
  supp : P'.support = a :: m ++ [b]
  tpath : IsTPath (H ⊔ pairGraph N F) (a :: A ++ b :: B) P'
  sides : OnBothSides (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P'
  sep : Separates (H ⊔ pairGraph N F) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B}
  safe : IsSafe H (pairGraph N F) (a :: A ++ b :: B)
  lenF : F.length / 2 < P'.support.length
  arrT0 : s₁.arrs aT0 = T.map Fin.val
  recArrs : ∀ x, isRecordArr x → (s₁.arrs x).length ≤ c * (N + H.edgeFinset.card + 1)

/-- A walk between distinct vertices has a vertex list `a m b`. -/
theorem exists_support_eq {V : Type*} {G : SimpleGraph V} {a b : V} (P : G.Walk a b) (hab : a ≠ b) :
    ∃ m, P.support = a :: m ++ [b] := by
  have hne : P.support.tail ≠ [] := by
    intro h
    have hs := P.support_eq_cons
    rw [h] at hs
    have hl := P.getLast_support
    simp only [hs, List.getLast_singleton] at hl
    exact hab hl
  have h2 : P.support.tail.getLast hne = b := by
    rw [List.getLast_tail]; exact P.getLast_support
  refine ⟨P.support.tail.dropLast, ?_⟩
  calc P.support = a :: P.support.tail := P.support_eq_cons
    _ = a :: (P.support.tail.dropLast ++ [P.support.tail.getLast hne]) := by
        rw [List.dropLast_append_getLast]
    _ = a :: P.support.tail.dropLast ++ [b] := by rw [h2]; rfl

/-- `childProg_exec` with the list of new edges named. -/
theorem childProg_exec' {N w : ℕ} {H : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {Pv : List (Fin N)} {a b : Fin N} {A B m : List (Fin N)} (i : ℕ) {s : State} {F : List ℕ}
    (hFs : s.arrs aF = F)
    (hadj : IsAdjList H aStart aEnd aEnt lists s) (hF : IsNewEdgeList H Pv F)
    (P' : (H ⊔ pairGraph N F).Walk a b) (hm : P'.support = a :: m ++ [b])
    (hpath : s.arrs aNewPath = P'.support.map Fin.val)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val) (hlenA : s.regs rLenA = A.length)
    (hC : A.length + B.length + 2 ≤ N) (hmn : m.length + 2 ≤ N)
    (hAP : ∀ v ∈ A, v ∉ P'.support) (h40 : s.regs 40 = N) (hn : 4 * N + 4 < 2 ^ w)
    (hentw : (s.arrs aEnt).length < 2 ^ w) (hFw : F.length < 2 ^ w)
    (hcapw : totalAdjEntries lists + N * F.length < 2 ^ w) :
    ∃ s' t, Exec w (childProg i) s s' t ∧
      t ≤ 200 + 250 * N + 80 * totalAdjEntries lists + 90 * (N * F.length) ∧
      Keeps childRegs childArrs s s' ∧
      IsAdjList (subGraph (H ⊔ pairGraph N F) P'.support A i) aStart aEnd aEnt
        (restrictListFamily (sideFin (H ⊔ pairGraph N F) P'.support A i)
          (unionList lists F)) s' ∧
      (s'.arrs aEnt).length = totalAdjEntries lists + N * F.length ∧
      s'.arrs aCyc = (subCycle a b A B m i).map Fin.val := by
  subst hFs
  exact childProg_exec i hadj hF P' hm hpath hcyc hlenA hC hmn hAP h40 hn hentw hFw hcapw

/-! ### Lengths of frames -/

theorem length_encAll (l : List Arr) (s : State) :
    (encAll l s).length = (l.map fun x => (s.arrs x).length + 1).sum := by
  induction l with
  | nil => simp [encAll]
  | cons x l ih =>
    simp only [encAll, List.flatMap_cons, List.length_append, encArr, List.length_cons,
      List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- A bound on the number of entries of a frame. -/
theorem length_encAll_frame_le {N X Y : ℕ} (s : State) (h40 : (s.arrs aStart).length = N)
    (h41 : (s.arrs aEnd).length = N) (h42 : (s.arrs aEnt).length ≤ X)
    (h43 : (s.arrs aCyc).length ≤ N) (h44 : (s.arrs aPath).length ≤ N)
    (h47 : (s.arrs aF).length ≤ 2 * N + 1) (h48 : (s.arrs aNewPath).length ≤ N)
    (h55 : (s.arrs aT0).length ≤ N) (hrec : ∀ x, isRecordArr x → (s.arrs x).length ≤ Y) :
    (encAll frameArrs s).length ≤ 109 + 8 * N + X + 100 * Y := by
  rw [length_encAll, frameArrs, List.map_append, List.sum_append]
  have h1 : ((List.range' 200 100).map fun x => (s.arrs x).length + 1).sum ≤ 100 * (Y + 1) := by
    have := List.sum_le_card_nsmul ((List.range' 200 100).map fun x => (s.arrs x).length + 1)
      (Y + 1) (by
        intro v hv
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
        rw [List.mem_range'_1] at hx
        have := hrec x ⟨hx.1, by simpa using hx.2⟩
        omega)
    simpa using this
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-! ### The split step -/

/-- Subinstance `i` of a split is in memory. -/
def ChildAt {N : ℕ} (H : SimpleGraph (Fin N)) (lists : Fin N → List ℕ) (a b : Fin N)
    (A B m : List (Fin N)) (F : List ℕ) (P' : (H ⊔ pairGraph N F).Walk a b) (i : ℕ) (s : State) :
    Prop :=
  s.regs 40 = N ∧
  IsAdjList (subGraph (H ⊔ pairGraph N F) P'.support A i) aStart aEnd aEnt
    (restrictListFamily (sideFin (H ⊔ pairGraph N F) P'.support A i) (unionList lists F)) s ∧
  (s.arrs aEnt).length = totalAdjEntries lists + N * F.length ∧
  s.arrs aCyc = (subCycle a b A B m i).map Fin.val

theorem length_le_of_nodup {N : ℕ} {l : List (Fin N)} (h : l.Nodup) : l.length ≤ N := by
  have := h.length_le_card; simpa using this

namespace SplitData

variable {N w : ℕ} {comp : Cmd} {c : ℕ} {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]
  {lists : Fin N → List ℕ} {T : List (Fin N)} {s₁ : State} {a b : Fin N} {A B m : List (Fin N)}
  {P : H.Walk a b} {F : List ℕ} {P' : (H ⊔ pairGraph N F).Walk a b}

theorem lenC (hd : SplitData w comp c H lists T s₁ a b A B m P F P') :
    A.length + B.length + 2 ≤ N := by
  have := length_le_of_nodup hd.split.cyc.2.1; simp at this; omega

theorem lenP' (hd : SplitData w comp c H lists T s₁ a b A B m P F P') : P'.support.length ≤ N :=
  length_le_of_nodup hd.tpath.1.support_nodup

theorem lenM (hd : SplitData w comp c H lists T s₁ a b A B m P F P') : m.length + 2 ≤ N := by
  have := hd.lenP'; rw [hd.supp] at this; simp at this; omega

theorem lenF' (hd : SplitData w comp c H lists T s₁ a b A B m P F P') : F.length ≤ 2 * N + 1 := by
  have h1 := hd.lenF; have h2 := hd.lenP'; omega

theorem notMem_A (hd : SplitData w comp c H lists T s₁ a b A B m P F P') :
    ∀ v ∈ A, v ∉ P'.support := fun _ hv =>
  notMem_support_of_mem (IsCycleList.mono hd.split.cyc le_sup_left) hd.tpath (List.mem_append_left B hv)

/-- The frame of a split is not longer than `109 + 8 N + |aEnt| + 100 c (N + M + 1)`. -/
theorem length_frame_le (hd : SplitData w comp c H lists T s₁ a b A B m P F P') :
    (encAll frameArrs s₁).length ≤
      109 + 8 * N + (s₁.arrs aEnt).length + 100 * (c * (N + H.edgeFinset.card + 1)) := by
  have hT : T.length ≤ N := by
    have := length_le_of_nodup hd.split.cyc.2.1
    rw [← hd.rot, List.length_rotate] at this; exact this
  have hP : P.support.length ≤ N := length_le_of_nodup hd.split.path.1.support_nodup
  apply length_encAll_frame_le s₁ hd.inst.adj.1.1 hd.inst.adj.1.2.1 le_rfl
  · rw [hd.inst.cyc]; simp; have := hd.lenC; omega
  · rw [hd.inst.path]; simpa using hP
  · rw [hd.arrF]; exact hd.lenF'
  · rw [hd.newPath]; simpa using hd.lenP'
  · rw [hd.arrT0]; simpa using hT
  · exact hd.recArrs

end SplitData

/-- **The split step**: push the frame and write subinstance `1`. -/
theorem splitStep_exec {N w : ℕ} (hn : 4 * N + 4 < 2 ^ w) {comp : Cmd} {c : ℕ}
    {H : SimpleGraph (Fin N)} [DecidableRel H.Adj] {lists : Fin N → List ℕ} {T : List (Fin N)}
    {s₁ : State} {a b : Fin N} {A B m : List (Fin N)} {P : H.Walk a b} {F : List ℕ}
    {P' : (H ⊔ pairGraph N F).Walk a b} (hd : SplitData w comp c H lists T s₁ a b A B m P F P')
    (D R : List ℕ) (hh : s₁.arrs aHeap = D ++ R) (hp : s₁.regs rHp = D.length)
    (hR : (encAll frameArrs s₁).length + 3 ≤ R.length) (hDR : D.length + R.length < 2 ^ w)
    (hxw : ∀ x ∈ frameArrs, ∀ v ∈ s₁.arrs x, v < 2 ^ w)
    (hent : (s₁.arrs aEnt).length < 2 ^ w)
    (hcap : totalAdjEntries lists + N * (2 * N + 1) < 2 ^ w) :
    ∃ s' t, Exec w splitStep s₁ s' t ∧
      t ≤ 1800 + 250 * N + 80 * totalAdjEntries lists + 16 * (encAll frameArrs s₁).length +
        90 * (N * F.length) ∧
      ChildAt H lists a b A B m F P' 1 s' ∧ s'.regs rMode = s₁.regs rMode ∧ Low s₁ s' ∧
      s'.regs rHp = D.length + (frameOf s₁ A.length 1 D.length).length ∧
      s'.arrs aHeap = D ++ frameOf s₁ A.length 1 D.length ++
        R.drop (frameOf s₁ A.length 1 D.length).length := by
  have hlenA := hd.inst.lenA
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hp₂, hh₂⟩ := pushFrame_exec (by omega) D R s₁ hh hp hR hDR hxw
    (by rw [hlenA]; have := hd.lenC; omega)
  rw [hlenA] at hp₂ hh₂
  have ha : ∀ x, x ≠ aHeap → s₂.arrs x = s₁.arrs x := fun x hx => hk₂.2 x (by simp [hx])
  have hFw : F.length < 2 ^ w := by have := hd.lenF'; omega
  have hcapw : totalAdjEntries lists + N * F.length < 2 ^ w := by
    have := Nat.mul_le_mul_left N hd.lenF'; omega
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hadj₃, hent₃, hcyc₃⟩ := childProg_exec' (B := B) 1
    (by rw [ha _ (by decide)]; exact hd.arrF)
    (hd.inst.adj.of_arrs_eq (ha _ (by decide)) (ha _ (by decide)) (ha _ (by decide)))
    hd.newEdges P' hd.supp (by rw [ha _ (by decide)]; exact hd.newPath)
    (by rw [ha _ (by decide)]; exact hd.inst.cyc)
    (by rw [hk₂.1 rLenA (by decide)]; exact hlenA) hd.lenC hd.lenM hd.notMem_A
    (by rw [hk₂.1 40 (by decide)]; exact hd.inst.n) hn (by rw [ha _ (by decide)]; exact hent)
    hFw hcapw
  refine ⟨s₃, _, .seq hex₂ hex₃, by omega, ⟨?_, hadj₃, hent₃, hcyc₃⟩, ?_, ?_, ?_, ?_⟩
  · rw [hk₃.1 40 (by decide), hk₂.1 40 (by decide)]; exact hd.inst.n
  · rw [hk₃.1 rMode (by decide), hk₂.1 rMode (by decide)]
  · exact (hk₂.low (by decide) (by decide)).trans (hk₃.low (by decide) (by decide))
  · rw [hk₃.1 rHp (by decide)]; exact hp₂
  · rw [hk₃.2 aHeap (by decide)]; exact hh₂

/-- What the completion step keeps, by `CompSpec`. -/
theorem dkeep_of_comp {s s' : State} (hr : ∀ r < 300, r ≠ rFlag → s'.regs r = s.regs r)
    (ha : ∀ x < 200, x ≠ aQ → x ≠ aR → x ≠ aF → x ≠ aNewPath → s'.arrs x = s.arrs x) :
    DKeep s s' :=
  ⟨hr rHp (by decide) (by decide), ha aHeap (by decide) (by decide) (by decide) (by decide)
    (by decide), fun r hr' => hr r (show (r : ℕ) < 300 by omega)
      (fun h => by rw [h] at hr'; exact absurd hr' (by decide)),
    fun x hx => ha x (show (x : ℕ) < 200 by omega) (fun h => by rw [h] at hx; exact absurd hx (by decide))
      (fun h => by rw [h] at hx; exact absurd hx (by decide))
      (fun h => by rw [h] at hx; exact absurd hx (by decide))
      (fun h => by rw [h] at hx; exact absurd hx (by decide))⟩

theorem flag_eval {w : ℕ} (hw : 1 < 2 ^ w) {s : State} {v : ℕ} (hv : s.regs rFlag = v)
    (hv2 : v < 2) :
    (Expr.op .eq (.reg rFlag) (.const 1)).eval w s = some (if v = 1 then 1 else 0) :=
  eq_eval (reg_eval hv (by omega)) (const_eval' hw) hw

/-- **After the completion step**: the answer `True` (the completion step found a crossing), or
the split. -/
theorem afterSep_exec {comp : Cmd} {c c_w : ℕ} (hcomp : CompSpec comp c c_w) {N w : ℕ}
    (hn : 4 * N + 4 < 2 ^ w) {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]
    {lists : Fin N → List ℕ} (hwH : wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w)
    {T : List (Fin N)} {a b : Fin N} {A B : List (Fin N)} {P : H.Walk a b}
    (hrot : T.rotate (T.idxOf a) = a :: A ++ b :: B) (hT : T.Nodup)
    (hsplit : IsSplitInput H a b A B P) (D R : List ℕ) (s : State)
    (hinst : InstanceAt H lists a b A B P s) (hT0 : s.arrs aT0 = T.map Fin.val)
    (hh : s.arrs aHeap = D ++ R) (hp : s.regs rHp = D.length)
    (hR : 112 + 8 * N + (s.arrs aEnt).length + 100 * (c * (N + H.edgeFinset.card + 1)) ≤
      R.length)
    (hDR : D.length + R.length < 2 ^ w)
    (hxw : ∀ x ∈ frameArrs, ∀ v ∈ s.arrs x, v < 2 ^ w) (hent : (s.arrs aEnt).length < 2 ^ w)
    (hcap : totalAdjEntries lists + N * (2 * N + 1) < 2 ^ w) :
    ∃ s' t, Exec w (afterSep comp) s s' t ∧
      ((DKeep s s' ∧ s'.regs rMode = 1 ∧ s'.regs rRes = 1 ∧ CrossingAt H T aQ aR s' ∧
          t ≤ 220 + 120 * N + c * N * (N + H.edgeFinset.card + 1)) ∨
        (∃ (m : List (Fin N)) (F : List ℕ) (P' : (H ⊔ pairGraph N F).Walk a b) (s₁ : State),
          SplitData w comp c H lists T s₁ a b A B m P F P' ∧ ChildAt H lists a b A B m F P' 1 s' ∧
          s'.regs rMode = s.regs rMode ∧ Low s s' ∧
          s'.regs rHp = D.length + (frameOf s₁ A.length 1 D.length).length ∧
          s'.arrs aHeap = D ++ frameOf s₁ A.length 1 D.length ++
            R.drop (frameOf s₁ A.length 1 D.length).length ∧
          (∀ x ∈ frameArrs, ∀ v ∈ s₁.arrs x, v < 2 ^ w) ∧
          (s₁.arrs aEnt).length = (s.arrs aEnt).length ∧
          t ≤ c * P'.support.length * (N + H.edgeFinset.card + 1) + 1810 + 250 * N +
            80 * totalAdjEntries lists + 16 * (encAll frameArrs s₁).length +
            90 * (N * F.length))) := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, hr₁, ha₁, hrec₁, hout⟩ := hcomp N H lists a b A B P hsplit w hwH s hinst hent
  have hdk₁ := dkeep_of_comp hr₁ ha₁
  have h40₁ : s₁.regs 40 = N := by rw [hr₁ 40 (by decide) (by decide)]; exact hinst.n
  have hT0₁ : s₁.arrs aT0 = T.map Fin.val := by
    rw [ha₁ aT0 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hT0
  have hPN : P.support.length ≤ N := length_le_of_nodup hsplit.path.1.support_nodup
  rcases hout with ⟨hf, hcr, ht₁⟩ | ⟨hf, F, P', hF, hnp, hnew, htp, hsides, hsep', hsafe, hlenF, ht₁⟩
  · -- The completion step found a crossing.
    rw [← hrot] at hcr
    obtain ⟨s₂, t₂, hex₂, ht₂, hdk₂, hm₂, hr₂, hcr₂⟩ := answerTrue_exec H T hT (T.idxOf a) s₁ hn
      h40₁ hT0₁ hcr
    refine ⟨s₂, _, .seq hex₁ (.ite_true (flag_eval hw1 hf (by omega)) (by simp) hex₂),
      Or.inl ⟨hdk₁.trans hdk₂, hm₂, hr₂, hcr₂, ?_⟩⟩
    have : c * P.support.length * (N + H.edgeFinset.card + 1) ≤
        c * N * (N + H.edgeFinset.card + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hPN)
    simp only [Expr.cost]; omega
  · -- A completion: the split.
    have hab : a ≠ b := by
      have := hsplit.cyc.2.1
      intro h; subst h; simp at this
    obtain ⟨m, hm⟩ := exists_support_eq P' hab
    have hinst₁ : InstanceAt H lists a b A B P s₁ :=
      ⟨by rw [hr₁ rN (by decide) (by decide)]; exact hinst.n,
       by rw [hr₁ rLenA (by decide) (by decide)]; exact hinst.lenA,
       hinst.adj.of_arrs_eq (ha₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (ha₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (ha₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)),
       by rw [ha₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinst.cyc,
       by rw [ha₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinst.path⟩
    have hd : SplitData w comp c H lists T s₁ a b A B m P F P' :=
      ⟨hrot, hsplit, ⟨s, t₁, hinst, hent, hex₁⟩, hf, hinst₁, hF, hnew, hnp, hm, htp, hsides, hsep',
        hsafe, hlenF, hT0₁, hrec₁⟩
    have hent₁ : (s₁.arrs aEnt).length = (s.arrs aEnt).length := by
      rw [ha₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    have hxw₁ : ∀ x ∈ frameArrs, ∀ v ∈ s₁.arrs x, v < 2 ^ w := fun x hx =>
      hex₁.arrs_lt x (hxw x hx)
    have hfr := hd.length_frame_le
    obtain ⟨s₂, t₂, hex₂, ht₂, hch₂, hm₂, hlow₂, hp₂, hh₂⟩ := splitStep_exec hn hd D R
      (by rw [hdk₁.2.1]; exact hh) (by rw [hdk₁.1]; exact hp) (by omega) hDR hxw₁
      (by omega) hcap
    refine ⟨s₂, _, .seq hex₁ (.ite_false (by rw [flag_eval hw1 hf (by omega)]; rfl) hex₂),
      Or.inr ⟨m, F, P', s₁, hd, hch₂, ?_, hdk₁.2.2.trans hlow₂, hp₂, hh₂, hxw₁, hent₁, ?_⟩⟩
    · rw [hm₂, hr₁ rMode (by decide) (by decide)]
    · simp only [Expr.cost]; omega

theorem found_eval {w : ℕ} (hw : 1 < 2 ^ w) {s : State} {v : ℕ} (hv : s.regs rFound = v)
    (hv2 : v < 2) (k : ℕ) (hk : k < 2) :
    (Expr.op .eq (.reg rFound) (.const k)).eval w s = some (if v = k then 1 else 0) :=
  eq_eval (reg_eval hv (by omega)) (const_eval' (by omega)) hw

/-- **After a `C`-path was found**: the separation test, then the answer `True` or the rest of the
round. -/
theorem afterFind_exec {comp : Cmd} {c c_w : ℕ} (hcomp : CompSpec comp c c_w) {N w : ℕ}
    (hn : 4 * N + 4 < 2 ^ w) {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]
    {lists : Fin N → List ℕ} (hwH : wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w)
    {T : List (Fin N)} (hcycT : IsCycleList H T) {a b : Fin N} {A B : List (Fin N)}
    {P : H.Walk a b} (hrot : T.rotate (T.idxOf a) = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ [])
    (hTP : IsTPath H T P) (D R : List ℕ) (s : State)
    (hinst : InstanceAt H lists a b A B P s) (hT0 : s.arrs aT0 = T.map Fin.val)
    (hh : s.arrs aHeap = D ++ R) (hp : s.regs rHp = D.length)
    (hR : 112 + 8 * N + (s.arrs aEnt).length + 100 * (c * (N + H.edgeFinset.card + 1)) ≤
      R.length)
    (hDR : D.length + R.length < 2 ^ w)
    (hxw : ∀ x ∈ frameArrs, ∀ v ∈ s.arrs x, v < 2 ^ w) (hent : (s.arrs aEnt).length < 2 ^ w)
    (hcap : totalAdjEntries lists + N * (2 * N + 1) < 2 ^ w) :
    ∃ s' t, Exec w (afterFind comp) s s' t ∧
      ((DKeep s s' ∧ s'.regs rMode = 1 ∧ s'.regs rRes = 1 ∧ CrossingAt H T aQ aR s' ∧
          t ≤ 300 + 240 * N + 29 * totalAdjEntries lists + c * N * (N + H.edgeFinset.card + 1)) ∨
        (∃ (m : List (Fin N)) (F : List ℕ) (P' : (H ⊔ pairGraph N F).Walk a b) (s₁ : State),
          SplitData w comp c H lists T s₁ a b A B m P F P' ∧ ChildAt H lists a b A B m F P' 1 s' ∧
          s'.regs rMode = s.regs rMode ∧ Low s s' ∧
          s'.regs rHp = D.length + (frameOf s₁ A.length 1 D.length).length ∧
          s'.arrs aHeap = D ++ frameOf s₁ A.length 1 D.length ++
            R.drop (frameOf s₁ A.length 1 D.length).length ∧
          (∀ x ∈ frameArrs, ∀ v ∈ s₁.arrs x, v < 2 ^ w) ∧
          (s₁.arrs aEnt).length = (s.arrs aEnt).length ∧
          t ≤ c * P'.support.length * (N + H.edgeFinset.card + 1) + 1900 + 370 * N +
            109 * totalAdjEntries lists + 16 * (encAll frameArrs s₁).length +
            90 * (N * F.length))) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hcyc' : IsCycleList H (a :: A ++ b :: B) := hrot ▸ hcycT.rotate _
  have hTP' : IsTPath H (a :: A ++ b :: B) P := by
    rw [← hrot]; exact (isTPath_congr (fun x => List.mem_rotate.symm) P).mp hTP
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hres⟩ := sepProg_exec H lists A B P hcyc'.2.1 hTP' hn s
    hinst.cyc hinst.path hinst.lenA hinst.n hinst.adj hent
  have hdk₁ : DKeep s s₁ := hk₁.dkeep (by decide) (by decide)
  have hT0₁ : s₁.arrs aT0 = T.map Fin.val := by rw [hk₁.2 aT0 (by decide)]; exact hT0
  have hT : T.Nodup := hcycT.2.1
  rcases hres with ⟨h0, hsep⟩ | ⟨h1, hcr⟩
  · -- `P` separates: the completion step.
    have hinst₁ : InstanceAt H lists a b A B P s₁ :=
      ⟨by rw [hk₁.1 rN (by decide)]; exact hinst.n, by rw [hk₁.1 rLenA (by decide)]; exact hinst.lenA,
       hinst.adj.of_arrs_eq (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)),
       by rw [hk₁.2 _ (by decide)]; exact hinst.cyc, by rw [hk₁.2 _ (by decide)]; exact hinst.path⟩
    have hent₁ : (s₁.arrs aEnt).length = (s.arrs aEnt).length := by rw [hk₁.2 _ (by decide)]
    obtain ⟨s₂, t₂, hex₂, hout⟩ := afterSep_exec hcomp hn hwH hrot hT ⟨hcyc', hA, hB, hTP', hsep⟩
      D R s₁ hinst₁ hT0₁ (by rw [hdk₁.2.1]; exact hh) (by rw [hdk₁.1]; exact hp) (by omega) hDR
      (fun x hx => hex₁.arrs_lt x (hxw x hx)) (by omega) hcap
    refine ⟨s₂, _, .seq hex₁ (.ite_false (by rw [found_eval hw1 h0 (by omega) 1 (by omega)]; rfl)
      hex₂), ?_⟩
    rcases hout with ⟨hdk₂, hm₂, hr₂, hcr₂, ht₂⟩ |
      ⟨m, F, P', s₃, hd, hch, hm₂, hlow, hp₂, hh₂, hxw₃, hent₃, ht₂⟩
    · exact Or.inl ⟨hdk₁.trans hdk₂, hm₂, hr₂, hcr₂, by simp only [Expr.cost]; omega⟩
    · refine Or.inr ⟨m, F, P', s₃, hd, hch, ?_, hdk₁.2.2.trans hlow, hp₂, hh₂, hxw₃, ?_, ?_⟩
      · rw [hm₂, hk₁.1 rMode (by decide)]
      · rw [hent₃, hent₁]
      · simp only [Expr.cost]; omega
  · -- A crossing: line 7.
    rw [← hrot] at hcr
    obtain ⟨s₂, t₂, hex₂, ht₂, hdk₂, hm₂, hr₂, hcr₂⟩ := answerTrue_exec H T hT (T.idxOf a) s₁ hn
      (by rw [hk₁.1 40 (by decide)]; exact hinst.n) hT0₁ hcr
    refine ⟨s₂, _, .seq hex₁ (.ite_true (found_eval hw1 h1 (by omega) 1 (by omega)) (by simp)
      hex₂), Or.inl ⟨hdk₁.trans hdk₂, hm₂, hr₂, hcr₂, ?_⟩⟩
    simp only [Expr.cost]; omega

/-- The steps of a round that answers at once, without the completion step's share. -/
def leafCost (N M : ℕ) : ℕ := 2500 + 700 * N + 400 * M

/-- The outcome of a solve round: it answered (`rRes = 0` with no crossing, or `rRes = 1` with a
crossing of `T` in `aQ`, `aR`), keeping the heap; or it split the instance, pushed the frame and
wrote subinstance `1` into memory. -/
def SolveOut (w : ℕ) (comp : Cmd) (c : ℕ) {N : ℕ} (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (lists : Fin N → List ℕ) (T : List (Fin N)) (D R : List ℕ) (s s' : State) (t : ℕ) : Prop :=
  (DKeep s s' ∧ s'.regs rMode = 1 ∧
    ((s'.regs rRes = 0 ∧ ¬ IsCrossed H T ∧ t ≤ leafCost N (totalAdjEntries lists)) ∨
      (s'.regs rRes = 1 ∧ CrossingAt H T aQ aR s' ∧
        t ≤ leafCost N (totalAdjEntries lists) + c * N * (N + H.edgeFinset.card + 1)))) ∨
  (∃ (a b : Fin N) (A B m : List (Fin N)) (P : H.Walk a b) (F : List ℕ)
      (P' : (H ⊔ pairGraph N F).Walk a b) (s₁ : State),
    SplitData w comp c H lists T s₁ a b A B m P F P' ∧ ChildAt H lists a b A B m F P' 1 s' ∧
    s'.regs rMode = 0 ∧ Low s s' ∧
    s'.regs rHp = D.length + (frameOf s₁ A.length 1 D.length).length ∧
    s'.arrs aHeap = D ++ frameOf s₁ A.length 1 D.length ++
      R.drop (frameOf s₁ A.length 1 D.length).length ∧
    (∀ x ∈ frameArrs, ∀ v ∈ s₁.arrs x, v < 2 ^ w) ∧
    (s₁.arrs aEnt).length = (s.arrs aEnt).length ∧
    t ≤ leafCost N (totalAdjEntries lists) + c * P'.support.length * (N + H.edgeFinset.card + 1) +
      16 * (encAll frameArrs s₁).length + 90 * (N * F.length))

/-- **A solve round.** On the instance `(H, T)` in memory, with `T` a cycle of `H`, the round
answers or splits (`SolveOut`). -/
theorem solveRound_exec {comp : Cmd} {c c_w : ℕ} (hcomp : CompSpec comp c c_w) {N w : ℕ}
    (hn : 4 * N + 4 < 2 ^ w) {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]
    {lists : Fin N → List ℕ} (hwH : wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w)
    {T : List (Fin N)} (hcycT : IsCycleList H T) (D R : List ℕ) (s : State)
    (h40 : s.regs 40 = N) (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hcyc : s.arrs aCyc = T.map Fin.val) (hmode : s.regs rMode = 0)
    (hh : s.arrs aHeap = D ++ R) (hp : s.regs rHp = D.length)
    (hR : 112 + 8 * N + (s.arrs aEnt).length + 100 * (c * (N + H.edgeFinset.card + 1)) ≤
      R.length)
    (hDR : D.length + R.length < 2 ^ w)
    (hxw : ∀ x ∈ frameArrs, ∀ v ∈ s.arrs x, v < 2 ^ w) (hent : (s.arrs aEnt).length < 2 ^ w)
    (hcap : totalAdjEntries lists + N * (2 * N + 1) < 2 ^ w) :
    ∃ s' t, Exec w (solveRound comp) s s' t ∧ SolveOut w comp c H lists T D R s s' t := by
  have hw1 : 1 < 2 ^ w := by omega
  have hT : T.Nodup := hcycT.2.1
  have hTN : T.length ≤ N := length_le_of_nodup hT
  -- Keep the cycle as given.
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hT0₁⟩ := copyProg_exec (dst := aT0) (src := aCyc) (by decide)
    (T.map Fin.val) s hw1 (by simp; omega) (fun x hx => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; have := v.2; omega) hcyc
  -- Lines 2 and 5.
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hres⟩ := findProg_exec H lists T hT hn s₁
    (by rw [hk₁.2 _ (by decide)]; exact hcyc) (by rw [hk₁.1 40 (by decide)]; exact h40)
    (hadj.of_arrs_eq (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)))
    (by rw [hk₁.2 _ (by decide)]; exact hent)
  have hdk₂ : DKeep s s₂ := (hk₁.dkeep (by decide) (by decide)).trans (hk₂.dkeep (by decide)
    (by decide))
  have hxw₂ : ∀ x ∈ frameArrs, ∀ v ∈ s₂.arrs x, v < 2 ^ w := fun x hx =>
    hex₂.arrs_lt x (hex₁.arrs_lt x (hxw x hx))
  have hT0₂ : s₂.arrs aT0 = T.map Fin.val := by rw [hk₂.2 _ (by decide)]; exact hT0₁
  have hent₂ : (s₂.arrs aEnt).length = (s.arrs aEnt).length := by
    rw [hk₂.2 _ (by decide), hk₁.2 _ (by decide)]
  rcases hres with ⟨h0, hno⟩ | ⟨h1, a, b, A, B, P, hrot, hA, hB, hTP, hcyc₂, hpath₂, hlen₂⟩
  · -- Line 3.
    obtain ⟨s₃, hex₃, hdk₃, hm₃, hr₃, -⟩ := answerFalse_exec hw1 s₂
    refine ⟨s₃, _, .seq hex₁ (.seq hex₂ (.ite_true (found_eval hw1 h0 (by omega) 0 (by omega))
      (by simp) hex₃)), Or.inl ⟨hdk₂.trans hdk₃, hm₃, Or.inl ⟨hr₃, hno, ?_⟩⟩⟩
    simp only [List.length_map] at ht₁; simp only [Expr.cost, leafCost]; omega
  · have hinst : InstanceAt H lists a b A B P s₂ :=
      ⟨by rw [hk₂.1 40 (by decide), hk₁.1 40 (by decide)]; exact h40, hlen₂,
       hadj.of_arrs_eq (by rw [hk₂.2 _ (by decide), hk₁.2 _ (by decide)])
        (by rw [hk₂.2 _ (by decide), hk₁.2 _ (by decide)])
        (by rw [hk₂.2 _ (by decide), hk₁.2 _ (by decide)]), hcyc₂, hpath₂⟩
    obtain ⟨s₃, t₃, hex₃, hout⟩ := afterFind_exec hcomp hn hwH hcycT hrot hA hB hTP D R s₂ hinst
      hT0₂ (by rw [hdk₂.2.1]; exact hh) (by rw [hdk₂.1]; exact hp) (by rw [hent₂]; exact hR) hDR
      hxw₂ (by rw [hent₂]; exact hent) hcap
    have hex : Exec w (solveRound comp) s s₃ (t₁ + (t₂ + (3 + t₃))) :=
      .seq hex₁ (.seq hex₂ (.ite_false (by rw [found_eval hw1 h1 (by omega) 0 (by omega)]; rfl)
        hex₃))
    refine ⟨s₃, _, hex, ?_⟩
    rcases hout with ⟨hdk₃, hm₃, hr₃, hcr₃, ht₃⟩ |
      ⟨m, F, P', s₄, hd, hch, hm₃, hlow, hp₃, hh₃, hxw₄, hent₄, ht₃⟩
    · exact Or.inl ⟨hdk₂.trans hdk₃, hm₃, Or.inr ⟨hr₃, hcr₃, by
        simp only [List.length_map] at ht₁; simp only [leafCost]; omega⟩⟩
    · refine Or.inr ⟨a, b, A, B, m, P, F, P', s₄, hd, hch, ?_, hdk₂.2.2.trans hlow, hp₃, hh₃,
        hxw₄, by rw [hent₄, hent₂], ?_⟩
      · rw [hm₃, hk₂.1 rMode (by decide), hk₁.1 rMode (by decide)]; exact hmode
      · simp only [List.length_map] at ht₁; simp only [leafCost]; omega

end GraphMinor.Compute.TwoPaths
