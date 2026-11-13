module

public import GraphMinor.Compute.TwoPathsHeap
public import GraphMinor.Compute.TwoPathsSep
public import GraphMinor.Compute.WhileRounds

/-!
# The driver of Algorithm 5.1: the program

Algorithm 5.1 of Humeau and Pous (arXiv:2505.16431v2, Section 5.1, page 18) is recursive:

```
 1: procedure 2DP(G, C)
 2:     if there are no C-paths between non-consecutive vertices of C then
 3:         return False
 4:     else
 5:         P ← a C-path between non-consecutive vertices of C
 6:         if P does not separate C in G then
 7:             return True
 8:         else
 9:             G, P ← P_completion(G, C, P)
10:             G_i, C_i ← two subinstances induced by G, P and C
11:             return (2DP(G_1,C_1) ∨ 2DP(G_2,C_2))
```

A Word RAM program has no recursion, so the driver is one loop with an explicit stack of *frames*
on the heap (`TwoPathsHeap.lean`). Register `rMode` says what the loop does next: `0` solve the
instance in memory, `1` return the answer `rRes` to the frame on top of the stack, `2` stop.

* A *solve round* (`solveRound`) runs lines 2 to 10 on the instance in memory. When it answers at
  once (lines 3 and 7, or a crossing found by the completion step), it writes the answer and turns
  to mode `1`. Otherwise it pushes a frame that holds the instance, the output of the completion
  step and the side `1` (`pushFrame`), and writes the first subinstance into memory.
* A *return round* (`returnRound`) reads the frame on top of the stack (`loadTop`). If the answer
  is a crossing of the subinstance, the extraction step turns it into a crossing of the instance
  of the frame, and the frame is popped. If the answer is `False` for side `1`, the frame is kept
  with side `2` and the second subinstance is written into memory (mode `0`). If it is `False` for
  side `2`, the frame is popped: both calls of line 11 answered `False`. When the stack is empty,
  the loop stops.

A frame is the list of the arrays `frameArrs` (each saved as its length and its entries), then
three entries: the length of `A`, the side, and the start of the frame, which is the heap pointer
after a pop.

This file defines the programs and proves the two programs on frames: `pushFrame_exec` and
`loadTop_exec`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-! ### Registers and frames -/

/-- The mode of the loop: `0` solve, `1` return, `2` stop. -/
abbrev rMode : Reg := 130
/-- The answer of the last instance solved: `0` for no crossing, `1` for a crossing in `aQ`, `aR`. -/
abbrev rRes : Reg := 131
/-- The start of the frame being pushed. -/
abbrev rStart : Reg := 132
/-- The heap pointer before the frame on top is read. -/
abbrev rTop : Reg := 133
/-- The side stored in the frame on top. -/
abbrev rTopSide : Reg := 134

/-- The arrays of a frame: the instance (adjacency lists, the cycle `a A b B`, the path `P`), the
output `F`, `P'` of the completion step, the cycle `T` as given (`aT0`), and the arrays
`200 … 299` that the completion step leaves for the extraction step. -/
def frameArrs : List Arr := [aStart, aEnd, aEnt, aCyc, aPath, aF, aNewPath, aT0] ++
  List.range' 200 100

/-- The entries of a frame: the arrays `frameArrs` of `s`, then `|A|`, the side and the start. -/
def frameOf (s : State) (lenA side p : ℕ) : List ℕ := encAll frameArrs s ++ [lenA, side, p]

theorem mem_frameArrs {x : ℕ} : x ∈ frameArrs ↔
    x = 40 ∨ x = 41 ∨ x = 42 ∨ x = 43 ∨ x = 44 ∨ x = 47 ∨ x = 48 ∨ x = 55 ∨ (200 ≤ x ∧ x < 300) := by
  simp only [frameArrs, aStart, aEnd, aEnt, aCyc, aPath, aF, aNewPath, aT0, List.mem_append,
    List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem frameArrs_nodup : frameArrs.Nodup := by
  rw [frameArrs, List.nodup_append]
  refine ⟨by decide, List.nodup_range', ?_⟩
  intro x hx y hy
  simp only [aStart, aEnd, aEnt, aCyc, aPath, aF, aNewPath, aT0, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  simp only [List.mem_range'_1] at hy
  rintro rfl
  rcases hx with h|h|h|h|h|h|h|h <;> (subst h; simp at hy)

theorem aHeap_notMem_frameArrs : aHeap ∉ frameArrs := by
  rw [mem_frameArrs]; simp only [aHeap]; omega

theorem length_frameArrs : frameArrs.length = 108 := by simp [frameArrs]

theorem le_of_mem_frameArrs {x : ℕ} (hx : x ∈ frameArrs) : 40 ≤ x := by
  rw [mem_frameArrs] at hx
  omega

/-! ### Pushing a frame -/

/-- Push the frame of the instance in memory, with side `1`. -/
def pushFrame : Cmd :=
  .seq (.assign rStart (.reg rHp))
    (.seq (saveAll frameArrs)
      (.seq (.write aHeap (.reg rHp) (.reg rLenA))
        (.seq (.write aHeap (.op .add (.reg rHp) (.const 1)) (.const 1))
          (.seq (.write aHeap (.op .add (.reg rHp) (.const 2)) (.reg rStart))
            (.assign rHp (.op .add (.reg rHp) (.const 3)))))))

theorem set_append_cons (L R : List ℕ) (x v : ℕ) : (L ++ x :: R).set L.length v = L ++ v :: R := by
  induction L with
  | nil => simp
  | cons y L ih => simp [ih]

/-- Changing the side entry of a frame on the heap. -/
theorem set_frameOf (D E : List ℕ) (s : State) (lenA side p v : ℕ) :
    (D ++ frameOf s lenA side p ++ E).set (D.length + (encAll frameArrs s).length + 1) v =
      D ++ frameOf s lenA v p ++ E := by
  have h : D ++ frameOf s lenA side p ++ E =
      (D ++ encAll frameArrs s ++ [lenA]) ++ side :: (p :: E) := by simp [frameOf]
  rw [h, show D.length + (encAll frameArrs s).length + 1 =
    (D ++ encAll frameArrs s ++ [lenA]).length by simp; omega, set_append_cons]
  simp [frameOf]

theorem length_frameOf (s : State) (lenA side p : ℕ) :
    (frameOf s lenA side p).length = (encAll frameArrs s).length + 3 := by
  simp [frameOf]

theorem encAll_congr {l : List Arr} {s s' : State} (h : ∀ x ∈ l, s'.arrs x = s.arrs x) :
    encAll l s' = encAll l s := by
  simp only [encAll]
  exact List.flatMap_congr fun x hx => by rw [h x hx]

theorem frameOf_congr {s s' : State} (h : ∀ x ∈ frameArrs, s'.arrs x = s.arrs x)
    (lenA side p : ℕ) : frameOf s' lenA side p = frameOf s lenA side p := by
  simp [frameOf, encAll_congr h]

/-- **Pushing a frame.** -/
theorem pushFrame_exec {w : ℕ} (hw : 1 < 2 ^ w) (D R : List ℕ) (s : State)
    (hh : s.arrs aHeap = D ++ R) (hp : s.regs rHp = D.length)
    (hR : (encAll frameArrs s).length + 3 ≤ R.length) (hDR : D.length + R.length < 2 ^ w)
    (hxw : ∀ x ∈ frameArrs, ∀ v ∈ s.arrs x, v < 2 ^ w) (hA : s.regs rLenA < 2 ^ w) :
    ∃ s' t, Exec w pushFrame s s' t ∧ t ≤ 1600 + 16 * (encAll frameArrs s).length ∧
      Keeps [rStart, rHp, rI4, rLen] [aHeap] s s' ∧
      s'.regs rHp = D.length + (frameOf s (s.regs rLenA) 1 D.length).length ∧
      s'.arrs aHeap = D ++ frameOf s (s.regs rLenA) 1 D.length ++
        R.drop (frameOf s (s.regs rLenA) 1 D.length).length := by
  set enc := encAll frameArrs s with henc
  set s₁ := s.setReg rStart D.length with hs₁
  have hex₁ : Exec w (.assign rStart (.reg rHp)) s s₁ (1 + 1) :=
    .assign (reg_eval hp (by omega))
  have henc₁ : encAll frameArrs s₁ = enc := rfl
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hp₂, hh₂⟩ := saveAll_exec hw frameArrs aHeap_notMem_frameArrs D R
    s₁ (by simpa [s₁] using hh) (by simp [s₁, hp]) (by rw [henc₁]; omega) hDR
    (fun x hx v hv => hxw x hx v (by simpa [s₁] using hv))
  rw [henc₁] at ht₂ hp₂ hh₂
  obtain ⟨x₁, x₂, x₃, R₂, hR₂⟩ : ∃ x₁ x₂ x₃ R₂, R.drop enc.length = x₁ :: x₂ :: x₃ :: R₂ := by
    have hl : 3 ≤ (R.drop enc.length).length := by simp; omega
    match h : R.drop enc.length, hl with
    | x₁ :: x₂ :: x₃ :: R₂, _ => exact ⟨x₁, x₂, x₃, R₂, rfl⟩
  have hrS : s₂.regs rStart = D.length := by rw [hk₂.1 rStart (by decide)]; simp [s₁]
  have hrA : s₂.regs rLenA = s.regs rLenA := by rw [hk₂.1 rLenA (by decide)]; simp [s₁]
  have hlen : D.length + enc.length + 3 ≤ D.length + R.length := by omega
  -- The three writes.
  set s₃ := s₂.writeArr aHeap (D.length + enc.length) (s.regs rLenA) with hs₃
  have hex₃ : Exec w (.write aHeap (.reg rHp) (.reg rLenA)) s₂ s₃ (1 + 1 + 1) :=
    .write (reg_eval hp₂ (by omega)) (reg_eval hrA hA) (by rw [hh₂, hR₂]; simp)
  have hh₃ : s₃.arrs aHeap = (D ++ enc ++ [s.regs rLenA]) ++ x₂ :: x₃ :: R₂ := by
    simp only [s₃, State.writeArr_arrs_self, hh₂, hR₂]
    rw [show D.length + enc.length = (D ++ enc).length by simp, set_append_cons]; simp
  set s₄ := s₃.writeArr aHeap (D.length + enc.length + 1) 1 with hs₄
  have hex₄ : Exec w (.write aHeap (.op .add (.reg rHp) (.const 1)) (.const 1)) s₃ s₄
      (1 + 1 + 1 + 1 + 1) :=
    .write (add_eval (reg_eval (by simp [s₃, hp₂]) (by omega)) (const_eval' (by omega))
      (by omega)) (const_eval' hw) (by rw [hh₃]; simp; omega)
  have hh₄ : s₄.arrs aHeap = (D ++ enc ++ [s.regs rLenA, 1]) ++ x₃ :: R₂ := by
    simp only [s₄, State.writeArr_arrs_self, hh₃]
    rw [show D.length + enc.length + 1 = (D ++ enc ++ [s.regs rLenA]).length by simp; omega,
      set_append_cons]; simp
  set s₅ := s₄.writeArr aHeap (D.length + enc.length + 2) D.length with hs₅
  have hex₅ : Exec w (.write aHeap (.op .add (.reg rHp) (.const 2)) (.reg rStart)) s₄ s₅
      (1 + 1 + 1 + 1 + 1) :=
    .write (add_eval (reg_eval (by simp [s₄, s₃, hp₂]) (by omega)) (const_eval' (by omega))
      (by omega)) (reg_eval (by simp [s₄, s₃, hrS]) (by omega)) (by rw [hh₄]; simp; omega)
  have hh₅ : s₅.arrs aHeap = (D ++ enc ++ [s.regs rLenA, 1, D.length]) ++ R₂ := by
    simp only [s₅, State.writeArr_arrs_self, hh₄]
    rw [show D.length + enc.length + 2 = (D ++ enc ++ [s.regs rLenA, 1]).length by simp; omega,
      set_append_cons]; simp
  set s₆ := s₅.setReg rHp (D.length + enc.length + 3) with hs₆
  have hex₆ : Exec w (.assign rHp (.op .add (.reg rHp) (.const 3))) s₅ s₆ (1 + 1 + 1 + 1) :=
    .assign (add_eval (reg_eval (by simp [s₅, s₄, s₃, hp₂]) (by omega)) (const_eval' (by omega))
      (by omega))
  have hfl : (frameOf s (s.regs rLenA) 1 D.length).length = enc.length + 3 := length_frameOf ..
  refine ⟨s₆, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), ?_, ?_, ?_, ?_⟩
  · rw [length_frameArrs] at ht₂; omega
  · refine ((((((Keeps.refl _ _ s).setReg (by decide) _).trans hk₂ (by decide) (by decide)).writeArr
      (by decide) _ _).writeArr (by decide) _ _).writeArr (by decide) _ _).setReg (by decide) _
  · rw [hfl]; simp only [s₆, State.setReg_regs_self]; omega
  · have hd : R.drop (frameOf s (s.regs rLenA) 1 D.length).length = R₂ := by
      have h3 : (R.drop enc.length).drop 3 = R₂ := by rw [hR₂]; rfl
      rw [List.drop_drop] at h3
      rw [hfl]; exact h3
    rw [hd]; simp only [s₆, State.setReg_arrs, hh₅, frameOf, List.append_assoc, ← henc]

/-! ### Reading the frame on top -/

/-- Read the frame on top of the stack: `|A|` into `rLenA`, the side into `rTopSide`, the arrays back
into memory, and set the heap pointer to the start of the frame (a pop). The old pointer is kept in
`rTop`. -/
def loadTop : Cmd :=
  .seq (.assign rTop (.reg rHp))
    (.seq (.assign rLenA (.read aHeap (.op .sub (.reg rTop) (.const 3))))
      (.seq (.assign rTopSide (.read aHeap (.op .sub (.reg rTop) (.const 2))))
        (.seq (.assign rHp (.read aHeap (.op .sub (.reg rTop) (.const 1))))
          (.seq (loadAll frameArrs)
            (.assign rHp (.read aHeap (.op .sub (.reg rTop) (.const 1))))))))

/-- **Reading the frame on top.** -/
theorem loadTop_exec {w : ℕ} (hw : 1 < 2 ^ w) (D E : List ℕ) (s₁ s : State) (lenA side : ℕ)
    (hh : s.arrs aHeap = D ++ frameOf s₁ lenA side D.length ++ E)
    (hp : s.regs rHp = D.length + (frameOf s₁ lenA side D.length).length)
    (hlt : (D ++ frameOf s₁ lenA side D.length ++ E).length < 2 ^ w)
    (hhw : ∀ v ∈ s.arrs aHeap, v < 2 ^ w) :
    ∃ s' t, Exec w loadTop s s' t ∧ t ≤ 1900 + 16 * (encAll frameArrs s₁).length ∧
      Keeps [rTop, rLenA, rTopSide, rHp, rI4, rLen] frameArrs s s' ∧
      s'.regs rTop = D.length + (frameOf s₁ lenA side D.length).length ∧ s'.regs rLenA = lenA ∧
      s'.regs rTopSide = side ∧ s'.regs rHp = D.length ∧
      ∀ x ∈ frameArrs, s'.arrs x = s₁.arrs x := by
  have hfl : (frameOf s₁ lenA side D.length).length = (encAll frameArrs s₁).length + 3 :=
    length_frameOf ..
  have hL : D ++ frameOf s₁ lenA side D.length ++ E =
      D ++ encAll frameArrs s₁ ++ (lenA :: side :: D.length :: E) := by simp [frameOf]
  rw [hL] at hh hlt
  rw [hfl] at hp
  set enc := encAll frameArrs s₁ with henc
  set L := D ++ enc ++ (lenA :: side :: D.length :: E) with hLdef
  have hhw' : ∀ v ∈ L, v < 2 ^ w := fun v hv => hhw v (by rw [hh]; exact hv)
  have hLl : L.length = D.length + enc.length + 3 + E.length := by simp [L]; omega
  have hg0 : L[D.length + enc.length]? = some lenA := by
    simp only [L]; rw [List.getElem?_append_right (by simp)]; simp
  have hg1 : L[D.length + enc.length + 1]? = some side := by
    simp only [L]; rw [List.getElem?_append_right (by simp)]
    simp [show D.length + enc.length + 1 - (D.length + enc.length) = 1 by omega]
  have hg2 : L[D.length + enc.length + 2]? = some D.length := by
    simp only [L]; rw [List.getElem?_append_right (by simp)]
    simp [show D.length + enc.length + 2 - (D.length + enc.length) = 2 by omega]
  have hv0 : lenA < 2 ^ w := hhw' _ (List.mem_of_getElem? hg0)
  have hv1 : side < 2 ^ w := hhw' _ (List.mem_of_getElem? hg1)
  have hv2 : D.length < 2 ^ w := hhw' _ (List.mem_of_getElem? hg2)
  set top := D.length + enc.length + 3 with htop
  have hrT : ∀ st : State, st.regs rTop = top → ∀ j, j ≤ 3 →
      (Expr.op .sub (.reg rTop) (.const j)).eval w st = some (top - j) := fun st h1 j hj =>
    sub_eval (reg_eval h1 (by omega)) (const_eval' (by omega))
  set s₂ := s.setReg rTop top with hs₂
  have hex₂ : Exec w (.assign rTop (.reg rHp)) s s₂ (1 + 1) :=
    .assign (reg_eval hp (by omega))
  set s₃ := s₂.setReg rLenA lenA with hs₃
  have hex₃ : Exec w (.assign rLenA (.read aHeap (.op .sub (.reg rTop) (.const 3)))) s₂ s₃
      (1 + 1 + 1 + 1 + 1) :=
    .assign (readEnd_eval (X := aHeap) hh (hrT s₂ (by simp [s₂]) 3 (by omega))
      (by rw [show top - 3 = D.length + enc.length by omega]; exact hg0) hv0)
  set s₄ := s₃.setReg rTopSide side with hs₄
  have hex₄ : Exec w (.assign rTopSide (.read aHeap (.op .sub (.reg rTop) (.const 2)))) s₃ s₄
      (1 + 1 + 1 + 1 + 1) :=
    .assign (readEnd_eval (X := aHeap) hh (hrT s₃ (by simp [s₃, s₂]) 2 (by omega))
      (by rw [show top - 2 = D.length + enc.length + 1 by omega]; exact hg1) hv1)
  set s₅ := s₄.setReg rHp D.length with hs₅
  have hex₅ : Exec w (.assign rHp (.read aHeap (.op .sub (.reg rTop) (.const 1)))) s₄ s₅
      (1 + 1 + 1 + 1 + 1) :=
    .assign (readEnd_eval (X := aHeap) hh (hrT s₄ (by simp [s₄, s₃, s₂]) 1 (by omega))
      (by rw [show top - 1 = D.length + enc.length + 2 by omega]; exact hg2) hv2)
  have hh₅ : s₅.arrs aHeap = D ++ encLists (frameArrs.map s₁.arrs) ++
      (lenA :: side :: D.length :: E) := by
    rw [← encAll_eq]; exact hh
  obtain ⟨s₆, t₆, hex₆, ht₆, hk₆, hp₆, hhe₆, hx₆⟩ := loadAll_exec hw frameArrs
    (frameArrs.map s₁.arrs) aHeap_notMem_frameArrs (by simp) D (lenA :: side :: D.length :: E) s₅
    hh₅ (by simp [s₅]) (by rw [← encAll_eq]; exact hlt)
    (fun v h => hhw' v (by rw [← encAll_eq] at h; exact h))
  rw [← encAll_eq, ← henc] at ht₆ hp₆
  have hh₆ : s₆.arrs aHeap = L := by rw [hhe₆]; exact hh
  have hT₆ : s₆.regs rTop = top := by rw [hk₆.1 rTop (by decide)]; simp [s₅, s₄, s₃, s₂]
  set s₇ := s₆.setReg rHp D.length with hs₇
  have hex₇ : Exec w (.assign rHp (.read aHeap (.op .sub (.reg rTop) (.const 1)))) s₆ s₇
      (1 + 1 + 1 + 1 + 1) :=
    .assign (readEnd_eval hh₆ (hrT s₆ hT₆ 1 (by omega))
      (by rw [show top - 1 = D.length + enc.length + 2 by omega]; exact hg2) hv2)
  have hkeep : Keeps [rTop, rLenA, rTopSide, rHp, rI4, rLen] frameArrs s s₇ :=
    ((((((Keeps.refl _ _ s).setReg (by decide) _).setReg (by decide) _).setReg (by decide)
      _).setReg (by decide) _).trans hk₆ (by decide) (fun _ h => h)).setReg (by decide) _
  refine ⟨s₇, _, .seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))), ?_, hkeep,
    ?_, ?_, ?_, by simp [s₇], ?_⟩
  · rw [length_frameArrs] at ht₆; omega
  · rw [hfl]; simp only [s₇, State.setReg_regs_ne _ _ (show rTop ≠ rHp by decide), hT₆]; omega
  · simp only [s₇, State.setReg_regs_ne _ _ (show rLenA ≠ rHp by decide)]
    rw [hk₆.1 rLenA (by decide)]; simp [s₅, s₄, s₃]
  · simp only [s₇, State.setReg_regs_ne _ _ (show rTopSide ≠ rHp by decide)]
    rw [hk₆.1 rTopSide (by decide)]; simp [s₅, s₄]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [s₇, State.setReg_arrs]
    rw [hx₆ frameArrs_nodup i hi]; simp

end GraphMinor.Compute.TwoPaths
