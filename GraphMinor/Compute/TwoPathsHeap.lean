module

public import GraphMinor.Compute.TwoPathsNorm

/-!
# Saving arrays on a heap

The recursion of Algorithm 5.1 keeps the instances of the pending calls on a stack. A Word RAM
program names its arrays by constants, so the stack lives in one array, the *heap* `aHeap`, with a
pointer `rHp` to its first free entry. An array `x` with content `L` is saved as the entries
`|L| :: L` (`saveArr`), and read back from there (`loadArr`). A list of arrays is saved and loaded
one after the other (`saveAll`, `loadAll`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-- The heap. -/
abbrev aHeap : Arr := 70
/-- The heap pointer: the first free entry of the heap. -/
abbrev rHp : Reg := 120
/-- The counter of the copy loops of the heap. -/
abbrev rI4 : Reg := 121
/-- The length of the array being saved or loaded. -/
abbrev rLen : Reg := 122

/-- The registers that the heap programs write. -/
def heapRegs : List ℕ := [rHp, rI4, rLen]

/-! ### One array -/

/-- Append `|x| :: x` to the heap. -/
def saveArr (x : Arr) : Cmd :=
  .seq (.assign rLen (.len x))
    (.seq (.write aHeap (.reg rHp) (.reg rLen))
      (.seq (.assign rHp (.op .add (.reg rHp) (.const 1)))
        (appProg rI4 rHp (.const 0) (.reg rLen) aHeap x (.reg rI4))))

/-- Read `|L| :: L` from the heap into `x`. -/
def loadArr (x : Arr) : Cmd :=
  .seq (.assign rLen (.read aHeap (.reg rHp)))
    (.seq (.assign rHp (.op .add (.reg rHp) (.const 1)))
      (.seq (mapProg rI4 (.reg rLen) x aHeap (.op .add (.reg rHp) (.reg rI4)))
        (.assign rHp (.op .add (.reg rHp) (.reg rLen)))))

/-- The entries that save the list `L`. -/
def encArr (L : List ℕ) : List ℕ := L.length :: L

theorem map_range'_getD_self (L : List ℕ) :
    (List.range' 0 L.length).map (fun i => L.getD i 0) = L := by
  rw [map_range'_getD _ _ _ (by omega), List.drop_zero, List.take_length]

/-- **Saving an array.** -/
theorem saveArr_exec {w : ℕ} {x : Arr} (hx : x ≠ aHeap) (D R : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hheap : s.arrs aHeap = D ++ R) (hp : s.regs rHp = D.length)
    (hR : (s.arrs x).length + 1 ≤ R.length) (hDR : D.length + R.length < 2 ^ w)
    (hxw : ∀ v ∈ s.arrs x, v < 2 ^ w) :
    ∃ s' t, Exec w (saveArr x) s s' t ∧ t ≤ 14 + 16 * (s.arrs x).length ∧
      Keeps heapRegs [aHeap] s s' ∧ s'.regs rHp = D.length + (encArr (s.arrs x)).length ∧
      s'.arrs aHeap = D ++ encArr (s.arrs x) ++ R.drop (encArr (s.arrs x)).length := by
  set L := s.arrs x with hL
  have hLw : L.length < 2 ^ w := by omega
  set s₁ := s.setReg rLen L.length
  have hex₁ : Exec w (.assign rLen (.len x)) s s₁ (1 + 1) := .assign (len_eval rfl hLw)
  obtain ⟨r₀, R', rfl⟩ : ∃ r₀ R', R = r₀ :: R' := by
    cases R with
    | nil => simp at hR
    | cons r₀ R' => exact ⟨r₀, R', rfl⟩
  set s₂ := s₁.writeArr aHeap D.length L.length
  have hex₂ : Exec w (.write aHeap (.reg rHp) (.reg rLen)) s₁ s₂ (1 + 1 + 1) :=
    .write (reg_eval (by simp [s₁, hp]) (by simp at hDR; omega))
      (reg_eval (by simp [s₁]) hLw) (by simp [s₁, hheap])
  have hh₂ : s₂.arrs aHeap = (D ++ [L.length]) ++ R' := by
    simp only [s₂, s₁, State.writeArr, State.setArr_arrs, ite_true, State.setReg_arrs, hheap]
    rw [List.set_append_right _ _ (le_refl _), Nat.sub_self, List.set_cons_zero]; simp
  set s₃ := s₂.setReg rHp (D.length + 1)
  have hex₃ : Exec w (.assign rHp (.op .add (.reg rHp) (.const 1))) s₂ s₃ (1 + 1 + 1 + 1) :=
    .assign (add_eval (reg_eval (by simp [s₂, s₁, hp]) (by simp at hDR; omega))
      (const_eval' (by omega)) (by simp at hDR; omega))
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hc₄, hd₄⟩ := appProg_exec rI4 rHp (.const 0) (.reg rLen) aHeap x
    (.reg rI4) (Ne.symm hx) (by decide) L (D ++ [L.length]) R' id 0 L.length s₃ hw (Nat.zero_le _)
    (by simp at hR; omega) (by simp at hDR ⊢; omega) hLw (const_eval' (by omega))
    (fun st hst => reg_eval (by rw [hst.1 rLen (by decide)]; simp [s₃, s₂, s₁]) hLw)
    (fun st i hst hri _ hi => reg_eval hri (show i < 2 ^ w by omega)) (fun i _ hi => hi)
    hxw (by simp [s₃, s₂, s₁, State.writeArr, hL, State.setArr_arrs_ne _ _ hx]) (by simp [s₃, hh₂])
    (by simp [s₃])
  rw [Nat.sub_zero, show (fun i => L.getD (id i) 0) = (fun i => L.getD i 0) from rfl,
    map_range'_getD_self] at hd₄
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_,
    ((((Keeps.refl _ _ s).setReg (by decide) _).writeArr (by decide) _ _).setReg (by decide)
      _).trans hk₄ (by decide) (by decide), ?_, ?_⟩
  · simp only [Expr.cost] at ht₄; rw [Nat.sub_zero] at ht₄; omega
  · rw [hc₄]; simp [encArr]; omega
  · rw [hd₄]; simp [encArr]

/-- **Loading an array.** -/
theorem loadArr_exec {w : ℕ} {x : Arr} (hx : x ≠ aHeap) (D L E : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hheap : s.arrs aHeap = D ++ encArr L ++ E) (hp : s.regs rHp = D.length)
    (hlen : (D ++ encArr L ++ E).length < 2 ^ w) (hhw : ∀ v ∈ D ++ encArr L ++ E, v < 2 ^ w) :
    ∃ s' t, Exec w (loadArr x) s s' t ∧ t ≤ 17 + 16 * L.length ∧
      Keeps heapRegs [x] s s' ∧ s'.regs rHp = D.length + (encArr L).length ∧ s'.arrs x = L := by
  have hlt : D.length + L.length + 1 < 2 ^ w := by simp [encArr] at hlen; omega
  have hget : (D ++ encArr L ++ E)[D.length]? = some L.length := by
    simp [encArr, List.getElem?_append_right]
  set s₁ := s.setReg rLen L.length
  have hex₁ : Exec w (.assign rLen (.read aHeap (.reg rHp))) s s₁ (1 + 1 + 1) :=
    .assign (readEnd_eval hheap (reg_eval hp (by omega)) hget (by omega))
  set s₂ := s₁.setReg rHp (D.length + 1)
  have hex₂ : Exec w (.assign rHp (.op .add (.reg rHp) (.const 1))) s₁ s₂ (1 + 1 + 1 + 1) :=
    .assign (add_eval (reg_eval (by simp [s₁, hp]) (by omega)) (const_eval' (by omega))
      (by omega))
  have hh₂ : s₂.arrs aHeap = D ++ encArr L ++ E := by simp [s₂, s₁, hheap]
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hd₃⟩ := mapProg_exec rI4 (.reg rLen) x aHeap
    (.op .add (.reg rHp) (.reg rI4)) hx L.length (fun i => D.length + 1 + i)
    (D ++ encArr L ++ E) s₂ hw (by omega)
    (fun st hst => reg_eval (by rw [hst.1 rLen (by decide)]; simp [s₂, s₁]) (by omega))
    (fun st i hst hri hi => add_eval (reg_eval (by rw [hst.1 rHp (by decide)]; simp [s₂])
      (by omega)) (reg_eval hri (by omega)) (by omega))
    (fun i hi => by simp [encArr]; omega) hhw hh₂
  have hL : (List.range L.length).map (fun i => (D ++ encArr L ++ E).getD (D.length + 1 + i) 0) =
      L := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.length_map, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD, encArr,
      List.append_assoc, List.getElem?_append_right (Nat.le_add_right_of_le (Nat.le_add_right _ 1)),
      show D.length + 1 + i - D.length = i + 1 by omega, List.cons_append,
      List.getElem?_cons_succ, List.getElem?_append_left h₁, List.getElem?_eq_getElem h₁,
      Option.getD_some]
  rw [hL] at hd₃
  set s₄ := s₃.setReg rHp (D.length + 1 + L.length)
  have hex₄ : Exec w (.assign rHp (.op .add (.reg rHp) (.reg rLen))) s₃ s₄ (1 + 1 + 1 + 1) :=
    .assign (add_eval (reg_eval (by rw [hk₃.1 rHp (by decide)]; simp [s₂]) (by omega))
      (reg_eval (by rw [hk₃.1 rLen (by decide)]; simp [s₂, s₁]) (by omega)) (by omega))
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_,
    ((((Keeps.refl _ _ s).setReg (by decide) _).setReg (by decide) _).trans hk₃ (by decide)
      (fun _ h => h)).setReg (by decide) _, by simp [s₄, encArr]; omega, by simp [s₄, hd₃]⟩
  simp only [Expr.cost] at ht₃; omega

/-! ### A list of arrays -/

/-- Save the arrays of `l` in order. -/
def saveAll : List Arr → Cmd
  | [] => .skip
  | x :: l => .seq (saveArr x) (saveAll l)

/-- Load the arrays of `l` in order. -/
def loadAll : List Arr → Cmd
  | [] => .skip
  | x :: l => .seq (loadArr x) (loadAll l)

/-- The entries that save the arrays `l` of `s`. -/
def encAll (l : List Arr) (s : State) : List ℕ := l.flatMap fun x => encArr (s.arrs x)

/-- The number of entries of the contents `Ls`. -/
def encLists (Ls : List (List ℕ)) : List ℕ := Ls.flatMap encArr

theorem encAll_eq (l : List Arr) (s : State) : encAll l s = encLists (l.map s.arrs) := by
  simp [encAll, encLists, List.flatMap_map]

/-- **Saving a list of arrays.** -/
theorem saveAll_exec {w : ℕ} (hw : 1 < 2 ^ w) :
    ∀ (l : List Arr), aHeap ∉ l → ∀ (D R : List ℕ) (s : State), s.arrs aHeap = D ++ R →
      s.regs rHp = D.length → (encAll l s).length ≤ R.length → D.length + R.length < 2 ^ w →
      (∀ x ∈ l, ∀ v ∈ s.arrs x, v < 2 ^ w) →
      ∃ s' t, Exec w (saveAll l) s s' t ∧ t ≤ 1 + 14 * l.length + 16 * (encAll l s).length ∧
        Keeps heapRegs [aHeap] s s' ∧ s'.regs rHp = D.length + (encAll l s).length ∧
        s'.arrs aHeap = D ++ encAll l s ++ R.drop (encAll l s).length
  | [], _, D, R, s, hh, hp, _, _, _ => ⟨s, 1, .skip s, by simp, Keeps.refl _ _ s, by simp [encAll, hp],
      by simp [encAll, hh]⟩
  | x :: l, hl, D, R, s, hh, hp, hR, hDR, hxw => by
    have hx : x ≠ aHeap := fun e => hl (by simp [e])
    have hl' : aHeap ∉ l := fun h => hl (List.mem_cons_of_mem _ h)
    have henc : encAll (x :: l) s = encArr (s.arrs x) ++ encAll l s := by simp [encAll]
    rw [henc] at hR ⊢
    simp only [List.length_append] at hR
    obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hp₁, hh₁⟩ := saveArr_exec hx D R s hw hh hp
      (by simp [encArr] at hR; omega) hDR (hxw x (by simp))
    have hsame : ∀ y, y ≠ aHeap → s₁.arrs y = s.arrs y := fun y hy => hk₁.2 y (by simp [hy])
    have henc₁ : encAll l s₁ = encAll l s := by
      simp only [encAll]
      exact List.flatMap_congr fun y hy => by rw [hsame y (fun e => hl' (e ▸ hy))]
    obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hp₂, hh₂⟩ := saveAll_exec hw l hl' (D ++ encArr (s.arrs x))
      (R.drop (encArr (s.arrs x)).length) s₁ (by rw [hh₁]) (by rw [hp₁]; simp)
      (by rw [henc₁]; simp; omega) (by simp at hDR ⊢; omega)
      (fun y hy v hv => hxw y (List.mem_cons_of_mem _ hy) v
        (by rwa [hsame y (fun e => hl' (e ▸ hy))] at hv))
    rw [henc₁] at ht₂ hp₂ hh₂
    refine ⟨s₂, _, .seq hex₁ hex₂, ?_, hk₁.trans hk₂ (fun _ h => h) (fun _ h => h), ?_, ?_⟩
    · simp only [List.length_cons, List.length_append, encArr] at ht₁ ht₂ ⊢; omega
    · rw [hp₂]; simp; omega
    · rw [hh₂, List.drop_drop]; simp [List.append_assoc, Nat.add_comm]

/-- **Loading a list of arrays.** -/
theorem loadAll_exec {w : ℕ} (hw : 1 < 2 ^ w) :
    ∀ (l : List Arr) (Ls : List (List ℕ)), aHeap ∉ l → ∀ (hlen : l.length = Ls.length),
      ∀ (D E : List ℕ) (s : State), s.arrs aHeap = D ++ encLists Ls ++ E →
      s.regs rHp = D.length → (D ++ encLists Ls ++ E).length < 2 ^ w →
      (∀ v ∈ D ++ encLists Ls ++ E, v < 2 ^ w) →
      ∃ s' t, Exec w (loadAll l) s s' t ∧ t ≤ 1 + 17 * l.length + 16 * (encLists Ls).length ∧
        Keeps heapRegs l s s' ∧ s'.regs rHp = D.length + (encLists Ls).length ∧
        s'.arrs aHeap = s.arrs aHeap ∧
        (l.Nodup → ∀ i (h : i < l.length), s'.arrs l[i] = Ls[i]'(hlen ▸ h))
  | [], [], _, _, D, E, s, hh, hp, _, _ => ⟨s, 1, .skip s, by simp, Keeps.refl _ _ s,
      by simp [encLists, hp], rfl, fun _ i h => by simp at h⟩
  | [], _ :: _, _, h, _, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, h, _, _, _, _, _, _, _ => by simp at h
  | x :: l, L :: Ls, hl, hlen, D, E, s, hh, hp, hlt, hhw => by
    have hx : x ≠ aHeap := fun e => hl (by simp [e])
    have hl' : aHeap ∉ l := fun h => hl (List.mem_cons_of_mem _ h)
    have henc : encLists (L :: Ls) = encArr L ++ encLists Ls := by simp [encLists]
    rw [henc] at hh hlt hhw ⊢
    obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hp₁, hx₁⟩ := loadArr_exec hx D L (encLists Ls ++ E) s hw
      (by rw [hh]; simp) hp (by simpa using hlt) (by simpa using hhw)
    have hh₁ : s₁.arrs aHeap = (D ++ encArr L) ++ encLists Ls ++ E := by
      rw [hk₁.2 aHeap (by simp [Ne.symm hx]), hh]; simp
    obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hp₂, hhe₂, hx₂⟩ := loadAll_exec hw l Ls hl'
      (by simpa using hlen) (D ++ encArr L) E s₁ hh₁ (by rw [hp₁]; simp)
      (by simp at hlt ⊢; omega) (fun v hv => hhw v (by simpa using hv))
    refine ⟨s₂, _, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_append] at ht₁ ht₂ ⊢
      simp only [encArr, List.length_cons] at ht₁ ht₂ ⊢; omega
    · exact (hk₁.mono (fun _ h => h) (by simp)).trans hk₂ (fun _ h => h)
        (fun a h => List.mem_cons_of_mem _ h)
    · rw [hp₂]; simp; omega
    · rw [hhe₂, hh₁, hh]; simp
    · intro hnd i hi
      rcases i with _ | i
      · simp only [List.getElem_cons_zero]
        rw [hk₂.2 x (List.nodup_cons.mp hnd).1]; exact hx₁
      · simp only [List.getElem_cons_succ]
        exact hx₂ (List.nodup_cons.mp hnd).2 i (by simp at hi; omega)

end GraphMinor.Compute.TwoPaths
