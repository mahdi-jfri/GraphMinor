module

public import GraphMinor.Compute.TwoPathsUndoIns
public import GraphMinor.Compute.TwoPathsCompChain
import GraphMinor.Compute.TwoPathsSweep
import GraphMinor.Compute.TwoPathsChild
import GraphMinor.Compute.TwoPathsChord
import GraphMinor.Compute.TwoPathsRotate
import GraphMinor.HP25.Lemma43Fan

/-!
# One collapse record on the successor array

`linkProg A` builds the successor array of the path in array `A` (each vertex goes at the end), and
`recProg` undoes one collapse record `y, z, |N|, N` of `aT2Rec` on the successor array of the two
paths. Both are `insLoop` (`TwoPathsUndoIns.lean`) with a few reads around it.

`recProg` follows `spliceT2Lists` (`TwoPathsExtSplice.lean`): when `N` is not empty and `z` comes
right after `y` on a path, it puts `N` between them in its order; when `y` comes right after `z`, it
puts `N` between them in reverse order; otherwise it does nothing. The test costs two reads, since
on two disjoint paths without repeats the successor of `y` is `z` exactly when `y z` is an edge of
one of them in this order (`linkArr_succ_iff`).

* `linkProg_exec`: the successor array of the path in `A` is added;
* `recProg_exec` (`TwoPathsUndoStep.lean`): under `SpliceOK`, the successor array of `Q, R`
  becomes that of `spliceT2Lists y z N Q R`, in at most `60 + 24 |N|` steps.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- Add the successor array of the path in array `A` to `aUdNxt`. -/
def linkProg (A : Arr) : Cmd :=
  .ite (.len A)
    (.seq (.assign rUdp (.read A (.const 0)))
    (.seq (.assign rUdo (.const 1))
    (.seq (.assign rUdk (.op .sub (.len A) (.const 1)))
    (.seq (.assign rUdfwd (.const 1)) (insLoop A)))))
    .skip

/-- Read the collapse record at offset `aUdOff[rUdcnt]` of `aT2Rec`: `y`, `z`, `|N|`, and the
offset of `N`. -/
def recRead : Cmd :=
  .seq (.assign rUdo (.read aUdOff (.reg rUdcnt)))
  (.seq (.assign rUdy (.read aT2Rec (.reg rUdo)))
  (.seq (.assign rUdz (.read aT2Rec (.op .add (.reg rUdo) (.const 1))))
  (.seq (.assign rUdk (.read aT2Rec (.op .add (.reg rUdo) (.const 2))))
    (.assign rUdo (.op .add (.reg rUdo) (.const 3))))))

/-- Splice the window of the record read by `recRead`, if a path uses `y z`. -/
def recCase : Cmd :=
  .ite (.reg rUdk)
    (.ite (.op .eq (.read aUdNxt (.reg rUdy)) (.op .add (.reg rUdz) (.const 1)))
      (.seq (.assign rUdp (.reg rUdy)) (.seq (.assign rUdfwd (.const 1)) (insLoop aT2Rec)))
      (.ite (.op .eq (.read aUdNxt (.reg rUdz)) (.op .add (.reg rUdy) (.const 1)))
        (.seq (.assign rUdp (.reg rUdz)) (.seq (.assign rUdfwd (.const 0)) (insLoop aT2Rec)))
        .skip))
    .skip

/-- Undo the collapse record at offset `aUdOff[rUdcnt]` of `aT2Rec` on the successor array. -/
def recProg : Cmd := .seq recRead recCase

/-- The registers that `insLoop`, `linkProg` and `recProg` write. -/
def recRegs : List ℕ := [rUdi, rUdx, rUdp, rUdo, rUdk, rUdfwd, rUdy, rUdz]

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

public section

variable {w V : ℕ}

theorem isListEdge_mid (l₀ l₁ : List ℕ) (y z : ℕ) : HP25.IsListEdge (l₀ ++ y :: z :: l₁) y z := by
  have h := HP25.isListEdge_getElem (l₀ ++ y :: z :: l₁) l₀.length (by simp)
  simpa [List.getElem_append_right] using h

theorem take_succ_getD (L : List ℕ) {i : ℕ} (hi : i < L.length) :
    L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  simp

/-- On two disjoint lists without repeats, the successor of `y` is `z` exactly when `z` comes right
after `y` on one of them. -/
theorem linkArr_succ_iff {Q R : List ℕ} (hQ : Q.Nodup) (hR : R.Nodup) (hd : Q.Disjoint R)
    (y z : ℕ) : nextOf Q y + nextOf R y = z + 1 ↔
      (∃ l₀ l₁, Q = l₀ ++ y :: z :: l₁) ∨ (∃ l₀ l₁, R = l₀ ++ y :: z :: l₁) := by
  by_cases hyQ : y ∈ Q
  · have hyR : y ∉ R := fun h => hd hyQ h
    rw [nextOf_of_not_mem hyR, Nat.add_zero, nextOf_eq_iff hQ]
    refine ⟨Or.inl, ?_⟩
    rintro (h | ⟨l₀, l₁, rfl⟩)
    · exact h
    · exact absurd (by simp) hyR
  · rw [nextOf_of_not_mem hyQ, Nat.zero_add, nextOf_eq_iff hR]
    refine ⟨Or.inr, ?_⟩
    rintro (⟨l₀, l₁, rfl⟩ | h)
    · exact absurd (by simp) hyQ
    · exact h

/-- **Splicing forwards.** With `z` right after `y` on the first list, the loop puts the entries
`N` of `src` from offset `o` between `y` and `z`. -/
theorem spliceFwd_exec {src : ℕ} (hsrc : src ≠ aUdNxt) (hw : 1 < 2 ^ w) {st : State}
    {o y z : ℕ} {S N l₀ l₁ L' : List ℕ} (ho : st.regs rUdo = o) (hk : st.regs rUdk = N.length)
    (hf : st.regs rUdfwd = 1) (hp : st.regs rUdp = y) (hS : st.arrs src = S)
    (hN : ∀ i < N.length, S.getD (o + i) 0 = N.getD i 0) (hok : o + N.length ≤ S.length)
    (hnxt : st.arrs aUdNxt = linkArr V (l₀ ++ y :: z :: l₁) L')
    (hnd : (l₀ ++ y :: N ++ z :: l₁).Nodup)
    (hL' : ∀ v ∈ l₀ ++ y :: N ++ z :: l₁, v ∉ L' ∧ v < V) (hVw : V < 2 ^ w)
    (hokw : o + N.length < 2 ^ w) :
    ∃ st' c, Exec w (insLoop src) st st' c ∧ c ≤ 5 + 24 * N.length ∧
      Keeps [rUdi, rUdx, rUdp] [aUdNxt] st st' ∧
      st'.arrs aUdNxt = linkArr V (l₀ ++ y :: N ++ z :: l₁) L' := by
  have hsub : ∀ i ≤ N.length, (l₀ ++ (y :: N).take (i + 1) ++ z :: l₁).Sublist
      (l₀ ++ y :: N ++ z :: l₁) := by
    intro i _
    refine ((List.Sublist.refl l₀).append ?_).append (List.Sublist.refl _)
    exact List.take_sublist _ _
  have hfin : l₀ ++ (y :: N).take (N.length + 1) ++ z :: l₁ = l₀ ++ y :: N ++ z :: l₁ := by
    rw [List.take_of_length_le (by simp)]
  have h0 : l₀ ++ (y :: N).take (0 + 1) ++ z :: l₁ = l₀ ++ y :: z :: l₁ := by simp
  obtain ⟨st', c, hex, hc, hks, hn⟩ := insLoop_exec (V := V) (S := S) (L' := L') hsrc hw
    (fun i => l₀ ++ (y :: N).take (i + 1) ++ z :: l₁) (fun i => (y :: N).getD i 0) ho hk hf
    (by simpa using hp) hS hok (by rw [h0]; exact hnxt)
    (fun i hi => by
      have h1 : i < (y :: N).length := by simp; omega
      have h2 : i + 1 < (y :: N).length := by simp; omega
      have hg : (y :: N).getD (i + 1) 0 = S.getD (o + i) 0 := by
        rw [hN i hi]; rfl
      refine ⟨l₀ ++ (y :: N).take i, z :: l₁, ?_, ?_⟩
      · rw [take_succ_getD _ h1]; simp
      · rw [take_succ_getD _ h2, take_succ_getD _ h1, hg]; simp)
    (fun i hi => by
      simp only [one_ne_zero, ↓reduceIte]
      rw [hN i hi]; rfl)
    (fun i hi => hnd.sublist (hsub i hi))
    (fun i hi v hv => hL' v ((hsub i hi).subset hv)) hVw hokw (by omega)
  exact ⟨st', c, hex, hc, hks, by rw [hn, hfin]⟩

/-- **Splicing backwards.** With `y` right after `z` on the first list, the loop puts the entries
`N` of `src` from offset `o` between `z` and `y`, in reverse order. -/
theorem spliceBwd_exec {src : ℕ} (hsrc : src ≠ aUdNxt) (hw : 1 < 2 ^ w) {st : State}
    {o y z : ℕ} {S N l₀ l₁ L' : List ℕ} (ho : st.regs rUdo = o) (hk : st.regs rUdk = N.length)
    (hf : st.regs rUdfwd = 0) (hp : st.regs rUdp = z) (hS : st.arrs src = S)
    (hN : ∀ i < N.length, S.getD (o + i) 0 = N.getD i 0) (hok : o + N.length ≤ S.length)
    (hnxt : st.arrs aUdNxt = linkArr V (l₀ ++ z :: y :: l₁) L')
    (hnd : (l₀ ++ z :: N.reverse ++ y :: l₁).Nodup)
    (hL' : ∀ v ∈ l₀ ++ z :: N.reverse ++ y :: l₁, v ∉ L' ∧ v < V) (hVw : V < 2 ^ w)
    (hokw : o + N.length < 2 ^ w) :
    ∃ st' c, Exec w (insLoop src) st st' c ∧ c ≤ 5 + 24 * N.length ∧
      Keeps [rUdi, rUdx, rUdp] [aUdNxt] st st' ∧
      st'.arrs aUdNxt = linkArr V (l₀ ++ z :: N.reverse ++ y :: l₁) L' := by
  have hsub : ∀ i ≤ N.length, (l₀ ++ z :: (N.take i).reverse ++ y :: l₁).Sublist
      (l₀ ++ z :: N.reverse ++ y :: l₁) := by
    intro i _
    refine ((List.Sublist.refl l₀).append (List.Sublist.cons_cons _ ?_)).append (List.Sublist.refl _)
    exact List.reverse_sublist.mpr (List.take_sublist _ _)
  obtain ⟨st', c, hex, hc, hks, hn⟩ := insLoop_exec (V := V) (S := S) (L' := L') hsrc hw
    (fun i => l₀ ++ z :: (N.take i).reverse ++ y :: l₁) (fun _ => z) ho hk hf hp hS hok
    (by simpa using hnxt)
    (fun i hi => ⟨l₀, (N.take i).reverse ++ y :: l₁, by simp, by
      rw [take_succ_getD _ hi, hN i hi]; simp⟩)
    (fun i _ => by simp)
    (fun i hi => hnd.sublist (hsub i hi))
    (fun i hi v hv => hL' v ((hsub i hi).subset hv)) hVw hokw (by omega)
  exact ⟨st', c, hex, hc, hks, by rw [hn, List.take_of_length_le le_rfl]⟩


/-- **Building the successor array of a path.** -/
theorem linkProg_exec {A : ℕ} (hA : A ≠ aUdNxt) (hw : 1 < 2 ^ w) {st : State} {L L' : List ℕ}
    (hL : st.arrs A = L) (hnd : L.Nodup) (hL' : ∀ v ∈ L, v ∉ L' ∧ v < V)
    (hnxt : st.arrs aUdNxt = linkArr V [] L') (hVw : V < 2 ^ w) (hLw : L.length < 2 ^ w) :
    ∃ st' c, Exec w (linkProg A) st st' c ∧ c ≤ 20 + 24 * L.length ∧
      Keeps recRegs [aUdNxt] st st' ∧ st'.arrs aUdNxt = linkArr V L L' := by
  have hlen : (Expr.len A).eval w st = some L.length := len_eval hL hLw
  cases L with
  | nil =>
    exact ⟨st, _, .ite_false hlen (.skip _), by simp, Keeps.refl _ _ _, hnxt⟩
  | cons a L₀ =>
    have hav : a < V := (hL' a (by simp)).2
    set L := a :: L₀ with hLdef
    have hrd : (Expr.read A (.const 0)).eval w st = some a := by
      have := read_eval (s := st) (a := A) (const_eval' (w := w) (s := st) (c := 0) (by omega))
        (by simp [hL, L])
        (by simp only [hL, L, List.getElem_cons_zero]; omega)
      simpa [hL, L] using this
    set s₁ := st.setReg rUdp a
    set s₂ := s₁.setReg rUdo 1
    have hsub : (Expr.op .sub (.len A) (.const 1)).eval w s₂ = some (L.length - 1) :=
      sub_eval (len_eval (by simp [s₂, s₁, hL]) hLw) (const_eval' hw)
    set s₃ := s₂.setReg rUdk (L.length - 1)
    set s₄ := s₃.setReg rUdfwd 1
    have hkp : Keeps recRegs [aUdNxt] st s₄ :=
      ((((Keeps.refl _ _ _).setReg (by simp [recRegs]) _).setReg (by simp [recRegs]) _).setReg
        (by simp [recRegs]) _).setReg (by simp [recRegs]) _
    have hlenL : 1 + (L.length - 1) = L.length := by simp [L]; omega
    obtain ⟨s₅, c, hex, hc, hks, hn⟩ := insLoop_exec (V := V) (S := L) (L' := L') hA hw
      (fun i => L.take (i + 1)) (fun i => L.getD i 0) (st := s₄) (o := 1) (k := L.length - 1)
      (f := 1) (by simp [s₄, s₃, s₂]) (by simp [s₄, s₃]) (by simp [s₄])
      (by simp [s₄, s₃, s₂, s₁, L]) (by simp [s₄, s₃, s₂, s₁, hL]) (by omega)
      (by simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, hnxt, L, List.take_succ_cons,
        List.take_zero, linkArr_single])
      (fun i hi => by
        have h1 : i < L.length := by omega
        have h2 : i + 1 < L.length := by omega
        refine ⟨L.take i, [], ?_, ?_⟩
        · rw [take_succ_getD _ h1]
        · rw [take_succ_getD _ h2, take_succ_getD _ h1, Nat.add_comm 1 i]; simp)
      (fun i hi => by simp only [one_ne_zero, ↓reduceIte, Nat.add_comm 1 i])
      (fun i _ => hnd.sublist (List.take_sublist _ _))
      (fun i _ v hv => hL' v (List.mem_of_mem_take hv)) hVw (by omega) (by omega)
    refine ⟨s₅, _, .ite_true hlen (by simp [L]) (.seq (.assign hrd) (.seq (.assign
      (const_eval' (by omega))) (.seq (.assign hsub) (.seq (.assign (const_eval' (by omega)))
      hex)))), ?_, hkp.trans (hks.mono (by simp [recRegs]) (by simp)) (fun r h => h)
      (fun a h => h), ?_⟩
    · simp only [Expr.cost] at hc ⊢; simp only [L, List.length_cons] at hc ⊢; omega
    · rw [hn, show L.length - 1 + 1 = L.length by simp [L], List.take_length]


end

end GraphMinor.Compute.TwoPaths
