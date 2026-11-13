module

public import GraphMinor.Compute.TwoPathsLink
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.TwoPathsSweepLoop
import GraphMinor.Compute.TwoPathsSweep
import GraphMinor.Compute.TwoPathsChild
import GraphMinor.Compute.TwoPathsRotate

/-!
# Splicing a list into a successor array

The program that undoes the collapse edges keeps the two paths of a crossing in the successor
array `aUdNxt` (`linkArr`, `TwoPathsLink.lean`). Its one basic move is to put a vertex `x` right
after a vertex `p` of one of the paths: two writes, `nxt[x] := nxt[p]` and `nxt[p] := x + 1`.

`insLoop src` does this for the entries `src[o], …, src[o + k - 1]` in turn. After each move it
either goes on after the vertex just put in (register `rUdfwd` not `0`), which puts the entries in
their order, or stays after `p`, which puts them in reverse order. `insLoop_exec` gives the result
for any sequence of lists in which each move is one such insertion. It serves three times: to
build the successor array of a path (each vertex goes at the end), and to splice a window forwards
or backwards.

All registers and arrays of these programs are at `400` or above.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- Register holding a bound `V` on the vertices. -/
abbrev rUdV : Reg := 400
/-- Loop counter. -/
abbrev rUdi : Reg := 401
/-- Position in the records. -/
abbrev rUdpos : Reg := 402
/-- Number of records. -/
abbrev rUdcnt : Reg := 403
/-- Offset of the entries to put in. -/
abbrev rUdo : Reg := 404
/-- First end of a collapse edge. -/
abbrev rUdy : Reg := 405
/-- Second end of a collapse edge. -/
abbrev rUdz : Reg := 406
/-- Number of entries to put in. -/
abbrev rUdk : Reg := 407
/-- The vertex after which the next entry goes. -/
abbrev rUdp : Reg := 408
/-- The entry being put in. -/
abbrev rUdx : Reg := 409
/-- Whether the entries go in their order (not `0`) or in reverse order (`0`). -/
abbrev rUdfwd : Reg := 410
/-- Cursor of the read-back, one more than a vertex, or `0`. -/
abbrev rUdc : Reg := 411
/-- Length of the path read back. -/
abbrev rUdn : Reg := 412
/-- Array holding the first path. -/
abbrev aUdQ : Arr := 400
/-- Array holding the second path. -/
abbrev aUdR : Arr := 401
/-- The successor array. -/
abbrev aUdNxt : Arr := 402
/-- The offsets of the records. -/
abbrev aUdOff : Arr := 403

/-- Put `x = src[o + i]` right after `p`, and move `p` to `x` when `rUdfwd` is not `0`. -/
def insBody (src : Arr) : Cmd :=
  .seq (.assign rUdx (.read src (.op .add (.reg rUdo) (.reg rUdi))))
  (.seq (.write aUdNxt (.reg rUdx) (.read aUdNxt (.reg rUdp)))
  (.seq (.write aUdNxt (.reg rUdp) (.op .add (.reg rUdx) (.const 1)))
    (.ite (.reg rUdfwd) (.assign rUdp (.reg rUdx)) .skip)))

/-- Put the `k` entries of `src` from offset `o` after `p`, one by one. -/
def insLoop (src : Arr) : Cmd :=
  .seq (.assign rUdi (.const 0)) (forUp rUdi (.reg rUdk) (insBody src))

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

public section

variable {w V : ℕ}

/-- **One insertion.** -/
theorem insBody_exec {src : ℕ} (hsrc : src ≠ aUdNxt) {st : State} {i o p f x : ℕ}
    {P T L' : List ℕ} (hi : st.regs rUdi = i) (ho : st.regs rUdo = o) (hp : st.regs rUdp = p)
    (hf : st.regs rUdfwd = f) (hS : o + i < (st.arrs src).length) (hx : (st.arrs src)[o + i] = x)
    (hnxt : st.arrs aUdNxt = linkArr V (P ++ p :: T) L')
    (hnd : (P ++ p :: x :: T).Nodup) (hpL : p ∉ L') (hxL : x ∉ L') (hpV : p < V) (hxV : x < V)
    (hT : ∀ u ∈ P ++ p :: T, u < V) (hVw : V < 2 ^ w) (hoi : o + i < 2 ^ w) (hf2 : f < 2 ^ w) :
    ∃ st' c, Exec w (insBody src) st st' c ∧ c ≤ 17 ∧ Keeps [rUdx, rUdp] [aUdNxt] st st' ∧
      st'.arrs aUdNxt = linkArr V (P ++ p :: x :: T) L' ∧
      st'.regs rUdp = (if f = 0 then p else x) := by
  have hoi' : (Expr.op .add (.reg rUdo) (.reg rUdi)).eval w st = some (o + i) :=
    add_eval (reg_eval ho (by omega)) (reg_eval hi (by omega)) hoi
  have hrd : (Expr.read src (.op .add (.reg rUdo) (.reg rUdi))).eval w st = some x := by
    have := read_eval (s := st) hoi' hS (by rw [hx]; omega)
    rwa [hx] at this
  set s₁ := st.setReg rUdx x
  have hlen : (linkArr V (P ++ p :: T) L').length = V := length_linkArr _ _ _
  have hval : (linkArr V (P ++ p :: T) L')[p]'(by rw [hlen]; exact hpV) =
      nextOf (P ++ p :: T) p := by
    rw [linkArr_getElem, nextOf_of_not_mem hpL, Nat.add_zero]
  have hvle : nextOf (P ++ p :: T) p ≤ V := nextOf_le hT p
  have hrd₂ : (Expr.read aUdNxt (.reg rUdp)).eval w s₁ = some (nextOf (P ++ p :: T) p) := by
    have h1 : (s₁.arrs aUdNxt) = linkArr V (P ++ p :: T) L' := by simp [s₁, hnxt]
    have := read_eval (s := s₁) (a := aUdNxt) (E := .reg rUdp)
      (reg_eval (v := p) (by simp [s₁, hp]) (lt_trans hpV hVw)) (by rw [h1, hlen]; exact hpV)
      (by simp only [h1]; rw [hval]; omega)
    simp only [h1] at this
    rw [this, hval]
  set s₂ := s₁.writeArr aUdNxt x (nextOf (P ++ p :: T) p)
  have hex₂ : Exec w (.write aUdNxt (.reg rUdx) (.read aUdNxt (.reg rUdp))) s₁ s₂ 4 :=
    .write (reg_eval (by simp [s₁]) (by omega)) hrd₂ (by simp [s₁, hnxt, hlen, hxV])
  set s₃ := s₂.writeArr aUdNxt p (x + 1)
  have hex₃ : Exec w (.write aUdNxt (.reg rUdp) (.op .add (.reg rUdx) (.const 1))) s₂ s₃ 5 :=
    .write (reg_eval (by simp [s₂, s₁, hp]) (by omega))
      (add_eval (reg_eval (by simp [s₂, s₁]) (by omega)) (const_eval' (by omega)) (by omega))
      (by simp [s₂, s₁, hnxt, hlen, hpV])
  have hnxt₃ : s₃.arrs aUdNxt = linkArr V (P ++ p :: x :: T) L' := by
    have h := linkArr_insert hnd hpL hxL hpV hxV
    rw [getElem!_pos _ p (by rw [hlen]; exact hpV), hval] at h
    simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs, hnxt]
    exact h
  have hk₃ : Keeps [rUdx, rUdp] [aUdNxt] st s₃ :=
    (((Keeps.refl _ _ _).setReg (by simp) _).writeArr (by simp) _ _).writeArr (by simp) _ _
  have hfe : (Expr.reg rUdfwd).eval w s₃ = some f := reg_eval (by simp [s₃, s₂, s₁, hf]) hf2
  by_cases hf0 : f = 0
  · refine ⟨s₃, _, .seq (.assign hrd) (.seq hex₂ (.seq hex₃ (.ite_false (hf0 ▸ hfe)
      (.skip _)))), by simp, hk₃, hnxt₃, by simp [s₃, s₂, s₁, hp, hf0]⟩
  · refine ⟨s₃.setReg rUdp x, _, .seq (.assign hrd) (.seq hex₂ (.seq hex₃ (.ite_true hfe hf0
      (.assign (reg_eval (by simp [s₃, s₂, s₁]) (by omega)))))), by simp, hk₃.setReg (by simp) _,
      by simp [hnxt₃], by simp [hf0]⟩

/-- **The insertion loop.** `Lf i` is the list after `i` moves and `pf i` the vertex after which
move `i` puts `src[o + i]`. Each move must be an insertion right after `pf i`, and the lists must
have no repeats and miss the other list `L'`. Then the loop turns the successor array of
`Lf 0, L'` into that of `Lf k, L'`, in at most `5 + 24 k` steps. -/
theorem insLoop_exec {src : ℕ} (hsrc : src ≠ aUdNxt) (hw : 1 < 2 ^ w) {st : State}
    {o k f : ℕ} {S L' : List ℕ} (Lf : ℕ → List ℕ) (pf : ℕ → ℕ)
    (ho : st.regs rUdo = o) (hk : st.regs rUdk = k) (hf : st.regs rUdfwd = f)
    (hp : st.regs rUdp = pf 0) (hS : st.arrs src = S) (hok : o + k ≤ S.length)
    (hnxt : st.arrs aUdNxt = linkArr V (Lf 0) L')
    (hstep : ∀ i < k, ∃ P T, Lf i = P ++ pf i :: T ∧ Lf (i + 1) = P ++ pf i :: S.getD (o + i) 0 :: T)
    (hpf : ∀ i < k, pf (i + 1) = if f = 0 then pf i else S.getD (o + i) 0)
    (hnd : ∀ i ≤ k, (Lf i).Nodup) (hL' : ∀ i ≤ k, ∀ v ∈ Lf i, v ∉ L' ∧ v < V)
    (hVw : V < 2 ^ w) (hokw : o + k < 2 ^ w) (hf2 : f < 2 ^ w) :
    ∃ st' c, Exec w (insLoop src) st st' c ∧ c ≤ 5 + 24 * k ∧
      Keeps [rUdi, rUdx, rUdp] [aUdNxt] st st' ∧ st'.arrs aUdNxt = linkArr V (Lf k) L' := by
  let I : ℕ → State → Prop := fun i s => Keeps [rUdi, rUdx, rUdp] [aUdNxt] st s ∧ s.regs rUdi = i ∧
    s.regs rUdp = pf i ∧ s.arrs aUdNxt = linkArr V (Lf i) L'
  have hI0 : I 0 (st.setReg rUdi 0) :=
    ⟨(Keeps.refl _ _ _).setReg (by simp) _, by simp, by simp [hp], by simp [hnxt]⟩
  obtain ⟨st', c, hex, hc, hI⟩ := forUp_pot I (fun _ => 0) k 17 (r_i := rUdi) (hi := .reg rUdk)
    (body := insBody src) hw (by omega)
    (fun i _ s hs => ⟨hs.2.1, reg_eval (by rw [hs.1.1 rUdk (by simp)]; exact hk) (by omega)⟩)
    (fun i hi s hs => by
      obtain ⟨hks, hsi, hsp, hsn⟩ := hs
      obtain ⟨P, T, hLi, hLi'⟩ := hstep i hi
      have hSs : s.arrs src = S := by rw [hks.2 src (by simp [hsrc])]; exact hS
      have hx : (s.arrs src)[o + i]'(by rw [hSs]; omega) = S.getD (o + i) 0 := by
        simp only [hSs]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hnd' := hnd (i + 1) (by omega)
      rw [hLi'] at hnd'
      have hmem : pf i ∈ Lf i := by rw [hLi]; simp
      have hxm : S.getD (o + i) 0 ∈ Lf (i + 1) := by rw [hLi']; simp
      obtain ⟨s', c, hex, hc, hks', hn', hp'⟩ := insBody_exec (V := V) (w := w) hsrc
        (st := s) (i := i) (o := o) (p := pf i) (f := f) (x := S.getD (o + i) 0) (P := P)
        (T := T) (L' := L') hsi (by rw [hks.1 rUdo (by simp)]; exact ho) hsp
        (by rw [hks.1 rUdfwd (by simp)]; exact hf) (by rw [hSs]; omega) hx
        (by rw [hsn, hLi]) hnd' (hL' i (by omega) _ hmem).1 (hL' (i + 1) (by omega) _ hxm).1
        (hL' i (by omega) _ hmem).2 (hL' (i + 1) (by omega) _ hxm).2
        (fun u hu => (hL' i (by omega) u (hLi ▸ hu)).2) hVw (by omega) hf2
      refine ⟨s', c, hex, by omega, ⟨(hks.trans hks' (by simp) (by simp)).setReg (by simp) _,
        by simp, ?_, ?_⟩, by rw [hks'.1 rUdi (by simp)]; exact hsi⟩
      · rw [State.setReg_regs_ne _ _ (by decide), hp', hpf i hi]
      · rw [State.setReg_arrs, hn', hLi'])
    0 (Nat.zero_le _) _ hI0
  refine ⟨st', _, .seq (.assign (const_eval' (by omega))) hex, ?_, hI.1, hI.2.2.2⟩
  simp only [Expr.cost] at hc ⊢
  omega

end

end GraphMinor.Compute.TwoPaths
