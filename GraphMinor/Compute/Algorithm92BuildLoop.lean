module

public import GraphMinor.Compute.Algorithm92BuildProg
import GraphMinor.Compute.Algorithm92Search

/-!
# Graph Minors XIII, (9.2): the loops that write the layout (`Algorithm92BuildLoop.lean`)

The first program after `F` (page 101 of Graph Minors XIII) writes the layout of `H ∪ F` in two
loops: one over the paths of the wall (`wallBody`) and one over the paths of `F` (`segBody`).
This file proves the two loops.

* `wallLoop_exec`: after the loop over the paths of the wall, the layout is written up to the
  block of the first path of `F`.
* `segLoop_exec`: after the loop over the paths of `F`, the whole layout is written, and the node
  marks hold the branch vertices and the ends of the paths of `F`.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

/-- The indicator of a set of numbers, as entries `0` and `1`. -/
noncomputable def ind (P : ℕ → Prop) : ℕ → ℕ := by
  classical exact fun v => if P v then 1 else 0

theorem update_ind (P : ℕ → Prop) (a : ℕ) :
    Function.update (ind P) a 1 = ind (fun v => P v ∨ v = a) := by
  funext v
  simp only [Function.update_apply, ind]
  by_cases hv : v = a
  · subst hv; simp
  · by_cases hp : P v
    · simp [hv, hp]
    · simp [hv, hp]

variable {l m p h k r : ℕ} {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}

variable (x segs) in
/-- The numbers marked as nodes after the ends of the first `j` paths of `F` are marked: the
separator, the branch vertices, and the ends of these paths. -/
def ndJ (j : ℕ) (v : ℕ) : Prop :=
  v = x.n ∨ (∃ u, (x.W.branchVert u).val = v) ∨
    ∃ j', ∃ hj : j' < j ∧ j' < segs.length, ((segs[j']'hj.2).head?.map Fin.val = some v ∨
      (segs[j']'hj.2).getLast?.map Fin.val = some v)

theorem ndJ_succ {j : ℕ} (hj : j < segs.length) :
    markEnds (ind (ndJ x segs j)) (segs[j]).length ((segs[j].map Fin.val).getD 0 0)
      ((segs[j].map Fin.val).getD ((segs[j]).length - 1) 0) = ind (ndJ x segs (j + 1)) := by
  unfold markEnds
  split_ifs with hpos
  · rw [update_ind, update_ind]
    congr 1
    funext v
    obtain ⟨y, Q, hQ⟩ : ∃ y Q, segs[j] = y :: Q := by
      cases hc : segs[j] with
      | nil => rw [hc] at hpos; simp at hpos
      | cons y Q => exact ⟨y, Q, rfl⟩
    have hlast : (segs[j].map Fin.val).getD ((segs[j]).length - 1) 0 =
        ((y :: Q).getLast (by simp)).val := by
      rw [hQ, List.getLast_eq_getElem, List.getD_eq_getElem _ _ (by simp), List.getElem_map]
    have hhead : (segs[j].map Fin.val).getD 0 0 = y.val := by rw [hQ]; simp
    rw [hlast, hhead]
    apply propext
    simp only [ndJ]
    constructor
    · rintro (((h1 | h2 | ⟨j', hj', h3⟩) | h4) | h5)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨j', ⟨by omega, hj'.2⟩, h3⟩)
      · exact Or.inr (Or.inr ⟨j, ⟨by omega, hj⟩, Or.inl (by rw [hQ, h4]; simp)⟩)
      · exact Or.inr (Or.inr ⟨j, ⟨by omega, hj⟩, Or.inr (by
          rw [hQ, h5, List.getLast?_eq_some_getLast (by simp)]; simp)⟩)
    · rintro (h1 | h2 | ⟨j', hj', h3⟩)
      · exact Or.inl (Or.inl (Or.inl h1))
      · exact Or.inl (Or.inl (Or.inr (Or.inl h2)))
      · by_cases hjj : j' = j
        · subst hjj
          rcases h3 with h3 | h3
          · rw [hQ] at h3; simp at h3; exact Or.inl (Or.inr h3.symm)
          · rw [hQ, List.getLast?_eq_some_getLast (by simp)] at h3
            simp at h3; exact Or.inr h3.symm
        · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨j', ⟨by omega, hj'.2⟩, h3⟩)))
  · have hnil : segs[j] = [] := List.eq_nil_of_length_eq_zero (by omega)
    congr 1
    funext v
    apply propext
    simp only [ndJ]
    constructor
    · rintro (h1 | h2 | ⟨j', hj', h3⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨j', ⟨by omega, hj'.2⟩, h3⟩)
    · rintro (h1 | h2 | ⟨j', hj', h3⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · by_cases hjj : j' = j
        · subst hjj; rw [hnil] at h3; simp at h3
        · exact Or.inr (Or.inr ⟨j', ⟨by omega, hj'.2⟩, h3⟩)

theorem ind_ndJ_length {v : ℕ} (hv : v < x.n + 1) :
    ind (ndJ x segs segs.length) v = if ndB x segs v then 1 else 0 := by
  simp only [ind]
  congr 1
  apply propext
  by_cases hvn : v = x.n
  · subst hvn; simp [ndJ, ndB_of_le (le_refl _)]
  have hvn' : v < x.n := by omega
  rw [show v = (⟨v, hvn'⟩ : Fin x.n).val from rfl, ndB_val]
  simp only [decide_eq_true_eq, fNodes, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, List.mem_toFinset, List.mem_flatMap, List.mem_append, Option.mem_toList, ndJ]
  constructor
  · rintro (h1 | ⟨u, hu⟩ | ⟨j', hj', h3⟩)
    · exact absurd h1 hvn
    · exact Or.inl ⟨u, Fin.ext hu⟩
    · refine Or.inr ⟨segs[j'], List.getElem_mem _, ?_⟩
      rcases h3 with h3 | h3
      · obtain ⟨y, hy, hyv⟩ := Option.map_eq_some_iff.mp h3
        exact Or.inl (by rw [hy]; exact congrArg some (Fin.ext hyv))
      · obtain ⟨y, hy, hyv⟩ := Option.map_eq_some_iff.mp h3
        exact Or.inr (by rw [hy]; exact congrArg some (Fin.ext hyv))
  · rintro (⟨u, hu⟩ | ⟨P, hP, h3⟩)
    · exact Or.inr (Or.inl ⟨u, by rw [hu]⟩)
    · obtain ⟨j', hj', rfl⟩ := List.mem_iff_getElem.mp hP
      refine Or.inr (Or.inr ⟨j', ⟨hj', hj'⟩, ?_⟩)
      rcases h3 with h3 | h3
      · exact Or.inl (by rw [h3]; rfl)
      · exact Or.inr (by rw [h3]; rfl)


/-! ### Facts on the layout used by the two loops -/

theorem getD_layout {j t : ℕ} (hj : j < (blocks x segs).length)
    (ht : t < ((blocks x segs)[j]).length) :
    (layout x segs).getD (lpos x segs j + t) 0 = ((blocks x segs)[j]).getD t 0 := by
  rw [layout_eq]; exact getD_flatten_take _ hj ht

theorem lpos_le (j : ℕ) : lpos x segs j ≤ (layout x segs).length := by
  rw [layout_eq]; exact length_flatten_take_le _ j

theorem wcur_le (j : ℕ) : wcur x j ≤ x.W.encList.length := by
  rw [encList_eq, wcur]
  have := length_flatten_take_le ((ivl x).map lenPre) j
  simp only [List.length_append, List.length_cons, List.length_nil, length_bvl]; omega

theorem le_length_encList : 3 + elemWallNumVerts h ≤ x.W.encList.length := by
  rw [encList_eq]; simp; omega

theorem scur_le (j : ℕ) : scur x segs j ≤ (encSegs92 segs).length := by
  rw [encSegs92_eq, scur]
  have := length_flatten_take_le ((sgl x segs).map lenPre) j
  simp only [List.length_cons]; omega

variable (x segs) in
/-- A bound on all the numbers that the program after `F` writes or reads, before the
compression: the word size must be large enough to hold it. -/
def bigB : ℕ := (layout x segs).length + x.W.encList.length + (encSegs92 segs).length +
  2 * (elemWallEdges h).length + h + elemWallNumVerts h + x.n + 8

theorem lt_of_mem_encList_w {w v : ℕ} (hB : bigB x segs < 2 ^ w) (hv : v ∈ x.W.encList) :
    v < 2 ^ w := by
  have := lt_of_mem_encList hv; unfold bigB at hB; omega

/-! ### The loop over the paths of the wall -/

/-- The loop over the paths of the wall. -/
def wallLoop (h : ℕ) : Cmd := forUp ri (.const (elemWallEdges h).length) wallBody

variable (x segs) in
/-- The invariant of the wall loop after `i` rounds, from the start state `s0`. -/
def wallInv (s0 : State) (i : ℕ) (s : State) : Prop :=
  s.regs rn = x.n ∧ s.regs rpos = lpos x segs i ∧ s.regs rcur = wcur x i ∧ s.regs ri = i ∧
    s.arrs aL = tab (layout x segs).length (preTab (layout x segs) (lpos x segs i)) ∧
    (∀ a, a ≠ aL → s.arrs a = s0.arrs a) ∧
    (∀ r, r ≠ rpos → r ≠ rcur → r ≠ rcnt → r ≠ rA → r ≠ rB → r ≠ rt → r ≠ ri →
      s.regs r = s0.regs r)

theorem wallStep {w : ℕ} {s0 : State} (hW0 : s0.arrs aW = x.W.encList)
    (hE0 : s0.arrs aEdge = edgeTab h) (hB : bigB x segs < 2 ^ w) {i : ℕ}
    (hi : i < (elemWallEdges h).length) :
    ⦃wallInv x segs s0 i⦄[w] wallBody
      ⦃fun s' => wallInv x segs s0 (i + 1) (s'.setReg ri (i + 1)) ∧ s'.regs ri = i⦄ ≤
        fun _ => 53 + 15 * x.n := by
  rintro s ⟨hrn, hpos, hcur, hri, hL, ha, hr⟩
  have hiB : i < (blocks x segs).length := by simp; omega
  have hbl := blocks_wall (x := x) (segs := segs) hi
  have hblen : ((blocks x segs)[i]).length = (x.W.internalVerts ⟨i, hi⟩).length + 3 := by
    rw [hbl]; simp
  obtain ⟨hc1, hc2⟩ := getD_encList_wall (x := x) hi
  obtain ⟨he1, he2⟩ := getD_edgeTab hi
  have hlen := length_internalVerts_le_of_isValid x.hW_valid.2.2 ⟨i, hi⟩
  have hV := le_length_encList (x := x)
  have hlp := lpos_succ (x := x) (segs := segs) (j := i) (by omega)
  have hlp2 := lpos_le (x := x) (segs := segs) (i + 1)
  have hwc := wcur_succ (x := x) hi
  have hwc2 := wcur_le (x := x) (i + 1)
  unfold bigB at hB
  have hcopy : ∀ t < (x.W.internalVerts ⟨i, hi⟩).length,
      x.W.encList.getD (wcur x i + 1 + t) 0 = (layout x segs).getD (lpos x segs i + 2 + t) 0 := by
    intro t ht
    rw [hc2 t ht, Nat.add_assoc, getD_layout hiB (by omega), hbl,
      show 2 + t = t + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_append _ _ _ _ (by simpa using ht)]
  have hb1 : x.W.encList.getD (3 + ((elemWallEdges h)[i]'hi).1.val) 0 =
      (layout x segs).getD (lpos x segs i + 1) 0 := by
    rw [getD_encList_bv _ (((elemWallEdges h)[i]'hi).1.2), getD_layout hiB (by omega), hbl,
      List.getD_cons_succ, List.getD_cons_zero]
  have hb2 : x.W.encList.getD (3 + ((elemWallEdges h)[i]'hi).2.val) 0 =
      (layout x segs).getD (lpos x segs i + 2 + (x.W.internalVerts ⟨i, hi⟩).length) 0 := by
    rw [getD_encList_bv _ (((elemWallEdges h)[i]'hi).2.2), Nat.add_assoc,
      getD_layout hiB (by omega), hbl,
      show 2 + (x.W.internalVerts ⟨i, hi⟩).length = (x.W.internalVerts ⟨i, hi⟩).length + 1 + 1
        by omega, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hsep : (layout x segs).getD (lpos x segs i) 0 = x.n := by
    rw [show lpos x segs i = lpos x segs i + 0 by rfl, getD_layout hiB (by omega), hbl,
      List.getD_cons_zero]
  have hu1 := ((elemWallEdges h)[i]'hi).1.2
  have hu2 := ((elemWallEdges h)[i]'hi).2.2
  have hvW : ∀ v ∈ x.W.encList, v < 2 ^ w :=
    fun v hv => lt_of_mem_encList_w (segs := segs) (by unfold bigB; omega) hv
  have hvE : ∀ v ∈ edgeTab h, v < 2 ^ w := fun v hv => by have := lt_of_mem_edgeTab hv; omega
  obtain ⟨s', t, ex, ht, hpos', hcur', hL', ha', hr'⟩ := wallBody_exec (w := w) (s := s)
    (Wa := x.W.encList) (Et := edgeTab h) (Lay := layout x segs) (kk := i)
    (cnt := (x.W.internalVerts ⟨i, hi⟩).length)
    (u1 := ((elemWallEdges h)[i]'hi).1.val) (u2 := ((elemWallEdges h)[i]'hi).2.val)
    hrn hpos hcur hri hL (by rw [ha aW (by decide), hW0]) (by rw [ha aEdge (by decide), hE0])
    hc1 hcopy he1 he2 hb1 hb2 hsep
    (by omega) (by omega) (by omega) (by omega) (by rw [length_edgeTab]; omega)
    hvW hvE (by omega) (by rw [length_edgeTab]; omega)
  have hri' : s'.regs ri = i := by
    rw [hr' ri (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hri]
  refine ⟨s', t, ex, by simp only; omega, ⟨?_, ?_, ?_, by simp, ?_, ?_, ?_⟩, hri'⟩
  · rw [State.setReg_regs_ne _ _ (by decide),
      hr' rn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrn]
  · rw [State.setReg_regs_ne _ _ (by decide), hpos', hlp, hblen]; omega
  · rw [State.setReg_regs_ne _ _ (by decide), hcur', hwc]
  · rw [State.setReg_arrs, hL', hlp, hblen, show lpos x segs i +
      ((x.W.internalVerts ⟨i, hi⟩).length + 3) = lpos x segs i + 3 +
      (x.W.internalVerts ⟨i, hi⟩).length by omega]
  · intro a hne; rw [State.setReg_arrs, ha' a hne, ha a hne]
  · intro q h1 h2 h3 h4 h5 h6 h7
    rw [State.setReg_regs_ne _ _ h7, hr' q h1 h2 h3 h4 h5 h6, hr q h1 h2 h3 h4 h5 h6 h7]

theorem wallLoop_exec {w : ℕ} {s0 : State} (hW0 : s0.arrs aW = x.W.encList)
    (hE0 : s0.arrs aEdge = edgeTab h) (hB : bigB x segs < 2 ^ w) (hI : wallInv x segs s0 0 s0) :
    ∃ s' t, Exec w (wallLoop h) s0 s' t ∧ t ≤ 3 + (elemWallEdges h).length * (60 + 15 * x.n) ∧
      wallInv x segs s0 (elemWallEdges h).length s' := by
  have hB' := hB; unfold bigB at hB'
  have := Triple.forUp_const (w := w) (wallInv x segs s0) (elemWallEdges h).length
    (53 + 15 * x.n) (r_i := ri) (hi := .const (elemWallEdges h).length) (body := wallBody)
    (by omega) (by omega) (fun i _ s hs => ⟨hs.2.2.2.1, ev_const (by omega)⟩)
    (fun i hi => wallStep hW0 hE0 hB hi) s0 hI
  obtain ⟨s', t, ex, ht, hs'⟩ := this
  refine ⟨s', t, ex, ?_, hs'⟩
  simp only [Expr.cost] at ht
  have : (elemWallEdges h).length * (1 + 6 + (53 + 15 * x.n)) =
      (elemWallEdges h).length * (60 + 15 * x.n) := by ring_nf
  omega

/-! ### The loop over the paths of `F` -/

theorem markEnds_congr {g : ℕ → ℕ} {cnt a b a' b' : ℕ} (h : 0 < cnt → a = a' ∧ b = b') :
    markEnds g cnt a b = markEnds g cnt a' b' := by
  unfold markEnds
  split_ifs with hc
  · rw [(h hc).1, (h hc).2]
  · rfl

theorem length_lt_encSegs : segs.length < (encSegs92 segs).length := by
  unfold encSegs92
  induction segs with
  | nil => simp
  | cons P segs ih =>
    simp only [List.flatMap_cons, List.length_cons, List.length_append, List.length_map] at ih ⊢
    omega

theorem lt_of_mem_encSegs (hnd : ∀ P ∈ segs, P.length ≤ x.n) {v : ℕ}
    (hv : v ∈ encSegs92 segs) : v ≤ (encSegs92 segs).length + x.n := by
  simp only [encSegs92, List.mem_cons, List.mem_flatMap, List.mem_map] at hv
  rcases hv with rfl | ⟨P, hP, rfl | ⟨y, -, rfl⟩⟩
  · have := length_lt_encSegs (segs := segs); omega
  · have := hnd P hP; omega
  · have := y.2; omega

/-- The loop over the paths of `F`. -/
def segLoop : Cmd := forUp ri (.read aF (.const 0)) segBody

variable (x segs) in
/-- The invariant of the loop over the paths of `F` after `j` rounds, from the start state
`s0`. -/
def segInv (s0 : State) (j : ℕ) (s : State) : Prop :=
  s.regs rn = x.n ∧ s.regs rpos = lpos x segs ((elemWallEdges h).length + j) ∧
    s.regs rcur = scur x segs j ∧ s.regs ri = j ∧
    s.arrs aL = tab (layout x segs).length
      (preTab (layout x segs) (lpos x segs ((elemWallEdges h).length + j))) ∧
    s.arrs aN = tab (x.n + 1) (ind (ndJ x segs j)) ∧
    (∀ a, a ≠ aL → a ≠ aN → s.arrs a = s0.arrs a) ∧
    (∀ r, r ≠ rpos → r ≠ rcur → r ≠ rcnt → r ≠ rA → r ≠ rB → r ≠ rt → r ≠ ri →
      s.regs r = s0.regs r)

theorem segStep {w : ℕ} {s0 : State} (hF0 : s0.arrs aF = encSegs92 segs)
    (hnd : ∀ P ∈ segs, P.length ≤ x.n) (hB : bigB x segs < 2 ^ w) {j : ℕ}
    (hj : j < segs.length) :
    ⦃segInv x segs s0 j⦄[w] segBody
      ⦃fun s' => segInv x segs s0 (j + 1) (s'.setReg ri (j + 1)) ∧ s'.regs ri = j⦄ ≤
        fun _ => 50 + 15 * x.n := by
  rintro s ⟨hrn, hpos, hcur, hri, hL, hN, ha, hr⟩
  have hjB : (elemWallEdges h).length + j < (blocks x segs).length := by simp; omega
  have hbl := blocks_seg (x := x) (segs := segs) hj
  have hblen := congrArg List.length hbl
  rw [List.length_cons, List.length_map] at hblen
  obtain ⟨hc1, hc2⟩ := getD_encSegs (x := x) hj
  have hlen := hnd _ (List.getElem_mem hj)
  have hlp := lpos_succ (x := x) (segs := segs) (j := (elemWallEdges h).length + j) (by omega)
  have hlp2 := lpos_le (x := x) (segs := segs) ((elemWallEdges h).length + j + 1)
  have hsc := scur_succ (x := x) hj
  have hsc2 := scur_le (x := x) (segs := segs) (j + 1)
  have hcopy : ∀ t < (segs[j]'hj).length, (encSegs92 segs).getD (scur x segs j + 1 + t) 0 =
      (layout x segs).getD (lpos x segs ((elemWallEdges h).length + j) + 1 + t) 0 := by
    intro t ht
    rw [hc2 t ht, Nat.add_assoc, getD_layout hjB (by omega), hbl, Nat.add_comm 1 t,
      List.getD_cons_succ]
  have hvert : ∀ t < (segs[j]'hj).length, (encSegs92 segs).getD (scur x segs j + 1 + t) 0 < x.n := by
    intro t ht
    rw [hc2 t ht, List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]
    exact Fin.isLt _
  have hsep : (layout x segs).getD (lpos x segs ((elemWallEdges h).length + j)) 0 = x.n := by
    rw [show lpos x segs ((elemWallEdges h).length + j) =
      lpos x segs ((elemWallEdges h).length + j) + 0 from rfl, getD_layout hjB (by omega), hbl,
      List.getD_cons_zero]
  have hvF : ∀ v ∈ encSegs92 segs, v < 2 ^ w := fun v hv => by
    have := lt_of_mem_encSegs hnd hv; unfold bigB at hB; omega
  unfold bigB at hB
  obtain ⟨s', t, ex, ht, hpos', hcur', hL', hN', ha', hr'⟩ := segBody_exec (w := w) (s := s)
    (Fa := encSegs92 segs) (Lay := layout x segs) (cnt := (segs[j]'hj).length)
    hrn hpos hcur hL (by rw [ha aF (by decide) (by decide), hF0]) hN hc1 hcopy hvert hsep
    (by omega) (by omega) hvF (by omega)
  have hri' : s'.regs ri = j := by
    rw [hr' ri (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hri]
  have hme : markEnds (ind (ndJ x segs j)) (segs[j]'hj).length
      ((encSegs92 segs).getD (scur x segs j + 1) 0)
      ((encSegs92 segs).getD (scur x segs j + (segs[j]'hj).length) 0) =
      markEnds (ind (ndJ x segs j)) (segs[j]'hj).length (((segs[j]'hj).map Fin.val).getD 0 0)
        (((segs[j]'hj).map Fin.val).getD ((segs[j]'hj).length - 1) 0) := by
    apply markEnds_congr
    intro hpos0
    constructor
    · rw [← Nat.add_zero (scur x segs j + 1), hc2 0 hpos0]
    · rw [show scur x segs j + (segs[j]'hj).length =
        scur x segs j + 1 + ((segs[j]'hj).length - 1) by omega, hc2 _ (by omega)]
  refine ⟨s', t, ex, by simp only; omega, ⟨?_, ?_, ?_, by simp, ?_, ?_, ?_, ?_⟩, hri'⟩
  · rw [State.setReg_regs_ne _ _ (by decide),
      hr' rn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrn]
  · rw [State.setReg_regs_ne _ _ (by decide), hpos', ← Nat.add_assoc, hlp, hblen]; omega
  · rw [State.setReg_regs_ne _ _ (by decide), hcur', hsc]
  · rw [State.setReg_arrs, hL', ← Nat.add_assoc, hlp, hblen, Nat.add_comm (segs[j]'hj).length 1,
      Nat.add_assoc]
  · rw [State.setReg_arrs, hN', ← ndJ_succ hj, hme]
  · intro a h1 h2; rw [State.setReg_arrs, ha' a h1 h2, ha a h1 h2]
  · intro q h1 h2 h3 h4 h5 h6 h7
    rw [State.setReg_regs_ne _ _ h7, hr' q h1 h2 h3 h4 h5 h6, hr q h1 h2 h3 h4 h5 h6 h7]

theorem segLoop_exec {w : ℕ} {s0 : State} (hF0 : s0.arrs aF = encSegs92 segs)
    (hnd : ∀ P ∈ segs, P.length ≤ x.n) (hB : bigB x segs < 2 ^ w)
    (hI : segInv x segs s0 0 s0) :
    ∃ s' t, Exec w segLoop s0 s' t ∧ t ≤ 4 + segs.length * (61 + 15 * x.n) ∧
      segInv x segs s0 segs.length s' := by
  have hB' := hB; unfold bigB at hB'
  have hlenF := length_lt_encSegs (segs := segs)
  have := Triple.forUp_const (w := w) (segInv x segs s0) segs.length
    (50 + 15 * x.n) (r_i := ri) (hi := .read aF (.const 0)) (body := segBody)
    (by omega) (by omega) (fun i _ s hs => ⟨hs.2.2.2.1, ev_read (ev_const (by omega))
      (by rw [hs.2.2.2.2.2.2.1 aF (by decide) (by decide), hF0]; omega)
      (by rw [hs.2.2.2.2.2.2.1 aF (by decide) (by decide), hF0, encSegs92]; rfl) (by omega)⟩)
    (fun i hi => segStep hF0 hnd hB hi) s0 hI
  obtain ⟨s', t, ex, ht, hs'⟩ := this
  refine ⟨s', t, ex, ?_, hs'⟩
  simp only [Expr.cost] at ht
  have : segs.length * (1 + 1 + 6 + (50 + 15 * x.n)) ≤ segs.length * (61 + 15 * x.n) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end Alg92

end GraphMinor.Compute
