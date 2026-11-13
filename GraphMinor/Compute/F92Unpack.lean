module

public import GraphMinor.Compute.Algorithm92FClaim
public import GraphMinor.Compute.Algorithm92F
public import GraphMinor.Compute.Algorithm92Route
public import GraphMinor.Compute.Algorithm94Init

/-!
# Graph Minors XIII, (9.2): Input Parsing and Wall Unpacking (`F92Unpack.lean`)

This file implements the first phase of the Word RAM program for `F92ProgClaim`
(Graph Minors XIII, (9.2), page 101):
- Parameterized wall and subwall unpacking (`f92ParseFixedWallProg`, `f92UnpackSubwallAtProg`)
  using only registers `≥ r_base` and arrays `≥ a_base`.
- Bitset difference (`sdiffBitSetProg`) to compute `(x.W_sub a).insideFinset =
  (x.W_sub a).vertexFinset \ (x.W_sub a).perimeterFinset`.
- Initialization (`f92InitProg`): copies `x.G.enc` into `a_G`, unpacks `x.W` to mark
  `x.W.vertexFinset` in `aHV a_base`, copies `x.W.encList` into `a_W`, copies the packed subwall
  encodings into `aSub a_base`, builds the simple-graph CSR adjacency lists of `x.G.toSimpleGraph`
  in `(aStart a_base, aEnd a_base, aEntries a_base)`, and restores `inArr`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

theorem length_encAlg92In_le {l m p h k r : ℕ} (x : Alg92Input l m p h k r) :
    (encAlg92In x).length ≤ (2 + 3 * x.G.numActivePairs) + (k + 1) * maxWallEncLen h x.n := by
  have hG : x.G.enc.length = 2 + 3 * x.G.numActivePairs := MultiDigraph.length_enc x.G
  have hW : x.W.encList.length ≤ maxWallEncLen h x.n := by
    have h1 := Alg91.length_encList_le_of_isValid x.hW_valid.2.2
    have h2 := length_elemWallEdges_le h
    unfold maxWallEncLen; omega
  have hsub : ∀ xs : List (Fin k),
      (xs.flatMap (fun j => (x.W_sub j).encList)).length ≤ xs.length * maxWallEncLen h x.n := by
    intro xs
    induction xs with
    | nil => simp
    | cons j xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hj : (x.W_sub j).encList.length ≤ maxWallEncLen h x.n :=
        length_encList_le_maxWallEncLen x.hW_valid.2.2 (x.hnondiv j).1
      rw [Nat.add_one_mul]; omega
  have hsub_tot := hsub (List.finRange k)
  rw [List.length_finRange] at hsub_tot
  unfold encAlg92In
  rw [List.length_append, List.length_append, Nat.add_mul, Nat.one_mul]
  omega

namespace Alg92

/-! ### Section 1: Array Layout Offsets above `a_base` -/

/-- Bitset array for `x.W.vertexFinset`. -/
abbrev aHV (a_base : ℕ) : Arr := a_base
/-- Array holding the packed subwall encodings `(List.finRange k).flatMap (fun j => (x.W_sub j).encList)`. -/
abbrev aSub (a_base : ℕ) : Arr := a_base + 1
/-- CSR start array for `x.G.toSimpleGraph`. -/
abbrev aStart (a_base : ℕ) : Arr := a_base + 2
/-- CSR end array for `x.G.toSimpleGraph`. -/
abbrev aEnd (a_base : ℕ) : Arr := a_base + 3
/-- CSR entries array for `x.G.toSimpleGraph`. -/
abbrev aEntries (a_base : ℕ) : Arr := a_base + 4
/-- Scratch array 1 (`inArr` backup, wall perimeter, etc.). -/
abbrev aTmp1 (a_base : ℕ) : Arr := a_base + 5
/-- Scratch array 2 (`toSimpleGraphProg` buffer, subwall perimeter, etc.). -/
abbrev aTmp2 (a_base : ℕ) : Arr := a_base + 6
/-- Scratch array 3 (`toSimpleGraphProg` degree array, etc.). -/
abbrev aTmp3 (a_base : ℕ) : Arr := a_base + 7
/-- BFS label array. -/
abbrev aLab92 (a_base : ℕ) : Arr := a_base + 8
/-- BFS parent array. -/
abbrev aPar92 (a_base : ℕ) : Arr := a_base + 9
/-- BFS queue array. -/
abbrev aQue92 (a_base : ℕ) : Arr := a_base + 10
/-- Bitset array for `segs.flatten.toFinset` during `F` construction. -/
abbrev aFset (a_base : ℕ) : Arr := a_base + 11
/-- Flat body of `encSegs92 segs` (without leading `segs.length`) during `F` construction. -/
abbrev aFbody (a_base : ℕ) : Arr := a_base + 12
/-- Bitset array for `(x.W_sub j).vertexFinset`. -/
abbrev aSubV (a_base j : ℕ) : Arr := a_base + 13 + 3 * j
/-- Bitset array for `(x.W_sub j).insideFinset`. -/
abbrev aSubIn (a_base j : ℕ) : Arr := a_base + 14 + 3 * j
/-- Array holding `(P j).map Fin.val` for the `j`-th subwall's `H`-path. -/
abbrev aPath (a_base j : ℕ) : Arr := a_base + 15 + 3 * j

/-- Unfold array layout abbreviations and `inArr`, then discharge by `omega`. -/
macro "f92_omega" : tactic =>
  `(tactic| (dsimp only [aHV, aSub, aStart, aEnd, aEntries, aTmp1, aTmp2, aTmp3,
    aLab92, aPar92, aQue92, aFset, aFbody, aSubV, aSubIn, aPath,
    Arr, Reg, inArr, outArr, outReg] at *; omega))

/-! ### Section 2: Parameterized Wall and Subwall Unpacking -/

/-- Process the `k`-th edge of `W : WallOfHeight h' G` using registers `r_base + 1 .. r_base + 4`
and position register `r_pos`:
1. `recordLenPrefixedGenProg a_src r_pos (r_base + 2) (r_base + 3)`
2. `markSliceGenProg a_src a_V (r_base + 2) (r_base + 3) (r_base + 4)`
3. If `WallOfHeight.isElemWallPerimEdge h' k = true`, marks `e.1`, `e.2`, and the slice
   `(r_base + 2, r_base + 3)` in `a_perim`. -/
def f92ProcessWallEdgeProg (h' : ℕ) (a_src a_V a_perim : Arr) (r_base r_pos : ℕ)
    (k : Fin (elemWallEdges h').length) : Cmd :=
  let e := (elemWallEdges h')[k.1]'k.2
  .seq (recordLenPrefixedGenProg a_src r_pos (r_base + 2) (r_base + 3))
    (.seq (markSliceGenProg a_src a_V (r_base + 2) (r_base + 3) (r_base + 4))
      (if WallOfHeight.isElemWallPerimEdge h' k then
        .seq (markBranchVertGenProg a_src a_perim (r_base + 1) e.1)
          (.seq (markBranchVertGenProg a_src a_perim (r_base + 1) e.2)
            (markSliceGenProg a_src a_perim (r_base + 2) (r_base + 3) (r_base + 4)))
      else .skip))

theorem f92ProcessWallEdgeProg_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (a_src a_V a_perim : ℕ) (r_base r_pos : ℕ)
    (k : Fin (elemWallEdges h').length)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hr_pos : r_base + 4 < r_pos)
    (pre_W pre_k suf_k : List ℕ) (SV SP : Finset (Fin n))
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h' < 2 ^ w)
    (htotW_w : (pre_W ++ W.encList).length < 2 ^ w)
    (hnext_w : (pre_k ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length < 2 ^ w)
    {s : State}
    (hsrcW : ∃ suf_W, s.arrs a_src = pre_W ++ W.encList ++ suf_W)
    (hsrc_k : s.arrs a_src =
      pre_k ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val) ++ suf_k)
    (hroff : s.regs (r_base + 1) = pre_W.length)
    (hrpos : s.regs r_pos = pre_k.length)
    (hbitsV : s.arrs a_V = bitSetList SV)
    (hbitsP : s.arrs a_perim = bitSetList SP) :
    ∃ s' t,
      Exec w (f92ProcessWallEdgeProg h' a_src a_V a_perim r_base r_pos k) s s' t ∧
      t ≤ 55 + n + 48 * (W.internalVerts k).length ∧
      s'.regs r_pos =
        (pre_k ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length ∧
      s'.arrs a_V = bitSetList (SV ∪ (W.internalVerts k).toFinset) ∧
      s'.arrs a_perim =
        bitSetList (if WallOfHeight.isElemWallPerimEdge h' k then SP ∪ (W.subdivPathVerts k).toFinset else SP) ∧
      (∀ a : ℕ, a ≠ a_V → a ≠ a_perim → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < r_base + 2 ∨ r_base + 4 < r) → r ≠ r_pos → s'.regs r = s.regs r) := by
  -- 1. recordLenPrefixedGenProg a_src r_pos (r_base + 2) (r_base + 3)
  rcases recordLenPrefixedGenProg_exec a_src (r_pos := r_pos) (r_start := r_base + 2) (r_len := r_base + 3)
      (by omega) (by omega) (by omega) pre_k (W.internalVerts k) suf_k hw1 hnext_w hsrc_k hrpos with
    ⟨s₁, t₁, hex₁, ht₁, hr2_1, hr3_1, hrpos₁, harr₁, hreg₁⟩
  -- 2. markSliceGenProg a_src a_V (r_base + 2) (r_base + 3) (r_base + 4)
  let pre_slice := pre_k ++ [(W.internalVerts k).length]
  have hsrc_slice : s.arrs a_src = pre_slice ++ (W.internalVerts k).map Fin.val ++ suf_k := by
    simpa [pre_slice, List.append_assoc] using hsrc_k
  have hpre_slice_len : pre_slice.length = pre_k.length + 1 := by simp [pre_slice]
  have htot_slice_w : (pre_slice ++ (W.internalVerts k).map Fin.val).length < 2 ^ w := by
    simpa [pre_slice, List.append_assoc] using hnext_w
  rcases markSliceGenProg_exec a_src a_V (r_start := r_base + 2) (r_len := r_base + 3) (r_idx := r_base + 4)
      hne_sV (by omega) (by omega) pre_slice (W.internalVerts k) suf_k SV
      hw1 hn_w htot_slice_w
      (by rw [harr₁, hsrc_slice])
      (by rw [hpre_slice_len]; exact hr2_1)
      hr3_1
      (by rw [harr₁]; exact hbitsV) with
    ⟨s₂, t₂, hex₂, ht₂, hbitsV₂, harr₂, hreg₂⟩
  -- 3. Perimeter marking
  have hsrc₂ : s₂.arrs a_src = s.arrs a_src := by rw [harr₂ a_src hne_sV, harr₁]
  have hr1_2 : s₂.regs (r_base + 1) = pre_W.length := by
    rw [hreg₂ (r_base + 1) (by omega), hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hroff]
  have hr2_2 : s₂.regs (r_base + 2) = pre_slice.length := by
    rw [hreg₂ (r_base + 2) (by omega), hpre_slice_len, hr2_1]
  have hr3_2 : s₂.regs (r_base + 3) = (W.internalVerts k).length := by
    rw [hreg₂ (r_base + 3) (by omega), hr3_1]
  have hbitsP₂ : s₂.arrs a_perim = bitSetList SP := by
    rw [harr₂ a_perim hne_VP.symm, harr₁, hbitsP]
  have hperim_step :
      ∃ s₃ t₃,
        Exec w
          (if WallOfHeight.isElemWallPerimEdge h' k then
            .seq (markBranchVertGenProg a_src a_perim (r_base + 1) ((elemWallEdges h')[k.1]'k.2).1)
              (.seq (markBranchVertGenProg a_src a_perim (r_base + 1) ((elemWallEdges h')[k.1]'k.2).2)
                (markSliceGenProg a_src a_perim (r_base + 2) (r_base + 3) (r_base + 4)))
          else .skip)
          s₂ s₃ t₃ ∧
        t₃ ≤ 17 + 14 * (W.internalVerts k).length ∧
        s₃.arrs a_perim =
          bitSetList (if WallOfHeight.isElemWallPerimEdge h' k then SP ∪ (W.subdivPathVerts k).toFinset else SP) ∧
        (∀ a : ℕ, a ≠ a_perim → s₃.arrs a = s₂.arrs a) ∧
        (∀ r : ℕ, r ≠ r_base + 4 → s₃.regs r = s₂.regs r) := by
    cases hperim : WallOfHeight.isElemWallPerimEdge h' k
    · exact ⟨s₂, 1, .skip s₂, by omega, hbitsP₂, fun _ _ => rfl, fun _ _ => rfl⟩
    · rcases hsrcW with ⟨suf_W, hsrcW_eq⟩
      let e := (elemWallEdges h')[k.1]'k.2
      rcases markBranchVertGenProg_exec W a_src a_perim (r_base + 1) e.1 pre_W suf_W SP
          hw1 hn_w hc_w htotW_w (by rw [hsrc₂, hsrcW_eq]) hr1_2 hbitsP₂ with
        ⟨s₂a, t₂a, hex₂a, ht₂a, hbitsP_a, harr₂a, hreg₂a⟩
      rcases markBranchVertGenProg_exec W a_src a_perim (r_base + 1) e.2 pre_W suf_W
          (insert (W.branchVert e.1) SP)
          hw1 hn_w hc_w htotW_w
          (by rw [harr₂a a_src hne_sP, hsrc₂, hsrcW_eq])
          (by rw [hreg₂a (r_base + 1), hr1_2])
          hbitsP_a with
        ⟨s₂b, t₂b, hex₂b, ht₂b, hbitsP_b, harr₂b, hreg₂b⟩
      rcases markSliceGenProg_exec a_src a_perim (r_start := r_base + 2) (r_len := r_base + 3) (r_idx := r_base + 4)
          hne_sP (by omega) (by omega) pre_slice (W.internalVerts k) suf_k
          (insert (W.branchVert e.2) (insert (W.branchVert e.1) SP))
          hw1 hn_w htot_slice_w
          (by rw [harr₂b a_src hne_sP, harr₂a a_src hne_sP, hsrc₂, hsrc_slice])
          (by rw [hreg₂b (r_base + 2), hreg₂a (r_base + 2), hr2_2])
          (by rw [hreg₂b (r_base + 3), hreg₂a (r_base + 3), hr3_2])
          hbitsP_b with
        ⟨s₂c, t₂c, hex₂c, ht₂c, hbitsP_c, harr₂c, hreg₂c⟩
      have hbitsP_c' : s₂c.arrs a_perim = bitSetList (SP ∪ (W.subdivPathVerts k).toFinset) :=
        hbitsP_c.trans (congrArg bitSetList (insert_branchVerts_union_internal_eq_subdiv W k SP))
      refine ⟨s₂c, t₂a + (t₂b + t₂c),
        Exec.seq hex₂a (.seq hex₂b hex₂c),
        by omega,
        hbitsP_c',
        fun a ha => (harr₂c a ha).trans ((harr₂b a ha).trans (harr₂a a ha)),
        fun r hr => (hreg₂c r hr).trans ((hreg₂b r).trans (hreg₂a r))⟩
  rcases hperim_step with ⟨s₃, t₃, hex₃, ht₃, hbitsP₃, harr₃, hreg₃⟩
  refine ⟨s₃, t₁ + (t₂ + t₃),
    .seq hex₁ (.seq hex₂ hex₃),
    by omega,
    by rw [hreg₃ r_pos (by omega), hreg₂ r_pos (by omega), hrpos₁],
    by rw [harr₃ a_V hne_VP, hbitsV₂],
    hbitsP₃,
    fun a haV haP => by rw [harr₃ a haP, harr₂ a haV, harr₁],
    fun r hr hne_pos => by
      have hr4 : r ≠ r_base + 4 := by omega
      have hr2 : r ≠ r_base + 2 := by omega
      have hr3 : r ≠ r_base + 3 := by omega
      rw [hreg₃ r hr4, hreg₂ r hr4, hreg₁ r hne_pos hr2 hr3]⟩

/-- Process the first `j` edges of `W : WallOfHeight h' G`. -/
def f92ProcessWallEdgesUpTo (h' : ℕ) (a_src a_V a_perim : Arr) (r_base r_pos : ℕ) : ℕ → Cmd
  | 0 => .skip
  | j + 1 =>
    .seq (f92ProcessWallEdgesUpTo h' a_src a_V a_perim r_base r_pos j)
      (if hj : j < (elemWallEdges h').length then
        f92ProcessWallEdgeProg h' a_src a_V a_perim r_base r_pos ⟨j, hj⟩
      else .skip)

theorem f92ProcessWallEdgesUpTo_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (hW : W.IsValid)
    (a_src a_V a_perim : ℕ) (r_base r_pos : ℕ)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hr_pos : r_base + 4 < r_pos)
    (pre_W pre_edges suf : List ℕ) (SV₀ : Finset (Fin n))
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h' < 2 ^ w)
    (htotW_w : (pre_W ++ W.encList).length < 2 ^ w)
    (htotE_w :
      (pre_edges ++
        (List.finRange (elemWallEdges h').length).flatMap
          (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length <
        2 ^ w) :
    ∀ j (_hj : j ≤ (elemWallEdges h').length) {s : State}
      (_hsrcW : ∃ suf_W, s.arrs a_src = pre_W ++ W.encList ++ suf_W)
      (_hsrcE : s.arrs a_src =
        pre_edges ++
          (List.finRange (elemWallEdges h').length).flatMap
            (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val) ++
          suf)
      (_hroff : s.regs (r_base + 1) = pre_W.length)
      (_hrpos : s.regs r_pos = pre_edges.length)
      (_hbitsV : s.arrs a_V = bitSetList SV₀)
      (_hbitsP : s.arrs a_perim = bitSetList (∅ : Finset (Fin n))),
      ∃ s' t,
        Exec w (f92ProcessWallEdgesUpTo h' a_src a_V a_perim r_base r_pos j) s s' t ∧
        t ≤ 1 + j * (55 + 49 * n) ∧
        s'.regs r_pos =
          (pre_edges ++
            ((List.finRange (elemWallEdges h').length).take j).flatMap
              (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length ∧
        s'.arrs a_V = bitSetList (SV₀ ∪ edgeInternalFinsetUpTo W j) ∧
        s'.arrs a_perim = bitSetList (perimFinsetUpTo W j) ∧
        (∀ a : ℕ, a ≠ a_V → a ≠ a_perim → s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, (r < r_base + 2 ∨ r_base + 4 < r) → r ≠ r_pos → s'.regs r = s.regs r)
  | 0, _, s, _, _, _, hrpos, hbitsV, hbitsP => by
    exact ⟨s, 1, .skip s, by omega, by simpa using hrpos,
      by simpa using hbitsV, by simpa using hbitsP,
      fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | j + 1, hj, s, hsrcW, hsrcE, hroff, hrpos, hbitsV, hbitsP => by
    have hj_lt : j < (elemWallEdges h').length := by omega
    let f : Fin (elemWallEdges h').length → List ℕ :=
      fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val
    rcases f92ProcessWallEdgesUpTo_exec W hW a_src a_V a_perim r_base r_pos
        hne_sV hne_sP hne_VP hr_pos pre_W pre_edges suf SV₀
        hw1 hn_w hc_w htotW_w htotE_w j (by omega) hsrcW hsrcE hroff hrpos hbitsV hbitsP with
      ⟨s₁, t₁, hex₁, ht₁, hrpos₁, hbitsV₁, hbitsP₁, harr₁, hreg₁⟩
    have hsrc₁ : s₁.arrs a_src = s.arrs a_src := harr₁ a_src hne_sV hne_sP
    let pre_j := pre_edges ++ ((List.finRange (elemWallEdges h').length).take j).flatMap f
    let suf_j := ((List.finRange (elemWallEdges h').length).drop (j + 1)).flatMap f ++ suf
    have hsplit :
        pre_edges ++ (List.finRange (elemWallEdges h').length).flatMap f ++ suf =
          pre_j ++ f ⟨j, hj_lt⟩ ++ suf_j := by
      rw [Alg91.flatMap_finRange_eq_take_append_drop f j,
        Alg91.flatMap_drop_eq_cons f hj_lt]
      simp [pre_j, suf_j, List.append_assoc]
    have hnext_le :
        (pre_j ++ f ⟨j, hj_lt⟩).length ≤
          (pre_edges ++ (List.finRange (elemWallEdges h').length).flatMap f).length := by
      rw [Alg91.flatMap_finRange_eq_take_append_drop f j,
        Alg91.flatMap_drop_eq_cons f hj_lt]
      simp [pre_j, List.length_append]
    have hnext_w : (pre_j ++ f ⟨j, hj_lt⟩).length < 2 ^ w :=
      Nat.lt_of_le_of_lt hnext_le htotE_w
    rcases f92ProcessWallEdgeProg_exec W a_src a_V a_perim r_base r_pos ⟨j, hj_lt⟩
        hne_sV hne_sP hne_VP hr_pos pre_W pre_j suf_j
        (SV₀ ∪ edgeInternalFinsetUpTo W j) (perimFinsetUpTo W j)
        hw1 hn_w hc_w htotW_w hnext_w
        (by rcases hsrcW with ⟨suf_W, hW_eq⟩; exact ⟨suf_W, by rw [hsrc₁, hW_eq]⟩)
        (by rw [hsrc₁, hsrcE, hsplit])
        (by rw [hreg₁ (r_base + 1) (Or.inl (by omega)) (by omega), hroff])
        hrpos₁ hbitsV₁ hbitsP₁ with
      ⟨s₂, t₂, hex₂, ht₂, hrpos₂, hbitsV₂, hbitsP₂, harr₂, hreg₂⟩
    have hlen_int : (W.internalVerts ⟨j, hj_lt⟩).length ≤ n :=
      Alg91.length_internalVerts_le_of_isValid hW ⟨j, hj_lt⟩
    have ht₂_bound : t₂ ≤ 55 + 49 * n := by
      have : 48 * (W.internalVerts ⟨j, hj_lt⟩).length ≤ 48 * n :=
        Nat.mul_le_mul_left 48 hlen_int
      omega
    have hrpos₂' :
        s₂.regs r_pos =
          (pre_edges ++ ((List.finRange (elemWallEdges h').length).take (j + 1)).flatMap f).length := by
      rw [hrpos₂, Alg91.flatMap_take_succ_finRange f hj_lt, ← List.append_assoc]
    have hbitsV₂' : s₂.arrs a_V = bitSetList (SV₀ ∪ edgeInternalFinsetUpTo W (j + 1)) := by
      rw [hbitsV₂, edgeInternalFinsetUpTo_succ W hj_lt, Finset.union_assoc]
    have hbitsP₂' : s₂.arrs a_perim = bitSetList (perimFinsetUpTo W (j + 1)) := by
      rw [hbitsP₂, perimFinsetUpTo_succ W hj_lt]
    refine ⟨s₂, t₁ + t₂,
      by simpa [f92ProcessWallEdgesUpTo, hj_lt] using Exec.seq hex₁ hex₂,
      by rw [Nat.succ_mul]; omega,
      hrpos₂', hbitsV₂', hbitsP₂',
      fun a haV haP => (harr₂ a haV haP).trans (harr₁ a haV haP),
      fun r hr hne_pos => (hreg₂ r hr hne_pos).trans (hreg₁ r hr hne_pos)⟩

/-- Unpack a wall `W : WallOfHeight h' G` of known height `h'` from `a_src` starting at `r_pos`,
using `s.regs r_base = n` and scratch registers `r_base + 1 .. r_base + 4`.
Populates `IsBitSet W.vertexFinset a_V s'` and `IsBitSet W.perimeterFinset a_perim s'` and advances
`r_pos` to `(pre_W ++ W.encList).length`. -/
def f92ParseFixedWallProg (h' : ℕ) (a_src a_V a_perim : Arr) (r_base r_pos : ℕ) : Cmd :=
  .seq (.assign (r_base + 1) (.reg r_pos))
    (.seq (.alloc a_V (.reg r_base))
      (.seq (.alloc a_perim (.reg r_base))
        (.seq (markBranchVertListGenProg a_src a_V (r_base + 1) (List.finRange (elemWallNumVerts h')))
          (.seq (.assign r_pos (.op .add (.reg (r_base + 1)) (.const (3 + elemWallNumVerts h'))))
            (f92ProcessWallEdgesUpTo h' a_src a_V a_perim r_base r_pos
              (elemWallEdges h').length)))))

theorem f92ParseFixedWallProg_exec {w h h' n : ℕ} (hle : h' ≤ h)
    {G : MultiDigraph n} (W : WallOfHeight h' G) (hW : W.IsValid)
    (a_src a_V a_perim : ℕ) (r_base r_pos : ℕ)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hr_pos : r_base + 4 < r_pos)
    (pre_W suf_W : List ℕ)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htotW_w : (pre_W ++ W.encList).length < 2 ^ w)
    {s : State}
    (hsrcW : s.arrs a_src = pre_W ++ W.encList ++ suf_W)
    (hrn : s.regs r_base = n)
    (hrpos : s.regs r_pos = pre_W.length) :
    ∃ s' t,
      Exec w (f92ParseFixedWallProg h' a_src a_V a_perim r_base r_pos) s s' t ∧
      t ≤ parseWallCost h n ∧
      s'.regs r_pos = (pre_W ++ W.encList).length ∧
      IsBitSet W.vertexFinset a_V s' ∧
      IsBitSet W.perimeterFinset a_perim s' ∧
      (∀ a : ℕ, a ≠ a_V → a ≠ a_perim → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < r_base + 1 ∨ r_base + 4 < r) → r ≠ r_pos → s'.regs r = s.regs r) := by
  have hV_mono : elemWallNumVerts h' ≤ elemWallNumVerts h := Alg91.elemWallNumVerts_mono hle
  have hc'_w : 3 + elemWallNumVerts h' < 2 ^ w := by omega
  have hoff_w : pre_W.length < 2 ^ w := by simp [List.length_append] at htotW_w; omega
  -- 1. reg (r_base + 1) := reg r_pos
  let s₁ := s.setReg (r_base + 1) pre_W.length
  have hex₁ : Exec w (.assign (r_base + 1) (.reg r_pos)) s s₁ 2 :=
    .assign (by simp [hrpos, hoff_w])
  -- 2. alloc a_V (reg r_base)
  have hrn₁ : s₁.regs r_base = n := by
    simp [s₁, hrn]
  let s₂ := s₁.setArr a_V (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_V (.reg r_base)) s₁ s₂ (1 + n) :=
    .alloc (by simp [hrn₁, hn_w])
  -- 3. alloc a_perim (reg r_base)
  let s₃ := s₂.setArr a_perim (List.replicate n 0)
  have hex₃ : Exec w (.alloc a_perim (.reg r_base)) s₂ s₃ (1 + n) :=
    .alloc (by simp [s₂, hrn₁, hn_w])
  -- 4. markBranchVertListGenProg a_src a_V (r_base + 1) (List.finRange (elemWallNumVerts h'))
  have hsrcW₃ : s₃.arrs a_src = pre_W ++ W.encList ++ suf_W := by
    simp [s₃, s₂, s₁, hne_sP, hne_sV, hsrcW]
  have hbitsV₃ : s₃.arrs a_V = bitSetList (∅ : Finset (Fin n)) := by
    simp [s₃, s₂, hne_VP, Alg91.bitSetList_empty]
  rcases markBranchVertListGenProg_exec W a_src a_V (r_base + 1) hne_sV pre_W suf_W
      hw1 hn_w hc'_w htotW_w (List.finRange (elemWallNumVerts h')) ∅
      hsrcW₃ (by simp [s₃, s₂, s₁]) hbitsV₃ with
    ⟨s₄, t₄, hex₄, ht₄, hbitsV₄, harr₄, hreg₄⟩
  rw [Finset.empty_union] at hbitsV₄
  rw [List.length_finRange] at ht₄
  -- 5. reg r_pos := reg (r_base + 1) + (3 + elemWallNumVerts h')
  let hdr := [h', elemWallNumVerts h', (elemWallEdges h').length] ++
    (List.finRange (elemWallNumVerts h')).map (fun u => (W.branchVert u).1)
  let edgesPart :=
    (List.finRange (elemWallEdges h').length).flatMap
      (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)
  have hW_eq : W.encList = hdr ++ edgesPart := by
    unfold WallOfHeight.encList; rfl
  let pre_edges := pre_W ++ hdr
  have hpre_edges_len : pre_edges.length = pre_W.length + (3 + elemWallNumVerts h') := by
    simp [pre_edges, hdr]; omega
  have htotE_eq : pre_edges ++ edgesPart = pre_W ++ W.encList := by
    simp [pre_edges, hW_eq, List.append_assoc]
  have hr1_4 : s₄.regs (r_base + 1) = pre_W.length := by
    rw [hreg₄ (r_base + 1)]; simp [s₃, s₂, s₁]
  let s₅ := s₄.setReg r_pos pre_edges.length
  have hex₅ :
      Exec w (.assign r_pos (.op .add (.reg (r_base + 1)) (.const (3 + elemWallNumVerts h')))) s₄ s₅ 4 :=
    .assign (by
      rw [hpre_edges_len]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_4, hoff_w, hc'_w,
        show pre_W.length + (3 + elemWallNumVerts h') < 2 ^ w by
          have : pre_edges.length ≤ (pre_W ++ W.encList).length := by
            rw [← htotE_eq]; simp [List.length_append]
          omega])
  -- 6. f92ProcessWallEdgesUpTo
  have hsrc₅ : s₅.arrs a_src = s.arrs a_src := by
    simp [s₅, harr₄ a_src hne_sV, s₃, s₂, s₁, hne_sP, hne_sV]
  have hbitsP₅ : s₅.arrs a_perim = bitSetList (∅ : Finset (Fin n)) := by
    simp [s₅, harr₄ a_perim hne_VP.symm, s₃, Alg91.bitSetList_empty]
  rcases f92ProcessWallEdgesUpTo_exec W hW a_src a_V a_perim r_base r_pos
      hne_sV hne_sP hne_VP hr_pos
      pre_W pre_edges suf_W
      ((List.finRange (elemWallNumVerts h')).toFinset.image W.branchVert)
      hw1 hn_w hc'_w htotW_w (by rw [htotE_eq]; exact htotW_w)
      (elemWallEdges h').length le_rfl (s := s₅)
      ⟨suf_W, by rw [hsrc₅, hsrcW]⟩
      (by rw [hsrc₅, hsrcW, ← htotE_eq])
      (by
        have h1_pos : (r_base + 1 : Reg) ≠ r_pos := by omega
        dsimp [s₅]; rw [State.setReg_regs_ne _ _ h1_pos, hr1_4])
      (by simp [s₅])
      (by simp [s₅, hbitsV₄])
      hbitsP₅ with
    ⟨s₆, t₆, hex₆, ht₆, hrpos₆, hbitsV₆, hbitsP₆, harr₆, hreg₆⟩
  have htake_all :
      (List.finRange (elemWallEdges h').length).take (elemWallEdges h').length =
        List.finRange (elemWallEdges h').length :=
    List.take_of_length_le (by simp)
  rw [htake_all, htotE_eq] at hrpos₆
  rw [branchVerts_union_edgeInternalFinsetUpTo_full W] at hbitsV₆
  rw [perimFinsetUpTo_full W] at hbitsP₆
  have hE_le : (elemWallEdges h').length ≤ 2 * elemWallNumVerts h :=
    (length_elemWallEdges_le h').trans (Nat.mul_le_mul_left 2 hV_mono)
  have ht₆_bound : t₆ ≤ 1 + 2 * elemWallNumVerts h * (55 + 49 * n) := by
    have : (elemWallEdges h').length * (55 + 49 * n) ≤
        2 * elemWallNumVerts h * (55 + 49 * n) :=
      Nat.mul_le_mul_right _ hE_le
    omega
  refine ⟨s₆, 2 + ((1 + n) + ((1 + n) + (t₄ + (4 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by unfold parseWallCost; omega,
    hrpos₆,
    IsBitSet.of_bitSetList W.vertexFinset a_V s₆ hbitsV₆,
    IsBitSet.of_bitSetList W.perimeterFinset a_perim s₆ hbitsP₆,
    fun a haV haP => by
      rw [harr₆ a haV haP]
      simp [s₅, harr₄ a haV, s₃, s₂, s₁, haP, haV],
    fun r hr hne_pos => by
      have hr' : r < r_base + 2 ∨ r_base + 4 < r := by omega
      rw [hreg₆ r hr' hne_pos]
      have hr1 : (r : Reg) ≠ r_base + 1 := by omega
      dsimp [s₅]
      rw [State.setReg_regs_ne _ _ hne_pos, hreg₄ r]
      dsimp [s₃, s₂, s₁]
      rw [State.setReg_regs_ne _ _ hr1]⟩

/-- Dispatch over `1 ≤ m' ≤ m` on `reg (r_base + 1) = a_src[r_pos]` to call
`f92ParseFixedWallProg m' a_src a_V a_perim r_base r_pos`. -/
def f92UnpackSubwallDispatchProg (a_src a_V a_perim : Arr) (r_base r_pos : ℕ) : ℕ → Cmd
  | 0 => .skip
  | m + 1 =>
    .ite (.op .eq (.reg (r_base + 1)) (.const (m + 1)))
      (f92ParseFixedWallProg (m + 1) a_src a_V a_perim r_base r_pos)
      (f92UnpackSubwallDispatchProg a_src a_V a_perim r_base r_pos m)

/-- Unpack a subwall `W_sub : WallOfHeight h_sub G` with `1 ≤ h_sub ≤ h` from `a_src` at `r_pos`:
reads `reg (r_base + 1) := a_src[r_pos]` (`h_sub`) and dispatches to `f92ParseFixedWallProg h_sub`
to populate `IsBitSet W_sub.vertexFinset a_V`, `IsBitSet W_sub.perimeterFinset a_perim`, and
advance `r_pos` past `W_sub.encList`. -/
def f92UnpackSubwallAtProg (h : ℕ) (a_src a_V a_perim : Arr) (r_base r_pos : ℕ) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_src (.reg r_pos)))
    (f92UnpackSubwallDispatchProg a_src a_V a_perim r_base r_pos h)

theorem f92UnpackSubwallDispatchProg_exec {w h h_sub n : ℕ} (h1_sub : 1 ≤ h_sub)
    {G : MultiDigraph n} (W_sub : WallOfHeight h_sub G) (hW_sub : W_sub.IsValid)
    (a_src a_V a_perim : ℕ) (r_base r_pos : ℕ)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hr_pos : r_base + 4 < r_pos)
    (pre_W suf_W : List ℕ)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hh_w : h < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htotW_w : (pre_W ++ W_sub.encList).length < 2 ^ w) :
    ∀ m (_hm_le : m ≤ h) (_hh_le : h_sub ≤ m) {s : State}
      (_hsrcW : s.arrs a_src = pre_W ++ W_sub.encList ++ suf_W)
      (_hrn : s.regs r_base = n)
      (_hr1 : s.regs (r_base + 1) = h_sub)
      (_hrpos : s.regs r_pos = pre_W.length),
      ∃ s' t,
        Exec w (f92UnpackSubwallDispatchProg a_src a_V a_perim r_base r_pos m) s s' t ∧
        t ≤ 4 * m + parseWallCost h n ∧
        s'.regs r_pos = (pre_W ++ W_sub.encList).length ∧
        IsBitSet W_sub.vertexFinset a_V s' ∧
        IsBitSet W_sub.perimeterFinset a_perim s' ∧
        (∀ a : ℕ, a ≠ a_V → a ≠ a_perim → s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, (r < r_base + 1 ∨ r_base + 4 < r) → r ≠ r_pos → s'.regs r = s.regs r)
  | 0, _, hh_le, _, _, _, _, _ => by omega
  | m + 1, hm_le, hh_le, s, hsrcW, hrn, hr1, hrpos => by
    have hm1_w : m + 1 < 2 ^ w := by omega
    have hsub_w : h_sub < 2 ^ w := by omega
    have h0_w : 0 < 2 ^ w := by omega
    by_cases hh_eq : h_sub = m + 1
    · subst hh_eq
      have hcond :
          (Expr.op .eq (.reg (r_base + 1)) (.const (m + 1))).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1, hsub_w, hw1]
      rcases f92ParseFixedWallProg_exec hm_le W_sub hW_sub a_src a_V a_perim r_base r_pos
          hne_sV hne_sP hne_VP hr_pos pre_W suf_W hw1 hn_w hc_w htotW_w hsrcW hrn hrpos with
        ⟨s', t', hex', ht', hrpos', hV', hP', harr', hreg'⟩
      refine ⟨s', 3 + t',
        by simpa [f92UnpackSubwallDispatchProg] using Exec.ite_true hcond (by omega) hex',
        by omega, hrpos', hV', hP', harr', hreg'⟩
    · have hcond :
          (Expr.op .eq (.reg (r_base + 1)) (.const (m + 1))).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1, hsub_w, hm1_w, hh_eq, h0_w]
      rcases f92UnpackSubwallDispatchProg_exec h1_sub W_sub hW_sub a_src a_V a_perim r_base r_pos
          hne_sV hne_sP hne_VP hr_pos pre_W suf_W hw1 hn_w hh_w hc_w htotW_w
          m (by omega) (by omega) hsrcW hrn hr1 hrpos with
        ⟨s', t', hex', ht', hrpos', hV', hP', harr', hreg'⟩
      refine ⟨s', 3 + t',
        by simpa [f92UnpackSubwallDispatchProg] using Exec.ite_false hcond hex',
        by rw [Nat.succ_mul]; omega, hrpos', hV', hP', harr', hreg'⟩

theorem f92UnpackSubwallAtProg_exec {w h h_sub n : ℕ} (h1_sub : 1 ≤ h_sub) (hle : h_sub ≤ h)
    {G : MultiDigraph n} (W_sub : WallOfHeight h_sub G) (hW_sub : W_sub.IsValid)
    (a_src a_V a_perim : ℕ) (r_base r_pos : ℕ)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hr_pos : r_base + 4 < r_pos)
    (pre_W suf_W : List ℕ)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hh_w : h < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htotW_w : (pre_W ++ W_sub.encList).length < 2 ^ w)
    {s : State}
    (hsrcW : s.arrs a_src = pre_W ++ W_sub.encList ++ suf_W)
    (hrn : s.regs r_base = n)
    (hrpos : s.regs r_pos = pre_W.length) :
    ∃ s' t,
      Exec w (f92UnpackSubwallAtProg h a_src a_V a_perim r_base r_pos) s s' t ∧
      t ≤ 3 + 4 * h + parseWallCost h n ∧
      s'.regs r_pos = (pre_W ++ W_sub.encList).length ∧
      IsBitSet W_sub.vertexFinset a_V s' ∧
      IsBitSet W_sub.perimeterFinset a_perim s' ∧
      (∀ a : ℕ, a ≠ a_V → a ≠ a_perim → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < r_base + 1 ∨ r_base + 4 < r) → r ≠ r_pos → s'.regs r = s.regs r) := by
  have hoff_w : pre_W.length < 2 ^ w := by simp [List.length_append] at htotW_w; omega
  have hsub_w : h_sub < 2 ^ w := by omega
  have hin_len : pre_W.length < (s.arrs a_src).length := by
    rw [hsrcW]; simp [List.length_append, W_sub.length_encList]
  have hread_h : (s.arrs a_src)[pre_W.length]'hin_len = h_sub := by
    let rest := W_sub.encList ++ suf_W
    have hsplit : s.arrs a_src = pre_W ++ rest := by rw [hsrcW, List.append_assoc]
    have hlen2 : pre_W.length < (pre_W ++ rest).length := by
      simp [rest, W_sub.length_encList]
    apply Alg91.getElem_of_eq hsplit rfl (h₂ := hlen2)
    rw [List.getElem_append_right (le_refl pre_W.length)]
    simp [rest, WallOfHeight.encList]
  let s₁ := s.setReg (r_base + 1) h_sub
  have hex₁ : Exec w (.assign (r_base + 1) (.read a_src (.reg r_pos))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hrpos, hoff_w, hin_len, hread_h, hsub_w])
  rcases f92UnpackSubwallDispatchProg_exec h1_sub W_sub hW_sub a_src a_V a_perim r_base r_pos
      hne_sV hne_sP hne_VP hr_pos pre_W suf_W hw1 hn_w hh_w hc_w htotW_w
      h le_rfl hle (s := s₁)
      hsrcW
      (by simp [s₁, hrn])
      (by simp [s₁])
      (by
        have hpos1 : (r_pos : Reg) ≠ r_base + 1 := by omega
        dsimp [s₁]; rw [State.setReg_regs_ne _ _ hpos1, hrpos]) with
    ⟨s₂, t₂, hex₂, ht₂, hrpos₂, hV₂, hP₂, harr₂, hreg₂⟩
  refine ⟨s₂, 3 + t₂, .seq hex₁ hex₂, by omega,
    hrpos₂, hV₂, hP₂, harr₂,
    fun r hr hne_pos => by
      rw [hreg₂ r hr hne_pos]
      have hr1 : (r : Reg) ≠ r_base + 1 := by omega
      dsimp [s₁]
      rw [State.setReg_regs_ne _ _ hr1]⟩

/-! ### Section 3: Bitset Difference (`sdiffBitSetProg`) -/

/-- Build the indicator bitset `A \ B` in `a_dst` from `IsBitSet A a_A s` and `IsBitSet B a_B s`,
using loop register `r_u` and `n` in `r_n`. -/
def sdiffBitSetProg (a_A a_B a_dst : Arr) (r_n r_u : Reg) : Cmd :=
  .seq (.alloc a_dst (.reg r_n))
    (.seq (.assign r_u (.const 0))
      (forUp r_u (.reg r_n)
        (.write a_dst (.reg r_u) (.op .sub (.read a_A (.reg r_u)) (.read a_B (.reg r_u))))))

theorem sdiffBitSetProg_exec {w n : ℕ} (A B : Finset (Fin n))
    (a_A a_B a_dst : Arr) (r_n r_u : Reg)
    (hne_Ad : a_A ≠ a_dst) (hne_Bd : a_B ≠ a_dst) (hne_reg : r_n ≠ r_u)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hA : IsBitSet A a_A s) (hB : IsBitSet B a_B s)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (sdiffBitSetProg a_A a_B a_dst r_n r_u) s s' t ∧
      t ≤ 6 + 15 * n ∧
      IsBitSet (A \ B) a_dst s' ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_u → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_dst (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_dst (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_u 0
  have hex₂ : Exec w (.assign r_u (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (i : ℕ) (st : State) : Prop :=
    st.regs r_n = n ∧
    st.regs r_u = i ∧
    IsBitSet A a_A st ∧
    IsBitSet B a_B st ∧
    (∃ (hlen : (st.arrs a_dst).length = n),
      ∀ u : Fin n, u.1 < i →
        (st.arrs a_dst)[u.1]'(by rw [hlen]; exact u.2) =
          if u ∈ A \ B then 1 else 0) ∧
    (∀ a : Arr, a ≠ a_dst → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_u → st.regs r = s.regs r)
  have hloop :
      ⦃Inv 0⦄[w]
        forUp r_u (.reg r_n)
          (.write a_dst (.reg r_u) (.op .sub (.read a_A (.reg r_u)) (.read a_B (.reg r_u))))
      ⦃Inv n⦄ ≤
        fun _ => ((Expr.reg r_n).cost + 2) + n * ((Expr.reg r_n).cost + 6 + 7) := by
    apply Triple.forUp_const Inv n 7 hw hn_w
    · intro i _ st hinv
      exact ⟨hinv.2.1, by rw [Expr.eval, hinv.1]; simp [checkWord, hn_w]⟩
    · intro i hi st ⟨hrn_i, hru_i, hA_i, hB_i, ⟨hlen_i, hprev_i⟩, harr_i, hreg_i⟩
      let u : Fin n := ⟨i, hi⟩
      rcases hA_i with ⟨hA_len, hA_le, hA_mem⟩
      rcases hB_i with ⟨hB_len, hB_le, hB_mem⟩
      have hi_A : i < (st.arrs a_A).length := by rw [hA_len]; exact hi
      have hi_B : i < (st.arrs a_B).length := by rw [hB_len]; exact hi
      let a_u := (st.arrs a_A)[i]'hi_A
      let b_u := (st.arrs a_B)[i]'hi_B
      have hau_le : a_u ≤ 1 := hA_le u
      have hbu_le : b_u ≤ 1 := hB_le u
      have hau_w : a_u < 2 ^ w := by omega
      have hbu_w : b_u < 2 ^ w := by omega
      have hsub_w : a_u - b_u < 2 ^ w := by omega
      have hi_w : i < 2 ^ w := by omega
      let st' := st.writeArr a_dst i (a_u - b_u)
      have hex_step :
          Exec w (.write a_dst (.reg r_u) (.op .sub (.read a_A (.reg r_u)) (.read a_B (.reg r_u))))
            st st' 7 :=
        .write (by simp [Expr.eval, checkWord, hru_i, hi_w])
          (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_i, hi_w,
            hi_A, hi_B, a_u, b_u, hau_w, hbu_w, hsub_w])
          (by rw [hlen_i]; exact hi)
      refine ⟨st', 7, hex_step, by dsimp only; omega, ?_, hru_i⟩
      refine ⟨by simp [st', State.setReg, hne_reg, hrn_i],
        by simp [st', State.setReg],
        ⟨by simpa [st', hne_Ad] using hA_len,
          fun x => by simpa [st', hne_Ad] using hA_le x,
          fun x => by simpa [st', hne_Ad] using hA_mem x⟩,
        ⟨by simpa [st', hne_Bd] using hB_len,
          fun x => by simpa [st', hne_Bd] using hB_le x,
          fun x => by simpa [st', hne_Bd] using hB_mem x⟩,
        ⟨by simp [st', hlen_i],
          fun u' hu' => by
            simp only [st', State.setReg_arrs, State.writeArr_arrs_self]
            rcases Nat.lt_succ_iff_lt_or_eq.mp hu' with hlt | heq
            · rw [List.getElem_set_ne (by omega)]
              exact hprev_i u' hlt
            · have hu'_eq : u' = u := Fin.ext heq
              subst hu'_eq
              rw [List.getElem_set_self]
              have hmemA := hA_mem u
              have hmemB := hB_mem u
              change a_u ≠ 0 ↔ u ∈ A at hmemA
              change b_u ≠ 0 ↔ u ∈ B at hmemB
              by_cases huA : u ∈ A <;> by_cases huB : u ∈ B
              · have ha1 : a_u = 1 := by have := hmemA.mpr huA; omega
                have hb1 : b_u = 1 := by have := hmemB.mpr huB; omega
                simp [huA, huB, ha1, hb1]
              · have ha1 : a_u = 1 := by have := hmemA.mpr huA; omega
                have hb0 : b_u = 0 := not_ne_iff.mp (hmemB.not.mpr huB)
                simp [huA, huB, ha1, hb0]
              · have ha0 : a_u = 0 := not_ne_iff.mp (hmemA.not.mpr huA)
                simp [huA, huB, ha0]
              · have ha0 : a_u = 0 := not_ne_iff.mp (hmemA.not.mpr huA)
                simp [huA, huB, ha0]⟩,
        fun a ha => by simp [st', State.setReg, State.writeArr_arrs_ne _ _ _ ha, harr_i a ha],
        fun r hr => by simp [st', State.setReg, hr, hreg_i r hr]⟩
  have hinv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂, s₁, hne_reg, hrn],
      by simp [s₂],
      hA.of_arr_eq (by simp [s₂, s₁, hne_Ad]),
      hB.of_arr_eq (by simp [s₂, s₁, hne_Bd]),
      ⟨by simp [s₂, s₁], fun u hu => by omega⟩,
      fun a ha => by simp [s₂, s₁, ha],
      fun r hr => by simp [s₂, s₁, State.setReg, hr]⟩
  rcases hloop s₂ hinv₀ with ⟨s₃, t₃, hex₃, ht₃, _, _, _, _, ⟨hlen₃, hprev₃⟩, harr₃, hreg₃⟩
  dsimp [Expr.cost] at ht₃
  have hbit_out : IsBitSet (A \ B) a_dst s₃ := by
    refine ⟨hlen₃, fun u => ?_, fun u => ?_⟩
    · rw [hprev₃ u u.2]
      split_ifs <;> omega
    · rw [hprev₃ u u.2]
      split_ifs with h
      · simp [h]
      · simp [h]
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hbit_out, harr₃, hreg₃⟩

/-! ### Section 4: Initialization Routine (`f92InitProg`) -/

/-- Copy an entire array `a_src` into `a_dst` by first reading `.len a_src` into `r_len` and
then running `readSliceProg a_src (.const 0) a_dst (.reg r_len) r_scratch`. -/
def copyArrProg (a_src a_dst : Arr) (r_len r_scratch : Reg) : Cmd :=
  .seq (.assign r_len (.len a_src))
    (readSliceProg a_src (.const 0) a_dst (.reg r_len) r_scratch)

theorem copyArrProg_exec {w : ℕ} (a_src a_dst : ℕ) (r_len r_scratch : ℕ)
    (hne_arr : a_src ≠ a_dst) (hr_len : r_len < r_scratch)
    (xs : List ℕ) (hxs_w : ∀ v ∈ xs, v < 2 ^ w)
    (hw : 1 < 2 ^ w) (hlen_w : xs.length < 2 ^ w)
    {s : State} (hsrc : s.arrs a_src = xs) :
    ∃ s' t,
      Exec w (copyArrProg a_src a_dst r_len r_scratch) s s' t ∧
      t ≤ 16 * xs.length + 11 ∧
      s'.arrs a_dst = xs ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_len, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_len xs.length
  have hex₁ : Exec w (.assign r_len (.len a_src)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsrc, hlen_w])
  rcases readSliceProg_exec_full a_src a_dst (.const 0) r_len r_scratch hne_arr hr_len
      [] xs [] rfl rfl hxs_w hw (by simpa using hlen_w) (s := s₁)
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₁, hsrc])
      (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩
  dsimp [Expr.cost] at ht₂
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hdst₂, harr₂, fun r hr => ?_⟩
  rw [hreg₂ r (Or.inl (by omega))]
  simp [s₁, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_len)]

/-- Initialization program for `F92ProgClaim`:
Given `s₀.arrs inArr = encAlg92In x = x.G.enc ++ x.W.encList ++ sub_flat`:
1. Reads `x.n = inArr[0]` into `reg r_base`,
2. Computes `x.G.enc.length = 2 + 3 * inArr[1]` into `reg (r_base + 5)` and saves it in `reg (r_base + 6)`,
3. Copies `x.G.enc` into `a_G`,
4. Runs `f92ParseFixedWallProg h inArr (aHV a_base) (aTmp1 a_base) r_base (r_base + 5)` to mark
   `x.W.vertexFinset` in `aHV a_base` and advance `reg (r_base + 5)` to `(x.G.enc ++ x.W.encList).length`,
5. Copies `x.W.encList` into `a_W`,
6. Copies `sub_flat` into `aSub a_base`,
7. Saves `inArr` to `aTmp1 a_base`, runs `toSimpleGraphProg` on `a_G` to build
   `IsAdjList x.G.toSimpleGraph (aStart a_base) (aEnd a_base) (aEntries a_base)`, and restores `inArr`. -/
def f92InitProg (h : ℕ) (a_G a_W a_base r_base : ℕ) : Cmd :=
  .seq (.assign r_base (.read inArr (.const 0)))
    (.seq (.assign (r_base + 5) (.op .add (.const 2) (.op .mul (.const 3) (.read inArr (.const 1)))))
      (.seq (.assign (r_base + 6) (.reg (r_base + 5)))
        (.seq (readSliceProg inArr (.const 0) a_G (.reg (r_base + 5)) (r_base + 8))
          (.seq (f92ParseFixedWallProg h inArr (aHV a_base) (aTmp1 a_base) r_base (r_base + 5))
            (.seq (.assign (r_base + 7) (.op .sub (.reg (r_base + 5)) (.reg (r_base + 6))))
              (.seq (readSliceProg inArr (.reg (r_base + 6)) a_W (.reg (r_base + 7)) (r_base + 8))
                (.seq (.assign (r_base + 7) (.op .sub (.len inArr) (.reg (r_base + 5))))
                  (.seq (readSliceProg inArr (.reg (r_base + 5)) (aSub a_base) (.reg (r_base + 7)) (r_base + 8))
                    (.seq (copyArrProg inArr (aTmp1 a_base) (r_base + 7) (r_base + 8))
                      (.seq (toSimpleGraphProg a_G (aTmp2 a_base) (aTmp3 a_base)
                              (aStart a_base) (aEnd a_base) (aEntries a_base) (r_base + 1))
                        (copyArrProg (aTmp1 a_base) inArr (r_base + 7) (r_base + 8))))))))))))

theorem all_lt_encAlg92In {w l m p h k r : ℕ} (x : Alg92Input l m p h k r)
    (hn_w : x.n < 2 ^ w) (hm_w : x.G.numActivePairs < 2 ^ w) (he_w : x.G.numEdges < 2 ^ w)
    (hh_w : h < 2 ^ w) (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w) :
    ∀ v ∈ encAlg92In x, v < 2 ^ w := by
  intro v hv
  unfold encAlg92In at hv
  simp only [List.mem_append, List.mem_flatMap] at hv
  rcases hv with (hvG | hvW) | ⟨j, _, hvj⟩
  · exact all_lt_enc_multiDigraph x.G hn_w hm_w he_w v hvG
  · exact all_lt_encList_of_isValid x.W x.hW_valid.2.2 le_rfl hh_w hc2_w hn_w v hvW
  · exact all_lt_encList_of_isValid (x.W_sub j)
      (x.W.isValid_of_isSubwallOf x.hW_valid.2.2 (x.hnondiv j).1)
      (le_of_isSubwallOf (x.hnondiv j).1) hh_w hc2_w hn_w v hvj

theorem f92InitProg_exec {w l m p h k r : ℕ} (x : Alg92Input l m p h k r)
    (a_G a_W a_base r_base : ℕ)
    (hin_lt : inArr < a_base) (haG_lt : a_G < a_base) (haW_lt : a_W < a_base)
    (hne_in_G : inArr ≠ a_G) (hne_in_W : inArr ≠ a_W) (hne_G_W : a_G ≠ a_W)
    (hw3 : 3 < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hh_w : h < 2 ^ w)
    (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w)
    (he_w : x.G.numEdges < 2 ^ w)
    (hin_w : (encAlg92In x).length < 2 ^ w)
    {s₀ : State} (hs₀ : s₀.arrs inArr = encAlg92In x) :
    ∃ s' time,
      Exec w (f92InitProg h a_G a_W a_base r_base) s₀ s' time ∧
      time ≤ 200 + 48 * (encAlg92In x).length + parseWallCost h x.n +
        23 * x.n + 184 * x.G.numActivePairs ∧
      s'.regs r_base = x.n ∧
      s'.arrs a_G = x.G.enc ∧
      s'.arrs a_W = x.W.encList ∧
      IsBitSet x.W.vertexFinset (aHV a_base) s' ∧
      s'.arrs (aSub a_base) = (List.finRange k).flatMap (fun j => (x.W_sub j).encList) ∧
      IsAdjList x.G.toSimpleGraph (aStart a_base) (aEnd a_base) (aEntries a_base)
        (edgeNeighbors (edgeListOf x.G.toSimpleGraph)) s' ∧
      (s'.arrs (aEntries a_base)).length = 2 * (edgeListOf x.G.toSimpleGraph).length ∧
      (∀ a : ℕ, a < a_base → a ≠ a_G → a ≠ a_W → s'.arrs a = s₀.arrs a) ∧
      (∀ r < r_base, s'.regs r = s₀.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hc_w : 3 + elemWallNumVerts h < 2 ^ w := by omega
  have hin_lt_nat : (inArr : ℕ) < a_base := hin_lt
  have hin0 : (inArr : ℕ) = 0 := rfl
  let sub_flat := (List.finRange k).flatMap (fun j => (x.W_sub j).encList)
  have hin_eq : encAlg92In x = x.G.enc ++ x.W.encList ++ sub_flat := rfl
  have hG_len : x.G.enc.length = 2 + 3 * x.G.numActivePairs := MultiDigraph.length_enc x.G
  have hGW_len_le : (x.G.enc ++ x.W.encList).length ≤ (encAlg92In x).length := by
    rw [hin_eq]; simp [List.length_append]
  have hGW_w : (x.G.enc ++ x.W.encList).length < 2 ^ w := by omega
  have hG_len_w : x.G.enc.length < 2 ^ w := by
    simp [List.length_append] at hGW_w; omega
  have hm_w : x.G.numActivePairs < 2 ^ w := by omega
  have h3m_w : 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hin_all_w : ∀ v ∈ encAlg92In x, v < 2 ^ w :=
    all_lt_encAlg92In x hn_w hm_w he_w hh_w hc2_w
  have hin_len0 : 0 < (s₀.arrs inArr).length := by
    rw [hs₀, hin_eq]; simp [MultiDigraph.enc]
  have hin_len1 : 1 < (s₀.arrs inArr).length := by
    rw [hs₀, hin_eq]; simp [MultiDigraph.enc]
  have hin_get0 : (s₀.arrs inArr)[0]'hin_len0 = x.n := by
    simp [hs₀, hin_eq, MultiDigraph.enc]
  have hin_get1 : (s₀.arrs inArr)[1]'hin_len1 = x.G.numActivePairs := by
    simp [hs₀, hin_eq, MultiDigraph.enc]
  -- 1. reg r_base := inArr[0]
  let s₁ := s₀.setReg r_base x.n
  have hex₁ : Exec w (.assign r_base (.read inArr (.const 0))) s₀ s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hin_len0, hin_get0, hn_w])
  -- 2. reg (r_base + 5) := 2 + 3 * inArr[1]
  let s₂ := s₁.setReg (r_base + 5) x.G.enc.length
  have hex₂ :
      Exec w (.assign (r_base + 5) (.op .add (.const 2) (.op .mul (.const 3) (.read inArr (.const 1)))))
        s₁ s₂ 7 :=
    .assign (by
      rw [hG_len]
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hw1, hw3, hin_len1, hin_get1, hm_w, h3m_w, show 2 < 2 ^ w by omega,
        show 2 + 3 * x.G.numActivePairs < 2 ^ w by omega])
  -- 3. reg (r_base + 6) := reg (r_base + 5)
  let s₃ := s₂.setReg (r_base + 6) x.G.enc.length
  have hex₃ : Exec w (.assign (r_base + 6) (.reg (r_base + 5))) s₂ s₃ 2 :=
    .assign (by simp only [s₂, Expr.eval, checkWord, State.setReg_regs_self, hG_len_w, ↓reduceIte])
  -- 4. readSliceProg inArr 0 a_G (reg (r_base + 5)) (r_base + 8)
  have hG_enc_w : ∀ v ∈ x.G.enc, v < 2 ^ w :=
    all_lt_enc_multiDigraph x.G hn_w hm_w he_w
  rcases readSliceProg_exec_full inArr a_G (.const 0) (r_base + 5) (r_base + 8)
      hne_in_G (by omega) [] x.G.enc (x.W.encList ++ sub_flat)
      rfl rfl hG_enc_w hw1 (by simpa using hG_len_w) (s := s₃)
      (by simp [Expr.eval, checkWord, h0_w])
      (by
        change s₀.arrs inArr = [] ++ x.G.enc ++ (x.W.encList ++ sub_flat)
        rw [hs₀, hin_eq]; simp [List.append_assoc])
      (by simp [s₃, s₂]) with
    ⟨s₄, t₄, hex₄, ht₄, harrG_4, harr₄, hreg₄⟩
  -- 5. f92ParseFixedWallProg h inArr (aHV a_base) (aTmp1 a_base) r_base (r_base + 5)
  rcases f92ParseFixedWallProg_exec le_rfl x.W x.hW_valid.2.2
      inArr (aHV a_base) (aTmp1 a_base) r_base (r_base + 5)
      (by f92_omega)
      (by f92_omega)
      (by f92_omega)
      (by omega)
      x.G.enc sub_flat hw1 hn_w hc_w hGW_w (s := s₄)
      (by rw [harr₄ inArr hne_in_G]; exact hs₀)
      (by
        rw [hreg₄ r_base (Or.inl (by omega))]
        simp [s₃, s₂, s₁])
      (by
        rw [hreg₄ (r_base + 5) (Or.inl (by omega))]
        simp [s₃, s₂]) with
    ⟨s₅, t₅, hex₅, ht₅, hr5_5, hWV_5, _, harr₅, hreg₅⟩
  -- 6. reg (r_base + 7) := reg (r_base + 5) - reg (r_base + 6)
  have hr6_5 : s₅.regs (r_base + 6) = x.G.enc.length := by
    rw [hreg₅ (r_base + 6) (Or.inr (by omega)) (by omega), hreg₄ (r_base + 6) (Or.inl (by omega))]
    simp [s₃]
  have hr5_5' : s₅.regs (r_base + 5) = x.G.enc.length + x.W.encList.length := by
    rw [hr5_5, List.length_append]
  have hW_len_w : x.W.encList.length < 2 ^ w := by
    simp [List.length_append] at hGW_w; omega
  let s₆ := s₅.setReg (r_base + 7) x.W.encList.length
  have hex₆ : Exec w (.assign (r_base + 7) (.op .sub (.reg (r_base + 5)) (.reg (r_base + 6)))) s₅ s₆ 4 :=
    .assign (by
      have htot_w : x.G.enc.length + x.W.encList.length < 2 ^ w := by
        simpa [List.length_append] using hGW_w
      simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr5_5', hr6_5,
        hG_len_w, htot_w, hW_len_w, ↓reduceIte, Nat.add_sub_cancel_left])
  -- 7. readSliceProg inArr (reg (r_base + 6)) a_W (reg (r_base + 7)) (r_base + 8)
  have hW_enc_w : ∀ v ∈ x.W.encList, v < 2 ^ w :=
    all_lt_encList_of_isValid x.W x.hW_valid.2.2 le_rfl hh_w hc2_w hn_w
  have hin_6 : s₆.arrs inArr = x.G.enc ++ x.W.encList ++ sub_flat := by
    simp only [s₆, State.setReg_arrs]
    rw [harr₅ inArr (by f92_omega) (by f92_omega),
      harr₄ inArr hne_in_G]
    exact hs₀
  rcases readSliceProg_exec_full inArr a_W (.reg (r_base + 6)) (r_base + 7) (r_base + 8)
      hne_in_W (by omega) x.G.enc x.W.encList sub_flat
      rfl rfl hW_enc_w hw1 (by simpa [List.length_append] using hGW_w) (s := s₆)
      (by
        have hr6_6 : s₆.regs (r_base + 6) = x.G.enc.length := by
          simp [s₆, hr6_5]
        simp only [Expr.eval, checkWord, hr6_6, hG_len_w, ↓reduceIte])
      hin_6 (by simp [s₆]) with
    ⟨s₇, t₇, hex₇, ht₇, harrW_7, harr₇, hreg₇⟩
  -- 8. reg (r_base + 7) := len inArr - reg (r_base + 5)
  have hin_7 : s₇.arrs inArr = (x.G.enc ++ x.W.encList) ++ sub_flat ++ [] := by
    rw [harr₇ inArr hne_in_W, hin_6]; simp
  have hr5_7 : s₇.regs (r_base + 5) = (x.G.enc ++ x.W.encList).length := by
    rw [hreg₇ (r_base + 5) (Or.inl (by omega))]
    simp [s₆, hr5_5]
  have hin_len_7 : (s₇.arrs inArr).length = (x.G.enc ++ x.W.encList).length + sub_flat.length := by
    rw [hin_7, List.append_nil, List.length_append]
  have hin_len_eq : (s₇.arrs inArr).length = (encAlg92In x).length := by
    rw [hin_7, List.append_nil, ← hin_eq]
  have hsub_len_w : sub_flat.length < 2 ^ w := by omega
  let s₈ := s₇.setReg (r_base + 7) sub_flat.length
  have hex₈ : Exec w (.assign (r_base + 7) (.op .sub (.len inArr) (.reg (r_base + 5)))) s₇ s₈ 4 :=
    .assign (by
      have htot_w : (x.G.enc ++ x.W.encList).length + sub_flat.length < 2 ^ w := by omega
      simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hin_len_7, hr5_7,
        hGW_w, htot_w, hsub_len_w, ↓reduceIte, Nat.add_sub_cancel_left])
  -- 9. readSliceProg inArr (reg (r_base + 5)) (aSub a_base) (reg (r_base + 7)) (r_base + 8)
  have hsub_enc_w : ∀ v ∈ sub_flat, v < 2 ^ w := by
    intro v hv
    apply hin_all_w
    rw [hin_eq]
    simp [hv]
  rcases readSliceProg_exec_full inArr (aSub a_base) (.reg (r_base + 5)) (r_base + 7) (r_base + 8)
      (by f92_omega) (by omega) (x.G.enc ++ x.W.encList) sub_flat []
      rfl rfl hsub_enc_w hw1 (by omega) (s := s₈)
      (by
        have hr5_8 : s₈.regs (r_base + 5) = (x.G.enc ++ x.W.encList).length := by
          simp [s₈, hr5_7]
        simp only [Expr.eval, checkWord, hr5_8, hGW_w, ↓reduceIte])
      hin_7 (by simp [s₈]) with
    ⟨s₉, t₉, hex₉, ht₉, harrSub_9, harr₉, hreg₉⟩
  -- 10. copyArrProg inArr (aTmp1 a_base) (r_base + 7) (r_base + 8)
  have hin_9 : s₉.arrs inArr = encAlg92In x := by
    rw [harr₉ inArr (by f92_omega)]
    dsimp [s₈]
    simpa [hin_eq] using hin_7
  rcases copyArrProg_exec inArr (aTmp1 a_base) (r_base + 7) (r_base + 8)
      (by f92_omega) (by omega)
      (encAlg92In x) hin_all_w hw1 hin_w hin_9 with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, htmp1_10, harr₁₀, hreg₁₀⟩
  -- 11. toSimpleGraphProg a_G (aTmp2 a_base) (aTmp3 a_base) (aStart a_base) (aEnd a_base) (aEntries a_base) (r_base + 1)
  have haG_10 : s₁₀.arrs a_G = x.G.enc ++ [] := by
    rw [List.append_nil, harr₁₀ a_G (by f92_omega),
      harr₉ a_G (by f92_omega)]
    dsimp [s₈]
    rw [harr₇ a_G hne_G_W]
    dsimp [s₆]
    rw [harr₅ a_G (by f92_omega) (by f92_omega)]
    exact harrG_4
  rcases toSimpleGraphProg_exec x.G [] a_G (aTmp2 a_base) (aTmp3 a_base)
      (aStart a_base) (aEnd a_base) (aEntries a_base) (r_base + 1)
      (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega)
      (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega)
      hw3 hn_w (by rw [← hG_len]; exact hG_len_w) haG_10 with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, _, _, _, hadj₁₁, hent₁₁, harr₁₁, hreg₁₁⟩
  -- 12. copyArrProg (aTmp1 a_base) inArr (r_base + 7) (r_base + 8)
  have htmp1_11 : s₁₁.arrs (aTmp1 a_base) = encAlg92In x := by
    rw [harr₁₁ (aTmp1 a_base)
      (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega)]
    exact htmp1_10
  rcases copyArrProg_exec (aTmp1 a_base) inArr (r_base + 7) (r_base + 8)
      (by f92_omega) (by omega)
      (encAlg92In x) hin_all_w hw1 hin_w htmp1_11 with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hin_12, harr₁₂, hreg₁₂⟩
  have hex_all : Exec w (f92InitProg h a_G a_W a_base r_base) s₀ s₁₂
      (3 + (7 + (2 + (t₄ + (t₅ + (4 + (t₇ + (4 + (t₉ + (t₁₀ + (t₁₁ + t₁₂))))))))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂))))))))))
  dsimp [Expr.cost] at ht₄ ht₇ ht₉
  have ht_slices : t₄ + t₇ + t₉ ≤ 16 * (encAlg92In x).length + 28 := by
    have hlen_sum :
        x.G.enc.length + x.W.encList.length + sub_flat.length = (encAlg92In x).length := by
      rw [hin_eq, List.length_append, List.length_append]
    have hmul_sum :
        16 * x.G.enc.length + 16 * x.W.encList.length + 16 * sub_flat.length =
          16 * (encAlg92In x).length := by
      rw [← hlen_sum]; ring
    omega
  refine ⟨s₁₂, _, hex_all, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- s₁₂.regs r_base = x.n
    rw [hreg₁₂ r_base (by omega), hreg₁₁ r_base (by omega), hreg₁₀ r_base (by omega),
      hreg₉ r_base (Or.inl (by omega))]
    dsimp [s₈]
    rw [State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 7),
      hreg₇ r_base (Or.inl (by omega))]
    dsimp [s₆]
    rw [State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 7),
      hreg₅ r_base (Or.inl (by omega)) (by omega),
      hreg₄ r_base (Or.inl (by omega))]
    simp [s₃, s₂, s₁]
  · -- s₁₂.arrs a_G = x.G.enc
    rw [harr₁₂ a_G hne_in_G.symm,
      harr₁₁ a_G (by f92_omega) hne_in_G.symm (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega)]
    simpa using haG_10
  · -- s₁₂.arrs a_W = x.W.encList
    rw [harr₁₂ a_W hne_in_W.symm,
      harr₁₁ a_W (by f92_omega) hne_in_W.symm (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega),
      harr₁₀ a_W (by f92_omega),
      harr₉ a_W (by f92_omega)]
    exact harrW_7
  · -- IsBitSet x.W.vertexFinset (aHV a_base) s₁₂
    refine hWV_5.of_arr_eq ?_
    rw [harr₁₂ (aHV a_base) (by f92_omega),
      harr₁₁ (aHV a_base) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega),
      harr₁₀ (aHV a_base) (by f92_omega),
      harr₉ (aHV a_base) (by f92_omega)]
    dsimp [s₈]
    rw [harr₇ (aHV a_base) (by f92_omega)]
    rfl
  · -- s₁₂.arrs (aSub a_base) = sub_flat
    rw [harr₁₂ (aSub a_base) (by f92_omega),
      harr₁₁ (aSub a_base) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega),
      harr₁₀ (aSub a_base) (by f92_omega)]
    exact harrSub_9
  · -- IsAdjList
    exact hadj₁₁.of_arrs_eq
      (harr₁₂ (aStart a_base) (by f92_omega))
      (harr₁₂ (aEnd a_base) (by f92_omega))
      (harr₁₂ (aEntries a_base) (by f92_omega))
  · -- (s₁₂.arrs (aEntries a_base)).length
    rw [harr₁₂ (aEntries a_base) (by f92_omega)]
    exact hent₁₁
  · -- ∀ a < a_base, a ≠ a_G → a ≠ a_W → s₁₂.arrs a = s₀.arrs a
    intro a ha_lt haG haW
    by_cases hain : a = inArr
    · subst hain; exact hin_12.trans hs₀.symm
    · rw [harr₁₂ a hain,
        harr₁₁ a (by f92_omega) hain (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega),
        harr₁₀ a (by f92_omega),
        harr₉ a (by f92_omega)]
      dsimp [s₈]
      rw [harr₇ a haW]
      dsimp [s₆]
      rw [harr₅ a (by f92_omega) (by f92_omega),
        harr₄ a haG]
      rfl
  · -- ∀ r < r_base, s₁₂.regs r = s₀.regs r
    intro r hr
    rw [hreg₁₂ r (by omega), hreg₁₁ r (by omega), hreg₁₀ r (by omega),
      hreg₉ r (Or.inl (by omega))]
    dsimp [s₈]
    rw [State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 7),
      hreg₇ r (Or.inl (by omega))]
    dsimp [s₆]
    rw [State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 7),
      hreg₅ r (Or.inl (by omega)) (by omega),
      hreg₄ r (Or.inl (by omega))]
    dsimp [s₃, s₂, s₁]
    rw [State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 6),
      State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 5),
      State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base)]

/-- Constant factor for `f92InitProg` time bound in terms of `alg92Size x`. -/
def f92InitFactor (h k : ℕ) : ℕ :=
  664 + 214 * elemWallNumVerts h + 48 * (k + 1) * (4 + 3 * elemWallNumVerts h)

theorem f92InitCost_le_mul {l m p h k r : ℕ} (x : Alg92Input l m p h k r) :
    200 + 48 * (encAlg92In x).length + parseWallCost h x.n +
      23 * x.n + 184 * x.G.numActivePairs ≤
        f92InitFactor h k * alg92Size x := by
  have hsz1 : 1 ≤ alg92Size x := by unfold alg92Size; omega
  have hn : x.n ≤ alg92Size x := by unfold alg92Size; omega
  have hm : x.G.numActivePairs ≤ alg92Size x := by
    have := Alg91.numActivePairs_le_numEdges x.G
    unfold alg92Size; omega
  have hin := length_encAlg92In_le x
  have h1 : 200 * 1 ≤ 200 * alg92Size x := Nat.mul_le_mul_left 200 hsz1
  have h2 : 48 * (2 + 3 * x.G.numActivePairs) ≤ 240 * alg92Size x := by omega
  have h3 : 48 * ((k + 1) * maxWallEncLen h x.n) ≤
      48 * (k + 1) * (4 + 3 * elemWallNumVerts h) * alg92Size x := by
    have hmax := maxWallEncLen_le_mul h x.n (alg92Size x) hsz1 hn
    have hmul := Nat.mul_le_mul_left (48 * (k + 1)) hmax
    calc 48 * ((k + 1) * maxWallEncLen h x.n)
        = (48 * (k + 1)) * maxWallEncLen h x.n := by ring
      _ ≤ (48 * (k + 1)) * ((4 + 3 * elemWallNumVerts h) * alg92Size x) := hmul
      _ = 48 * (k + 1) * (4 + 3 * elemWallNumVerts h) * alg92Size x := by ring
  have h4 := parseWallCost_le_mul h x.n (alg92Size x) hsz1 hn
  rw [Nat.add_mul] at h4
  have h5 : 48 * (encAlg92In x).length ≤
      48 * (2 + 3 * x.G.numActivePairs) + 48 * ((k + 1) * maxWallEncLen h x.n) := by
    have := Nat.mul_le_mul_left 48 hin
    omega
  unfold f92InitFactor
  simp only [Nat.add_mul]
  omega

end Alg92

end GraphMinor.Compute

end
