module

public import GraphMinor.Compute.Algorithm74Lift

/-!
# Word RAM Implementation of Graph Minors XIII, (7.4) Algorithm

This file implements the single height-independent Word RAM program `alg74Prog` (depending only on
`p`) and proves `algorithm_7_4 : Algorithm74Statement`, completing the formalization of the
algorithmic part of Graph Minors XIII, (7.4) (page 90).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators

set_option linter.deprecated false
attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges coordOf alg74LiftRadius

theorem State.setReg_regs_nat (s : State) (r r' v : ℕ) :
    (s.setReg r v).regs r' = if r' = r then v else s.regs r' :=
  State.setReg_regs s r r' v

/-! ### Section 1: Word-Size Bounds, Input Indexing, and Bit-Slice Helpers -/

/-- Auxiliary array 2: maps each wall vertex `v < n` to `termLocCode x.W v`. -/
abbrev locArr : Arr := 2

/-- Auxiliary array 3: maps each elementary-wall edge index `k < E_J` to `((elemWallEdges h)[k]).1.1`. -/
abbrev edgeU1Arr : Arr := 3

/-- Auxiliary array 4: maps each elementary-wall edge index `k < E_J` to `((elemWallEdges h)[k]).2.1`. -/
abbrev edgeU2Arr : Arr := 4

theorem mul_pow_ge_mul_self (b : ℕ) (hb : 2 ≤ b) :
    ∀ c : ℕ, 1 ≤ c → c * b ≤ b ^ c
  | 0, hc => by omega
  | 1, _ => by simp
  | c + 1 + 1, _ => by
    have ih := mul_pow_ge_mul_self b hb (c + 1) (by omega)
    have hb_le : b ≤ b ^ (c + 1) := by
      calc b = b ^ 1 := (Nat.pow_one b).symm
        _ ≤ b ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc (c + 1 + 1) * b
      _ = (c + 1) * b + b := by ring
      _ ≤ b ^ (c + 1) + b ^ (c + 1) := Nat.add_le_add ih hb_le
      _ = 2 * b ^ (c + 1) := (Nat.two_mul _).symm
      _ ≤ b * b ^ (c + 1) := Nat.mul_le_mul_right _ hb
      _ = b ^ (c + 1 + 1) := by ring

theorem mul_lt_two_pow_wordSize {c : ℕ} (hc : 1 ≤ c) (m : ℕ) :
    c * (m + 2) < 2 ^ wordSize c m := by
  let b := 2 ^ (Nat.log 2 (m + 2) + 1)
  have hlt : m + 2 < b := lt_two_pow_log_succ m
  have hb2 : 2 ≤ b := by omega
  have h1 : c * (m + 2) < c * b := Nat.mul_lt_mul_of_pos_left hlt hc
  have h2 : c * b ≤ b ^ c := mul_pow_ge_mul_self b hb2 c hc
  have h3 : b ^ c = 2 ^ wordSize c m := by
    dsimp [b, wordSize]
    rw [← Nat.pow_mul, Nat.mul_comm]
  omega

theorem numActivePairs_le_numEdges {n : ℕ} (G : MultiDigraph n) :
    G.numActivePairs ≤ G.numEdges := by
  have hcard : G.numActivePairs = G.activePairsList.toFinset.card :=
    (List.toFinset_card_of_nodup G.nodup_activePairsList).symm
  rw [hcard, Finset.card_eq_sum_ones]
  have h1 :
      ∑ x ∈ G.activePairsList.toFinset, 1 ≤
        ∑ x ∈ G.activePairsList.toFinset, G.edgeMult x.1 x.2 := by
    apply Finset.sum_le_sum
    intro x hx
    rw [List.mem_toFinset, G.mem_activePairsList] at hx
    omega
  have h2 :
      ∑ x ∈ G.activePairsList.toFinset, G.edgeMult x.1 x.2 ≤
        ∑ x ∈ (Finset.univ : Finset (Fin n × Fin n)), G.edgeMult x.1 x.2 :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h3 :
      ∑ x ∈ (Finset.univ : Finset (Fin n × Fin n)), G.edgeMult x.1 x.2 = G.numEdges := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    rfl
  omega

theorem elemWallNumVerts_le_n {p r : ℕ} (x : Alg74Input p r) :
    elemWallNumVerts x.h ≤ x.n ∧ 2 * x.h ≤ elemWallNumVerts x.h := by
  have hcard := x.W.card_vertexFinset_of_isValid x.hW_valid.2.2
  have hle_n : x.W.vertexFinset.card ≤ x.n := by
    simpa using Finset.card_le_univ x.W.vertexFinset
  have heq := elemWallNumVerts_eq x.h
  have hprod : 2 * x.h + 2 ≤ (x.h + 1) * (2 * x.h + 2) := by nlinarith
  omega

theorem length_alg74Path_bounds {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    2 ≤ (alg74Path x e).length ∧ (alg74Path x e).length ≤ x.n := by
  rcases x.hpaths_valid (toChoose2Fin e) with ⟨_, hlen2, hnodup, _⟩
  have hcard : (alg74Path x e).length = (alg74Path x e).toFinset.card :=
    (List.toFinset_card_of_nodup hnodup).symm
  have hle : (alg74Path x e).toFinset.card ≤ x.n := by
    simpa using Finset.card_le_univ (alg74Path x e).toFinset
  exact ⟨hlen2, by omega⟩

theorem length_flatMap_of_const_len {α : Type*} (xs : List α) (n : ℕ) (g : α → List ℕ)
    (hg : ∀ a ∈ xs, (g a).length = n) :
    (xs.flatMap g).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, hg a List.mem_cons_self,
      ih (fun x hx => hg x (List.mem_cons_of_mem a hx)), List.length_cons, Nat.succ_mul]
    omega

theorem getElem_flatMap_of_const_len {α : Type*} (xs : List α) (n : ℕ) (g : α → List ℕ)
    (hg : ∀ a ∈ xs, (g a).length = n)
    (i : ℕ) (hi : i < xs.length) (j : ℕ) (hj : j < n) :
    (xs.flatMap g)[i * n + j]'(by rw [length_flatMap_of_const_len xs n g hg]; nlinarith) =
      (g (xs[i]'hi))[j]'(by rw [hg (xs[i]'hi) (List.getElem_mem hi)]; exact hj) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    have ha_len : (g a).length = n := hg a List.mem_cons_self
    have hrest : ∀ x ∈ rest, (g x).length = n :=
      fun x hx => hg x (List.mem_cons_of_mem a hx)
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem_append_left (by omega)
    | succ i' =>
      have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem_append_right (by rw [ha_len, Nat.succ_mul]; omega)]
      have hsub : (i' + 1) * n + j - (g a).length = i' * n + j := by
        rw [ha_len, Nat.succ_mul]
        omega
      simp only [hsub]
      exact ih hrest i' hi'

theorem getElem_congr_idx {α : Type*} (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length) :
    l[i]'hi = l[j]'(h ▸ hi) := by
  subst h
  rfl

theorem getElem_of_getElem? {α : Type*} {l : List α} {i : ℕ} {v : α}
    (h : l[i]? = some v) (hlt : i < l.length) :
    l[i]'hlt = v := by
  rw [List.getElem?_eq_getElem hlt] at h
  exact Option.some.inj h

/-- Integer location code of a vertex `v : Fin n` in `W : WallOfHeight h G`:
- `u.1 < elemWallNumVerts h` if `W.branchVert u = v`,
- `elemWallNumVerts h + k.1` if `v ∈ W.internalVerts k`,
- `elemWallNumVerts h + (elemWallEdges h).length` otherwise. -/
def termLocCode {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (v : Fin n) : ℕ :=
  match (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u => u.1
  | none =>
    match (List.finRange (elemWallEdges h).length).find?
        (fun k => decide (v ∈ W.internalVerts k)) with
    | some k => elemWallNumVerts h + k.1
    | none => elemWallNumVerts h + (elemWallEdges h).length

theorem termLocCode_branchVert {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) (u : Fin (elemWallNumVerts h)) :
    termLocCode W (W.branchVert u) = u.1 := by
  rcases hW with ⟨hbr_inj, _, _, _⟩
  unfold termLocCode
  cases hfind : (List.finRange (elemWallNumVerts h)).find?
      (fun u' => decide (W.branchVert u' = W.branchVert u)) with
  | some u' =>
    have heq : W.branchVert u' = W.branchVert u := by simpa using List.find?_some hfind
    exact congrArg Fin.val (hbr_inj heq)
  | none =>
    have hnone := List.find?_eq_none.mp hfind u (List.mem_finRange u)
    simp at hnone

theorem mem_internalVerts_iff_termLocCode {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid)
    (v : Fin n) (k : Fin (elemWallEdges h).length) :
    v ∈ W.internalVerts k ↔ termLocCode W v = elemWallNumVerts h + k.1 := by
  rcases hW with ⟨_, _, hnot_br, hdisj_int⟩
  unfold termLocCode
  constructor
  · intro hv
    have hfind1 :
        (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) = none := by
      rw [List.find?_eq_none]
      intro u _
      simp only [decide_eq_true_eq]
      intro heq
      exact hnot_br k u (heq ▸ hv)
    rw [hfind1]
    cases hfind2 : (List.finRange (elemWallEdges h).length).find?
        (fun k' => decide (v ∈ W.internalVerts k')) with
    | some k' =>
      have hk' : v ∈ W.internalVerts k' := by
        simpa using List.find?_some hfind2
      by_cases heq : k' = k
      · subst heq; rfl
      · exact False.elim (hdisj_int k' k heq hk' hv)
    | none =>
      have hnone := List.find?_eq_none.mp hfind2 k (List.mem_finRange k)
      simp [hv] at hnone
  · intro hloc
    cases hfind1 : (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
    | some u =>
      rw [hfind1] at hloc
      dsimp only at hloc
      have := u.2
      omega
    | none =>
      rw [hfind1] at hloc
      dsimp only at hloc
      cases hfind2 : (List.finRange (elemWallEdges h).length).find?
          (fun k' => decide (v ∈ W.internalVerts k')) with
      | some k' =>
        rw [hfind2] at hloc
        dsimp only at hloc
        have hk_eq : k' = k := Fin.ext (by omega)
        subst hk_eq
        simpa using List.find?_some hfind2
      | none =>
        rw [hfind2] at hloc
        dsimp only at hloc
        have := k.2
        omega

theorem mem_vertexFinset_iff {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (v : Fin n) :
    v ∈ W.vertexFinset ↔
      (∃ u : Fin (elemWallNumVerts h), W.branchVert u = v) ∨
      (∃ k : Fin (elemWallEdges h).length, v ∈ W.internalVerts k) := by
  unfold WallOfHeight.vertexFinset
  simp [List.mem_flatMap]

theorem termLocCode_lt_of_mem_vertexFinset {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) {v : Fin n} (hv : v ∈ W.vertexFinset) :
    termLocCode W v < elemWallNumVerts h + (elemWallEdges h).length := by
  rw [mem_vertexFinset_iff] at hv
  rcases hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
  · rw [termLocCode_branchVert hW u]
    have := u.2
    omega
  · rw [(mem_internalVerts_iff_termLocCode hW v k).mp hvk]
    have := k.2
    omega

/-- Representative branch vertex `u : Fin (elemWallNumVerts h)` of a location code
`loc < elemWallNumVerts h + (elemWallEdges h).length`. -/
def repVertOfLoc (h loc : ℕ) (hloc : loc < elemWallNumVerts h + (elemWallEdges h).length) :
    Fin (elemWallNumVerts h) :=
  if h1 : loc < elemWallNumVerts h then
    ⟨loc, h1⟩
  else
    ((elemWallEdges h)[loc - elemWallNumVerts h]'(by omega)).1

private theorem coordOf_repVertOfLoc_eq {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} {v : Fin n} (hv : v ∈ W.vertexFinset)
    (loc : ℕ) (hloc : loc < elemWallNumVerts h + (elemWallEdges h).length)
    (heq : termLocCode W v = loc) :
    coordOf h (repVertOfLoc h loc hloc) = repCoord W v := by
  unfold termLocCode at heq
  unfold repCoord
  cases hfind1 : (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u =>
    rw [hfind1] at heq
    dsimp only at heq
    subst heq
    simp [repVertOfLoc, u.2]
  | none =>
    rw [hfind1] at heq
    dsimp only at heq
    cases hfind2 : (List.finRange (elemWallEdges h).length).find?
        (fun k => decide (v ∈ W.internalVerts k)) with
    | some k =>
      rw [hfind2] at heq
      dsimp only at heq
      subst heq
      have hnot1 : ¬ (elemWallNumVerts h + k.1 < elemWallNumVerts h) := by omega
      have hsub : elemWallNumVerts h + k.1 - elemWallNumVerts h = k.1 := by omega
      simp [repVertOfLoc, hnot1, hsub]
    | none =>
      exfalso
      rw [mem_vertexFinset_iff] at hv
      rcases hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
      · have hnone := List.find?_eq_none.mp hfind1 u (List.mem_finRange u)
        simp at hnone
      · have hnone := List.find?_eq_none.mp hfind2 k (List.mem_finRange k)
        simp [hvk] at hnone

theorem coordOf_repVertOfLoc_termLocCode {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) {v : Fin n} (hv : v ∈ W.vertexFinset) :
    coordOf h (repVertOfLoc h (termLocCode W v) (termLocCode_lt_of_mem_vertexFinset hW hv)) =
      repCoord W v :=
  coordOf_repVertOfLoc_eq hv (termLocCode W v) (termLocCode_lt_of_mem_vertexFinset hW hv) rfl

theorem coarseCol_eq_ite {h x : ℕ} (hh : 1 ≤ h) (hx : x ≤ 2 * h + 1) :
    coarseCol h x =
      if x = 0 then 1 else if x = 2 * h + 1 then h else (x + 1) / 2 := by
  unfold coarseCol
  split_ifs <;> omega

/-- Encoded flat list of a slice `ks : List (Fin (elemWallEdges h).length)` of internal vertex lists. -/
def encInternalSlice {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (ks : List (Fin (elemWallEdges h).length)) : List ℕ :=
  ks.flatMap (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)

@[simp]
theorem encInternalSlice_nil {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) :
    encInternalSlice W [] = [] := rfl

@[simp]
theorem encInternalSlice_cons {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (k : Fin (elemWallEdges h).length) (ks : List (Fin (elemWallEdges h).length)) :
    encInternalSlice W (k :: ks) =
      (W.internalVerts k).length :: (W.internalVerts k).map Fin.val ++ encInternalSlice W ks := rfl

theorem wallEncList_eq_append_encInternalSlice {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) :
    W.encList =
      [h, elemWallNumVerts h, (elemWallEdges h).length] ++
      (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1) ++
      encInternalSlice W (List.finRange (elemWallEdges h).length) := rfl

theorem length_le_length_encInternalSlice {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (ks : List (Fin (elemWallEdges h).length)) :
    ks.length ≤ (encInternalSlice W ks).length := by
  induction ks with
  | nil => simp [encInternalSlice]
  | cons k rest ih =>
    rw [encInternalSlice_cons]
    simp only [List.length_append, List.length_cons]
    omega

/-- Encoded flat list of a slice `es : List (Fin (completeGraphEdges p).length)` of $H$-paths. -/
def encHPathsSlice {p r : ℕ} (x : Alg74Input p r)
    (es : List (Fin (completeGraphEdges p).length)) : List ℕ :=
  es.flatMap (fun e => (alg74Path x e).length :: (alg74Path x e).map Fin.val)

@[simp]
theorem encHPathsSlice_nil {p r : ℕ} (x : Alg74Input p r) :
    encHPathsSlice x [] = [] := rfl

@[simp]
theorem encHPathsSlice_cons {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length)
    (es : List (Fin (completeGraphEdges p).length)) :
    encHPathsSlice x (e :: es) =
      (alg74Path x e).length :: (alg74Path x e).map Fin.val ++ encHPathsSlice x es := rfl

theorem encHPathsSlice_finRange {p r : ℕ} (x : Alg74Input p r) :
    encHPathsSlice x (List.finRange (completeGraphEdges p).length) = encHPaths x.paths := by
  unfold encHPathsSlice encHPaths alg74Path toChoose2Fin
  have hlen := length_completeGraphEdges p
  have hmap :
      List.map (fun e : Fin (completeGraphEdges p).length =>
        (⟨e.1, hlen ▸ e.2⟩ : Fin (p.choose 2)))
        (List.finRange (completeGraphEdges p).length) =
      List.finRange (p.choose 2) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi₁ hi₂
      ext
      simp
  rw [← hmap, List.flatMap_map]

theorem length_encHPathsSlice_le {p r : ℕ} (x : Alg74Input p r) :
    ∀ es : List (Fin (completeGraphEdges p).length),
      (encHPathsSlice x es).length ≤ es.length * (x.n + 1)
  | [] => by simp
  | e :: rest => by
    have hb := (length_alg74Path_bounds x e).2
    have ih := length_encHPathsSlice_le x rest
    simp only [encHPathsSlice_cons, List.length_append, List.length_cons, List.length_map,
      Nat.succ_mul]
    omega

theorem getElem_encAlg74In_n {p r : ℕ} (x : Alg74Input p r)
    (hlt : 0 < (encAlg74In x).length) :
    (encAlg74In x)[0]'hlt = x.n := by
  apply getElem_of_getElem? _ hlt
  unfold encAlg74In MultiDigraph.enc
  simp

theorem getElem_encAlg74In_m {p r : ℕ} (x : Alg74Input p r)
    (hlt : 1 < (encAlg74In x).length) :
    (encAlg74In x)[1]'hlt = x.G.numActivePairs := by
  apply getElem_of_getElem? _ hlt
  unfold encAlg74In MultiDigraph.enc
  simp

theorem getElem_encAlg74In_active_fst {p r : ℕ} (x : Alg74Input p r)
    (idx : ℕ) (hidx : idx < x.G.numActivePairs)
    (hlt : 2 + 3 * idx < (encAlg74In x).length) :
    (encAlg74In x)[2 + 3 * idx]'hlt =
      (x.G.activePairsList[idx]'hidx).1.1 := by
  apply getElem_of_getElem? _ hlt
  unfold encAlg74In
  rw [List.getElem?_append_left (by simp [MultiDigraph.length_enc]; omega)]
  rw [List.getElem?_append_left (by simp [MultiDigraph.length_enc]; omega)]
  unfold MultiDigraph.enc
  rw [List.getElem?_append_right (by simp)]
  have hsub : 2 + 3 * idx - ([x.n, x.G.numActivePairs] : List ℕ).length = 3 * idx := by
    simp
  rw [hsub]
  have hlt_ft : 3 * idx < (x.G.flatTriples x.G.activePairsList).length := by
    rw [x.G.length_flatTriples]
    exact Nat.mul_lt_mul_of_pos_left hidx (by omega)
  rw [List.getElem?_eq_getElem hlt_ft]
  congr 1
  exact x.G.getElem_flatTriples_fst x.G.activePairsList idx hidx

theorem getElem_encAlg74In_active_snd {p r : ℕ} (x : Alg74Input p r)
    (idx : ℕ) (hidx : idx < x.G.numActivePairs)
    (hlt : 2 + 3 * idx + 1 < (encAlg74In x).length) :
    (encAlg74In x)[2 + 3 * idx + 1]'hlt =
      (x.G.activePairsList[idx]'hidx).2.1 := by
  apply getElem_of_getElem? _ hlt
  unfold encAlg74In
  rw [List.getElem?_append_left (by simp [MultiDigraph.length_enc]; omega)]
  rw [List.getElem?_append_left (by simp [MultiDigraph.length_enc]; omega)]
  unfold MultiDigraph.enc
  rw [List.getElem?_append_right (by simp; omega)]
  have hsub : 2 + 3 * idx + 1 - ([x.n, x.G.numActivePairs] : List ℕ).length = 3 * idx + 1 := by
    simp; omega
  rw [hsub]
  have hlt_ft : 3 * idx + 1 < (x.G.flatTriples x.G.activePairsList).length := by
    rw [x.G.length_flatTriples]
    change 3 * idx + 1 < 3 * x.G.numActivePairs
    omega
  rw [List.getElem?_eq_getElem hlt_ft]
  congr 1
  exact x.G.getElem_flatTriples_snd x.G.activePairsList idx hidx

private theorem getElem?_encAlg74In_wall {p r : ℕ} (x : Alg74Input p r)
    {j : ℕ} (hj : j < x.W.encList.length) :
    (encAlg74In x)[2 + 3 * x.G.numActivePairs + j]? = x.W.encList[j]? := by
  unfold encAlg74In
  have hlt1 : 2 + 3 * x.G.numActivePairs + j < (x.G.enc ++ x.W.encList).length := by
    simp [MultiDigraph.length_enc]; omega
  rw [List.getElem?_append_left hlt1]
  have hle1 : x.G.enc.length ≤ 2 + 3 * x.G.numActivePairs + j := by
    simp [MultiDigraph.length_enc]
  rw [List.getElem?_append_right hle1]
  have hsub : 2 + 3 * x.G.numActivePairs + j - x.G.enc.length = j := by
    rw [MultiDigraph.length_enc]; omega
  rw [hsub]

theorem getElem?_encAlg74In_h {p r : ℕ} (x : Alg74Input p r) :
    (encAlg74In x)[2 + 3 * x.G.numActivePairs]? = some x.h := by
  have h := getElem?_encAlg74In_wall x (j := 0) (by simp [WallOfHeight.length_encList])
  rw [Nat.add_zero] at h
  rw [h]
  unfold WallOfHeight.encList
  simp

theorem getElem?_encAlg74In_VJ {p r : ℕ} (x : Alg74Input p r) :
    (encAlg74In x)[2 + 3 * x.G.numActivePairs + 1]? = some (elemWallNumVerts x.h) := by
  rw [getElem?_encAlg74In_wall x (j := 1) (by simp [WallOfHeight.length_encList]; omega)]
  unfold WallOfHeight.encList
  simp

theorem getElem?_encAlg74In_EJ {p r : ℕ} (x : Alg74Input p r) :
    (encAlg74In x)[2 + 3 * x.G.numActivePairs + 2]? = some (elemWallEdges x.h).length := by
  rw [getElem?_encAlg74In_wall x (j := 2) (by simp [WallOfHeight.length_encList]; omega)]
  unfold WallOfHeight.encList
  simp

theorem getElem?_encAlg74In_branchVert {p r : ℕ} (x : Alg74Input p r)
    (u : Fin (elemWallNumVerts x.h)) :
    (encAlg74In x)[2 + 3 * x.G.numActivePairs + 3 + u.1]? =
      some (x.W.branchVert u).1 := by
  have hu := u.2
  have hidx : 2 + 3 * x.G.numActivePairs + 3 + u.1 = 2 + 3 * x.G.numActivePairs + (3 + u.1) := by
    omega
  rw [hidx, getElem?_encAlg74In_wall x (j := 3 + u.1) (by simp [WallOfHeight.length_encList]; omega)]
  unfold WallOfHeight.encList
  have hpre_len :
      ([x.h, elemWallNumVerts x.h, (elemWallEdges x.h).length] ++
        (List.finRange (elemWallNumVerts x.h)).map (fun u => (x.W.branchVert u).1)).length =
      3 + elemWallNumVerts x.h := by
    simp; omega
  rw [List.getElem?_append_left (by rw [hpre_len]; omega)]
  rw [List.getElem?_append_right (by simp)]
  have hsub2 :
      3 + u.1 - ([x.h, elemWallNumVerts x.h, (elemWallEdges x.h).length] : List ℕ).length = u.1 := by
    simp
  rw [hsub2]
  have hlt3 :
      u.1 < ((List.finRange (elemWallNumVerts x.h)).map (fun u => (x.W.branchVert u).1)).length := by
    simp [hu]
  rw [List.getElem?_eq_getElem hlt3]
  simp

/-- Predicate asserting that the slice `arr[offset .. offset + n]` is the `0`/`1` indicator of
`S : Finset (Fin n)`. -/
def IsBitSlice {n : ℕ} (arr : List ℕ) (offset : ℕ) (S : Finset (Fin n)) : Prop :=
  ∃ (_ : offset + n ≤ arr.length),
    ∀ v : Fin n, arr[offset + v.1]'(by have := v.2; omega) = if v ∈ S then 1 else 0

theorem isBitSlice_empty_of_zero {n : ℕ} (arr : List ℕ) (offset : ℕ)
    (hlen : offset + n ≤ arr.length)
    (hzero : ∀ v : Fin n, arr[offset + v.1]'(by have := v.2; omega) = 0) :
    IsBitSlice arr offset (∅ : Finset (Fin n)) :=
  ⟨hlen, fun v => by simp [hzero v]⟩

theorem isBitSlice_set_insert {n : ℕ} {arr : List ℕ} {offset : ℕ} {S : Finset (Fin n)}
    (h : IsBitSlice arr offset S) (v : Fin n) :
    IsBitSlice (arr.set (offset + v.1) 1) offset (insert v S) := by
  rcases h with ⟨hlen, hval⟩
  refine ⟨by rw [List.length_set]; exact hlen, fun u => ?_⟩
  rw [List.getElem_set]
  by_cases huv : u = v
  · subst huv
    simp
  · have hne : offset + v.1 ≠ offset + u.1 := by
      intro heq
      exact huv (Fin.ext (by omega))
    rw [if_neg hne, hval u]
    simp [huv]

theorem isBitSlice_set_other {n : ℕ} {arr : List ℕ} {offset : ℕ} {S : Finset (Fin n)}
    (h : IsBitSlice arr offset S) (idx val : ℕ)
    (hout : idx < offset ∨ offset + n ≤ idx) :
    IsBitSlice (arr.set idx val) offset S := by
  rcases h with ⟨hlen, hval⟩
  refine ⟨by rw [List.length_set]; exact hlen, fun u => ?_⟩
  have hne : idx ≠ offset + u.1 := by
    have := u.2
    omega
  rw [List.getElem_set_ne hne]
  exact hval u

/-- Command setting the bit for vertex `e_v` in color `gamma`'s bit slice of `outArr`
(at offset `2 + 2 * K + gamma * r_0`). -/
def markVertexCmd (K gamma : ℕ) (e_v : Expr) : Cmd :=
  .write outArr
    (.op .add (.const (2 + 2 * K))
      (.op .add (.op .mul (.const gamma) (.reg 0)) e_v))
    (.const 1)

theorem markVertexCmd_exec {w p K n : ℕ} (gamma : Fin p) (e_v : Expr) (v : Fin n)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hp_w : p < 2 ^ w)
    (hout_w : 2 + 2 * K + p * n < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hev : e_v.eval w s = some v.1)
    (hout_len : (s.arrs outArr).length = 2 + 2 * K + p * n) :
    let idx := 2 + 2 * K + gamma.1 * n + v.1
    let s' := s.writeArr outArr idx 1
    Exec w (markVertexCmd K gamma.1 e_v) s s' (e_v.cost + 8) ∧
    (s'.arrs outArr).length = 2 + 2 * K + p * n ∧
    (∀ {S : Finset (Fin n)},
      IsBitSlice (s.arrs outArr) (2 + 2 * K + gamma.1 * n) S →
      IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * n) (insert v S)) ∧
    (∀ (gamma' : Fin p) {S' : Finset (Fin n)}, gamma' ≠ gamma →
      IsBitSlice (s.arrs outArr) (2 + 2 * K + gamma'.1 * n) S' →
      IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma'.1 * n) S') ∧
    (∀ i : ℕ, i < 2 + 2 * K →
      (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
    s'.regs = s.regs ∧
    (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) := by
  have hp_pos : 1 ≤ p := by have := gamma.2; omega
  have hgn_le : gamma.1 * n + v.1 < p * n := by
    have h1 : (gamma.1 + 1) * n ≤ p * n := Nat.mul_le_mul_right n gamma.2
    rw [Nat.add_mul, Nat.one_mul] at h1
    have := v.2
    omega
  have hn_w : n < 2 ^ w := by
    have : 1 * n ≤ p * n := Nat.mul_le_mul_right n hp_pos
    omega
  have hg_w : gamma.1 < 2 ^ w := Nat.lt_trans gamma.2 hp_w
  have hgn_w : gamma.1 * n < 2 ^ w := by omega
  have hgnv_w : gamma.1 * n + v.1 < 2 ^ w := by omega
  have h2K_w : 2 + 2 * K < 2 ^ w := by omega
  have hidx_lt : 2 + 2 * K + (gamma.1 * n + v.1) < (s.arrs outArr).length := by omega
  have hidx_w : 2 + 2 * K + (gamma.1 * n + v.1) < 2 ^ w := by omega
  have heval_idx :
      (Expr.op .add (.const (2 + 2 * K))
        (.op .add (.op .mul (.const gamma.1) (.reg 0)) e_v)).eval w s =
      some (2 + 2 * K + gamma.1 * n + v.1) := by
    simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0, hev,
      h2K_w, hg_w, hn_w, hgn_w, hgnv_w, hidx_w, ↓reduceIte]
    rw [← Nat.add_assoc]
  have heval_val : (Expr.const 1).eval w s = some 1 := by
    simp [Expr.eval, checkWord, hw1]
  have hex : Exec w (markVertexCmd K gamma.1 e_v) s
      (s.writeArr outArr (2 + 2 * K + gamma.1 * n + v.1) 1) (e_v.cost + 8) := by
    have hcost :
        (Expr.op .add (.const (2 + 2 * K))
          (.op .add (.op .mul (.const gamma.1) (.reg 0)) e_v)).cost +
        (Expr.const 1).cost + 1 = e_v.cost + 8 := by
      simp [Expr.cost]; omega
    rw [← hcost]
    exact .write heval_idx heval_val (by omega)
  refine ⟨hex, by simp [hout_len], fun hS => isBitSlice_set_insert hS v,
    fun gamma' S' hne hS' => ?_, fun i hi => ?_, rfl, fun a ha => State.writeArr_arrs_ne _ _ _ ha⟩
  · apply isBitSlice_set_other hS'
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · right
      have h1 : (gamma'.1 + 1) * n ≤ gamma.1 * n := Nat.mul_le_mul_right n hlt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    · left
      have h1 : (gamma.1 + 1) * n ≤ gamma'.1 * n := Nat.mul_le_mul_right n hgt
      rw [Nat.add_mul, Nat.one_mul] at h1
      have := v.2
      omega
  · simp only [State.writeArr_arrs_self, List.getElem?_set]
    have hne : 2 + 2 * K + gamma.1 * n + v.1 ≠ i := by omega
    simp [hne]

/-! ### Section 2: Header Initialization, One-Pass Wall Scan, and Arithmetic Wall-Edge Table -/

/-- Step 1 (`initCmd p`): reads `n`, `m'`, `w_off`, `h`, `V_J`, `E_J`, computes `W = 2 * h + 2`,
and allocates `outArr`, `locArr`, `edgeU1Arr`, and `edgeU2Arr`. -/
def initCmd (p : ℕ) : Cmd :=
  let K := (completeGraphEdges p).length
  .seq (.assign 0 (.read inArr (.const 0)))
    (.seq (.assign 1 (.read inArr (.const 1)))
      (.seq (.assign 2 (.op .add (.const 2) (.op .mul (.const 3) (.reg 1))))
        (.seq (.assign 3 (.read inArr (.reg 2)))
          (.seq (.assign 12 (.read inArr (.op .add (.reg 2) (.const 1))))
            (.seq (.assign 13 (.read inArr (.op .add (.reg 2) (.const 2))))
              (.seq (.assign 14 (.op .add (.op .mul (.const 2) (.reg 3)) (.const 2)))
                (.seq (.alloc outArr (.op .add (.const (2 + 2 * K)) (.op .mul (.const p) (.reg 0))))
                  (.seq (.write outArr (.const 0) (.const p))
                    (.seq (.write outArr (.const 1) (.const K))
                      (.seq (.alloc locArr (.reg 0))
                        (.seq (.alloc edgeU1Arr (.reg 13))
                          (.alloc edgeU2Arr (.reg 13)))))))))))))

theorem initCmd_exec {w p r : ℕ} (x : Alg74Input p r)
    {s : State}
    (hw3 : 3 < 2 ^ w)
    (hp_w : p < 2 ^ w)
    (hK_w : (completeGraphEdges p).length < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hW_w : 2 * x.h + 2 < 2 ^ w)
    (hVJ_w : elemWallNumVerts x.h < 2 ^ w)
    (hEJ_w : (elemWallEdges x.h).length < 2 ^ w)
    (hin_w : (encAlg74In x).length < 2 ^ w)
    (hout_w : 2 + 2 * (completeGraphEdges p).length + p * x.n < 2 ^ w)
    (hin : s.arrs inArr = encAlg74In x) :
    let K := (completeGraphEdges p).length
    let V_J := elemWallNumVerts x.h
    let E_J := (elemWallEdges x.h).length
    ∃ s' t,
      Exec w (initCmd p) s s' t ∧
      t ≤ (p + 1) * x.n + 2 * E_J + 2 * K + 60 ∧
      s'.arrs inArr = encAlg74In x ∧
      s'.regs 0 = x.n ∧
      s'.regs 1 = x.G.numActivePairs ∧
      s'.regs 2 = 2 + 3 * x.G.numActivePairs ∧
      s'.regs 3 = x.h ∧
      s'.regs 12 = V_J ∧
      s'.regs 13 = E_J ∧
      s'.regs 14 = 2 * x.h + 2 ∧
      (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
      (s'.arrs outArr)[0]? = some p ∧
      (s'.arrs outArr)[1]? = some K ∧
      (∀ gamma : Fin p,
        IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * x.n) (∅ : Finset (Fin x.n))) ∧
      (s'.arrs locArr).length = x.n ∧
      (s'.arrs edgeU1Arr).length = E_J ∧
      (s'.arrs edgeU2Arr).length = E_J := by
  intro K V_J E_J
  change K < 2 ^ w at hK_w
  change V_J < 2 ^ w at hVJ_w
  change E_J < 2 ^ w at hEJ_w
  change 2 + 2 * K + p * x.n < 2 ^ w at hout_w
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hh_w : x.h < 2 ^ w := by omega
  have h2h_w : 2 * x.h < 2 ^ w := by omega
  have hin_len_ge : 2 + 3 * x.G.numActivePairs + 3 ≤ (encAlg74In x).length := by
    simp [encAlg74In, MultiDigraph.length_enc, WallOfHeight.length_encList]
    omega
  have hlen0 : 0 < (s.arrs inArr).length := by rw [hin]; omega
  have hlen1 : 1 < (s.arrs inArr).length := by rw [hin]; omega
  have hget0 : (s.arrs inArr)[0]'hlen0 = x.n := by
    simp only [hin]; exact getElem_encAlg74In_n x (by omega)
  have hget1 : (s.arrs inArr)[1]'hlen1 = x.G.numActivePairs := by
    simp only [hin]; exact getElem_encAlg74In_m x (by omega)
  let w_off := 2 + 3 * x.G.numActivePairs
  have hm_w : x.G.numActivePairs < 2 ^ w := by omega
  have h3m_w : 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hwoff_w : w_off < 2 ^ w := by dsimp [w_off]; omega
  have hwoff1_w : w_off + 1 < 2 ^ w := by dsimp [w_off]; omega
  have hwoff2_w : w_off + 2 < 2 ^ w := by dsimp [w_off]; omega
  have hlen_w0 : w_off < (s.arrs inArr).length := by rw [hin]; dsimp [w_off]; omega
  have hlen_w1 : w_off + 1 < (s.arrs inArr).length := by rw [hin]; dsimp [w_off]; omega
  have hlen_w2 : w_off + 2 < (s.arrs inArr).length := by rw [hin]; dsimp [w_off]; omega
  have hget_h : (s.arrs inArr)[w_off]'hlen_w0 = x.h := by
    apply getElem_of_getElem? _ hlen_w0
    rw [hin]; exact getElem?_encAlg74In_h x
  have hget_VJ : (s.arrs inArr)[w_off + 1]'hlen_w1 = V_J := by
    apply getElem_of_getElem? _ hlen_w1
    rw [hin]; exact getElem?_encAlg74In_VJ x
  have hget_EJ : (s.arrs inArr)[w_off + 2]'hlen_w2 = E_J := by
    apply getElem_of_getElem? _ hlen_w2
    rw [hin]; exact getElem?_encAlg74In_EJ x
  have h22K_w : 2 + 2 * K < 2 ^ w := by omega
  have hpn_w : p * x.n < 2 ^ w := by omega
  let s₁ := s.setReg 0 x.n
  have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hlen0, hget0, hn_w])
  let s₂ := s₁.setReg 1 x.G.numActivePairs
  have hex₂ : Exec w (.assign 1 (.read inArr (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, h1_w, hlen1, hget1, hm_w])
  let s₃ := s₂.setReg 2 w_off
  have hex₃ : Exec w (.assign 2 (.op .add (.const 2) (.op .mul (.const 3) (.reg 1)))) s₂ s₃ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂,
      h2_w, hw3, hm_w, h3m_w, hwoff_w, w_off])
  let s₄ := s₃.setReg 3 x.h
  have hex₄ : Exec w (.assign 3 (.read inArr (.reg 2))) s₃ s₄ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hwoff_w, hlen_w0, hget_h, hh_w])
  let s₅ := s₄.setReg 12 V_J
  have hex₅ : Exec w (.assign 12 (.read inArr (.op .add (.reg 2) (.const 1)))) s₄ s₅ 5 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁,
      hwoff_w, h1_w, hwoff1_w, hlen_w1, hget_VJ, hVJ_w])
  let s₆ := s₅.setReg 13 E_J
  have hex₆ : Exec w (.assign 13 (.read inArr (.op .add (.reg 2) (.const 2)))) s₅ s₆ 5 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁,
      hwoff_w, h2_w, hwoff2_w, hlen_w2, hget_EJ, hEJ_w])
  let s₇ := s₆.setReg 14 (2 * x.h + 2)
  have hex₇ : Exec w (.assign 14 (.op .add (.op .mul (.const 2) (.reg 3)) (.const 2))) s₆ s₇ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅, s₄,
      h2_w, hh_w, h2h_w, hW_w])
  let out_len := 2 + 2 * K + p * x.n
  let s₈ := s₇.setArr outArr (List.replicate out_len 0)
  have hex₈ : Exec w (.alloc outArr (.op .add (.const (2 + 2 * K)) (.op .mul (.const p) (.reg 0))))
      s₇ s₈ (5 + out_len) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
      h22K_w, hp_w, hn_w, hpn_w, hout_w, out_len])
  let s₉ := s₈.writeArr outArr 0 p
  have hex₉ : Exec w (.write outArr (.const 0) (.const p)) s₈ s₉ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w]) (by simp [Expr.eval, checkWord, hp_w])
      (by simp [s₈, out_len])
  let s₁₀ := s₉.writeArr outArr 1 K
  have hex₁₀ : Exec w (.write outArr (.const 1) (.const K)) s₉ s₁₀ 3 :=
    .write (by simp [Expr.eval, checkWord, h1_w]) (by simp [Expr.eval, checkWord, hK_w])
      (by simp [s₉, s₈, out_len]; omega)
  let s₁₁ := s₁₀.setArr locArr (List.replicate x.n 0)
  have hex₁₁ : Exec w (.alloc locArr (.reg 0)) s₁₀ s₁₁ (1 + x.n) :=
    .alloc (by simp [Expr.eval, checkWord, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hn_w])
  let s₁₂ := s₁₁.setArr edgeU1Arr (List.replicate E_J 0)
  have hex₁₂ : Exec w (.alloc edgeU1Arr (.reg 13)) s₁₁ s₁₂ (1 + E_J) :=
    .alloc (by simp [Expr.eval, checkWord, s₁₁, s₁₀, s₉, s₈, s₇, s₆, hEJ_w])
  let s₁₃ := s₁₂.setArr edgeU2Arr (List.replicate E_J 0)
  have hex₁₃ : Exec w (.alloc edgeU2Arr (.reg 13)) s₁₂ s₁₃ (1 + E_J) :=
    .alloc (by simp [Expr.eval, checkWord, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, hEJ_w])
  have hout_eq : s₁₃.arrs outArr = s₁₀.arrs outArr := by
    simp [s₁₃, s₁₂, s₁₁, State.setArr_arrs_ne]
  have hout_len10 : (s₁₀.arrs outArr).length = 2 + 2 * K + p * x.n := by
    simp [s₁₀, s₉, s₈, out_len]
  refine ⟨s₁₃,
    3 + (3 + (6 + (3 + (5 + (5 + (6 + ((5 + out_len) + (3 + (3 + ((1 + x.n) + ((1 + E_J) + (1 + E_J)))))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
      (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ hex₁₃))))))))))),
    by dsimp [out_len]; nlinarith,
    by simp [s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hin],
    by simp [s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁],
    by simp [s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂],
    by simp [s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, w_off],
    by simp [s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄],
    by simp [s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅],
    by simp [s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆],
    by simp [s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇],
    by rw [hout_eq, hout_len10],
    ?_, ?_, ?_,
    by simp [s₁₃, s₁₂, s₁₁, State.setArr_arrs_ne],
    by simp [s₁₃, s₁₂, State.setArr_arrs_ne],
    by simp [s₁₃]⟩
  · rw [hout_eq, List.getElem?_eq_getElem (by omega : 0 < (s₁₀.arrs outArr).length)]
    simp [s₁₀, s₉, s₈]
  · rw [hout_eq, List.getElem?_eq_getElem (by omega : 1 < (s₁₀.arrs outArr).length)]
    simp [s₁₀, s₉, s₈]
  · intro gamma
    rw [hout_eq]
    refine isBitSlice_empty_of_zero _ _ ?_ ?_
    · rw [hout_len10]
      have := gamma.2
      nlinarith
    · intro v
      have hne1 : 1 ≠ 2 + 2 * K + gamma.1 * x.n + v.1 := by omega
      have hne0 : 0 ≠ 2 + 2 * K + gamma.1 * x.n + v.1 := by omega
      simp only [s₁₀, s₉, s₈, State.writeArr, State.setArr_arrs_self]
      rw [List.getElem_set_ne hne1, List.getElem_set_ne hne0, List.getElem_replicate]

/-- Loop body of `scanBranchVertsLoop`: reads `r_11 := inArr[r_2 + 3 + r_8]` and writes
`locArr[r_11] := r_8`. -/
def scanBranchVertsBody : Cmd :=
  .seq (.assign 11 (.read inArr (.op .add (.op .add (.reg 2) (.const 3)) (.reg 8))))
    (.seq (.write locArr (.reg 11) (.reg 8))
      (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
        (.assign 9 (.op .sub (.reg 9) (.const 1)))))

/-- Loop scanning the `V_J` branch vertices in `inArr` and recording `locArr[branchVert u] = u`. -/
def scanBranchVertsLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) scanBranchVertsBody

theorem scanBranchVertsLoop_exec {w p r : ℕ} (x : Alg74Input p r)
    (hw3 : 3 < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hin_w : (encAlg74In x).length < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = elemWallNumVerts x.h) {s : State}
      (_hin : s.arrs inArr = encAlg74In x)
      (_hloc_len : (s.arrs locArr).length = x.n)
      (_hr2 : s.regs 2 = 2 + 3 * x.G.numActivePairs)
      (_hr8 : s.regs 8 = idx)
      (_hr9 : s.regs 9 = rem)
      (_hprev : ∀ u : Fin (elemWallNumVerts x.h), u.1 < idx →
        (s.arrs locArr)[(x.W.branchVert u).1]? = some u.1),
      ∃ s' t,
        Exec w scanBranchVertsLoop s s' t ∧
        t ≤ 22 * rem + 3 ∧
        (s'.arrs locArr).length = x.n ∧
        (∀ u : Fin (elemWallNumVerts x.h),
          (s'.arrs locArr)[(x.W.branchVert u).1]? = some u.1) ∧
        (∀ reg : Reg, reg ≠ 8 → reg ≠ 9 → reg ≠ 11 → s'.regs reg = s.regs reg) ∧
        (∀ a : Arr, a ≠ locArr → s'.arrs a = s.arrs a)
  | 0, idx, hrem, s, _, hloc_len, _, _, hr9, hprev => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hloc_len,
      fun u => hprev u (by have := u.2; omega),
      fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | rem + 1, idx, hrem, s, hin, hloc_len, hr2, hr8, hr9, hprev => by
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have hu_lt : idx < elemWallNumVerts x.h := by omega
    let u : Fin (elemWallNumVerts x.h) := ⟨idx, hu_lt⟩
    have hin_len_VJ :
        2 + 3 * x.G.numActivePairs + 3 + elemWallNumVerts x.h ≤ (encAlg74In x).length := by
      simp [encAlg74In, MultiDigraph.length_enc, WallOfHeight.length_encList]
      omega
    have hin_len : 2 + 3 * x.G.numActivePairs + 3 + idx < (encAlg74In x).length := by omega
    have hwoff_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
    have hwoff3_w : 2 + 3 * x.G.numActivePairs + 3 < 2 ^ w := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hrem_w : rem + 1 < 2 ^ w := by omega
    have hrem0_w : rem < 2 ^ w := by omega
    have hpos_w : 2 + 3 * x.G.numActivePairs + 3 + idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, h1_w, hrem_w]
    have hlen_in : 2 + 3 * x.G.numActivePairs + 3 + idx < (s.arrs inArr).length := by
      rw [hin]; exact hin_len
    have hget_br : (s.arrs inArr)[2 + 3 * x.G.numActivePairs + 3 + idx]'hlen_in =
        (x.W.branchVert u).1 := by
      apply getElem_of_getElem? _ hlen_in
      rw [hin]
      exact getElem?_encAlg74In_branchVert x u
    have hbr_lt : (x.W.branchVert u).1 < x.n := (x.W.branchVert u).2
    have hbr_w : (x.W.branchVert u).1 < 2 ^ w := by omega
    let s₁ := s.setReg 11 (x.W.branchVert u).1
    have hex₁ : Exec w (.assign 11 (.read inArr (.op .add (.op .add (.reg 2) (.const 3)) (.reg 8))))
        s s₁ 7 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr8,
        hwoff_w, hw3, hwoff3_w, hidx_w, hpos_w, hlen_in, hget_br, hbr_w])
    let s₂ := s₁.writeArr locArr (x.W.branchVert u).1 idx
    have hex₂ : Exec w (.write locArr (.reg 11) (.reg 8)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, s₁, hbr_w])
        (by simp [Expr.eval, checkWord, s₁, hr8, hidx_w])
        (by simp [s₁, hloc_len, hbr_lt])
    let s₃ := s₂.setReg 8 (idx + 1)
    have hex₃ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr8,
        hidx_w, h1_w, hidx1_w])
    let s₄ := s₃.setReg 9 rem
    have hex₄ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hr9,
        hrem_w, h1_w, hrem0_w])
    have hex_body : Exec w scanBranchVertsBody s s₄ (7 + (3 + (4 + 4))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
    have hin₄ : s₄.arrs inArr = encAlg74In x := by
      simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne, hin]
    have hloc_len4 : (s₄.arrs locArr).length = x.n := by
      simp [s₄, s₃, s₂, s₁, hloc_len]
    have hr2_4 : s₄.regs 2 = 2 + 3 * x.G.numActivePairs := by
      simp [s₄, s₃, s₂, s₁, hr2]
    have hr8_4 : s₄.regs 8 = idx + 1 := by simp [s₄, s₃]
    have hr9_4 : s₄.regs 9 = rem := by simp [s₄]
    have hprev₄ : ∀ u' : Fin (elemWallNumVerts x.h), u'.1 < idx + 1 →
        (s₄.arrs locArr)[(x.W.branchVert u').1]? = some u'.1 := by
      intro u' hu'
      simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hu') with hlt | heq
      · have hne_u : u' ≠ u := fun h => by subst h; dsimp [u] at hlt; omega
        have hne_br : (x.W.branchVert u).1 ≠ (x.W.branchVert u').1 := by
          intro hval
          exact hne_u (x.hW_valid.2.2.1 (Fin.ext hval.symm))
        rw [List.getElem?_set_ne hne_br]
        exact hprev u' hlt
      · have heq_u : u' = u := Fin.ext heq
        subst heq_u
        rw [List.getElem?_set_self (by rw [hloc_len]; exact hbr_lt)]
    rcases scanBranchVertsLoop_exec x hw3 hn_w hin_w rem (idx + 1) (by omega)
        hin₄ hloc_len4 hr2_4 hr8_4 hr9_4 hprev₄ with
      ⟨s', t_rest, hex_rest, ht_rest, hloc_len', hall', hregs', harrs'⟩
    refine ⟨s', 3 + (7 + (3 + (4 + 4))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by omega, hloc_len', hall', ?_, ?_⟩
    · intro reg h8 h9 h11
      rw [hregs' reg h8 h9 h11]
      simp [s₄, s₃, s₂, s₁, h8, h9, h11]
    · intro a ha
      rw [harrs' a ha]
      simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha]

/-- Loop body of `scanOneInternalListLoop`: reads `r_11 := inArr[r_8]` and writes
`locArr[r_11] := r_6`. -/
def scanOneInternalListBody : Cmd :=
  .seq (.assign 11 (.read inArr (.reg 8)))
    (.seq (.write locArr (.reg 11) (.reg 6))
      (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
        (.assign 9 (.op .sub (.reg 9) (.const 1)))))

/-- Loop scanning one internal vertex list `vs` in `inArr` and setting `locArr[v] := r_6`. -/
def scanOneInternalListLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) scanOneInternalListBody

private theorem getElem_append_cons {α : Type*} (pre : List α) (a : α) (suf : List α)
    (pos : ℕ) (hpos : pre.length = pos) :
    (pre ++ (a :: suf))[pos]'(by simp [hpos]) = a := by
  subst hpos
  rw [List.getElem_append_right (le_refl _)]
  simp

theorem scanOneInternalListLoop_exec {w n : ℕ} (val : ℕ)
    (hw1 : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hval_w : val < 2 ^ w) :
    ∀ (vs : List (Fin n)) (pre suf : List ℕ) {s : State}
      (_hin : s.arrs inArr = pre ++ (vs.map Fin.val ++ suf))
      (_hin_w : (s.arrs inArr).length < 2 ^ w)
      (_hloc_len : (s.arrs locArr).length = n)
      (_hr6 : s.regs 6 = val)
      (_hr8 : s.regs 8 = pre.length)
      (_hr9 : s.regs 9 = vs.length),
      ∃ s' t,
        Exec w scanOneInternalListLoop s s' t ∧
        t ≤ 17 * vs.length + 3 ∧
        s'.regs 8 = (pre ++ vs.map Fin.val).length ∧
        (s'.arrs locArr).length = n ∧
        (∀ v ∈ vs, (s'.arrs locArr)[v.1]? = some val) ∧
        (∀ u : Fin n, u ∉ vs → (s'.arrs locArr)[u.1]? = (s.arrs locArr)[u.1]?) ∧
        (∀ reg : Reg, reg ≠ 8 → reg ≠ 9 → reg ≠ 11 → s'.regs reg = s.regs reg) ∧
        (∀ a : Arr, a ≠ locArr → s'.arrs a = s.arrs a)
  | [], pre, suf, s, _, _, hloc_len, _, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, by simpa using hr8, hloc_len,
      fun _ h => False.elim (List.not_mem_nil h),
      fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | v :: rest, pre, suf, s, hin, hin_w, hloc_len, hr6, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hlen_in : pre.length + 1 + rest.length ≤ (s.arrs inArr).length := by
      simp [hin]; omega
    have hpos_w : pre.length < 2 ^ w := by omega
    have hpos1_w : pre.length + 1 < 2 ^ w := by omega
    have hrem_w : rest.length + 1 < 2 ^ w := by omega
    have hrem0_w : rest.length < 2 ^ w := by omega
    have hr9_eq : s.regs 9 = rest.length + 1 := by simpa using hr9
    have hv_lt : v.1 < n := v.2
    have hv_w : v.1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_eq, h0_w, hw1, hrem_w]
    have hpos_lt : pre.length < (s.arrs inArr).length := by omega
    have hget_v : (s.arrs inArr)[pre.length]'hpos_lt = v.1 := by
      simp only [hin, List.map_cons, List.cons_append]
      exact getElem_append_cons pre v.1 _ pre.length rfl
    let s₁ := s.setReg 11 v.1
    have hex₁ : Exec w (.assign 11 (.read inArr (.reg 8))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr8, hpos_w, hpos_lt, hget_v, hv_w])
    let s₂ := s₁.writeArr locArr v.1 val
    have hex₂ : Exec w (.write locArr (.reg 11) (.reg 6)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, s₁, hv_w])
        (by simp [Expr.eval, checkWord, s₁, hr6, hval_w])
        (by simp [s₁, hloc_len, hv_lt])
    let s₃ := s₂.setReg 8 (pre.length + 1)
    have hex₃ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr8,
        hpos_w, hw1, hpos1_w])
    let s₄ := s₃.setReg 9 rest.length
    have hex₄ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hr9_eq,
        hrem_w, hw1, hrem0_w])
    have hex_body : Exec w scanOneInternalListBody s s₄ (3 + (3 + (4 + 4))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
    have hin₄_eq : s₄.arrs inArr = s.arrs inArr := by
      simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne]
    have hin₄ : s₄.arrs inArr = (pre ++ [v.1]) ++ (rest.map Fin.val ++ suf) := by
      rw [hin₄_eq, hin]; simp
    have hin_w4 : (s₄.arrs inArr).length < 2 ^ w := by rwa [hin₄_eq]
    have hloc_len4 : (s₄.arrs locArr).length = n := by simp [s₄, s₃, s₂, s₁, hloc_len]
    have hr6_4 : s₄.regs 6 = val := by simp [s₄, s₃, s₂, s₁, hr6]
    have hr8_4 : s₄.regs 8 = (pre ++ [v.1]).length := by simp [s₄, s₃]
    have hr9_4 : s₄.regs 9 = rest.length := by simp [s₄]
    rcases scanOneInternalListLoop_exec val hw1 hn_w hval_w rest (pre ++ [v.1]) suf
        hin₄ hin_w4 hloc_len4 hr6_4 hr8_4 hr9_4 with
      ⟨s', t_rest, hex_rest, ht_rest, hr8', hloc_len', hmem', hnot_mem', hregs', harrs'⟩
    refine ⟨s', 3 + (3 + (3 + (4 + 4))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by simp only [List.length_cons]; omega,
      by simpa [List.append_assoc] using hr8',
      hloc_len', ?_, ?_, ?_, ?_⟩
    · intro z hz
      by_cases hzr : z ∈ rest
      · exact hmem' z hzr
      · have hzv : z = v := by
          rcases List.mem_cons.mp hz with rfl | hmem
          · rfl
          · exact False.elim (hzr hmem)
        subst hzv
        rw [hnot_mem' z hzr]
        simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
        exact List.getElem?_set_self (by rw [hloc_len]; exact hv_lt)
    · intro u hu
      have hu_ne : u ≠ v := fun h => hu (h ▸ List.mem_cons_self)
      have hu_rest : u ∉ rest := fun h => hu (List.mem_cons_of_mem v h)
      rw [hnot_mem' u hu_rest]
      simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
      exact List.getElem?_set_ne (Fin.val_ne_of_ne hu_ne.symm)
    · intro reg h8 h9 h11
      rw [hregs' reg h8 h9 h11]
      simp [s₄, s₃, s₂, s₁, h8, h9, h11]
    · intro a ha
      rw [harrs' a ha]
      simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha]

/-- Loop body of `scanInternalEdgesLoop`: scans internal vertex list `k = r_5` at `inArr[r_4]`,
setting `locArr[v] := V_J + k` and advancing `r_4`. -/
def scanInternalEdgesBody : Cmd :=
  .seq (.assign 9 (.read inArr (.reg 4)))
    (.seq (.assign 8 (.op .add (.reg 4) (.const 1)))
      (.seq (.assign 6 (.op .add (.reg 12) (.reg 5)))
        (.seq scanOneInternalListLoop
          (.seq (.assign 4 (.reg 8))
            (.seq (.assign 5 (.op .add (.reg 5) (.const 1)))
              (.assign 10 (.op .sub (.reg 10) (.const 1))))))))

/-- Loop scanning all `E_J` internal vertex lists in `inArr`. -/
def scanInternalEdgesLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 10)) scanInternalEdgesBody

theorem scanInternalEdgesLoop_exec {w p r : ℕ} (x : Alg74Input p r)
    (hw1 : 1 < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hloc_w : elemWallNumVerts x.h + (elemWallEdges x.h).length < 2 ^ w)
    (hin_w : (encAlg74In x).length < 2 ^ w) :
    ∀ (ks : List (Fin (elemWallEdges x.h).length)) (_hnd : ks.Nodup)
      (pre suf : List ℕ) {s : State}
      (_hin : s.arrs inArr = encAlg74In x)
      (_hsplit : encAlg74In x = pre ++ (encInternalSlice x.W ks ++ suf))
      (_hloc_len : (s.arrs locArr).length = x.n)
      (_hr4 : s.regs 4 = pre.length)
      (_hr5 : ∀ k_head, ks.head? = some k_head → s.regs 5 = k_head.1)
      (_hconsec : ∀ i (hi : i + 1 < ks.length),
        (ks[i + 1]'hi).1 = (ks[i]'(by omega)).1 + 1)
      (_hr10 : s.regs 10 = ks.length)
      (_hr12 : s.regs 12 = elemWallNumVerts x.h),
      ∃ s' t,
        Exec w scanInternalEdgesLoop s s' t ∧
        t ≤ 26 * ks.length + 17 * (encInternalSlice x.W ks).length + 3 ∧
        s'.regs 4 = (pre ++ encInternalSlice x.W ks).length ∧
        (s'.arrs locArr).length = x.n ∧
        (∀ k ∈ ks, ∀ v ∈ x.W.internalVerts k,
          (s'.arrs locArr)[v.1]? = some (elemWallNumVerts x.h + k.1)) ∧
        (∀ u : Fin x.n, (∀ k ∈ ks, u ∉ x.W.internalVerts k) →
          (s'.arrs locArr)[u.1]? = (s.arrs locArr)[u.1]?) ∧
        (∀ reg : Reg, reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 8 → reg ≠ 9 →
          reg ≠ 10 → reg ≠ 11 → s'.regs reg = s.regs reg) ∧
        (∀ a : Arr, a ≠ locArr → s'.arrs a = s.arrs a)
  | [], _, pre, suf, s, _, _, hloc_len, hr4, _, _, hr10, _ => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 10)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, by simpa using hr4, hloc_len,
      fun _ h => False.elim (List.not_mem_nil h),
      fun _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | k :: rest, hnd, pre, suf, s, hin, hsplit, hloc_len, hr4, hr5, hconsec, hr10, hr12 => by
    rcases List.nodup_cons.mp hnd with ⟨hk_not_mem, hnd_rest⟩
    have h0_w : 0 < 2 ^ w := by omega
    have vs := x.W.internalVerts k
    have hsplit_k :
        encAlg74In x =
          pre ++ ((x.W.internalVerts k).length :: (x.W.internalVerts k).map Fin.val ++
            (encInternalSlice x.W rest ++ suf)) := by
      simpa [encInternalSlice_cons, List.append_assoc] using hsplit
    have hlen_in_eq :
        (encAlg74In x).length =
          pre.length + 1 + (x.W.internalVerts k).length + (encInternalSlice x.W rest).length +
            suf.length := by
      rw [hsplit_k]
      simp only [List.length_append, List.length_cons, List.length_map]
      omega
    have hrest_le := length_le_length_encInternalSlice x.W rest
    have hpos_w : pre.length < 2 ^ w := by omega
    have hpos1_w : pre.length + 1 < 2 ^ w := by omega
    have hlenk_w : (x.W.internalVerts k).length < 2 ^ w := by omega
    have hrem_w : rest.length + 1 < 2 ^ w := by omega
    have hrem0_w : rest.length < 2 ^ w := by omega
    have hr5_k : s.regs 5 = k.1 := hr5 k rfl
    have hk_lt : k.1 < (elemWallEdges x.h).length := k.2
    have hVJ_w : elemWallNumVerts x.h < 2 ^ w := by omega
    have hk_w : k.1 < 2 ^ w := by omega
    have hk1_w : k.1 + 1 < 2 ^ w := by omega
    have hval_w : elemWallNumVerts x.h + k.1 < 2 ^ w := by omega
    have hr10_eq : s.regs 10 = rest.length + 1 := by simpa using hr10
    have hcond : (Expr.op .lt (.const 0) (.reg 10)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10_eq, h0_w, hw1, hrem_w]
    have hpos_lt : pre.length < (s.arrs inArr).length := by rw [hin]; omega
    have hget_len : (s.arrs inArr)[pre.length]'hpos_lt = (x.W.internalVerts k).length := by
      simp only [hin, hsplit_k, List.cons_append]
      exact getElem_append_cons pre (x.W.internalVerts k).length _ pre.length rfl
    let s₁ := s.setReg 9 (x.W.internalVerts k).length
    have hex₁ : Exec w (.assign 9 (.read inArr (.reg 4))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr4, hpos_w, hpos_lt, hget_len, hlenk_w])
    let s₂ := s₁.setReg 8 (pre.length + 1)
    have hex₂ : Exec w (.assign 8 (.op .add (.reg 4) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr4, hpos_w, hw1, hpos1_w])
    let s₃ := s₂.setReg 6 (elemWallNumVerts x.h + k.1)
    have hex₃ : Exec w (.assign 6 (.op .add (.reg 12) (.reg 5))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr12, hr5_k,
        hVJ_w, hk_w, hval_w])
    have hin₃_raw : s₃.arrs inArr = encAlg74In x := by simp [s₃, s₂, s₁, hin]
    have hin₃ :
        s₃.arrs inArr =
          (pre ++ [(x.W.internalVerts k).length]) ++
            ((x.W.internalVerts k).map Fin.val ++ (encInternalSlice x.W rest ++ suf)) := by
      rw [hin₃_raw, hsplit_k]; simp
    have hin_w3 : (s₃.arrs inArr).length < 2 ^ w := by rwa [hin₃_raw]
    have hloc_len3 : (s₃.arrs locArr).length = x.n := by simp [s₃, s₂, s₁, hloc_len]
    have hr6_3 : s₃.regs 6 = elemWallNumVerts x.h + k.1 := by simp [s₃]
    have hr8_3 : s₃.regs 8 = (pre ++ [(x.W.internalVerts k).length]).length := by simp [s₃, s₂]
    have hr9_3 : s₃.regs 9 = (x.W.internalVerts k).length := by simp [s₃, s₂, s₁]
    rcases scanOneInternalListLoop_exec (elemWallNumVerts x.h + k.1) hw1 hn_w hval_w
        (x.W.internalVerts k) (pre ++ [(x.W.internalVerts k).length])
        (encInternalSlice x.W rest ++ suf)
        hin₃ hin_w3 hloc_len3 hr6_3 hr8_3 hr9_3 with
      ⟨s₄, t_in, hex₄, ht_in, hr8_4, hloc_len4, hmem4, hnot_mem4, hregs4, harrs4⟩
    let pre₁ := pre ++ ((x.W.internalVerts k).length :: (x.W.internalVerts k).map Fin.val)
    have hr8_4_eq : s₄.regs 8 = pre₁.length := by
      simpa [pre₁, List.append_assoc] using hr8_4
    have hpre1_w : pre₁.length < 2 ^ w := by
      have : pre₁.length = pre.length + 1 + (x.W.internalVerts k).length := by
        simp [pre₁]; omega
      omega
    let s₅ := s₄.setReg 4 pre₁.length
    have hex₅ : Exec w (.assign 4 (.reg 8)) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr8_4_eq, hpre1_w])
    have hr5_4 : s₄.regs 5 = k.1 := by
      rw [hregs4 5 (by decide) (by decide) (by decide)]
      simp [s₃, s₂, s₁, hr5_k]
    let s₆ := s₅.setReg 5 (k.1 + 1)
    have hex₆ : Exec w (.assign 5 (.op .add (.reg 5) (.const 1))) s₅ s₆ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, hr5_4, hk_w, hw1, hk1_w])
    have hr10_4 : s₄.regs 10 = rest.length + 1 := by
      rw [hregs4 10 (by decide) (by decide) (by decide)]
      simp [s₃, s₂, s₁, hr10_eq]
    let s₇ := s₆.setReg 10 rest.length
    have hex₇ : Exec w (.assign 10 (.op .sub (.reg 10) (.const 1))) s₆ s₇ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅, hr10_4,
        hrem_w, hw1, hrem0_w])
    have hex_body : Exec w scanInternalEdgesBody s s₇ (3 + (4 + (4 + (t_in + (2 + (4 + 4)))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
    have hin₇ : s₇.arrs inArr = encAlg74In x := by
      simp [s₇, s₆, s₅, harrs4 inArr (by decide), hin₃_raw]
    have hsplit_rest : encAlg74In x = pre₁ ++ (encInternalSlice x.W rest ++ suf) := by
      simpa [pre₁, List.append_assoc] using hsplit_k
    have hloc_len7 : (s₇.arrs locArr).length = x.n := by
      simpa [s₇, s₆, s₅] using hloc_len4
    have hr4_7 : s₇.regs 4 = pre₁.length := by simp [s₇, s₆, s₅]
    have hr5_7 : ∀ k_head, rest.head? = some k_head → s₇.regs 5 = k_head.1 := by
      intro k_head hhead
      cases rest with
      | nil => simp at hhead
      | cons k' rest' =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        have hc0 := hconsec 0 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hc0
        simp [s₇, s₆, hc0]
    have hconsec_rest : ∀ i (hi : i + 1 < rest.length),
        (rest[i + 1]'hi).1 = (rest[i]'(by omega)).1 + 1 := by
      intro i hi
      have hc := hconsec (i + 1) (by simp; omega)
      rwa [List.getElem_cons_succ, List.getElem_cons_succ] at hc
    have hr10_7 : s₇.regs 10 = rest.length := by simp [s₇]
    have hr12_7 : s₇.regs 12 = elemWallNumVerts x.h := by
      have h4 : s₄.regs 12 = elemWallNumVerts x.h := by
        rw [hregs4 12 (by decide) (by decide) (by decide)]
        simp [s₃, s₂, s₁, hr12]
      simp [s₇, s₆, s₅, h4]
    rcases scanInternalEdgesLoop_exec x hw1 hn_w hloc_w hin_w rest hnd_rest
        pre₁ suf hin₇ hsplit_rest hloc_len7 hr4_7 hr5_7 hconsec_rest hr10_7 hr12_7 with
      ⟨s', t_rest, hex_rest, ht_rest, hr4', hloc_len', hmem', hnot_mem', hregs', harrs'⟩
    have hslice_len :
        (encInternalSlice x.W (k :: rest)).length =
          1 + (x.W.internalVerts k).length + (encInternalSlice x.W rest).length := by
      simp [encInternalSlice_cons]; omega
    refine ⟨s', 3 + (3 + (4 + (4 + (t_in + (2 + (4 + 4)))))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by rw [hslice_len, List.length_cons]; omega,
      by simpa [pre₁, encInternalSlice_cons, List.append_assoc] using hr4',
      hloc_len', ?_, ?_, ?_, ?_⟩
    · intro k' hk' v hv
      rcases List.mem_cons.mp hk' with rfl | hk'_rest
      · have hnot_in_rest : ∀ k'' ∈ rest, v ∉ x.W.internalVerts k'' := by
          intro k'' hk'' hv''
          have hne : k' ≠ k'' := fun h => hk_not_mem (h ▸ hk'')
          exact x.hW_valid.2.2.2.2.2 k' k'' hne hv hv''
        rw [hnot_mem' v hnot_in_rest]
        simpa [s₇, s₆, s₅] using hmem4 v hv
      · exact hmem' k' hk'_rest v hv
    · intro u hu
      have hu_rest : ∀ k' ∈ rest, u ∉ x.W.internalVerts k' :=
        fun k' hk' => hu k' (List.mem_cons_of_mem k hk')
      have hu_k : u ∉ x.W.internalVerts k := hu k List.mem_cons_self
      rw [hnot_mem' u hu_rest]
      simpa [s₇, s₆, s₅, s₃, s₂, s₁] using hnot_mem4 u hu_k
    · intro reg h4 h5 h6 h8 h9 h10 h11
      rw [hregs' reg h4 h5 h6 h8 h9 h10 h11]
      simp only [s₇, s₆, s₅, State.setReg_regs_ne _ _ h10,
        State.setReg_regs_ne _ _ h5, State.setReg_regs_ne _ _ h4,
        hregs4 reg h8 h9 h11,
        s₃, s₂, s₁, State.setReg_regs_ne _ _ h6, State.setReg_regs_ne _ _ h8,
        State.setReg_regs_ne _ _ h9]
    · intro a ha
      rw [harrs' a ha]
      simp [s₇, s₆, s₅, harrs4 a ha, s₃, s₂, s₁]

private theorem val_eq_zero_of_head?_finRange {n : ℕ} {k : Fin n}
    (h : (List.finRange n).head? = some k) : k.1 = 0 := by
  cases n with
  | zero => simp at h
  | succ m =>
    simp only [List.finRange_succ, List.head?_cons, Option.some.injEq] at h
    subst h
    rfl

/-- Step 2 (`scanWallCmd`): scans `x.W.encList` in one pass, populating `locArr` and setting
`r_4 = (x.G.enc ++ x.W.encList).length`. -/
def scanWallCmd : Cmd :=
  .seq (.assign 8 (.const 0))
    (.seq (.assign 9 (.reg 12))
      (.seq scanBranchVertsLoop
        (.seq (.assign 4 (.op .add (.op .add (.reg 2) (.const 3)) (.reg 12)))
          (.seq (.assign 5 (.const 0))
            (.seq (.assign 10 (.reg 13))
              scanInternalEdgesLoop)))))

theorem scanWallCmd_exec {w p r : ℕ} (x : Alg74Input p r)
    {s : State}
    (hw3 : 3 < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hloc_w : elemWallNumVerts x.h + (elemWallEdges x.h).length < 2 ^ w)
    (hin_w : (encAlg74In x).length < 2 ^ w)
    (hin : s.arrs inArr = encAlg74In x)
    (hloc_len : (s.arrs locArr).length = x.n)
    (hr2 : s.regs 2 = 2 + 3 * x.G.numActivePairs)
    (hr12 : s.regs 12 = elemWallNumVerts x.h)
    (hr13 : s.regs 13 = (elemWallEdges x.h).length) :
    ∃ s' t,
      Exec w scanWallCmd s s' t ∧
      t ≤ 22 * elemWallNumVerts x.h + 26 * (elemWallEdges x.h).length +
        17 * x.W.encList.length + 25 ∧
      s'.regs 4 = (x.G.enc ++ x.W.encList).length ∧
      (s'.arrs locArr).length = x.n ∧
      (∀ v ∈ x.W.vertexFinset,
        (s'.arrs locArr)[v.1]? = some (termLocCode x.W v)) ∧
      (∀ reg : Reg, reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 8 → reg ≠ 9 →
        reg ≠ 10 → reg ≠ 11 → s'.regs reg = s.regs reg) ∧
      (∀ a : Arr, a ≠ locArr → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  let V_J := elemWallNumVerts x.h
  let E_J := (elemWallEdges x.h).length
  have hVJ_w : V_J < 2 ^ w := by dsimp [V_J]; omega
  have hEJ_w : E_J < 2 ^ w := by dsimp [E_J]; omega
  let s₁ := s.setReg 8 0
  have hex₁ : Exec w (.assign 8 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 9 V_J
  have hex₂ : Exec w (.assign 9 (.reg 12)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₁, hr12, hVJ_w, V_J])
  rcases scanBranchVertsLoop_exec x hw3 hn_w hin_w V_J 0 (Nat.zero_add V_J) (s := s₂)
      (by simp [s₂, s₁, hin]) (by simp [s₂, s₁, hloc_len])
      (by simp [s₂, s₁, hr2]) (by simp [s₂, s₁]) (by simp [s₂])
      (fun _ hu => False.elim (Nat.not_lt_zero _ hu)) with
    ⟨s₃, t_br, hex₃, ht_br, hloc_len3, hbr3, hregs3, harrs3⟩
  let pre :=
    x.G.enc ++
      ([x.h, V_J, E_J] ++ (List.finRange V_J).map (fun u => (x.W.branchVert u).1))
  have hpre_len : pre.length = 2 + 3 * x.G.numActivePairs + 3 + V_J := by
    simp [pre, MultiDigraph.length_enc]; omega
  have hsplit :
      encAlg74In x =
        pre ++ (encInternalSlice x.W (List.finRange E_J) ++ encHPaths x.paths) := by
    unfold encAlg74In
    rw [wallEncList_eq_append_encInternalSlice]
    dsimp [pre, V_J, E_J]
    simp [List.append_assoc]
  have hlen_in_ge : pre.length ≤ (encAlg74In x).length := by
    rw [hsplit]; simp
  have hwoff_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hwoff3_w : 2 + 3 * x.G.numActivePairs + 3 < 2 ^ w := by omega
  have hpre_w : 2 + 3 * x.G.numActivePairs + 3 + V_J < 2 ^ w := by omega
  have hr2_3 : s₃.regs 2 = 2 + 3 * x.G.numActivePairs := by
    rw [hregs3 2 (by decide) (by decide) (by decide)]
    simp [s₂, s₁, hr2]
  have hr12_3 : s₃.regs 12 = V_J := by
    rw [hregs3 12 (by decide) (by decide) (by decide)]
    simp [s₂, s₁, hr12, V_J]
  have hr13_3 : s₃.regs 13 = E_J := by
    rw [hregs3 13 (by decide) (by decide) (by decide)]
    simp [s₂, s₁, hr13, E_J]
  let s₄ := s₃.setReg 4 pre.length
  have hex₄ : Exec w (.assign 4 (.op .add (.op .add (.reg 2) (.const 3)) (.reg 12))) s₃ s₄ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_3, hr12_3,
      hwoff_w, hw3, hwoff3_w, hVJ_w, hpre_w, hpre_len])
  let s₅ := s₄.setReg 5 0
  have hex₅ : Exec w (.assign 5 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₆ := s₅.setReg 10 E_J
  have hex₆ : Exec w (.assign 10 (.reg 13)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₅, s₄, hr13_3, hEJ_w])
  have hin₆ : s₆.arrs inArr = encAlg74In x := by
    simp [s₆, s₅, s₄, harrs3 inArr (by decide), s₂, s₁, hin]
  have hloc_len6 : (s₆.arrs locArr).length = x.n := by
    simpa [s₆, s₅, s₄] using hloc_len3
  have hr4_6 : s₆.regs 4 = pre.length := by simp [s₆, s₅, s₄]
  have hr5_6 : ∀ k_head, (List.finRange E_J).head? = some k_head → s₆.regs 5 = k_head.1 := by
    intro k_head hhead
    rw [val_eq_zero_of_head?_finRange hhead]
    simp [s₆, s₅]
  have hconsec6 : ∀ i (hi : i + 1 < (List.finRange E_J).length),
      ((List.finRange E_J)[i + 1]'hi).1 = ((List.finRange E_J)[i]'(by omega)).1 + 1 := by
    intro i hi
    simp
  have hr10_6 : s₆.regs 10 = (List.finRange E_J).length := by simp [s₆]
  have hr12_6 : s₆.regs 12 = V_J := by simp [s₆, s₅, s₄, hr12_3]
  rcases scanInternalEdgesLoop_exec x h1_w hn_w hloc_w hin_w
      (List.finRange E_J) (List.nodup_finRange E_J) pre (encHPaths x.paths)
      hin₆ hsplit hloc_len6 hr4_6 hr5_6 hconsec6 hr10_6 hr12_6 with
    ⟨s', t_int, hex₇, ht_int, hr4', hloc_len', hmem', hnot_mem', hregs', harrs'⟩
  have hslice_le : (encInternalSlice x.W (List.finRange E_J)).length ≤ x.W.encList.length := by
    rw [wallEncList_eq_append_encInternalSlice]
    dsimp [E_J]
    simp only [List.length_append]
    omega
  have hpre_append : pre ++ encInternalSlice x.W (List.finRange E_J) = x.G.enc ++ x.W.encList := by
    rw [wallEncList_eq_append_encInternalSlice]
    dsimp [pre, V_J, E_J]
    simp [List.append_assoc]
  refine ⟨s', 2 + (2 + (t_br + (6 + (2 + (2 + t_int))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by simp only [List.length_finRange] at ht_int; dsimp [V_J, E_J] at ht_br ht_int hslice_le; omega,
    by rwa [hpre_append] at hr4',
    hloc_len', ?_, ?_, ?_⟩
  · intro v hv
    rw [mem_vertexFinset_iff] at hv
    rcases hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
    · rw [termLocCode_branchVert x.hW_valid.2.2 u]
      have hnot_int : ∀ k ∈ List.finRange E_J, x.W.branchVert u ∉ x.W.internalVerts k :=
        fun k _ => x.hW_valid.2.2.2.2.1 k u
      rw [hnot_mem' (x.W.branchVert u) hnot_int]
      simpa [s₆, s₅, s₄] using hbr3 u
    · rw [(mem_internalVerts_iff_termLocCode x.hW_valid.2.2 v k).mp hvk]
      exact hmem' k (List.mem_finRange k) v hvk
  · intro reg h4 h5 h6 h8 h9 h10 h11
    rw [hregs' reg h4 h5 h6 h8 h9 h10 h11]
    simp only [s₆, s₅, s₄, State.setReg_regs_ne _ _ h10,
      State.setReg_regs_ne _ _ h5, State.setReg_regs_ne _ _ h4,
      hregs3 reg h8 h9 h11,
      s₂, s₁, State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8]
  · intro a ha
    rw [harrs' a ha]
    simp [s₆, s₅, s₄, harrs3 a ha, s₂, s₁]

/-- Horizontal edge list `[(u, u + 1)]` (if valid) from elementary-wall vertex `u`. -/
def elemWallHorizEdge (h u : ℕ) : List (Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)) :=
  let W := 2 * h + 2
  let V := elemWallNumVerts h
  let x := (u + 1) % W
  if h1 : x + 1 < W ∧ u + 1 < V then [(⟨u, by omega⟩, ⟨u + 1, h1.2⟩)] else []

/-- Vertical edge list `[(u, u + W)]` (if valid) from elementary-wall vertex `u`. -/
def elemWallVertEdge (h u : ℕ) : List (Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)) :=
  let W := 2 * h + 2
  let V := elemWallNumVerts h
  let x := (u + 1) % W
  let y := (u + 1) / W
  if h2 : u + W < V ∧ (x + y) % 2 = 1 then [(⟨u, by omega⟩, ⟨u + W, h2.1⟩)] else []

/-- Prefix `(List.range u).flatMap (fun i => elemWallHorizEdge h i ++ elemWallVertEdge h i)`
of `elemWallEdges h`. -/
def elemWallEdgesPrefix (h u : ℕ) : List (Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)) :=
  (List.range u).flatMap (fun i => elemWallHorizEdge h i ++ elemWallVertEdge h i)

theorem elemWallEdgesPrefix_zero (h : ℕ) : elemWallEdgesPrefix h 0 = [] := rfl

theorem elemWallEdgesPrefix_succ (h u : ℕ) :
    elemWallEdgesPrefix h (u + 1) =
      elemWallEdgesPrefix h u ++ elemWallHorizEdge h u ++ elemWallVertEdge h u := by
  unfold elemWallEdgesPrefix
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

theorem elemWallEdgesPrefix_full (h : ℕ) :
    elemWallEdgesPrefix h (elemWallNumVerts h) = elemWallEdges h := by
  rw [elemWallEdges_eq_flatMap]
  unfold elemWallEdgesPrefix
  have hrange :
      List.range (elemWallNumVerts h) = (List.finRange (elemWallNumVerts h)).map Fin.val := by
    refine List.ext_getElem (by simp) (fun i _ _ => by simp)
  rw [hrange, List.flatMap_map]
  rfl

/-- Predicate asserting that `arr1` and `arr2` match the endpoints of prefix `L` of
`elemWallEdges h`. -/
def Alg74MatchesEdgePrefix {h : ℕ} (arr1 arr2 : List ℕ)
    (L : List (Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h))) : Prop :=
  arr1.length = (elemWallEdges h).length ∧
  arr2.length = (elemWallEdges h).length ∧
  ∀ i (hi : i < L.length),
    arr1[i]? = some (L[i]'hi).1.1 ∧ arr2[i]? = some (L[i]'hi).2.1

/-- Conditional command appending `(e_u1, e_u2)` to `(edgeU1Arr, edgeU2Arr)` at index `r_5`
when `cond` holds. -/
def condAppendEdgeCmd (cond e_u1 e_u2 : Expr) : Cmd :=
  .ite cond
    (.seq (.write edgeU1Arr (.reg 5) e_u1)
      (.seq (.write edgeU2Arr (.reg 5) e_u2)
        (.assign 5 (.op .add (.reg 5) (.const 1)))))
    .skip

theorem condAppendEdgeCmd_exec {w h : ℕ} (cond e_u1 e_u2 : Expr)
    (L extra : List (Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)))
    (P : Prop) [Decidable P] (u₁ u₂ : ℕ)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hEJ_w : (elemWallEdges h).length < 2 ^ w)
    (hcond : cond.eval w s = some (if P then 1 else 0))
    (hextra_len : (L ++ extra).length ≤ (elemWallEdges h).length)
    (hextra_eq : ∀ _ : P, ∃ e : Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h),
      extra = [e] ∧ e.1.1 = u₁ ∧ e.2.1 = u₂ ∧
      e_u1.eval w s = some u₁ ∧
      (∀ s' : State, s'.regs = s.regs → e_u2.eval w s' = some u₂))
    (hextra_nil : ¬ P → extra = [])
    (hr5 : s.regs 5 = L.length)
    (hmatch : Alg74MatchesEdgePrefix (s.arrs edgeU1Arr) (s.arrs edgeU2Arr) L) :
    ∃ s' t,
      Exec w (condAppendEdgeCmd cond e_u1 e_u2) s s' t ∧
      t ≤ cond.cost + e_u1.cost + e_u2.cost + 11 ∧
      s'.regs 5 = (L ++ extra).length ∧
      Alg74MatchesEdgePrefix (s'.arrs edgeU1Arr) (s'.arrs edgeU2Arr) (L ++ extra) ∧
      (∀ reg : Reg, reg ≠ 5 → s'.regs reg = s.regs reg) ∧
      (∀ a : Arr, a ≠ edgeU1Arr → a ≠ edgeU2Arr → s'.arrs a = s.arrs a) := by
  rcases hmatch with ⟨hlen1, hlen2, hvals⟩
  by_cases hP : P
  · rcases hextra_eq hP with ⟨e, rfl, rfl, rfl, heval1, heval2⟩
    rw [if_pos hP] at hcond
    have hlt_EJ : L.length < (elemWallEdges h).length := by
      simp only [List.length_append, List.length_singleton] at hextra_len
      omega
    have hk_w : L.length < 2 ^ w := by omega
    have hk1_w : L.length + 1 < 2 ^ w := by omega
    let s₁ := s.writeArr edgeU1Arr L.length e.1.1
    have hex₁ : Exec w (.write edgeU1Arr (.reg 5) e_u1) s s₁ (2 + e_u1.cost) := by
      have hc : (Expr.reg 5).cost + e_u1.cost + 1 = 2 + e_u1.cost := by simp [Expr.cost]; omega
      rw [← hc]
      exact .write (by simp [Expr.eval, checkWord, hr5, hk_w]) heval1 (by omega)
    let s₂ := s₁.writeArr edgeU2Arr L.length e.2.1
    have hex₂ : Exec w (.write edgeU2Arr (.reg 5) e_u2) s₁ s₂ (2 + e_u2.cost) := by
      have hc : (Expr.reg 5).cost + e_u2.cost + 1 = 2 + e_u2.cost := by simp [Expr.cost]; omega
      rw [← hc]
      exact .write (by simp [Expr.eval, checkWord, s₁, hr5, hk_w]) (heval2 s₁ rfl)
        (by simp [s₁, State.writeArr_arrs_ne, hlen2, hlt_EJ])
    let s₃ := s₂.setReg 5 (L.length + 1)
    have hex₃ : Exec w (.assign 5 (.op .add (.reg 5) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr5,
        hk_w, hw1, hk1_w])
    refine ⟨s₃, cond.cost + ((2 + e_u1.cost) + ((2 + e_u2.cost) + 4)),
      .ite_true hcond (by omega) (.seq hex₁ (.seq hex₂ hex₃)),
      by omega,
      by simp [s₃],
      ⟨by simp [s₃, s₂, s₁, State.writeArr_arrs_ne, hlen1],
       by simp [s₃, s₂, s₁, hlen2],
       ?_⟩,
      fun reg h5 => by simp [s₃, s₂, s₁, h5],
      fun a ha1 ha2 => by
        simp [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha1, State.writeArr_arrs_ne _ _ _ ha2]⟩
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
    · rw [List.getElem_append_left hlt]
      have hne : L.length ≠ i := by omega
      simp only [s₃, s₂, s₁, State.setReg_arrs,
        State.writeArr_arrs_ne _ _ _ (by decide : edgeU1Arr ≠ edgeU2Arr),
        State.writeArr_arrs_self]
      rw [List.getElem?_set_ne hne, List.getElem?_set_ne hne]
      exact hvals i hlt
    · simp only [List.getElem_append_right (le_refl L.length), Nat.sub_self,
        List.getElem_singleton]
      simp only [s₃, s₂, s₁, State.setReg_arrs,
        State.writeArr_arrs_ne _ _ _ (by decide : edgeU1Arr ≠ edgeU2Arr),
        State.writeArr_arrs_self]
      exact ⟨List.getElem?_set_self (by omega),
        List.getElem?_set_self (by simp [State.writeArr_arrs_ne, hlen2, hlt_EJ])⟩
  · rw [if_neg hP] at hcond
    rw [hextra_nil hP, List.append_nil]
    exact ⟨s, cond.cost + 1, .ite_false hcond (.skip s), by omega, hr5,
      ⟨hlen1, hlen2, hvals⟩, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem elemWallEdgesPrefix_length_le_succ (h u : ℕ) :
    (elemWallEdgesPrefix h u).length ≤ (elemWallEdgesPrefix h (u + 1)).length := by
  rw [elemWallEdgesPrefix_succ]
  simp only [List.length_append]
  omega

theorem elemWallEdgesPrefix_length_mono (h : ℕ) {u v : ℕ} (huv : u ≤ v) :
    (elemWallEdgesPrefix h u).length ≤ (elemWallEdgesPrefix h v).length := by
  induction huv with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (elemWallEdgesPrefix_length_le_succ h _)

/-- Condition expression `r_6 + 1 < r_14 ∧ r_8 + 1 < r_12` for a horizontal wall edge. -/
def condHorizEdgeExpr : Expr :=
  exprAnd (exprLt (.op .add (.reg 6) (.const 1)) (.reg 14))
    (exprLt (.op .add (.reg 8) (.const 1)) (.reg 12))

/-- Condition expression `r_8 + r_14 < r_12 ∧ (r_6 + r_7) % 2 == 1` for a vertical wall edge. -/
def condVertEdgeExpr : Expr :=
  exprAnd (exprLt (.op .add (.reg 8) (.reg 14)) (.reg 12))
    (exprEq (.op .mod (.op .add (.reg 6) (.reg 7)) (.const 2)) (.const 1))

/-- Loop body of `buildWallEdgesLoop`: computes `(x, y)` of vertex `u = r_8` and appends any
valid horizontal and vertical elementary-wall edges from `u`. -/
def buildWallEdgesBody : Cmd :=
  .seq (.assign 6 (.op .mod (.op .add (.reg 8) (.const 1)) (.reg 14)))
    (.seq (.assign 7 (.op .div (.op .add (.reg 8) (.const 1)) (.reg 14)))
      (.seq (condAppendEdgeCmd condHorizEdgeExpr (.reg 8) (.op .add (.reg 8) (.const 1)))
        (.seq (condAppendEdgeCmd condVertEdgeExpr (.reg 8) (.op .add (.reg 8) (.reg 14)))
          (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
            (.assign 9 (.op .sub (.reg 9) (.const 1)))))))

/-- Loop generating all `E_J` elementary-wall edges in `(edgeU1Arr, edgeU2Arr)`. -/
def buildWallEdgesLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) buildWallEdgesBody

theorem buildWallEdgesLoop_exec {w h : ℕ}
    (hw3 : 3 < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hEJ_w : (elemWallEdges h).length < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = elemWallNumVerts h) {s : State}
      (_hr5 : s.regs 5 = (elemWallEdgesPrefix h idx).length)
      (_hr8 : s.regs 8 = idx)
      (_hr9 : s.regs 9 = rem)
      (_hr12 : s.regs 12 = elemWallNumVerts h)
      (_hr14 : s.regs 14 = 2 * h + 2)
      (_hmatch : Alg74MatchesEdgePrefix (s.arrs edgeU1Arr) (s.arrs edgeU2Arr)
        (elemWallEdgesPrefix h idx)),
      ∃ s' t,
        Exec w buildWallEdgesLoop s s' t ∧
        t ≤ 95 * rem + 3 ∧
        Alg74MatchesEdgePrefix (s'.arrs edgeU1Arr) (s'.arrs edgeU2Arr)
          (elemWallEdges h) ∧
        (∀ reg : Reg, reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
          s'.regs reg = s.regs reg) ∧
        (∀ a : Arr, a ≠ edgeU1Arr → a ≠ edgeU2Arr → s'.arrs a = s.arrs a)
  | 0, idx, hrem, s, _, _, hr9, _, _, hmatch => by
    have h0_w : 0 < 2 ^ w := by omega
    have hidx : idx = elemWallNumVerts h := by omega
    subst hidx
    rw [elemWallEdgesPrefix_full] at hmatch
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hmatch,
      fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | rem + 1, idx, hrem, s, hr5, hr8, hr9, hr12, hr14, hmatch => by
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have h2_w : 2 < 2 ^ w := by omega
    let W := 2 * h + 2
    let V := elemWallNumVerts h
    have hW_pos : 0 < W := by dsimp [W]; omega
    have hW_w : W < 2 ^ w := by dsimp [W]; omega
    have hV_w : V < 2 ^ w := by dsimp [V]; omega
    have hidx_lt : idx < V := by dsimp [V]; omega
    have hidx_w : idx < 2 ^ w := by omega
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hidxW_w : idx + W < 2 ^ w := by dsimp [W, V] at *; omega
    have hrem_w : rem + 1 < 2 ^ w := by omega
    have hrem0_w : rem < 2 ^ w := by omega
    let xc := (idx + 1) % W
    let yc := (idx + 1) / W
    have hxc_lt : xc < W := Nat.mod_lt _ hW_pos
    have hxc_w : xc < 2 ^ w := by omega
    have hxc1_w : xc + 1 < 2 ^ w := by omega
    have hyc_le : yc ≤ idx + 1 := Nat.div_le_self (idx + 1) W
    have hyc_w : yc < 2 ^ w := by omega
    have hxcy_w : xc + yc < 2 ^ w := by dsimp [W, V] at *; omega
    have hmod2_lt : (xc + yc) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hmod2_w : (xc + yc) % 2 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, h1_w, hrem_w]
    let s₁ := s.setReg 6 xc
    have hex₁ : Exec w (.assign 6 (.op .mod (.op .add (.reg 8) (.const 1)) (.reg 14))) s s₁ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8, hr14,
        hidx_w, h1_w, hidx1_w, hW_w, hxc_w, xc, W])
    let s₂ := s₁.setReg 7 yc
    have hex₂ : Exec w (.assign 7 (.op .div (.op .add (.reg 8) (.const 1)) (.reg 14))) s₁ s₂ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr8, hr14,
        hidx_w, h1_w, hidx1_w, hW_w, hyc_w, yc, W])
    have hprefix_succ :
        elemWallEdgesPrefix h (idx + 1) =
          elemWallEdgesPrefix h idx ++ elemWallHorizEdge h idx ++ elemWallVertEdge h idx :=
      elemWallEdgesPrefix_succ h idx
    have hprefix_le_full :
        (elemWallEdgesPrefix h (idx + 1)).length ≤ (elemWallEdges h).length := by
      rw [← elemWallEdgesPrefix_full h]
      exact elemWallEdgesPrefix_length_mono h (by omega)
    have hhoriz_le :
        (elemWallEdgesPrefix h idx ++ elemWallHorizEdge h idx).length ≤ (elemWallEdges h).length := by
      have := hprefix_le_full
      rw [hprefix_succ] at this
      simp only [List.length_append] at this ⊢
      omega
    have he_h1 : (Expr.op .add (.reg 6) (.const 1)).eval w s₂ = some (xc + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hxc_w, h1_w, hxc1_w]
    have he_h2 : (Expr.reg 14).eval w s₂ = some W := by
      simp [Expr.eval, checkWord, s₂, s₁, hr14, hW_w, W]
    have he_h3 : (Expr.op .add (.reg 8) (.const 1)).eval w s₂ = some (idx + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr8, hidx_w, h1_w, hidx1_w]
    have he_h4 : (Expr.reg 12).eval w s₂ = some V := by
      simp [Expr.eval, checkWord, s₂, s₁, hr12, hV_w, V]
    have hcondHoriz :
        condHorizEdgeExpr.eval w s₂ = some (if xc + 1 < W ∧ idx + 1 < V then 1 else 0) := by
      unfold condHorizEdgeExpr
      rw [eval_exprAnd h1_w (eval_exprLt h1_w he_h1 he_h2) (eval_exprLt h1_w he_h3 he_h4)]
    rcases condAppendEdgeCmd_exec condHorizEdgeExpr (.reg 8) (.op .add (.reg 8) (.const 1))
        (elemWallEdgesPrefix h idx) (elemWallHorizEdge h idx)
        (xc + 1 < W ∧ idx + 1 < V) idx (idx + 1) (s := s₂)
        h1_w hEJ_w hcondHoriz hhoriz_le
        (fun hP => ⟨(⟨idx, hidx_lt⟩, ⟨idx + 1, hP.2⟩),
          dif_pos hP, rfl, rfl,
          by simp [Expr.eval, checkWord, s₂, s₁, hr8, hidx_w],
          fun s' hs' => by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hs', s₂, s₁, hr8,
              hidx_w, h1_w, hidx1_w]⟩)
        (fun hP => dif_neg hP)
        (by simp [s₂, s₁, hr5])
        (by simpa [s₂, s₁] using hmatch) with
      ⟨s₃, t_h, hex₃, ht_h, hr5_3, hmatch3, hregs3, harrs3⟩
    have hr6_3 : s₃.regs 6 = xc := by
      rw [hregs3 6 (by decide)]; simp [s₂, s₁]
    have hr7_3 : s₃.regs 7 = yc := by
      rw [hregs3 7 (by decide)]; simp [s₂]
    have hr8_3 : s₃.regs 8 = idx := by
      rw [hregs3 8 (by decide)]; simp [s₂, s₁, hr8]
    have hr9_3 : s₃.regs 9 = rem + 1 := by
      rw [hregs3 9 (by decide)]; simp [s₂, s₁, hr9]
    have hr12_3 : s₃.regs 12 = V := by
      rw [hregs3 12 (by decide)]; simp [s₂, s₁, hr12, V]
    have hr14_3 : s₃.regs 14 = W := by
      rw [hregs3 14 (by decide)]; simp [s₂, s₁, hr14, W]
    have he_v1 : (Expr.op .add (.reg 8) (.reg 14)).eval w s₃ = some (idx + W) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_3, hr14_3, hidx_w, hW_w, hidxW_w]
    have he_v2 : (Expr.reg 12).eval w s₃ = some V := by
      simp [Expr.eval, checkWord, hr12_3, hV_w]
    have he_v3 : (Expr.op .mod (.op .add (.reg 6) (.reg 7)) (.const 2)).eval w s₃ =
        some ((xc + yc) % 2) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr6_3, hr7_3,
        hxc_w, hyc_w, hxcy_w, h2_w, hmod2_w]
    have he_v4 : (Expr.const 1).eval w s₃ = some 1 := by
      simp [Expr.eval, checkWord, h1_w]
    have hcondVert :
        condVertEdgeExpr.eval w s₃ = some (if idx + W < V ∧ (xc + yc) % 2 = 1 then 1 else 0) := by
      unfold condVertEdgeExpr
      rw [eval_exprAnd h1_w (eval_exprLt h1_w he_v1 he_v2) (eval_exprEq h1_w he_v3 he_v4)]
    have hvert_le :
        ((elemWallEdgesPrefix h idx ++ elemWallHorizEdge h idx) ++ elemWallVertEdge h idx).length ≤
          (elemWallEdges h).length := by
      rwa [← hprefix_succ]
    rcases condAppendEdgeCmd_exec condVertEdgeExpr (.reg 8) (.op .add (.reg 8) (.reg 14))
        (elemWallEdgesPrefix h idx ++ elemWallHorizEdge h idx) (elemWallVertEdge h idx)
        (idx + W < V ∧ (xc + yc) % 2 = 1) idx (idx + W) (s := s₃)
        h1_w hEJ_w hcondVert hvert_le
        (fun hP => ⟨(⟨idx, hidx_lt⟩, ⟨idx + W, hP.1⟩),
          dif_pos hP, rfl, rfl,
          by simp [Expr.eval, checkWord, hr8_3, hidx_w],
          fun s' hs' => by
            have h8' : s'.regs 8 = idx := by rw [hs', hr8_3]
            have h14' : s'.regs 14 = W := by rw [hs', hr14_3]
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h8', h14',
              hidx_w, hW_w, hidxW_w]⟩)
        (fun hP => dif_neg hP)
        hr5_3 hmatch3 with
      ⟨s₄, t_v, hex₄, ht_v, hr5_4, hmatch4, hregs4, harrs4⟩
    have hr8_4 : s₄.regs 8 = idx := by rw [hregs4 8 (by decide), hr8_3]
    have hr9_4 : s₄.regs 9 = rem + 1 := by rw [hregs4 9 (by decide), hr9_3]
    have hr12_4 : s₄.regs 12 = V := by rw [hregs4 12 (by decide), hr12_3]
    have hr14_4 : s₄.regs 14 = W := by rw [hregs4 14 (by decide), hr14_3]
    let s₅ := s₄.setReg 8 (idx + 1)
    have hex₅ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_4, hidx_w, h1_w, hidx1_w])
    let s₆ := s₅.setReg 9 rem
    have hex₆ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₅ s₆ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, hr9_4,
        hrem_w, h1_w, hrem0_w])
    have hex_body : Exec w buildWallEdgesBody s s₆ (6 + (6 + (t_h + (t_v + (4 + 4))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))
    have hr5_6 : s₆.regs 5 = (elemWallEdgesPrefix h (idx + 1)).length := by
      rw [hprefix_succ]
      simpa [s₆, s₅] using hr5_4
    have hmatch6 : Alg74MatchesEdgePrefix (s₆.arrs edgeU1Arr) (s₆.arrs edgeU2Arr)
        (elemWallEdgesPrefix h (idx + 1)) := by
      rw [hprefix_succ]
      simpa [s₆, s₅] using hmatch4
    rcases buildWallEdgesLoop_exec hw3 hVJW_w hEJ_w rem (idx + 1) (by omega) (s := s₆)
        hr5_6 (by simp [s₆, s₅]) (by simp [s₆])
        (by simp [s₆, s₅, hr12_4, V]) (by simp [s₆, s₅, hr14_4, W]) hmatch6 with
      ⟨s', t_rest, hex_rest, ht_rest, hmatch', hregs', harrs'⟩
    have hc_h : condHorizEdgeExpr.cost + (Expr.reg 8).cost +
        (Expr.op .add (.reg 8) (.const 1)).cost + 11 ≤ 30 := by decide
    have hc_v : condVertEdgeExpr.cost + (Expr.reg 8).cost +
        (Expr.op .add (.reg 8) (.reg 14)).cost + 11 ≤ 40 := by decide
    refine ⟨s', 3 + (6 + (6 + (t_h + (t_v + (4 + 4))))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by omega, hmatch', ?_, ?_⟩
    · intro reg h5 h6 h7 h8 h9
      rw [hregs' reg h5 h6 h7 h8 h9]
      simp only [s₆, s₅, State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8,
        hregs4 reg h5, hregs3 reg h5,
        s₂, s₁, State.setReg_regs_ne _ _ h7, State.setReg_regs_ne _ _ h6]
    · intro a ha1 ha2
      rw [harrs' a ha1 ha2]
      simp [s₆, s₅, harrs4 a ha1 ha2, harrs3 a ha1 ha2, s₂, s₁]

/-- Step 2b (`buildWallEdgesCmd`): populates `edgeU1Arr` and `edgeU2Arr` with the endpoints
of all `E_J` elementary-wall edges in `O(V_J)` steps. -/
def buildWallEdgesCmd : Cmd :=
  .seq (.assign 5 (.const 0))
    (.seq (.assign 8 (.const 0))
      (.seq (.assign 9 (.reg 12))
        buildWallEdgesLoop))

theorem buildWallEdgesCmd_exec {w h : ℕ} {s : State}
    (hw3 : 3 < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hEJ_w : (elemWallEdges h).length < 2 ^ w)
    (hr12 : s.regs 12 = elemWallNumVerts h)
    (hr14 : s.regs 14 = 2 * h + 2)
    (hu1_len : (s.arrs edgeU1Arr).length = (elemWallEdges h).length)
    (hu2_len : (s.arrs edgeU2Arr).length = (elemWallEdges h).length) :
    ∃ s' t,
      Exec w buildWallEdgesCmd s s' t ∧
      t ≤ 95 * elemWallNumVerts h + 10 ∧
      (s'.arrs edgeU1Arr).length = (elemWallEdges h).length ∧
      (s'.arrs edgeU2Arr).length = (elemWallEdges h).length ∧
      (∀ k : Fin (elemWallEdges h).length,
        (s'.arrs edgeU1Arr)[k.1]? = some ((elemWallEdges h)[k.1]'k.2).1.1 ∧
        (s'.arrs edgeU2Arr)[k.1]? = some ((elemWallEdges h)[k.1]'k.2).2.1) ∧
      (∀ reg : Reg, reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
        s'.regs reg = s.regs reg) ∧
      (∀ a : Arr, a ≠ edgeU1Arr → a ≠ edgeU2Arr → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hV_w : elemWallNumVerts h < 2 ^ w := by omega
  let s₁ := s.setReg 5 0
  have hex₁ : Exec w (.assign 5 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 8 0
  have hex₂ : Exec w (.assign 8 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg 9 (elemWallNumVerts h)
  have hex₃ : Exec w (.assign 9 (.reg 12)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₂, s₁, hr12, hV_w])
  have hmatch0 : Alg74MatchesEdgePrefix (s₃.arrs edgeU1Arr) (s₃.arrs edgeU2Arr)
      (elemWallEdgesPrefix h 0) :=
    ⟨by simp [s₃, s₂, s₁, hu1_len], by simp [s₃, s₂, s₁, hu2_len],
     fun _ hi => by simp [elemWallEdgesPrefix_zero] at hi⟩
  rcases buildWallEdgesLoop_exec hw3 hVJW_w hEJ_w (elemWallNumVerts h) 0
      (Nat.zero_add _) (s := s₃) (by simp [s₃, s₂, s₁, elemWallEdgesPrefix_zero])
      (by simp [s₃, s₂]) (by simp [s₃])
      (by simp [s₃, s₂, s₁, hr12]) (by simp [s₃, s₂, s₁, hr14]) hmatch0 with
    ⟨s', t_loop, hex₄, ht_loop, ⟨hlen1', hlen2', hvals'⟩, hregs', harrs'⟩
  refine ⟨s', 2 + (2 + (2 + t_loop)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hlen1', hlen2',
    fun k => hvals' k.1 k.2,
    fun reg h5 h6 h7 h8 h9 => by
      rw [hregs' reg h5 h6 h7 h8 h9]
      simp [s₃, s₂, s₁, h5, h8, h9],
    fun a ha1 ha2 => by
      rw [harrs' a ha1 ha2]
      simp [s₃, s₂, s₁]⟩

/-! ### Section 3: Active-Pair Search and $H$-Path Processing -/

/-- Whether `(u, v)` appears in `x.G.activePairsList` at some index `k ≥ idx`. -/
def ActivePairFoundFrom {p r : ℕ} (x : Alg74Input p r) (u v : Fin x.n) (idx : ℕ) : Prop :=
  ∃ k : Fin x.G.numActivePairs, idx ≤ k.1 ∧
    (x.G.activePairsList[k.1]'k.2).1 = u ∧ (x.G.activePairsList[k.1]'k.2).2 = v

instance instDecidableActivePairFoundFrom {p r : ℕ} (x : Alg74Input p r)
    (u v : Fin x.n) (idx : ℕ) : Decidable (ActivePairFoundFrom x u v idx) := by
  unfold ActivePairFoundFrom
  infer_instance

theorem activePairFoundFrom_self {p r : ℕ} (x : Alg74Input p r) (u v : Fin x.n) :
    ¬ ActivePairFoundFrom x u v x.G.numActivePairs := by
  rintro ⟨k, hk, _⟩
  have := k.2
  omega

theorem activePairFoundFrom_step {p r : ℕ} (x : Alg74Input p r) (u v : Fin x.n)
    (idx : ℕ) (hidx : idx < x.G.numActivePairs) :
    (((x.G.activePairsList[idx]'hidx).1.1 = u.1 ∧
      (x.G.activePairsList[idx]'hidx).2.1 = v.1) ∨
      ActivePairFoundFrom x u v (idx + 1)) ↔
    ActivePairFoundFrom x u v idx := by
  unfold ActivePairFoundFrom
  constructor
  · rintro (⟨h1, h2⟩ | ⟨k, hk, h1, h2⟩)
    · exact ⟨⟨idx, hidx⟩, le_rfl, Fin.ext h1, Fin.ext h2⟩
    · exact ⟨k, by omega, h1, h2⟩
  · rintro ⟨k, hk, h1, h2⟩
    rcases Nat.eq_or_lt_of_le hk with rfl | hgt
    · exact Or.inl ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
    · exact Or.inr ⟨k, hgt, h1, h2⟩

theorem activePairFoundFrom_zero {p r : ℕ} (x : Alg74Input p r) (u v : Fin x.n) :
    ActivePairFoundFrom x u v 0 ↔ 0 < x.G.edgeMult u v := by
  rw [← x.G.mem_activePairsList (u, v), List.mem_iff_getElem]
  unfold ActivePairFoundFrom MultiDigraph.numActivePairs
  constructor
  · rintro ⟨k, _, h1, h2⟩
    exact ⟨k.1, k.2, Prod.ext h1 h2⟩
  · rintro ⟨i, hi, heq⟩
    exact ⟨⟨i, hi⟩, Nat.zero_le i, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

/-- Loop body of `checkActivePairLoop`: checks whether `x.G.activePairsList[r_8]` equals `(r_6, r_7)`,
setting `r_10 := 1` on a match. -/
def checkActivePairBody : Cmd :=
  .seq (.assign 11 (.op .add (.const 2) (.op .mul (.const 3) (.reg 8))))
    (.seq (.ite (.op .mul
          (.op .eq (.read inArr (.reg 11)) (.reg 6))
          (.op .eq (.read inArr (.op .add (.reg 11) (.const 1))) (.reg 7)))
        (.assign 10 (.const 1))
        .skip)
      (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
        (.assign 9 (.op .sub (.reg 9) (.const 1)))))

/-- Loop scanning `x.G.activePairsList` to test `0 < x.G.edgeMult u v`. -/
def checkActivePairLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) checkActivePairBody

theorem checkActivePairLoop_exec {w p r : ℕ} (x : Alg74Input p r)
    (u v : Fin x.n)
    (hw3 : 3 < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hm_w : 2 + 3 * x.G.numActivePairs < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = x.G.numActivePairs)
      (Found : Prop) [Decidable Found] {s : State}
      (_hin : s.arrs inArr = encAlg74In x)
      (_hr6 : s.regs 6 = u.1)
      (_hr7 : s.regs 7 = v.1)
      (_hr8 : s.regs 8 = idx)
      (_hr9 : s.regs 9 = rem)
      (_hr10 : s.regs 10 = if Found then 1 else 0),
      ∃ s' t,
        Exec w checkActivePairLoop s s' t ∧
        t ≤ 30 * rem + 3 ∧
        s'.regs 10 = (if Found ∨ ActivePairFoundFrom x u v idx then 1 else 0) ∧
        (∀ reg : Reg, reg ≠ 8 → reg ≠ 9 → reg ≠ 10 → reg ≠ 11 → s'.regs reg = s.regs reg) ∧
        s'.arrs = s.arrs
  | 0, idx, hrem, Found, _, s, _, _, _, _, hr9, hr10 => by
    have hidx_eq : idx = x.G.numActivePairs := by omega
    subst hidx_eq
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, fun _ _ _ _ _ => rfl, rfl⟩
    simp [hr10, activePairFoundFrom_self x u v]
  | rem + 1, idx, hrem, Found, _, s, hin, hr6, hr7, hr8, hr9, hr10 => by
    have hidx : idx < x.G.numActivePairs := by omega
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have h2_w : 2 < 2 ^ w := by omega
    have hrem_w : rem + 1 < 2 ^ w := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have h3idx_w : 3 * idx < 2 ^ w := by omega
    have h11_w : 2 + 3 * idx < 2 ^ w := by omega
    have h11_1_w : 2 + 3 * idx + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, h1_w, hrem_w]
    let s₁ := s.setReg 11 (2 + 3 * idx)
    have hex₁ : Exec w (.assign 11 (.op .add (.const 2) (.op .mul (.const 3) (.reg 8)))) s s₁ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8,
        h2_w, hw3, hidx_w, h3idx_w, h11_w])
    have hlen_in : 2 + 3 * idx + 1 < (encAlg74In x).length := by
      simp only [encAlg74In, List.length_append, MultiDigraph.length_enc]
      omega
    have hlen_in0 : 2 + 3 * idx < (encAlg74In x).length := by omega
    let u_cur := (x.G.activePairsList[idx]'hidx).1
    let v_cur := (x.G.activePairsList[idx]'hidx).2
    have hrd0 : (s₁.arrs inArr)[2 + 3 * idx]'(by rw [State.setReg_arrs, hin]; exact hlen_in0) =
        u_cur.1 := by
      simp only [s₁, State.setReg_arrs, hin, u_cur]
      exact getElem_encAlg74In_active_fst x idx hidx hlen_in0
    have hrd1 : (s₁.arrs inArr)[2 + 3 * idx + 1]'(by rw [State.setReg_arrs, hin]; exact hlen_in) =
        v_cur.1 := by
      simp only [s₁, State.setReg_arrs, hin, v_cur]
      exact getElem_encAlg74In_active_snd x idx hidx hlen_in
    have hu_cur_w : u_cur.1 < 2 ^ w := Nat.lt_trans u_cur.2 hn_w
    have hv_cur_w : v_cur.1 < 2 ^ w := Nat.lt_trans v_cur.2 hn_w
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    let MatchCur : Prop := u_cur.1 = u.1 ∧ v_cur.1 = v.1
    have heval_ite :
        (Expr.op .mul
          (.op .eq (.read inArr (.reg 11)) (.reg 6))
          (.op .eq (.read inArr (.op .add (.reg 11) (.const 1))) (.reg 7))).eval w s₁ =
        some (if MatchCur then 1 else 0) := by
      have hlen1 : 2 + 3 * idx < (s₁.arrs inArr).length := by
        rw [State.setReg_arrs, hin]; exact hlen_in0
      have hlen2 : 2 + 3 * idx + 1 < (s₁.arrs inArr).length := by
        rw [State.setReg_arrs, hin]; exact hlen_in
      have heq6 : s₁.regs 6 = u.1 := by simp [s₁, hr6]
      have heq7 : s₁.regs 7 = v.1 := by simp [s₁, hr7]
      have heq11 : s₁.regs 11 = 2 + 3 * idx := by simp [s₁]
      have heval_eq1 :
          (Expr.op .eq (.read inArr (.reg 11)) (.reg 6)).eval w s₁ =
            some (if u_cur.1 = u.1 then 1 else 0) := by
        simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, heq11, heq6,
          h11_w, hlen1, hrd0, hu_cur_w, hu_w, ↓reduceDIte, ↓reduceIte]
        split_ifs <;> simp
      have heval_eq2 :
          (Expr.op .eq (.read inArr (.op .add (.reg 11) (.const 1))) (.reg 7)).eval w s₁ =
            some (if v_cur.1 = v.1 then 1 else 0) := by
        simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, heq11, heq7,
          h11_w, h1_w, h11_1_w, hlen2, hrd1, hv_cur_w, hv_w, ↓reduceDIte, ↓reduceIte]
        split_ifs <;> simp
      rw [Expr.eval, heval_eq1, heval_eq2]
      simp only [BinOp.eval, BinOp.raw, checkWord, MatchCur]
      by_cases h1 : u_cur.1 = u.1 <;> by_cases h2 : v_cur.1 = v.1
      · simp [h1, h2, h1_w]
      · simp [h1, h2, h0_w]
      · simp [h1, h2, h0_w]
      · simp [h1, h2, h0_w]
    have hite_step :
        ∃ s₂ t_ite,
          Exec w (.ite (.op .mul
              (.op .eq (.read inArr (.reg 11)) (.reg 6))
              (.op .eq (.read inArr (.op .add (.reg 11) (.const 1))) (.reg 7)))
            (.assign 10 (.const 1))
            .skip) s₁ s₂ t_ite ∧
          t_ite ≤ 13 ∧
          s₂.regs 10 = (if Found ∨ MatchCur then 1 else 0) ∧
          (∀ reg : Reg, reg ≠ 10 → s₂.regs reg = s₁.regs reg) ∧
          s₂.arrs = s₁.arrs := by
      by_cases hM : MatchCur
      · rw [if_pos hM] at heval_ite
        let s₂ := s₁.setReg 10 1
        have hex_t : Exec w (.assign 10 (.const 1)) s₁ s₂ 2 :=
          .assign (by simp [Expr.eval, checkWord, h1_w])
        refine ⟨s₂, 11 + 2, .ite_true heval_ite (by omega) hex_t, by omega, ?_,
          fun reg hne => State.setReg_regs_ne _ _ hne, rfl⟩
        simp [s₂, hM]
      · rw [if_neg hM] at heval_ite
        refine ⟨s₁, 11 + 1, .ite_false heval_ite (.skip s₁), by omega, ?_,
          fun _ _ => rfl, rfl⟩
        have hr10_1 : s₁.regs 10 = if Found then 1 else 0 := by simp [s₁, hr10]
        simp [hr10_1, hM]
    rcases hite_step with ⟨s₂, t_ite, hex_ite, ht_ite, hr10_2, hreg₂, harr₂⟩
    have hr8_2 : s₂.regs 8 = idx := by rw [hreg₂ 8 (by decide)]; simp [s₁, hr8]
    have hr9_2 : s₂.regs 9 = rem + 1 := by rw [hreg₂ 9 (by decide)]; simp [s₁, hr9]
    let s₃ := s₂.setReg 8 (idx + 1)
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hex₃ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_2, hidx_w, h1_w, hidx1_w])
    let s₄ := s₃.setReg 9 rem
    have hrem0_w : rem < 2 ^ w := by omega
    have hr9_3 : s₃.regs 9 = rem + 1 := by simp [s₃, hr9_2]
    have hex₄ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_3, hrem_w, h1_w, hrem0_w])
    have hex_body : Exec w checkActivePairBody s s₄ (6 + (t_ite + (4 + 4))) :=
      .seq hex₁ (.seq hex_ite (.seq hex₃ hex₄))
    have hin₄ : s₄.arrs inArr = encAlg74In x := by
      simp [s₄, s₃, harr₂, s₁, hin]
    have hr6_4 : s₄.regs 6 = u.1 := by
      simp only [s₄, s₃, State.setReg_regs_ne _ _ (by decide : (6 : Reg) ≠ 9),
        State.setReg_regs_ne _ _ (by decide : (6 : Reg) ≠ 8),
        hreg₂ 6 (by decide), s₁, State.setReg_regs_ne _ _ (by decide : (6 : Reg) ≠ 11), hr6]
    have hr7_4 : s₄.regs 7 = v.1 := by
      simp only [s₄, s₃, State.setReg_regs_ne _ _ (by decide : (7 : Reg) ≠ 9),
        State.setReg_regs_ne _ _ (by decide : (7 : Reg) ≠ 8),
        hreg₂ 7 (by decide), s₁, State.setReg_regs_ne _ _ (by decide : (7 : Reg) ≠ 11), hr7]
    have hr8_4 : s₄.regs 8 = idx + 1 := by simp [s₄, s₃]
    have hr9_4 : s₄.regs 9 = rem := by simp [s₄]
    have hr10_4 : s₄.regs 10 = if Found ∨ MatchCur then 1 else 0 := by
      simp only [s₄, s₃, State.setReg_regs_ne _ _ (by decide : (10 : Reg) ≠ 9),
        State.setReg_regs_ne _ _ (by decide : (10 : Reg) ≠ 8), hr10_2]
    rcases checkActivePairLoop_exec x u v hw3 hn_w hm_w rem (idx + 1) (by omega)
        (Found ∨ MatchCur) hin₄ hr6_4 hr7_4 hr8_4 hr9_4 hr10_4 with
      ⟨s', t_rest, hex_rest, ht_rest, hr10', hreg', harr'⟩
    refine ⟨s', 3 + (6 + (t_ite + (4 + 4))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest, by omega, ?_, ?_, ?_⟩
    · rw [hr10']
      apply if_congr
      · rw [or_assoc, activePairFoundFrom_step x u v idx hidx]
      · rfl
      · rfl
    · intro reg h8 h9 h10 h11
      rw [hreg' reg h8 h9 h10 h11]
      simp only [s₄, s₃, State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8,
        hreg₂ reg h10, s₁, State.setReg_regs_ne _ _ h11]
    · rw [harr']
      simp [s₄, s₃, harr₂, s₁]

/-- Command writing `[(alg74EdgePair x e).1.1, (alg74EdgePair x e).2.1]` to
`outArr[2 + 2 * e_idx .. 2 + 2 * e_idx + 1]` by scanning `x.G.activePairsList`. -/
def checkAndWriteEdgePairCmd (e_idx : ℕ) : Cmd :=
  .seq (.assign 8 (.const 0))
    (.seq (.assign 9 (.reg 1))
      (.seq (.assign 10 (.const 0))
        (.seq checkActivePairLoop
          (.ite (.op .eq (.reg 10) (.const 1))
            (.seq (.write outArr (.const (2 + 2 * e_idx)) (.reg 6))
              (.write outArr (.const (2 + 2 * e_idx + 1)) (.reg 7)))
            (.seq (.write outArr (.const (2 + 2 * e_idx)) (.reg 7))
              (.write outArr (.const (2 + 2 * e_idx + 1)) (.reg 6)))))))

theorem checkAndWriteEdgePairCmd_exec {w p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length)
    {s : State}
    (hw3 : 3 < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hm_w : 2 + 3 * x.G.numActivePairs < 2 ^ w)
    (hout_w : 2 + 2 * (completeGraphEdges p).length + p * x.n < 2 ^ w)
    (hin : s.arrs inArr = encAlg74In x)
    (hr1 : s.regs 1 = x.G.numActivePairs)
    (hr6 : s.regs 6 = (alg74PenultVert x e).1)
    (hr7 : s.regs 7 = (alg74LastVert x e).1)
    (hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n) :
    let K := (completeGraphEdges p).length
    ∃ s' t,
      Exec w (checkAndWriteEdgePairCmd e.1) s s' t ∧
      t ≤ 30 * x.G.numActivePairs + 27 ∧
      (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
      (s'.arrs outArr)[2 + 2 * e.1]? = some (alg74EdgePair x e).1.1 ∧
      (s'.arrs outArr)[2 + 2 * e.1 + 1]? = some (alg74EdgePair x e).2.1 ∧
      (∀ i : ℕ, i < 2 + 2 * K → i ≠ 2 + 2 * e.1 → i ≠ 2 + 2 * e.1 + 1 →
        (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
      (∀ (gamma : Fin p) {S : Finset (Fin x.n)},
        IsBitSlice (s.arrs outArr) (2 + 2 * K + gamma.1 * x.n) S →
        IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * x.n) S) ∧
      (∀ reg : Reg, reg ≠ 8 → reg ≠ 9 → reg ≠ 10 → reg ≠ 11 → s'.regs reg = s.regs reg) ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) := by
  intro K
  have he_lt : e.1 < K := e.2
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hm0_w : x.G.numActivePairs < 2 ^ w := by omega
  let s₁ := s.setReg 8 0
  have hex₁ : Exec w (.assign 8 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 9 x.G.numActivePairs
  have hex₂ : Exec w (.assign 9 (.reg 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₁, hr1, hm0_w])
  let s₃ := s₂.setReg 10 0
  have hex₃ : Exec w (.assign 10 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hin₃ : s₃.arrs inArr = encAlg74In x := by simp [s₃, s₂, s₁, hin]
  have hr6_3 : s₃.regs 6 = (alg74PenultVert x e).1 := by simp [s₃, s₂, s₁, hr6]
  have hr7_3 : s₃.regs 7 = (alg74LastVert x e).1 := by simp [s₃, s₂, s₁, hr7]
  have hr8_3 : s₃.regs 8 = 0 := by simp [s₃, s₂, s₁]
  have hr9_3 : s₃.regs 9 = x.G.numActivePairs := by simp [s₃, s₂]
  have hr10_3 : s₃.regs 10 = if False then 1 else 0 := by simp [s₃]
  rcases checkActivePairLoop_exec x (alg74PenultVert x e) (alg74LastVert x e)
      hw3 hn_w hm_w x.G.numActivePairs 0 (Nat.zero_add _) False
      hin₃ hr6_3 hr7_3 hr8_3 hr9_3 hr10_3 with
    ⟨s₄, t_loop, hex_loop, ht_loop, hr10_4, hreg₄, harr₄⟩
  have hr10_edge :
      s₄.regs 10 =
        if 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e) then 1 else 0 := by
    rw [hr10_4]
    exact if_congr (by simp [activePairFoundFrom_zero]) rfl rfl
  have hr6_4 : s₄.regs 6 = (alg74PenultVert x e).1 := by
    rw [hreg₄ 6 (by decide) (by decide) (by decide) (by decide), hr6_3]
  have hr7_4 : s₄.regs 7 = (alg74LastVert x e).1 := by
    rw [hreg₄ 7 (by decide) (by decide) (by decide) (by decide), hr7_3]
  have hout_s4 : s₄.arrs outArr = s.arrs outArr := by
    rw [harr₄]; rfl
  have hu_w : (alg74PenultVert x e).1 < 2 ^ w := Nat.lt_trans (alg74PenultVert x e).2 hn_w
  have hv_w : (alg74LastVert x e).1 < 2 ^ w := Nat.lt_trans (alg74LastVert x e).2 hn_w
  have he0_w : 2 + 2 * e.1 < 2 ^ w := by omega
  have he1_w : 2 + 2 * e.1 + 1 < 2 ^ w := by omega
  have he0_len : 2 + 2 * e.1 < (s₄.arrs outArr).length := by rw [hout_s4, hout_len]; omega
  have he1_len : 2 + 2 * e.1 + 1 < (s₄.arrs outArr).length := by rw [hout_s4, hout_len]; omega
  by_cases hpos : 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e)
  · rw [if_pos hpos] at hr10_edge
    have hcond : (Expr.op .eq (.reg 10) (.const 1)).eval w s₄ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10_edge, h1_w]
    let s₅ := s₄.writeArr outArr (2 + 2 * e.1) (alg74PenultVert x e).1
    have hex_w1 : Exec w (.write outArr (.const (2 + 2 * e.1)) (.reg 6)) s₄ s₅ 3 :=
      .write (by simp [Expr.eval, checkWord, he0_w])
        (by simp [Expr.eval, checkWord, hr6_4, hu_w]) he0_len
    let s₆ := s₅.writeArr outArr (2 + 2 * e.1 + 1) (alg74LastVert x e).1
    have hex_w2 : Exec w (.write outArr (.const (2 + 2 * e.1 + 1)) (.reg 7)) s₅ s₆ 3 :=
      .write (by simp [Expr.eval, checkWord, he1_w])
        (by simp [Expr.eval, checkWord, s₅, hr7_4, hv_w])
        (by simp [s₅, he1_len])
    have hex_ite :
        Exec w (.ite (.op .eq (.reg 10) (.const 1))
          (.seq (.write outArr (.const (2 + 2 * e.1)) (.reg 6))
            (.write outArr (.const (2 + 2 * e.1 + 1)) (.reg 7)))
          (.seq (.write outArr (.const (2 + 2 * e.1)) (.reg 7))
            (.write outArr (.const (2 + 2 * e.1 + 1)) (.reg 6)))) s₄ s₆ (3 + (3 + 3)) :=
      .ite_true hcond (by omega) (.seq hex_w1 hex_w2)
    refine ⟨s₆, 2 + (2 + (2 + (t_loop + (3 + (3 + 3))))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex_loop hex_ite))), by omega,
      by simp [s₆, s₅, hout_s4, hout_len, K], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [s₆, s₅, he0_len, alg74EdgePair_fst_of_pos x e hpos]
    · simp [s₆, s₅, he1_len, alg74EdgePair_snd_of_pos x e hpos]
    · intro i hi hne0 hne1
      simp [s₆, s₅, hne0.symm, hne1.symm, hout_s4]
    · intro gamma S hS
      simp only [s₆, s₅, State.writeArr_arrs_self, hout_s4]
      apply isBitSlice_set_other (isBitSlice_set_other hS _ _ (Or.inl (by omega)))
      exact Or.inl (by omega)
    · intro reg h8 h9 h10 h11
      simp only [s₆, s₅, State.writeArr_regs, hreg₄ reg h8 h9 h10 h11,
        s₃, s₂, s₁, State.setReg_regs_ne _ _ h10, State.setReg_regs_ne _ _ h9,
        State.setReg_regs_ne _ _ h8]
    · intro a ha
      simp [s₆, s₅, State.writeArr_arrs_ne _ _ _ ha, harr₄, s₃, s₂, s₁]
  · rw [if_neg hpos] at hr10_edge
    have hcond : (Expr.op .eq (.reg 10) (.const 1)).eval w s₄ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10_edge, h0_w, h1_w]
    let s₅ := s₄.writeArr outArr (2 + 2 * e.1) (alg74LastVert x e).1
    have hex_w1 : Exec w (.write outArr (.const (2 + 2 * e.1)) (.reg 7)) s₄ s₅ 3 :=
      .write (by simp [Expr.eval, checkWord, he0_w])
        (by simp [Expr.eval, checkWord, hr7_4, hv_w]) he0_len
    let s₆ := s₅.writeArr outArr (2 + 2 * e.1 + 1) (alg74PenultVert x e).1
    have hex_w2 : Exec w (.write outArr (.const (2 + 2 * e.1 + 1)) (.reg 6)) s₅ s₆ 3 :=
      .write (by simp [Expr.eval, checkWord, he1_w])
        (by simp [Expr.eval, checkWord, s₅, hr6_4, hu_w])
        (by simp [s₅, he1_len])
    have hex_ite :
        Exec w (.ite (.op .eq (.reg 10) (.const 1))
          (.seq (.write outArr (.const (2 + 2 * e.1)) (.reg 6))
            (.write outArr (.const (2 + 2 * e.1 + 1)) (.reg 7)))
          (.seq (.write outArr (.const (2 + 2 * e.1)) (.reg 7))
            (.write outArr (.const (2 + 2 * e.1 + 1)) (.reg 6)))) s₄ s₆ (3 + (3 + 3)) :=
      .ite_false hcond (.seq hex_w1 hex_w2)
    refine ⟨s₆, 2 + (2 + (2 + (t_loop + (3 + (3 + 3))))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex_loop hex_ite))), by omega,
      by simp [s₆, s₅, hout_s4, hout_len, K], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [s₆, s₅, he0_len, alg74EdgePair_fst_of_not_pos x e hpos]
    · simp [s₆, s₅, he1_len, alg74EdgePair_snd_of_not_pos x e hpos]
    · intro i hi hne0 hne1
      simp [s₆, s₅, hne0.symm, hne1.symm, hout_s4]
    · intro gamma S hS
      simp only [s₆, s₅, State.writeArr_arrs_self, hout_s4]
      apply isBitSlice_set_other (isBitSlice_set_other hS _ _ (Or.inl (by omega)))
      exact Or.inl (by omega)
    · intro reg h8 h9 h10 h11
      simp only [s₆, s₅, State.writeArr_regs, hreg₄ reg h8 h9 h10 h11,
        s₃, s₂, s₁, State.setReg_regs_ne _ _ h10, State.setReg_regs_ne _ _ h9,
        State.setReg_regs_ne _ _ h8]
    · intro a ha
      simp [s₆, s₅, State.writeArr_arrs_ne _ _ _ ha, harr₄, s₃, s₂, s₁]

/-- Loop body of `markPathListLoop`: reads `r_11 := inArr[r_8]` and marks vertex `r_11` in color
`gamma`'s bit slice of `outArr`. -/
def markPathListBody (K gamma : ℕ) : Cmd :=
  .seq (.assign 11 (.read inArr (.reg 8)))
    (.seq (markVertexCmd K gamma (.reg 11))
      (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
        (.assign 9 (.op .sub (.reg 9) (.const 1)))))

/-- Loop marking all vertices of a list `vs : List (Fin n)` in color `gamma`'s bit slice of `outArr`. -/
def markPathListLoop (K gamma : ℕ) : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) (markPathListBody K gamma)

private theorem getElem_append_cons_getElem {α : Type*} (pre : List α) (a : α) (mid suf : List α)
    (pos i : ℕ) (hpos : pre.length = pos) (hi : i < mid.length) :
    (pre ++ (a :: (mid ++ suf)))[pos + 1 + i]'(by simp [hpos]; omega) = mid[i]'hi := by
  subst hpos
  rw [List.getElem_append_right (by omega)]
  have hsub : pre.length + 1 + i - pre.length = i + 1 := by omega
  rw [getElem_congr_idx _ hsub, List.getElem_cons_succ]
  exact List.getElem_append_left hi

theorem markPathListLoop_exec {w p K n : ℕ} (gamma : Fin p)
    (hw1 : 1 < 2 ^ w)
    (hp_w : p < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hout_w : 2 + 2 * K + p * n < 2 ^ w) :
    ∀ (vs : List (Fin n)) (pre suf : List ℕ) (S : Finset (Fin n)) {s : State}
      (_hin : s.arrs inArr = pre ++ (vs.map Fin.val ++ suf))
      (_hin_w : (s.arrs inArr).length < 2 ^ w)
      (_hr0 : s.regs 0 = n)
      (_hr8 : s.regs 8 = pre.length)
      (_hr9 : s.regs 9 = vs.length)
      (_hout_len : (s.arrs outArr).length = 2 + 2 * K + p * n)
      (_hS : IsBitSlice (s.arrs outArr) (2 + 2 * K + gamma.1 * n) S),
      ∃ s' t,
        Exec w (markPathListLoop K gamma.1) s s' t ∧
        t ≤ 23 * vs.length + 3 ∧
        (s'.arrs outArr).length = 2 + 2 * K + p * n ∧
        IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * n) (S ∪ vs.toFinset) ∧
        (∀ (gamma' : Fin p) {S' : Finset (Fin n)}, gamma' ≠ gamma →
          IsBitSlice (s.arrs outArr) (2 + 2 * K + gamma'.1 * n) S' →
          IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma'.1 * n) S') ∧
        (∀ i : ℕ, i < 2 + 2 * K →
          (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
        (∀ reg : Reg, reg ≠ 8 → reg ≠ 9 → reg ≠ 11 → s'.regs reg = s.regs reg) ∧
        (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a)
  | [], pre, suf, S, s, _, _, _, _, hr9, hout_len, hS => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hout_len, by simpa using hS,
      fun _ _ _ hS' => hS', fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | v :: rest, pre, suf, S, s, hin, hin_w, hr0, hr8, hr9, hout_len, hS => by
    have h0_w : 0 < 2 ^ w := by omega
    have hlen_in : pre.length + 1 + rest.length ≤ (s.arrs inArr).length := by
      simp [hin]; omega
    have hpos_w : pre.length < 2 ^ w := by omega
    have hpos1_w : pre.length + 1 < 2 ^ w := by omega
    have hrem_w : rest.length + 1 < 2 ^ w := by omega
    have hrem0_w : rest.length < 2 ^ w := by omega
    have hr9_eq : s.regs 9 = rest.length + 1 := by simpa using hr9
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_eq, h0_w, hw1, hrem_w]
    have hget_v : (s.arrs inArr)[pre.length]'(by omega) = v.1 := by
      simp only [hin, List.map_cons, List.cons_append]
      exact getElem_append_cons pre v.1 _ pre.length rfl
    let s₁ := s.setReg 11 v.1
    have hex₁ : Exec w (.assign 11 (.read inArr (.reg 8))) s s₁ 3 := by
      have hpos_lt : pre.length < (s.arrs inArr).length := by omega
      exact .assign (by simp [Expr.eval, checkWord, hr8, hpos_w, hpos_lt, hget_v, hv_w])
    have hr0_1 : s₁.regs 0 = n := by simp [s₁, hr0]
    have hev_11 : (Expr.reg 11).eval w s₁ = some v.1 := by
      simp [Expr.eval, checkWord, s₁, hv_w]
    have hout_len1 : (s₁.arrs outArr).length = 2 + 2 * K + p * n := by simp [s₁, hout_len]
    rcases markVertexCmd_exec gamma (.reg 11) v hw1 hp_w hout_w hr0_1 hev_11 hout_len1 with
      ⟨hex₂, hout_len2, hS_ins, hS_other2, hprefix2, hregs2, harrs2⟩
    let s₂ := s₁.writeArr outArr (2 + 2 * K + gamma.1 * n + v.1) 1
    have hS₂ : IsBitSlice (s₂.arrs outArr) (2 + 2 * K + gamma.1 * n) (insert v S) :=
      hS_ins (by simpa [s₁] using hS)
    have hr8_2 : s₂.regs 8 = pre.length := by
      rw [hregs2]; simp [s₁, hr8]
    have hr9_2 : s₂.regs 9 = rest.length + 1 := by
      rw [hregs2]; simp [s₁, hr9]
    let s₃ := s₂.setReg 8 (pre.length + 1)
    have hex₃ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_2, hpos_w, hw1, hpos1_w])
    let s₄ := s₃.setReg 9 rest.length
    have hr9_3 : s₃.regs 9 = rest.length + 1 := by simp [s₃, hr9_2]
    have hex₄ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_3, hrem_w, hw1, hrem0_w])
    have hex_body : Exec w (markPathListBody K gamma.1) s s₄ (3 + (9 + (4 + 4))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
    have hin₄ : s₄.arrs inArr = (pre ++ [v.1]) ++ (rest.map Fin.val ++ suf) := by
      have hin_eq : s₄.arrs inArr = s.arrs inArr := by
        simp [s₄, s₃, s₂, s₁]
      rw [hin_eq, hin]
      simp
    have hin_w4 : (s₄.arrs inArr).length < 2 ^ w := by
      have hin_eq : s₄.arrs inArr = s.arrs inArr := by
        simp [s₄, s₃, s₂, s₁]
      rwa [hin_eq]
    have hr0_4 : s₄.regs 0 = n := by
      simp [s₄, s₃, s₂, hr0_1]
    have hr8_4 : s₄.regs 8 = (pre ++ [v.1]).length := by simp [s₄, s₃]
    have hr9_4 : s₄.regs 9 = rest.length := by simp [s₄]
    have hout_len4 : (s₄.arrs outArr).length = 2 + 2 * K + p * n := by
      simpa [s₄, s₃, s₂] using hout_len2
    have hS₄ : IsBitSlice (s₄.arrs outArr) (2 + 2 * K + gamma.1 * n) (insert v S) := by
      simpa [s₄, s₃] using hS₂
    rcases markPathListLoop_exec gamma hw1 hp_w hn_w hout_w rest (pre ++ [v.1]) suf (insert v S)
        hin₄ hin_w4 hr0_4 hr8_4 hr9_4 hout_len4 hS₄ with
      ⟨s', t_rest, hex_rest, ht_rest, hout_len', hS', hS_other', hprefix', hregs', harrs'⟩
    have hset_eq : insert v S ∪ rest.toFinset = S ∪ (v :: rest).toFinset := by
      ext z
      simp
    rw [hset_eq] at hS'
    refine ⟨s', 3 + (3 + (9 + (4 + 4))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by simp only [List.length_cons]; omega,
      hout_len', hS', ?_, ?_, ?_, ?_⟩
    · intro gamma' S' hne hS'_0
      apply hS_other' gamma' hne
      simpa [s₄, s₃, s₂] using hS_other2 gamma' hne (by simpa [s₁] using hS'_0)
    · intro i hi
      rw [hprefix' i hi]
      simpa [s₄, s₃, s₂, s₁] using hprefix2 i hi
    · intro reg h8 h9 h11
      rw [hregs' reg h8 h9 h11]
      simp only [s₄, s₃, State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8,
        s₂, State.writeArr_regs, s₁, State.setReg_regs_ne _ _ h11]
    · intro a ha
      rw [harrs' a ha]
      simp [s₄, s₃, s₂, harrs2 a ha, s₁]

theorem getElem_pathBlock_head {n : ℕ} (P : List (Fin n)) (hne : P ≠ [])
    (pre suf : List ℕ) (pos : ℕ) (hpos : pre.length = pos) :
    (pre ++ (P.length :: P.map Fin.val ++ suf))[pos + 1]'(by
      have := List.length_pos_of_ne_nil hne; simp [hpos]; omega) =
      (P.head hne).1 := by
  have hlen_pos : 0 < (P.map Fin.val).length := by
    simp [List.length_pos_of_ne_nil hne]
  have h1 : pos + 1 = pos + 1 + 0 := by omega
  simp only [List.cons_append]
  rw [getElem_congr_idx _ h1,
    getElem_append_cons_getElem pre P.length (P.map Fin.val) suf pos 0 hpos hlen_pos]
  simp [List.head_eq_getElem_zero]

theorem getElem_pathBlock_penult {n : ℕ} (P : List (Fin n)) (hdrop : P.dropLast ≠ [])
    (hlen2 : 2 ≤ P.length) (pre suf : List ℕ) (pos : ℕ) (hpos : pre.length = pos) :
    (pre ++ (P.length :: P.map Fin.val ++ suf))[pos + P.length - 1]'(by simp [hpos]; omega) =
      (P.dropLast.getLast hdrop).1 := by
  have hidx : P.length - 2 < (P.map Fin.val).length := by simp; omega
  have h1 : pos + P.length - 1 = pos + 1 + (P.length - 2) := by omega
  simp only [List.cons_append]
  rw [getElem_congr_idx _ h1,
    getElem_append_cons_getElem pre P.length (P.map Fin.val) suf pos (P.length - 2) hpos hidx]
  rw [List.getLast_eq_getElem]
  simp only [List.getElem_map, List.getElem_dropLast]
  congr 1
  exact getElem_congr_idx P (by rw [List.length_dropLast]; omega) _

theorem getElem_pathBlock_last {n : ℕ} (P : List (Fin n)) (hne : P ≠ [])
    (hlen2 : 2 ≤ P.length) (pre suf : List ℕ) (pos : ℕ) (hpos : pre.length = pos) :
    (pre ++ (P.length :: P.map Fin.val ++ suf))[pos + P.length]'(by simp [hpos]) =
      (P.getLast hne).1 := by
  have hidx : P.length - 1 < (P.map Fin.val).length := by simp; omega
  have h1 : pos + P.length = pos + 1 + (P.length - 1) := by omega
  simp only [List.cons_append]
  rw [getElem_congr_idx _ h1,
    getElem_append_cons_getElem pre P.length (P.map Fin.val) suf pos (P.length - 1) hpos hidx]
  simp [List.getLast_eq_getElem]

theorem pathBlock_eq_dropLast_append {n : ℕ} (P : List (Fin n)) (hne : P ≠ [])
    (pre suf : List ℕ) :
    pre ++ (P.length :: P.map Fin.val ++ suf) =
      (pre ++ [P.length]) ++ (P.dropLast.map Fin.val ++ ([(P.getLast hne).1] ++ suf)) := by
  have hmap : P.map Fin.val = P.dropLast.map Fin.val ++ [(P.getLast hne).1] := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    simp
  rw [hmap]
  simp [List.append_assoc]

/-- Command processing the `e`-th $H$-path in `inArr` at offset `r_4`. -/
def processOnePathCmd (p : ℕ) (e : Fin (completeGraphEdges p).length) : Cmd :=
  let K := (completeGraphEdges p).length
  let gamma₁ := ((completeGraphEdges p)[e.1]'e.2).1
  .seq (.assign 5 (.read inArr (.reg 4)))
    (.seq (.assign (20 + 2 * e.1) (.read inArr (.op .add (.reg 4) (.const 1))))
      (.seq (.assign 6 (.read inArr (.op .sub (.op .add (.reg 4) (.reg 5)) (.const 1))))
        (.seq (.assign 7 (.read inArr (.op .add (.reg 4) (.reg 5))))
          (.seq (.assign (20 + 2 * e.1 + 1) (.reg 7))
            (.seq (checkAndWriteEdgePairCmd e.1)
              (.seq (.assign 8 (.op .add (.reg 4) (.const 1)))
                (.seq (.assign 9 (.op .sub (.reg 5) (.const 1)))
                  (.seq (markPathListLoop K gamma₁.1)
                    (.assign 4 (.op .add (.op .add (.reg 4) (.const 1)) (.reg 5)))))))))))

theorem processOnePathCmd_exec {w p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length)
    (pre suf : List ℕ)
    (S : Fin p → Finset (Fin x.n))
    {s : State}
    (hw3 : 3 < 2 ^ w)
    (hp_w : p < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hm_w : 2 + 3 * x.G.numActivePairs < 2 ^ w)
    (hin_w : (encAlg74In x).length < 2 ^ w)
    (hout_w : 2 + 2 * (completeGraphEdges p).length + p * x.n < 2 ^ w)
    (hin : s.arrs inArr = encAlg74In x)
    (hsplit : encAlg74In x = pre ++ ((alg74Path x e).length :: (alg74Path x e).map Fin.val ++ suf))
    (hr0 : s.regs 0 = x.n)
    (hr1 : s.regs 1 = x.G.numActivePairs)
    (hr4 : s.regs 4 = pre.length)
    (hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
    (hS : ∀ gamma : Fin p,
      IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + gamma.1 * x.n) (S gamma)) :
    let K := (completeGraphEdges p).length
    let P := alg74Path x e
    let gamma₁ := ((completeGraphEdges p)[e.1]'e.2).1
    ∃ s' t,
      Exec w (processOnePathCmd p e) s s' t ∧
      t ≤ 30 * x.G.numActivePairs + 23 * x.n + 65 ∧
      s'.arrs inArr = encAlg74In x ∧
      (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
      s'.regs 0 = x.n ∧
      s'.regs 1 = x.G.numActivePairs ∧
      s'.regs 2 = s.regs 2 ∧
      s'.regs 3 = s.regs 3 ∧
      s'.regs 4 = (pre ++ (P.length :: P.map Fin.val)).length ∧
      s'.regs (20 + 2 * e.1) = (alg74TermVert x (edgeStartTerm e)).1 ∧
      s'.regs (20 + 2 * e.1 + 1) = (alg74TermVert x (edgeEndTerm e)).1 ∧
      (∀ reg : Reg, 12 ≤ reg → reg ≠ 20 + 2 * e.1 → reg ≠ 20 + 2 * e.1 + 1 →
        s'.regs reg = s.regs reg) ∧
      (s'.arrs outArr)[2 + 2 * e.1]? = some (alg74EdgePair x e).1.1 ∧
      (s'.arrs outArr)[2 + 2 * e.1 + 1]? = some (alg74EdgePair x e).2.1 ∧
      (∀ i : ℕ, i < 2 + 2 * K → i ≠ 2 + 2 * e.1 → i ≠ 2 + 2 * e.1 + 1 →
        (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
      (∀ gamma : Fin p,
        IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * x.n)
          (if gamma₁ = gamma then S gamma ∪ P.dropLast.toFinset else S gamma)) ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) := by
  intro K P gamma₁
  have hne : P ≠ [] := alg74Path_ne_nil x e
  have hdrop : P.dropLast ≠ [] := alg74Path_dropLast_ne_nil x e
  rcases length_alg74Path_bounds x e with ⟨hlen2, hlen_le_n⟩
  change 2 ≤ P.length at hlen2
  change P.length ≤ x.n at hlen_le_n
  have h1_w : 1 < 2 ^ w := by omega
  have hlen_in_eq : (encAlg74In x).length = pre.length + 1 + P.length + suf.length := by
    rw [hsplit]
    simp only [P, List.length_append, List.length_cons, List.length_map]
    omega
  have hpos_w : pre.length < 2 ^ w := by omega
  have hpos1_w : pre.length + 1 < 2 ^ w := by omega
  have hlenP_w : P.length < 2 ^ w := by omega
  have hlenP1_w : P.length - 1 < 2 ^ w := by omega
  have hposP_w : pre.length + P.length < 2 ^ w := by omega
  have hposP1_w : pre.length + P.length - 1 < 2 ^ w := by omega
  have hpos1P_w : pre.length + 1 + P.length < 2 ^ w := by omega
  have hlt_in0 : pre.length < (encAlg74In x).length := by omega
  have hlt_in1 : pre.length + 1 < (encAlg74In x).length := by omega
  have hlt_in_pen : pre.length + P.length - 1 < (encAlg74In x).length := by omega
  have hlt_in_last : pre.length + P.length < (encAlg74In x).length := by omega
  have hin_split : s.arrs inArr = pre ++ (P.length :: P.map Fin.val ++ suf) :=
    hin.trans hsplit
  have hget_len : (s.arrs inArr)[pre.length]'(by rw [hin]; exact hlt_in0) = P.length := by
    simp only [hin_split]
    exact getElem_append_cons pre P.length _ pre.length rfl
  let s₁ := s.setReg 5 P.length
  have hex₁ : Exec w (.assign 5 (.read inArr (.reg 4))) s s₁ 3 := by
    have hlt : pre.length < (s.arrs inArr).length := by rw [hin]; exact hlt_in0
    exact .assign (by simp [Expr.eval, checkWord, hr4, hpos_w, hlt, hget_len, hlenP_w])
  have hget_head : (s₁.arrs inArr)[pre.length + 1]'(by simp [s₁, hin, hlt_in1]) =
      (alg74TermVert x (edgeStartTerm e)).1 := by
    simp only [s₁, State.setReg_arrs, hin_split, alg74TermVert_edgeStartTerm]
    exact getElem_pathBlock_head P hne pre suf pre.length rfl
  have hstart_w : (alg74TermVert x (edgeStartTerm e)).1 < 2 ^ w :=
    Nat.lt_trans (alg74TermVert x (edgeStartTerm e)).2 hn_w
  let s₂ := s₁.setReg (20 + 2 * e.1) (alg74TermVert x (edgeStartTerm e)).1
  have hex₂ : Exec w (.assign (20 + 2 * e.1) (.read inArr (.op .add (.reg 4) (.const 1)))) s₁ s₂ 5 := by
    have hlt : pre.length + 1 < (s₁.arrs inArr).length := by simp [s₁, hin, hlt_in1]
    have hr4_1 : s₁.regs 4 = pre.length := by simp [s₁, hr4]
    exact .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_1,
      hpos_w, h1_w, hpos1_w, hlt, hget_head, hstart_w])
  have hget_penult : (s₂.arrs inArr)[pre.length + P.length - 1]'(by simp [s₂, s₁, hin, hlt_in_pen]) =
      (alg74PenultVert x e).1 := by
    simp only [s₂, s₁, State.setReg_arrs, hin_split, alg74PenultVert]
    exact getElem_pathBlock_penult P hdrop hlen2 pre suf pre.length rfl
  have hpen_w : (alg74PenultVert x e).1 < 2 ^ w :=
    Nat.lt_trans (alg74PenultVert x e).2 hn_w
  let s₃ := s₂.setReg 6 (alg74PenultVert x e).1
  have hex₃ :
      Exec w (.assign 6 (.read inArr (.op .sub (.op .add (.reg 4) (.reg 5)) (.const 1)))) s₂ s₃ 7 := by
    have hlt : pre.length + P.length - 1 < (s₂.arrs inArr).length := by simp [s₂, s₁, hin, hlt_in_pen]
    have hr4_2 : s₂.regs 4 = pre.length := by
      simp only [s₂, s₁, State.setReg_regs_nat, hr4]; split_ifs <;> omega
    have hr5_2 : s₂.regs 5 = P.length := by
      simp only [s₂, s₁, State.setReg_regs_nat]; split_ifs <;> omega
    exact .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_2, hr5_2,
      hpos_w, hlenP_w, hposP_w, h1_w, hposP1_w, hlt, hget_penult, hpen_w])
  have hget_last : (s₃.arrs inArr)[pre.length + P.length]'(by simp [s₃, s₂, s₁, hin, hlt_in_last]) =
      (alg74LastVert x e).1 := by
    simp only [s₃, s₂, s₁, State.setReg_arrs, hin_split, alg74LastVert]
    exact getElem_pathBlock_last P hne hlen2 pre suf pre.length rfl
  have hlast_w : (alg74LastVert x e).1 < 2 ^ w :=
    Nat.lt_trans (alg74LastVert x e).2 hn_w
  let s₄ := s₃.setReg 7 (alg74LastVert x e).1
  have hex₄ : Exec w (.assign 7 (.read inArr (.op .add (.reg 4) (.reg 5)))) s₃ s₄ 5 := by
    have hlt : pre.length + P.length < (s₃.arrs inArr).length := by simp [s₃, s₂, s₁, hin, hlt_in_last]
    have hr4_3 : s₃.regs 4 = pre.length := by
      simp only [s₃, s₂, s₁, State.setReg_regs_nat, hr4]; split_ifs <;> omega
    have hr5_3 : s₃.regs 5 = P.length := by
      simp only [s₃, s₂, s₁, State.setReg_regs_nat]; split_ifs <;> omega
    exact .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_3, hr5_3,
      hpos_w, hlenP_w, hposP_w, hlt, hget_last, hlast_w])
  let s₅ := s₄.setReg (20 + 2 * e.1 + 1) (alg74LastVert x e).1
  have hex₅ : Exec w (.assign (20 + 2 * e.1 + 1) (.reg 7)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₄, hlast_w])
  have hin₅ : s₅.arrs inArr = encAlg74In x := by simp [s₅, s₄, s₃, s₂, s₁, hin]
  have hr1_5 : s₅.regs 1 = x.G.numActivePairs := by
    simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_regs_nat, hr1]; split_ifs <;> omega
  have hr6_5 : s₅.regs 6 = (alg74PenultVert x e).1 := by
    simp only [s₅, s₄, s₃, State.setReg_regs_nat]; split_ifs <;> omega
  have hr7_5 : s₅.regs 7 = (alg74LastVert x e).1 := by
    simp only [s₅, s₄, State.setReg_regs_nat]; split_ifs <;> omega
  have hout_len5 : (s₅.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n := by
    simp [s₅, s₄, s₃, s₂, s₁, hout_len]
  rcases checkAndWriteEdgePairCmd_exec x e hw3 hn_w hm_w hout_w hin₅ hr1_5 hr6_5 hr7_5 hout_len5 with
    ⟨s₆, t_edge, hex₆, ht_edge, hout_len6, hedge0_6, hedge1_6, hedge_other6, hS_6, hreg6, harr6⟩
  have hr4_6 : s₆.regs 4 = pre.length := by
    rw [hreg6 4 (by decide) (by decide) (by decide) (by decide)]
    simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_regs_nat, hr4]; split_ifs <;> omega
  have hr5_6 : s₆.regs 5 = P.length := by
    rw [hreg6 5 (by decide) (by decide) (by decide) (by decide)]
    simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_regs_nat]; split_ifs <;> omega
  let s₇ := s₆.setReg 8 (pre.length + 1)
  have hex₇ : Exec w (.assign 8 (.op .add (.reg 4) (.const 1))) s₆ s₇ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_6, hpos_w, h1_w, hpos1_w])
  let s₈ := s₇.setReg 9 (P.length - 1)
  have hr5_7 : s₇.regs 5 = P.length := by simp [s₇, hr5_6]
  have hex₈ : Exec w (.assign 9 (.op .sub (.reg 5) (.const 1))) s₇ s₈ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr5_7, hlenP_w, h1_w, hlenP1_w])
  have hin₈_raw : s₈.arrs inArr = encAlg74In x := by
    simp [s₈, s₇, harr6 inArr (by decide), hin₅]
  have hin₈ :
      s₈.arrs inArr =
        (pre ++ [P.length]) ++ (P.dropLast.map Fin.val ++ ([(P.getLast hne).1] ++ suf)) := by
    rw [hin₈_raw, hsplit]
    exact pathBlock_eq_dropLast_append P hne pre suf
  have hin_w8 : (s₈.arrs inArr).length < 2 ^ w := by rwa [hin₈_raw]
  have hr0_8 : s₈.regs 0 = x.n := by
    have hne20 : (0 : Reg) ≠ 20 + 2 * e.1 := by dsimp [Reg]; omega
    have hne21 : (0 : Reg) ≠ 20 + 2 * e.1 + 1 := by dsimp [Reg]; omega
    simp only [s₈, s₇, State.setReg_regs_ne _ _ (by decide : (0 : Reg) ≠ 9),
      State.setReg_regs_ne _ _ (by decide : (0 : Reg) ≠ 8),
      hreg6 0 (by decide) (by decide) (by decide) (by decide),
      s₅, s₄, s₃, s₂, s₁,
      State.setReg_regs_ne _ _ hne21,
      State.setReg_regs_ne _ _ (by decide : (0 : Reg) ≠ 7),
      State.setReg_regs_ne _ _ (by decide : (0 : Reg) ≠ 6),
      State.setReg_regs_ne _ _ hne20,
      State.setReg_regs_ne _ _ (by decide : (0 : Reg) ≠ 5),
      hr0]
  have hr8_8 : s₈.regs 8 = (pre ++ [P.length]).length := by simp [s₈, s₇]
  have hr9_8 : s₈.regs 9 = P.dropLast.length := by simp [s₈, List.length_dropLast]
  have hout_len8 : (s₈.arrs outArr).length = 2 + 2 * K + p * x.n := by
    simpa [s₈, s₇] using hout_len6
  have hS_8 : ∀ gamma : Fin p,
      IsBitSlice (s₈.arrs outArr) (2 + 2 * K + gamma.1 * x.n) (S gamma) := by
    intro gamma
    simpa [s₈, s₇] using hS_6 gamma (by simpa [s₅, s₄, s₃, s₂, s₁] using hS gamma)
  rcases markPathListLoop_exec gamma₁ h1_w hp_w hn_w hout_w P.dropLast (pre ++ [P.length])
      ([(P.getLast hne).1] ++ suf) (S gamma₁) hin₈ hin_w8 hr0_8 hr8_8 hr9_8 hout_len8 (hS_8 gamma₁) with
    ⟨s₉, t_mark, hex₉, ht_mark, hout_len9, hS_g1_9, hS_other9, hprefix9, hregs9, harrs9⟩
  have hr4_9 : s₉.regs 4 = pre.length := by
    rw [hregs9 4 (by decide) (by decide) (by decide)]
    simp [s₈, s₇, hr4_6]
  have hr5_9 : s₉.regs 5 = P.length := by
    rw [hregs9 5 (by decide) (by decide) (by decide)]
    simp [s₈, s₇, hr5_6]
  let s₁₀ := s₉.setReg 4 (pre.length + 1 + P.length)
  have hex₁₀ :
      Exec w (.assign 4 (.op .add (.op .add (.reg 4) (.const 1)) (.reg 5))) s₉ s₁₀ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_9, hr5_9,
      hpos_w, h1_w, hpos1_w, hlenP_w, hpos1P_w])
  have ht_mark_le : t_mark ≤ 23 * x.n := by
    have hd_le : P.dropLast.length + 1 ≤ x.n := by
      rw [List.length_dropLast]; omega
    have hmul : 23 * (P.dropLast.length + 1) ≤ 23 * x.n := Nat.mul_le_mul_left 23 hd_le
    omega
  refine ⟨s₁₀, 3 + (5 + (7 + (5 + (2 + (t_edge + (4 + (4 + (t_mark + 6)))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s₁₀, harrs9 inArr (by decide), hin₈_raw]
  · simpa [s₁₀] using hout_len9
  · simp only [s₁₀, State.setReg_regs_ne _ _ (by decide : (0 : Reg) ≠ 4),
      hregs9 0 (by decide) (by decide) (by decide), hr0_8]
  · simp only [s₁₀, State.setReg_regs_ne _ _ (by decide : (1 : Reg) ≠ 4),
      hregs9 1 (by decide) (by decide) (by decide),
      s₈, s₇, State.setReg_regs_ne _ _ (by decide : (1 : Reg) ≠ 9),
      State.setReg_regs_ne _ _ (by decide : (1 : Reg) ≠ 8),
      hreg6 1 (by decide) (by decide) (by decide) (by decide), hr1_5]
  · simp only [s₁₀, State.setReg_regs_ne _ _ (by decide : (2 : Reg) ≠ 4),
      hregs9 2 (by decide) (by decide) (by decide),
      s₈, s₇, State.setReg_regs_ne _ _ (by decide : (2 : Reg) ≠ 9),
      State.setReg_regs_ne _ _ (by decide : (2 : Reg) ≠ 8),
      hreg6 2 (by decide) (by decide) (by decide) (by decide),
      s₅, s₄, s₃, s₂, s₁, State.setReg_regs_nat]; split_ifs <;> omega
  · simp only [s₁₀, State.setReg_regs_ne _ _ (by decide : (3 : Reg) ≠ 4),
      hregs9 3 (by decide) (by decide) (by decide),
      s₈, s₇, State.setReg_regs_ne _ _ (by decide : (3 : Reg) ≠ 9),
      State.setReg_regs_ne _ _ (by decide : (3 : Reg) ≠ 8),
      hreg6 3 (by decide) (by decide) (by decide) (by decide),
      s₅, s₄, s₃, s₂, s₁, State.setReg_regs_nat]; split_ifs <;> omega
  · simp [s₁₀]; omega
  · simp only [s₁₀, s₈, s₇, s₅, s₄, s₃, s₂, State.setReg_regs_nat,
      hregs9 (20 + 2 * e.1) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
      hreg6 (20 + 2 * e.1) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
        (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]; split_ifs <;> omega
  · simp only [s₁₀, s₈, s₇, s₅, State.setReg_regs_nat,
      hregs9 (20 + 2 * e.1 + 1) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
      hreg6 (20 + 2 * e.1 + 1) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
        (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
      alg74LastVert, alg74TermVert_edgeEndTerm]; split_ifs <;> omega
  · intro reg h12 hne0 hne1
    dsimp [Reg] at h12 hne0 hne1
    simp only [s₁₀, s₈, s₇, s₅, s₄, s₃, s₂, s₁, State.setReg_regs_nat,
      hregs9 reg (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
      hreg6 reg (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
        (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]; split_ifs <;> omega
  · have hlt0 : 2 + 2 * e.1 < 2 + 2 * K := by have := e.2; omega
    simp only [s₁₀, State.setReg_arrs, hprefix9 (2 + 2 * e.1) hlt0, s₈, s₇, hedge0_6]
  · have hlt1 : 2 + 2 * e.1 + 1 < 2 + 2 * K := by have := e.2; omega
    simp only [s₁₀, State.setReg_arrs, hprefix9 (2 + 2 * e.1 + 1) hlt1, s₈, s₇, hedge1_6]
  · intro i hi hne0 hne1
    simp only [s₁₀, State.setReg_arrs, hprefix9 i hi, s₈, s₇, hedge_other6 i hi hne0 hne1,
      s₅, s₄, s₃, s₂, s₁]
  · intro gamma
    dsimp only [K, P, gamma₁] at hS_g1_9 hS_other9 hS_8 ⊢
    by_cases hcol : ((completeGraphEdges p)[e.1]'e.2).1 = gamma
    · rw [if_pos hcol, ← hcol]
      simpa [s₁₀] using hS_g1_9
    · rw [if_neg hcol]
      have hne : gamma ≠ ((completeGraphEdges p)[e.1]'e.2).1 := Ne.symm hcol
      simpa [s₁₀] using hS_other9 gamma hne (hS_8 gamma)
  · intro a ha
    simp [s₁₀, harrs9 a ha, s₈, s₇, harr6 a ha, s₅, s₄, s₃, s₂, s₁]

/-- Command processing all $H$-paths in a list `es : List (Fin (completeGraphEdges p).length)`. -/
def processPathsCmd (p : ℕ) : List (Fin (completeGraphEdges p).length) → Cmd
  | [] => .skip
  | e :: rest => .seq (processOnePathCmd p e) (processPathsCmd p rest)

/-- Union of `(alg74Path x e).dropLast.toFinset` over `e ∈ es.toFinset` whose first endpoint has
color `gamma`. -/
def pathBranchUnion {p r : ℕ} (x : Alg74Input p r)
    (es : List (Fin (completeGraphEdges p).length)) (gamma : Fin p) : Finset (Fin x.n) :=
  (es.toFinset.filter (fun e : Fin (completeGraphEdges p).length =>
    ((completeGraphEdges p)[e.1]'e.2).1 = gamma)).biUnion
    (fun e => (alg74Path x e).dropLast.toFinset)

@[simp]
theorem pathBranchUnion_nil {p r : ℕ} (x : Alg74Input p r) (gamma : Fin p) :
    pathBranchUnion x [] gamma = ∅ := by
  simp [pathBranchUnion]

theorem pathBranchUnion_cons {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length)
    (es : List (Fin (completeGraphEdges p).length)) (gamma : Fin p) :
    pathBranchUnion x (e :: es) gamma =
      (if ((completeGraphEdges p)[e.1]'e.2).1 = gamma then
        (alg74Path x e).dropLast.toFinset else ∅) ∪
      pathBranchUnion x es gamma := by
  ext v
  simp only [pathBranchUnion, List.toFinset_cons, Finset.filter_insert, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset]
  split_ifs with hcol
  · simp [or_and_right, exists_or]
  · simp

theorem processPathsCmd_exec {w p r : ℕ} (x : Alg74Input p r)
    (hw3 : 3 < 2 ^ w)
    (hp_w : p < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hm_w : 2 + 3 * x.G.numActivePairs < 2 ^ w)
    (hin_w : (encAlg74In x).length < 2 ^ w)
    (hout_w : 2 + 2 * (completeGraphEdges p).length + p * x.n < 2 ^ w) :
    ∀ (es : List (Fin (completeGraphEdges p).length)) (_hnd : es.Nodup)
      (pre suf : List ℕ)
      (S : Fin p → Finset (Fin x.n))
      {s : State}
      (_hin : s.arrs inArr = encAlg74In x)
      (_hsplit : encAlg74In x = pre ++ (encHPathsSlice x es ++ suf))
      (_hr0 : s.regs 0 = x.n)
      (_hr1 : s.regs 1 = x.G.numActivePairs)
      (_hr4 : s.regs 4 = pre.length)
      (_hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
      (_hS : ∀ gamma : Fin p,
        IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + gamma.1 * x.n) (S gamma)),
      let K := (completeGraphEdges p).length
      ∃ s' t,
        Exec w (processPathsCmd p es) s s' t ∧
        t ≤ (30 * x.G.numActivePairs + 23 * x.n + 65) * es.length + 1 ∧
        s'.arrs inArr = encAlg74In x ∧
        (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
        s'.regs 0 = x.n ∧
        s'.regs 1 = x.G.numActivePairs ∧
        s'.regs 2 = s.regs 2 ∧
        s'.regs 3 = s.regs 3 ∧
        (∀ e ∈ es,
          s'.regs (20 + 2 * e.1) = (alg74TermVert x (edgeStartTerm e)).1 ∧
          s'.regs (20 + 2 * e.1 + 1) = (alg74TermVert x (edgeEndTerm e)).1 ∧
          (s'.arrs outArr)[2 + 2 * e.1]? = some (alg74EdgePair x e).1.1 ∧
          (s'.arrs outArr)[2 + 2 * e.1 + 1]? = some (alg74EdgePair x e).2.1) ∧
        (∀ reg : Reg, 12 ≤ reg → (∀ e ∈ es, reg ≠ 20 + 2 * e.1 ∧ reg ≠ 20 + 2 * e.1 + 1) →
          s'.regs reg = s.regs reg) ∧
        (∀ i : ℕ, i < 2 + 2 * K → (∀ e ∈ es, i ≠ 2 + 2 * e.1 ∧ i ≠ 2 + 2 * e.1 + 1) →
          (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
        (∀ gamma : Fin p,
          IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * x.n)
            (S gamma ∪ pathBranchUnion x es gamma)) ∧
        (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a)
  | [], _, _, _, S, s, hin, _, hr0, hr1, _, hout_len, hS => by
    refine ⟨s, 1, .skip s, by omega, hin, hout_len, hr0, hr1, rfl, rfl,
      fun _ h => False.elim (List.not_mem_nil h),
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun gamma => by simpa using hS gamma,
      fun _ _ => rfl⟩
  | e :: rest, hnd, pre, suf, S, s, hin, hsplit, hr0, hr1, hr4, hout_len, hS => by
    rcases List.nodup_cons.mp hnd with ⟨he_not_mem, hnd_rest⟩
    have hsplit_e :
        encAlg74In x =
          pre ++ ((alg74Path x e).length :: (alg74Path x e).map Fin.val ++
            (encHPathsSlice x rest ++ suf)) := by
      simpa [encHPathsSlice_cons, List.append_assoc] using hsplit
    rcases processOnePathCmd_exec x e pre (encHPathsSlice x rest ++ suf) S
        hw3 hp_w hn_w hm_w hin_w hout_w hin hsplit_e hr0 hr1 hr4 hout_len hS with
      ⟨s₁, t₁, hex₁, ht₁, hin₁, hout_len1, hr0_1, hr1_1, hr2_1, hr3_1, hr4_1,
        hterm0_1, hterm1_1, hreg_other1, hedge0_1, hedge1_1, hedge_other1, hS_1, harr1⟩
    let S₁ : Fin p → Finset (Fin x.n) := fun gamma =>
      if ((completeGraphEdges p)[e.1]'e.2).1 = gamma then
        S gamma ∪ (alg74Path x e).dropLast.toFinset else S gamma
    let pre₁ := pre ++ ((alg74Path x e).length :: (alg74Path x e).map Fin.val)
    have hsplit_rest : encAlg74In x = pre₁ ++ (encHPathsSlice x rest ++ suf) := by
      simpa [pre₁, List.append_assoc] using hsplit_e
    rcases processPathsCmd_exec x hw3 hp_w hn_w hm_w hin_w hout_w rest hnd_rest
        pre₁ suf S₁ hin₁ hsplit_rest hr0_1 hr1_1 hr4_1 hout_len1 hS_1 with
      ⟨s', t₂, hex₂, ht₂, hin', hout_len', hr0', hr1', hr2', hr3',
        hdone_rest, hreg_other', hedge_other', hS', harr'⟩
    refine ⟨s', t₁ + t₂, .seq hex₁ hex₂,
      by simp only [List.length_cons, Nat.mul_succ]; omega,
      hin', hout_len', hr0', hr1', hr2'.trans hr2_1, hr3'.trans hr3_1,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with he'_eq | he'_rest
      · rw [he'_eq]
        have hne_reg : ∀ e'' ∈ rest,
            (20 + 2 * e.1 ≠ 20 + 2 * e''.1 ∧ 20 + 2 * e.1 ≠ 20 + 2 * e''.1 + 1) ∧
            (20 + 2 * e.1 + 1 ≠ 20 + 2 * e''.1 ∧ 20 + 2 * e.1 + 1 ≠ 20 + 2 * e''.1 + 1) ∧
            (2 + 2 * e.1 ≠ 2 + 2 * e''.1 ∧ 2 + 2 * e.1 ≠ 2 + 2 * e''.1 + 1) ∧
            (2 + 2 * e.1 + 1 ≠ 2 + 2 * e''.1 ∧ 2 + 2 * e.1 + 1 ≠ 2 + 2 * e''.1 + 1) := by
          intro e'' he''
          have hne_val : e.1 ≠ e''.1 := fun h => he_not_mem (Fin.ext h ▸ he'')
          refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hreg_other' (20 + 2 * e.1) (by dsimp [Reg]; omega) (fun e'' he'' => (hne_reg e'' he'').1), hterm0_1]
        · rw [hreg_other' (20 + 2 * e.1 + 1) (by dsimp [Reg]; omega) (fun e'' he'' => (hne_reg e'' he'').2.1), hterm1_1]
        · rw [hedge_other' (2 + 2 * e.1) (by have := e.2; omega)
            (fun e'' he'' => (hne_reg e'' he'').2.2.1), hedge0_1]
        · rw [hedge_other' (2 + 2 * e.1 + 1) (by have := e.2; omega)
            (fun e'' he'' => (hne_reg e'' he'').2.2.2), hedge1_1]
      · exact hdone_rest e' he'_rest
    · intro reg h12 hne_all
      have hne_e := hne_all e List.mem_cons_self
      have hne_rest : ∀ e' ∈ rest, reg ≠ 20 + 2 * e'.1 ∧ reg ≠ 20 + 2 * e'.1 + 1 :=
        fun e' he' => hne_all e' (List.mem_cons_of_mem e he')
      rw [hreg_other' reg h12 hne_rest, hreg_other1 reg h12 hne_e.1 hne_e.2]
    · intro i hi hne_all
      have hne_e := hne_all e List.mem_cons_self
      have hne_rest : ∀ e' ∈ rest, i ≠ 2 + 2 * e'.1 ∧ i ≠ 2 + 2 * e'.1 + 1 :=
        fun e' he' => hne_all e' (List.mem_cons_of_mem e he')
      rw [hedge_other' i hi hne_rest, hedge_other1 i hi hne_e.1 hne_e.2]
    · intro gamma
      have hset :
          S₁ gamma ∪ pathBranchUnion x rest gamma =
            S gamma ∪ pathBranchUnion x (e :: rest) gamma := by
        dsimp [S₁]
        rw [pathBranchUnion_cons]
        split_ifs <;> simp [Finset.union_assoc]
      rw [← hset]
      exact hS' gamma
    · intro a ha
      rw [harr' a ha, harr1 a ha]


end GraphMinor.Compute
