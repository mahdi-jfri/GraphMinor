module

public import GraphMinor.Compute.Algorithm92Search

/-!
# Graph Minors XIII, (9.2): the key of the compressed input as a list (`Algorithm92Key.lean`)

Page 101 of Graph Minors XIII: "Since the size of $F$ is bounded (exept for divalent vertices) by a
function of $l, m$, and $p$, we can find an $(l, m)$-star or a model of $K_p$ in $H \cup F$ in time
$\le C\varepsilon(G)$." The program looks up the answer for the compressed copy of `H ∪ F` in a
table. To do so it writes a list of numbers that describes the compressed input: this file defines
that list and proves that it determines the data of the compressed input.

* `compKey x segs`: the number `N` of vertices of the compressed graph, the numbers of the branch
  vertices, and then, for each path of `H ∪ F`, the separator `N` followed by the numbers of the
  vertices of the path that stand for their blobs. These are the lists that the program computes.
* `decodeK`: reads the data of an input back from such a list. Two vertices of the compressed
  graph are adjacent when they follow each other on one of the compressed paths
  (`IsPathSystem.consec_filter_of_cAdj` and `IsPathSystem.cAdj_of_consec_filter`).
* `decodeK_compKey`: the list of the compressed input decodes to the data of the compressed input.
* `tableK`: the stored answer for a list, and `isAlg92Output_tableK`: it is correct for the
  compressed input.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {n : ℕ} {S : Finset (Fin n)} {Ps : List (List (Fin n))} {G : MultiDigraph n}

/-! ### Adjacency in the compressed graph is adjacency along the compressed paths -/

section PathSystem

variable (hP : IsPathSystem G S Ps)
include hP

/-- The first vertex of `y :: Y` that stands for its blob is the vertex `cRep y` that stands for
the blob of `y`, when `y :: Y` is the end of a path of the system. -/
theorem IsPathSystem.head?_filter_isRepB {P : List (Fin n)} (hPs : P ∈ Ps) {X Y : List (Fin n)}
    {y : Fin n} (hdec : P = X ++ y :: Y) :
    ((y :: Y).filter (isRepB S Ps)).head? = some (cRep S Ps y) := by
  by_cases hy : cRep S Ps y = y
  · simp [isRepB, hy]
  have hyS : y ∉ S := fun h => hy (cRep_of_mem_S h)
  have hyP : y ∈ P := by rw [hdec]; simp
  obtain ⟨A, a, R, c, B, hdec', -, -, -, hyR, hrun⟩ := hP.exists_run hPs hyP hyS
  obtain ⟨R1, R2, rfl⟩ := List.append_of_mem hyR
  have hnd := hP.nodup P hPs
  have hY : Y = R2 ++ c :: B :=
    (nodup_split_unique hnd hdec (A' := A ++ a :: R1) (by rw [hdec']; simp)).2
  have hRne : R1 ++ y :: R2 ≠ [] := by simp
  have hrep : ∀ z ∈ R1 ++ y :: R2, cRep S Ps z = (R1 ++ y :: R2).getLast hRne := fun z hz => by
    simp only [cRep, (hrun z hz).1]
  have hR2 : R2 ≠ [] := by
    rintro rfl
    exact hy (by rw [hrep y (by simp)]; simp)
  have hlast : (R1 ++ y :: R2).getLast hRne = R2.getLast hR2 := by
    rw [List.getLast_append_of_ne_nil hRne (List.cons_ne_nil _ _), List.getLast_cons hR2]
  have hsplit : y :: Y = (y :: R2.dropLast) ++ R2.getLast hR2 :: (c :: B) := by
    rw [hY]
    conv_lhs => rw [← List.dropLast_append_getLast hR2]
    simp
  have hnd2 : ((y :: R2.dropLast) ++ [R2.getLast hR2]).Nodup := by
    have hinf : (y :: R2) <:+: P := ⟨A ++ a :: R1, c :: B, by rw [hdec']; simp⟩
    have := hnd.sublist hinf.sublist
    rwa [← List.dropLast_append_getLast hR2, ← List.cons_append] at this
  have hnot : R2.getLast hR2 ∉ y :: R2.dropLast := by
    intro hmem
    rw [List.nodup_append] at hnd2
    exact hnd2.2.2 _ hmem _ (List.mem_singleton_self _) rfl
  have hinR : ∀ z ∈ y :: R2.dropLast, z ∈ R1 ++ y :: R2 := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · simp
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.dropLast_subset _ hz))
  have hl : R2.getLast hR2 ∈ R1 ++ y :: R2 :=
    List.mem_append_right _ (List.mem_cons_of_mem _ (List.getLast_mem hR2))
  rw [hsplit, List.filter_append, List.filter_eq_nil_iff.mpr, List.nil_append,
    List.filter_cons_of_pos]
  · simp [hrep y (by simp), hlast]
  · simp [isRepB, hrep _ hl, hlast]
  · intro z hz
    have hzne : z ≠ R2.getLast hR2 := fun h => hnot (h ▸ hz)
    simp [isRepB, hrep z (hinR z hz), hlast, Ne.symm hzne]

/-- Two vertices that follow each other on a path, with different representatives: the
representatives follow each other on the compressed path. -/
theorem IsPathSystem.consec_filter_of_consec {P : List (Fin n)} (hPs : P ∈ Ps) {y z : Fin n}
    (hc : Consec P y z) (hne : cRep S Ps y ≠ cRep S Ps z) :
    Consec (P.filter (isRepB S Ps)) (cRep S Ps y) (cRep S Ps z) := by
  obtain ⟨X, Y, hdec⟩ := hc
  have hz := hP.head?_filter_isRepB hPs (X := X ++ [y]) (Y := Y) (y := z) (by rw [hdec]; simp)
  by_cases hy : cRep S Ps y = y
  · obtain ⟨Z, hZ⟩ : ∃ Z, (z :: Y).filter (isRepB S Ps) = cRep S Ps z :: Z := by
      cases h : (z :: Y).filter (isRepB S Ps) with
      | nil => rw [h] at hz; simp at hz
      | cons a Z =>
        rw [h, List.head?_cons, Option.some.injEq] at hz
        exact ⟨Z, by rw [hz]⟩
    refine ⟨X.filter (isRepB S Ps), Z, ?_⟩
    rw [hdec, List.filter_append, List.filter_cons_of_pos (by simp [isRepB, hy]), hZ, hy]
  · exfalso
    apply hne
    have hy' := hP.head?_filter_isRepB hPs (X := X) (Y := z :: Y) hdec
    rw [List.filter_cons_of_neg (by simp [isRepB, hy])] at hy'
    rw [hy'] at hz
    exact Option.some.inj hz

/-- **Adjacent vertices of the compressed graph follow each other on a compressed path.** -/
theorem IsPathSystem.consec_filter_of_cAdj {u v : Fin n} (h : CAdj S Ps u v) :
    ∃ P ∈ Ps, Consec (P.filter (isRepB S Ps)) u v ∨ Consec (P.filter (isRepB S Ps)) v u := by
  obtain ⟨huv, y, z, ⟨P, hPs, hc | hc⟩, rfl, rfl⟩ := h
  · exact ⟨P, hPs, Or.inl (hP.consec_filter_of_consec hPs hc huv)⟩
  · exact ⟨P, hPs, Or.inr (hP.consec_filter_of_consec hPs hc (Ne.symm huv))⟩

end PathSystem

/-! ### Splitting a list at separators -/

/-- Split a list at the separator `sep`: the entries before the first separator, and the blocks
that follow each copy of the separator. -/
def splitSepAux (sep : ℕ) : List ℕ → List ℕ × List (List ℕ)
  | [] => ([], [])
  | a :: l =>
    if a = sep then ([], (splitSepAux sep l).1 :: (splitSepAux sep l).2)
    else (a :: (splitSepAux sep l).1, (splitSepAux sep l).2)

/-- The blocks that follow each copy of the separator `sep`. -/
def splitSep (sep : ℕ) (l : List ℕ) : List (List ℕ) := (splitSepAux sep l).2

theorem splitSepAux_append (sep : ℕ) (L : List ℕ) :
    ∀ c : List ℕ, sep ∉ c →
      splitSepAux sep (c ++ L) = (c ++ (splitSepAux sep L).1, (splitSepAux sep L).2)
  | [], _ => by simp
  | a :: c, hc => by
    have ha : a ≠ sep := fun h => hc (h ▸ List.mem_cons_self ..)
    rw [List.cons_append, splitSepAux, if_neg ha,
      splitSepAux_append sep L c (fun h => hc (List.mem_cons_of_mem _ h))]
    simp

theorem splitSepAux_flatMap (sep : ℕ) :
    ∀ cs : List (List ℕ), (∀ c ∈ cs, sep ∉ c) → splitSepAux sep (cs.flatMap (sep :: ·)) = ([], cs)
  | [], _ => by simp [splitSepAux]
  | c :: cs, hc => by
    rw [List.flatMap_cons, List.cons_append, splitSepAux, if_pos rfl,
      splitSepAux_append sep _ c (hc c (by simp)),
      splitSepAux_flatMap sep cs (fun d hd => hc d (by simp [hd]))]
    simp

theorem splitSep_flatMap (sep : ℕ) (cs : List (List ℕ)) (hcs : ∀ c ∈ cs, sep ∉ c) :
    splitSep sep (cs.flatMap (sep :: ·)) = cs := by
  rw [splitSep, splitSepAux_flatMap sep cs hcs]

/-! ### The key list and its decoding -/

variable {h : ℕ}

open Classical in
/-- The data of an input read back from a key list `N :: bv ++ KL`: `N` vertices, the branch
vertices `bv`, and the compressed paths, each one after a separator `N` in `KL`. Two vertices are
adjacent when they follow each other on a compressed path, and the inner vertices of the `k`-th
path of the wall are the inner vertices of the `k`-th compressed path. -/
noncomputable def decodeK (h : ℕ) : List ℕ → Option (InputData h)
  | [] => none
  | N :: rest =>
    if hN : 0 < N then
      some ⟨N,
        fun i j => if i.val ≠ j.val ∧ ∃ cp ∈ splitSep N (rest.drop (elemWallNumVerts h)),
            Consec cp i.val j.val ∨ Consec cp j.val i.val then 1 else 0,
        fun u => ⟨rest.getD u.val 0 % N, Nat.mod_lt _ hN⟩,
        fun k => (((splitSep N (rest.drop (elemWallNumVerts h))).getD k.val []).tail.dropLast).map
          (fun v => ⟨v % N, Nat.mod_lt _ hN⟩)⟩
    else none

variable {l m p k r : ℕ} (x : Alg92Input l m p h k r)

/-- The key list of the compressed copy of `H ∪ F`: the number `N` of its vertices, the numbers
of the branch vertices, and for each path of `H ∪ F` the separator `N` followed by the numbers of
the vertices of the path that stand for their blobs. -/
noncomputable def compKey (segs : List (List (Fin x.n))) : List ℕ :=
  (fVerts x segs).card ::
    ((List.finRange (elemWallNumVerts h)).map (fun u => (fι x segs (x.W.branchVert u)).val) ++
      (fPaths x segs).flatMap (fun P => (fVerts x segs).card ::
        ((P.filter (isRepB (fNodes x segs) (fPaths x segs))).map (fun y => (fι x segs y).val))))

variable {x}

theorem fι_lt (segs : List (List (Fin x.n))) (y : Fin x.n) :
    (fι x segs y).val < (fVerts x segs).card := (fι x segs y).2

/-- The compressed paths: for each path of `H ∪ F`, the numbers of its vertices that stand for
their blobs. -/
noncomputable def cpsOf (segs : List (List (Fin x.n))) : List (List ℕ) :=
  (fPaths x segs).map (fun P =>
    (P.filter (isRepB (fNodes x segs) (fPaths x segs))).map (fun y => (fι x segs y).val))

theorem compKey_eq (segs : List (List (Fin x.n))) :
    compKey x segs = (fVerts x segs).card ::
      ((List.finRange (elemWallNumVerts h)).map (fun u => (fι x segs (x.W.branchVert u)).val) ++
        (cpsOf segs).flatMap ((fVerts x segs).card :: ·)) := by
  unfold compKey cpsOf
  rw [List.flatMap_map]

theorem splitSep_cpsOf (segs : List (List (Fin x.n))) :
    splitSep (fVerts x segs).card ((cpsOf segs).flatMap ((fVerts x segs).card :: ·)) =
      cpsOf segs := by
  refine splitSep_flatMap _ _ fun c hc hNc => ?_
  unfold cpsOf at hc
  rw [List.mem_map] at hc
  obtain ⟨P, -, rfl⟩ := hc
  rw [List.mem_map] at hNc
  obtain ⟨y, -, hy⟩ := hNc
  have := fι_lt segs y
  omega

theorem mem_cpsOf {segs : List (List (Fin x.n))} {cp : List ℕ} (hcp : cp ∈ cpsOf segs) :
    ∃ P ∈ fPaths x segs, cp = (P.filter (isRepB (fNodes x segs) (fPaths x segs))).map
      (fun y => (fι x segs y).val) := by
  unfold cpsOf at hcp
  rw [List.mem_map] at hcp
  obtain ⟨P, hP, rfl⟩ := hcp
  exact ⟨P, hP, rfl⟩

section FSystem

variable {segs : List (List (Fin x.n))} {paths : Fin k → List (Fin x.n)}
  (hF : IsFSystem x segs paths)
include hF

/-- Adjacency in the compressed graph, read on the compressed paths. -/
theorem IsFSystem.cAdj_iff (i j : Fin (fVerts x segs).card) :
    CAdj (fNodes x segs) (fPaths x segs) (fE x segs i) (fE x segs j) ↔
      (i.val ≠ j.val ∧ ∃ cp ∈ cpsOf segs, Consec cp i.val j.val ∨ Consec cp j.val i.val) := by
  have hC := hF.isCompression
  have hP := hF.isPathSystem
  constructor
  · intro hca
    refine ⟨fun hij => hca.1 (by rw [Fin.ext hij]), ?_⟩
    obtain ⟨P, hPs, hc⟩ := hP.consec_filter_of_cAdj hca
    have hmem : (P.filter (isRepB (fNodes x segs) (fPaths x segs))).map
        (fun y => (fι x segs y).val) ∈ cpsOf segs := by
      unfold cpsOf
      exact List.mem_map_of_mem hPs
    refine ⟨_, hmem, ?_⟩
    have e1 : (fι x segs (fE x segs i)).val = i.val := by rw [hC.ι_e]
    have e2 : (fι x segs (fE x segs j)).val = j.val := by rw [hC.ι_e]
    rcases hc with hc | hc
    · have := hc.map (fun y => (fι x segs y).val)
      rw [e1, e2] at this
      exact Or.inl this
    · have := hc.map (fun y => (fι x segs y).val)
      rw [e1, e2] at this
      exact Or.inr this
  · rintro ⟨-, cp, hcp, hc⟩
    obtain ⟨P, hPs, rfl⟩ := mem_cpsOf hcp
    have key : ∀ a b : Fin (fVerts x segs).card,
        Consec ((P.filter (isRepB (fNodes x segs) (fPaths x segs))).map
          (fun y => (fι x segs y).val)) a.val b.val →
        CAdj (fNodes x segs) (fPaths x segs) (fE x segs a) (fE x segs b) := by
      intro a b hab
      obtain ⟨y, z, hyz, hya, hzb⟩ := exists_of_consec_map hab
      have hmem : ∀ t ∈ P.filter (isRepB (fNodes x segs) (fPaths x segs)),
          t ∈ fVerts x segs := by
        intro t ht
        rw [List.mem_filter] at ht
        exact mem_cVerts_iff.mpr (Or.inr ⟨⟨P, hPs, ht.1⟩, by simpa [isRepB] using ht.2⟩)
      have hya' : fE x segs a = y := by
        rw [← hC.e_ι y (hmem y hyz.mem_left)]
        congr 1
        exact Fin.ext hya.symm
      have hzb' : fE x segs b = z := by
        rw [← hC.e_ι z (hmem z hyz.mem_right)]
        congr 1
        exact Fin.ext hzb.symm
      rw [hya', hzb']
      exact hP.cAdj_of_consec_filter hPs hyz
    rcases hc with hc | hc
    · exact key i j hc
    · exact (key j i hc).symm

omit hF in
/-- The `k`-th compressed path is the compressed `k`-th path of the wall. -/
theorem getD_cpsOf (k' : Fin (elemWallEdges h).length) :
    (cpsOf segs).getD k'.val [] = ((x.W.subdivPathVerts k').filter
      (isRepB (fNodes x segs) (fPaths x segs))).map (fun y => (fι x segs y).val) := by
  unfold cpsOf
  rw [fPaths, List.map_append, List.getD_append _ _ _ _ (by simp)]
  simp

omit hF in
/-- The inner vertices of the paths of the compressed wall, read on the compressed paths. -/
theorem wall_cpsOf (k' : Fin (elemWallEdges h).length) (hN : 0 < (fVerts x segs).card) :
    (((cpsOf segs).getD k'.val []).tail.dropLast).map
        (fun v => (⟨v % (fVerts x segs).card, Nat.mod_lt _ hN⟩ : Fin (fVerts x segs).card)) =
      ((x.W.internalVerts k').filter (isRepB (fNodes x segs) (fPaths x segs))).map
        (fι x segs) := by
  have hrepS : ∀ y ∈ fNodes x segs, isRepB (fNodes x segs) (fPaths x segs) y = true := by
    intro y hy
    simp [isRepB, cRep_of_mem_S hy]
  rw [getD_cpsOf, subdivPathVerts]
  rw [List.filter_append, List.filter_append,
    List.filter_cons_of_pos (hrepS _ (branchVert_mem_fNodes segs _)),
    List.filter_cons_of_pos (hrepS _ (branchVert_mem_fNodes segs _))]
  simp only [List.filter_nil, List.map_append, List.map_cons, List.map_nil,
    List.singleton_append, List.cons_append, List.tail_cons, List.dropLast_concat, List.map_map]
  refine List.map_congr_left fun y _ => Fin.ext ?_
  simp [Nat.mod_eq_of_lt (fι_lt segs y)]

theorem keyData_compressInput :
    keyData (compressInput hF) = ⟨(fVerts x segs).card,
      (cGraph (fNodes x segs) (fPaths x segs) (fE x segs)).edgeMult,
      (cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) x.W).branchVert,
      (cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) x.W).internalVerts⟩ :=
  rfl

/-- **The key list decodes to the data of the compressed input.** -/
theorem decodeK_compKey :
    decodeK h (compKey x segs) = some (keyData (compressInput hF)) := by
  have hN : 0 < (fVerts x segs).card := fVerts_card_pos segs
  have hlen : ((List.finRange (elemWallNumVerts h)).map
      (fun u => (fι x segs (x.W.branchVert u)).val)).length = elemWallNumVerts h := by simp
  rw [keyData_compressInput hF, compKey_eq, decodeK, dif_pos hN, List.drop_left' hlen,
    splitSep_cpsOf]
  congr 1
  refine Sigma.ext rfl (heq_of_eq ?_)
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i j
    simp only [cGraph]
    have hc := hF.cAdj_iff i j
    by_cases hc' : CAdj (fNodes x segs) (fPaths x segs) (fE x segs i) (fE x segs j)
    · rw [if_pos hc', if_pos (hc.mp hc')]
    · have hn : ¬ (i.val ≠ j.val ∧ ∃ cp ∈ cpsOf segs,
          Consec cp i.val j.val ∨ Consec cp j.val i.val) := fun h => hc' (hc.mpr h)
      rw [if_neg hc', if_neg hn]
  · funext u
    refine Fin.ext ?_
    dsimp only
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [cWall, Nat.mod_eq_of_lt (fι_lt segs _)]
  · funext k'
    dsimp only
    rw [wall_cpsOf k' hN]
    rfl

end FSystem

/-! ### The table -/

open Classical in
/-- The stored answer for the data `D` of an input: a correct output of an input with these data,
if there is one. -/
noncomputable def tableD (l m p k r : ℕ) (D : InputData h) : List ℕ :=
  if hD : ∃ x : Alg92Input l m p h k r, keyData x = D then
    if hout : ∃ out, IsAlg92Output l m p hD.choose out then hout.choose else []
  else []

/-- **The stored answer is correct**, when every input has a correct output. -/
theorem isAlg92Output_tableD
    (hex : ∀ x : Alg92Input l m p h k r, ∃ out, IsAlg92Output l m p x out)
    (D : InputData h) (x : Alg92Input l m p h k r) (hx : keyData x = D) :
    IsAlg92Output l m p x (tableD l m p k r D) := by
  have hD : ∃ x : Alg92Input l m p h k r, keyData x = D := ⟨x, hx⟩
  have hout := hex hD.choose
  unfold tableD
  rw [dite_eq_left_of_eq_true (eq_true hD), dite_eq_left_of_eq_true (eq_true hout)]
  have hc := hout.choose_spec
  rw [isAlg92Output_iff_isDataOutput] at hc ⊢
  have e : keyData hD.choose = keyData x := hD.choose_spec.trans hx.symm
  rw [← e]
  exact hc

/-- The stored answer for a key list. -/
noncomputable def tableK (h l m p k r : ℕ) (κ : List ℕ) : List ℕ :=
  match decodeK h κ with
  | some D => tableD (h := h) l m p k r D
  | none => []

/-- **The stored answer for the key list of the compressed input is correct for it.** -/
theorem isAlg92Output_tableK
    (hex : ∀ y : Alg92Input l m p h k r, ∃ out, IsAlg92Output l m p y out)
    {segs : List (List (Fin x.n))} {paths : Fin k → List (Fin x.n)}
    (hF : IsFSystem x segs paths) :
    IsAlg92Output l m p (compressInput hF) (tableK h l m p k r (compKey x segs)) := by
  unfold tableK
  rw [decodeK_compKey hF]
  exact isAlg92Output_tableD hex _ _ rfl

end Alg92

end GraphMinor.Compute
