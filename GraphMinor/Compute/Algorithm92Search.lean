module

public import GraphMinor.Compute.Algorithm92Input
public import GraphMinor.Compute.Algorithm92Table

/-!
# Graph Minors XIII, (9.2): the search in `H ∪ F` by a table (`Algorithm92Search.lean`)

Page 101 of Graph Minors XIII: "Since the size of $F$ is bounded (exept for divalent vertices) by a
function of $l, m$, and $p$, we can find an $(l, m)$-star or a model of $K_p$ in $H \cup F$ in time
$\le C\varepsilon(G)$."

* `card_cVerts_le`: a compressed path system has at most `|S| + |Ps| · |S|` vertices, since every
  vertex that is not a node is the vertex just before a node on one of the paths.
* `card_fVerts_le`: so the compressed copy of `H ∪ F` has at most `bound92 h s` vertices when `F`
  has at most `s` paths. This bound depends only on `h` and `s`.
* `isAlg92Output_table92_compressInput`: the stored answer for the key of the compressed input is
  correct for it, and so (by `exists_isAlg92Output_of_isFSystem`) gives a correct answer for the
  input.
-/

public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {n : ℕ} {S : Finset (Fin n)} {Ps : List (List (Fin n))} {G : MultiDigraph n}

/-- The vertex just before `c` on the list `P` (or `c` itself if there is none). -/
def predOf (P : List (Fin n)) (c : Fin n) : Fin n :=
  ((P.take (P.idxOf c)).getLast?).getD c

theorem predOf_of_consec {P : List (Fin n)} (hP : P.Nodup) {v c : Fin n} (h : Consec P v c) :
    predOf P c = v := by
  obtain ⟨A, B, rfl⟩ := h
  have hc : c ∉ A ++ [v] := by
    intro hc
    have hP' : ((A ++ [v]) ++ c :: B).Nodup := by simpa using hP
    rw [List.nodup_append] at hP'
    exact hP'.2.2 c hc c List.mem_cons_self rfl
  have hidx : (A ++ v :: c :: B).idxOf c = (A ++ [v]).length := by
    rw [show A ++ v :: c :: B = (A ++ [v]) ++ c :: B by simp,
      List.idxOf_append_of_notMem hc]
    simp
  unfold predOf
  rw [hidx, show A ++ v :: c :: B = (A ++ [v]) ++ c :: B by simp, List.take_left]
  simp

/-- **The size of a compressed path system.** -/
theorem IsPathSystem.card_cVerts_le (hP : IsPathSystem G S Ps) :
    (cVerts S Ps).card ≤ S.card + Ps.length * S.card := by
  classical
  have hsub : cVerts S Ps ⊆ S ∪ (Ps.toFinset ×ˢ S).image (fun q => predOf q.1 q.2) := by
    intro v hv
    rw [Finset.mem_union]
    by_cases hvS : v ∈ S
    · exact Or.inl hvS
    · right
      obtain ⟨⟨P, hPs, hvP⟩, hvr⟩ := (mem_cVerts_iff.mp hv).resolve_left hvS
      obtain ⟨A, a, R, c, B, hdec, -, hc, -, hvR, hrun⟩ := hP.exists_run hPs hvP hvS
      have hRne : R ≠ [] := List.ne_nil_of_mem hvR
      have hlast : R.getLast hRne = v := by
        rw [← hvr]; simp only [cRep, (hrun v hvR).1]
      have hcon : Consec P v c := by
        refine ⟨A ++ a :: R.dropLast, B, ?_⟩
        rw [hdec, ← hlast]
        conv_lhs => rw [← List.dropLast_append_getLast hRne]
        simp
      rw [Finset.mem_image]
      exact ⟨(P, c), Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hPs, hc⟩,
        predOf_of_consec (hP.nodup P hPs) hcon⟩
  calc (cVerts S Ps).card
      ≤ (S ∪ (Ps.toFinset ×ˢ S).image (fun q => predOf q.1 q.2)).card := Finset.card_le_card hsub
    _ ≤ S.card + ((Ps.toFinset ×ˢ S).image (fun q => predOf q.1 q.2)).card :=
        Finset.card_union_le _ _
    _ ≤ S.card + (Ps.toFinset ×ˢ S).card := by
        have := Finset.card_image_le (s := Ps.toFinset ×ˢ S) (f := fun q => predOf q.1 q.2)
        omega
    _ ≤ S.card + Ps.length * S.card := by
        rw [Finset.card_product]
        have := List.toFinset_card_le Ps
        have := Nat.mul_le_mul_right S.card this
        omega

/-- The bound on the number of vertices of the compressed copy of `H ∪ F` when `F` has at most `s`
paths. -/
@[expose] def bound92 (h s : ℕ) : ℕ :=
  (elemWallNumVerts h + 2 * s) + ((elemWallEdges h).length + s) * (elemWallNumVerts h + 2 * s)

variable {l m p h k r : ℕ} {x : Alg92Input l m p h k r}

theorem card_fNodes_le (segs : List (List (Fin x.n))) :
    (fNodes x segs).card ≤ elemWallNumVerts h + 2 * segs.length := by
  unfold fNodes
  have h1 := Finset.card_union_le (Finset.univ.image x.W.branchVert)
    (segs.flatMap (fun P => P.head?.toList ++ P.getLast?.toList)).toFinset
  have h2 : (Finset.univ.image x.W.branchVert).card ≤ elemWallNumVerts h := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin (elemWallNumVerts h))))
      (f := x.W.branchVert)
    simpa using this
  have h3 : (segs.flatMap (fun P => P.head?.toList ++ P.getLast?.toList)).toFinset.card ≤
      2 * segs.length := by
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_flatMap]
    have : ∀ P ∈ segs, (P.head?.toList ++ P.getLast?.toList).length ≤ 2 := by
      intro P _
      cases P.head? <;> cases P.getLast? <;> simp
    have := List.sum_le_length_nsmul (segs.map fun P => (P.head?.toList ++ P.getLast?.toList).length)
      2 (by simpa using this)
    simpa [mul_comm] using this
  omega

theorem card_fVerts_le {segs : List (List (Fin x.n))} {paths : Fin k → List (Fin x.n)}
    (hF : IsFSystem x segs paths) {s : ℕ} (hs : segs.length ≤ s) :
    (fVerts x segs).card ≤ bound92 h s := by
  have h1 := hF.isPathSystem.card_cVerts_le
  have h2 := card_fNodes_le (x := x) segs
  have h3 : (fPaths x segs).length = (elemWallEdges h).length + segs.length := by
    simp [fPaths]
  rw [h3] at h1
  unfold bound92
  have h4 : (fNodes x segs).card ≤ elemWallNumVerts h + 2 * s := by omega
  have h5 : (elemWallEdges h).length + segs.length ≤ (elemWallEdges h).length + s := by omega
  exact h1.trans (Nat.add_le_add h4 (Nat.mul_le_mul h5 h4))

theorem cGraph_edgeMult_le_one {N : ℕ} (e : Fin N → Fin n) (i j : Fin N) :
    (cGraph S Ps e).edgeMult i j ≤ 1 := by
  classical
  show (if CAdj S Ps (e i) (e j) then 1 else 0) ≤ 1
  split <;> simp

theorem length_internalVerts_le_of_isValid {n' : ℕ} {G' : MultiDigraph n'} {W : WallOfHeight h G'}
    (hW : W.IsValid) (k : Fin (elemWallEdges h).length) : (W.internalVerts k).length ≤ n' := by
  have hnd : (W.internalVerts k).Nodup := by
    have := (hW.2.1 k).1
    unfold subdivPathVerts at this
    exact (this.sublist (List.sublist_append_left _ _)).sublist (List.sublist_append_right _ _)
  simpa using hnd.length_le_card

/-- The key of the compressed input, when it has at most `B` vertices. -/
noncomputable def compressKey {segs : List (List (Fin x.n))} {paths : Fin k → List (Fin x.n)}
    (hF : IsFSystem x segs paths) {B : ℕ} (hB : (fVerts x segs).card ≤ B) : Key92 h B :=
  key92Of B (compressInput hF) hB
    (length_internalVerts_le_of_isValid (compressInput hF).hW_valid.2.2)

/-- **The search in `H ∪ F` by a table.** If every input of (9.2) has a correct output, then the
stored answer for the key of the compressed input is correct for the compressed input. -/
theorem isAlg92Output_table92_compressInput
    (hex : ∀ y : Alg92Input l m p h k r, ∃ out, IsAlg92Output l m p y out)
    {segs : List (List (Fin x.n))} {paths : Fin k → List (Fin x.n)}
    (hF : IsFSystem x segs paths) {B : ℕ} (hB : (fVerts x segs).card ≤ B) :
    IsAlg92Output l m p (compressInput hF) (table92 l m p k r (compressKey hF hB)) :=
  isAlg92Output_table92 hex _ _
    (ofKey92_key92Of B (compressInput hF) hB _ (fun i j => cGraph_edgeMult_le_one _ i j)).symm

end Alg92

end GraphMinor.Compute
