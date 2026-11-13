module

public import GraphMinor.Compute.Algorithm101Loop
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Complete Word RAM Implementation of Graph Minors XIII, Algorithm (10.1)

This file assembles the pre-pass, vision buffer initialization, and member iteration loop into the
complete Word RAM program `alg101Prog` for **Graph Minors XIII, Algorithm (10.1)**
(N. Robertson and P. D. Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), pages 106–107):

1. **Section 1 (`ParsedCase3Block` Word Bounds, Stream Length Bounds, and Work-Size Sums):**
   Establishes word-size bounds for all fields of a valid `ParsedCase3Block`, linear bounds on the
   serialized member stream length and `buildVertOwnerProg` cost under `IsSocietyDivision`, and the
   quadratic bound $\sum_j (\text{memberWorkSize}_j)^2 \le ((q + 10)(n + m + 1))^2$.
2. **Section 2 (`alg101PrePassPart1Prog`, `alg101PrePassPart2Prog`, `alg101PrePassProg`):**
   Computes $(n, m)$, extracts `xSeqOf X'`, parses Section 1 (`W.encList`) into `a101_W_br`,
   `a101_W_brOf`, `a101_W_edgeOf`, builds `a101_perim` and `a101_WH`, reads Section 2 (`K_vList`,
   `K_eList`, `corners`, `M`), builds the compass CSR graph `G_K` and lookup tables `a101_KInd`,
   `a101_isCorner`, `a101_degK`, and runs the pre-pass `buildVertOwnerProg` to populate
   `a101_owner`.
3. **Section 3 (`alg101InitVisProg`, `alg101MemberLoop_aux`):**
   Allocates `a101_visBuf` and summary tables `a101_memIsInt`, `a101_memVOf`, `a101_memFolioCode`,
   writes the vision header `(xSeqOf X').length :: xSeqOf X' ++ [M]`, and runs
   `forUp r101_j (.reg r101_M) (alg101MemberStepProg p q δ prog41)` over all $M$ members.
4. **Section 4 (`alg101Prog`, `alg101Prog_exec`):**
   Proves that `alg101Prog` produces a valid serialized vision `vOut : ParsedVisionOutput G X' blk q δ`
   in `a101_visBuf p` together with wall and member summary tables in $O((n + m + 1)^2)$ steps.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-! ### Section 1: Block Word Bounds, Stream Length Bounds, and Work-Size Sum Bounds -/

theorem ParsedCase3Block.wall_h_le_n {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block D_del X') :
    blk.wallSec.h ≤ n := by
  have h1 := blk.wallSec.W.elemWallNumVerts_le_card_vertexFinset blk.wallSec.hW
  have h2 := blk.wallSec.W.card_vertexFinset_le
  have h3 := elemWallNumVerts_eq blk.wallSec.h
  have h4 := blk.wallSec.h2
  have h5 : (blk.wallSec.h + 1) * (2 * blk.wallSec.h + 2) =
      2 * blk.wallSec.h * blk.wallSec.h + 4 * blk.wallSec.h + 2 := by ring
  omega

theorem ParsedCase3Block.K_vList_lt_n {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X') :
    ∀ x ∈ blk.K_vList, x < n := fun x hx =>
  ((mem_vertexSet_delGraph_iff G X' x).mp (blk.K_vList_mem_delGraph hx)).1

theorem ParsedCase3Block.corners_length {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block D_del X') :
    blk.corners.length = 4 := by
  rw [blk.hcorners_eq, List.length_ofFn]

theorem ParsedCase3Block.corners_lt_n {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block D_del X') :
    ∀ x ∈ blk.corners, x < n := by
  intro x hx
  rw [blk.hcorners_eq] at hx
  rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
  exact (blk.wallSec.W.branchVert (elemWallCornerIdx blk.wallSec.h2 i)).2

theorem ParsedCase3Block.K_eList_endpoints_lt {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X') :
    ∀ t ∈ blk.K_eList, t.1 < n ∧ t.2.1 < n := by
  intro t ht
  rcases blk.hK_e_valid t ht with ⟨_, ht1, ht2⟩
  exact ⟨blk.K_vList_lt_n t.1 ht1, blk.K_vList_lt_n t.2.1 ht2⟩

theorem ParsedCase3Block.encEdgeTriples_K_eList_lt {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X') :
    ∀ x ∈ encEdgeTriples blk.K_eList, x < n + G.numEdges + 1 := by
  intro x hx
  rcases (mem_encEdgeTriples_iff blk.K_eList x).mp hx with ⟨e, he, rfl | rfl | rfl⟩
  · have hlt := (blk.K_eList_endpoints_lt e he).1; omega
  · have hlt := (blk.K_eList_endpoints_lt e he).2; omega
  · have he_del := (blk.K_eList_mem_delGraph he).1
    rw [delGraph_eq] at he_del
    rcases he_del.1 with ⟨hu, hv, hk⟩
    have hm_le := G.edgeMult_le_numEdges ⟨e.1, hu⟩ ⟨e.2.1, hv⟩
    omega

theorem ParsedCase3Block.member_enc_le {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X') :
    ∀ r ∈ blk.members, ∀ x ∈ r.enc, x ≤ 2 * (n + G.numEdges + 1) := by
  intro r hr x hx
  have hr_val := blk.member_valid_iff hr
  have hv_len : r.vList.length ≤ n := hr_val.1
  have hdel_le : (G.deleteVertices X').numEdges ≤ G.numEdges := G.numEdges_deleteVertices_le X'
  have he_len : r.eList.length ≤ G.numEdges := le_trans hr_val.2.2.2.1 hdel_le
  have ht_le : r.t_len ≤ 2 * G.numEdges + 1 := by have := hr_val.2.2.2.2.2.2.2.1; omega
  unfold Case3MemberRecord.enc at hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with (((rfl | hxv) | (rfl | hxe)) | ((rfl | hxp) | hxt))
  · omega
  · have hlt := blk.member_vList_lt hr hxv; omega
  · omega
  · have hlt := blk.encEdgeTriples_K_eList_lt x ?_
    · omega
    · rcases (mem_encEdgeTriples_iff r.eList x).mp hxe with ⟨e, he, hex⟩
      exact (mem_encEdgeTriples_iff blk.K_eList x).mpr ⟨e, (hr_val.2.2.2.2.2.1 e he).1, hex⟩
  · omega
  · have hlt := blk.member_parList_lt hr hxp; omega
  · have hlt := hr_val.2.2.2.2.2.2.2.2.2.2.2 x hxt; omega

private theorem sum_map_le_sum_map {α : Type*} (l : List α) (f g : α → ℕ)
    (hfg : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hfg a List.mem_cons_self)
      (ih (fun x hx => hfg x (List.mem_cons_of_mem a hx)))

private theorem sum_map_add {α : Type*} (l : List α) (f g : α → ℕ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem sum_map_mul_left {α : Type*} (l : List α) (c : ℕ) (f : α → ℕ) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

private theorem sum_map_const {α : Type*} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = c * l.length := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

theorem ParsedCase3Block.sum_t_len_le {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X') :
    (blk.members.map Case3MemberRecord.t_len).sum ≤ 2 * G.numEdges + blk.members.length := by
  have hle : (blk.members.map Case3MemberRecord.t_len).sum ≤
      (blk.members.map (fun r => 2 * r.eList.length + 1)).sum := by
    apply sum_map_le_sum_map
    intro r hr
    exact (blk.member_valid_iff hr).2.2.2.2.2.2.2.1
  rw [sum_map_add, sum_map_mul_left, sum_map_const] at hle
  have he_sum : (blk.members.map (fun r => r.eList.length)).sum ≤ G.numEdges :=
    le_trans blk.hmembers_edge_sum (G.numEdges_deleteVertices_le X')
  omega

theorem ParsedCase3Block.length_flatMap_member_enc_le {n : ℕ} {G : MultiDigraph n}
    {X' : Finset (Fin n)} (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hDiv : GM13.IsSocietyDivision blk.toSociety blk.toDivision) :
    (blk.members.flatMap Case3MemberRecord.enc).length ≤ 14 * (n + G.numEdges + 1) := by
  rw [List.length_flatMap]
  have hlen_eq :
      (blk.members.map (fun r => r.enc.length)).sum =
        (blk.members.map (fun r => (r.vList.length + 4 * r.eList.length) + (r.t_len + 3))).sum := by
    congr 1
    apply List.map_congr_left
    intro r hr
    have hr_val := blk.member_valid_iff hr
    have hpar_len := hr_val.2.2.2.2.2.2.2.2.1
    have htau_len := hr_val.2.2.2.2.2.2.2.2.2.2.1
    unfold Case3MemberRecord.enc
    simp only [List.length_append, List.length_cons, length_encEdgeTriples,
      hpar_len, htau_len]
    omega
  rw [hlen_eq, sum_map_add, sum_map_add, sum_map_mul_left, sum_map_add, sum_map_const]
  have hv_sum := blk.sum_vList_length_le hDiv
  have he_sum : (blk.members.map (fun r => r.eList.length)).sum ≤ G.numEdges :=
    le_trans blk.hmembers_edge_sum (G.numEdges_deleteVertices_le X')
  have ht_sum := blk.sum_t_len_le
  have hm_len : blk.members.length ≤ n + G.numEdges + 1 := by
    have h1 := blk.hmembers_len; have h2 := G.numEdges_deleteVertices_le X'; omega
  omega

theorem ParsedCase3Block.buildVertOwner_sum_le {n : ℕ} {G : MultiDigraph n}
    {X' : Finset (Fin n)} (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hDiv : GM13.IsSocietyDivision blk.toSociety blk.toDivision) :
    (blk.members.map (fun r => 40 * r.vList.length + 67 * r.eList.length + 18 * r.t_len + 105)).sum ≤
      400 * (n + G.numEdges + 1) := by
  have heq :
      (blk.members.map (fun r => 40 * r.vList.length + 67 * r.eList.length + 18 * r.t_len + 105)).sum =
        (blk.members.map (fun r => (40 * r.vList.length + 67 * r.eList.length) + (18 * r.t_len + 105))).sum := by
    apply congrArg List.sum; apply List.map_congr_left; intro r _; omega
  rw [heq, sum_map_add, sum_map_add, sum_map_mul_left, sum_map_mul_left,
    sum_map_add, sum_map_mul_left, sum_map_const]
  have hv_sum := blk.sum_vList_length_le hDiv
  have he_sum : (blk.members.map (fun r => r.eList.length)).sum ≤ G.numEdges :=
    le_trans blk.hmembers_edge_sum (G.numEdges_deleteVertices_le X')
  have ht_sum := blk.sum_t_len_le
  have hm_len : blk.members.length ≤ n + G.numEdges + 1 := by
    have h1 := blk.hmembers_len; have h2 := G.numEdges_deleteVertices_le X'; omega
  omega

theorem sum_sq_le_sq_sum : ∀ (l : List ℕ), (l.map (fun x => x ^ 2)).sum ≤ l.sum ^ 2
  | [] => by simp
  | a :: tl => by
    simp only [List.map_cons, List.sum_cons]
    have ih := sum_sq_le_sq_sum tl
    have hsq : (a + tl.sum) ^ 2 = a ^ 2 + tl.sum ^ 2 + 2 * a * tl.sum := by ring
    omega

private theorem map_finRange_getElem {α β : Type*} (l : List α) (f : α → β) :
    (List.finRange l.length).map (fun j => f (l[j.1]'j.2)) = l.map f := by
  apply List.ext_getElem (by simp); intro i hi₁ hi₂; simp

theorem sum_memberWorkSize_le {n q : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety)
    (hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision)
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val) :
    ((List.finRange blk.members.length).map (memberWorkSize G blk q xSeq)).sum ≤
      (q + 10) * (n + G.numEdges + 1) := by
  have heq :
      ((List.finRange blk.members.length).map (memberWorkSize G blk q xSeq)).sum =
        ((List.finRange blk.members.length).map (fun j =>
          ((q + 4) + (blk.members[j.1]'j.2).vList.length) +
          (memberTildeAEList G blk xSeq j).length)).sum := by
    apply congrArg List.sum; apply List.map_congr_left; intro j _; unfold memberWorkSize; omega
  have htilde_sum :
      ((List.finRange blk.members.length).map (fun j => (memberTildeAEList G blk xSeq j).length)).sum =
        (((List.finRange blk.members.length).map (memberTildeAEList G blk xSeq)).flatten).length := by
    rw [List.length_flatten, List.map_map]; rfl
  rw [heq, sum_map_add, sum_map_add (f := fun _ => q + 4), sum_map_const, List.length_finRange,
    map_finRange_getElem blk.members (fun r => r.vList.length), htilde_sum]
  have hv_sum := blk.sum_vList_length_le hRD.1
  have he_tilde_sum := length_flatten_memberTildeAEList_le_numEdges G blk hWS hRD hx_set
  have hm_len : blk.members.length ≤ n + G.numEdges + 1 := by
    have h1 := blk.hmembers_len; have h2 := G.numEdges_deleteVertices_le X'; omega
  have hq_mul : (q + 4) * blk.members.length ≤ (q + 4) * (n + G.numEdges + 1) :=
    Nat.mul_le_mul_left (q + 4) hm_len
  have hq10 : (q + 10) * (n + G.numEdges + 1) =
      (q + 4) * (n + G.numEdges + 1) + 6 * (n + G.numEdges + 1) := by ring
  omega

theorem sum_memberWorkSize_sq_le {n q : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety)
    (hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision)
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val) :
    ((List.finRange blk.members.length).map (fun j => (memberWorkSize G blk q xSeq j) ^ 2)).sum ≤
      ((q + 10) * (n + G.numEdges + 1)) ^ 2 := by
  have hmap :
      (List.finRange blk.members.length).map (fun j => (memberWorkSize G blk q xSeq j) ^ 2) =
        ((List.finRange blk.members.length).map (memberWorkSize G blk q xSeq)).map (fun x => x ^ 2) := by
    rw [List.map_map]; rfl
  have h1 :
      ((List.finRange blk.members.length).map (fun j => (memberWorkSize G blk q xSeq j) ^ 2)).sum ≤
        (((List.finRange blk.members.length).map (memberWorkSize G blk q xSeq)).sum) ^ 2 := by
    rw [hmap]
    exact sum_sq_le_sq_sum _
  have h2 := sum_memberWorkSize_le (q := q) G blk hWS hRD hx_set
  exact le_trans h1 (Nat.pow_le_pow_left h2 2)

/-! ### Section 2: Pre-Pass (`alg101PrePassPart1Prog`, `alg101PrePassPart2Prog`, `alg101PrePassProg`) -/

/-- Part 1 of the Algorithm (10.1) pre-pass:
1. Computes `n` (`r101_n`) and `m = G.numEdges` (`r101_m`).
2. Builds `xSeqOf X'` (`a101_xSeq`, length in `r101_xLen`) and `a101_xInd`.
3. Reads Section 1 (`W.encList`) of the Case (iii) block into `a101_W_br`, `a101_W_brOf`,
   `a101_W_edgeOf`, advancing `r101_off`.
4. Builds `a101_perim = bitSetList W.perimFinset` and `a101_WH = bitSetList W.vertexFinset`. -/
def alg101PrePassPart1Prog (p h : ℕ) : Cmd :=
  .seq (sumEdgeMultProg (a101_G p) r101_n)
    (.seq (.assign r101_m (.reg r101_xLen))
      (.seq (buildXSeqProg (a101_X p) (a101_buf p) (a101_xSeq p) r101_n r101_xLen r101_base)
        (.seq (buildListIndProg (a101_xSeq p) (a101_xInd p) r101_xLen r101_n r101_base)
          (.seq (.assign r101_off (.const 0))
            (.seq (readWallSectionProg (a101_block p)
              (a101_W_br p) (a101_W_brOf p) (a101_W_edgeOf p)
              r101_off r101_n 64 65 66 r101_base)
              (.seq (buildWallSubsetBitSetProg (isPerimBr h) (isElemWallPerimEdge h)
                (a101_W_brOf p) (a101_W_edgeOf p) (a101_Q0 p) (a101_Q1 p) (a101_perim p)
                r101_n r101_base)
                (@buildWallSubsetBitSetProg h (fun _ => true) (fun _ => true)
                  (a101_W_brOf p) (a101_W_edgeOf p) (a101_Q0 p) (a101_Q1 p) (a101_WH p)
                  r101_n r101_base)))))))

theorem alg101PrePassPart1Prog_exec {w n p : ℕ}
    (G : MultiDigraph n) (X' : Finset (Fin n))
    (blk : ParsedCase3Block (G.deleteVertices X') X') (rem : List ℕ)
    (hw3 : 3 < 2 ^ w) (h2n_w : 2 * n + 4 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w)
    (hwall_len_w : blk.wallSec.W.encList.length < 2 ^ w)
    {s : State}
    (hG : s.arrs (a101_G p) = G.enc)
    (hX : s.arrs (a101_X p) = bitSetList X')
    (hblock : s.arrs (a101_block p) = blk.wallSec.W.encList ++ rem) :
    ∃ s' t,
      Exec w (alg101PrePassPart1Prog p blk.wallSec.h) s s' t ∧
      t ≤ 22 * G.numActivePairs + 150 * n + 55 * blk.wallSec.W.encList.length + 180 ∧
      s'.regs r101_n = n ∧
      s'.regs r101_m = G.numEdges ∧
      s'.regs r101_xLen = (xSeqOf X').length ∧
      s'.regs r101_off = blk.wallSec.W.encList.length ∧
      s'.arrs (a101_G p) = G.enc ∧
      s'.arrs (a101_X p) = bitSetList X' ∧
      s'.arrs (a101_xSeq p) = xSeqOf X' ∧
      s'.arrs (a101_xInd p) =
        bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeqOf X')) ∧
      s'.arrs (a101_W_br p) =
        (List.finRange (elemWallNumVerts blk.wallSec.h)).map
          (fun u => (blk.wallSec.W.branchVert u).1) ∧
      s'.arrs (a101_W_brOf p) = List.ofFn (wallBrOf blk.wallSec.W) ∧
      s'.arrs (a101_W_edgeOf p) = List.ofFn (wallEdgeOf blk.wallSec.W) ∧
      s'.arrs (a101_perim p) = bitSetList blk.wallSec.W.perimFinset ∧
      s'.arrs (a101_WH p) = bitSetList blk.wallSec.W.vertexFinset ∧
      AtStream (a101_block p) blk.wallSec.W.encList.length rem s' ∧
      (∀ a < alg105ArrBase p, s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < 50 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hh_le : blk.wallSec.h ≤ n := blk.wall_h_le_n
  have hnv_le : elemWallNumVerts blk.wallSec.h ≤ n :=
    le_trans (blk.wallSec.W.elemWallNumVerts_le_card_vertexFinset blk.wallSec.hW)
      blk.wallSec.W.card_vertexFinset_le
  have hne_le : (elemWallEdges blk.wallSec.h).length ≤ 2 * n :=
    le_trans (length_elemWallEdges_le blk.wallSec.h) (Nat.mul_le_mul_left 2 hnv_le)
  -- 1. sumEdgeMultProg
  rcases sumEdgeMultProg_exec G (a101_G p) r101_n hw3 hn_w hm3_w hm_w hG with
    ⟨s₁, t₁, hex₁, ht₁, hrn₁, _, hrm_xLen₁, harr₁, hreg₁⟩
  -- 2. .assign r101_m (.reg r101_xLen)
  let s₂ := s₁.setReg r101_m G.numEdges
  have hex₂ : Exec w (.assign r101_m (.reg r101_xLen)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrm_xLen₁, hm_w])
  -- 3. buildXSeqProg
  rcases buildXSeqProg_exec X' (a101_X p) (a101_buf p) (a101_xSeq p)
      r101_n r101_xLen r101_base
      (by omega) (by omega) (by omega) (by decide) (by decide) (by decide)
      hw (by omega) (s := s₂)
      (by simp [s₂, harr₁, hX]) (by simp [s₂, State.setReg, hrn₁]) with
    ⟨s₃, t₃, hex₃, ht₃, hxSeq₃, hrxLen₃, harr₃, hreg₃⟩
  -- 4. buildListIndProg for xInd
  have hxSeq_lt : ∀ x ∈ xSeqOf X', x < n := fun _ hx => mem_xSeqOf_lt X' hx
  have hxSeq_len_le : (xSeqOf X').length ≤ n := length_xSeqPrefix_le X'
  rcases buildListIndProg_exec (xSeqOf X') hxSeq_lt (a101_xSeq p) (a101_xInd p)
      r101_xLen r101_n r101_base
      (by omega) (by decide) (by decide) hw hn_w (by omega) (s := s₃)
      hxSeq₃ hrxLen₃
      (by rw [hreg₃ r101_n (by decide) (by decide)]; simp [s₂, State.setReg, hrn₁]) with
    ⟨s₄, t₄, hex₄, ht₄, hxInd₄, harr₄, hreg₄⟩
  -- 5. .assign r101_off (.const 0)
  let s₅ := s₄.setReg r101_off 0
  have hex₅ : Exec w (.assign r101_off (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 6. readWallSectionProg
  have hstream₅ : AtStream (a101_block p) 0 (blk.wallSec.W.encList ++ rem) s₅ := by
    refine ⟨[], rfl, ?_⟩
    simp [s₅, harr₄ (a101_block p) (by omega), harr₃ (a101_block p) (by omega) (by omega),
      s₂, harr₁, hblock]
  have hrn₅ : s₅.regs r101_n = n := by
    simp [s₅, State.setReg, hreg₄ r101_n (by decide),
      hreg₃ r101_n (by decide) (by decide), s₂, hrn₁]
  rcases readWallSectionProg_exec
      (a_src := a101_block p) (a_W_br := a101_W_br p)
      (a_W_brOf := a101_W_brOf p) (a_W_edgeOf := a101_W_edgeOf p)
      blk.wallSec.W blk.wallSec.hW
      r101_off r101_n 64 65 66 r101_base
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w (by omega) (by simpa using hwall_len_w)
      (s := s₅) hstream₅ (by simp [s₅]) hrn₅ with
    ⟨s₆, t₆, hex₆, ht₆, _, _, _, hroff₆, hWbr₆, hWbrOf₆, hWedgeOf₆, hstream₆, harr₆, hreg₆⟩
  simp only [Nat.zero_add] at hroff₆ hstream₆
  -- 7. buildWallSubsetBitSetProg for a101_perim
  have hrn₆ : s₆.regs r101_n = n := by
    rw [hreg₆ r101_n (by decide) (by decide) (by decide) (by decide) (by decide), hrn₅]
  rcases buildWallSubsetBitSetProg_exec blk.wallSec.W
      (isPerimBr blk.wallSec.h) (isElemWallPerimEdge blk.wallSec.h)
      (a101_W_brOf p) (a101_W_edgeOf p) (a101_Q0 p) (a101_Q1 p) (a101_perim p)
      r101_n r101_base
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by decide)
      hw2 hn_w (by omega) (by omega) (s := s₆) hWbrOf₆ hWedgeOf₆ hrn₆ with
    ⟨s₇, t₇, hex₇, ht₇, hperim₇, harr₇, hreg₇⟩
  have hperim_eq :
      Finset.univ.filter (fun v : Fin n =>
        wallSubsetInd blk.wallSec.W (isPerimBr blk.wallSec.h)
          (isElemWallPerimEdge blk.wallSec.h) v = true) =
      blk.wallSec.W.perimFinset := by
    ext v
    simp [wallSubsetInd_perimFinset blk.wallSec.hW v]
  rw [hperim_eq] at hperim₇
  -- 8. buildWallSubsetBitSetProg for a101_WH
  rcases buildWallSubsetBitSetProg_exec blk.wallSec.W
      (fun _ => true) (fun _ => true)
      (a101_W_brOf p) (a101_W_edgeOf p) (a101_Q0 p) (a101_Q1 p) (a101_WH p)
      r101_n r101_base
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by decide)
      hw2 hn_w (by omega) (by omega) (s := s₇)
      (by rw [harr₇ (a101_W_brOf p) (by omega) (by omega) (by omega), hWbrOf₆])
      (by rw [harr₇ (a101_W_edgeOf p) (by omega) (by omega) (by omega), hWedgeOf₆])
      (by rw [hreg₇ r101_n (by decide), hrn₆]) with
    ⟨s₈, t₈, hex₈, ht₈, hWH₈, harr₈, hreg₈⟩
  have hWH_eq :
      Finset.univ.filter (fun v : Fin n =>
        wallSubsetInd blk.wallSec.W (fun _ => true) (fun _ => true) v = true) =
      blk.wallSec.W.vertexFinset := by
    ext v
    simp [wallSubsetInd_vertexFinset blk.wallSec.hW v]
  rw [hWH_eq] at hWH₈
  have harr_prev : ∀ a < a101_perim p, s₈.arrs a = s₆.arrs a := fun a ha => by
    rw [harr₈ a (by omega) (by omega) (by omega), harr₇ a (by omega) (by omega) (by omega)]
  have hreg_prev : ∀ r < r101_base, s₈.regs r = s₆.regs r := fun r hr => by
    rw [hreg₈ r hr, hreg₇ r hr]
  refine ⟨s₈, t₁ + (2 + (t₃ + (t₄ + (2 + (t₆ + (t₇ + t₈)))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    by omega,
    by rw [hreg_prev r101_n (by decide), hrn₆],
    by rw [hreg_prev r101_m (by decide),
         hreg₆ r101_m (by decide) (by decide) (by decide) (by decide) (by decide)]
       simp [s₅, State.setReg, hreg₄ r101_m (by decide),
         hreg₃ r101_m (by decide) (by decide), s₂],
    by rw [hreg_prev r101_xLen (by decide),
         hreg₆ r101_xLen (by decide) (by decide) (by decide) (by decide) (by decide)]
       simp [s₅, State.setReg, hreg₄ r101_xLen (by decide), hrxLen₃],
    by rw [hreg_prev r101_off (by decide), hroff₆],
    by rw [harr_prev (a101_G p) (by omega), harr₆ (a101_G p) (by omega) (by omega) (by omega)]
       dsimp only [s₅, s₂]
       rw [State.setReg_arrs, harr₄ (a101_G p) (by omega),
         harr₃ (a101_G p) (by omega) (by omega), State.setReg_arrs, harr₁, hG],
    by rw [harr_prev (a101_X p) (by omega), harr₆ (a101_X p) (by omega) (by omega) (by omega)]
       simp [s₅, harr₄ (a101_X p) (by omega), harr₃ (a101_X p) (by omega) (by omega), s₂, harr₁, hX],
    by rw [harr_prev (a101_xSeq p) (by omega), harr₆ (a101_xSeq p) (by omega) (by omega) (by omega)]
       simp [s₅, harr₄ (a101_xSeq p) (by omega), hxSeq₃],
    by rw [harr_prev (a101_xInd p) (by omega), harr₆ (a101_xInd p) (by omega) (by omega) (by omega)]
       simp [s₅, hxInd₄],
    by rw [harr_prev (a101_W_br p) (by omega), hWbr₆],
    by rw [harr_prev (a101_W_brOf p) (by omega), hWbrOf₆],
    by rw [harr_prev (a101_W_edgeOf p) (by omega), hWedgeOf₆],
    by rw [harr₈ (a101_perim p) (by omega) (by omega) (by omega), hperim₇],
    hWH₈,
    hstream₆.of_arr_eq (harr_prev (a101_block p) (by omega)),
    fun a ha => by
      rw [harr_prev a (by omega), harr₆ a (by omega) (by omega) (by omega)]
      simp [s₅, harr₄ a (by omega), harr₃ a (by omega) (by omega), s₂, harr₁],
    fun r hr => by
      rw [hreg_prev r (by omega),
        hreg₆ r (by omega) (by omega) (by omega) (by omega) (by omega)]
      dsimp only [s₅]
      rw [State.setReg_regs_ne _ _ (show r ≠ r101_off by omega),
        hreg₄ r (by omega), hreg₃ r (by omega) (by omega)]
      dsimp only [s₂]
      rw [State.setReg_regs_ne _ _ (show r ≠ r101_m by omega), hreg₁ r (by omega)]⟩

/-- Part 2 of the Algorithm (10.1) pre-pass:
1. Reads `K_vList` into `a101_KV p` and builds the compass CSR graph `G_K` in
   `(a101_start p, a101_end p, a101_entries p)`.
2. Reads `K_eList` into `a101_KE p`, `corners` into `a101_corners p`, and `M = blk.members.length`
   into `r101_M`.
3. Builds `a101_KInd p`, `a101_isCorner p`, and `a101_degK p`.
4. Saves the member stream start offset `r101_off` in `r101_visPos`, runs `buildVertOwnerProg`
   to populate `a101_owner p`, and restores `r101_off` from `r101_visPos`. -/
def alg101PrePassPart2Prog (p : ℕ) : Cmd :=
  .seq (readLengthPrefixedProg (a101_block p) (a101_KV p) r101_off 64 r101_base)
    (.seq (buildCompassCSRProg (a101_G p) (a101_KV p) (a101_KE p)
      64 r101_n r101_base r101_R_off (alg105ArrBase p + 13))
      (.seq (readEdgeTriplesStreamProg (a101_block p) (a101_KE p) r101_off 65 66 r101_base)
        (.seq (.assign 66 (.const 4))
          (.seq (readStreamSliceProg (a101_block p) (a101_corners p) r101_off 66 r101_base)
            (.seq (readStreamWordProg (a101_block p) r101_off r101_M)
              (.seq (buildListIndProg (a101_KV p) (a101_KInd p) 64 r101_n r101_base)
                (.seq (buildListIndProg (a101_corners p) (a101_isCorner p) 66 r101_n r101_base)
                  (.seq (countIncEdgesProg (a101_KE p) (a101_degK p) 65 r101_n r101_base)
                    (.seq (.assign r101_visPos (.reg r101_off))
                      (.seq (buildVertOwnerProg (a101_block p) r101_off r101_M r101_n
                        (a101_rV p) (a101_rE p) (a101_rPar p) (a101_rTau p)
                        (a101_Q0 p) (a101_owner p)
                        r101_vLen r101_rELen r101_rT r101_j r101_base)
                        (.assign r101_off (.reg r101_visPos))))))))))))

theorem alg101PrePassPart2Prog_exec {w n p off₀ : ℕ}
    (G : MultiDigraph n) {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hDiv : GM13.IsSocietyDivision blk.toSociety blk.toDivision)
    (rest : List ℕ)
    (hw6 : 6 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (h3m_w : 3 * G.numEdges + 1 < 2 ^ w)
    (hN_w : 2 * (n + G.numEdges + 1) < 2 ^ w)
    (hoff_w : off₀ + (1 + blk.K_vList.length) + (1 + 3 * blk.K_eList.length) + 4 + 1 +
      (blk.members.flatMap Case3MemberRecord.enc).length < 2 ^ w)
    {s : State}
    (hG : s.arrs (a101_G p) = G.enc)
    (hrn : s.regs r101_n = n)
    (hroff : s.regs r101_off = off₀)
    (hstream : AtStream (a101_block p) off₀
      ((blk.K_vList.length :: blk.K_vList) ++
        (blk.K_eList.length :: encEdgeTriples blk.K_eList) ++
        blk.corners ++
        (blk.members.length :: blk.members.flatMap Case3MemberRecord.enc) ++ rest) s) :
    let off_mem := off₀ + (1 + blk.K_vList.length) + (1 + 3 * blk.K_eList.length) + 4 + 1
    let lists := edgeNeighbors (edgeListOf (G.deleteVertices (Z_notK blk)).toSimpleGraph)
    ∃ s' t,
      Exec w (alg101PrePassPart2Prog p) s s' t ∧
      t ≤ 500 * (n + G.numEdges + 1) + 304 * G.numActivePairs + 500 ∧
      s'.regs r101_M = blk.members.length ∧
      s'.regs r101_off = off_mem ∧
      AtStream (a101_block p) off_mem
        ((blk.members.flatMap Case3MemberRecord.enc) ++ rest) s' ∧
      s'.arrs (a101_KV p) = blk.K_vList ∧
      s'.arrs (a101_KE p) = encEdgeTriples blk.K_eList ∧
      s'.arrs (a101_corners p) = blk.corners ∧
      s'.arrs (a101_KInd p) =
        bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ blk.K_vList)) ∧
      s'.arrs (a101_isCorner p) =
        bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ blk.corners)) ∧
      s'.arrs (a101_degK p) = List.ofFn (fun v : Fin n => incEdgeCount blk.K_eList v.1) ∧
      IsAdjList (G.deleteVertices (Z_notK blk)).toSimpleGraph
        (a101_start p) (a101_end p) (a101_entries p) lists s' ∧
      (s'.arrs (a101_entries p)).length ≤ 2 * G.numActivePairs ∧
      totalAdjEntries lists ≤ 2 * G.numActivePairs ∧
      s'.arrs (a101_owner p) = List.ofFn (fun u : Fin n => vertOwner blk u.1) ∧
      (∀ a < a101_KV p, s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < 55 → s'.regs r = s.regs r) := by
  intro off_mem lists
  have hw : 1 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hKV_lt : ∀ x ∈ blk.K_vList, x < n := blk.K_vList_lt_n
  have hKV_w : ∀ x ∈ blk.K_vList, x < 2 ^ w := fun x hx => lt_trans (hKV_lt x hx) hn_w
  have hKVL_le : blk.K_vList.length ≤ n := blk.hK_v_len
  have hKEL_le : blk.K_eList.length ≤ G.numEdges :=
    le_trans blk.hK_e_len (G.numEdges_deleteVertices_le X')
  have hKE_w : ∀ x ∈ encEdgeTriples blk.K_eList, x < 2 ^ w := fun x hx =>
    lt_trans (blk.encEdgeTriples_K_eList_lt x hx) (by omega)
  have hcor_len : blk.corners.length = 4 := blk.corners_length
  have hcor_lt : ∀ x ∈ blk.corners, x < n := blk.corners_lt_n
  have hcor_w : ∀ x ∈ blk.corners, x < 2 ^ w := fun x hx => lt_trans (hcor_lt x hx) hn_w
  have hM_le : blk.members.length ≤ n + G.numEdges + 1 := by
    have h1 := blk.hmembers_len
    have h2 := G.numEdges_deleteVertices_le X'
    omega
  have hM_w : blk.members.length < 2 ^ w := by omega
  -- 1. readLengthPrefixedProg for K_vList
  have hstream₀ :
      AtStream (a101_block p) off₀
        (blk.K_vList.length :: blk.K_vList ++
          ((blk.K_eList.length :: encEdgeTriples blk.K_eList) ++
            blk.corners ++
            (blk.members.length :: blk.members.flatMap Case3MemberRecord.enc) ++ rest)) s := by
    simpa [List.append_assoc] using hstream
  rcases readLengthPrefixedProg_exec
      (a_src := a101_block p) (a_dst := a101_KV p)
      r101_off 64 r101_base
      (by omega) (by decide) (by decide) (by decide)
      hKV_w hw (by omega) hstream₀ hroff with
    ⟨s₁, t₁, hex₁, ht₁, hKV₁, hr64_1, hroff₁, hstream₁, harr₁, hreg₁⟩
  -- 2. buildCompassCSRProg
  have hrn₁ : s₁.regs r101_n = n := by
    rw [hreg₁ r101_n (by decide) (by decide) (by decide), hrn]
  rcases buildCompassCSRProg_exec blk (a101_G p) (a101_KV p) (a101_KE p)
      64 r101_n r101_base r101_R_off (alg105ArrBase p + 13)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide)
      hw3 hn_w hm3_w (by omega) (s := s₁)
      (by rw [harr₁ (a101_G p) (by omega), hG]) hKV₁ hr64_1 hrn₁ with
    ⟨s₂, t₂, hex₂, ht₂, _, hadj₂, hent_len₂, htot_lists, harr₂, hreg₂⟩
  -- 3. readEdgeTriplesStreamProg for K_eList
  have hstream₂ :
      AtStream (a101_block p) (off₀ + 1 + blk.K_vList.length)
        (blk.K_eList.length :: encEdgeTriples blk.K_eList ++
          (blk.corners ++
            (blk.members.length :: blk.members.flatMap Case3MemberRecord.enc) ++ rest)) s₂ := by
    simpa [List.append_assoc] using (hstream₁.of_arr_eq (harr₂ (a101_block p) (by omega) (by omega)))
  rcases readEdgeTriplesStreamProg_exec
      (a_src := a101_block p) (a_dst := a101_KE p)
      r101_off 65 66 r101_base
      (by omega) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hKE_w hw3 (by omega) hstream₂
      (by rw [hreg₂ r101_off (by decide), hroff₁]) with
    ⟨s₃, t₃, hex₃, ht₃, hKE₃, hr65_3, _, hroff₃, hstream₃, harr₃, hreg₃⟩
  -- 4. .assign 66 (.const 4)
  let s₄ := s₃.setReg 66 4
  have hex₄ : Exec w (.assign 66 (.const 4)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 4 < 2 ^ w by omega])
  -- 5. readStreamSliceProg for corners
  have hstream₄ :
      AtStream (a101_block p)
        (off₀ + 1 + blk.K_vList.length + 1 + 3 * blk.K_eList.length)
        (blk.corners ++
          ((blk.members.length :: blk.members.flatMap Case3MemberRecord.enc) ++ rest)) s₄ := by
    simpa [List.append_assoc] using (hstream₃.of_arr_eq (by simp [s₄]))
  rcases readStreamSliceProg_exec
      (a_src := a101_block p) (a_dst := a101_corners p)
      r101_off 66 r101_base
      (by omega) (by decide) (by decide) (by decide)
      hcor_w hw (by rw [hcor_len]; omega) (s := s₄) hstream₄
      (by simp [s₄, State.setReg, hroff₃])
      (by simp [s₄, hcor_len]) with
    ⟨s₅, t₅, hex₅, ht₅, hcor₅, hroff₅, hr66_5, hstream₅, harr₅, hreg₅⟩
  rw [hcor_len] at ht₅ hroff₅ hr66_5 hstream₅
  -- 6. readStreamWordProg for r101_M = blk.members.length
  have hstream₅' :
      AtStream (a101_block p)
        (off₀ + 1 + blk.K_vList.length + 1 + 3 * blk.K_eList.length + 4)
        (blk.members.length :: ((blk.members.flatMap Case3MemberRecord.enc) ++ rest)) s₅ := by
    simpa using hstream₅
  rcases readStreamWordProg_exec
      (a_src := a101_block p)
      r101_off r101_M (by decide)
      hw (by omega) hM_w hstream₅' hroff₅ with
    ⟨s₆, t₆, hex₆, ht₆, hrM₆, hroff₆, hstream₆, harr₆, hreg₆⟩
  have hoff_mem_eq :
      off₀ + 1 + blk.K_vList.length + 1 + 3 * blk.K_eList.length + 4 + 1 = off_mem := by
    dsimp [off_mem]; omega
  rw [hoff_mem_eq] at hroff₆ hstream₆
  -- 7. buildListIndProg for a101_KInd
  have hKV₆ : s₆.arrs (a101_KV p) = blk.K_vList := by
    rw [harr₆, harr₅ (a101_KV p) (by omega)]
    dsimp only [s₄]
    rw [State.setReg_arrs, harr₃ (a101_KV p) (by omega),
      harr₂ (a101_KV p) (by omega) (by omega), hKV₁]
  have hr64_6 : s₆.regs 64 = blk.K_vList.length := by
    rw [hreg₆ 64 (by decide) (by decide), hreg₅ 64 (by decide) (by decide)]
    simp [s₄, State.setReg, hreg₃ 64 (by decide) (by decide) (by decide) (by decide),
      hreg₂ 64 (by decide), hr64_1]
  have hrn₆ : s₆.regs r101_n = n := by
    rw [hreg₆ r101_n (by decide) (by decide), hreg₅ r101_n (by decide) (by decide)]
    simp [s₄, State.setReg, hreg₃ r101_n (by decide) (by decide) (by decide) (by decide),
      hreg₂ r101_n (by decide), hrn₁]
  rcases buildListIndProg_exec blk.K_vList hKV_lt (a101_KV p) (a101_KInd p)
      64 r101_n r101_base (by omega) (by decide) (by decide)
      hw hn_w (by omega) (s := s₆) hKV₆ hr64_6 hrn₆ with
    ⟨s₇, t₇, hex₇, ht₇, hKInd₇, harr₇, hreg₇⟩
  -- 8. buildListIndProg for a101_isCorner
  rcases buildListIndProg_exec blk.corners hcor_lt (a101_corners p) (a101_isCorner p)
      66 r101_n r101_base (by omega) (by decide) (by decide)
      hw hn_w (by rw [hcor_len]; omega) (s := s₇)
      (by rw [harr₇ (a101_corners p) (by omega), harr₆, hcor₅])
      (by rw [hreg₇ 66 (by decide), hreg₆ 66 (by decide) (by decide), hcor_len, hr66_5])
      (by rw [hreg₇ r101_n (by decide), hrn₆]) with
    ⟨s₈, t₈, hex₈, ht₈, hisC₈, harr₈, hreg₈⟩
  -- 9. countIncEdgesProg for a101_degK
  rcases countIncEdgesProg_exec blk.K_eList blk.K_eList_endpoints_lt
      (a101_KE p) (a101_degK p) 65 r101_n r101_base
      (by omega) (by decide) (by decide) hw3 hn_w (by omega) (s := s₈)
      (by rw [harr₈ (a101_KE p) (by omega), harr₇ (a101_KE p) (by omega),
            harr₆, harr₅ (a101_KE p) (by omega)]; dsimp only [s₄]; rw [State.setReg_arrs]; exact hKE₃)
      (by rw [hreg₈ 65 (by decide), hreg₇ 65 (by decide),
            hreg₆ 65 (by decide) (by decide), hreg₅ 65 (by decide) (by decide)]
          simp [s₄, State.setReg, hr65_3])
      (by rw [hreg₈ r101_n (by decide), hreg₇ r101_n (by decide), hrn₆]) with
    ⟨s₉, t₉, hex₉, ht₉, hdegK₉, harr₉, hreg₉⟩
  -- 10. .assign r101_visPos (.reg r101_off)
  have hroff₉ : s₉.regs r101_off = off_mem := by
    rw [hreg₉ r101_off (by decide), hreg₈ r101_off (by decide),
      hreg₇ r101_off (by decide), hroff₆]
  have hoff_mem_w : off_mem < 2 ^ w := by dsimp [off_mem]; omega
  let s₁₀ := s₉.setReg r101_visPos off_mem
  have hex₁₀ : Exec w (.assign r101_visPos (.reg r101_off)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, hroff₉, hoff_mem_w])
  -- 11. buildVertOwnerProg
  have hwords_mem : ∀ r ∈ blk.members, ∀ x ∈ r.enc, x < 2 ^ w := fun r hr x hx =>
    lt_of_le_of_lt (blk.member_enc_le r hr x hx) hN_w
  have hstream₁₀ :
      AtStream (a101_block p) off_mem
        ((blk.members.flatMap Case3MemberRecord.enc) ++ rest) s₁₀ := by
    apply hstream₆.of_arr_eq
    simp [s₁₀, harr₉ (a101_block p) (by omega),
      harr₈ (a101_block p) (by omega), harr₇ (a101_block p) (by omega)]
  rcases buildVertOwnerProg_exec blk rest off_mem
      (a101_block p) r101_off r101_M r101_n
      (a101_rV p) (a101_rE p) (a101_rPar p) (a101_rTau p) (a101_Q0 p) (a101_owner p)
      r101_vLen r101_rELen r101_rT r101_j r101_base
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw3 hn_w hwords_mem hM_w (by dsimp [off_mem]; omega)
      (s := s₁₀) hstream₁₀
      (by simp [s₁₀, State.setReg, hroff₉])
      (by simp [s₁₀, State.setReg, hreg₉ r101_M (by decide),
            hreg₈ r101_M (by decide), hreg₇ r101_M (by decide), hrM₆])
      (by simp [s₁₀, State.setReg, hreg₉ r101_n (by decide),
            hreg₈ r101_n (by decide), hreg₇ r101_n (by decide), hrn₆]) with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, _, _, howner₁₁, harr₁₁, hreg₁₁⟩
  -- 12. .assign r101_off (.reg r101_visPos)
  have hrvisPos₁₁ : s₁₁.regs r101_visPos = off_mem := by
    rw [hreg₁₁ r101_visPos (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₁₀]
  let s₁₂ := s₁₁.setReg r101_off off_mem
  have hex₁₂ : Exec w (.assign r101_off (.reg r101_visPos)) s₁₁ s₁₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrvisPos₁₁, hoff_mem_w])
  have hsum_own := blk.buildVertOwner_sum_le hDiv
  have harr_s₁₂_s₆ : ∀ a < a101_owner p,
      a ≠ a101_KInd p → a ≠ a101_isCorner p → a ≠ a101_degK p →
      s₁₂.arrs a = s₆.arrs a := fun a ha h14 h15 h16 => by
    simp only [s₁₂, State.setReg_arrs]
    rw [harr₁₁ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [s₁₀, State.setReg_arrs]
    rw [harr₉ a h16, harr₈ a h15, harr₇ a h14]
  have harr_s₆_s₂ : ∀ a < a101_owner p,
      a ≠ a101_KE p → a ≠ a101_corners p →
      s₆.arrs a = s₂.arrs a := fun a _ h12 h13 => by
    rw [harr₆, harr₅ a h13]
    simp only [s₄, State.setReg_arrs]
    rw [harr₃ a h12]
  have hadj₁₂ : IsAdjList (G.deleteVertices (Z_notK blk)).toSimpleGraph
      (a101_start p) (a101_end p) (a101_entries p) lists s₁₂ :=
    hadj₂.of_arrs_eq
      (by rw [harr_s₁₂_s₆ (a101_start p) (by omega) (by omega) (by omega) (by omega),
            harr_s₆_s₂ (a101_start p) (by omega) (by omega) (by omega)])
      (by rw [harr_s₁₂_s₆ (a101_end p) (by omega) (by omega) (by omega) (by omega),
            harr_s₆_s₂ (a101_end p) (by omega) (by omega) (by omega)])
      (by rw [harr_s₁₂_s₆ (a101_entries p) (by omega) (by omega) (by omega) (by omega),
            harr_s₆_s₂ (a101_entries p) (by omega) (by omega) (by omega)])
  have hent_len₁₂ : (s₁₂.arrs (a101_entries p)).length ≤ 2 * G.numActivePairs := by
    rw [harr_s₁₂_s₆ (a101_entries p) (by omega) (by omega) (by omega) (by omega),
      harr_s₆_s₂ (a101_entries p) (by omega) (by omega) (by omega)]
    exact hent_len₂
  refine ⟨s₁₂,
    t₁ + (t₂ + (t₃ + (2 + (t₅ + (t₆ + (t₇ + (t₈ + (t₉ + (2 + (t₁₁ + 2)))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))),
    by omega,
    by simp [s₁₂, State.setReg,
         hreg₁₁ r101_M (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
         s₁₀, hreg₉ r101_M (by decide), hreg₈ r101_M (by decide), hreg₇ r101_M (by decide), hrM₆],
    by simp [s₁₂],
    hstream₆.of_arr_eq (harr_s₁₂_s₆ (a101_block p) (by omega) (by omega) (by omega) (by omega)),
    by rw [harr_s₁₂_s₆ (a101_KV p) (by omega) (by omega) (by omega) (by omega), hKV₆],
    by rw [harr_s₁₂_s₆ (a101_KE p) (by omega) (by omega) (by omega) (by omega),
         harr₆, harr₅ (a101_KE p) (by omega)]; exact hKE₃,
    by rw [harr_s₁₂_s₆ (a101_corners p) (by omega) (by omega) (by omega) (by omega), harr₆, hcor₅],
    by simp only [s₁₂, State.setReg_arrs]
       rw [harr₁₁ (a101_KInd p) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
       simp [s₁₀, harr₉ (a101_KInd p) (by omega), harr₈ (a101_KInd p) (by omega), hKInd₇],
    by simp only [s₁₂, State.setReg_arrs]
       rw [harr₁₁ (a101_isCorner p) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
       simp [s₁₀, harr₉ (a101_isCorner p) (by omega), hisC₈],
    by simp only [s₁₂, State.setReg_arrs]
       rw [harr₁₁ (a101_degK p) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
       simp [s₁₀, hdegK₉],
    hadj₁₂, hent_len₁₂, htot_lists,
    by simp [s₁₂, howner₁₁],
    fun a ha => by
      rw [harr_s₁₂_s₆ a (by omega) (by omega) (by omega) (by omega),
        harr_s₆_s₂ a (by omega) (by omega) (by omega),
        harr₂ a (by omega) (by omega), harr₁ a (by omega)],
    fun r hr => by
      have hr_lt72 : r < r101_base := by omega
      have hr_ne_off : r ≠ r101_off := by omega
      have hr_ne_vis : r ≠ r101_visPos := by omega
      have hr_ne_M : r ≠ r101_M := by omega
      have hr_ne_j : r ≠ r101_j := by omega
      have hr_ne_vLen : r ≠ r101_vLen := by omega
      have hr_ne_rELen : r ≠ r101_rELen := by omega
      have hr_ne_rT : r ≠ r101_rT := by omega
      have hr_ne_64 : r ≠ 64 := by omega
      have hr_ne_65 : r ≠ 65 := by omega
      have hr_ne_66 : r ≠ 66 := by omega
      dsimp only [s₁₂]
      rw [State.setReg_regs_ne _ _ hr_ne_off,
        hreg₁₁ r hr_lt72 hr_ne_off hr_ne_vLen hr_ne_rELen hr_ne_rT hr_ne_j]
      dsimp only [s₁₀]
      rw [State.setReg_regs_ne _ _ hr_ne_vis,
        hreg₉ r hr_lt72, hreg₈ r hr_lt72, hreg₇ r hr_lt72,
        hreg₆ r hr_ne_off hr_ne_M, hreg₅ r hr_lt72 hr_ne_off]
      dsimp only [s₄]
      rw [State.setReg_regs_ne _ _ hr_ne_66,
        hreg₃ r hr_lt72 hr_ne_off hr_ne_65 hr_ne_66,
        hreg₂ r hr_lt72, hreg₁ r hr_lt72 hr_ne_off hr_ne_64]⟩

/-- Complete pre-pass of Algorithm (10.1): runs Part 1 followed by Part 2. -/
def alg101PrePassProg (p h : ℕ) : Cmd :=
  .seq (alg101PrePassPart1Prog p h) (alg101PrePassPart2Prog p)

/-! ### Section 3: Vision Buffer Initialization and Member Loop (`alg101InitVisProg`, `alg101MemberLoop_aux`) -/

/-- Initialize the serialized Vision output buffer `a101_visBuf p` with capacity
`(2 + xLen) + M * memberPerCap C41 n m`, write the header `xLen :: xSeq ++ [M]`,
allocate the member summary tables `a101_memIsInt p`, `a101_memVOf p`, `a101_memFolioCode p`
of length `M`, and set `r101_j := 0`. -/
def alg101InitVisProg (p C41 : ℕ) : Cmd :=
  .seq (.assign r101_base (.op .add (.op .add (.reg r101_n) (.reg r101_m)) (.const 1)))
    (.seq (.assign r101_base
      (.op .add (.op .mul (.const C41) (.reg r101_base))
        (.op .mul (.const 18) (.reg r101_base))))
      (.seq (.assign r101_base
        (.op .add (.op .add (.const 2) (.reg r101_xLen))
          (.op .mul (.reg r101_M) (.reg r101_base))))
        (.seq (initPrefixBufferProg (a101_visBuf p) (.reg r101_base) r101_visPos)
          (.seq (appendLengthPrefixedProg (a101_xSeq p) (a101_visBuf p)
            r101_xLen r101_visPos r101_base)
            (.seq (appendWordProg (a101_visBuf p) r101_visPos (.reg r101_M))
              (.seq (.alloc (a101_memIsInt p) (.reg r101_M))
                (.seq (.alloc (a101_memVOf p) (.reg r101_M))
                  (.seq (.alloc (a101_memFolioCode p) (.reg r101_M))
                    (.assign r101_j (.const 0))))))))))

theorem alg101InitVisProg_exec {w n m p M C41 : ℕ}
    (xSeq : List ℕ) (hxSeq_lt : ∀ x ∈ xSeq, x < n)
    (hw18 : 18 < 2 ^ w) (hn_w : n < 2 ^ w) (hm_w : m < 2 ^ w) (hM_w : M < 2 ^ w)
    (hC41_w : C41 < 2 ^ w)
    (hcap_w : (2 + xSeq.length) + M * memberPerCap C41 n m < 2 ^ w)
    (hper_w : memberPerCap C41 n m < 2 ^ w)
    {s : State}
    (hxSeq : s.arrs (a101_xSeq p) = xSeq)
    (hrn : s.regs r101_n = n)
    (hrm : s.regs r101_m = m)
    (hrxLen : s.regs r101_xLen = xSeq.length)
    (hrM : s.regs r101_M = M) :
    ∃ s' t,
      Exec w (alg101InitVisProg p C41) s s' t ∧
      t ≤ (2 + xSeq.length) + M * memberPerCap C41 n m + 18 * xSeq.length + 3 * M + 50 ∧
      IsPrefixBuffer (a101_visBuf p) ((xSeq.length :: xSeq) ++ [M])
        (M * memberPerCap C41 n m) s' ∧
      s'.regs r101_visPos = ((xSeq.length :: xSeq) ++ [M]).length ∧
      s'.arrs (a101_memIsInt p) = List.replicate M 0 ∧
      s'.arrs (a101_memVOf p) = List.replicate M 0 ∧
      s'.arrs (a101_memFolioCode p) = List.replicate M 0 ∧
      s'.regs r101_j = 0 ∧
      (∀ a : ℕ, a ≠ a101_visBuf p → a ≠ a101_memIsInt p →
        a ≠ a101_memVOf p → a ≠ a101_memFolioCode p → s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < r101_base → r ≠ r101_visPos → r ≠ r101_j → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hC41_nm1_w : C41 * (n + m + 1) < 2 ^ w := by
    unfold memberPerCap at hper_w; omega
  have h18_nm1_w : 18 * (n + m + 1) < 2 ^ w := by
    unfold memberPerCap at hper_w; omega
  have hnm1_w : n + m + 1 < 2 ^ w := by omega
  have hnm_w : n + m < 2 ^ w := by omega
  have hxLen_w : xSeq.length < 2 ^ w := by omega
  have h2xLen_w : 2 + xSeq.length < 2 ^ w := by omega
  have hM_per_w : M * memberPerCap C41 n m < 2 ^ w := by omega
  let cap_vis := (2 + xSeq.length) + M * memberPerCap C41 n m
  -- 1. r101_base := n + m + 1
  let s₁ := s.setReg r101_base (n + m + 1)
  have hex₁ :
      Exec w (.assign r101_base (.op .add (.op .add (.reg r101_n) (.reg r101_m)) (.const 1)))
        s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hrn, hrm, hn_w, hm_w, hnm_w, hw, hnm1_w])
  -- 2. r101_base := memberPerCap C41 n m
  let s₂ := s₁.setReg r101_base (memberPerCap C41 n m)
  have hex₂ :
      Exec w (.assign r101_base
        (.op .add (.op .mul (.const C41) (.reg r101_base))
          (.op .mul (.const 18) (.reg r101_base)))) s₁ s₂ 8 :=
    .assign (by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hC41_w, hnm1_w, hC41_nm1_w, hw18, h18_nm1_w,
        show C41 * (n + m + 1) + 18 * (n + m + 1) = memberPerCap C41 n m from rfl, hper_w])
  -- 3. r101_base := cap_vis
  let s₃ := s₂.setReg r101_base cap_vis
  have hex₃ :
      Exec w (.assign r101_base
        (.op .add (.op .add (.const 2) (.reg r101_xLen))
          (.op .mul (.reg r101_M) (.reg r101_base)))) s₂ s₃ 8 :=
    .assign (by
      simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hw2, hrxLen, hxLen_w, h2xLen_w, hrM, hM_w, hper_w, hM_per_w, cap_vis, hcap_w])
  -- 4. initPrefixBufferProg
  rcases initPrefixBufferProg_exec (cap := cap_vis) (a101_visBuf p) (.reg r101_base) r101_visPos
      hw (s := s₃) (by simp [s₃, Expr.eval, checkWord, cap_vis, hcap_w]) with
    ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hrvisPos₄, harr₄, hreg₄⟩
  -- 5. appendLengthPrefixedProg for xSeq
  have hbuf₄' :
      IsPrefixBuffer (a101_visBuf p) []
        (1 + xSeq.length + (1 + M * memberPerCap C41 n m)) s₄ := by
    unfold IsPrefixBuffer at hbuf₄ ⊢
    rw [hbuf₄]
    have hrep : cap_vis = 1 + xSeq.length + (1 + M * memberPerCap C41 n m) := by
      dsimp [cap_vis]; omega
    rw [hrep]
  have hxSeq_w : ∀ x ∈ xSeq, x < 2 ^ w := fun x hx => lt_trans (hxSeq_lt x hx) hn_w
  rcases appendLengthPrefixedProg_exec (a101_xSeq p) (a101_visBuf p)
      r101_xLen r101_visPos r101_base
      (by omega) (by decide) (by decide) (by decide)
      hxSeq_w hw (by simp; omega) (s := s₄)
      (by rw [harr₄ (a101_xSeq p) (by omega)]; simp [s₃, s₂, s₁, hxSeq])
      hbuf₄'
      (by rw [hreg₄ r101_xLen (by decide)]; simp [s₃, s₂, s₁, hrxLen])
      hrvisPos₄ with
    ⟨s₅, t₅, hex₅, ht₅, hbuf₅, hrvisPos₅, _, harr₅, hreg₅⟩
  simp only [List.nil_append] at hbuf₅ hrvisPos₅
  -- 6. appendWordProg for r101_M
  have hbuf₅' :
      IsPrefixBuffer (a101_visBuf p) (xSeq.length :: xSeq)
        (M * memberPerCap C41 n m + 1) s₅ := by
    unfold IsPrefixBuffer at hbuf₅ ⊢
    rw [hbuf₅, Nat.add_comm 1]
  have hrM₅ : s₅.regs r101_M = M := by
    rw [hreg₅ r101_M (by decide) (by decide), hreg₄ r101_M (by decide)]
    simp [s₃, s₂, s₁, hrM]
  rcases appendWordProg_exec (val := M) (a101_visBuf p) r101_visPos (.reg r101_M)
      hw (by simp; omega) hbuf₅' hrvisPos₅
      (by simp [Expr.eval, checkWord, hrM₅, hM_w]) with
    ⟨s₆, t₆, hex₆, ht₆, hbuf₆, hrvisPos₆, harr₆, hreg₆⟩
  -- 7-9. Three .alloc commands and .assign r101_j 0
  have hrM₆ : s₆.regs r101_M = M := by rw [hreg₆ r101_M (by decide), hrM₅]
  let s₇ := s₆.setArr (a101_memIsInt p) (List.replicate M 0)
  have hex₇ : Exec w (.alloc (a101_memIsInt p) (.reg r101_M)) s₆ s₇ (1 + M) :=
    .alloc (by simp [Expr.eval, checkWord, hrM₆, hM_w])
  let s₈ := s₇.setArr (a101_memVOf p) (List.replicate M 0)
  have hex₈ : Exec w (.alloc (a101_memVOf p) (.reg r101_M)) s₇ s₈ (1 + M) :=
    .alloc (by simp [s₇, Expr.eval, checkWord, hrM₆, hM_w])
  let s₉ := s₈.setArr (a101_memFolioCode p) (List.replicate M 0)
  have hex₉ : Exec w (.alloc (a101_memFolioCode p) (.reg r101_M)) s₈ s₉ (1 + M) :=
    .alloc (by simp [s₈, s₇, Expr.eval, checkWord, hrM₆, hM_w])
  let s₁₀ := s₉.setReg r101_j 0
  have hex₁₀ : Exec w (.assign r101_j (.const 0)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  dsimp [Expr.cost] at ht₄ ht₆
  refine ⟨s₁₀,
    6 + (8 + (8 + (t₄ + (t₅ + (t₆ + ((1 + M) + ((1 + M) + ((1 + M) + 2)))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
    by dsimp [cap_vis] at ht₄; omega,
    hbuf₆.of_arr_eq (by
      dsimp only [s₁₀, s₉, s₈, s₇]
      rw [State.setReg_arrs,
        State.setArr_arrs_ne _ _ (show a101_visBuf p ≠ a101_memFolioCode p by omega),
        State.setArr_arrs_ne _ _ (show a101_visBuf p ≠ a101_memVOf p by omega),
        State.setArr_arrs_ne _ _ (show a101_visBuf p ≠ a101_memIsInt p by omega)]),
    by simp [s₁₀, s₉, s₈, s₇, hrvisPos₆],
    by dsimp only [s₁₀, s₉, s₈, s₇]
       rw [State.setReg_arrs,
         State.setArr_arrs_ne _ _ (show a101_memIsInt p ≠ a101_memFolioCode p by omega),
         State.setArr_arrs_ne _ _ (show a101_memIsInt p ≠ a101_memVOf p by omega)]
       simp,
    by dsimp only [s₁₀, s₉, s₈, s₇]
       rw [State.setReg_arrs,
         State.setArr_arrs_ne _ _ (show a101_memVOf p ≠ a101_memFolioCode p by omega)]
       simp,
    by simp [s₁₀, s₉],
    by simp [s₁₀],
    fun a h1 h2 h3 h4 => by
      simp only [s₁₀, s₉, s₈, s₇, State.setReg_arrs,
        State.setArr_arrs_ne _ _ h4, State.setArr_arrs_ne _ _ h3, State.setArr_arrs_ne _ _ h2]
      rw [harr₆ a h1, harr₅ a h1, harr₄ a h1]
      rfl,
    fun r hr hne₁ hne₂ => by
      have hr_ne_base : r ≠ r101_base := by omega
      dsimp only [s₁₀, s₉, s₈, s₇]
      rw [State.setReg_regs_ne _ _ hne₂, State.setArr_regs, State.setArr_regs, State.setArr_regs,
        hreg₆ r hne₁, hreg₅ r hr hne₁, hreg₄ r hne₁]
      dsimp only [s₃, s₂, s₁]
      rw [State.setReg_regs_ne _ _ hr_ne_base, State.setReg_regs_ne _ _ hr_ne_base,
        State.setReg_regs_ne _ _ hr_ne_base]⟩

/-- Inductive execution theorem for the member iteration loop
`forUp r101_j (.reg r101_M) (alg101MemberStepProg p q δ prog41)`. -/
theorem alg101MemberLoop_aux {w n p q q_C δ ω c41 C41 : ℕ} {prog41 : Cmd}
    (h41 : Alg41ProgSpec p q δ ω prog41 c41 C41)
    (G : MultiDigraph n) {X' : Finset (Fin n)} (hx_card : X'.card ≤ q)
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q_C X'.toNatSet blk.toGMWall blk.toSociety blk.toDivision)
    (hbd_all : ∀ j : Fin blk.members.length,
      isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true →
      MemberBranchDecompValid G X' ω (blk.members[j.1]'j.2))
    (xSeq : List ℕ) (hx_nd : xSeq.Nodup) (hx_set : xSeq.toFinset = X'.image Fin.val)
    (lists : Fin n → List ℕ) (htot_lists : totalAdjEntries lists ≤ 2 * G.numEdges) (rest : List ℕ)
    (hw6 : 6 < 2 ^ w) (h2n_w : 2 * n + 4 < 2 ^ w)
    (h2nsq_w : 2 + 6 * (n * n) < 2 ^ w)
    (hcapE_w : 6 * G.numEdges + 1 < 2 ^ w)
    (hM_w : blk.members.length < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hwords_all : ∀ r ∈ blk.members, ∀ x ∈ r.enc, x < 2 ^ w)
    (hw41 : wordSize c41 (n + G.numEdges + 1) ≤ w)
    (h41_len_w : C41 * (n + G.numEdges + 1) < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w)
    (hw_len : maxFolioEncLen101 q δ < 2 ^ w)
    (hw_word : maxFolioEncWord q δ + 1 < 2 ^ w)
    (hw_q : q + 4 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = blk.members.length)
    (off : ℕ)
    (hoff_w : off + ((blk.members.drop k).flatMap Case3MemberRecord.enc).length < 2 ^ w)
    (pfx : List ℕ) (rem_cap : ℕ)
    (hpfx_rem_w : pfx.length + rem * memberPerCap C41 n G.numEdges < 2 ^ w)
    (hcap_ge : rem * memberPerCap C41 n G.numEdges ≤ rem_cap)
    (recs_pfx : List VisionMemberRecord) (hrecs_len : recs_pfx.length = k)
    {s : State}
    (hstream : AtStream (a101_block p) off
      (((blk.members.drop k).flatMap Case3MemberRecord.enc) ++ rest) s)
    (hroff : s.regs r101_off = off)
    (hvisBuf : IsPrefixBuffer (a101_visBuf p) pfx rem_cap s)
    (hrvisPos : s.regs r101_visPos = pfx.length)
    (hmemInt : s.arrs (a101_memIsInt p) =
      recs_pfx.map VisionMemberRecord.isInterior ++ List.replicate rem 0)
    (hmemVOf : s.arrs (a101_memVOf p) =
      recs_pfx.map VisionMemberRecord.vOf ++ List.replicate rem 0)
    (hmemFCode : s.arrs (a101_memFolioCode p) =
      recs_pfx.map VisionMemberRecord.folioCode ++ List.replicate rem 0)
    (hG : s.arrs (a101_G p) = G.enc)
    (hxSeq : s.arrs (a101_xSeq p) = xSeq)
    (hxInd : s.arrs (a101_xInd p) = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeq)))
    (hperim : s.arrs (a101_perim p) = bitSetList blk.wallSec.W.perimFinset)
    (hWH : s.arrs (a101_WH p) = bitSetList blk.wallSec.W.vertexFinset)
    (hcor : s.arrs (a101_corners p) = blk.corners)
    (hKInd : s.arrs (a101_KInd p) = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ blk.K_vList)))
    (hisC : s.arrs (a101_isCorner p) =
      bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ blk.corners)))
    (hdegK : s.arrs (a101_degK p) = List.ofFn (fun v : Fin n => incEdgeCount blk.K_eList v.1))
    (hadj : IsAdjList (G.deleteVertices (Z_notK blk)).toSimpleGraph
      (a101_start p) (a101_end p) (a101_entries p) lists s)
    (hent_w : (s.arrs (a101_entries p)).length < 2 ^ w)
    (howner : s.arrs (a101_owner p) = List.ofFn (fun u : Fin n => vertOwner blk u.1))
    (hrn : s.regs r101_n = n)
    (hrm : s.regs r101_m = G.numEdges)
    (hrxLen : s.regs r101_xLen = xSeq.length)
    (hrM : s.regs r101_M = blk.members.length)
    (hrj : s.regs r101_j = k) :
    ∃ (s' : State) (t : ℕ) (recs_suff : List VisionMemberRecord) (rem_cap' : ℕ),
      Exec w (forUp r101_j (.reg r101_M) (alg101MemberStepProg p q δ prog41)) s s' t ∧
      t ≤ 3 + rem * memberLinearCost n G.numEdges q δ C41 +
        600 * (((List.finRange blk.members.length).drop k).map
          (fun j => (memberWorkSize G blk q xSeq j) ^ 2)).sum ∧
      recs_suff.length = rem ∧
      (∀ idx (hidx : idx < rem) (hidx' : idx < recs_suff.length),
        let j : Fin blk.members.length := ⟨k + idx, by omega⟩
        let m := recs_suff[idx]'hidx'
        isValidVisionMemberRecord G X' blk q δ xSeq (blk.members[j.1]'j.2) m = true ∧
        VisionMemberRecordFolioValid blk.wallSec.W δ xSeq (blk.members[j.1]'j.2) m ∧
        m.tildeA_eList = memberTildeAEList G blk xSeq j) ∧
      IsPrefixBuffer (a101_visBuf p) (pfx ++ recs_suff.flatMap VisionMemberRecord.enc) rem_cap' s' ∧
      s'.arrs (a101_memIsInt p) = (recs_pfx ++ recs_suff).map VisionMemberRecord.isInterior ∧
      s'.arrs (a101_memVOf p) = (recs_pfx ++ recs_suff).map VisionMemberRecord.vOf ∧
      s'.arrs (a101_memFolioCode p) = (recs_pfx ++ recs_suff).map VisionMemberRecord.folioCode ∧
      (∀ a < a101_rV p,
        a ≠ a101_visBuf p → a ≠ a101_memIsInt p → a ≠ a101_memVOf p → a ≠ a101_memFolioCode p →
          s'.arrs a = s.arrs a) ∧
      (∀ (reg : ℕ), reg < 56 → s'.regs reg = s.regs reg) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k off pfx rem_cap recs_pfx s with
  | zero =>
    have hk_eq : k = blk.members.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r101_j) (.reg r101_M)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrM, hM_w, h0_w]
    refine ⟨s, 3, [], rem_cap, .while_false hcond, by omega, rfl,
      (fun _ h _ => nomatch h),
      by simpa using hvisBuf,
      by simpa using hmemInt,
      by simpa using hmemVOf,
      by simpa using hmemFCode,
      fun _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < blk.members.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    let j : Fin blk.members.length := ⟨k, hk_lt⟩
    let r := blk.members[k]'hk_lt
    have hr_mem : r ∈ blk.members := List.getElem_mem hk_lt
    have hcond : (Expr.op .lt (.reg r101_j) (.reg r101_M)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrM, hk_w, hM_w, hk_lt, hw]
    have hdrop_r : blk.members.drop k = r :: blk.members.drop (k + 1) :=
      drop_eq_getElem_cons blk.members hk_lt
    have hstream_r :
        AtStream (a101_block p) off
          (r.enc ++ (((blk.members.drop (k + 1)).flatMap Case3MemberRecord.enc) ++ rest)) s := by
      rw [hdrop_r] at hstream
      simpa [List.flatMap_cons, List.append_assoc] using hstream
    have hoff_r_w : off + r.enc.length < 2 ^ w := by
      rw [hdrop_r, List.flatMap_cons, List.length_append] at hoff_w
      omega
    let rem_cap₀ := rem_cap - memberPerCap C41 n G.numEdges
    have hbuf₀ :
        IsPrefixBuffer (a101_visBuf p) pfx
          (memberPerCap C41 n G.numEdges + rem_cap₀) s := by
      unfold IsPrefixBuffer at hvisBuf ⊢
      have hrep : rem_cap = memberPerCap C41 n G.numEdges + rem_cap₀ := by
        dsimp [rem_cap₀]
        have : 1 * memberPerCap C41 n G.numEdges ≤ (rem + 1) * memberPerCap C41 n G.numEdges :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      rwa [← hrep]
    have hpfx_w : pfx.length + memberPerCap C41 n G.numEdges < 2 ^ w := by
      have : 1 * memberPerCap C41 n G.numEdges ≤ (rem + 1) * memberPerCap C41 n G.numEdges :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    rcases alg101MemberStepProg_exec h41 G hx_card blk hC xSeq hx_nd hx_set lists htot_lists
        j (hbd_all j) (((blk.members.drop (k + 1)).flatMap Case3MemberRecord.enc) ++ rest)
        off pfx rem_cap₀ recs_pfx hrecs_len rem
        hw6 h2n_w h2nsq_w hcapE_w hM_w henc_w (hwords_all r hr_mem) hoff_r_w
        hw41 h41_len_w hpfx_w hw_code hw_len hw_word hw_q
        hstream_r hroff hbuf₀ hrvisPos hmemInt hmemVOf hmemFCode
        hG hxSeq hxInd hperim hWH hcor hKInd hisC hdegK hadj hent_w howner
        hrn hrm hrxLen hrj with
      ⟨s₁, t₁, m, hex₁, ht₁, hstream₁, hroff₁, hm_val, hm_fval, hm_eList, hm_len,
        hvisBuf₁, hrvisPos₁, hmemInt₁, hmemVOf₁, hmemFCode₁, harr₁, hreg₁⟩
    have hrj₁ : s₁.regs r101_j = k := by
      rw [hreg₁ r101_j (by decide) (by decide) (by decide), hrj]
    let s₂ := s₁.setReg r101_j (k + 1)
    have hex₂ : Exec w (.assign r101_j (.op .add (.reg r101_j) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj₁, hk_w, hw, hk1_w])
    have harr₂_eq : ∀ a < a101_rV p,
        a ≠ a101_visBuf p → a ≠ a101_memIsInt p → a ≠ a101_memVOf p → a ≠ a101_memFolioCode p →
        s₂.arrs a = s.arrs a := fun a ha h1 h2 h3 h4 => by
      simp [s₂, harr₁ a ha h1 h2 h3 h4]
    have hpfx_rem_w' : (pfx ++ m.enc).length + rem * memberPerCap C41 n G.numEdges < 2 ^ w := by
      rw [List.length_append]
      have : (rem + 1) * memberPerCap C41 n G.numEdges =
          memberPerCap C41 n G.numEdges + rem * memberPerCap C41 n G.numEdges := by ring
      omega
    have hcap_ge' :
        rem * memberPerCap C41 n G.numEdges ≤
          (memberPerCap C41 n G.numEdges - m.enc.length) + rem_cap₀ := by
      dsimp [rem_cap₀]
      have : (rem + 1) * memberPerCap C41 n G.numEdges =
          memberPerCap C41 n G.numEdges + rem * memberPerCap C41 n G.numEdges := by ring
      omega
    rcases ih (k + 1) (by omega) (off + (blk.members[j.1]'j.2).enc.length)
        (by rw [hdrop_r, List.flatMap_cons, List.length_append] at hoff_w
            dsimp [r, j] at hoff_w ⊢; omega)
        (pfx ++ m.enc) ((memberPerCap C41 n G.numEdges - m.enc.length) + rem_cap₀)
        hpfx_rem_w' hcap_ge' (recs_pfx ++ [m]) (by simp [hrecs_len])
        (s := s₂)
        (hstream₁.of_arr_eq rfl)
        (by simp [s₂, State.setReg, hroff₁])
        (hvisBuf₁.of_arr_eq rfl)
        (by simp [s₂, State.setReg, hrvisPos₁])
        (by simp [s₂, hmemInt₁])
        (by simp [s₂, hmemVOf₁])
        (by simp [s₂, hmemFCode₁])
        (by rw [harr₂_eq (a101_G p) (by omega) (by omega) (by omega) (by omega) (by omega), hG])
        (by rw [harr₂_eq (a101_xSeq p) (by omega) (by omega) (by omega) (by omega) (by omega), hxSeq])
        (by rw [harr₂_eq (a101_xInd p) (by omega) (by omega) (by omega) (by omega) (by omega), hxInd])
        (by rw [harr₂_eq (a101_perim p) (by omega) (by omega) (by omega) (by omega) (by omega), hperim])
        (by rw [harr₂_eq (a101_WH p) (by omega) (by omega) (by omega) (by omega) (by omega), hWH])
        (by rw [harr₂_eq (a101_corners p) (by omega) (by omega) (by omega) (by omega) (by omega), hcor])
        (by rw [harr₂_eq (a101_KInd p) (by omega) (by omega) (by omega) (by omega) (by omega), hKInd])
        (by rw [harr₂_eq (a101_isCorner p) (by omega) (by omega) (by omega) (by omega) (by omega), hisC])
        (by rw [harr₂_eq (a101_degK p) (by omega) (by omega) (by omega) (by omega) (by omega), hdegK])
        (hadj.of_arrs_eq
          (harr₂_eq (a101_start p) (by omega) (by omega) (by omega) (by omega) (by omega))
          (harr₂_eq (a101_end p) (by omega) (by omega) (by omega) (by omega) (by omega))
          (harr₂_eq (a101_entries p) (by omega) (by omega) (by omega) (by omega) (by omega)))
        (by rw [harr₂_eq (a101_entries p) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hent_w)
        (by rw [harr₂_eq (a101_owner p) (by omega) (by omega) (by omega) (by omega) (by omega), howner])
        (by simp [s₂, State.setReg, hreg₁ r101_n (by decide) (by decide) (by decide), hrn])
        (by simp [s₂, State.setReg, hreg₁ r101_m (by decide) (by decide) (by decide), hrm])
        (by simp [s₂, State.setReg, hreg₁ r101_xLen (by decide) (by decide) (by decide), hrxLen])
        (by simp [s₂, State.setReg, hreg₁ r101_M (by decide) (by decide) (by decide), hrM])
        (by simp [s₂]) with
      ⟨s₃, t₃, recs_suff, rem_cap', hex₃, ht₃, hlen_suff, hprops_suff, hvisBuf₃,
        hmemInt₃, hmemVOf₃, hmemFCode₃, harr₃, hreg₃⟩
    have hdrop_fin :
        (List.finRange blk.members.length).drop k =
          j :: (List.finRange blk.members.length).drop (k + 1) := by
      have hlen_fin : k < (List.finRange blk.members.length).length := by simp [hk_lt]
      rw [drop_eq_getElem_cons _ hlen_fin, List.getElem_finRange]
      rfl
    have ht_step :
        3 + (t₁ + 4) + t₃ ≤
          3 + (rem + 1) * memberLinearCost n G.numEdges q δ C41 +
            600 * (((List.finRange blk.members.length).drop k).map
              (fun j => (memberWorkSize G blk q xSeq j) ^ 2)).sum := by
      rw [hdrop_fin, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
      omega
    refine ⟨s₃, 3 + (t₁ + 4) + t₃, m :: recs_suff, rem_cap',
      .while_true hcond (by omega) (.seq hex₁ hex₂) hex₃,
      ht_step, by simp [hlen_suff],
      ?_,
      by simpa [List.flatMap_cons, List.append_assoc] using hvisBuf₃,
      by simpa [List.append_assoc] using hmemInt₃,
      by simpa [List.append_assoc] using hmemVOf₃,
      by simpa [List.append_assoc] using hmemFCode₃,
      fun a ha h1 h2 h3 h4 =>
        (harr₃ a ha h1 h2 h3 h4).trans (harr₂_eq a ha h1 h2 h3 h4),
      fun reg hlt => by
        rw [hreg₃ reg hlt]
        dsimp only [s₂]
        rw [State.setReg_regs_ne _ _ (show reg ≠ r101_j by omega),
          hreg₁ reg (by omega) (by omega) (by omega)]⟩
    intro idx hidx hidx_len
    cases idx with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      exact ⟨hm_val, hm_fval, hm_eList⟩
    | succ idx' =>
      have hidx' : idx' < rem := Nat.lt_of_succ_lt_succ hidx
      have hidx_len' : idx' < recs_suff.length := Nat.lt_of_succ_lt_succ hidx_len
      have hsub := hprops_suff idx' hidx' hidx_len'
      dsimp only at hsub ⊢
      have hk1_lt : (k + 1) + idx' < blk.members.length := by omega
      have hget_eq : blk.members[k + (idx' + 1)]'(by omega) =
          blk.members[(k + 1) + idx']'hk1_lt := by congr 1; omega
      have hj_eq : (⟨k + (idx' + 1), by omega⟩ : Fin blk.members.length) =
          ⟨(k + 1) + idx', hk1_lt⟩ := Fin.ext (by dsimp; omega)
      simp only [List.getElem_cons_succ, hget_eq, hj_eq]
      exact hsub

/-! ### Section 4: Complete Algorithm (10.1) Program (`alg101Prog`, `alg101Prog_exec`) -/

/-- Complete Word RAM program for **Graph Minors XIII, Algorithm (10.1)** (page 106):
1. Runs `alg101PrePassProg p h` to parse the Case (iii) block and build the compass CSR graph
   and vertex/edge lookup tables.
2. Runs `alg101InitVisProg p C41` to initialize `a101_visBuf p` and member summary arrays.
3. Iterates `alg101MemberStepProg p q δ prog41` over all $M$ members. -/
def alg101Prog (p q δ h C41 : ℕ) (prog41 : Cmd) : Cmd :=
  .seq (alg101PrePassProg p h)
    (.seq (alg101InitVisProg p C41)
      (forUp r101_j (.reg r101_M) (alg101MemberStepProg p q δ prog41)))

/-- Total quadratic time constant $C_{101}(q, \delta, C_{41})$ for `alg101Prog`. -/
def alg101TimeConst (q δ C41 : ℕ) : ℕ :=
  600 * (q + 10) ^ 2 + 36 * C41 + 4000 +
    ((maxFolioEncLen101 q δ + 1) * (4 * maxFolioEncWord q δ + 10) + 4 * (q + 4))

set_option maxHeartbeats 800000 in
theorem alg101Prog_exec {w n p q q_C δ ω c41 C41 : ℕ} {prog41 : Cmd}
    (h41 : Alg41ProgSpec p q δ ω prog41 c41 C41)
    (G : MultiDigraph n) {X' : Finset (Fin n)} (hx_card : X'.card ≤ q)
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q_C X'.toNatSet blk.toGMWall blk.toSociety blk.toDivision)
    (hbd_all : ∀ j : Fin blk.members.length,
      isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true →
      MemberBranchDecompValid G X' ω (blk.members[j.1]'j.2))
    (block : List ℕ) (hparse_blk : parseCase3Block (G.deleteVertices X') X' block = some blk)
    (h2nsq_w : 2 + 6 * (n * n) < 2 ^ w) (hN_w : 24 * (n + G.numEdges + 1) < 2 ^ w)
    (hw41 : wordSize c41 (n + G.numEdges + 1) ≤ w) (hC41_w : C41 < 2 ^ w)
    (hvis_cap_w : (2 + n) + (n + G.numEdges + 1) * memberPerCap C41 n G.numEdges < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w) (hw_len : maxFolioEncLen101 q δ < 2 ^ w)
    (hw_word : maxFolioEncWord q δ + 1 < 2 ^ w) (hw_q : q + 4 < 2 ^ w)
    {s : State} (hG : s.arrs (a101_G p) = G.enc) (hX : s.arrs (a101_X p) = bitSetList X')
    (hblock : s.arrs (a101_block p) = block) :
    ∃ (s' : State) (t : ℕ) (vOut : ParsedVisionOutput G X' blk q δ),
      Exec w (alg101Prog p q δ blk.wallSec.h C41 prog41) s s' t ∧
      t ≤ alg101TimeConst q δ C41 * (n + G.numEdges + 1) ^ 2 ∧
      parseVisionOutput G X' blk q δ (s'.arrs (a101_visBuf p)) = some vOut ∧
      vOut.xSeq = xSeqOf X' ∧
      (∀ (j : Fin blk.members.length)
        (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
        (folioOut : ParsedFolioAndModels
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
        parseFolioAndModelsFull
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
          δ (vOut.recordAt j).folioWords = some folioOut →
        IsDeltaFolioRep δ
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
          folioOut.folio) ∧
      s'.regs r101_n = n ∧ s'.regs r101_M = blk.members.length ∧
      s'.arrs (a101_W_br p) =
        (List.finRange (elemWallNumVerts blk.wallSec.h)).map
          (fun u => (blk.wallSec.W.branchVert u).1) ∧
      s'.arrs (a101_W_brOf p) = List.ofFn (wallBrOf blk.wallSec.W) ∧
      s'.arrs (a101_W_edgeOf p) = List.ofFn (wallEdgeOf blk.wallSec.W) ∧
      s'.arrs (a101_memIsInt p) = vOut.records.map VisionMemberRecord.isInterior ∧
      s'.arrs (a101_memVOf p) = vOut.records.map VisionMemberRecord.vOf ∧
      s'.arrs (a101_memFolioCode p) = vOut.records.map VisionMemberRecord.folioCode ∧
      (∀ a < alg105ArrBase p, s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < 50 → s'.regs r = s.regs r) := by
  let N := n + G.numEdges + 1
  have hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety := by
    rw [delGraph_eq]; exact hC.isWallSociety
  have hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision := hC.isRuralDivision
  have hDiv : GM13.IsSocietyDivision blk.toSociety blk.toDivision := hRD.1
  have hw18 : 18 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm_w : G.numEdges < 2 ^ w := by omega
  have hact_le_m : G.numActivePairs ≤ G.numEdges := G.numActivePairs_le_numEdges
  have hact_le_nsq : G.numActivePairs ≤ n * n := G.numActivePairs_le_sq
  have hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w := by omega
  have hwall_len_le : blk.wallSec.W.encList.length ≤ 3 + 3 * n :=
    blk.wallSec.W.length_encList_le blk.wallSec.hW
  have hKVL_le : blk.K_vList.length ≤ n := blk.hK_v_len
  have hKEL_le : blk.K_eList.length ≤ G.numEdges :=
    le_trans blk.hK_e_len (G.numEdges_deleteVertices_le X')
  have hM_le : blk.members.length ≤ n + G.numEdges + 1 := by
    have := blk.hmembers_len; have := G.numEdges_deleteVertices_le X'; omega
  have hflat_mem_le : (blk.members.flatMap Case3MemberRecord.enc).length ≤ 14 * (n + G.numEdges + 1) :=
    blk.length_flatMap_member_enc_le hDiv
  have hper_ge : 18 ≤ memberPerCap C41 n G.numEdges := by unfold memberPerCap; omega
  have hper_w : memberPerCap C41 n G.numEdges < 2 ^ w := by
    have := Nat.mul_le_mul_right (memberPerCap C41 n G.numEdges) (show 1 ≤ n + G.numEdges + 1 by omega)
    omega
  have h41_len_w : C41 * (n + G.numEdges + 1) < 2 ^ w := by
    have : C41 * (n + G.numEdges + 1) ≤ memberPerCap C41 n G.numEdges := by unfold memberPerCap; omega
    omega
  rcases eq_encCase3Block_append_of_parseCase3Block hparse_blk with ⟨rest, hblock_eq⟩
  have hblock_split :
      s.arrs (a101_block p) =
        blk.wallSec.W.encList ++
          ((blk.K_vList.length :: blk.K_vList) ++
            (blk.K_eList.length :: encEdgeTriples blk.K_eList) ++
            blk.corners ++
            (blk.members.length :: blk.members.flatMap Case3MemberRecord.enc) ++ rest) := by
    rw [hblock, hblock_eq]; unfold encCase3Block; simp [List.append_assoc]
  -- 1. Pre-pass Part 1 & Part 2
  rcases alg101PrePassPart1Prog_exec G X' blk
      ((blk.K_vList.length :: blk.K_vList) ++
        (blk.K_eList.length :: encEdgeTriples blk.K_eList) ++
        blk.corners ++
        (blk.members.length :: blk.members.flatMap Case3MemberRecord.enc) ++ rest)
      hw3 (by omega) hm3_w hm_w (by omega) hG hX hblock_split with
    ⟨s₁, t₁, hex₁, ht₁, hrn₁, hrm₁, hrxLen₁, hroff₁,
      hG₁, _, hxSeq₁, hxInd₁, hWbr₁, hWbrOf₁, hWedgeOf₁, hperim₁, hWH₁,
      hstream₁, harr₁, hreg₁⟩
  have hoff₂_w :
      blk.wallSec.W.encList.length + (1 + blk.K_vList.length) +
        (1 + 3 * blk.K_eList.length) + 4 + 1 +
        (blk.members.flatMap Case3MemberRecord.enc).length < 2 ^ w := by omega
  rcases alg101PrePassPart2Prog_exec G blk hDiv rest
      hw6 hn_w hm3_w (by omega) (by omega) hoff₂_w
      hG₁ hrn₁ hroff₁ hstream₁ with
    ⟨s₂, t₂, hex₂, ht₂, hrM₂, hroff₂, hstream₂,
      hKV₂, hKE₂, hcor₂, hKInd₂, hisC₂, hdegK₂, hadj₂, hent_len₂, htot_lists,
      howner₂, harr₂, hreg₂⟩
  -- 3. Vision Buffer & Summary Initialization
  let xSeq := xSeqOf X'
  have hx_nd : xSeq.Nodup := nodup_xSeqOf X'
  have hx_set : xSeq.toFinset = X'.image Fin.val := toFinset_xSeqOf X'
  have hx_lt : ∀ x ∈ xSeq, x < n := fun _ hx => mem_xSeqOf_lt X' hx
  have hx_len_le : xSeq.length ≤ n := length_xSeqPrefix_le X'
  have hcap_vis_w :
      (2 + xSeq.length) + blk.members.length * memberPerCap C41 n G.numEdges < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ hM_le)) hvis_cap_w
  rcases alg101InitVisProg_exec xSeq hx_lt hw18 hn_w hm_w (by omega)
      hC41_w hcap_vis_w hper_w (s := s₂)
      (by rw [harr₂ (a101_xSeq p) (by omega), hxSeq₁])
      (by rw [hreg₂ r101_n (by decide), hrn₁])
      (by rw [hreg₂ r101_m (by decide), hrm₁])
      (by rw [hreg₂ r101_xLen (by decide), hrxLen₁])
      hrM₂ with
    ⟨s₃, t₃, hex₃, ht₃, hvisBuf₃, hrvisPos₃, hmemInt₃, hmemVOf₃, hmemFCode₃, hrj₃, harr₃, hreg₃⟩
  -- 4. Member Iteration Loop
  have harr_s₃_s₂ : ∀ a < a101_memIsInt p, a ≠ a101_visBuf p → s₃.arrs a = s₂.arrs a :=
    fun a ha hne => harr₃ a hne (by omega) (by omega) (by omega)
  have hreg_s₃_s₂ : ∀ (r : ℕ), r < r101_base → r ≠ r101_visPos → r ≠ r101_j → s₃.regs r = s₂.regs r :=
    hreg₃
  have hwords_all : ∀ r ∈ blk.members, ∀ x ∈ r.enc, x < 2 ^ w := fun r hr x hx =>
    lt_of_le_of_lt (blk.member_enc_le r hr x hx) (by omega)
  rcases alg101MemberLoop_aux h41 G hx_card blk hC hbd_all xSeq hx_nd hx_set
      (edgeNeighbors (edgeListOf (G.deleteVertices (Z_notK blk)).toSimpleGraph))
      (le_trans htot_lists (Nat.mul_le_mul_left 2 hact_le_m)) rest
      hw6 (by omega) h2nsq_w (by omega) (by omega) hm3_w hwords_all
      hw41 h41_len_w hw_code hw_len hw_word hw_q
      blk.members.length 0 (by omega)
      (blk.wallSec.W.encList.length + (1 + blk.K_vList.length) +
        (1 + 3 * blk.K_eList.length) + 4 + 1)
      (by simpa using hoff₂_w) ((xSeq.length :: xSeq) ++ [blk.members.length])
      (blk.members.length * memberPerCap C41 n G.numEdges)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (le_rfl) [] rfl (s := s₃)
      (hstream₂.of_arr_eq (harr_s₃_s₂ (a101_block p) (by omega) (by omega)))
      (by rw [hreg_s₃_s₂ r101_off (by decide) (by decide) (by decide), hroff₂])
      hvisBuf₃ hrvisPos₃ (by simpa using hmemInt₃) (by simpa using hmemVOf₃)
      (by simpa using hmemFCode₃)
      (by rw [harr_s₃_s₂ (a101_G p) (by omega) (by omega), harr₂ (a101_G p) (by omega), hG₁])
      (by rw [harr_s₃_s₂ (a101_xSeq p) (by omega) (by omega), harr₂ (a101_xSeq p) (by omega), hxSeq₁])
      (by rw [harr_s₃_s₂ (a101_xInd p) (by omega) (by omega), harr₂ (a101_xInd p) (by omega), hxInd₁])
      (by rw [harr_s₃_s₂ (a101_perim p) (by omega) (by omega), harr₂ (a101_perim p) (by omega), hperim₁])
      (by rw [harr_s₃_s₂ (a101_WH p) (by omega) (by omega), harr₂ (a101_WH p) (by omega), hWH₁])
      (by rw [harr_s₃_s₂ (a101_corners p) (by omega) (by omega), hcor₂])
      (by rw [harr_s₃_s₂ (a101_KInd p) (by omega) (by omega), hKInd₂])
      (by rw [harr_s₃_s₂ (a101_isCorner p) (by omega) (by omega), hisC₂])
      (by rw [harr_s₃_s₂ (a101_degK p) (by omega) (by omega), hdegK₂])
      (hadj₂.of_arrs_eq (harr_s₃_s₂ (a101_start p) (by omega) (by omega))
        (harr_s₃_s₂ (a101_end p) (by omega) (by omega))
        (harr_s₃_s₂ (a101_entries p) (by omega) (by omega)))
      (by rw [harr_s₃_s₂ (a101_entries p) (by omega) (by omega)]; exact lt_of_le_of_lt hent_len₂ (by omega))
      (by rw [harr_s₃_s₂ (a101_owner p) (by omega) (by omega), howner₂])
      (by rw [hreg_s₃_s₂ r101_n (by decide) (by decide) (by decide), hreg₂ r101_n (by decide), hrn₁])
      (by rw [hreg_s₃_s₂ r101_m (by decide) (by decide) (by decide), hreg₂ r101_m (by decide), hrm₁])
      (by rw [hreg_s₃_s₂ r101_xLen (by decide) (by decide) (by decide), hreg₂ r101_xLen (by decide), hrxLen₁])
      (by rw [hreg_s₃_s₂ r101_M (by decide) (by decide) (by decide), hrM₂])
      hrj₃ with
    ⟨s₄, t₄, records, rem_cap', hex₄, ht₄, hrec_len, hrec_props, hvisBuf₄,
      hmemInt₄, hmemVOf₄, hmemFCode₄, harr₄, hreg₄⟩
  simp only [Nat.zero_add, List.drop_zero, List.nil_append] at ht₄ hrec_props hmemInt₄ hmemVOf₄ hmemFCode₄
  -- 5. Assemble ParsedVisionOutput
  have hmap_eList :
      records.map VisionMemberRecord.tildeA_eList =
        (List.finRange blk.members.length).map (memberTildeAEList G blk xSeq) := by
    apply List.ext_getElem (by simp [hrec_len])
    intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_finRange]
    exact (hrec_props i (by simpa using hi₂) (by simpa [hrec_len] using hi₂)).2.2
  let vOut : ParsedVisionOutput G X' blk q δ :=
    { xSeq := xSeq, records := records, hx_nodup := hx_nd, hx_set := hx_set
      hmembers_ne := blk.members_ne_nil_of_isRuralDivision hWS hRD, hrecords_len := hrec_len
      hrecords_valid := fun j => (hrec_props j.1 j.2 (by rw [hrec_len]; exact j.2)).1
      hedges_nodup := by rw [hmap_eList]; exact flatten_memberTildeAEList_nodup G blk hRD hx_set
      hedges_cover := by rw [hmap_eList]; exact flatten_memberTildeAEList_cover G blk hWS hRD hx_set }
  have hvis_arr :
      s₄.arrs (a101_visBuf p) =
        encVisionOutput vOut.xSeq vOut.records ++ List.replicate rem_cap' 0 := by
    unfold IsPrefixBuffer at hvisBuf₄
    rw [hvisBuf₄]; unfold encVisionOutput; dsimp [vOut]; rw [hrec_len]; simp [List.append_assoc]
  have hparse_vis :
      parseVisionOutput G X' blk q δ (s₄.arrs (a101_visBuf p)) = some vOut := by
    rw [hvis_arr]; exact parseVisionOutput_encVisionOutput vOut (List.replicate rem_cap' 0)
  have hrep_out :
      ∀ (j : Fin blk.members.length)
        (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
        (folioOut : ParsedFolioAndModels
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
        parseFolioAndModelsFull
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
          δ (vOut.recordAt j).folioWords = some folioOut →
        IsDeltaFolioRep δ
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
          folioOut.folio := by
    intro j hInt folioOut hp
    exact (hrec_props j.1 j.2 (by rw [hrec_len]; exact j.2)).2.1 hInt folioOut hp
  -- 6. Total time bound
  have hsum_sq := sum_memberWorkSize_sq_le G blk hWS hRD hx_set (q := q)
  have ht_total :
      (t₁ + t₂) + (t₃ + t₄) ≤ alg101TimeConst q δ C41 * N ^ 2 := by
    let F := (maxFolioEncLen101 q δ + 1) * (4 * maxFolioEncWord q δ + 10) + 4 * (q + 4)
    have hN_pos : 1 ≤ N := by dsimp [N]; omega
    have hN_le_sq : N ≤ N * N := Nat.le_mul_self N
    have ht12_sq : t₁ + t₂ ≤ 1560 * (N * N) :=
      le_trans (show t₁ + t₂ ≤ 1560 * N by dsimp [N] at *; omega) (Nat.mul_le_mul_left 1560 hN_le_sq)
    have hM_cap : blk.members.length * memberPerCap C41 n G.numEdges ≤ N * ((C41 + 18) * N) := by
      unfold memberPerCap
      have h1 : blk.members.length * ((C41 + 18) * N) ≤ N * ((C41 + 18) * N) :=
        Nat.mul_le_mul_right ((C41 + 18) * N) hM_le
      have h2 : (C41 + 18) * N = C41 * (n + G.numEdges + 1) + 18 * (n + G.numEdges + 1) := by
        dsimp [N]; ring
      rw [← h2]
      exact h1
    have ht3_le : t₃ ≤ N * ((C41 + 18) * N) + 75 * (N * N) := by
      have : (2 + xSeq.length) + 18 * xSeq.length + 3 * blk.members.length + 50 ≤ 75 * N := by
        dsimp [N] at *; omega
      have := le_trans this (Nat.mul_le_mul_left 75 hN_le_sq); omega
    have hM_lin :
        blk.members.length * memberLinearCost n G.numEdges q δ C41 ≤
          N * (35 * (C41 * N) + 1950 * N + F) := by
      simpa [memberLinearCost, N, F] using
        Nat.mul_le_mul_right (memberLinearCost n G.numEdges q δ C41) hM_le
    have hF_sq : N * F ≤ F * (N * N) := by
      rw [Nat.mul_comm N F]; exact Nat.mul_le_mul_left F hN_le_sq
    have h600_sq :
        600 * (((List.finRange blk.members.length).map
          (fun j => (memberWorkSize G blk q xSeq j) ^ 2)).sum) ≤
          600 * ((q + 10) ^ 2 * (N * N)) := by
      have h1 := Nat.mul_le_mul_left 600 hsum_sq
      have h2 : ((q + 10) * (n + G.numEdges + 1)) ^ 2 = (q + 10) ^ 2 * (N * N) := by
        dsimp [N]; ring
      rwa [h2] at h1
    have h3_sq : 3 ≤ 3 * (N * N) := by have := le_trans hN_pos hN_le_sq; omega
    have halg_eq :
        alg101TimeConst q δ C41 * N ^ 2 =
          600 * ((q + 10) ^ 2 * (N * N)) + N * ((C41 + 18) * N) +
            N * (35 * (C41 * N) + 1950 * N) + F * (N * N) + 2032 * (N * N) := by
      change (600 * (q + 10) ^ 2 + 36 * C41 + 4000 + F) * N ^ 2 = _; ring
    rw [halg_eq]
    have hN_dist := Nat.mul_add N (35 * (C41 * N) + 1950 * N) F
    omega
  have harr_s₄_s₁ : ∀ a < a101_KV p, a ≠ a101_visBuf p → s₄.arrs a = s₁.arrs a :=
    fun a ha hne => by
      rw [harr₄ a (by omega) hne (by omega) (by omega) (by omega),
        harr_s₃_s₂ a (by omega) hne, harr₂ a ha]
  refine ⟨s₄, (t₁ + t₂) + (t₃ + t₄), vOut, .seq (.seq hex₁ hex₂) (.seq hex₃ hex₄), ht_total,
    hparse_vis, rfl, hrep_out,
    by rw [hreg₄ r101_n (by decide), hreg_s₃_s₂ r101_n (by decide) (by decide) (by decide),
         hreg₂ r101_n (by decide), hrn₁],
    by rw [hreg₄ r101_M (by decide), hreg_s₃_s₂ r101_M (by decide) (by decide) (by decide), hrM₂],
    by rw [harr_s₄_s₁ (a101_W_br p) (by omega) (by omega), hWbr₁],
    by rw [harr_s₄_s₁ (a101_W_brOf p) (by omega) (by omega), hWbrOf₁],
    by rw [harr_s₄_s₁ (a101_W_edgeOf p) (by omega) (by omega), hWedgeOf₁],
    hmemInt₄, hmemVOf₄, hmemFCode₄,
    fun a ha => by rw [harr_s₄_s₁ a (by omega) (by omega), harr₁ a ha],
    fun r hr => by
      rw [hreg₄ r (by omega), hreg_s₃_s₂ r (by omega) (by omega) (by omega),
        hreg₂ r (by omega), hreg₁ r hr]⟩

end GraphMinor.Compute
