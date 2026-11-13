module

public import GraphMinor.Compute.Algorithm101

/-!
# Reading the wall input for Graph Minors XIII, (10.1)

A wall is supplied with its vertex set and perimeter bitsets. The perimeter is
the circuit bounding the infinite region in the elementary drawing (XIII,
Section 7, page 88). These are arrays representing the given wall, not answers
to the vision problem. The parser therefore uses one program for all heights.
It reads the subdivision and builds the same vertex lookup arrays as the
height-specific parser, while preserving the two wall bitsets.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-- Height-independent wall-input pre-pass for XIII (10.1), pages 106–107.
The supplied wall vertex and perimeter arrays remain available to the member loop. -/
def alg101WallInputPrePass (p : ℕ) : Cmd :=
  .seq (sumEdgeMultProg (a101_G p) r101_n)
    (.seq (.assign r101_m (.reg r101_xLen))
      (.seq (buildXSeqProg (a101_X p) (a101_buf p) (a101_xSeq p) r101_n r101_xLen r101_base)
        (.seq (buildListIndProg (a101_xSeq p) (a101_xInd p) r101_xLen r101_n r101_base)
          (.seq (.assign r101_off (.const 0))
            (readWallSectionProg (a101_block p)
              (a101_W_br p) (a101_W_brOf p) (a101_W_edgeOf p)
              r101_off r101_n 64 65 66 r101_base)))))

/-- The uniform pre-pass reads the supplied wall and root set in linear time,
with the wall's own vertex and perimeter arrays retained as part of its input. -/
theorem alg101WallInputPrePass_exec {w n p : ℕ}
    (G : MultiDigraph n) (X' : Finset (Fin n))
    (blk : ParsedCase3Block (G.deleteVertices X') X') (rem : List ℕ)
    (hw3 : 3 < 2 ^ w) (h2n_w : 2 * n + 4 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w)
    (hwall_len_w : blk.wallSec.W.encList.length < 2 ^ w)
    {s : State}
    (hG : s.arrs (a101_G p) = G.enc)
    (hX : s.arrs (a101_X p) = bitSetList X')
    (hblock : s.arrs (a101_block p) = blk.wallSec.W.encList ++ rem)
    (hperim : s.arrs (a101_perim p) = bitSetList blk.wallSec.W.perimFinset)
    (hWH : s.arrs (a101_WH p) = bitSetList blk.wallSec.W.vertexFinset) :
    ∃ s' t,
      Exec w (alg101WallInputPrePass p) s s' t ∧
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
  have hrn₆ : s₆.regs r101_n = n := by
    rw [hreg₆ r101_n (by decide) (by decide) (by decide) (by decide) (by decide), hrn₅]
  have hperim₆ : s₆.arrs (a101_perim p) = bitSetList blk.wallSec.W.perimFinset := by
    rw [harr₆ (a101_perim p) (by omega) (by omega) (by omega)]
    simp [s₅, harr₄ (a101_perim p) (by omega),
      harr₃ (a101_perim p) (by omega) (by omega), s₂, harr₁, hperim]
  have hWH₆ : s₆.arrs (a101_WH p) = bitSetList blk.wallSec.W.vertexFinset := by
    rw [harr₆ (a101_WH p) (by omega) (by omega) (by omega)]
    simp [s₅, harr₄ (a101_WH p) (by omega),
      harr₃ (a101_WH p) (by omega) (by omega), s₂, harr₁, hWH]
  have harr_prev : ∀ a < a101_perim p, s₆.arrs a = s₆.arrs a := fun _ _ => rfl
  have hreg_prev : ∀ r < r101_base, s₆.regs r = s₆.regs r := fun _ _ => rfl
  refine ⟨s₆, t₁ + (2 + (t₃ + (t₄ + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
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
    hperim₆,
    hWH₆,
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


end GraphMinor.Compute
