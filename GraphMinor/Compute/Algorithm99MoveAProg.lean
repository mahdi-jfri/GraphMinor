module

public import GraphMinor.Compute.Algorithm99MoveBlock
public import GraphMinor.Compute.Algorithm101Steps
public import GraphMinor.Compute.BitSet

/-!
# The program that moves output (a) of steps (5) to (7) of (9.9) to `G`

Output (a) of steps (5) to (7) of Algorithm (9.9) (Graph Minors XIII, page 104) is a block of
the renumbered graph `G'` (`IsCase3StepsOutputA`). The program `alg99MoveAProg` renames it in
place along `orig` (`mvBlock`), and copies the renamed part to the output array. By
`Algorithm99MoveA`, the decoder `case3Decoder` reads from the result the objects of output (iii)
of (9.9) for `G` and `orig(X)`.

* `renamedBlock_eq_movedBlock`: when array `o` stores `orig`, the words that `mvBlock` writes
  are the code `p.movedBlock` of the renamed parsed block.
* `alg99MoveAProg_exec`: the program, from a block that parses to `p`.
* `isAlg99OutputIII_of_case3StepsOutputA`: the conditions of output (iii) of (9.9), from
  output (a), for a valid state of (9.9).
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Function GraphMinor.GM09 GraphMinor.GM13 GraphMinor.Transport

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

variable {v n : ℕ} {G' : MultiDigraph v} {G : MultiDigraph n} {X : Finset (Fin v)}
  {orig : Fin v → Fin n}

/-- The array that stores `orig`. -/
def origList (orig : Fin v → Fin n) : List ℕ := List.ofFn (fun j => (orig j).1)

theorem origList_getD {x : ℕ} (hx : x < v) :
    (origList orig).getD x 0 = (orig ⟨x, hx⟩).1 := by
  simp [origList, hx]

theorem origList_getD_eq_origVertexEmb (hinj : Injective orig) {x : ℕ} (hx : x < v) :
    (origList orig).getD x 0 = origVertexEmb orig hinj x := by
  rw [origList_getD hx]
  exact (origVertexEmb_apply_val orig hinj ⟨x, hx⟩).symm

theorem lt_of_isDelGraphVert {m : ℕ} {Y : Finset (Fin m)} {x : ℕ}
    (h : isDelGraphVert m Y x = true) : x < m := by
  unfold isDelGraphVert at h
  split_ifs at h with hx
  · exact hx

/-! ### Every word of the renamed block is a word of the block or a renamed word -/

section Words

variable {φ : ℕ → ℕ}

theorem mem_encEdgeTriples_map {y : ℕ} :
    ∀ {es : List (ℕ × ℕ × ℕ)}, y ∈ encEdgeTriples (es.map (mvTriple φ)) →
      (∃ x, y = φ x) ∨ y ∈ encEdgeTriples es
  | [], h => by simp [encEdgeTriples] at h
  | ⟨a, b, k⟩ :: es, h => by
    simp only [List.map_cons, mvTriple, encEdgeTriples, List.mem_cons] at h ⊢
    rcases h with rfl | rfl | rfl | h
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inl ⟨b, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rcases mem_encEdgeTriples_map h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

theorem mem_mvRunsCode_map {y : ℕ} :
    ∀ {Ls : List (List ℕ)}, y ∈ mvRunsCode (Ls.map (List.map φ)) →
      (∃ x, y = φ x) ∨ y ∈ mvRunsCode Ls
  | [], h => by simp [mvRunsCode] at h
  | l :: Ls, h => by
    simp only [mvRunsCode, List.map_cons, List.flatMap_cons, List.mem_append, List.mem_cons,
      List.length_map, List.mem_map] at h ⊢
    rcases h with (rfl | ⟨x, -, rfl⟩) | h
    · exact Or.inr (Or.inl (Or.inl rfl))
    · exact Or.inl ⟨x, rfl⟩
    · rcases mem_mvRunsCode_map (Ls := Ls) (by simpa [mvRunsCode] using h) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (by simpa [mvRunsCode] using h'))

theorem mem_enc_rename {y : ℕ} {rec : Case3MemberRecord}
    (h : y ∈ (rec.rename φ (mvTriple φ)).enc) : (∃ x, y = φ x) ∨ y ∈ rec.enc := by
  have hT := @mem_encEdgeTriples_map φ y rec.eList
  simp only [Case3MemberRecord.enc, Case3MemberRecord.rename, List.length_map, List.cons_append,
    List.mem_cons, List.mem_append, List.mem_map] at h hT ⊢
  aesop

theorem mem_renamedEncList {h v : ℕ} {A : MultiDigraph v} {W : WallOfHeight h A} {y : ℕ}
    (hy : y ∈ W.renamedEncList φ) : (∃ x, y = φ x) ∨ y ∈ W.encList := by
  rw [WallOfHeight.encList_eq_runs]
  unfold WallOfHeight.renamedEncList at hy
  rw [List.mem_append, List.mem_append] at hy
  rw [List.mem_append, List.mem_append]
  rcases hy with (h1 | h2) | h3
  · exact Or.inr (Or.inl (Or.inl h1))
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h2
    exact Or.inl ⟨x, rfl⟩
  · rcases mem_mvRunsCode_map h3 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')

/-- Every word of the renamed block is a word of the block or a value of `φ`. -/
theorem mem_renamedBlock {h v : ℕ} {A : MultiDigraph v} {W : WallOfHeight h A}
    {Kv : List ℕ} {Ke : List (ℕ × ℕ × ℕ)} {c : List ℕ} {ms : List Case3MemberRecord} {y : ℕ}
    (hy : y ∈ renamedBlock φ W Kv Ke c ms) :
    (∃ x, y = φ x) ∨ y ∈ encCase3Block W Kv Ke c ms := by
  unfold renamedBlock at hy
  unfold encCase3Block
  simp only [List.mem_append] at hy ⊢
  rcases hy with (((h1 | h2) | h3) | h4) | h5
  · rcases mem_renamedEncList h1 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl h'))))
  · rcases List.mem_cons.mp h2 with rfl | h2
    · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (by simp)))))
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h2
      exact Or.inl ⟨x, rfl⟩
  · rcases List.mem_cons.mp h3 with rfl | h3
    · exact Or.inr (Or.inl (Or.inl (Or.inr (by simp))))
    · rcases mem_encEdgeTriples_map h3 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl (Or.inl (Or.inr (List.mem_cons_of_mem _ h'))))
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h4
    exact Or.inl ⟨x, rfl⟩
  · rcases List.mem_cons.mp h5 with rfl | h5
    · exact Or.inr (Or.inr (by simp))
    · obtain ⟨rec', hrec', hy'⟩ := List.mem_flatMap.mp h5
      obtain ⟨rec, hrec, rfl⟩ := List.mem_map.mp hrec'
      rcases mem_enc_rename hy' with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨rec, hrec, h'⟩)))

theorem length_renamedBlock {h v : ℕ} {A : MultiDigraph v} (W : WallOfHeight h A)
    (Kv : List ℕ) (Ke : List (ℕ × ℕ × ℕ)) (c : List ℕ) (ms : List Case3MemberRecord) :
    (renamedBlock φ W Kv Ke c ms).length = (encCase3Block W Kv Ke c ms).length := by
  have hW : (W.renamedEncList φ).length = W.encList.length := by
    rw [WallOfHeight.encList_eq_runs]
    simp [WallOfHeight.renamedEncList, length_mvRunsCode_map]
  have hM : ∀ L : List Case3MemberRecord,
      ((L.map (Case3MemberRecord.rename φ (mvTriple φ))).flatMap Case3MemberRecord.enc).length =
        (L.flatMap Case3MemberRecord.enc).length := by
    intro L
    induction L with
    | nil => rfl
    | cons rec L ih =>
      simp only [List.map_cons, List.flatMap_cons, List.length_append, ih,
        length_enc_memberRecord, Case3MemberRecord.rename, List.length_map]
  simp only [renamedBlock, encCase3Block, List.length_append, List.length_cons, hW, hM,
    List.length_map, length_encEdgeTriples]

end Words

/-! ### Output (a) gives output (iii) of (9.9) -/

/-- For a valid state, the edges of `G' = (G_i \ X) ∪ H_i` between `u` and `w` are none or all
of those of `G` between `orig u` and `orig w`. -/
theorem Alg99Iter.IsValid.edgeMult_wallUnion {h' s : ℕ} {st : Alg99Iter h' G}
    (hst : st.IsValid s) (X : Finset (Fin st.v)) (u w : Fin st.v) :
    (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).edgeMult u w = 0 ∨
      (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).edgeMult u w =
        G.edgeMult (st.orig u) (st.orig w) := by
  rw [WallOfHeight.wallUnionMultiDigraph_edgeMult]
  split_ifs
  · exact hst.edgeMult_eq u w
  · exact Or.inl rfl

/-- **Output (a) gives output (iii) of (9.9).** Let `st` be a valid state of (9.9), `X` the set
of (9.7), `G' = (G_i \ X) ∪ H_i`, and `W` the wall of step (4), whose compass misses `Z_i`.
If steps (5) to (7) end with output (a), the block in `a_wall` parses to some `p`, and the
renamed block `p.movedBlock` has, for `G` and `orig(X)`, the properties of output (iii) of
(9.9): the decoded wall has height `h` and is flat in `G \ orig(X)`, the decoded society is
its society, the decoded division is rural, and the interior members with at least two edges
get decompositions of width at most `ω`. -/
theorem isAlg99OutputIII_of_case3StepsOutputA {h' s h ω : ℕ} {st : Alg99Iter h' G}
    (hst : st.IsValid s) {X : Finset (Fin st.v)}
    {W : WallOfHeight h ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X)}
    {h2 : 2 ≤ h} {he : Even h} {hW : W.IsValid} (hZ : Disjoint W.compassFinset st.Z)
    (hK : W.compassFinset.toNatSet =
      V(wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X)
        (W.toGMWall h2 he hW)))
    {C_blk w a_out a_wall : ℕ} {s' : State}
    (hA : IsCase3StepsOutputA h ω (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X W h2 he
      hW C_blk w a_out a_wall s') :
    ∃ p : ParsedCase3Block
        ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X) X,
      parseCase3Block _ X (s'.arrs a_wall) = some p ∧
      let blk' := p.movedBlock hst.orig_injective (hst.edgeMult_wallUnion X)
      let XG := X.image st.orig
      let H := case3Decoder.wall n G XG blk'
      let S_H := case3Decoder.society n G XG blk'
      let 𝒜 := case3Decoder.division n G XG blk'
      H.height = h ∧
      IsFlatWallIn (GM09.deleteVertices G.toGMDigraph.toGraph XG.toNatSet) H ∧
      IsWallSociety (GM09.deleteVertices G.toGMDigraph.toGraph XG.toNatSet) H S_H ∧
      IsRuralDivision S_H 𝒜 ∧
      ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
        IsInteriorMember H 𝒜 A →
          let bd := case3Decoder.branchDecomp n G XG blk' A
          E(A).ncard ≤ 1 ∨
            (IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
              graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω) := by
  obtain ⟨Kv, Ke, c, ms, -, hwall, -, -, hH, hheight, hflat, hsoc, hrd, hbd⟩ := hA
  rw [← hwall] at hH hheight hflat hsoc hrd hbd
  set blk := s'.arrs a_wall
  obtain ⟨p, hparse⟩ : ∃ p, parseCase3Block ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X) X blk = some p := by
    cases hp : parseCase3Block ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X) X blk with
    | some p => exact ⟨p, rfl⟩
    | none =>
      have hdiv : case3Decoder.division st.v (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X blk = ∅ := by
        simp [case3Decoder, case3DivisionOfDel, hp]
      rw [hdiv] at hrd
      exact absurd hrd (not_isRuralDivision_empty hsoc)
  refine ⟨p, hparse, ?_⟩
  obtain ⟨hw, -, -⟩ := case3Decoder_of_parse hparse
  have hpH : p.toGMWall = W.toGMWall h2 he hW := hw ▸ hH
  have hdel : delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X = delGraph st.Gi X := delGraph_wallUnionMultiDigraph _ _ _
  have hHle : p.toGMWall.graph ≤ delGraph st.Gi X := by
    rw [← hdel, delGraph_eq_deleteVertices, ← hw]
    exact hflat.1
  have hZ' : Disjoint V(wallCompass (delGraph st.Gi X) p.toGMWall) st.Z.toNatSet := by
    rw [← hdel, hpH, ← hK]
    exact disjoint_toNatSet hZ
  have hcomp := wallCompass_relabel_eq hst hHle hZ'
  rw [← hdel] at hcomp
  exact isCase3Output_movedBlock hst.orig_injective (hst.edgeMult_wallUnion X)
    (fun _ => mem_image_orig_iff hst.orig_injective) p hparse hcomp
    hheight hflat hsoc hrd hbd

variable (hinj : Injective orig)
  (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
  (p : ParsedCase3Block (G'.deleteVertices X) X)

include hmult in
/-- **The renamed words are the renamed block.** With `o = origList orig`, the block that
`mvBlock` writes is the code of `p.moveOrig`. -/
theorem renamedBlock_eq_movedBlock :
    renamedBlock (fun x => (origList orig).getD x 0) p.wallSec.W p.K_vList p.K_eList p.corners
      p.members = p.movedBlock hinj hmult := by
  set φ : ℕ → ℕ := fun x => (origList orig).getD x 0 with hφ
  have hKv : ∀ x ∈ p.K_vList, φ x = origVertexEmb orig hinj x := fun x hx =>
    origList_getD_eq_origVertexEmb hinj (lt_of_isDelGraphVert (p.hK_v_valid x hx))
  have hKe : ∀ e ∈ p.K_eList, mvTriple φ e = origEdgeEmb orig hinj e := by
    intro e he
    obtain ⟨-, h1, h2⟩ := p.hK_e_valid e he
    rw [origEdgeEmb_apply, mvTriple, hKv _ h1, hKv _ h2]
  have hwall : p.wallSec.W.renamedEncList φ =
      (p.wallSec.W.moveOrig (G.deleteVertices (X.image orig)) orig).encList :=
    WallOfHeight.renamedEncList_eq_encList_moveOrig orig φ
      (fun u => origList_getD u.2) p.wallSec.W
  have hms : p.members.map (Case3MemberRecord.rename φ (mvTriple φ)) =
      p.members.map (Case3MemberRecord.rename (origVertexEmb orig hinj)
        (origEdgeEmb orig hinj)) := by
    refine List.map_congr_left fun rec hrec => ?_
    have h := p.member_valid_iff hrec
    simp only [Case3MemberRecord.rename, Case3MemberRecord.mk.injEq, and_true]
    refine ⟨List.map_congr_left fun x hx => hKv x (h.2.2.1 x hx),
      List.map_congr_left fun e he => hKe e (h.2.2.2.2.2.1 e he).1⟩
  have hc : p.corners.map φ = p.corners.map (origVertexEmb orig hinj) :=
    List.map_congr_left fun x hx => hKv x (p.hcorners_mem x hx)
  simp only [renamedBlock, ParsedCase3Block.movedBlock, encCase3Block, hwall, hc, hms,
    List.map_congr_left hKv, List.map_congr_left hKe]
  simp only [ParsedCase3Block.moveOrig, ParsedWallSection.moveOrig, List.length_map]

/-- **The renaming program.** Rename the block in array `a` in place (`mvBlock`), then copy
its renamed part to array `a_dst`. -/
def alg99MoveAProg (a o a_dst : Arr) (r : Reg) : Cmd :=
  .seq (mvBlock a o r) (readSliceProg a (.const 0) a_dst (.reg r) (r + 10))

/-- **Running the renaming program.** If array `a` holds a block that parses to `p` and array
`o` holds `orig`, then `alg99MoveAProg` writes `p.movedBlock` to array `a_dst`, in time linear
in the length of the block. -/
theorem alg99MoveAProg_exec {w : ℕ} {blk : List ℕ}
    (hparse : parseCase3Block (G'.deleteVertices X) X blk = some p)
    {a o a_dst : Arr} (hao : a ≠ o) (had : a ≠ a_dst) (r : Reg) {s : State}
    (ha : s.arrs a = blk) (ho : s.arrs o = origList orig) (hr : s.regs r = 0)
    (hblk_w : ∀ x ∈ blk, x < 2 ^ w) (hn_w : n < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hlen_w : blk.length < 2 ^ w) :
    ∃ s' t, Exec w (alg99MoveAProg a o a_dst r) s s' t ∧ t ≤ 116 * blk.length + 210 ∧
      s'.arrs a_dst = p.movedBlock hinj hmult ∧
      (p.movedBlock hinj hmult).length ≤ blk.length ∧
      (∀ x ∈ p.movedBlock hinj hmult, x < 2 ^ w) ∧
      (∀ b, b ≠ a → b ≠ a_dst → s'.arrs b = s.arrs b) ∧
      (∀ q < r, s'.regs q = s.regs q) := by
  obtain ⟨rest, hblk⟩ := eq_encCase3Block_append_of_parseCase3Block hparse
  have hvn := le_of_injective_orig hinj
  have hKv : ∀ x ∈ p.K_vList, x < v := fun x hx => lt_of_isDelGraphVert (p.hK_v_valid x hx)
  have ho_w : ∀ y ∈ s.arrs o, y < 2 ^ w := by
    rw [ho]
    intro y hy
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    exact lt_trans (orig j).2 hn_w
  have hφ_w : ∀ x, (s.arrs o).getD x 0 < 2 ^ w := by
    intro x
    rw [List.getD_eq_getElem?_getD]
    cases hx : (s.arrs o)[x]? with
    | none => simp
    | some y => exact ho_w y (List.mem_of_getElem? hx)
  obtain ⟨s₁, t₁, hex₁, ht₁, hA₁, hP₁, hB₁, hR₁⟩ :=
    mvBlock_exec p.wallSec.W hao r (s := s) (T := rest) (ha.trans hblk) hr
      (by rw [ho]; simp [origList]) (by omega) hKv
      (fun e he => ⟨hKv _ (p.hK_e_valid e he).2.1, hKv _ (p.hK_e_valid e he).2.2⟩)
      (by rw [p.hcorners_eq, List.length_ofFn])
      (fun x hx => hKv x (p.hcorners_mem x hx))
      (fun rec hrec => by
        have h := p.member_valid_iff hrec
        exact ⟨h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
          fun x hx => hKv x (h.2.2.1 x hx),
          fun e he => ⟨hKv _ (p.hK_e_valid e (h.2.2.2.2.2.1 e he).1).2.1,
            hKv _ (p.hK_e_valid e (h.2.2.2.2.2.1 e he).1).2.2⟩⟩)
      ho_w hw4 (by rw [← hblk]; exact hlen_w)
  set E := encCase3Block p.wallSec.W p.K_vList p.K_eList p.corners p.members
  have hmid : renamedBlock (fun x => (s.arrs o).getD x 0) p.wallSec.W p.K_vList p.K_eList
      p.corners p.members = p.movedBlock hinj hmult := by
    rw [ho]
    exact renamedBlock_eq_movedBlock hinj hmult p
  have hmid_len : (p.movedBlock hinj hmult).length = E.length := by
    rw [← hmid, length_renamedBlock]
  have hE_le : E.length ≤ blk.length := by rw [hblk]; simp
  have hmid_w : ∀ x ∈ p.movedBlock hinj hmult, x < 2 ^ w := by
    intro y hy
    rw [← hmid] at hy
    rcases mem_renamedBlock hy with ⟨x, rfl⟩ | hy'
    · exact hφ_w x
    · exact hblk_w y (by rw [hblk]; exact List.mem_append_left _ hy')
  obtain ⟨s₂, t₂, hex₂, ht₂, hA₂, hB₂, hR₂⟩ :=
    readSliceProg_exec (w := w) (off := 0) a a_dst (.const 0) r (r + 10) had (by omega)
      [] (p.movedBlock hinj hmult) rest rfl rfl hmid_w (by omega)
      (by simp only [Nat.zero_add]; rw [hmid_len]; omega)
      (by simp [Expr.eval, checkWord])
      (by rw [hA₁, hmid]; simp)
      (by rw [hP₁, hmid_len])
  refine ⟨s₂, t₁ + t₂, Exec.seq hex₁ hex₂, ?_, hA₂, by omega, hmid_w, ?_, ?_⟩
  · simp only [Expr.cost] at ht₂
    omega
  · intro b hb hb'
    rw [hB₂ b hb', hB₁ b hb]
  · intro q hq
    rw [hR₂ q (by romega), hR₁ q hq]

end GraphMinor.Compute
