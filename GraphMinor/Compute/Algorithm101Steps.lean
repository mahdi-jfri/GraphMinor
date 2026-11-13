module

public import GraphMinor.Compute.Algorithm101Vision
public import GraphMinor.Compute.Algorithm105
public import GraphMinor.Compute.Menger

/-!
# Step Invariants and Word RAM Gadgets for Graph Minors XIII, Algorithm (10.1)

This file establishes the mathematical invariants and reusable Word RAM gadgets for Steps 1–4 of
Algorithm (10.1) (N. Robertson and P. D. Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), pages 106–107):

1. **Case (iii) Block Serialization and Size Bounds (`Section 1`):**
   - `eq_encCase3Block_append_of_parseCase3Block`: any `block` with
     `parseCase3Block D_del X' block = some p` has prefix
     `encCase3Block p.wallSec.W p.K_vList p.K_eList p.corners p.members`.
   - `sum_vList_length_le`: in any society division `IsSocietyDivision p.toSociety p.toDivision`,
     the sum of `r.vList.length` over `r ∈ p.members` is at most `n + 3 * p.members.length ≤ 4 * N`.
   - `not_mem_writtenRegs_shiftMem` and `not_mem_writtenArrs_shiftMem`: automatic preservation of
     registers `< R_off` and arrays `< A_off` for shifted commands `c.shiftMem R_off A_off`.
2. **Step 2 Edge Partition and Branch-Decomposition Bridge (`Section 2`):**
   - `vertOwner`, `incidentOwner`, `extraEdges`, `memberTildeAEList`: deterministic assignment of
     edges in `G` with both ends in `X' ∪ V(K)` to members `j : Fin p.members.length`, proving
     `Nodup`, `hedges_cover`, and `filter = r.eList`.
   - `tildeAMultiDigraph_deleteVertices_eq` and `isWrittenDigraphBD_of_member`: bridge from
     `p.branchDecomp_toSubgraph` on `A_j` to `IsWrittenDigraphBD ω` on
     `(tildeAMultiDigraph vList eList).deleteVertices Z_X`, ready for `convertBDProg`.
3. **Steps 1 & 4 Compass Adjacency, Menger Non-Separation, and `traceWalkStopB` (`Section 3`):**
   - `Z_notK` and `G_K_adj_iff_isKEdgeBetween`: under `HypothesisC`, adjacency in
     `G_K = (G.deleteVertices (Z_notK p)).toSimpleGraph` coincides with `isKEdgeBetween p.K_eList`.
   - `not_isABSeparator_step1` and `not_isABSeparator_step4`: rules out separators of size `< 3` in
     Step 1 (by `hDiv.disjoint_paths_to_bar`) and size `< 1` in Step 4
     (by `GM13.exists_vOf_of_isInteriorMember`).
   - `traceWalkStopB`: truncates a path-system walk at its first vertex in `B`, yielding a simple
     path in `K` whose only vertex in `B` is its endpoint.
   - `isMemberBoundaryVert_iff_corner_or_other_member`: characterizes boundary vertices of `A_j`
     under `IsSocietyDivision` via corners and shared member vertices.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-! ### Section 1: Case (iii) Block Serialization, Society Vertex Sum, and `.shiftMem` Bounds -/

theorem not_mem_writtenRegs_shiftMem {c : Cmd} {R_off A_off r : ℕ} (hr : r < R_off) :
    r ∉ (c.shiftMem R_off A_off).writtenRegs := by
  induction c with
  | skip => simp [Cmd.shiftMem]
  | assign r' _ =>
    simp only [Cmd.shiftMem, Cmd.writtenRegs, Finset.mem_singleton]
    omega
  | write _ _ _ => simp [Cmd.shiftMem]
  | alloc _ _ => simp [Cmd.shiftMem]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp [Cmd.shiftMem, ih₁, ih₂]
  | ite _ c₁ c₂ ih₁ ih₂ =>
    simp [Cmd.shiftMem, ih₁, ih₂]
  | «while» _ body ih =>
    simp [Cmd.shiftMem, ih]

theorem not_mem_writtenArrs_shiftMem {c : Cmd} {R_off A_off a : ℕ} (ha : a < A_off) :
    a ∉ (c.shiftMem R_off A_off).writtenArrs := by
  induction c with
  | skip => simp [Cmd.shiftMem]
  | assign _ _ => simp [Cmd.shiftMem]
  | write a' _ _ =>
    simp only [Cmd.shiftMem, Cmd.writtenArrs, Finset.mem_singleton]
    omega
  | alloc a' _ =>
    simp only [Cmd.shiftMem, Cmd.writtenArrs, Finset.mem_singleton]
    omega
  | seq c₁ c₂ ih₁ ih₂ =>
    simp [Cmd.shiftMem, ih₁, ih₂]
  | ite _ c₁ c₂ ih₁ ih₂ =>
    simp [Cmd.shiftMem, ih₁, ih₂]
  | «while» _ body ih =>
    simp [Cmd.shiftMem, ih]

theorem Exec.regs_and_arrs_preserved_of_shiftMem {w R_off A_off : ℕ} {c : Cmd}
    {s s' : State} {t : ℕ}
    (hex : Exec w (c.shiftMem R_off A_off) s s' t) :
    (∀ r < R_off, s'.regs r = s.regs r) ∧
    (∀ a < A_off, s'.arrs a = s.arrs a) :=
  ⟨fun _ hr => hex.regs_eq_of_not_mem_writtenRegs (not_mem_writtenRegs_shiftMem hr),
   fun _ ha => hex.arrs_eq_of_not_mem_writtenArrs (not_mem_writtenArrs_shiftMem ha)⟩

theorem eq_append_of_takeExactNat {k : ℕ} {l xs rest : List ℕ}
    (h : takeExactNat k l = some (xs, rest)) :
    xs.length = k ∧ l = xs ++ rest := by
  unfold takeExactNat at h
  split_ifs at h with hle
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨List.length_take_of_le (Nat.le_of_not_lt hle), (List.take_append_drop k l).symm⟩

theorem eq_encEdgeTriples_append_of_takeEdgeTriples :
    ∀ {m : ℕ} {l : List ℕ} {es : List (ℕ × ℕ × ℕ)} {rest : List ℕ},
      takeEdgeTriples m l = some (es, rest) →
      es.length = m ∧ l = encEdgeTriples es ++ rest
  | 0, l, es, rest, h => by
    simp only [takeEdgeTriples, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | m + 1, u :: v :: k :: rest₀, es, rest, h => by
    simp only [takeEdgeTriples] at h
    cases hrec : takeEdgeTriples m rest₀ with
    | none => rw [hrec] at h; nomatch h
    | some p =>
      rcases p with ⟨es', rest'⟩
      rw [hrec] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rcases eq_encEdgeTriples_append_of_takeEdgeTriples hrec with ⟨hlen, heq⟩
      refine ⟨by simp [hlen], ?_⟩
      simp [encEdgeTriples, heq]
  | _ + 1, [], _, _, h => by simp [takeEdgeTriples] at h
  | _ + 1, [_], _, _, h => by simp [takeEdgeTriples] at h
  | _ + 1, [_, _], _, _, h => by simp [takeEdgeTriples] at h

theorem map_val_toFinList_of_all {n : ℕ} {X' : Finset (Fin n)} :
    ∀ {vs : List ℕ},
      vs.all (isDelGraphVert n X') = true →
      (toFinList n vs).map Fin.val = vs ∧
      (toFinList n vs).length = vs.length ∧
      (∀ v ∈ toFinList n vs, v ∉ X')
  | [], _ => ⟨rfl, rfl, fun _ hv => nomatch hv⟩
  | v :: vs, hall => by
    rw [List.all_cons, Bool.and_eq_true] at hall
    rcases hall with ⟨hv, hvs⟩
    unfold isDelGraphVert at hv
    split_ifs at hv with hlt
    simp only [decide_eq_true_eq] at hv
    rcases map_val_toFinList_of_all hvs with ⟨hmap, hlen, hnot⟩
    simp only [toFinList, hlt, ↓reduceDIte, List.map_cons, hmap, List.length_cons, hlen,
      List.mem_cons, true_and]
    rintro w (rfl | hw)
    · exact hv
    · exact hnot w hw

theorem eq_flatMap_append_of_takeSubdivLists {n : ℕ} (X' : Finset (Fin n)) :
    ∀ {ne : ℕ} {l : List ℕ} {vss : List (List (Fin n))} {rest : List ℕ},
      takeSubdivLists n X' ne l = some (vss, rest) →
      vss.length = ne ∧
      l = vss.flatMap (fun vs => vs.length :: vs.map Fin.val) ++ rest
  | 0, l, vss, rest, h => by
    simp only [takeSubdivLists, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | _ + 1, [], _, _, h => by simp [takeSubdivLists] at h
  | ne + 1, len_k :: rest₀, vss, rest, h => by
    simp only [takeSubdivLists] at h
    split_ifs at h with hle
    cases htake : takeExactNat len_k rest₀ with
    | none => rw [htake] at h; nomatch h
    | some p₁ =>
      rcases p₁ with ⟨vs, rest₁⟩
      rw [htake] at h
      dsimp only at h
      split_ifs at h with hall
      cases hrec : takeSubdivLists n X' ne rest₁ with
      | none => rw [hrec] at h; nomatch h
      | some p₂ =>
        rcases p₂ with ⟨vss', rest₂⟩
        rw [hrec] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rcases eq_append_of_takeExactNat htake with ⟨hvs_len, hrest₀⟩
        rcases map_val_toFinList_of_all hall with ⟨hmap, hfin_len, _⟩
        rcases eq_flatMap_append_of_takeSubdivLists X' hrec with ⟨hvss_len, hrest₁⟩
        refine ⟨by simp [hvss_len], ?_⟩
        simp [hrest₀, hrest₁, hmap, hfin_len, hvs_len, List.append_assoc]

private theorem flatMap_finRange_getD_eq {α β : Type*} {m : ℕ} (l : List α)
    (hm : l.length = m) (d : α) (f : α → List β) :
    (List.finRange m).flatMap (fun k => f (l.getD k.1 d)) = l.flatMap f := by
  subst hm
  have hmap : (List.finRange l.length).map (fun k : Fin l.length => l.getD k.1 d) = l := by
    apply List.ext_getElem (by simp)
    intro i _ hi₂
    simp only [List.getElem_map, List.getElem_finRange]
    exact List.getD_eq_getElem l d hi₂
  rw [← List.flatMap_map, hmap]

theorem eq_encList_append_of_parseWallSection {n : ℕ} {D_del : MultiDigraph n}
    {X' : Finset (Fin n)} {l : List ℕ} {pw : ParsedWallSection D_del X'} {rest : List ℕ}
    (h : parseWallSection D_del X' l = some (pw, rest)) :
    l = pw.W.encList ++ rest := by
  unfold parseWallSection at h
  rcases l with _ | ⟨h₀, _ | ⟨nv, _ | ⟨ne, rest₀⟩⟩⟩
  · nomatch h
  · nomatch h
  · nomatch h
  · dsimp only at h
    split_ifs at h with hcond
    rcases hcond with ⟨h2, he, rfl, rfl, hnv_le⟩
    cases htake : takeExactNat (elemWallNumVerts h₀) rest₀ with
    | none => rw [htake] at h; nomatch h
    | some p₁ =>
      rcases p₁ with ⟨brWords, rest₁⟩
      rw [htake] at h
      dsimp only at h
      split_ifs at h with hbr
      cases hsub : takeSubdivLists n X' (elemWallEdges h₀).length rest₁ with
      | none => rw [hsub] at h; nomatch h
      | some p₂ =>
        rcases p₂ with ⟨intLists, rest₂⟩
        rw [hsub] at h
        dsimp only [finishWallSection] at h
        split_ifs at h with hval
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hpw_eq, rfl⟩
        rcases eq_append_of_takeExactNat htake with ⟨hbr_len, hrest₀⟩
        rcases eq_flatMap_append_of_takeSubdivLists X' hsub with ⟨hint_len, hrest₁⟩
        have hbr_eq :
            (List.finRange (elemWallNumVerts h₀)).map
              (fun u : Fin (elemWallNumVerts h₀) =>
                (let v := brWords.getD u.1 0
                 if hv : v < n then (⟨v, hv⟩ : Fin n)
                 else ⟨0, Nat.zero_lt_of_lt (lt_of_lt_of_le u.2 hnv_le)⟩).1) =
              brWords := by
          apply List.ext_getElem (by simp [hbr_len])
          intro i hi₁ hi₂
          simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
          have hmem : brWords[i]'hi₂ ∈ brWords := List.getElem_mem hi₂
          have hv_del := hbr _ hmem
          unfold isDelGraphVert at hv_del
          split_ifs at hv_del with hlt
          simp only [List.getD_eq_getElem _ _ hi₂, hlt, ↓reduceDIte]
        have hint_eq :=
          flatMap_finRange_getD_eq intLists hint_len []
            (fun vs => vs.length :: vs.map Fin.val)
        subst hpw_eq
        unfold WallOfHeight.encList
        dsimp only
        rw [hbr_eq, hint_eq, hrest₀, hrest₁]
        simp [List.append_assoc]

theorem eq_enc_append_of_parseOneMemberRecord {l : List ℕ} {r : Case3MemberRecord} {rest : List ℕ}
    (h : parseOneMemberRecord l = some (r, rest)) :
    r.parList.length = r.t_len ∧
    r.tauList.length = r.eList.length ∧
    l = r.enc ++ rest := by
  unfold parseOneMemberRecord at h
  rcases l with _ | ⟨v_len, rest₁⟩
  · nomatch h
  · dsimp only at h
    cases h₁ : takeExactNat v_len rest₁ with
    | none => rw [h₁] at h; nomatch h
    | some p₁ =>
      rcases p₁ with ⟨vList, _ | ⟨e_len, rest₃⟩⟩
      · rw [h₁] at h; nomatch h
      · rw [h₁] at h
        dsimp only at h
        cases h₂ : takeEdgeTriples e_len rest₃ with
        | none => rw [h₂] at h; nomatch h
        | some p₂ =>
          rcases p₂ with ⟨eList, _ | ⟨t_len, rest₅⟩⟩
          · rw [h₂] at h; nomatch h
          · rw [h₂] at h
            dsimp only at h
            cases h₃ : takeExactNat t_len rest₅ with
            | none => rw [h₃] at h; nomatch h
            | some p₃ =>
              rcases p₃ with ⟨parList, rest₆⟩
              rw [h₃] at h
              dsimp only at h
              cases h₄ : takeExactNat e_len rest₆ with
              | none => rw [h₄] at h; nomatch h
              | some p₄ =>
                rcases p₄ with ⟨tauList, rest₇⟩
                rw [h₄] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                rcases eq_append_of_takeExactNat h₁ with ⟨hv_len, hrest₁⟩
                rcases eq_encEdgeTriples_append_of_takeEdgeTriples h₂ with ⟨he_len, hrest₃⟩
                rcases eq_append_of_takeExactNat h₃ with ⟨hpar_len, hrest₅⟩
                rcases eq_append_of_takeExactNat h₄ with ⟨htau_len, hrest₆⟩
                refine ⟨hpar_len, htau_len.trans he_len.symm, ?_⟩
                unfold Case3MemberRecord.enc
                dsimp only
                rw [hv_len, he_len, hrest₁, hrest₃, hrest₅, hrest₆]
                simp [List.append_assoc]

theorem eq_flatMap_enc_append_of_parseMemberRecords :
    ∀ {m : ℕ} {l : List ℕ} {rs : List Case3MemberRecord} {rest : List ℕ},
      parseMemberRecords m l = some (rs, rest) →
      rs.length = m ∧ l = rs.flatMap Case3MemberRecord.enc ++ rest
  | 0, l, rs, rest, h => by
    simp only [parseMemberRecords, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | m + 1, l, rs, rest, h => by
    simp only [parseMemberRecords] at h
    cases h₁ : parseOneMemberRecord l with
    | none => rw [h₁] at h; nomatch h
    | some p₁ =>
      rcases p₁ with ⟨r, rest₁⟩
      rw [h₁] at h
      dsimp only at h
      cases h₂ : parseMemberRecords m rest₁ with
      | none => rw [h₂] at h; nomatch h
      | some p₂ =>
        rcases p₂ with ⟨rs', rest₂⟩
        rw [h₂] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rcases eq_enc_append_of_parseOneMemberRecord h₁ with ⟨_, _, hl⟩
        rcases eq_flatMap_enc_append_of_parseMemberRecords h₂ with ⟨hlen, hrest₁⟩
        exact ⟨by simp [hlen], by simp [hl, hrest₁, List.append_assoc]⟩

/-- Any `block` parsed by `parseCase3Block D_del X' block = some p` begins with the canonical
prefix `encCase3Block p.wallSec.W p.K_vList p.K_eList p.corners p.members`. -/
theorem eq_encCase3Block_append_of_parseCase3Block {n : ℕ} {D_del : MultiDigraph n}
    {X' : Finset (Fin n)} {block : List ℕ} {p : ParsedCase3Block D_del X'}
    (h : parseCase3Block D_del X' block = some p) :
    ∃ rest : List ℕ,
      block = encCase3Block p.wallSec.W p.K_vList p.K_eList p.corners p.members ++ rest := by
  unfold parseCase3Block at h
  cases hwall : parseWallSection D_del X' block with
  | none => rw [hwall] at h; nomatch h
  | some pw_rest =>
    rcases pw_rest with ⟨wallSec, _ | ⟨K_v_len, rest₂⟩⟩
    · rw [hwall] at h; nomatch h
    · rw [hwall] at h
      dsimp only at h
      cases hKv : takeExactNat K_v_len rest₂ with
      | none => rw [hKv] at h; nomatch h
      | some pKv =>
        rcases pKv with ⟨K_vList, _ | ⟨K_e_len, rest₄⟩⟩
        · rw [hKv] at h; nomatch h
        · rw [hKv] at h
          dsimp only at h
          cases hKe : takeEdgeTriples K_e_len rest₄ with
          | none => rw [hKe] at h; nomatch h
          | some pKe =>
            rcases pKe with ⟨K_eList, rest₅⟩
            rw [hKe] at h
            dsimp only at h
            cases hc : takeExactNat 4 rest₅ with
            | none => rw [hc] at h; nomatch h
            | some pc =>
              rcases pc with ⟨corners, _ | ⟨num_members, rest₇⟩⟩
              · rw [hc] at h; nomatch h
              · rw [hc] at h
                dsimp only at h
                split_ifs at h with hnum
                cases hmem : parseMemberRecords num_members rest₇ with
                | none => rw [hmem] at h; nomatch h
                | some pmem =>
                  rcases pmem with ⟨members, rest₈⟩
                  rw [hmem] at h
                  dsimp only at h
                  split_ifs at h with hcond
                  simp only [Option.some.injEq] at h
                  subst h
                  have h₀ := eq_encList_append_of_parseWallSection hwall
                  rcases eq_append_of_takeExactNat hKv with ⟨hKv_len, hrest₂⟩
                  rcases eq_encEdgeTriples_append_of_takeEdgeTriples hKe with ⟨hKe_len, hrest₄⟩
                  rcases eq_append_of_takeExactNat hc with ⟨_, hrest₅⟩
                  rcases eq_flatMap_enc_append_of_parseMemberRecords hmem with ⟨hmem_len, hrest₇⟩
                  refine ⟨rest₈, ?_⟩
                  unfold encCase3Block
                  dsimp only
                  rw [hKv_len, hKe_len, hmem_len, h₀, hrest₂, hrest₄, hrest₅, hrest₇]
                  simp [List.append_assoc]

private theorem sum_map_eq_sum_fin {α : Type*} (l : List α) (f : α → ℕ) :
    (l.map f).sum = ∑ j : Fin l.length, f (l[j.1]'j.2) := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Fin.sum_univ_succ, ih]
    rfl

/-- Under a society division `IsSocietyDivision p.toSociety p.toDivision`, the sum of
`r.vList.length` over all `r ∈ p.members` is at most `n + 3 * p.members.length`. -/
theorem ParsedCase3Block.sum_vList_length_le {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hDiv : GM13.IsSocietyDivision p.toSociety p.toDivision) :
    (p.members.map (fun r => r.vList.length)).sum ≤ n + 3 * p.members.length := by
  let M := p.members.length
  let A_of (j : Fin M) : Graph ℕ (ℕ × ℕ × ℕ) :=
    (p.members[j.1]'j.2).toSubgraph (delGraph G X')
  have hA_mem : ∀ j : Fin M, A_of j ∈ p.toDivision := fun j =>
    ⟨p.members[j.1]'j.2, List.getElem_mem j.2, rfl⟩
  have hA_inj : Function.Injective A_of := fun j₁ j₂ heq =>
    ParsedVisionOutput.member_injective heq
  let V_of (j : Fin M) : Finset ℕ := (p.members[j.1]'j.2).vList.toFinset
  let : ∀ j : Fin M, DecidablePred (· ∈ GM13.divBoundary p.toSociety (A_of j)) :=
    fun _ => Classical.decPred _
  let B_of (j : Fin M) : Finset ℕ :=
    (V_of j).filter (fun v => v ∈ GM13.divBoundary p.toSociety (A_of j))
  let I_of (j : Fin M) : Finset ℕ :=
    (V_of j).filter (fun v => v ∉ GM13.divBoundary p.toSociety (A_of j))
  have hcard_split : ∀ j : Fin M,
      (p.members[j.1]'j.2).vList.length = (I_of j).card + (B_of j).card := by
    intro j
    have hr_val := p.member_valid_iff (List.getElem_mem j.2)
    rw [← List.toFinset_card_of_nodup hr_val.2.1]
    change (V_of j).card = (I_of j).card + (B_of j).card
    rw [add_comm, Finset.card_filter_add_card_filter_not]
  have hB_le : ∀ j : Fin M, (B_of j).card ≤ 3 := by
    intro j
    have hsub : (B_of j : Set ℕ) ⊆ GM13.divBoundary p.toSociety (A_of j) := by
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    have hfin : (GM13.divBoundary p.toSociety (A_of j)).Finite :=
      p.toSociety.finite_V.subset
        (fun _ hx => (hDiv.sub_of_mem (hA_mem j)).vertexSet_mono hx.1)
    have hncard := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at hncard
    exact hncard.trans (hDiv.boundary_ncard_le_three (hA_mem j))
  have hI_disj : Pairwise (fun j₁ j₂ : Fin M => Disjoint (I_of j₁) (I_of j₂)) := by
    intro j₁ j₂ hne
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    rcases Finset.mem_filter.mp hv₁ with ⟨hvV₁, hvNotB₁⟩
    rcases Finset.mem_filter.mp hv₂ with ⟨hvV₂, _⟩
    have hvA₁ : v ∈ V(A_of j₁) := by
      rw [p.vertexSet_member_toSubgraph (List.getElem_mem j₁.2)]
      exact List.mem_toFinset.mp hvV₁
    have hvA₂ : v ∈ V(A_of j₂) := by
      rw [p.vertexSet_member_toSubgraph (List.getElem_mem j₂.2)]
      exact List.mem_toFinset.mp hvV₂
    have hinter : v ∈ V(A_of j₁) ∩ V(A_of j₂) := ⟨hvA₁, hvA₂⟩
    rw [hDiv.vertex_inter_eq (hA_mem j₁) (hA_mem j₂) (hA_inj.ne hne)] at hinter
    exact hvNotB₁ hinter.1
  have hI_sub : Finset.univ.biUnion I_of ⊆ Finset.range n := by
    intro v hv
    rcases Finset.mem_biUnion.mp hv with ⟨j, _, hvI⟩
    have hv_mem : v ∈ (p.members[j.1]'j.2).vList :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hvI).1
    have hr_val := p.member_valid_iff (List.getElem_mem j.2)
    have hv_del := p.K_vList_mem_delGraph (hr_val.2.2.1 v hv_mem)
    exact Finset.mem_range.mpr ((mem_vertexSet_delGraph_iff G X' v).mp hv_del).1
  have hsum_I : (∑ j : Fin M, (I_of j).card) ≤ n := by
    rw [← Finset.card_biUnion (fun j₁ _ j₂ _ hne => hI_disj hne)]
    exact (Finset.card_le_card hI_sub).trans (by simp)
  have hsum_B : (∑ j : Fin M, (B_of j).card) ≤ 3 * M := by
    calc (∑ j : Fin M, (B_of j).card) ≤ ∑ _j : Fin M, 3 :=
          Finset.sum_le_sum (fun j _ => hB_le j)
      _ = 3 * M := by simp [Nat.mul_comm]
  rw [sum_map_eq_sum_fin p.members (fun r => r.vList.length)]
  calc (∑ j : Fin M, (p.members[j.1]'j.2).vList.length)
      = (∑ j : Fin M, (I_of j).card) + (∑ j : Fin M, (B_of j).card) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => hcard_split j)
    _ ≤ n + 3 * M := Nat.add_le_add hsum_I hsum_B

/-! ### Section 2: Step 2 Edge Partition (`memberTildeAEList`) and Branch-Decomposition Bridge -/

/-- Under `IsWallSociety` and `IsRuralDivision`, `p.members` is nonempty. -/
theorem ParsedCase3Block.members_ne_nil_of_isRuralDivision {n : ℕ} {G : MultiDigraph n}
    {X' : Finset (Fin n)} (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    (hRD : GM13.IsRuralDivision p.toSociety p.toDivision) :
    p.members ≠ [] := by
  intro hemp
  have hdiv_emp : p.toDivision = ∅ := by
    ext A
    simp [ParsedCase3Block.toDivision, hemp]
  rw [hdiv_emp] at hRD
  exact not_isRuralDivision_empty hWS hRD

/-- Index `j < p.members.length` of the first member record whose `vList` contains `v`
(defaulting to `0`). -/
def vertOwner {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (v : ℕ) : ℕ :=
  match (List.finRange p.members.length).find?
      (fun j => decide (v ∈ (p.members[j.1]'j.2).vList)) with
  | some j => j.1
  | none => 0

theorem vertOwner_lt_and_mem_of_mem_K_vList {n : ℕ} {G : MultiDigraph n}
    {X' : Finset (Fin n)} (p : ParsedCase3Block (G.deleteVertices X') X')
    (hDiv : GM13.IsSocietyDivision p.toSociety p.toDivision)
    {v : ℕ} (hv : v ∈ p.K_vList) :
    ∃ hlt : vertOwner p v < p.members.length,
      v ∈ (p.members[vertOwner p v]'hlt).vList := by
  have hv_soc : v ∈ V(p.toSociety.G) := by
    change v ∈ V(p.toCompassGraph)
    rw [p.vertexSet_toCompassGraph]
    exact hv
  have hunion : V(subgraphSUnion p.toSociety.G p.toDivision) = V(p.toSociety.G) :=
    congrArg Graph.vertexSet hDiv.sUnion_eq
  rw [GM09.vertexSet_subgraphSUnion] at hunion
  rw [← hunion, Set.mem_iUnion₂] at hv_soc
  rcases hv_soc with ⟨A, ⟨r, hr_mem, rfl⟩, hvA⟩
  have hvA' : v ∈ V(r.toSubgraph (delGraph G X')) := hvA
  rw [p.vertexSet_member_toSubgraph hr_mem, Set.mem_ofPred_eq] at hvA'
  rcases List.mem_iff_getElem.mp hr_mem with ⟨j₀, hj₀, rfl⟩
  unfold vertOwner
  cases hfind : (List.finRange p.members.length).find?
      (fun j => decide (v ∈ (p.members[j.1]'j.2).vList)) with
  | none =>
    have hfalse := List.find?_eq_none.mp hfind ⟨j₀, hj₀⟩ (List.mem_finRange _)
    simp [hvA'] at hfalse
  | some j =>
    have hpred := List.find?_some hfind
    simp only [decide_eq_true_eq] at hpred
    exact ⟨j.2, hpred⟩

/-- Owner member index `< p.members.length` for an edge with endpoints `(u, v)` having at least one
endpoint in `xSeq` and both endpoints in `xSeq ++ p.K_vList`. -/
def incidentOwner {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (xSeq : List ℕ) (u v : ℕ) : ℕ :=
  if u ∉ xSeq then vertOwner p u
  else if v ∉ xSeq then vertOwner p v
  else 0

/-- Correctness of `incidentOwner` when `u ∈ xSeq ∨ v ∈ xSeq`. -/
theorem incidentOwner_valid_of_cross {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    (hRD : GM13.IsRuralDivision p.toSociety p.toDivision)
    (xSeq : List ℕ) {u v : ℕ}
    (hcross : u ∈ xSeq ∨ v ∈ xSeq)
    (hu : u ∈ xSeq ∨ u ∈ p.K_vList) (hv : v ∈ xSeq ∨ v ∈ p.K_vList) :
    ∃ hlt : incidentOwner p xSeq u v < p.members.length,
      (u ∈ (p.members[incidentOwner p xSeq u v]'hlt).vList ∨ u ∈ xSeq) ∧
      (v ∈ (p.members[incidentOwner p xSeq u v]'hlt).vList ∨ v ∈ xSeq) := by
  have hDiv := hRD.isDivision
  have hne := p.members_ne_nil_of_isRuralDivision hWS hRD
  have hpos : 0 < p.members.length := List.length_pos_of_ne_nil hne
  unfold incidentOwner
  by_cases hu_x : u ∉ xSeq
  · rw [ite_eq_left hu_x]
    have hu_K : u ∈ p.K_vList := hu.resolve_left hu_x
    have hv_x : v ∈ xSeq := hcross.resolve_left hu_x
    rcases vertOwner_lt_and_mem_of_mem_K_vList p hDiv hu_K with ⟨hlt, hu_mem⟩
    exact ⟨hlt, Or.inl hu_mem, Or.inr hv_x⟩
  · push Not at hu_x
    rw [ite_eq_right (not_not.mpr hu_x)]
    by_cases hv_x : v ∉ xSeq
    · rw [ite_eq_left hv_x]
      have hv_K : v ∈ p.K_vList := hv.resolve_left hv_x
      rcases vertOwner_lt_and_mem_of_mem_K_vList p hDiv hv_K with ⟨hlt, hv_mem⟩
      exact ⟨hlt, Or.inr hu_x, Or.inl hv_mem⟩
    · push Not at hv_x
      rw [ite_eq_right (not_not.mpr hv_x)]
      exact ⟨hpos, Or.inr hu_x, Or.inr hv_x⟩

/-- Extra edges assigned to member `j : Fin p.members.length`: all edges of `G` with at least one
endpoint in `xSeq`, both endpoints in `xSeq ++ p.K_vList`, and `incidentOwner = j.1`. -/
def extraEdges {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : Fin p.members.length) : List (ℕ × ℕ × ℕ) :=
  G.activePairsList.flatMap fun pair =>
    let u := pair.1
    let v := pair.2
    if (u.1 ∈ xSeq ∨ v.1 ∈ xSeq) ∧
       (u.1 ∈ xSeq ∨ u.1 ∈ p.K_vList) ∧
       (v.1 ∈ xSeq ∨ v.1 ∈ p.K_vList) ∧
       incidentOwner p xSeq u.1 v.1 = j.1 then
      (List.range (G.edgeMult u v)).map fun k => (u.1, v.1, k)
    else []

@[simp]
theorem mem_extraEdges_iff {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : Fin p.members.length) (e : ℕ × ℕ × ℕ) :
    e ∈ extraEdges G p xSeq j ↔
      e ∈ G.toGMDigraph.edgeSet ∧
      (e.1 ∈ xSeq ∨ e.2.1 ∈ xSeq) ∧
      (e.1 ∈ xSeq ∨ e.1 ∈ p.K_vList) ∧
      (e.2.1 ∈ xSeq ∨ e.2.1 ∈ p.K_vList) ∧
      incidentOwner p xSeq e.1 e.2.1 = j.1 := by
  rcases e with ⟨u, v, k⟩
  unfold extraEdges
  simp only [List.mem_flatMap, MultiDigraph.mem_activePairsList, MultiDigraph.toGMDigraph,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨u', v'⟩, _, hmem⟩
    dsimp only at hmem
    split_ifs at hmem with hcond
    · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
      rcases hmem with ⟨k', hk', rfl, rfl, rfl⟩
      exact ⟨⟨u'.2, v'.2, hk'⟩, hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2⟩
    · nomatch hmem
  · rintro ⟨⟨hu, hv, hk⟩, hcross, hu_xk, hv_xk, hown⟩
    refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), Nat.zero_lt_of_lt hk, ?_⟩
    dsimp only
    rw [ite_eq_left ⟨hcross, hu_xk, hv_xk, hown⟩]
    simp [hk]

theorem nodup_extraEdges {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : Fin p.members.length) :
    (extraEdges G p xSeq j).Nodup := by
  unfold extraEdges
  rw [List.nodup_flatMap]
  refine ⟨fun pair _ => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact List.nodup_range.map (fun k₁ k₂ h => by simpa using h)
    · exact List.nodup_nil
  · refine G.nodup_activePairsList.imp ?_
    intro p₁ p₂ hne e he₁ he₂
    dsimp only at he₁ he₂
    split_ifs at he₁ with hc₁ <;> split_ifs at he₂ with hc₂
    · simp only [List.mem_map, List.mem_range] at he₁ he₂
      rcases he₁ with ⟨k₁, _, rfl⟩
      rcases he₂ with ⟨k₂, _, heq⟩
      simp only [Prod.mk.injEq] at heq
      exact hne (Prod.ext (Fin.ext heq.1.symm) (Fin.ext heq.2.1.symm))
    · nomatch he₂
    · nomatch he₁
    · nomatch he₁

/-- Full edge list `tildeA_eList` for member `j : Fin p.members.length` in Step 2 of Algorithm (10.1). -/
def memberTildeAEList {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : Fin p.members.length) : List (ℕ × ℕ × ℕ) :=
  (p.members[j.1]'j.2).eList ++ extraEdges G p xSeq j

theorem member_eList_disjoint_xSeq {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val)
    (j : Fin p.members.length) {e : ℕ × ℕ × ℕ}
    (he : e ∈ (p.members[j.1]'j.2).eList) :
    e.1 ∉ xSeq ∧ e.2.1 ∉ xSeq := by
  have hr_val := p.member_valid_iff (List.getElem_mem j.2)
  rcases hr_val.2.2.2.2.2.1 e he with ⟨heK, _, _⟩
  have he_del := (p.K_eList_mem_delGraph heK).1
  rw [delGraph_eq] at he_del
  have hx_eq : {x : ℕ | x ∈ xSeq} = X'.toNatSet := by
    ext x
    have h := Finset.ext_iff.mp hx_set x
    simpa [Finset.toNatSet] using h
  rw [← hx_eq] at he_del
  exact ⟨he_del.2.2.2, he_del.2.1.2⟩

theorem nodup_memberTildeAEList {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val)
    (j : Fin p.members.length) :
    (memberTildeAEList G p xSeq j).Nodup := by
  unfold memberTildeAEList
  have hr_val := p.member_valid_iff (List.getElem_mem j.2)
  refine List.Nodup.append hr_val.2.2.2.2.1 (nodup_extraEdges G p xSeq j) ?_
  intro e he₁ he₂
  have hnot := member_eList_disjoint_xSeq p hx_set j he₁
  have hcross := ((mem_extraEdges_iff G p xSeq j e).mp he₂).2.1
  rcases hcross with h1 | h2
  · exact hnot.1 h1
  · exact hnot.2 h2

theorem filter_memberTildeAEList {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val)
    (j : Fin p.members.length) :
    (memberTildeAEList G p xSeq j).filter (fun e => decide (e.1 ∉ xSeq ∧ e.2.1 ∉ xSeq)) =
      (p.members[j.1]'j.2).eList := by
  unfold memberTildeAEList
  rw [List.filter_append]
  have h₁ :
      ((p.members[j.1]'j.2).eList).filter (fun e => decide (e.1 ∉ xSeq ∧ e.2.1 ∉ xSeq)) =
        (p.members[j.1]'j.2).eList := by
    rw [List.filter_eq_self]
    intro e he
    simp [member_eList_disjoint_xSeq p hx_set j he]
  have h₂ :
      (extraEdges G p xSeq j).filter (fun e => decide (e.1 ∉ xSeq ∧ e.2.1 ∉ xSeq)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp only [decide_eq_true_eq, not_and_or, not_not]
    exact ((mem_extraEdges_iff G p xSeq j e).mp he).2.1
  rw [h₁, h₂, List.append_nil]

theorem memberTildeAEList_valid_ends {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    (hRD : GM13.IsRuralDivision p.toSociety p.toDivision)
    (xSeq : List ℕ) (j : Fin p.members.length) (sSeq : List ℕ)
    (hs_sub : ∀ s ∈ sSeq, s ∈ (p.members[j.1]'j.2).vList) :
    ∀ e ∈ memberTildeAEList G p xSeq j,
      isDelGraphEdge G e = true ∧
      e.1 ∈ memberTildeAVList xSeq (p.members[j.1]'j.2) sSeq ∧
      e.2.1 ∈ memberTildeAVList xSeq (p.members[j.1]'j.2) sSeq := by
  intro e he
  unfold memberTildeAEList at he
  rw [List.mem_append] at he
  rcases he with he_r | he_ex
  · have hr_val := p.member_valid_iff (List.getElem_mem j.2)
    rcases hr_val.2.2.2.2.2.1 e he_r with ⟨heK, he1, he2⟩
    have he_del := (p.K_eList_mem_delGraph heK).1
    rw [delGraph_eq] at he_del
    refine ⟨isDelGraphEdge_eq_true_iff_mem_toGMDigraph.mpr he_del.1,
      (mem_memberTildeAVList_iff xSeq _ sSeq hs_sub e.1).mpr (Or.inl he1),
      (mem_memberTildeAVList_iff xSeq _ sSeq hs_sub e.2.1).mpr (Or.inl he2)⟩
  · rcases (mem_extraEdges_iff G p xSeq j e).mp he_ex with ⟨heG, hcross, hu_xk, hv_xk, hown⟩
    rcases incidentOwner_valid_of_cross p hWS hRD xSeq hcross hu_xk hv_xk with ⟨hlt, hu_mem, hv_mem⟩
    rcases j with ⟨j_val, hj_lt⟩
    dsimp only at hown hs_sub ⊢
    subst hown
    refine ⟨isDelGraphEdge_eq_true_iff_mem_toGMDigraph.mpr heG,
      (mem_memberTildeAVList_iff xSeq _ sSeq hs_sub e.1).mpr hu_mem,
      (mem_memberTildeAVList_iff xSeq _ sSeq hs_sub e.2.1).mpr hv_mem⟩

theorem flatten_memberTildeAEList_nodup {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hRD : GM13.IsRuralDivision p.toSociety p.toDivision)
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val) :
    (((List.finRange p.members.length).map (memberTildeAEList G p xSeq)).flatten).Nodup := by
  have hDiv := hRD.isDivision
  change ((List.finRange p.members.length).flatMap (memberTildeAEList G p xSeq)).Nodup
  rw [List.nodup_flatMap]
  refine ⟨fun j _ => nodup_memberTildeAEList G p hx_set j, ?_⟩
  refine (List.nodup_finRange p.members.length).imp ?_
  intro j₁ j₂ hne e he₁ he₂
  change e ∈ memberTildeAEList G p xSeq j₁ at he₁
  change e ∈ memberTildeAEList G p xSeq j₂ at he₂
  unfold memberTildeAEList at he₁ he₂
  rw [List.mem_append] at he₁ he₂
  rcases he₁ with hr₁ | hex₁ <;> rcases he₂ with hr₂ | hex₂
  · have hA₁ : (p.members[j₁.1]'j₁.2).toSubgraph (delGraph G X') ∈ p.toDivision :=
      ⟨_, List.getElem_mem j₁.2, rfl⟩
    have hA₂ : (p.members[j₂.1]'j₂.2).toSubgraph (delGraph G X') ∈ p.toDivision :=
      ⟨_, List.getElem_mem j₂.2, rfl⟩
    have hne_A : (p.members[j₁.1]'j₁.2).toSubgraph (delGraph G X') ≠
        (p.members[j₂.1]'j₂.2).toSubgraph (delGraph G X') :=
      fun h => hne (ParsedVisionOutput.member_injective h)
    have heA₁ : e ∈ E((p.members[j₁.1]'j₁.2).toSubgraph (delGraph G X')) := by
      rw [p.edgeSet_member_toSubgraph (List.getElem_mem j₁.2)]
      exact hr₁
    have heA₂ : e ∈ E((p.members[j₂.1]'j₂.2).toSubgraph (delGraph G X')) := by
      rw [p.edgeSet_member_toSubgraph (List.getElem_mem j₂.2)]
      exact hr₂
    exact Set.disjoint_left.mp (hDiv.edge_disjoint hA₁ hA₂ hne_A) heA₁ heA₂
  · have hnot := member_eList_disjoint_xSeq p hx_set j₁ hr₁
    rcases ((mem_extraEdges_iff G p xSeq j₂ e).mp hex₂).2.1 with h1 | h2
    · exact hnot.1 h1
    · exact hnot.2 h2
  · have hnot := member_eList_disjoint_xSeq p hx_set j₂ hr₂
    rcases ((mem_extraEdges_iff G p xSeq j₁ e).mp hex₁).2.1 with h1 | h2
    · exact hnot.1 h1
    · exact hnot.2 h2
  · have hown₁ := ((mem_extraEdges_iff G p xSeq j₁ e).mp hex₁).2.2.2.2
    have hown₂ := ((mem_extraEdges_iff G p xSeq j₂ e).mp hex₂).2.2.2.2
    exact hne (Fin.ext (hown₁.symm.trans hown₂))

theorem flatten_memberTildeAEList_cover {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    (hRD : GM13.IsRuralDivision p.toSociety p.toDivision)
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val) :
    ∀ e ∈ allXKMultiDigraphEdges G xSeq p.K_vList,
      e ∈ ((List.finRange p.members.length).map (memberTildeAEList G p xSeq)).flatten := by
  have hDiv := hRD.isDivision
  have hx_eq : {x : ℕ | x ∈ xSeq} = X'.toNatSet := by
    ext x
    have h := Finset.ext_iff.mp hx_set x
    simpa [Finset.toNatSet] using h
  intro e he
  rcases (mem_allXKMultiDigraphEdges_iff G xSeq p.K_vList e).mp he with ⟨heG, hu_xk, hv_xk⟩
  rw [List.mem_flatten]
  by_cases hcross : e.1 ∈ xSeq ∨ e.2.1 ∈ xSeq
  · rcases incidentOwner_valid_of_cross p hWS hRD xSeq hcross hu_xk hv_xk with ⟨hlt, _, _⟩
    let j : Fin p.members.length := ⟨incidentOwner p xSeq e.1 e.2.1, hlt⟩
    refine ⟨memberTildeAEList G p xSeq j, List.mem_map_of_mem (List.mem_finRange j), ?_⟩
    unfold memberTildeAEList
    exact List.mem_append_right _ ((mem_extraEdges_iff G p xSeq j e).mpr
      ⟨heG, hcross, hu_xk, hv_xk, rfl⟩)
  · push Not at hcross
    have hu_K : e.1 ∈ p.K_vList := hu_xk.resolve_left hcross.1
    have hv_K : e.2.1 ∈ p.K_vList := hv_xk.resolve_left hcross.2
    have hu_notX : e.1 ∉ X'.toNatSet := hx_eq ▸ hcross.1
    have hv_notX : e.2.1 ∉ X'.toNatSet := hx_eq ▸ hcross.2
    have hlink_del : (delGraph G X').IsLink e e.2.1 e.1 := by
      rw [delGraph_eq]
      exact ⟨⟨heG, ⟨heG.2.1, hv_notX⟩, ⟨heG.1, hu_notX⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
    have hu_soc : e.1 ∈ V(p.toSociety.G) := by
      change e.1 ∈ V(p.toCompassGraph)
      rw [p.vertexSet_toCompassGraph]
      exact hu_K
    have hv_soc : e.2.1 ∈ V(p.toSociety.G) := by
      change e.2.1 ∈ V(p.toCompassGraph)
      rw [p.vertexSet_toCompassGraph]
      exact hv_K
    have hlink_soc : p.toSociety.G.IsLink e e.2.1 e.1 := by
      rw [hWS.1] at hu_soc hv_soc ⊢
      dsimp [GM13.wallCompass]
      rw [induce_isLink]
      exact ⟨hlink_del, hv_soc, hu_soc⟩
    have he_soc : e ∈ E(p.toSociety.G) := hlink_soc.edge_mem
    have hunion : E(subgraphSUnion p.toSociety.G p.toDivision) = E(p.toSociety.G) :=
      congrArg Graph.edgeSet hDiv.sUnion_eq
    rw [GM09.edgeSet_subgraphSUnion hDiv.sub_of_mem] at hunion
    rw [← hunion, Set.mem_iUnion₂] at he_soc
    rcases he_soc with ⟨A, ⟨r, hr_mem, rfl⟩, heA⟩
    have heA' : e ∈ E(r.toSubgraph (delGraph G X')) := heA
    rw [p.edgeSet_member_toSubgraph hr_mem, Set.mem_ofPred_eq] at heA'
    rcases List.mem_iff_getElem.mp hr_mem with ⟨j₀, hj₀, rfl⟩
    let j : Fin p.members.length := ⟨j₀, hj₀⟩
    refine ⟨memberTildeAEList G p xSeq j, List.mem_map_of_mem (List.mem_finRange j), ?_⟩
    unfold memberTildeAEList
    exact List.mem_append_left _ heA'

/-- Deleting the `X'`-indices `{x : Fin vList.length | vList[x] ∈ xSeq}` from
`tildeAMultiDigraph vList (memberTildeAEList G p xSeq j)` yields
`tildeAMultiDigraph vList (p.members[j]).eList`. -/
def tildeAXFinset (vList xSeq : List ℕ) : Finset (Fin vList.length) :=
  Finset.univ.filter (fun x : Fin vList.length => (vList[x.1]'x.2) ∈ xSeq)

@[simp]
theorem mem_tildeAXFinset (vList xSeq : List ℕ) (x : Fin vList.length) :
    x ∈ tildeAXFinset vList xSeq ↔ (vList[x.1]'x.2) ∈ xSeq := by
  simp [tildeAXFinset]

theorem card_tildeAXFinset_le (vList xSeq : List ℕ) (hv_nd : vList.Nodup) :
    (tildeAXFinset vList xSeq).card ≤ xSeq.toFinset.card := by
  have hinj : Set.InjOn (fun x : Fin vList.length => vList[x.1]'x.2) (tildeAXFinset vList xSeq) :=
    fun x₁ _ x₂ _ heq => Fin.ext ((hv_nd.getElem_inj_iff).mp heq)
  rw [← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
  exact List.mem_toFinset.mpr ((mem_tildeAXFinset vList xSeq x).mp hx)

theorem tildeAMultiDigraph_deleteVertices_eq {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val)
    (j : Fin p.members.length) (vList : List ℕ) :
    (tildeAMultiDigraph vList (memberTildeAEList G p xSeq j)).deleteVertices
      (tildeAXFinset vList xSeq) =
      tildeAMultiDigraph vList (p.members[j.1]'j.2).eList := by
  ext x y
  simp only [MultiDigraph.deleteVertices_edgeMult, mem_tildeAXFinset, tildeAMultiDigraph]
  by_cases hxy : (vList[x.1]'x.2) ∉ xSeq ∧ (vList[y.1]'y.2) ∉ xSeq
  · rw [ite_eq_left hxy]
    congr 1
    unfold edgesBetween
    have hsub :
        (memberTildeAEList G p xSeq j).filter
          (fun e => decide (e.1 = vList[x.1]'x.2 ∧ e.2.1 = vList[y.1]'y.2)) =
        ((memberTildeAEList G p xSeq j).filter
          (fun e => decide (e.1 ∉ xSeq ∧ e.2.1 ∉ xSeq))).filter
          (fun e => decide (e.1 = vList[x.1]'x.2 ∧ e.2.1 = vList[y.1]'y.2)) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro e _
      by_cases h : e.1 = vList[x.1]'x.2 ∧ e.2.1 = vList[y.1]'y.2
      · rcases h with ⟨h1, h2⟩
        simp [h1, h2, hxy.1, hxy.2]
      · simp [h]
    rw [hsub, filter_memberTildeAEList G p hx_set j]
  · rw [ite_eq_right hxy]
    symm
    rw [List.length_eq_zero_iff, edgesBetween, List.filter_eq_nil_iff]
    intro e he
    simp only [decide_eq_true_eq]
    rintro ⟨he1, he2⟩
    have hnot := member_eList_disjoint_xSeq p hx_set j he
    exact hxy ⟨he1 ▸ hnot.1, he2 ▸ hnot.2⟩

/-- Explicit edge map from `Fin (tildeAMultiDigraph vList r.eList).toComputeDigraph.numEdges`
to `ℕ × ℕ × ℕ` in `r.eList`. -/
noncomputable def tildeADelEdgeTriple (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ))
    (i : Fin (tildeAMultiDigraph vList eList).toComputeDigraph.numEdges) : ℕ × ℕ × ℕ :=
  let G_del := tildeAMultiDigraph vList eList
  let p := (G_del.edgeEquiv i).1
  (edgesBetween eList (vList.getD p.1 0) (vList.getD p.2.1 0)).getD p.2.2 (0, 0, 0)

/-- Leaf-assignment function `f_tau₀ : ℕ → ℕ` on `(tildeAMultiDigraph vList r.eList).toComputeDigraph`
derived from a `Case3MemberRecord` `r`. -/
noncomputable def memberFTau0 (vList : List ℕ) (r : Case3MemberRecord) (i : ℕ) : ℕ :=
  let G_del := tildeAMultiDigraph vList r.eList
  if hi : i < G_del.toComputeDigraph.numEdges then
    r.tauList.getD (r.eList.idxOf (tildeADelEdgeTriple vList r.eList ⟨i, hi⟩)) 0
  else 0

theorem isCubicOrLeafTree_of_isTernaryTree {t : ℕ} {T : SimpleGraph (Fin t)}
    [DecidableRel T.Adj] (hT : GM10.IsTernaryTree T) :
    IsCubicOrLeafTree T := by
  refine ⟨hT.isTree, fun v => ?_⟩
  convert hT.degree_eq_one_or_three v

/-- Synthetic `GM13.Digraph` on `{v | v ∈ vList}` and `{e | e ∈ eList}`. -/
def listDigraph (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ))
    (he_ends : ∀ e ∈ eList, e.1 ∈ vList ∧ e.2.1 ∈ vList) :
    GM13.Digraph ℕ (ℕ × ℕ × ℕ) where
  vertexSet := {v : ℕ | v ∈ vList}
  edgeSet := {e : ℕ × ℕ × ℕ | e ∈ eList}
  tail e := e.1
  head e := e.2.1
  tail_mem e he := (he_ends e he).1
  head_mem e he := (he_ends e he).2

theorem tildeADelEdgeTriple_mem_and_bijOn (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ))
    (hv_nd : vList.Nodup) (he_nd : eList.Nodup)
    (he_ends : ∀ e ∈ eList, e.1 ∈ vList ∧ e.2.1 ∈ vList) :
    let G_del := tildeAMultiDigraph vList eList
    G_del.toComputeDigraph.numEdges = eList.length ∧
    Set.BijOn (tildeADelEdgeTriple vList eList) Set.univ {e : ℕ × ℕ × ℕ | e ∈ eList} ∧
    ∀ i : Fin G_del.toComputeDigraph.numEdges,
      let e := tildeADelEdgeTriple vList eList i
      e ∈ eList ∧
      e.1 = vList[(G_del.toComputeDigraph.tail i).1]'(G_del.toComputeDigraph.tail i).2 ∧
      e.2.1 = vList[(G_del.toComputeDigraph.head i).1]'(G_del.toComputeDigraph.head i).2 := by
  intro G_del
  let D₀ := listDigraph vList eList he_ends
  have he_ends' : ∀ e ∈ eList, D₀.tail e = e.1 ∧ D₀.head e = e.2.1 ∧ e.1 ∈ vList ∧ e.2.1 ∈ vList :=
    fun e he => ⟨rfl, rfl, (he_ends e he).1, (he_ends e he).2⟩
  let iso := isoTildeAMultiDigraph D₀ vList eList hv_nd rfl he_nd rfl he_ends'
  have hnum : G_del.toComputeDigraph.numEdges = eList.length := by
    change G_del.directedEdgesList.length = eList.length
    rw [G_del.length_directedEdgesList]
    exact numEdges_tildeAMultiDigraph D₀ vList eList hv_nd rfl he_nd rfl he_ends'
  have hbij_eq :
      tildeADelEdgeTriple vList eList =
        fun i : Fin G_del.toComputeDigraph.numEdges => iso.eMap (G_del.edgeEquiv i).1 := rfl
  have hbij : Set.BijOn (tildeADelEdgeTriple vList eList) Set.univ {e : ℕ × ℕ × ℕ | e ∈ eList} := by
    rw [hbij_eq]
    refine ⟨fun i _ => iso.bijOn_e.mapsTo (G_del.edgeEquiv i).2,
      fun i₁ _ i₂ _ heq => ?_,
      fun e he => ?_⟩
    · have hp_eq := iso.bijOn_e.injOn (G_del.edgeEquiv i₁).2 (G_del.edgeEquiv i₂).2 heq
      exact G_del.edgeEquiv.injective (Subtype.ext hp_eq)
    · rcases iso.bijOn_e.surjOn he with ⟨p, hp, rfl⟩
      refine ⟨G_del.edgeEquiv.symm ⟨p, hp⟩, Set.mem_univ _, ?_⟩
      simp
  refine ⟨hnum, hbij, fun i => ?_⟩
  have he_mem : tildeADelEdgeTriple vList eList i ∈ eList :=
    hbij.mapsTo (Set.mem_univ i)
  have hpair := G_del.getElem_directedEdgeTriples_fst_snd i.1 i.2
  have htail_eq : (G_del.edgeEquiv i).1.1 = (G_del.toComputeDigraph.tail i).1 :=
    congrArg Prod.fst hpair
  have hhead_eq : (G_del.edgeEquiv i).1.2.1 = (G_del.toComputeDigraph.head i).1 :=
    congrArg Prod.snd hpair
  have htail_iso := iso.tail_eq (G_del.edgeEquiv i).2
  have hhead_iso := iso.head_eq (G_del.edgeEquiv i).2
  change (tildeADelEdgeTriple vList eList i).1 =
    vList.getD (G_del.edgeEquiv i).1.1 0 at htail_iso
  change (tildeADelEdgeTriple vList eList i).2.1 =
    vList.getD (G_del.edgeEquiv i).1.2.1 0 at hhead_iso
  rw [htail_eq, List.getD_eq_getElem _ _ (G_del.toComputeDigraph.tail i).2] at htail_iso
  rw [hhead_eq, List.getD_eq_getElem _ _ (G_del.toComputeDigraph.head i).2] at hhead_iso
  exact ⟨he_mem, htail_iso, hhead_iso⟩

/-- Bridge from `p.branchDecomp_toSubgraph` on an interior member `r = p.members[j]` to
`IsWrittenDigraphBD ω (tildeAMultiDigraph vList r.eList).toComputeDigraph r.t_len (r.parList.getD · 0) (memberFTau0 vList r)`. -/
theorem isWrittenDigraphBD_of_member {n ω : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    (vList : List ℕ) (hv_nd : vList.Nodup)
    (hr_sub_v : ∀ v ∈ r.vList, v ∈ vList)
    (hbd_in :
      let A := r.toSubgraph (delGraph G X')
      let bd := r.toBranchDecomp
      E(A).ncard ≤ 1 ∨
        (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
          GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)) :
    IsWrittenDigraphBD ω (tildeAMultiDigraph vList r.eList).toComputeDigraph
      r.t_len (fun z => r.parList.getD z 0) (memberFTau0 vList r) := by
  have hr_val := p.member_valid_iff hr
  rcases hr_val with ⟨_, _, _, _, he_nd, he_valid, ht1, ht_le, hpar_len, hpar_lt, htau_len, htau_lt⟩
  let G_del := tildeAMultiDigraph vList r.eList
  have he_ends : ∀ e ∈ r.eList, e.1 ∈ vList ∧ e.2.1 ∈ vList := fun e he =>
    ⟨hr_sub_v e.1 (he_valid e he).2.1, hr_sub_v e.2.1 (he_valid e he).2.2⟩
  rcases tildeADelEdgeTriple_mem_and_bijOn vList r.eList hv_nd he_nd he_ends with
    ⟨hnum, hbij, htriple_props⟩
  have htau_bound : ∀ i < G_del.toComputeDigraph.numEdges, memberFTau0 vList r i < r.t_len := by
    intro i hi
    unfold memberFTau0
    rw [dite_eq_left hi]
    have he_mem : tildeADelEdgeTriple vList r.eList ⟨i, hi⟩ ∈ r.eList :=
      (htriple_props ⟨i, hi⟩).1
    have hidx_lt : r.eList.idxOf (tildeADelEdgeTriple vList r.eList ⟨i, hi⟩) < r.tauList.length := by
      rw [htau_len]
      exact List.idxOf_lt_length_of_mem he_mem
    rw [List.getD_eq_getElem _ _ hidx_lt]
    exact htau_lt _ (List.getElem_mem hidx_lt)
  refine ⟨ht1, by rw [hnum]; exact ht_le, hpar_lt, htau_bound, ?_⟩
  by_cases hle1 : G_del.toComputeDigraph.numEdges ≤ 1
  · exact Or.inl hle1
  · right
    refine ⟨htau_bound, ?_⟩
    let A := r.toSubgraph (delGraph G X')
    have hEA_eq : E(A) = {e : ℕ × ℕ × ℕ | e ∈ r.eList} :=
      p.edgeSet_member_toSubgraph hr
    have hVA_eq : V(A) = {v : ℕ | v ∈ r.vList} :=
      p.vertexSet_member_toSubgraph hr
    have hEA_ncard : E(A).ncard = r.eList.length := by
      have hset : E(A) = ↑r.eList.toFinset := by
        rw [hEA_eq]; ext e; simp
      rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup he_nd]
    rcases hbd_in with hEA_le1 | ⟨hbd_A, hwidth_A⟩
    · change E(A).ncard ≤ 1 at hEA_le1
      change G_del.toComputeDigraph.numEdges = r.eList.length at hnum
      omega
    · have ht_max : max r.t_len 1 = r.t_len := Nat.max_eq_left ht1
      let par₀ (z : ℕ) : ℕ := r.parList.getD z 0
      let T := parentTree r.t_len par₀
      let τ₀ (i : Fin G_del.toComputeDigraph.numEdges) : Fin r.t_len :=
        ⟨memberFTau0 vList r i.1, htau_bound i.1 i.2⟩
      let τ_r (e : ℕ × ℕ × ℕ) : Fin r.t_len :=
        let idx := r.eList.idxOf e
        let u := r.tauList.getD idx 0
        if hu : u < r.t_len then ⟨u, hu⟩ else ⟨0, ht1⟩
      have hbd_eq : r.toBranchDecomp = ⟨r.t_len, T, τ_r⟩ := by
        unfold Case3MemberRecord.toBranchDecomp
        dsimp only [T, par₀, τ_r]
        generalize_proofs hp
        revert hp
        rw [ht_max]
        intro _
        rfl
      rw [hbd_eq] at hbd_A hwidth_A
      dsimp only at hbd_A hwidth_A
      have hτ₀_eq : ∀ i : Fin G_del.toComputeDigraph.numEdges,
          τ₀ i = τ_r (tildeADelEdgeTriple vList r.eList i) := by
        intro i
        ext
        dsimp only [τ₀, τ_r]
        unfold memberFTau0
        dsimp only
        have hi_lt : i.1 < G_del.toComputeDigraph.numEdges := i.2
        rw [dite_eq_left hi_lt]
        have hlt := htau_bound i.1 i.2
        unfold memberFTau0 at hlt
        dsimp only at hlt
        rw [dite_eq_left hi_lt] at hlt
        rw [dite_eq_left hlt]
      have hT_cubic : IsCubicOrLeafTree T := by
        rcases hbd_A.1 with h_empty | htern
        · exact False.elim (@IsEmpty.false _ h_empty ⟨0, ht1⟩)
        · exact isCubicOrLeafTree_of_isTernaryTree htern
      refine ⟨hT_cubic, ?_, ?_⟩
      · rw [coe_treeLeaves_eq_leafSet_of_cubic hT_cubic]
        change Set.BijOn τ₀ Set.univ (GM10.leafSet T)
        have hcomp : τ₀ = τ_r ∘ tildeADelEdgeTriple vList r.eList := funext hτ₀_eq
        rw [← hEA_eq] at hbij
        rw [hcomp]
        exact hbd_A.2.comp hbij
      · intro f hf
        have hf_mem : f ∈ T.edgeSet := Set.mem_toFinset.mp hf
        let cutA : Set ℕ :=
          {v ∈ V(A) | ∃ e₁ ∈ E(A), ∃ e₂ ∈ E(A),
            ¬ (T.deleteEdges {f}).Reachable (τ_r e₁) (τ_r e₂) ∧
            A.Inc e₁ v ∧ A.Inc e₂ v}
        have hcutA_fin : cutA.Finite :=
          (finite_vertexSet_subgraphOfLists (delGraph G X') r.vList r.eList).subset
            (fun _ hv => hv.1)
        have hcut_sub :
            ((digraphTreeEdgeCutVerts G_del.toComputeDigraph T τ₀ f).image
              (fun w : Fin vList.length => vList[w.1]'w.2) : Set ℕ) ⊆ cutA := by
          intro v hv
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
          rcases hv with ⟨w, hw, rfl⟩
          rcases (mem_digraphTreeEdgeCutVerts_iff G_del.toComputeDigraph T τ₀ f w).mp hw with
            ⟨i₁, i₂, hinc₁, hinc₂, hnr⟩
          let e₁ := tildeADelEdgeTriple vList r.eList i₁
          let e₂ := tildeADelEdgeTriple vList r.eList i₂
          rcases htriple_props i₁ with ⟨he₁_mem, he₁_1, he₁_2⟩
          rcases htriple_props i₂ with ⟨he₂_mem, he₂_1, he₂_2⟩
          have he₁_A : e₁ ∈ E(A) := by rw [hEA_eq]; exact he₁_mem
          have he₂_A : e₂ ∈ E(A) := by rw [hEA_eq]; exact he₂_mem
          have hinc_to_A :
              ∀ (i : Fin G_del.toComputeDigraph.numEdges),
                digraphIncident G_del.toComputeDigraph w i →
                vList[w.1]'w.2 ∈ V(A) ∧
                A.Inc (tildeADelEdgeTriple vList r.eList i) (vList[w.1]'w.2) := by
            intro i hinc
            let e := tildeADelEdgeTriple vList r.eList i
            rcases htriple_props i with ⟨he_mem, he_1, he_2⟩
            rcases he_valid e he_mem with ⟨heK, he_v1, he_v2⟩
            have he_del := (p.K_eList_mem_delGraph heK).1
            have hlink_del : (delGraph G X').IsLink e e.2.1 e.1 := by
              rw [delGraph_eq] at he_del ⊢
              exact ⟨he_del, Or.inl ⟨rfl, rfl⟩⟩
            have hle_A : A ≤ delGraph G X' := subgraphOfLists_le _ _ _
            have he_A : e ∈ E(A) := by rw [hEA_eq]; exact he_mem
            have hlink_A : A.IsLink e e.2.1 e.1 := (hle_A.isLink_iff he_A).mpr hlink_del
            rcases hinc with hhead | htail
            · subst hhead
              rw [← he_2]
              exact ⟨hlink_A.left_mem, ⟨e.1, hlink_A⟩⟩
            · subst htail
              rw [← he_1]
              exact ⟨hlink_A.right_mem, ⟨e.2.1, hlink_A.symm⟩⟩
          rcases hinc_to_A i₁ hinc₁ with ⟨hvA, hA_inc₁⟩
          rcases hinc_to_A i₂ hinc₂ with ⟨_, hA_inc₂⟩
          rw [hτ₀_eq i₁, hτ₀_eq i₂] at hnr
          exact ⟨hvA, e₁, he₁_A, e₂, he₂_A, hnr, hA_inc₁, hA_inc₂⟩
        have hinj_v : Function.Injective (fun w : Fin vList.length => vList[w.1]'w.2) :=
          fun w₁ w₂ heq => Fin.ext ((hv_nd.getElem_inj_iff).mp heq)
        have hcard_le_ord :
            (digraphTreeEdgeCutVerts G_del.toComputeDigraph T τ₀ f).card ≤
              GM13.graphBranchEdgeOrder A T τ_r f := by
          rw [← Finset.card_image_of_injective _ hinj_v, ← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard hcut_sub hcutA_fin
        have hord_le_width :
            GM13.graphBranchEdgeOrder A T τ_r f ≤ GM13.graphBranchDecompWidth A T τ_r := by
          unfold GM13.graphBranchDecompWidth
          apply le_csSup
          · exact ⟨(V(A).ncard : ℕ), by
              rintro _ ⟨f', _, rfl⟩
              exact Set.ncard_le_ncard (fun _ hv => hv.1)
                (finite_vertexSet_subgraphOfLists (delGraph G X') r.vList r.eList)⟩
          · exact ⟨f, hf_mem, rfl⟩
        exact (hcard_le_ord.trans hord_le_width).trans hwidth_A

/-! ### Section 3: Steps 1 & 4 Compass Adjacency, Menger Non-Separation, and `traceWalkStopB` -/

/-- The vertex subset `{u : Fin n | u.1 ∉ p.K_vList}` outside the compass `K`. -/
def Z_notK {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n => u.1 ∉ p.K_vList)

@[simp]
theorem mem_Z_notK_iff {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (u : Fin n) :
    u ∈ Z_notK p ↔ u.1 ∉ p.K_vList := by
  simp [Z_notK]

theorem isKEdgeBetween_eq_true_iff (K_eList : List (ℕ × ℕ × ℕ)) (u v : ℕ) :
    isKEdgeBetween K_eList u v = true ↔
      u ≠ v ∧ ∃ e ∈ K_eList, (e.1 = u ∧ e.2.1 = v) ∨ (e.1 = v ∧ e.2.1 = u) := by
  unfold isKEdgeBetween
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  refine and_congr_right' (exists_congr fun e => and_congr_right' ?_)
  tauto

/-- Under `IsWallSociety (delGraph G X') p.toGMWall p.toSociety`, adjacency in
`G_K = (G.deleteVertices (Z_notK p)).toSimpleGraph` is equivalent to
`isKEdgeBetween p.K_eList u.1 v.1 = true`. -/
theorem G_K_adj_iff_isKEdgeBetween {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    (u v : Fin n) :
    ((G.deleteVertices (Z_notK p)).toSimpleGraph).Adj u v ↔
      isKEdgeBetween p.K_eList u.1 v.1 = true := by
  rw [MultiDigraph.toSimpleGraph_adj, isKEdgeBetween_eq_true_iff]
  simp only [MultiDigraph.deleteVertices_edgeMult, mem_Z_notK_iff, not_not]
  constructor
  · rintro ⟨hne, hpos⟩
    have hne_val : u.1 ≠ v.1 := Fin.val_ne_of_ne hne
    by_cases hK : u.1 ∈ p.K_vList ∧ v.1 ∈ p.K_vList
    · rcases hK with ⟨huK, hvK⟩
      have hu_del := p.K_vList_mem_delGraph huK
      have hv_del := p.K_vList_mem_delGraph hvK
      rw [vertexSet_delGraph] at hu_del hv_del
      have hu_soc : u.1 ∈ V(p.toSociety.G) := by
        change u.1 ∈ V(p.toCompassGraph)
        rw [p.vertexSet_toCompassGraph]; exact huK
      have hv_soc : v.1 ∈ V(p.toSociety.G) := by
        change v.1 ∈ V(p.toCompassGraph)
        rw [p.vertexSet_toCompassGraph]; exact hvK
      rw [ite_eq_left ⟨huK, hvK⟩, ite_eq_left ⟨hvK, huK⟩] at hpos
      have hex_edge :
          (0 < G.edgeMult u v) ∨ (0 < G.edgeMult v u) := by omega
      rcases hex_edge with huv | hvu
      · let e : ℕ × ℕ × ℕ := (u.1, v.1, 0)
        have hlink_del : (delGraph G X').IsLink e v.1 u.1 := by
          rw [delGraph_eq]
          exact ⟨⟨⟨u.2, v.2, huv⟩, hv_del, hu_del⟩, Or.inl ⟨rfl, rfl⟩⟩
        have hlink_soc : p.toSociety.G.IsLink e v.1 u.1 := by
          rw [hWS.1] at hu_soc hv_soc ⊢
          dsimp [GM13.wallCompass]
          rw [induce_isLink]
          exact ⟨hlink_del, hv_soc, hu_soc⟩
        have he_mem : e ∈ p.K_eList := by
          have hm := hlink_soc.edge_mem
          change e ∈ E(p.toCompassGraph) at hm
          rwa [p.edgeSet_toCompassGraph] at hm
        exact ⟨hne_val, e, he_mem, Or.inl ⟨rfl, rfl⟩⟩
      · let e : ℕ × ℕ × ℕ := (v.1, u.1, 0)
        have hlink_del : (delGraph G X').IsLink e u.1 v.1 := by
          rw [delGraph_eq]
          exact ⟨⟨⟨v.2, u.2, hvu⟩, hu_del, hv_del⟩, Or.inl ⟨rfl, rfl⟩⟩
        have hlink_soc : p.toSociety.G.IsLink e u.1 v.1 := by
          rw [hWS.1] at hu_soc hv_soc ⊢
          dsimp [GM13.wallCompass]
          rw [induce_isLink]
          exact ⟨hlink_del, hu_soc, hv_soc⟩
        have he_mem : e ∈ p.K_eList := by
          have hm := hlink_soc.edge_mem
          change e ∈ E(p.toCompassGraph) at hm
          rwa [p.edgeSet_toCompassGraph] at hm
        exact ⟨hne_val, e, he_mem, Or.inr ⟨rfl, rfl⟩⟩
    · have h1 : ¬ (u.1 ∈ p.K_vList ∧ v.1 ∈ p.K_vList) := hK
      have h2 : ¬ (v.1 ∈ p.K_vList ∧ u.1 ∈ p.K_vList) := fun ⟨hA, hB⟩ => hK ⟨hB, hA⟩
      rw [ite_eq_right h1, ite_eq_right h2] at hpos
      omega
  · rintro ⟨hne_val, e, heK, ⟨he1, he2⟩ | ⟨he1, he2⟩⟩
    · have hne : u ≠ v := fun h => hne_val (congrArg Fin.val h)
      rcases p.hK_e_valid e heK with ⟨_, he1_K, he2_K⟩
      have huK : u.1 ∈ p.K_vList := he1 ▸ he1_K
      have hvK : v.1 ∈ p.K_vList := he2 ▸ he2_K
      have he_del := (p.K_eList_mem_delGraph heK).1
      rw [delGraph_eq] at he_del
      have hm : e.2.2 < G.edgeMult u v := by
        have h := he_del.1.2.2
        rcases e with ⟨u', v', k'⟩
        dsimp only at he1 he2 h
        subst he1 he2
        exact h
      refine ⟨hne, ?_⟩
      rw [ite_eq_left ⟨huK, hvK⟩]
      omega
    · have hne : u ≠ v := fun h => hne_val (congrArg Fin.val h)
      rcases p.hK_e_valid e heK with ⟨_, he1_K, he2_K⟩
      have hvK : v.1 ∈ p.K_vList := he1 ▸ he1_K
      have huK : u.1 ∈ p.K_vList := he2 ▸ he2_K
      have he_del := (p.K_eList_mem_delGraph heK).1
      rw [delGraph_eq] at he_del
      have hm : e.2.2 < G.edgeMult v u := by
        have h := he_del.1.2.2
        rcases e with ⟨v', u', k'⟩
        dsimp only at he1 he2 h
        subst he1 he2
        exact h
      refine ⟨hne, ?_⟩
      rw [ite_eq_left ⟨huK, hvK⟩, ite_eq_left ⟨hvK, huK⟩]
      omega

/-- Any `GraphWalk p.toSociety.G s t` lifts to a `SimpleGraph.Walk` in
`G_K = (G.deleteVertices (Z_notK p)).toSimpleGraph` whose vertex support is contained in `w.support`. -/
theorem exists_walk_G_K_of_graphWalk {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    {s t : ℕ} (w : GraphWalk p.toSociety.G s t) :
    ∃ (u v : Fin n) (w' : ((G.deleteVertices (Z_notK p)).toSimpleGraph).Walk u v),
      u.1 = s ∧ v.1 = t ∧ ∀ x ∈ w'.support, x.1 ∈ w.support := by
  induction w with
  | @nil x hx =>
    have hxK : x ∈ p.K_vList := by
      change x ∈ V(p.toCompassGraph) at hx
      rwa [p.vertexSet_toCompassGraph] at hx
    have hx_lt : x < n :=
      ((mem_vertexSet_delGraph_iff G X' x).mp (p.K_vList_mem_delGraph hxK)).1
    refine ⟨⟨x, hx_lt⟩, ⟨x, hx_lt⟩, .nil, rfl, rfl, fun u hu => ?_⟩
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    subst hu
    exact List.mem_singleton.mpr rfl
  | @cons x y z e hlink w_tail ih =>
    rcases ih with ⟨u_y, u_z, w_yz, hy_eq, hz_eq, hsup⟩
    have hx_soc : x ∈ V(p.toSociety.G) := hlink.left_mem
    have hxK : x ∈ p.K_vList := by
      change x ∈ V(p.toCompassGraph) at hx_soc
      rwa [p.vertexSet_toCompassGraph] at hx_soc
    have hx_lt : x < n :=
      ((mem_vertexSet_delGraph_iff G X' x).mp (p.K_vList_mem_delGraph hxK)).1
    let u_x : Fin n := ⟨x, hx_lt⟩
    by_cases hxy : u_x = u_y
    · subst hxy
      refine ⟨u_x, u_z, w_yz, rfl, hz_eq, fun w_u hw_u => ?_⟩
      simp only [GraphWalk.support_cons, List.mem_cons]
      exact Or.inr (hsup w_u hw_u)
    · have hne_val : x ≠ y := by
        intro h
        apply hxy
        exact Fin.ext (h.trans hy_eq.symm)
      have hadj : ((G.deleteVertices (Z_notK p)).toSimpleGraph).Adj u_x u_y := by
        rw [G_K_adj_iff_isKEdgeBetween p hWS, isKEdgeBetween_eq_true_iff]
        rcases (toCompassGraph_isLink_iff p).mp hlink with ⟨heK, ⟨he2, he1⟩ | ⟨he2, he1⟩⟩
        · exact ⟨by simpa [u_x, hy_eq] using hne_val, e, heK,
            Or.inr ⟨by simpa [u_x, hy_eq] using he1, by simpa [u_x] using he2⟩⟩
        · exact ⟨by simpa [u_x, hy_eq] using hne_val, e, heK,
            Or.inl ⟨by simpa [u_x] using he1, by simpa [u_x, hy_eq] using he2⟩⟩
      refine ⟨u_x, u_z, .cons hadj w_yz, rfl, hz_eq, fun w_u hw_u => ?_⟩
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw_u
      simp only [GraphWalk.support_cons, List.mem_cons]
      rcases hw_u with rfl | hw_u
      · exact Or.inl rfl
      · exact Or.inr (hsup w_u hw_u)

/-- Any path `IsGraphPathWithEnds p.toSociety.G P s t` lifts to a `SimpleGraph.Walk` in
`G_K = (G.deleteVertices (Z_notK p)).toSimpleGraph` whose vertex support lies in `V(P)`. -/
theorem exists_walk_G_K_of_isGraphPathWithEnds {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    {P : Graph ℕ (ℕ × ℕ × ℕ)} {s t : ℕ}
    (hP : GM09.IsGraphPathWithEnds p.toSociety.G P s t) :
    ∃ (u v : Fin n) (w' : ((G.deleteVertices (Z_notK p)).toSimpleGraph).Walk u v),
      u.1 = s ∧ v.1 = t ∧ ∀ x ∈ w'.support, x.1 ∈ V(P) := by
  rcases hP with ⟨hPG, W, _, hV, _⟩
  rcases W.exists_transfer (fun _ _ _ _ hl => hl.mono hPG)
      (fun _ hx => hPG.vertexSet_mono (W.mem_vertexSet_of_mem_support hx)) with ⟨W', hW'_sup, _⟩
  rcases exists_walk_G_K_of_graphWalk p hWS W' with ⟨u, v, w', hu, hv, hsup⟩
  refine ⟨u, v, w', hu, hv, fun x hx => ?_⟩
  rw [hV, Set.mem_ofPred_eq, ← hW'_sup]
  exact hsup x hx

/-- In Step 1 of Algorithm (10.1), when `(memberBoundaryList p.corners p.K_eList r).length = 3`,
there is no separator of size `< 3` in `G_K` between `A_bd` and `B_bar`. -/
theorem not_isABSeparator_step1 {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    (hDiv : GM13.IsSocietyDivision p.toSociety p.toDivision)
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    (hlen3 : (memberBoundaryList p.corners p.K_eList r).length = 3)
    (S_sep : Finset (Fin n)) :
    ¬ (IsABSeparator (G.deleteVertices (Z_notK p)).toSimpleGraph
        (Finset.univ.filter (fun u : Fin n => u.1 ∈ memberBoundaryList p.corners p.K_eList r))
        (Finset.univ.filter (fun u : Fin n => u.1 ∈ p.corners)) S_sep ∧ S_sep.card < 3) := by
  rintro ⟨hsep, hlt⟩
  let A_G := r.toSubgraph (delGraph G X')
  have hA_mem : A_G ∈ p.toDivision := ⟨r, hr, rfl⟩
  let B := GM13.divBoundary p.toSociety A_G
  have hB_eq : B = ((memberBoundaryList p.corners p.K_eList r).toFinset : Set ℕ) := by
    ext x
    simp only [B, A_G, Finset.mem_coe, List.mem_toFinset, mem_memberBoundaryList_iff p hr]
  have hB_ncard : B.ncard = 3 := by
    rw [hB_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_memberBoundaryList p hr)]
    exact hlen3
  obtain ⟨P₀, hP₀_disj, hP₀_paths⟩ := hDiv.disjoint_paths_to_bar hA_mem
  let eFin : Fin 3 ≃ Fin B.ncard := finCongr hB_ncard.symm
  have hwalk_ex : ∀ i : Fin 3, ∃ z ∈ S_sep, z.1 ∈ V(P₀ (eFin i)) := by
    intro i
    obtain ⟨s₀, hs₀, t₀, ht₀, hpath₀⟩ := hP₀_paths (eFin i)
    obtain ⟨u, v, w', hu, hv, hsup⟩ := exists_walk_G_K_of_isGraphPathWithEnds p hWS hpath₀
    have hu_A : u ∈ Finset.univ.filter (fun u : Fin n => u.1 ∈ memberBoundaryList p.corners p.K_eList r) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hu]
      exact (mem_memberBoundaryList_iff p hr s₀).mpr hs₀
    have hv_B : v ∈ Finset.univ.filter (fun u : Fin n => u.1 ∈ p.corners) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv]
      exact (mem_corners_iff_mem_bar p t₀).mpr ht₀
    obtain ⟨z, hz_sep, hz_sup⟩ := hsep ⟨u, v, hu_A, hv_B, w'⟩
    exact ⟨z, hz_sep, hsup z hz_sup⟩
  choose z hz_sep hz_mem using hwalk_ex
  let f : Fin 3 → S_sep := fun i => ⟨z i, hz_sep i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hz_eq : z i = z j := congrArg Subtype.val hij
    by_contra hne
    have hdisj := hP₀_disj (eFin.injective.ne hne)
    exact Set.disjoint_left.mp hdisj (hz_mem i) (hz_eq ▸ hz_mem j)
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

/-- In Step 4 of Algorithm (10.1), for every interior member `r ∈ p.members`,
there is no separator of size `< 1` in `G_K` between `A_start` and `p.wallSec.W.vertexFinset`. -/
theorem not_isABSeparator_step4 {n q : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q X'.toNatSet p.toGMWall p.toSociety p.toDivision)
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    (hInt : isMemberInterior p.wallSec.W r = true)
    (S_sep : Finset (Fin n)) :
    let bList := memberBoundaryList p.corners p.K_eList r
    let startList := if bList.isEmpty then r.vList else bList
    ¬ (IsABSeparator (G.deleteVertices (Z_notK p)).toSimpleGraph
        (Finset.univ.filter (fun u : Fin n => u.1 ∈ startList))
        p.wallSec.W.vertexFinset S_sep ∧ S_sep.card < 1) := by
  intro bList startList
  rintro ⟨hsep, hlt⟩
  have hInt_GM : GM13.IsInteriorMember p.toGMWall p.toDivision (r.toSubgraph (delGraph G X')) :=
    (isInteriorMember_toSubgraph_iff p hr).mpr hInt
  obtain ⟨v, hvH, P, s, hs_cond, hP, _⟩ := GM13.exists_vOf_of_isInteriorMember hC hInt_GM
  have hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety := by
    rw [delGraph_eq]; exact hC.isWallSociety
  obtain ⟨u_s, u_v, w', hu_s, hu_v, _⟩ :=
    exists_walk_G_K_of_isGraphPathWithEnds p hWS hP
  have hu_A : u_s ∈ Finset.univ.filter (fun u : Fin n => u.1 ∈ startList) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hu_s, startList]
    rcases hs_cond with hs_bd | ⟨hemp, hs_v⟩
    · have hs_bList : s ∈ bList := (mem_memberBoundaryList_iff p hr s).mpr hs_bd
      have hne : bList.isEmpty = false := List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hs_bList)
      rw [ite_eq_right (by simp [hne])]
      exact hs_bList
    · have hnil : bList = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        have hx_bd := (mem_memberBoundaryList_iff p hr x).mp hx
        rw [hemp] at hx_bd
        exact hx_bd
      have he : bList.isEmpty = true := by simp [hnil]
      rw [ite_eq_left he]
      rw [p.vertexSet_member_toSubgraph hr] at hs_v
      exact hs_v
  have hu_B : u_v ∈ p.wallSec.W.vertexFinset := by
    have hv_fin : v ∈ p.wallSec.W.vertexFinset.toNatSet := by
      rwa [← p.wallSec.W.vertexSet_toGMWall_eq_vertexFinset p.wallSec.h2 p.wallSec.he p.wallSec.hW]
    rcases hv_fin with ⟨w_u, hw_u, hw_eq⟩
    have heq : u_v = w_u := Fin.ext (hu_v.trans hw_eq.symm)
    rwa [heq]
  obtain ⟨z, hz_sep, _⟩ := hsep ⟨u_s, u_v, hu_A, hu_B, w'⟩
  have hpos : 0 < S_sep.card := Finset.card_pos.mpr ⟨z, hz_sep⟩
  omega

/-- Walk construction following `succ` for up to `fuel` steps, stopping as soon as a vertex in `B`
is reached. -/
def traceWalkStopB {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ) :
    ℕ → ∀ u : Fin n, Σ z : Fin n, G.Walk u z
  | 0, u => ⟨u, .nil⟩
  | d + 1, u =>
    if _hB : u ∈ B then
      ⟨u, .nil⟩
    else if h : succ u < n then
      let ⟨z, w⟩ := traceWalkStopB hsys d ⟨succ u, h⟩
      ⟨z, .cons (hsys.adj_of_succ u ⟨succ u, h⟩ rfl).2.2 w⟩
    else
      ⟨u, .nil⟩

theorem traceWalkStopB_succ_of_mem_B {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    (d : ℕ) (u : Fin n) (hB : u ∈ B) :
    traceWalkStopB hsys (d + 1) u = ⟨u, .nil⟩ := by
  dsimp only [traceWalkStopB]
  simp only [hB, ↓reduceDIte]

theorem traceWalkStopB_succ_of_lt {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    (d : ℕ) (u : Fin n) (hB : u ∉ B) (h : succ u < n) :
    traceWalkStopB hsys (d + 1) u =
      ⟨(traceWalkStopB hsys d ⟨succ u, h⟩).1,
        .cons (hsys.adj_of_succ u ⟨succ u, h⟩ rfl).2.2 (traceWalkStopB hsys d ⟨succ u, h⟩).2⟩ := by
  dsimp only [traceWalkStopB]
  simp only [hB, h, ↓reduceDIte]

theorem traceWalkStopB_succ_of_not_lt {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    (d : ℕ) (u : Fin n) (hB : u ∉ B) (h : ¬ succ u < n) :
    traceWalkStopB hsys (d + 1) u = ⟨u, .nil⟩ := by
  dsimp only [traceWalkStopB]
  simp only [hB, h, ↓reduceDIte]

/-- Combined induction invariant for `traceWalkStopB hsys fuel u` when `succAt succ k u₀ = some u`:
1. the walk support is nodup (`IsPath`),
2. every vertex in the support is of the form `succAt succ (k + j) u₀` for some `j ≤ fuel`,
3. either the walk's endpoint belongs to `B`, or `succAt succ (k + fuel) u₀ = some endpoint`,
4. any vertex in the walk support that belongs to `B` is the endpoint. -/
theorem traceWalkStopB_props {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    {u₀ : Fin n} (hu₀ : u₀ ∈ pathStarts used pred) :
    ∀ (fuel k : ℕ) (u : Fin n),
      succAt succ k u₀ = some u →
      (traceWalkStopB hsys fuel u).2.support.Nodup ∧
      (∀ x ∈ (traceWalkStopB hsys fuel u).2.support, ∃ j ≤ fuel, succAt succ (k + j) u₀ = some x) ∧
      ((traceWalkStopB hsys fuel u).1 ∈ B ∨
        succAt succ (k + fuel) u₀ = some (traceWalkStopB hsys fuel u).1) ∧
      (∀ x ∈ (traceWalkStopB hsys fuel u).2.support, x ∈ B → x = (traceWalkStopB hsys fuel u).1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k u hku
    simp only [traceWalkStopB, SimpleGraph.Walk.support_nil, List.nodup_singleton,
      List.mem_singleton, Nat.add_zero, true_and]
    refine ⟨?_, Or.inr hku, fun x hx _ => hx⟩
    rintro x rfl
    exact ⟨0, le_rfl, hku⟩
  | succ d ih =>
    intro k u hku
    by_cases hB : u ∈ B
    · rw [traceWalkStopB_succ_of_mem_B hsys d u hB]
      simp only [SimpleGraph.Walk.support_nil, List.nodup_singleton, List.mem_singleton, true_and]
      refine ⟨?_, Or.inl hB, fun x hx _ => hx⟩
      rintro x rfl
      exact ⟨0, Nat.zero_le _, by simpa using hku⟩
    · by_cases h : succ u < n
      · rw [traceWalkStopB_succ_of_lt hsys d u hB h]
        let v : Fin n := ⟨succ u, h⟩
        have hkv : succAt succ (k + 1) u₀ = some v :=
          (succAt_add_one k u₀ v).mpr ⟨u, hku, rfl⟩
        rcases ih (k + 1) v hkv with ⟨hnodup_v, hmem_v, hend_v, hstop_v⟩
        simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons]
        refine ⟨⟨?_, hnodup_v⟩, ?_, ?_, ?_⟩
        · intro hu_in
          rcases hmem_v u hu_in with ⟨j, _, hj⟩
          have ⟨_, heq⟩ := succAt_inj_of_pathStarts hsys hu₀ hu₀ hku hj
          omega
        · rintro x (rfl | hx)
          · exact ⟨0, Nat.zero_le _, by simpa using hku⟩
          · rcases hmem_v x hx with ⟨j, hj_le, hj⟩
            exact ⟨j + 1, Nat.add_le_add_right hj_le 1,
              by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj⟩
        · simpa [Nat.add_assoc, Nat.add_comm 1 d] using hend_v
        · rintro x (rfl | hx) hxB
          · exact (hB hxB).elim
          · exact hstop_v x hx hxB
      · rw [traceWalkStopB_succ_of_not_lt hsys d u hB h]
        simp only [SimpleGraph.Walk.support_nil, List.nodup_singleton, List.mem_singleton, true_and]
        refine ⟨?_, Or.inl ?_, fun x hx _ => hx⟩
        · rintro x rfl
          exact ⟨0, Nat.zero_le _, by simpa using hku⟩
        · have hle := hsys.succ_le u
          have hsn : succ u = n := by omega
          have hu_used : used u ≠ 0 :=
            used_ne_zero_of_succAt hsys ((mem_pathStarts u₀).mp hu₀).1 k hku
          exact hsys.end_mem_B u hu_used hsn

theorem isKWalkList_map_support_of_walk_G_K {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    {u v : Fin n} (w : ((G.deleteVertices (Z_notK p)).toSimpleGraph).Walk u v) :
    IsKWalkList p.K_eList (w.support.map Fin.val) := by
  induction w with
  | nil => trivial
  | @cons x y z hadj w_tail ih =>
    have hke : isKEdgeBetween p.K_eList x.1 y.1 = true :=
      (G_K_adj_iff_isKEdgeBetween p hWS x y).mp hadj
    cases w_tail with
    | nil =>
      exact ⟨hke, trivial⟩
    | cons _ _ =>
      exact ⟨hke, ih⟩

theorem mem_K_vList_of_walk_G_K {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    {u v : Fin n} (huK : u.1 ∈ p.K_vList)
    (w : ((G.deleteVertices (Z_notK p)).toSimpleGraph).Walk u v) :
    ∀ x ∈ w.support.map Fin.val, x ∈ p.K_vList := by
  induction w with
  | nil =>
    intro x hx
    simp only [SimpleGraph.Walk.support_nil, List.map_cons, List.map_nil, List.mem_singleton] at hx
    rwa [hx]
  | @cons x y z hadj w_tail ih =>
    have hke : isKEdgeBetween p.K_eList x.1 y.1 = true :=
      (G_K_adj_iff_isKEdgeBetween p hWS x y).mp hadj
    rcases (isKEdgeBetween_eq_true_iff p.K_eList x.1 y.1).mp hke with
      ⟨_, e, heK, ⟨_, he2⟩ | ⟨he1, _⟩⟩
    · have hyK : y.1 ∈ p.K_vList := he2 ▸ (p.hK_e_valid e heK).2.2
      intro w_x hwx
      simp only [SimpleGraph.Walk.support_cons, List.map_cons, List.mem_cons] at hwx
      rcases hwx with rfl | hwx
      · exact huK
      · exact ih hyK w_x hwx
    · have hyK : y.1 ∈ p.K_vList := he1 ▸ (p.hK_e_valid e heK).2.1
      intro w_x hwx
      simp only [SimpleGraph.Walk.support_cons, List.map_cons, List.mem_cons] at hwx
      rcases hwx with rfl | hwx
      · exact huK
      · exact ih hyK w_x hwx

theorem head_and_getLastD_map_support {n : ℕ} {G_s : SimpleGraph (Fin n)}
    {u v : Fin n} (w : G_s.Walk u v) :
    (w.support.map Fin.val).head (by simp) = u.1 ∧
    (w.support.map Fin.val).headD 0 = u.1 ∧
    (w.support.map Fin.val).getLastD 0 = v.1 := by
  induction w with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | @cons x y z hadj w_tail ih =>
    refine ⟨rfl, rfl, ?_⟩
    cases w_tail with
    | nil => exact rfl
    | cons _ _ => exact ih.2.2

theorem isValidKPathBetween_map_support_of_walk_G_K {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    {u v : Fin n} (huK : u.1 ∈ p.K_vList)
    (w : ((G.deleteVertices (Z_notK p)).toSimpleGraph).Walk u v)
    (hnd : w.support.Nodup) :
    isValidKPathBetween p.K_vList p.K_eList (w.support.map Fin.val) u.1 v.1 = true := by
  unfold isValidKPathBetween
  have hne : w.support.map Fin.val ≠ [] := by simp
  rw [dite_eq_left hne]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hnd.map Fin.val_injective, mem_K_vList_of_walk_G_K p hWS huK w⟩,
    isKWalkList_map_support_of_walk_G_K p hWS w⟩,
    (head_and_getLastD_map_support w).1, ?_⟩
  rw [List.getLast_map hne, SimpleGraph.Walk.getLast_support]

theorem traceWalkStopB_valid_of_start {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (G.deleteVertices (Z_notK p)).toSimpleGraph A B used pred succ)
    {u₀ : Fin n} (hu₀ : u₀ ∈ pathStarts used pred) (hu₀K : u₀.1 ∈ p.K_vList) :
    let res := traceWalkStopB hsys n u₀
    let L := res.2.support.map Fin.val
    isValidKPathBetween p.K_vList p.K_eList L u₀.1 res.1.1 = true ∧
    res.1 ∈ B ∧
    L.headD 0 = u₀.1 ∧
    L.getLastD 0 = res.1.1 ∧
    (∀ x ∈ res.2.support, ∃ j ≤ n, succAt succ j u₀ = some x) ∧
    (∀ x ∈ res.2.support, x ∈ B → x = res.1) := by
  intro res L
  have hprops := traceWalkStopB_props hsys hu₀ n 0 u₀ rfl
  simp only [Nat.zero_add] at hprops
  rcases hprops with ⟨hnd, hmem, hend, hstop⟩
  have hresB : res.1 ∈ B := by
    rcases hend with hB | hsome
    · exact hB
    · rw [succAt_self_eq_none hsys hu₀] at hsome
      nomatch hsome
  have hhg := head_and_getLastD_map_support res.2
  exact ⟨isValidKPathBetween_map_support_of_walk_G_K p hWS hu₀K res.2 hnd,
    hresB, hhg.2.1, hhg.2.2, hmem, hstop⟩

theorem traceWalkStopB_disjoint {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    {u₀ v₀ : Fin n} (hu₀ : u₀ ∈ pathStarts used pred) (hv₀ : v₀ ∈ pathStarts used pred)
    (hne : u₀ ≠ v₀) :
    ∀ v ∈ (traceWalkStopB hsys n u₀).2.support.map Fin.val,
      v ∉ (traceWalkStopB hsys n v₀).2.support.map Fin.val := by
  intro v hvu hvv
  rcases List.mem_map.mp hvu with ⟨xu, hxu, rfl⟩
  rcases List.mem_map.mp hvv with ⟨xv, hxv, hval⟩
  have hxeq : xv = xu := Fin.ext hval
  rw [hxeq] at hxv
  rcases (traceWalkStopB_props hsys hu₀ n 0 u₀ rfl).2.1 xu hxu with ⟨i, _, hi⟩
  rcases (traceWalkStopB_props hsys hv₀ n 0 v₀ rfl).2.1 xu hxv with ⟨j, _, hj⟩
  rw [Nat.zero_add] at hi hj
  exact hne (succAt_inj_of_pathStarts hsys hu₀ hv₀ hi hj).1

theorem isClockwiseCorners_trichotomy {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') {t₁ t₂ t₃ : ℕ}
    (ht₁ : t₁ ∈ p.corners) (ht₂ : t₂ ∈ p.corners) (ht₃ : t₃ ∈ p.corners)
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) :
    isClockwiseCorners p.corners t₁ t₂ t₃ = true ∨
      isClockwiseCorners p.corners t₁ t₃ t₂ = true := by
  rw [p.hcorners_eq] at ht₁ ht₂ ht₃
  rcases List.mem_ofFn.mp ht₁ with ⟨i₁, rfl⟩
  rcases List.mem_ofFn.mp ht₂ with ⟨i₂, rfl⟩
  rcases List.mem_ofFn.mp ht₃ with ⟨i₃, rfl⟩
  have hi12 : i₁ ≠ i₂ := fun h => h12 (congrArg (fun i => (p.wallSec.W.branchVert (elemWallCornerIdx p.wallSec.h2 i)).1) h)
  have hi13 : i₁ ≠ i₃ := fun h => h13 (congrArg (fun i => (p.wallSec.W.branchVert (elemWallCornerIdx p.wallSec.h2 i)).1) h)
  have hi23 : i₂ ≠ i₃ := fun h => h23 (congrArg (fun i => (p.wallSec.W.branchVert (elemWallCornerIdx p.wallSec.h2 i)).1) h)
  have hget : ∀ i : Fin 4,
      p.corners.getD i.1 0 =
        (p.wallSec.W.branchVert (elemWallCornerIdx p.wallSec.h2 i)).1 := by
    intro i
    rw [p.hcorners_eq, List.getD_eq_getElem _ _ (by simp [i.2]), List.getElem_ofFn]
  rcases isFin4Clockwise3_trichotomy hi12 hi13 hi23 with hcw | hcw
  · left
    unfold isClockwiseCorners
    simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨i₁, i₂, i₃, ⟨hget i₁, hget i₂, hget i₃⟩, hcw⟩
  · right
    unfold isClockwiseCorners
    simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨i₁, i₃, i₂, ⟨hget i₁, hget i₃, hget i₂⟩, hcw⟩

/-- For nodup lists `l₁ ⊆ l₂` and a boolean predicate `pred`, `l₂` contains an element outside `l₁`
satisfying `pred` if and only if `l₁.countP pred < l₂.countP pred`. -/
theorem any_not_mem_eq_decide_countP_lt {α : Type*} [DecidableEq α]
    {l₁ l₂ : List α} (hl₁ : l₁.Nodup) (hl₂ : l₂.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂)
    (pred : α → Bool) :
    l₂.any (fun e => decide (e ∉ l₁ ∧ pred e = true)) =
      decide (l₁.countP pred < l₂.countP pred) := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  have hf₁ : (l₁.filter pred).Nodup := hl₁.filter pred
  have hf₂ : (l₂.filter pred).Nodup := hl₂.filter pred
  have hsub_f : ∀ x ∈ l₁.filter pred, x ∈ l₂.filter pred := by
    intro x hx
    rw [List.mem_filter] at hx ⊢
    exact ⟨hsub x hx.1, hx.2⟩
  have hle : (l₁.filter pred).length ≤ (l₂.filter pred).length :=
    (List.subperm_of_subset hf₁ hsub_f).length_le
  by_cases hex : ∃ e ∈ l₂, e ∉ l₁ ∧ pred e = true
  · rcases hex with ⟨e, he₂, he₁, hpe⟩
    have hlhs : l₂.any (fun e => decide (e ∉ l₁ ∧ pred e = true)) = true := by
      rw [List.any_eq_true]
      exact ⟨e, he₂, by simp [he₁, hpe]⟩
    have he_f₂ : e ∈ l₂.filter pred := List.mem_filter.mpr ⟨he₂, hpe⟩
    have he_f₁ : e ∉ l₁.filter pred := fun h => he₁ (List.mem_filter.mp h).1
    have hnd_cons : (e :: l₁.filter pred).Nodup := List.nodup_cons.mpr ⟨he_f₁, hf₁⟩
    have hsub_cons : ∀ x ∈ e :: l₁.filter pred, x ∈ l₂.filter pred := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact he_f₂
      · exact hsub_f x hx
    have hlt : (l₁.filter pred).length < (l₂.filter pred).length :=
      (List.subperm_of_subset hnd_cons hsub_cons).length_le
    rw [hlhs, decide_eq_true hlt]
  · have hlhs : l₂.any (fun e => decide (e ∉ l₁ ∧ pred e = true)) = false := by
      rw [List.any_eq_false]
      intro e he₂
      simp only [decide_eq_true_eq, not_and]
      intro he₁ hpe
      exact hex ⟨e, he₂, he₁, hpe⟩
    have hsub_rev : ∀ x ∈ l₂.filter pred, x ∈ l₁.filter pred := by
      intro x hx
      rw [List.mem_filter] at hx ⊢
      refine ⟨?_, hx.2⟩
      by_contra hx₁
      exact hex ⟨x, hx.1, hx₁, hx.2⟩
    have hge : (l₂.filter pred).length ≤ (l₁.filter pred).length :=
      (List.subperm_of_subset hf₂ hsub_rev).length_le
    have hnot_lt : ¬ (l₁.filter pred).length < (l₂.filter pred).length := by omega
    rw [hlhs, decide_eq_false hnot_lt]

/-- `isMemberBoundaryVert` expressed via `countP` of incident edges in `r.eList` vs `p.K_eList`. -/
theorem isMemberBoundaryVert_eq_decide_countP_lt {n : ℕ} {G : MultiDigraph n}
    {X' : Finset (Fin n)} (p : ParsedCase3Block (G.deleteVertices X') X')
    {r : Case3MemberRecord} (hr : r ∈ p.members) (v : ℕ) :
    isMemberBoundaryVert p.corners p.K_eList r v =
      (decide (v ∈ r.vList) &&
        (decide (v ∈ p.corners) ||
          decide (r.eList.countP (fun e => decide (e.1 = v ∨ e.2.1 = v)) <
            p.K_eList.countP (fun e => decide (e.1 = v ∨ e.2.1 = v))))) := by
  have hr_val := p.member_valid_iff hr
  have he_nd : r.eList.Nodup := hr_val.2.2.2.2.1
  have he_sub : ∀ e ∈ r.eList, e ∈ p.K_eList := fun e he => (hr_val.2.2.2.2.2.1 e he).1
  unfold isMemberBoundaryVert
  congr 2
  have hrew :
      (fun e : ℕ × ℕ × ℕ => decide (e ∉ r.eList ∧ (e.1 = v ∨ e.2.1 = v))) =
        (fun e : ℕ × ℕ × ℕ => decide (e ∉ r.eList ∧ decide (e.1 = v ∨ e.2.1 = v) = true)) := by
    funext e
    simp only [decide_eq_true_eq]
  rw [hrew, any_not_mem_eq_decide_countP_lt he_nd p.hK_e_nodup he_sub]



