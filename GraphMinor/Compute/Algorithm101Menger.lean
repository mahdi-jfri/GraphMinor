module

public import GraphMinor.Compute.Algorithm101MengerBase

/-!
# Step 1 Attachment Paths and Step 4 Representative Wall Vertex for Algorithm (10.1)

This file implements and verifies Step 1 (`step1Len3Prog`, `buildStep1AttachmentProg`) and
Step 4 (`findPathStartProg`, `buildStep4VOfProg`) of **Graph Minors XIII, Algorithm (10.1)**
(pages 106–107).
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-- Step 1 branch for `bList.length = 3`:
1. Builds `bitSetList A_bd` in `a_A_bd`.
2. Runs Menger ($k=3$) into `a_ps` using `runMengerPathSystemProg`.
3. Reads `s₀, s₁, s₂` into `r_base .. r_base + 2` and traces `Q₀, Q₁, Q₂` into `a_Q0, a_Q1, a_Q2`
   with endpoints `t₀, t₁, t₂` in `r_base + 3 .. r_base + 5` and lengths in `r_base + 6 .. r_base + 8`.
4. Tests `checkClockwiseCornersProg` into `r_base + 9` and writes `(sSeq, P₁, P₂, P₃)`. -/
def step1Len3Prog (a_start a_end a_entries a_corners a_B_bar a_bList
    a_sSeq a_P1 a_P2 a_P3 a_A_bd a_buf a_Q0 a_Q1 a_Q2 a_ps : Arr)
    (r_n r_bLen r_sLen r_P1Len r_P2Len r_P3Len r_base : Reg) : Cmd :=
  .seq (buildListIndProg a_bList a_A_bd r_bLen r_n r_base)
    (.seq (.assign r_base (.const 3))
      (.seq (runMengerPathSystemProg a_start a_end a_entries a_A_bd a_B_bar a_ps
          r_n r_base (r_base + 1))
        (.seq (.assign r_base (.read a_bList (.const 0)))
          (.seq (.assign (r_base + 1) (.read a_bList (.const 1)))
            (.seq (.assign (r_base + 2) (.read a_bList (.const 2)))
              (.seq (traceWalkStopBProg (a_ps + 2) a_B_bar a_buf a_Q0
                  r_base r_n (r_base + 3) (r_base + 6) (r_base + 10))
                (.seq (traceWalkStopBProg (a_ps + 2) a_B_bar a_buf a_Q1
                    (r_base + 1) r_n (r_base + 4) (r_base + 7) (r_base + 10))
                  (.seq (traceWalkStopBProg (a_ps + 2) a_B_bar a_buf a_Q2
                      (r_base + 2) r_n (r_base + 5) (r_base + 8) (r_base + 10))
                    (.seq (checkClockwiseCornersProg a_corners
                        (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 9) (r_base + 10))
                      (.seq (copyArrWithLenProg a_Q0 a_P1 (r_base + 6) r_P1Len (r_base + 10))
                        (.ite (.op .eq (.reg (r_base + 9)) (.const 1))
                          (.seq (writeTripleSSeqProg a_sSeq r_sLen r_base (r_base + 1) (r_base + 2))
                            (.seq (copyArrWithLenProg a_Q1 a_P2 (r_base + 7) r_P2Len (r_base + 10))
                              (copyArrWithLenProg a_Q2 a_P3 (r_base + 8) r_P3Len (r_base + 10))))
                          (.seq (writeTripleSSeqProg a_sSeq r_sLen r_base (r_base + 2) (r_base + 1))
                            (.seq (copyArrWithLenProg a_Q2 a_P2 (r_base + 8) r_P2Len (r_base + 10))
                              (copyArrWithLenProg a_Q1 a_P3 (r_base + 7) r_P3Len (r_base + 10)))))))))))))))

/-- Full Step 1 program for an interior member `r ∈ p.members`:
If `bList.length < 3`, sets `sSeq := bList` and `P₁ = P₂ = P₃ = []`; otherwise runs `step1Len3Prog`. -/
def buildStep1AttachmentProg (a_start a_end a_entries a_corners a_B_bar a_bList
    a_sSeq a_P1 a_P2 a_P3 a_A_bd a_buf a_Q0 a_Q1 a_Q2 a_ps : Arr)
    (r_n r_bLen r_sLen r_P1Len r_P2Len r_P3Len r_base : Reg) : Cmd :=
  .ite (.op .lt (.reg r_bLen) (.const 3))
    (.seq (copyArrWithLenProg a_bList a_sSeq r_bLen r_sLen r_base)
      (.seq (allocEmptyArrProg a_P1 r_P1Len)
        (.seq (allocEmptyArrProg a_P2 r_P2Len)
          (allocEmptyArrProg a_P3 r_P3Len))))
    (step1Len3Prog a_start a_end a_entries a_corners a_B_bar a_bList
      a_sSeq a_P1 a_P2 a_P3 a_A_bd a_buf a_Q0 a_Q1 a_Q2 a_ps
      r_n r_bLen r_sLen r_P1Len r_P2Len r_P3Len r_base)

/-- Package of all Step 1 validity conditions on `(sSeq, P₁, P₂, P₃)` in `isValidVisionMemberRecord`. -/
def Step1AttachmentValid {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (r : Case3MemberRecord)
    (sSeq P₁ P₂ P₃ : List ℕ) : Prop :=
  let bList := memberBoundaryList p.corners p.K_eList r
  sSeq.Nodup ∧
  sSeq.toFinset = bList.toFinset ∧
  sSeq.length ≤ 3 ∧
  (∀ x ∈ sSeq, x < n) ∧
  P₁.length ≤ n + 1 ∧ (∀ x ∈ P₁, x < n) ∧
  P₂.length ≤ n + 1 ∧ (∀ x ∈ P₂, x < n) ∧
  P₃.length ≤ n + 1 ∧ (∀ x ∈ P₃, x < n) ∧
  (if sSeq.length = 3 then
    let s₁ := sSeq.getD 0 0
    let s₂ := sSeq.getD 1 0
    let s₃ := sSeq.getD 2 0
    let t₁ := P₁.getLastD 0
    let t₂ := P₂.getLastD 0
    let t₃ := P₃.getLastD 0
    isValidKPathBetween p.K_vList p.K_eList P₁ s₁ t₁ = true ∧
    isValidKPathBetween p.K_vList p.K_eList P₂ s₂ t₂ = true ∧
    isValidKPathBetween p.K_vList p.K_eList P₃ s₃ t₃ = true ∧
    ((∀ v ∈ P₁, v ∉ P₂) ∧ (∀ v ∈ P₁, v ∉ P₃) ∧ (∀ v ∈ P₂, v ∉ P₃)) ∧
    (∀ v ∈ P₁, (v ∈ bList ↔ v = s₁) ∧ (v ∈ p.corners ↔ v = t₁)) ∧
    (∀ v ∈ P₂, (v ∈ bList ↔ v = s₂) ∧ (v ∈ p.corners ↔ v = t₂)) ∧
    (∀ v ∈ P₃, (v ∈ bList ↔ v = s₃) ∧ (v ∈ p.corners ↔ v = t₃)) ∧
    isClockwiseCorners p.corners t₁ t₂ t₃ = true
  else True)

theorem ParsedCase3Block.member_vList_lt {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') {r : Case3MemberRecord}
    (hr : r ∈ p.members) {x : ℕ} (hx : x ∈ r.vList) : x < n :=
  ((mem_vertexSet_delGraph_iff G X' x).mp
    (isDelGraphVert_eq_true_iff.mp (p.hK_v_valid x ((p.member_valid_iff hr).2.2.1 x hx)))).1

theorem ParsedCase3Block.memberBoundaryList_lt {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') {r : Case3MemberRecord}
    (hr : r ∈ p.members) {x : ℕ} (hx : x ∈ memberBoundaryList p.corners p.K_eList r) : x < n :=
  p.member_vList_lt hr (List.mem_of_mem_filter hx)

private theorem toFinset_swap_second_third (a b c : ℕ) :
    ([a, c, b] : List ℕ).toFinset = ([a, b, c] : List ℕ).toFinset := by
  ext x
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem list_eq_three_of_length_eq_three {α : Type*} (l : List α) (h : l.length = 3)
    (h0 : 0 < l.length) (h1 : 1 < l.length) (h2 : 2 < l.length) :
    l = [l[0]'h0, l[1]'h1, l[2]'h2] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | _⟩⟩⟩ <;> simp_all

theorem step1_three_paths_valid {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    (hlen3 : (memberBoundaryList p.corners p.K_eList r).length = 3)
    {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (G.deleteVertices (Z_notK p)).toSimpleGraph
      (Finset.univ.filter (fun u : Fin n => u.1 ∈ memberBoundaryList p.corners p.K_eList r))
      (Finset.univ.filter (fun u : Fin n => u.1 ∈ p.corners))
      used pred succ)
    (hcard : (pathStarts used pred).card = 3) :
    let u₀ : Fin n := ⟨(memberBoundaryList p.corners p.K_eList r)[0]'(hlen3.symm ▸ Nat.zero_lt_succ 2),
      p.memberBoundaryList_lt hr (List.getElem_mem (hlen3.symm ▸ Nat.zero_lt_succ 2))⟩
    let u₁ : Fin n := ⟨(memberBoundaryList p.corners p.K_eList r)[1]'(hlen3.symm ▸ Nat.succ_lt_succ (Nat.zero_lt_succ 1)),
      p.memberBoundaryList_lt hr (List.getElem_mem (hlen3.symm ▸ Nat.succ_lt_succ (Nat.zero_lt_succ 1)))⟩
    let u₂ : Fin n := ⟨(memberBoundaryList p.corners p.K_eList r)[2]'(hlen3.symm ▸ Nat.lt_succ_self 2),
      p.memberBoundaryList_lt hr (List.getElem_mem (hlen3.symm ▸ Nat.lt_succ_self 2))⟩
    let Q₀ := (traceWalkStopB hsys n u₀).2.support.map Fin.val
    let Q₁ := (traceWalkStopB hsys n u₁).2.support.map Fin.val
    let Q₂ := (traceWalkStopB hsys n u₂).2.support.map Fin.val
    let t₀ := (traceWalkStopB hsys n u₀).1.1
    let t₁ := (traceWalkStopB hsys n u₁).1.1
    let t₂ := (traceWalkStopB hsys n u₂).1.1
    u₀ ∈ pathStarts used pred ∧ u₁ ∈ pathStarts used pred ∧ u₂ ∈ pathStarts used pred ∧
    t₀ ∈ p.corners ∧ t₁ ∈ p.corners ∧ t₂ ∈ p.corners ∧
    (if isClockwiseCorners p.corners t₀ t₁ t₂ then
      Step1AttachmentValid p r [u₀.1, u₁.1, u₂.1] Q₀ Q₁ Q₂
    else
      Step1AttachmentValid p r [u₀.1, u₂.1, u₁.1] Q₀ Q₂ Q₁) := by
  intro u₀ u₁ u₂ Q₀ Q₁ Q₂ t₀ t₁ t₂
  let bList := memberBoundaryList p.corners p.K_eList r
  have hb_lt : ∀ x ∈ bList, x < n := fun _ hx => p.memberBoundaryList_lt hr hx
  have hlen3' : bList.length = 3 := hlen3
  have hb_nd : bList.Nodup := nodup_memberBoundaryList p hr
  have hb_eq : bList = [u₀.1, u₁.1, u₂.1] :=
    list_eq_three_of_length_eq_three bList hlen3'
      (hlen3.symm ▸ Nat.zero_lt_succ 2)
      (hlen3.symm ▸ Nat.succ_lt_succ (Nat.zero_lt_succ 1))
      (hlen3.symm ▸ Nat.lt_succ_self 2)
  have hstarts_eq :
      pathStarts used pred = Finset.univ.filter (fun u : Fin n => u.1 ∈ bList) :=
    pathStarts_eq_filter_of_card_eq hb_nd hsys (by omega)
  have hu₀_st : u₀ ∈ pathStarts used pred := by
    rw [hstarts_eq, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hb_eq]; simp⟩
  have hu₁_st : u₁ ∈ pathStarts used pred := by
    rw [hstarts_eq, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hb_eq]; simp⟩
  have hu₂_st : u₂ ∈ pathStarts used pred := by
    rw [hstarts_eq, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hb_eq]; simp⟩
  have hnd3 : ([u₀.1, u₁.1, u₂.1] : List ℕ).Nodup := by rwa [← hb_eq]
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd3
  rcases hnd3 with ⟨⟨hne01_v, hne02_v, _⟩, ⟨hne12_v, _⟩, _⟩
  have hne01 : u₀ ≠ u₁ := fun h => hne01_v (congrArg Fin.val h)
  have hne02 : u₀ ≠ u₂ := fun h => hne02_v (congrArg Fin.val h)
  have hne12 : u₁ ≠ u₂ := fun h => hne12_v (congrArg Fin.val h)
  have hu_K : ∀ u : Fin n, u.1 ∈ bList → u.1 ∈ p.K_vList :=
    fun u hu => (p.member_valid_iff hr).2.2.1 u.1 (List.mem_of_mem_filter hu)
  have hv₀ := traceWalkStopB_valid_of_start p hWS hsys hu₀_st (hu_K u₀ (by simp [hb_eq]))
  have hv₁ := traceWalkStopB_valid_of_start p hWS hsys hu₁_st (hu_K u₁ (by simp [hb_eq]))
  have hv₂ := traceWalkStopB_valid_of_start p hWS hsys hu₂_st (hu_K u₂ (by simp [hb_eq]))
  have ht₀_c : t₀ ∈ p.corners := by simpa [t₀] using hv₀.2.1
  have ht₁_c : t₁ ∈ p.corners := by simpa [t₁] using hv₁.2.1
  have ht₂_c : t₂ ∈ p.corners := by simpa [t₂] using hv₂.2.1
  have hdisj01 := traceWalkStopB_disjoint hsys hu₀_st hu₁_st hne01
  have hdisj02 := traceWalkStopB_disjoint hsys hu₀_st hu₂_st hne02
  have hdisj12 := traceWalkStopB_disjoint hsys hu₁_st hu₂_st hne12
  have hdisj21 := traceWalkStopB_disjoint hsys hu₂_st hu₁_st hne12.symm
  have hu_in_Q : ∀ (u : Fin n), u.1 ∈ (traceWalkStopB hsys n u).2.support.map Fin.val := by
    intro u
    have hhd := (head_and_getLastD_map_support (traceWalkStopB hsys n u).2).1
    rw [← hhd]
    exact List.head_mem _
  have ht_in_Q : ∀ (u : Fin n),
      (traceWalkStopB hsys n u).1.1 ∈ (traceWalkStopB hsys n u).2.support.map Fin.val := by
    intro u
    exact List.mem_map_of_mem (SimpleGraph.Walk.end_mem_support _)
  have ht_ne01 : t₀ ≠ t₁ := fun h => hdisj01 t₀ (ht_in_Q u₀) (h ▸ ht_in_Q u₁)
  have ht_ne02 : t₀ ≠ t₂ := fun h => hdisj02 t₀ (ht_in_Q u₀) (h ▸ ht_in_Q u₂)
  have ht_ne12 : t₁ ≠ t₂ := fun h => hdisj12 t₁ (ht_in_Q u₁) (h ▸ ht_in_Q u₂)
  have hQ_hit : ∀ (u : Fin n) (hu_b : u.1 ∈ bList)
      (hnot : ∀ x ∈ bList, x ≠ u.1 → x ∉ (traceWalkStopB hsys n u).2.support.map Fin.val)
      (hstop : ∀ x ∈ (traceWalkStopB hsys n u).2.support,
        x ∈ Finset.univ.filter (fun w : Fin n => w.1 ∈ p.corners) →
        x = (traceWalkStopB hsys n u).1),
      ∀ v ∈ (traceWalkStopB hsys n u).2.support.map Fin.val,
        (v ∈ bList ↔ v = u.1) ∧ (v ∈ p.corners ↔ v = (traceWalkStopB hsys n u).1.1) := by
    intro u hu_b hnot hstop v hv
    have hend_c : (traceWalkStopB hsys n u).1.1 ∈ p.corners := by
      have hpr := traceWalkStopB_valid_of_start p hWS hsys
        (by rw [hstarts_eq]; simp [hu_b]) (hu_K u hu_b)
      simpa using hpr.2.1
    refine ⟨⟨fun hvb => ?_, fun h => h ▸ hu_b⟩, ⟨fun hvc => ?_, fun h => h ▸ hend_c⟩⟩
    · by_contra hne
      exact hnot v hvb hne hv
    · rcases List.mem_map.mp hv with ⟨x, hx, rfl⟩
      exact congrArg Fin.val (hstop x hx (by simp [hvc]))
  have hhit₀ : ∀ v ∈ Q₀, (v ∈ bList ↔ v = u₀.1) ∧ (v ∈ p.corners ↔ v = t₀) :=
    hQ_hit u₀ (by simp [hb_eq]) (by
      intro x hx hne
      rw [hb_eq] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (hne rfl).elim
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact fun hm => hdisj01 u₁.1 hm (hu_in_Q u₁)
        · rcases List.mem_singleton.mp hx with rfl
          exact fun hm => hdisj02 u₂.1 hm (hu_in_Q u₂)) hv₀.2.2.2.2.2
  have hhit₁ : ∀ v ∈ Q₁, (v ∈ bList ↔ v = u₁.1) ∧ (v ∈ p.corners ↔ v = t₁) :=
    hQ_hit u₁ (by simp [hb_eq]) (by
      intro x hx hne
      rw [hb_eq] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact fun hm => hdisj01 u₀.1 (hu_in_Q u₀) hm
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact (hne rfl).elim
        · rcases List.mem_singleton.mp hx with rfl
          exact fun hm => hdisj12 u₂.1 hm (hu_in_Q u₂)) hv₁.2.2.2.2.2
  have hhit₂ : ∀ v ∈ Q₂, (v ∈ bList ↔ v = u₂.1) ∧ (v ∈ p.corners ↔ v = t₂) :=
    hQ_hit u₂ (by simp [hb_eq]) (by
      intro x hx hne
      rw [hb_eq] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact fun hm => hdisj02 u₀.1 (hu_in_Q u₀) hm
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact fun hm => hdisj12 u₁.1 (hu_in_Q u₁) hm
        · rcases List.mem_singleton.mp hx with rfl
          exact (hne rfl).elim) hv₂.2.2.2.2.2
  have hQ_len_lt : ∀ u : Fin n,
      ((traceWalkStopB hsys n u).2.support.map Fin.val).length ≤ n + 1 ∧
      ∀ x ∈ (traceWalkStopB hsys n u).2.support.map Fin.val, x < n := by
    intro u
    have hwalk := traceWalkList_eq_traceWalkStopB hsys n u
    unfold traceWalkList at hwalk
    have h1 : [u.1] ++ (traceWalkTail (List.ofFn succ)
        (bitSetList (Finset.univ.filter (fun w : Fin n => w.1 ∈ p.corners))) n n u.1).1 =
        (traceWalkStopB hsys n u).2.support.map Fin.val := by
      simpa using congrArg Prod.fst hwalk
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← h1, List.length_append]
      have := length_traceWalkTail_le (List.ofFn succ)
        (bitSetList (Finset.univ.filter (fun w : Fin n => w.1 ∈ p.corners))) n n u.1
      simp; omega
    · rcases List.mem_map.mp hx with ⟨w_x, _, rfl⟩
      exact w_x.2
  have hlen₀ : Q₀.length ≤ n + 1 := (hQ_len_lt u₀).1
  have hlt₀ : ∀ x ∈ Q₀, x < n := (hQ_len_lt u₀).2
  have hlen₁ : Q₁.length ≤ n + 1 := (hQ_len_lt u₁).1
  have hlt₁ : ∀ x ∈ Q₁, x < n := (hQ_len_lt u₁).2
  have hlen₂ : Q₂.length ≤ n + 1 := (hQ_len_lt u₂).1
  have hlt₂ : ∀ x ∈ Q₂, x < n := (hQ_len_lt u₂).2
  have hpath₀ : isValidKPathBetween p.K_vList p.K_eList Q₀ u₀.1 t₀ = true := hv₀.1
  have hpath₁ : isValidKPathBetween p.K_vList p.K_eList Q₁ u₁.1 t₁ = true := hv₁.1
  have hpath₂ : isValidKPathBetween p.K_vList p.K_eList Q₂ u₂.1 t₂ = true := hv₂.1
  have hlast₀ : Q₀.getLastD 0 = t₀ := hv₀.2.2.2.1
  have hlast₁ : Q₁.getLastD 0 = t₁ := hv₁.2.2.2.1
  have hlast₂ : Q₂.getLastD 0 = t₂ := hv₂.2.2.2.1
  have hdisj01' : ∀ v ∈ Q₀, v ∉ Q₁ := hdisj01
  have hdisj02' : ∀ v ∈ Q₀, v ∉ Q₂ := hdisj02
  have hdisj12' : ∀ v ∈ Q₁, v ∉ Q₂ := hdisj12
  have hdisj21' : ∀ v ∈ Q₂, v ∉ Q₁ := hdisj21
  refine ⟨hu₀_st, hu₁_st, hu₂_st, ht₀_c, ht₁_c, ht₂_c, ?_⟩
  by_cases hcw : isClockwiseCorners p.corners t₀ t₁ t₂ = true
  · simp only [hcw, ↓reduceIte]
    refine ⟨by rwa [← hb_eq], by rw [← hb_eq], by simp,
      fun x hx => hb_lt x (hb_eq ▸ hx),
      hlen₀, hlt₀, hlen₁, hlt₁, hlen₂, hlt₂, ?_⟩
    simp only [List.length_cons, List.length_nil, ↓reduceIte, List.getD_cons_zero,
      List.getD_cons_succ, hlast₀, hlast₁, hlast₂]
    exact ⟨hpath₀, hpath₁, hpath₂, ⟨hdisj01', hdisj02', hdisj12'⟩, hhit₀, hhit₁, hhit₂, hcw⟩
  · simp only [hcw, Bool.false_eq_true, ↓reduceIte]
    have hcw' : isClockwiseCorners p.corners t₀ t₂ t₁ = true := by
      rcases isClockwiseCorners_trichotomy p ht₀_c ht₁_c ht₂_c ht_ne01 ht_ne02 ht_ne12 with h1 | h2
      · exact (hcw h1).elim
      · exact h2
    have hnd_swap : ([u₀.1, u₂.1, u₁.1] : List ℕ).Nodup := by
      simp [hne02_v, hne01_v, Ne.symm hne12_v]
    have hfin_swap : ([u₀.1, u₂.1, u₁.1] : List ℕ).toFinset = bList.toFinset := by
      rw [hb_eq]
      exact toFinset_swap_second_third u₀.1 u₁.1 u₂.1
    refine ⟨hnd_swap, hfin_swap, by simp,
      fun x hx => hb_lt x (List.mem_toFinset.mp (hfin_swap ▸ List.mem_toFinset.mpr hx)),
      hlen₀, hlt₀, hlen₂, hlt₂, hlen₁, hlt₁, ?_⟩
    simp only [List.length_cons, List.length_nil, ↓reduceIte, List.getD_cons_zero,
      List.getD_cons_succ, hlast₀, hlast₂, hlast₁]
    exact ⟨hpath₀, hpath₂, hpath₁, ⟨hdisj02', hdisj01', hdisj21'⟩, hhit₀, hhit₂, hhit₁, hcw'⟩

theorem step1Len3Prog_exec {w n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety)
    (hDiv : GM13.IsSocietyDivision p.toSociety p.toDivision)
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    (hlen3 : (memberBoundaryList p.corners p.K_eList r).length = 3)
    (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_corners a_B_bar a_bList
      a_sSeq a_P1 a_P2 a_P3 a_A_bd a_buf a_Q0 a_Q1 a_Q2 a_ps : ℕ)
    (r_n r_bLen r_sLen r_P1Len r_P2Len r_P3Len r_base : ℕ)
    (ha_st : a_start < a_sSeq) (ha_en : a_end < a_sSeq) (ha_ent : a_entries < a_sSeq)
    (ha_cor : a_corners < a_sSeq) (ha_Bbar : a_B_bar < a_sSeq) (ha_bL : a_bList < a_sSeq)
    (ha_order : a_sSeq < a_P1 ∧ a_P1 < a_P2 ∧ a_P2 < a_P3 ∧ a_P3 < a_A_bd ∧
      a_A_bd < a_buf ∧ a_buf < a_Q0 ∧ a_Q0 < a_Q1 ∧ a_Q1 < a_Q2 ∧ a_Q2 < a_ps)
    (hr_n : r_n < r_sLen) (hr_bL : r_bLen < r_sLen)
    (hr_order : r_sLen < r_P1Len ∧ r_P1Len < r_P2Len ∧ r_P2Len < r_P3Len ∧ r_P3Len < r_base)
    (hw6 : 6 < 2 ^ w) (h2n_w : 2 * n + 2 < 2 ^ w)
    {s : State}
    (hadj : IsAdjList (G.deleteVertices (Z_notK p)).toSimpleGraph a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hcor : s.arrs a_corners = p.corners)
    (hBbar : s.arrs a_B_bar = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ p.corners)))
    (hbL : s.arrs a_bList = memberBoundaryList p.corners p.K_eList r)
    (hrn : s.regs r_n = n)
    (hrbL : s.regs r_bLen = 3) :
    ∃ s' t sSeq P₁ P₂ P₃,
      Exec w (step1Len3Prog a_start a_end a_entries a_corners a_B_bar a_bList
        a_sSeq a_P1 a_P2 a_P3 a_A_bd a_buf a_Q0 a_Q1 a_Q2 a_ps
        r_n r_bLen r_sLen r_P1Len r_P2Len r_P3Len r_base) s s' t ∧
      t ≤ 1020 * n + 93 * totalAdjEntries lists + 650 ∧
      s'.arrs a_sSeq = sSeq ∧
      s'.arrs a_P1 = P₁ ∧
      s'.arrs a_P2 = P₂ ∧
      s'.arrs a_P3 = P₃ ∧
      s'.regs r_sLen = sSeq.length ∧
      s'.regs r_P1Len = P₁.length ∧
      s'.regs r_P2Len = P₂.length ∧
      s'.regs r_P3Len = P₃.length ∧
      Step1AttachmentValid p r sSeq P₁ P₂ P₃ ∧
      (∀ a < a_sSeq, s'.arrs a = s.arrs a) ∧
      (∀ r_reg < r_base,
        r_reg ≠ r_sLen → r_reg ≠ r_P1Len → r_reg ≠ r_P2Len → r_reg ≠ r_P3Len →
        s'.regs r_reg = s.regs r_reg) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let bList := memberBoundaryList p.corners p.K_eList r
  have hlen3' : bList.length = 3 := hlen3
  have hb_lt : ∀ x ∈ bList, x < n :=
    fun x hx => p.member_vList_lt hr (List.mem_of_mem_filter hx)
  -- 1. Build bitSetList A_bd in a_A_bd
  rcases buildListIndProg_exec bList hb_lt a_bList a_A_bd r_bLen r_n r_base
      (by omega) (by omega) (by omega) hw hn_w (by omega) hbL (by rw [hrbL, hlen3]) hrn with
    ⟨s₁, t₁, hex₁, ht₁, hA_bd₁, harr₁, hreg₁⟩
  -- 2. Set r_base := 3
  let s₂ := s₁.setReg r_base 3
  have hex₂ : Exec w (.assign r_base (.const 3)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw3])
  -- 3. Run Menger k = 3
  let A_bd := Finset.univ.filter (fun u : Fin n => u.1 ∈ bList)
  let B_bar := Finset.univ.filter (fun u : Fin n => u.1 ∈ p.corners)
  have hadj₂ :
      IsAdjList (G.deleteVertices (Z_notK p)).toSimpleGraph a_start a_end a_entries lists s₂ :=
    hadj.of_arrs_eq
      (by simp [s₂, harr₁ a_start (by omega)])
      (by simp [s₂, harr₁ a_end (by omega)])
      (by simp [s₂, harr₁ a_entries (by omega)])
  have hent₂_w : (s₂.arrs a_entries).length < 2 ^ w := by
    simp [s₂, harr₁ a_entries (by omega), hent_w]
  have hA₂_bit : IsBitSet A_bd a_A_bd s₂ :=
    IsBitSet.of_bitSetList A_bd a_A_bd s₂ (by simp [s₂, hA_bd₁, A_bd])
  have hB₂_bit : IsBitSet B_bar a_B_bar s₂ :=
    IsBitSet.of_bitSetList B_bar a_B_bar s₂ (by simp [s₂, harr₁ a_B_bar (by omega), hBbar, B_bar])
  have hrn₂ : s₂.regs r_n = n := by
    simp [s₂, show r_n ≠ r_base by omega, hreg₁ r_n (by omega), hrn]
  rcases runMengerPathSystemProg_exec (G.deleteVertices (Z_notK p)).toSimpleGraph
      lists A_bd B_bar a_start a_end a_entries a_A_bd a_B_bar a_ps
      r_n r_base (r_base + 1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw2 (by omega) hw3
      (not_isABSeparator_step1 p hWS hDiv hr hlen3)
      hadj₂ hent₂_w hA₂_bit hB₂_bit hrn₂ (by simp [s₂]) with
    ⟨s₃, t₃, used, pred, succ, hex₃, ht₃, hsys₃, hcard₃, harr₃, hreg₃⟩
  obtain ⟨_, _, hsucc₃⟩ := hsys₃.2.arrs_eq_ofFn
  obtain ⟨hu₀_st, hu₁_st, hu₂_st, ht₀_c, ht₁_c, ht₂_c, hvalid_ite⟩ :=
    step1_three_paths_valid p hWS hr hlen3 hsys₃.1 hcard₃
  let u₀ : Fin n := ⟨bList[0]'(by omega), hb_lt _ (List.getElem_mem (by omega))⟩
  let u₁ : Fin n := ⟨bList[1]'(by omega), hb_lt _ (List.getElem_mem (by omega))⟩
  let u₂ : Fin n := ⟨bList[2]'(by omega), hb_lt _ (List.getElem_mem (by omega))⟩
  have hbL₃ : s₃.arrs a_bList = bList := by
    rw [harr₃ a_bList (by omega)]; simp [s₂, harr₁ a_bList (by omega), hbL, bList]
  have hu0_w : u₀.1 < 2 ^ w := Nat.lt_trans u₀.2 hn_w
  have hu1_w : u₁.1 < 2 ^ w := Nat.lt_trans u₁.2 hn_w
  have hu2_w : u₂.1 < 2 ^ w := Nat.lt_trans u₂.2 hn_w
  -- 4. Read s₀, s₁, s₂ into r_base, r_base + 1, r_base + 2
  let s₄ := s₃.setReg r_base u₀.1
  have hex₄ : Exec w (.assign r_base (.read a_bList (.const 0))) s₃ s₄ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hbL₃, hlen3', u₀, hu0_w])
  let s₅ := s₄.setReg (r_base + 1) u₁.1
  have hex₅ : Exec w (.assign (r_base + 1) (.read a_bList (.const 1))) s₄ s₅ 3 :=
    .assign (by simp [s₄, Expr.eval, checkWord, hw, hbL₃, hlen3', u₁, hu1_w])
  let s₆ := s₅.setReg (r_base + 2) u₂.1
  have hex₆ : Exec w (.assign (r_base + 2) (.read a_bList (.const 2))) s₅ s₆ 3 :=
    .assign (by simp [s₅, s₄, Expr.eval, checkWord, hw2, hbL₃, hlen3', u₂, hu2_w])
  -- 5. Trace Q₀, Q₁, Q₂
  have hBbar₆ : s₆.arrs a_B_bar = bitSetList B_bar := by
    simp [s₆, s₅, s₄, harr₃ a_B_bar (by omega), s₂, harr₁ a_B_bar (by omega), hBbar, B_bar]
  have hrn₆ : s₆.regs r_n = n := by
    simp [s₆, s₅, s₄, show r_n ≠ r_base by omega, show r_n ≠ r_base + 1 by omega,
      show r_n ≠ r_base + 2 by omega, hreg₃ r_n (by omega), hrn₂]
  rcases traceWalkStopBProg_exec hsys₃.1 u₀
      (a_ps + 2) a_B_bar a_buf a_Q0 r_base r_n (r_base + 3) (r_base + 6) (r_base + 10)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw (by omega) (s := s₆) (by simp [s₆, s₅, s₄, hsucc₃]) hBbar₆
      (by simp [s₆, s₅, s₄]) hrn₆ with
    ⟨s₇, t₇, hex₇, ht₇, hQ0_7, ht0_7, hlen0_7, harr₇, hreg₇⟩
  rcases traceWalkStopBProg_exec hsys₃.1 u₁
      (a_ps + 2) a_B_bar a_buf a_Q1 (r_base + 1) r_n (r_base + 4) (r_base + 7) (r_base + 10)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw (by omega) (s := s₇)
      (by rw [harr₇ (a_ps + 2) (by omega) (by omega)]; simp [s₆, s₅, s₄, hsucc₃])
      (by rw [harr₇ a_B_bar (by omega) (by omega)]; exact hBbar₆)
      (by rw [hreg₇ (r_base + 1) (by omega) (by omega) (by omega)]; simp [s₆, s₅])
      (by rw [hreg₇ r_n (by omega) (by omega) (by omega)]; exact hrn₆) with
    ⟨s₈, t₈, hex₈, ht₈, hQ1_8, ht1_8, hlen1_8, harr₈, hreg₈⟩
  rcases traceWalkStopBProg_exec hsys₃.1 u₂
      (a_ps + 2) a_B_bar a_buf a_Q2 (r_base + 2) r_n (r_base + 5) (r_base + 8) (r_base + 10)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw (by omega) (s := s₈)
      (by rw [harr₈ (a_ps + 2) (by omega) (by omega), harr₇ (a_ps + 2) (by omega) (by omega)]
          simp [s₆, s₅, s₄, hsucc₃])
      (by rw [harr₈ a_B_bar (by omega) (by omega), harr₇ a_B_bar (by omega) (by omega)]
          exact hBbar₆)
      (by rw [hreg₈ (r_base + 2) (by omega) (by omega) (by omega),
            hreg₇ (r_base + 2) (by omega) (by omega) (by omega)]
          simp [s₆])
      (by rw [hreg₈ r_n (by omega) (by omega) (by omega),
            hreg₇ r_n (by omega) (by omega) (by omega)]
          exact hrn₆) with
    ⟨s₉, t₉, hex₉, ht₉, hQ2_9, ht2_9, hlen2_9, harr₉, hreg₉⟩
  -- 6. Check clockwise corners
  let Q₀ := (traceWalkStopB hsys₃.1 n u₀).2.support.map Fin.val
  let Q₁ := (traceWalkStopB hsys₃.1 n u₁).2.support.map Fin.val
  let Q₂ := (traceWalkStopB hsys₃.1 n u₂).2.support.map Fin.val
  let ep₀ := (traceWalkStopB hsys₃.1 n u₀).1.1
  let ep₁ := (traceWalkStopB hsys₃.1 n u₁).1.1
  let ep₂ := (traceWalkStopB hsys₃.1 n u₂).1.1
  change (if isClockwiseCorners p.corners ep₀ ep₁ ep₂ then
      Step1AttachmentValid p r [u₀.1, u₁.1, u₂.1] Q₀ Q₁ Q₂
    else
      Step1AttachmentValid p r [u₀.1, u₂.1, u₁.1] Q₀ Q₂ Q₁) at hvalid_ite
  have ht₁' : t₁ ≤ 2 * n + 54 := by omega
  have hcor₉ : s₉.arrs a_corners = p.corners := by
    rw [harr₉ a_corners (by omega) (by omega), harr₈ a_corners (by omega) (by omega),
      harr₇ a_corners (by omega) (by omega)]
    simp [s₆, s₅, s₄, harr₃ a_corners (by omega), s₂, harr₁ a_corners (by omega), hcor]
  rcases checkClockwiseCornersProg_exec p a_corners
      (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 9) (r_base + 10)
      (by omega) (by omega) (by omega) ht₀_c ht₁_c ht₂_c hw6 hn_w hcor₉
      (by rw [hreg₉ (r_base + 3) (by omega) (by omega) (by omega),
            hreg₈ (r_base + 3) (by omega) (by omega) (by omega), ht0_7])
      (by rw [hreg₉ (r_base + 4) (by omega) (by omega) (by omega), ht1_8])
      ht2_9 with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hcw₁₀, harr₁₀, hreg₁₀⟩
  -- 7. Copy Q₀ to a_P1
  have hQ_w : ∀ u : Fin n, ∀ x ∈ (traceWalkStopB hsys₃.1 n u).2.support.map Fin.val, x < 2 ^ w := by
    intro u x hx
    rcases List.mem_map.mp hx with ⟨v, _, rfl⟩
    exact Nat.lt_trans v.2 hn_w
  have hQ_len_le : ∀ u : Fin n,
      ((traceWalkStopB hsys₃.1 n u).2.support.map Fin.val).length ≤ n + 1 := by
    intro u
    have hwalk := traceWalkList_eq_traceWalkStopB hsys₃.1 n u
    unfold traceWalkList at hwalk
    have h1 : [u.1] ++ (traceWalkTail (List.ofFn succ) (bitSetList B_bar) n n u.1).1 =
        (traceWalkStopB hsys₃.1 n u).2.support.map Fin.val := by
      simpa using congrArg Prod.fst hwalk
    rw [← h1, List.length_append]
    have := length_traceWalkTail_le (List.ofFn succ) (bitSetList B_bar) n n u.1
    simp; omega
  have hQ0_10 : s₁₀.arrs a_Q0 = Q₀ := by
    rw [harr₁₀ a_Q0, harr₉ a_Q0 (by omega) (by omega), harr₈ a_Q0 (by omega) (by omega), hQ0_7]
  have hlen0_10 : s₁₀.regs (r_base + 6) = Q₀.length := by
    rw [hreg₁₀ (r_base + 6) (by omega) (by omega),
      hreg₉ (r_base + 6) (by omega) (by omega) (by omega),
      hreg₈ (r_base + 6) (by omega) (by omega) (by omega), hlen0_7]
  have hQ0_len_le : Q₀.length ≤ n + 1 := hQ_len_le u₀
  have hQ1_len_le : Q₁.length ≤ n + 1 := hQ_len_le u₁
  have hQ2_len_le : Q₂.length ≤ n + 1 := hQ_len_le u₂
  rcases copyArrWithLenProg_exec Q₀ (hQ_w u₀) a_Q0 a_P1 (r_base + 6) r_P1Len (r_base + 10)
      (by omega) (by omega) (by omega) hw (by omega) hQ0_10 hlen0_10 with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hP1_11, hrP1_11, harr₁₁, hreg₁₁⟩
  have ht₁₁' : t₁₁ ≤ 16 * n + 27 := by
    have : ((traceWalkStopB hsys₃.1 n u₀).2.support.map Fin.val).length ≤ n + 1 := hQ0_len_le
    omega
  -- Helper register & array facts on s₁₁
  have hr0_11 : s₁₁.regs r_base = u₀.1 := by
    rw [hreg₁₁ r_base (by omega) (by omega), hreg₁₀ r_base (by omega) (by omega),
      hreg₉ r_base (by omega) (by omega) (by omega),
      hreg₈ r_base (by omega) (by omega) (by omega),
      hreg₇ r_base (by omega) (by omega) (by omega)]
    simp [s₆, s₅, s₄]
  have hr1_11 : s₁₁.regs (r_base + 1) = u₁.1 := by
    rw [hreg₁₁ (r_base + 1) (by omega) (by omega), hreg₁₀ (r_base + 1) (by omega) (by omega),
      hreg₉ (r_base + 1) (by omega) (by omega) (by omega),
      hreg₈ (r_base + 1) (by omega) (by omega) (by omega),
      hreg₇ (r_base + 1) (by omega) (by omega) (by omega)]
    simp [s₆, s₅]
  have hr2_11 : s₁₁.regs (r_base + 2) = u₂.1 := by
    rw [hreg₁₁ (r_base + 2) (by omega) (by omega), hreg₁₀ (r_base + 2) (by omega) (by omega),
      hreg₉ (r_base + 2) (by omega) (by omega) (by omega),
      hreg₈ (r_base + 2) (by omega) (by omega) (by omega),
      hreg₇ (r_base + 2) (by omega) (by omega) (by omega)]
    simp [s₆]
  have hr7_11 : s₁₁.regs (r_base + 7) = Q₁.length := by
    rw [hreg₁₁ (r_base + 7) (by omega) (by omega), hreg₁₀ (r_base + 7) (by omega) (by omega),
      hreg₉ (r_base + 7) (by omega) (by omega) (by omega), hlen1_8]
  have hr8_11 : s₁₁.regs (r_base + 8) = Q₂.length := by
    rw [hreg₁₁ (r_base + 8) (by omega) (by omega), hreg₁₀ (r_base + 8) (by omega) (by omega),
      hlen2_9]
  have hr9_11 : s₁₁.regs (r_base + 9) = (if isClockwiseCorners p.corners ep₀ ep₁ ep₂ then 1 else 0) := by
    rw [hreg₁₁ (r_base + 9) (by omega) (by omega), hcw₁₀]
  have hQ1_11 : s₁₁.arrs a_Q1 = Q₁ := by
    rw [harr₁₁ a_Q1 (by omega), harr₁₀ a_Q1, harr₉ a_Q1 (by omega) (by omega), hQ1_8]
  have hQ2_11 : s₁₁.arrs a_Q2 = Q₂ := by
    rw [harr₁₁ a_Q2 (by omega), harr₁₀ a_Q2, hQ2_9]
  have harr_lt_11 : ∀ a < a_sSeq, s₁₁.arrs a = s.arrs a := by
    intro a ha
    rw [harr₁₁ a (by omega), harr₁₀ a, harr₉ a (by omega) (by omega),
      harr₈ a (by omega) (by omega), harr₇ a (by omega) (by omega)]
    simp [s₆, s₅, s₄, harr₃ a (by omega), s₂, harr₁ a (by omega)]
  have hreg_lt_11 : ∀ r_reg < r_base, r_reg ≠ r_P1Len → s₁₁.regs r_reg = s.regs r_reg := by
    intro r_reg hr_lt hne1
    rw [hreg₁₁ r_reg (by omega) hne1, hreg₁₀ r_reg (by omega) (by omega),
      hreg₉ r_reg (by omega) (by omega) (by omega),
      hreg₈ r_reg (by omega) (by omega) (by omega),
      hreg₇ r_reg (by omega) (by omega) (by omega)]
    simp [s₆, s₅, s₄, show r_reg ≠ r_base by omega, show r_reg ≠ r_base + 1 by omega,
      show r_reg ≠ r_base + 2 by omega, hreg₃ r_reg (by omega),
      s₂, hreg₁ r_reg hr_lt]
  -- 8. Branch on r_base + 9 == 1
  by_cases hcw : isClockwiseCorners p.corners ep₀ ep₁ ep₂ = true
  · simp only [hcw, ↓reduceIte] at hr9_11 hvalid_ite
    have hcond : (Expr.op .eq (.reg (r_base + 9)) (.const 1)).eval w s₁₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_11, hw]
    rcases writeTripleSSeqProg_exec a_sSeq r_sLen r_base (r_base + 1) (r_base + 2)
        (by omega) (by omega) (by omega) hw3 hu0_w hu1_w hu2_w hr0_11 hr1_11 hr2_11 with
      ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hsSeq₁₂, hrsLen₁₂, harr₁₂, hreg₁₂⟩
    rcases copyArrWithLenProg_exec Q₁ (hQ_w u₁) a_Q1 a_P2 (r_base + 7) r_P2Len (r_base + 10)
        (by omega) (by omega) (by omega) hw (by omega)
        (by rw [harr₁₂ a_Q1 (by omega), hQ1_11])
        (by rw [hreg₁₂ (r_base + 7) (by omega), hr7_11]) with
      ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hP2_13, hrP2_13, harr₁₃, hreg₁₃⟩
    have ht₁₃' : t₁₃ ≤ 16 * n + 27 := by
      have : ((traceWalkStopB hsys₃.1 n u₁).2.support.map Fin.val).length ≤ n + 1 := hQ1_len_le
      omega
    rcases copyArrWithLenProg_exec Q₂ (hQ_w u₂) a_Q2 a_P3 (r_base + 8) r_P3Len (r_base + 10)
        (by omega) (by omega) (by omega) hw (by omega)
        (by rw [harr₁₃ a_Q2 (by omega), harr₁₂ a_Q2 (by omega), hQ2_11])
        (by rw [hreg₁₃ (r_base + 8) (by omega) (by omega),
              hreg₁₂ (r_base + 8) (by omega), hr8_11]) with
      ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hP3_14, hrP3_14, harr₁₄, hreg₁₄⟩
    have ht₁₄' : t₁₄ ≤ 16 * n + 27 := by
      have : ((traceWalkStopB hsys₃.1 n u₂).2.support.map Fin.val).length ≤ n + 1 := hQ2_len_le
      omega
    have htime_tot :
        t₁ + (2 + (t₃ + (3 + (3 + (3 + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + (3 + (t₁₂ + (t₁₃ + t₁₄))))))))))))) ≤
          1020 * n + 93 * totalAdjEntries lists + 650 := by
      linarith
    refine ⟨s₁₄,
      t₁ + (2 + (t₃ + (3 + (3 + (3 + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + (3 + (t₁₂ + (t₁₃ + t₁₄))))))))))))),
      [u₀.1, u₁.1, u₂.1], Q₀, Q₁, Q₂,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
        (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁
          (.ite_true hcond (by omega) (.seq hex₁₂ (.seq hex₁₃ hex₁₄))))))))))))),
      htime_tot,
      by rw [harr₁₄ a_sSeq (by omega), harr₁₃ a_sSeq (by omega), hsSeq₁₂],
      by rw [harr₁₄ a_P1 (by omega), harr₁₃ a_P1 (by omega), harr₁₂ a_P1 (by omega), hP1_11],
      by rw [harr₁₄ a_P2 (by omega), hP2_13],
      hP3_14,
      by rw [hreg₁₄ r_sLen (by omega) (by omega), hreg₁₃ r_sLen (by omega) (by omega), hrsLen₁₂]; rfl,
      by rw [hreg₁₄ r_P1Len (by omega) (by omega), hreg₁₃ r_P1Len (by omega) (by omega),
           hreg₁₂ r_P1Len (by omega), hrP1_11],
      by rw [hreg₁₄ r_P2Len (by omega) (by omega), hrP2_13],
      hrP3_14,
      hvalid_ite,
      fun a ha => by
        rw [harr₁₄ a (by omega), harr₁₃ a (by omega), harr₁₂ a (by omega), harr_lt_11 a ha],
      fun r_reg hr_lt hne0 hne1 hne2 hne3 => by
        rw [hreg₁₄ r_reg (by omega) hne3, hreg₁₃ r_reg (by omega) hne2,
          hreg₁₂ r_reg hne0, hreg_lt_11 r_reg hr_lt hne1]⟩
  · simp only [hcw, Bool.false_eq_true, ↓reduceIte] at hr9_11 hvalid_ite
    have hcond : (Expr.op .eq (.reg (r_base + 9)) (.const 1)).eval w s₁₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_11, hw, h0_w]
    rcases writeTripleSSeqProg_exec a_sSeq r_sLen r_base (r_base + 2) (r_base + 1)
        (by omega) (by omega) (by omega) hw3 hu0_w hu2_w hu1_w hr0_11 hr2_11 hr1_11 with
      ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hsSeq₁₂, hrsLen₁₂, harr₁₂, hreg₁₂⟩
    rcases copyArrWithLenProg_exec Q₂ (hQ_w u₂) a_Q2 a_P2 (r_base + 8) r_P2Len (r_base + 10)
        (by omega) (by omega) (by omega) hw (by omega)
        (by rw [harr₁₂ a_Q2 (by omega), hQ2_11])
        (by rw [hreg₁₂ (r_base + 8) (by omega), hr8_11]) with
      ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hP2_13, hrP2_13, harr₁₃, hreg₁₃⟩
    have ht₁₃' : t₁₃ ≤ 16 * n + 27 := by
      have : ((traceWalkStopB hsys₃.1 n u₂).2.support.map Fin.val).length ≤ n + 1 := hQ2_len_le
      omega
    rcases copyArrWithLenProg_exec Q₁ (hQ_w u₁) a_Q1 a_P3 (r_base + 7) r_P3Len (r_base + 10)
        (by omega) (by omega) (by omega) hw (by omega)
        (by rw [harr₁₃ a_Q1 (by omega), harr₁₂ a_Q1 (by omega), hQ1_11])
        (by rw [hreg₁₃ (r_base + 7) (by omega) (by omega),
              hreg₁₂ (r_base + 7) (by omega), hr7_11]) with
      ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hP3_14, hrP3_14, harr₁₄, hreg₁₄⟩
    have ht₁₄' : t₁₄ ≤ 16 * n + 27 := by
      have : ((traceWalkStopB hsys₃.1 n u₁).2.support.map Fin.val).length ≤ n + 1 := hQ1_len_le
      omega
    have htime_tot :
        t₁ + (2 + (t₃ + (3 + (3 + (3 + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + (3 + (t₁₂ + (t₁₃ + t₁₄))))))))))))) ≤
          1020 * n + 93 * totalAdjEntries lists + 650 := by
      linarith
    refine ⟨s₁₄,
      t₁ + (2 + (t₃ + (3 + (3 + (3 + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + (3 + (t₁₂ + (t₁₃ + t₁₄))))))))))))),
      [u₀.1, u₂.1, u₁.1], Q₀, Q₂, Q₁,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
        (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁
          (.ite_false hcond (.seq hex₁₂ (.seq hex₁₃ hex₁₄))))))))))))),
      htime_tot,
      by rw [harr₁₄ a_sSeq (by omega), harr₁₃ a_sSeq (by omega), hsSeq₁₂],
      by rw [harr₁₄ a_P1 (by omega), harr₁₃ a_P1 (by omega), harr₁₂ a_P1 (by omega), hP1_11],
      by rw [harr₁₄ a_P2 (by omega), hP2_13],
      hP3_14,
      by rw [hreg₁₄ r_sLen (by omega) (by omega), hreg₁₃ r_sLen (by omega) (by omega), hrsLen₁₂]; rfl,
      by rw [hreg₁₄ r_P1Len (by omega) (by omega), hreg₁₃ r_P1Len (by omega) (by omega),
           hreg₁₂ r_P1Len (by omega), hrP1_11],
      by rw [hreg₁₄ r_P2Len (by omega) (by omega), hrP2_13],
      hrP3_14,
      hvalid_ite,
      fun a ha => by
        rw [harr₁₄ a (by omega), harr₁₃ a (by omega), harr₁₂ a (by omega), harr_lt_11 a ha],
      fun r_reg hr_lt hne0 hne1 hne2 hne3 => by
        rw [hreg₁₄ r_reg (by omega) hne3, hreg₁₃ r_reg (by omega) hne2,
          hreg₁₂ r_reg hne0, hreg_lt_11 r_reg hr_lt hne1]⟩

theorem buildStep1AttachmentProg_exec {w n q : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q X'.toNatSet p.toGMWall p.toSociety p.toDivision)
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_corners a_B_bar a_bList
      a_sSeq a_P1 a_P2 a_P3 a_A_bd a_buf a_Q0 a_Q1 a_Q2 a_ps : ℕ)
    (r_n r_bLen r_sLen r_P1Len r_P2Len r_P3Len r_base : ℕ)
    (ha_st : a_start < a_sSeq) (ha_en : a_end < a_sSeq) (ha_ent : a_entries < a_sSeq)
    (ha_cor : a_corners < a_sSeq) (ha_Bbar : a_B_bar < a_sSeq) (ha_bL : a_bList < a_sSeq)
    (ha_order : a_sSeq < a_P1 ∧ a_P1 < a_P2 ∧ a_P2 < a_P3 ∧ a_P3 < a_A_bd ∧
      a_A_bd < a_buf ∧ a_buf < a_Q0 ∧ a_Q0 < a_Q1 ∧ a_Q1 < a_Q2 ∧ a_Q2 < a_ps)
    (hr_n : r_n < r_sLen) (hr_bL : r_bLen < r_sLen)
    (hr_order : r_sLen < r_P1Len ∧ r_P1Len < r_P2Len ∧ r_P2Len < r_P3Len ∧ r_P3Len < r_base)
    (hw6 : 6 < 2 ^ w) (h2n_w : 2 * n + 2 < 2 ^ w)
    {s : State}
    (hadj : IsAdjList (G.deleteVertices (Z_notK p)).toSimpleGraph a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hcor : s.arrs a_corners = p.corners)
    (hBbar : s.arrs a_B_bar = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ p.corners)))
    (hbL : s.arrs a_bList = memberBoundaryList p.corners p.K_eList r)
    (hrn : s.regs r_n = n)
    (hrbL : s.regs r_bLen = (memberBoundaryList p.corners p.K_eList r).length) :
    ∃ s' t sSeq P₁ P₂ P₃,
      Exec w (buildStep1AttachmentProg a_start a_end a_entries a_corners a_B_bar a_bList
        a_sSeq a_P1 a_P2 a_P3 a_A_bd a_buf a_Q0 a_Q1 a_Q2 a_ps
        r_n r_bLen r_sLen r_P1Len r_P2Len r_P3Len r_base) s s' t ∧
      t ≤ 1020 * n + 93 * totalAdjEntries lists + 660 ∧
      s'.arrs a_sSeq = sSeq ∧
      s'.arrs a_P1 = P₁ ∧
      s'.arrs a_P2 = P₂ ∧
      s'.arrs a_P3 = P₃ ∧
      s'.regs r_sLen = sSeq.length ∧
      s'.regs r_P1Len = P₁.length ∧
      s'.regs r_P2Len = P₂.length ∧
      s'.regs r_P3Len = P₃.length ∧
      Step1AttachmentValid p r sSeq P₁ P₂ P₃ ∧
      (∀ a < a_sSeq, s'.arrs a = s.arrs a) ∧
      (∀ r_reg < r_base,
        r_reg ≠ r_sLen → r_reg ≠ r_P1Len → r_reg ≠ r_P2Len → r_reg ≠ r_P3Len →
        s'.regs r_reg = s.regs r_reg) := by
  have hw : 1 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let bList := memberBoundaryList p.corners p.K_eList r
  have hb_nd : bList.Nodup := nodup_memberBoundaryList p hr
  have hb_le3 : bList.length ≤ 3 := by
    have hA_mem : r.toSubgraph (delGraph G X') ∈ p.toDivision := ⟨r, hr, rfl⟩
    have hB_eq : GM13.divBoundary p.toSociety (r.toSubgraph (delGraph G X')) =
        (bList.toFinset : Set ℕ) := by
      ext x
      simp only [Finset.mem_coe, List.mem_toFinset, mem_memberBoundaryList_iff p hr, bList]
    have hle := hC.isRuralDivision.1.boundary_ncard_le_three hA_mem
    rw [hB_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hb_nd] at hle
    exact hle
  have hb_lt : ∀ x ∈ bList, x < n :=
    fun x hx => p.member_vList_lt hr (List.mem_of_mem_filter hx)
  have hb_w : ∀ x ∈ bList, x < 2 ^ w := fun x hx => Nat.lt_trans (hb_lt x hx) hn_w
  by_cases hlt3 : bList.length < 3
  · have hcond : (Expr.op .lt (.reg r_bLen) (.const 3)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbL, bList, hlt3, hw, hw3,
        show bList.length < 2 ^ w by omega]
    rcases copyArrWithLenProg_exec bList hb_w a_bList a_sSeq r_bLen r_sLen r_base
        (by omega) (by omega) (by omega) hw (by omega) hbL hrbL with
      ⟨s₁, t₁, hex₁, ht₁, hsSeq₁, hrsLen₁, harr₁, hreg₁⟩
    rcases allocEmptyArrProg_exec a_P1 r_P1Len hw s₁ with
      ⟨s₂, t₂, hex₂, ht₂, hP1_2, hrP1_2, harr₂, hreg₂⟩
    rcases allocEmptyArrProg_exec a_P2 r_P2Len hw s₂ with
      ⟨s₃, t₃, hex₃, ht₃, hP2_3, hrP2_3, harr₃, hreg₃⟩
    rcases allocEmptyArrProg_exec a_P3 r_P3Len hw s₃ with
      ⟨s₄, t₄, hex₄, ht₄, hP3_4, hrP3_4, harr₄, hreg₄⟩
    have hval : Step1AttachmentValid p r bList [] [] [] := by
      refine ⟨hb_nd, rfl, by omega, hb_lt, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
      have hne3 : bList.length ≠ 3 := by omega
      simp [hne3]
    refine ⟨s₄, 3 + (t₁ + (t₂ + (t₃ + t₄))), bList, [], [], [],
      .ite_true hcond (by omega) (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))),
      by omega,
      by rw [harr₄ a_sSeq (by omega), harr₃ a_sSeq (by omega), harr₂ a_sSeq (by omega), hsSeq₁],
      by rw [harr₄ a_P1 (by omega), harr₃ a_P1 (by omega), hP1_2],
      by rw [harr₄ a_P2 (by omega), hP2_3],
      hP3_4,
      by rw [hreg₄ r_sLen (by omega), hreg₃ r_sLen (by omega), hreg₂ r_sLen (by omega), hrsLen₁],
      by rw [hreg₄ r_P1Len (by omega), hreg₃ r_P1Len (by omega), hrP1_2]; rfl,
      by rw [hreg₄ r_P2Len (by omega), hrP2_3]; rfl,
      hrP3_4,
      hval,
      fun a ha => by
        rw [harr₄ a (by omega), harr₃ a (by omega), harr₂ a (by omega), harr₁ a (by omega)],
      fun r_reg hr_lt hne0 hne1 hne2 hne3 => by
        rw [hreg₄ r_reg hne3, hreg₃ r_reg hne2, hreg₂ r_reg hne1, hreg₁ r_reg hr_lt hne0]⟩
  · have hlen3 : bList.length = 3 := by omega
    have hcond : (Expr.op .lt (.reg r_bLen) (.const 3)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbL, bList, hlen3, hw3, h0_w]
    have hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety := by
      rw [delGraph_eq]; exact hC.isWallSociety
    rcases step1Len3Prog_exec p hWS hC.isRuralDivision.1 hr hlen3 lists
        a_start a_end a_entries a_corners a_B_bar a_bList
        a_sSeq a_P1 a_P2 a_P3 a_A_bd a_buf a_Q0 a_Q1 a_Q2 a_ps
        r_n r_bLen r_sLen r_P1Len r_P2Len r_P3Len r_base
        ha_st ha_en ha_ent ha_cor ha_Bbar ha_bL ha_order
        hr_n hr_bL hr_order hw6 h2n_w
        hadj hent_w hcor hBbar hbL hrn (by rw [hrbL, hlen3]) with
      ⟨s₁, t₁, sSeq, P₁, P₂, P₃, hex₁, ht₁, hsSeq₁, hP1_1, hP2_1, hP3_1,
        hrsLen₁, hrP1_1, hrP2_1, hrP3_1, hval₁, harr₁, hreg₁⟩
    exact ⟨s₁, 3 + t₁, sSeq, P₁, P₂, P₃, .ite_false hcond hex₁, by omega,
      hsSeq₁, hP1_1, hP2_1, hP3_1, hrsLen₁, hrP1_1, hrP2_1, hrP3_1, hval₁, harr₁, hreg₁⟩

/-! ### Section 4: Step 4 Representative Wall Vertex `v(A)` and Path (`buildStep4VOfProg`) -/

/-- Loop body of `findPathStartProg`: if `a_used[r_base] == 1 && a_pred[r_base] == r_n`, sets
`r_u0 := r_base`. -/
def findPathStartBody (a_used a_pred : Arr) (r_n r_u0 r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_used (.reg r_base)))
    (.seq (.assign (r_base + 2) (.read a_pred (.reg r_base)))
      (.ite (.op .mul (.op .eq (.reg (r_base + 1)) (.const 1))
          (.op .eq (.reg (r_base + 2)) (.reg r_n)))
        (.assign r_u0 (.reg r_base))
        .skip))

/-- Scan `0 .. r_n - 1` to find a vertex `u₀` with `a_used[u₀] == 1` and `a_pred[u₀] == r_n`. -/
def findPathStartProg (a_used a_pred : Arr) (r_n r_u0 r_base : Reg) : Cmd :=
  .seq (.assign r_u0 (.const 0))
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_n) (findPathStartBody a_used a_pred r_n r_u0 r_base)))

theorem findPathStartLoop_exec {w n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {u₀ : Fin n} (hu₀ : pathStarts used pred = {u₀})
    (a_used a_pred r_n r_u0 r_base : ℕ)
    (hr_n : r_n < r_base) (hr_u0 : r_u0 < r_base) (hne_nu : r_n ≠ r_u0)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n)
    {s : State}
    (hused : s.arrs a_used = List.ofFn used)
    (hpred : s.arrs a_pred = List.ofFn pred)
    (hrn : s.regs r_n = n)
    (hru0 : u₀.1 < k → s.regs r_u0 = u₀.1)
    (hrbase : s.regs r_base = k) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_n) (findPathStartBody a_used a_pred r_n r_u0 r_base)) s s' t ∧
      t ≤ 3 + 22 * rem ∧
      s'.regs r_u0 = u₀.1 ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_u0 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrn, hn_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hru0 u₀.2, fun _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    let v : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrn, hk_w, hn_w, hk_lt, hw]
    have huv_w : used v < 2 ^ w := Nat.lt_of_le_of_lt (hsys.used_le v) hw
    have hpv_w : pred v < 2 ^ w := Nat.lt_of_le_of_lt (hsys.pred_le v) (by omega)
    let s₁ := s.setReg (r_base + 1) (used v)
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_used (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrbase, hk_w, hused, hk_lt, v, huv_w])
    let s₂ := s₁.setReg (r_base + 2) (pred v)
    have hex₂ : Exec w (.assign (r_base + 2) (.read a_pred (.reg r_base))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hrbase, hk_w, hpred, hk_lt, v, hpv_w])
    have hv_iff : (used v = 1 ∧ pred v = n) ↔ v = u₀ := by
      have hmem : v ∈ pathStarts used pred ↔ v = u₀ := by rw [hu₀, Finset.mem_singleton]
      rw [mem_pathStarts] at hmem
      have hle := hsys.used_le v
      exact ⟨fun ⟨h1, h2⟩ => hmem.mp ⟨by omega, h2⟩,
        fun h => by rcases hmem.mpr h with ⟨h1, h2⟩; exact ⟨by omega, h2⟩⟩
    by_cases hvu : v = u₀
    · rcases hv_iff.mpr hvu with ⟨hu1, hp1⟩
      have hev_ite :
          (Expr.op .mul (.op .eq (.reg (r_base + 1)) (.const 1))
            (.op .eq (.reg (r_base + 2)) (.reg r_n))).eval w s₂ = some 1 := by
        simp [s₂, s₁, show r_n ≠ r_base + 1 by omega, show r_n ≠ r_base + 2 by omega,
          Expr.eval, BinOp.eval, BinOp.raw, checkWord, hu1, hp1, hrn, hw, hn_w]
      let s₃ := s₂.setReg r_u0 k
      have hex₃ : Exec w (.assign r_u0 (.reg r_base)) s₂ s₃ 2 :=
        .assign (by
          simp [s₂, s₁, Expr.eval, checkWord, hrbase, hk_w])
      let s₄ := s₃.setReg r_base (k + 1)
      have hex₄ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₃ s₄ 4 :=
        .assign (by
          simp [s₃, s₂, s₁, show r_base ≠ r_u0 by omega,
            Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hk_w, hw, hk1_w])
      rcases ih (k + 1) (by omega) (s := s₄)
          (by simp [s₄, s₃, s₂, s₁, hused])
          (by simp [s₄, s₃, s₂, s₁, hpred])
          (by simp [s₄, s₃, s₂, s₁, show r_n ≠ r_base by omega, hne_nu,
            show r_n ≠ r_base + 1 by omega, show r_n ≠ r_base + 2 by omega, hrn])
          (fun _ => by
            have hk_u0 : k = u₀.1 := congrArg Fin.val hvu
            simp [s₄, s₃, show r_u0 ≠ r_base by omega, hk_u0])
          (by simp [s₄]) with
        ⟨s₅, t₅, hex₅, ht₅, hru0_5, harr₅, hreg₅⟩
      refine ⟨s₅, 3 + ((3 + (3 + (7 + 2))) + 4) + t₅,
        .while_true hcond (by omega)
          (.seq (.seq hex₁ (.seq hex₂ (.ite_true hev_ite (by omega) hex₃))) hex₄) hex₅,
        by omega, hru0_5, harr₅,
        fun r hr hne => by
          rw [hreg₅ r hr hne]
          simp [s₄, s₃, s₂, s₁, show r ≠ r_base by omega, hne,
            show r ≠ r_base + 1 by omega, show r ≠ r_base + 2 by omega]⟩
    · have hnot : ¬ (used v = 1 ∧ pred v = n) := fun h => hvu (hv_iff.mp h)
      have hev_ite :
          (Expr.op .mul (.op .eq (.reg (r_base + 1)) (.const 1))
            (.op .eq (.reg (r_base + 2)) (.reg r_n))).eval w s₂ = some 0 := by
        simp only [s₂, s₁, State.setReg, Function.update_apply,
          show r_n ≠ r_base + 1 by omega, show r_n ≠ r_base + 2 by omega,
          show r_base + 1 ≠ r_base + 2 by omega, ↓reduceIte,
          Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hw, hn_w, huv_w, hpv_w]
        by_cases h1 : used v = 1 <;> by_cases h2 : pred v = n
        · exact (hnot ⟨h1, h2⟩).elim
        · simp [h1, h2, h0_w, hw]
        · simp [h1, h2, h0_w, hw]
        · simp [h1, h2, h0_w]
      let s₃ := s₂.setReg r_base (k + 1)
      have hex₃ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₂ s₃ 4 :=
        .assign (by
          simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hk_w, hw, hk1_w])
      rcases ih (k + 1) (by omega) (s := s₃)
          (by simp [s₃, s₂, s₁, hused])
          (by simp [s₃, s₂, s₁, hpred])
          (by simp [s₃, s₂, s₁, show r_n ≠ r_base by omega,
            show r_n ≠ r_base + 1 by omega, show r_n ≠ r_base + 2 by omega, hrn])
          (fun hlt => by
            have hne_k : u₀.1 ≠ k := fun h => hvu (Fin.ext h.symm)
            have hlt' : u₀.1 < k := by omega
            simp [s₃, s₂, s₁, show r_u0 ≠ r_base by omega,
              show r_u0 ≠ r_base + 1 by omega, show r_u0 ≠ r_base + 2 by omega, hru0 hlt'])
          (by simp [s₃]) with
        ⟨s₄, t₄, hex₄, ht₄, hru0_4, harr₄, hreg₄⟩
      refine ⟨s₄, 3 + ((3 + (3 + (7 + 1))) + 4) + t₄,
        .while_true hcond (by omega)
          (.seq (.seq hex₁ (.seq hex₂ (.ite_false hev_ite (.skip s₂)))) hex₃) hex₄,
        by omega, hru0_4, harr₄,
        fun r hr hne => by
          rw [hreg₄ r hr hne]
          simp [s₃, s₂, s₁, show r ≠ r_base by omega,
            show r ≠ r_base + 1 by omega, show r ≠ r_base + 2 by omega]⟩

theorem findPathStartProg_exec {w n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {u₀ : Fin n} (hu₀ : pathStarts used pred = {u₀})
    (a_used a_pred r_n r_u0 r_base : ℕ)
    (hr_n : r_n < r_base) (hr_u0 : r_u0 < r_base) (hne_nu : r_n ≠ r_u0)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hused : s.arrs a_used = List.ofFn used)
    (hpred : s.arrs a_pred = List.ofFn pred)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (findPathStartProg a_used a_pred r_n r_u0 r_base) s s' t ∧
      t ≤ 22 * n + 10 ∧
      s'.regs r_u0 = u₀.1 ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_u0 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_u0 0
  have hex₁ : Exec w (.assign r_u0 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases findPathStartLoop_exec hsys hu₀ a_used a_pred r_n r_u0 r_base
      hr_n hr_u0 hne_nu hw hn_w n 0 (by omega) (s := s₂)
      (by simp [s₂, s₁, hused])
      (by simp [s₂, s₁, hpred])
      (by simp [s₂, s₁, show r_n ≠ r_base by omega, hne_nu, hrn])
      (fun h => by omega)
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hru0_3, harr₃, hreg₃⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hru0_3, harr₃,
    fun r hr hne => by
      rw [hreg₃ r hr hne]
      simp [s₂, s₁, show r ≠ r_base by omega, hne]⟩

/-- Package of all Step 4 validity conditions on `(vOf, vOfPath)` in `isValidVisionMemberRecord`. -/
def Step4VOfValid {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (r : Case3MemberRecord)
    (vOf : ℕ) (vOfPath : List ℕ) : Prop :=
  let bList := memberBoundaryList p.corners p.K_eList r
  let s₀ := vOfPath.headD 0
  vOf < n ∧
  vOfPath.length ≤ n + 1 ∧
  (∀ x ∈ vOfPath, x < n) ∧
  vOf ∈ p.wallSec.W.vertexFinset.image Fin.val ∧
  isValidKPathBetween p.K_vList p.K_eList vOfPath s₀ vOf = true ∧
  (s₀ ∈ bList ∨ (bList = [] ∧ s₀ ∈ r.vList)) ∧
  (∀ v ∈ vOfPath, v ∈ p.wallSec.W.vertexFinset.image Fin.val ↔ v = vOf)

/-- Step 4 Word RAM program for an interior member `r ∈ p.members`:
1. Builds `bitSetList A_start` in `a_A_start` (`r.vList` if `r_bLen == 0`, else `bList`).
2. Runs Menger ($k=1$) from `a_A_start` to `a_WH` (`bitSetList p.wallSec.W.vertexFinset`) in `G_K`.
3. Finds the unique start vertex `u₀` in `r_base` via `findPathStartProg`.
4. Traces `vOfPath` into `a_vOfPath` with endpoint `r_vOf` and length `r_vOfPathLen` via
   `traceWalkStopBProg`. -/
def buildStep4VOfProg (a_start a_end a_entries a_WH a_bList a_vList
    a_vOfPath a_A_start a_buf a_ps : Arr)
    (r_n r_bLen r_vLen r_vOf r_vOfPathLen r_base : Reg) : Cmd :=
  .seq (.ite (.op .eq (.reg r_bLen) (.const 0))
      (buildListIndProg a_vList a_A_start r_vLen r_n r_base)
      (buildListIndProg a_bList a_A_start r_bLen r_n r_base))
    (.seq (.assign r_base (.const 1))
      (.seq (runMengerPathSystemProg a_start a_end a_entries a_A_start a_WH a_ps
          r_n r_base (r_base + 1))
        (.seq (findPathStartProg a_ps (a_ps + 1) r_n r_base (r_base + 1))
          (traceWalkStopBProg (a_ps + 2) a_WH a_buf a_vOfPath
            r_base r_n r_vOf r_vOfPathLen (r_base + 1)))))

theorem buildStep4VOfProg_exec {w n q : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q X'.toNatSet p.toGMWall p.toSociety p.toDivision)
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    (hInt : isMemberInterior p.wallSec.W r = true)
    (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_WH a_bList a_vList
      a_vOfPath a_A_start a_buf a_ps : ℕ)
    (r_n r_bLen r_vLen r_vOf r_vOfPathLen r_base : ℕ)
    (ha_st : a_start < a_vOfPath) (ha_en : a_end < a_vOfPath) (ha_ent : a_entries < a_vOfPath)
    (ha_WH : a_WH < a_vOfPath) (ha_bL : a_bList < a_vOfPath) (ha_vL : a_vList < a_vOfPath)
    (ha_order : a_vOfPath < a_A_start ∧ a_A_start < a_buf ∧ a_buf < a_ps)
    (hr_n : r_n < r_vOf) (hr_bL : r_bLen < r_vOf) (hr_vL : r_vLen < r_vOf)
    (hr_order : r_vOf < r_vOfPathLen ∧ r_vOfPathLen < r_base)
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n + 2 < 2 ^ w)
    {s : State}
    (hadj : IsAdjList (G.deleteVertices (Z_notK p)).toSimpleGraph a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hWH : s.arrs a_WH = bitSetList p.wallSec.W.vertexFinset)
    (hbL : s.arrs a_bList = memberBoundaryList p.corners p.K_eList r)
    (hvL : s.arrs a_vList = r.vList)
    (hrn : s.regs r_n = n)
    (hrbL : s.regs r_bLen = (memberBoundaryList p.corners p.K_eList r).length)
    (hrvL : s.regs r_vLen = r.vList.length) :
    ∃ s' t vOf vOfPath,
      Exec w (buildStep4VOfProg a_start a_end a_entries a_WH a_bList a_vList
        a_vOfPath a_A_start a_buf a_ps
        r_n r_bLen r_vLen r_vOf r_vOfPathLen r_base) s s' t ∧
      t ≤ 360 * n + 14 * r.vList.length + 31 * totalAdjEntries lists + 200 ∧
      s'.arrs a_vOfPath = vOfPath ∧
      s'.regs r_vOf = vOf ∧
      s'.regs r_vOfPathLen = vOfPath.length ∧
      Step4VOfValid p r vOf vOfPath ∧
      (∀ a < a_vOfPath, s'.arrs a = s.arrs a) ∧
      (∀ r_reg < r_base, r_reg ≠ r_vOf → r_reg ≠ r_vOfPathLen → s'.regs r_reg = s.regs r_reg) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let bList := memberBoundaryList p.corners p.K_eList r
  let startList := if bList.isEmpty then r.vList else bList
  have hr_val := p.member_valid_iff hr
  have hv_lt : ∀ x ∈ r.vList, x < n := fun x hx => p.member_vList_lt hr hx
  have hb_lt : ∀ x ∈ bList, x < n := fun x hx => hv_lt x (List.mem_of_mem_filter hx)
  have hvL_le : r.vList.length ≤ n := hr_val.1
  have hbL_le : bList.length ≤ r.vList.length := List.length_filter_le _ _
  -- 1. Build bitSetList A_start in a_A_start
  let A_start := Finset.univ.filter (fun u : Fin n => u.1 ∈ startList)
  have hex₁_combined :
      ∃ s₁ t₁,
        Exec w (.ite (.op .eq (.reg r_bLen) (.const 0))
          (buildListIndProg a_vList a_A_start r_vLen r_n r_base)
          (buildListIndProg a_bList a_A_start r_bLen r_n r_base)) s s₁ t₁ ∧
        t₁ ≤ 2 * n + 14 * r.vList.length + 13 ∧
        s₁.arrs a_A_start = bitSetList A_start ∧
        (∀ a : ℕ, a ≠ a_A_start → s₁.arrs a = s.arrs a) ∧
        (∀ r_reg < r_base, s₁.regs r_reg = s.regs r_reg) := by
    by_cases h0 : bList.length = 0
    · have hnil : bList = [] := List.eq_nil_of_length_eq_zero h0
      have hstart_eq : startList = r.vList := by simp [startList, hnil]
      have hcond : (Expr.op .eq (.reg r_bLen) (.const 0)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbL, bList, h0, h0_w, hw]
      rcases buildListIndProg_exec r.vList hv_lt a_vList a_A_start r_vLen r_n r_base
          (by omega) (by omega) (by omega) hw hn_w (by omega) hvL hrvL hrn with
        ⟨s₁, t₁, hex₁, ht₁, hout₁, harr₁, hreg₁⟩
      rw [← hstart_eq] at hout₁
      exact ⟨s₁, 3 + t₁, .ite_true hcond (by omega) hex₁, by omega, hout₁, harr₁, hreg₁⟩
    · have hne : bList.isEmpty = false := by
        cases hb : bList with
        | nil => simp [hb] at h0
        | cons _ _ => rfl
      have hstart_eq : startList = bList := by simp [startList, hne]
      have hcond : (Expr.op .eq (.reg r_bLen) (.const 0)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbL, bList, h0, h0_w,
          show bList.length < 2 ^ w by omega]
      rcases buildListIndProg_exec bList hb_lt a_bList a_A_start r_bLen r_n r_base
          (by omega) (by omega) (by omega) hw hn_w (by omega) hbL hrbL hrn with
        ⟨s₁, t₁, hex₁, ht₁, hout₁, harr₁, hreg₁⟩
      rw [← hstart_eq] at hout₁
      exact ⟨s₁, 3 + t₁, .ite_false hcond hex₁, by omega, hout₁, harr₁, hreg₁⟩
  rcases hex₁_combined with ⟨s₁, t₁, hex₁, ht₁, hA_start₁, harr₁, hreg₁⟩
  -- 2. Set r_base := 1 and run Menger k = 1
  let s₂ := s₁.setReg r_base 1
  have hex₂ : Exec w (.assign r_base (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hadj₂ :
      IsAdjList (G.deleteVertices (Z_notK p)).toSimpleGraph a_start a_end a_entries lists s₂ :=
    hadj.of_arrs_eq
      (by simp [s₂, harr₁ a_start (by omega)])
      (by simp [s₂, harr₁ a_end (by omega)])
      (by simp [s₂, harr₁ a_entries (by omega)])
  have hent₂_w : (s₂.arrs a_entries).length < 2 ^ w := by
    simp [s₂, harr₁ a_entries (by omega), hent_w]
  have hA₂_bit : IsBitSet A_start a_A_start s₂ :=
    IsBitSet.of_bitSetList A_start a_A_start s₂ (by simp [s₂, hA_start₁])
  have hB₂_bit : IsBitSet p.wallSec.W.vertexFinset a_WH s₂ :=
    IsBitSet.of_bitSetList p.wallSec.W.vertexFinset a_WH s₂
      (by simp [s₂, harr₁ a_WH (by omega), hWH])
  have hrn₂ : s₂.regs r_n = n := by
    simp [s₂, show r_n ≠ r_base by omega, hreg₁ r_n (by omega), hrn]
  rcases runMengerPathSystemProg_exec (G.deleteVertices (Z_notK p)).toSimpleGraph
      lists A_start p.wallSec.W.vertexFinset a_start a_end a_entries a_A_start a_WH a_ps
      r_n r_base (r_base + 1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw2 (by omega) hw
      (not_isABSeparator_step4 p hC hr hInt)
      hadj₂ hent₂_w hA₂_bit hB₂_bit hrn₂ (by simp [s₂]) with
    ⟨s₃, t₃, used, pred, succ, hex₃, ht₃, hsys₃, hcard₃, harr₃, hreg₃⟩
  obtain ⟨hused₃, hpred₃, hsucc₃⟩ := hsys₃.2.arrs_eq_ofFn
  obtain ⟨u₀, hu₀_eq⟩ := Finset.card_eq_one.mp hcard₃
  have hu₀_st : u₀ ∈ pathStarts used pred := by rw [hu₀_eq]; exact Finset.mem_singleton_self u₀
  -- 3. Find u₀ via findPathStartProg
  have hrn₃ : s₃.regs r_n = n := by rw [hreg₃ r_n (by omega), hrn₂]
  rcases findPathStartProg_exec hsys₃.1 hu₀_eq a_ps (a_ps + 1) r_n r_base (r_base + 1)
      (by omega) (by omega) (by omega) hw hn_w hused₃ hpred₃ hrn₃ with
    ⟨s₄, t₄, hex₄, ht₄, hru0_4, harr₄, hreg₄⟩
  -- 4. Trace vOfPath via traceWalkStopBProg
  have hWH₄ : s₄.arrs a_WH = bitSetList p.wallSec.W.vertexFinset := by
    rw [harr₄ a_WH, harr₃ a_WH (by omega)]; simp [s₂, harr₁ a_WH (by omega), hWH]
  rcases traceWalkStopBProg_exec hsys₃.1 u₀
      (a_ps + 2) a_WH a_buf a_vOfPath r_base r_n r_vOf r_vOfPathLen (r_base + 1)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw (by omega) (s := s₄)
      (by rw [harr₄ (a_ps + 2), hsucc₃]) hWH₄ hru0_4
      (by rw [hreg₄ r_n (by omega) (by omega), hrn₃]) with
    ⟨s₅, t₅, hex₅, ht₅, hpath₅, hvOf₅, hlen₅, harr₅, hreg₅⟩
  -- 5. Verify Step4VOfValid
  let res := traceWalkStopB hsys₃.1 n u₀
  let vOf := res.1.1
  let vOfPath := res.2.support.map Fin.val
  have hu₀_A : u₀ ∈ A_start := by
    rcases (mem_pathStarts u₀).mp hu₀_st with ⟨h1, h2⟩
    exact hsys₃.1.start_mem_A u₀ h1 h2
  have hu₀_start : u₀.1 ∈ startList := (Finset.mem_filter.mp hu₀_A).2
  have hu₀_vL : u₀.1 ∈ r.vList := by
    dsimp [startList] at hu₀_start
    split_ifs at hu₀_start with h
    · exact hu₀_start
    · exact List.mem_of_mem_filter hu₀_start
  have hu₀_K : u₀.1 ∈ p.K_vList := hr_val.2.2.1 u₀.1 hu₀_vL
  have hWS : GM13.IsWallSociety (delGraph G X') p.toGMWall p.toSociety := by
    rw [delGraph_eq]; exact hC.isWallSociety
  have hv_props := traceWalkStopB_valid_of_start p hWS hsys₃.1 hu₀_st hu₀_K
  have hwalk := traceWalkList_eq_traceWalkStopB hsys₃.1 n u₀
  unfold traceWalkList at hwalk
  have h1 : [u₀.1] ++ (traceWalkTail (List.ofFn succ)
      (bitSetList p.wallSec.W.vertexFinset) n n u₀.1).1 = vOfPath := by
    simpa [vOfPath, res] using congrArg Prod.fst hwalk
  have hpath_len : vOfPath.length ≤ n + 1 := by
    rw [← h1, List.length_append]
    have := length_traceWalkTail_le (List.ofFn succ) (bitSetList p.wallSec.W.vertexFinset) n n u₀.1
    simp; omega
  have hpath_lt : ∀ x ∈ vOfPath, x < n := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨w_x, _, rfl⟩
    exact w_x.2
  have hvOf_mem : vOf ∈ p.wallSec.W.vertexFinset.image Fin.val :=
    Finset.mem_image_of_mem Fin.val hv_props.2.1
  have hs₀_eq : vOfPath.headD 0 = u₀.1 := hv_props.2.2.1
  have hs₀_cond : vOfPath.headD 0 ∈ bList ∨ (bList = [] ∧ vOfPath.headD 0 ∈ r.vList) := by
    rw [hs₀_eq]
    dsimp [startList] at hu₀_start
    by_cases he : bList.isEmpty = true
    · simp only [he, ↓reduceIte] at hu₀_start
      exact Or.inr ⟨List.isEmpty_iff.mp he, hu₀_start⟩
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at hu₀_start
      exact Or.inl hu₀_start
  have hstop_WH : ∀ v ∈ vOfPath, v ∈ p.wallSec.W.vertexFinset.image Fin.val ↔ v = vOf := by
    intro v hv
    refine ⟨fun hvW => ?_, fun h => h ▸ hvOf_mem⟩
    rcases List.mem_map.mp hv with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hvW with ⟨y, hy, hyx⟩
    have hxy : x = y := Fin.ext hyx.symm
    subst hxy
    exact congrArg Fin.val (hv_props.2.2.2.2.2 x hx hy)
  have hstep4 : Step4VOfValid p r vOf vOfPath :=
    ⟨res.1.2, hpath_len, hpath_lt, hvOf_mem,
      by rw [hs₀_eq]; exact hv_props.1, hs₀_cond, hstop_WH⟩
  refine ⟨s₅, t₁ + (2 + (t₃ + (t₄ + t₅))), vOf, vOfPath,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hpath₅, hvOf₅, hlen₅, hstep4,
    fun a ha => by
      rw [harr₅ a (by omega) (by omega), harr₄ a, harr₃ a (by omega)]
      simp [s₂, harr₁ a (by omega)],
    fun r_reg hr_lt hne1 hne2 => by
      rw [hreg₅ r_reg (by omega) hne1 hne2, hreg₄ r_reg (by omega) (by omega),
        hreg₃ r_reg (by omega)]
      simp [s₂, show r_reg ≠ r_base by omega, hreg₁ r_reg hr_lt]⟩

end GraphMinor.Compute

