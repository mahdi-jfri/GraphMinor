module

import GraphMinor.Compute.CrossingClassProg

public import GraphMinor.Compute.CrossingOpsContract
public import GraphMinor.Compute.CrossingCleanRestore
public import GraphMinor.Crossing.CutSec4
public import GraphMinor.Crossing.CutSec91
public import GraphMinor.Crossing.CutSec94

/-!
# One trial of the contraction loop

Section 10, step 4 of `docs/crossing/crossing_extractor.tex`:
"copy the current instance; contract $uv$; restore cleanliness as in Section 9, using the markers
$N_K(u)\setminus\{v\}$; call `Classify` on the restored instance."

This file proves `trialRecProgClaim_of`, which establishes `TrialRecProgClaim` from
`RestoreRecNeProgClaim` and `ClassifyProgClaim`. It uses `copyInstanceRecProgClaim_proved`
(`CrossingOpsCopy.lean`), `contractRecProgClaim_proved` (`CrossingOpsContract.lean`), and the
already proved mathematical statements `sec91_proved`, `lemma7_proved`, and `sec4EdgeCount_proved`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### Combinatorial facts for a trial -/

/-- The degree `(G.neighborSet u).ncard` equals the length of `lists u` in `IsAdjListFamily`. -/
theorem ncard_neighborSet_eq_length {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (u : Fin N) :
    (G.neighborSet u).ncard = (lists u).length := by
  classical
  obtain ⟨Lu, hLu⟩ := exists_fin_list (lists u) (h u).1
  have hnd : Lu.Nodup := List.Nodup.of_map Fin.val (hLu ▸ (h u).2.1)
  have hmem : ∀ y : Fin N, y ∈ Lu ↔ y ∈ G.neighborSet u := by
    intro y
    rw [← List.mem_map_of_injective Fin.val_injective, hLu, (h u).2.2.2 y, mem_neighborSet]
  have hset : (Lu.toFinset : Set (Fin N)) = G.neighborSet u := by
    ext y
    simp [hmem y]
  rw [← hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    ← List.length_map (f := Fin.val), hLu]

/-- Upper bound on the length of `contrList lists u v x` that accounts for `contrList` at `u`
being empty. -/
theorem length_contrList_add_ite_le {N : ℕ} (lists : Fin N → List ℕ) {u v : ℕ} (huv : u ≠ v)
    (x : ℕ) :
    (contrList lists u v x).length + (if x = u then (listOf lists u).length else 0) ≤
      (listOf lists x).length + (if x = v then (listOf lists u).length else 0) := by
  by_cases hxu : x = u
  · subst hxu
    simp [contrList, huv]
  · have h := length_contrList_le lists u v x
    simp [hxu, h]

/-- Contracting an edge `uv` does not increase the number of edges. -/
theorem ncard_edgeSet_contractGraph_le {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) {u v : Fin N} (huv : G.Adj u v) :
    (contractGraph G u v).edgeSet.ncard ≤ G.edgeSet.ncard := by
  have hne : u.val ≠ v.val := fun e => huv.ne (Fin.ext e)
  have hfam := isAdjListFamily_contrList h huv
  have h1 : (flatUpTo (contrList lists u.val v.val) N).length =
      2 * (contractGraph G u v).edgeSet.ncard := length_flatUpTo_eq hfam
  have h2 : ∑ x ∈ Finset.range N, (listOf lists x).length = 2 * G.edgeSet.ncard := by
    have := length_flatUpTo_eq (H := G) (L := listOf lists) (fun x => by simpa [listOf_fin] using h x)
    rw [← this, length_flatUpTo]
  have hsum := Finset.sum_le_sum (s := Finset.range N) fun x _ =>
    length_contrList_add_ite_le lists hne x
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at hsum
  simp only [Finset.mem_range, u.2, v.2, ↓reduceIte, ← length_flatUpTo, h1, h2] at hsum
  omega

/-- Contracting an edge `uv` does not increase `instSize`. -/
theorem instSize_contractGraph_le {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) {u v : Fin N} (huv : G.Adj u v) :
    instSize N (contractGraph G u v) ≤ instSize N G := by
  have := ncard_edgeSet_contractGraph_le h huv
  unfold instSize
  omega

/-- Rotating two equal-length lists by `1` rotates their `zip` by `1`. -/
theorem zip_rotate_one {V : Type*} {A B : List V} (h : A.length = B.length) :
    (A.rotate 1).zip (B.rotate 1) = (A.zip B).rotate 1 := by
  cases A with
  | nil =>
    cases B with
    | nil => simp
    | cons _ _ => simp at h
  | cons a A' =>
    cases B with
    | nil => simp at h
    | cons b B' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.rotate_cons_succ, List.rotate_zero, List.rotate_cons_succ, List.rotate_zero,
        List.zip_cons_cons, List.rotate_cons_succ, List.rotate_zero, List.zip_append h]
      simp

/-- Rotating two equal-length lists by `k` rotates their `zip` by `k`. -/
theorem zip_rotate_distrib {V : Type*} {A B : List V} (h : A.length = B.length) (k : ℕ) :
    (A.rotate k).zip (B.rotate k) = (A.zip B).rotate k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← List.rotate_rotate A k 1, ← List.rotate_rotate B k 1,
      zip_rotate_one (by simp [h]), ih, List.rotate_rotate]

/-- `zip` with `rotate 1` commutes with `rotate k`. -/
theorem zip_rotate_one_rotate {V : Type*} (D : List V) (k : ℕ) :
    (D.rotate k).zip ((D.rotate k).rotate 1) = (D.zip (D.rotate 1)).rotate k := by
  rw [List.rotate_rotate, Nat.add_comm, ← List.rotate_rotate,
    zip_rotate_distrib (by simp) k]

/-- `HP25.IsCycleList` is preserved under rotating the cycle. -/
theorem isCycleList_rotate {V : Type*} {G : SimpleGraph V} {D : List V}
    (hD : HP25.IsCycleList G D) (k : ℕ) : HP25.IsCycleList G (D.rotate k) := by
  refine ⟨by simp [hD.1], List.nodup_rotate.mpr hD.2.1, fun p hp => ?_⟩
  rw [zip_rotate_one_rotate, List.mem_rotate] at hp
  exact hD.2.2 p hp

/-- `IsCycleEdge` is invariant under rotating the cycle. -/
theorem isCycleEdge_rotate {V : Type*} {D : List V} {u v : V} (k : ℕ) :
    IsCycleEdge (D.rotate k) u v ↔ IsCycleEdge D u v := by
  simp only [IsCycleEdge, zip_rotate_one_rotate, List.mem_rotate]

/-- Contracting the first vertex `u` of a cycle `u :: L` along a cycle edge incident to `u`
when `4 < (u :: L).length` produces a cycle `L` in `contractGraph K u v`. -/
theorem isCycleList_contractGraph_cons {V : Type*} [DecidableEq V] {K : SimpleGraph V} {u v : V}
    {L : List V} (hD : HP25.IsCycleList K (u :: L)) (hlen : 4 < (u :: L).length)
    (hce : IsCycleEdge (u :: L) u v) :
    HP25.IsCycleList (contractGraph K u v) L := by
  obtain ⟨h3, hnd, hadj⟩ := hD
  rw [List.nodup_cons] at hnd
  obtain ⟨huL, hndL⟩ := hnd
  cases L with
  | nil => simp at hlen
  | cons c t =>
    have ht_ne : t ≠ [] := by
      rintro rfl
      simp at hlen
    obtain ⟨mid, b, rfl⟩ : ∃ mid b, t = mid ++ [b] := by
      obtain ⟨b, mid, h⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr ht_ne)
      exact ⟨mid.reverse, b, by simpa using congrArg List.reverse h⟩
    have hrot1 : (u :: c :: (mid ++ [b])).rotate 1 = (c :: mid) ++ [b, u] := by
      rw [List.rotate_cons_succ, List.rotate_zero]; simp
    have hlen_cm : (c :: mid).length = (mid ++ [b]).length := by simp
    have hzip1 : (u :: c :: (mid ++ [b])).zip ((u :: c :: (mid ++ [b])).rotate 1) =
        (u, c) :: ((c :: mid).zip (mid ++ [b]) ++ [(b, u)]) := by
      rw [hrot1, show u :: c :: (mid ++ [b]) = u :: ((c :: mid) ++ [b]) by simp,
        show (c :: mid) ++ [b, u] = c :: ((mid ++ [b]) ++ [u]) by simp,
        List.zip_cons_cons, List.zip_append hlen_cm]
      simp
    have hrot2 : (c :: (mid ++ [b])).rotate 1 = (mid ++ [b]) ++ [c] := by
      rw [List.rotate_cons_succ, List.rotate_zero]
    have hzip2 : (c :: (mid ++ [b])).zip ((c :: (mid ++ [b])).rotate 1) =
        (c :: mid).zip (mid ++ [b]) ++ [(b, c)] := by
      rw [hrot2, show c :: (mid ++ [b]) = (c :: mid) ++ [b] by simp, List.zip_append hlen_cm]
      simp
    have huc : K.Adj u c := hadj (u, c) (by rw [hzip1]; simp)
    have hbu : K.Adj b u := hadj (b, u) (by rw [hzip1]; simp)
    have hmid_ne_u : ∀ p ∈ (c :: mid).zip (mid ++ [b]), p.1 ≠ u ∧ p.2 ≠ u := by
      intro p hp
      have hp1 : p.1 ∈ c :: (mid ++ [b]) := by
        have := (List.of_mem_zip hp).1
        simp only [List.mem_cons] at this ⊢
        rcases this with rfl | h
        · exact Or.inl rfl
        · exact Or.inr (List.mem_append_left _ h)
      have hp2 : p.2 ∈ c :: (mid ++ [b]) :=
        List.mem_cons_of_mem c (List.of_mem_zip hp).2
      exact ⟨fun h => huL (h ▸ hp1), fun h => huL (h ▸ hp2)⟩
    have hv_cb : v = c ∨ v = b := by
      obtain ⟨p, hp, hpeq⟩ := hce
      rw [hzip1, List.mem_cons, List.mem_append, List.mem_singleton] at hp
      rcases hp with rfl | hp | rfl
      · rcases hpeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact absurd rfl huc.ne
      · obtain ⟨hne1, hne2⟩ := hmid_ne_u p hp
        rcases hpeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd rfl hne1
        · exact absurd rfl hne2
      · rcases hpeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd rfl hbu.ne
        · exact Or.inr rfl
    have hbc_ne : b ≠ c := by
      rw [List.nodup_cons] at hndL
      exact fun h => hndL.1 (by simp [h.symm])
    have hbu_ne : b ≠ u := fun h => huL (by simp [h.symm])
    have hcu_ne : c ≠ u := fun h => huL (by simp [h])
    refine ⟨by simp at hlen ⊢; omega, hndL, fun p hp => ?_⟩
    rw [hzip2, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · obtain ⟨hne1, hne2⟩ := hmid_ne_u p hp
      have hadj_p : K.Adj p.1 p.2 := hadj p (by rw [hzip1]; simp [hp])
      exact ⟨hadj_p.ne, hne1, hne2, Or.inl hadj_p⟩
    · refine ⟨hbc_ne, hbu_ne, hcu_ne, ?_⟩
      rcases hv_cb with rfl | rfl
      · exact Or.inr (Or.inr ⟨rfl, hbu.symm⟩)
      · exact Or.inr (Or.inl ⟨rfl, huc⟩)

/-- Contracting a valid trial edge `uv` when `u ∈ D → 4 < D.length` preserves `HP25.IsCycleList`. -/
theorem isCycleList_contractGraph {V : Type*} [DecidableEq V] {K : SimpleGraph V} {D : List V}
    {u v : V} (hD : HP25.IsCycleList K D) (htrial : IsTrialEdge K D u v)
    (hlong : u ∈ D → 4 < D.length) :
    HP25.IsCycleList (contractGraph K u v) (contractCycle D u) := by
  unfold contractCycle
  split_ifs with huD
  · obtain ⟨D₁, D₂, rfl⟩ := List.mem_iff_append.mp huD
    have hnd := hD.2.1
    rw [List.nodup_append] at hnd
    have hu_not_D₁ : u ∉ D₁ := fun h => hnd.2.2 u h u List.mem_cons_self rfl
    have herase : (D₁ ++ u :: D₂).erase u = D₁ ++ D₂ := by
      rw [List.erase_append_right _ hu_not_D₁, List.erase_cons_head]
    have hrotD : (D₁ ++ u :: D₂).rotate D₁.length = u :: (D₂ ++ D₁) := by
      rw [show D₁ ++ u :: D₂ = D₁ ++ ([u] ++ D₂) by simp, List.rotate_append_length_eq]
      simp
    have hrotL : (D₂ ++ D₁).rotate D₂.length = D₁ ++ D₂ := List.rotate_append_length_eq D₂ D₁
    have hD_rot : HP25.IsCycleList K (u :: (D₂ ++ D₁)) := hrotD ▸ isCycleList_rotate hD D₁.length
    have hlen_rot : 4 < (u :: (D₂ ++ D₁)).length := by
      rw [← hrotD, List.length_rotate]
      exact hlong huD
    have hce : IsCycleEdge (D₁ ++ u :: D₂) u v := by
      rcases htrial.2 with h | h
      · exact absurd huD h
      · exact h
    have hce_rot : IsCycleEdge (u :: (D₂ ++ D₁)) u v :=
      hrotD ▸ (isCycleEdge_rotate D₁.length).mpr hce
    rw [herase, ← hrotL]
    exact isCycleList_rotate (isCycleList_contractGraph_cons hD_rot hlen_rot hce_rot) D₂.length
  · refine ⟨hD.1, hD.2.1, fun p hp => ?_⟩
    have hadj_p := hD.2.2 p hp
    have hp1 : p.1 ∈ D := (List.of_mem_zip hp).1
    have hp2 : p.2 ∈ D := List.mem_rotate.mp (List.of_mem_zip hp).2
    exact ⟨hadj_p.ne, fun h => huD (h ▸ hp1), fun h => huD (h ▸ hp2), Or.inl hadj_p⟩

/-- A valid replacement record preserves `HP25.IsCycleList`. -/
theorem isCycleList_newGraph {V : Type*} {r : ReplRecord V} {D : List V}
    (hD : HP25.IsCycleList r.graph D) (hval : r.IsValid D) :
    HP25.IsCycleList r.newGraph D := by
  refine ⟨hD.1, hD.2.1, fun p hp => ?_⟩
  have hp1 : p.1 ∈ D := (List.of_mem_zip hp).1
  have hp2 : p.2 ∈ D := List.mem_rotate.mp (List.of_mem_zip hp).2
  exact Or.inl ⟨hD.2.2 p hp, fun h => hval.2.1 p.1 h hp1, fun h => hval.2.1 p.2 h hp2⟩

/-- A valid replacement record adds at most `3` edges. -/
theorem ncard_edgeSet_newGraph_le {N : ℕ} {r : ReplRecord (Fin N)} {D : List (Fin N)}
    (hval : r.IsValid D) :
    r.newGraph.edgeSet.ncard ≤ r.graph.edgeSet.ncard + 3 := by
  obtain ⟨-, hdiff, -⟩ := sec4EdgeCount_proved r D hval
  have hsub : r.newGraph.edgeSet ⊆ r.graph.edgeSet ∪ (r.newGraph.edgeSet \ r.graph.edgeSet) :=
    fun e he => by simp [he]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le r.graph.edgeSet (r.newGraph.edgeSet \ r.graph.edgeSet)
  omega

/-- A restoration run whose records are valid produces a valid `IsHistory`, preserves
`HP25.IsCycleList`, shrinks the vertex set (`S' ⊆ S`), and adds at most `3 * rs.length` edges. -/
theorem isHistory_and_bounds_of_isRestoreRun {N : ℕ} [DecidableEq (Fin N)] {D : List (Fin N)}
    {w : Fin N} :
    ∀ (M : List (Fin N)) {H H' : SimpleGraph (Fin N)} {S S' : Set (Fin N)}
      {rs : List (ReplRecord (Fin N))},
      HP25.IsCycleList H D →
      IsRestoreRun D w M H S H' S' rs →
      (∀ r ∈ rs, r.IsValid D) →
      IsHistory (H, S, D) (rs.map CrossRecord.repl) (H', S', D) ∧
        HP25.IsCycleList H' D ∧
        S' ⊆ S ∧
        H'.edgeSet.ncard ≤ H.edgeSet.ncard + 3 * rs.length
  | [], _, _, _, _, _, hD, ⟨rfl, rfl, rfl⟩, _ => ⟨rfl, hD, Set.Subset.rfl, by simp⟩
  | z :: M, H, H', S, S', rs, hD, ⟨H₁, S₁, rec₁, rs', hstep, hrun, hrs⟩, hval => by
    have hval₁ : ∀ r ∈ rec₁.toList, r.IsValid D := fun r hr =>
      hval r (hrs ▸ List.mem_append_left _ hr)
    have hval' : ∀ r ∈ rs', r.IsValid D := fun r hr =>
      hval r (hrs ▸ List.mem_append_right _ hr)
    rcases hstep with ⟨-, rfl, rfl, rfl⟩ | ⟨-, -, -, p, q, -, -, rfl, rfl, rfl⟩
    · simp only [Option.toList_none, List.nil_append] at hrs
      subst hrs
      exact isHistory_and_bounds_of_isRestoreRun M hD hrun hval'
    · simp only [Option.toList_some, List.singleton_append] at hrs
      subst hrs
      set r := restoreRecord H S D w z p q
      have hr_val : r.IsValid D := hval₁ r (by simp)
      have hD₁ : HP25.IsCycleList r.newGraph D := isCycleList_newGraph hD hr_val
      have hedge₁ : r.newGraph.edgeSet.ncard ≤ H.edgeSet.ncard + 3 :=
        ncard_edgeSet_newGraph_le hr_val
      obtain ⟨hhist', hD', hsub', hedge'⟩ := isHistory_and_bounds_of_isRestoreRun M hD₁ hrun hval'
      refine ⟨⟨rfl, rfl, hr_val, hhist'⟩, hD', hsub'.trans Set.sdiff_subset,
        by simp only [List.length_cons]; omega⟩

/-! ### Building the marker list `M` and allocating the trial buffer -/

/-- Build the marker list `M = N_K(u) \ {v}` in `a_mk` from the adjacency list of `u` in `a`:
allocate `a_mk` of length `(a.en[u] - a.st[u]) - 1`, then emit all neighbours of `u` other than
`v`. Uses registers `R + 2, …, R + 6` (`r_cnt`, `r_k`, `r_hi`, `r_y`). -/
def buildMarkersProg (a : InstArrs) (a_mk R : ℕ) : Cmd :=
  let degE : Expr := .op .sub (.read a.en (.reg R)) (.read a.st (.reg R))
  .seq (.alloc a_mk (.op .sub degE (.const 1)))
    (.seq (.assign (R + 2) (.const 0))
      (forList a.st a.en a.ent R (R + 3) (R + 4) (R + 5)
        (.ite (.op .eq (.reg (R + 5)) (.reg (R + 1))) .skip
          (emitProg a_mk (R + 2) (.reg (R + 5))))))

theorem buildMarkersProg_exec {w N : ℕ} (a : InstArrs) (a_mk R : ℕ)
    (hok : ArrsOk (a.list ++ [a_mk]) (a_mk + 1))
    {K : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)} {u v : Fin N} {s : State}
    (hinst : IsInstanceAt a K S D s) (huv : K.Adj u v)
    (hu : s.regs R = u.val) (hv : s.regs (R + 1) = v.val)
    (hw : 4 * instSize N K + 4 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (M : List (Fin N)),
      Exec w (buildMarkersProg a a_mk R) s s' t ∧
      t ≤ 25 * ((K.neighborSet u).ncard + 1) ∧
      M.Nodup ∧ (∀ y : Fin N, y ∈ M ↔ y ∈ markers K u v) ∧
      M.length ≤ (K.neighborSet u).ncard ∧
      s'.arrs a_mk = M.map Fin.val ∧
      (∀ x, x ≠ a_mk → s'.arrs x = s.arrs x) ∧
      (∀ r < R + 2, s'.regs r = s.regs r) := by
  obtain ⟨-, -, ⟨lists, hadj⟩, hent, -⟩ := hinst
  have hnd_arrs := hok.1
  simp only [InstArrs.list, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd_arrs
  obtain ⟨-, ⟨-, -, -, hst_mk⟩, ⟨-, -, hen_mk⟩, ⟨-, hent_mk⟩, -⟩ := hnd_arrs
  have hsz : N + 2 * K.edgeSet.ncard + 2 ≤ 2 * instSize N K := by unfold instSize; omega
  have hw1 : 1 < 2 ^ w := by omega
  have huw : u.val < 2 ^ w := by have := u.2; omega
  have hvw : v.val < 2 ^ w := by have := v.2; omega
  obtain ⟨lu, hlu⟩ : ∃ lu, lists u = lu := ⟨_, rfl⟩
  have hdeg_eq : (K.neighborSet u).ncard = lu.length := by
    rw [ncard_neighborSet_eq_length hadj.2 u, hlu]
  have hlu_nd : lu.Nodup := hlu ▸ (hadj.2 u).2.1
  have hlu_lt : ∀ y ∈ lu, y < N := hlu ▸ (hadj.2 u).1
  have hlu_len : lu.length ≤ N := hlu ▸ (hadj.2 u).2.2.1
  have hv_mem : v.val ∈ lu := by rw [← hlu, (hadj.2 u).2.2.2 v]; exact huv
  have hflen := length_filter_ne_add hlu_nd v.val
  simp only [hv_mem, ↓reduceIte] at hflen
  obtain ⟨st, en, hlist, hen_le⟩ := exists_isListAt hadj u.2
  rw [listOf_fin, hlu] at hlist
  have hlist' := hlist
  obtain ⟨hu_st, hu_en, -, hdiff, hst_eq, hen_eq, -⟩ := hlist'
  have hen_w : en < 2 ^ w := by rw [hent] at hen_le; omega
  have hst_w : st < 2 ^ w := by omega
  have hdegE : (Expr.op .sub (.read a.en (.reg R)) (.read a.st (.reg R))).eval w s =
      some lu.length := by
    have e1 : (Expr.read a.en (.reg R)).eval w s = some en := by
      rw [eval_read (eval_reg hu huw) hu_en (by simp only [hen_eq]; exact hen_w), hen_eq]
    have e2 : (Expr.read a.st (.reg R)).eval w s = some st := by
      rw [eval_read (eval_reg hu huw) hu_st (by simp only [hst_eq]; exact hst_w), hst_eq]
    rw [eval_sub e1 e2, hdiff]
  set mlen := lu.length - 1
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = s.setArr a_mk (List.replicate mlen 0) := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ = s₁.setReg (R + 2) 0 := ⟨_, rfl⟩
  have hex₁ : Exec w (.alloc a_mk
      (.op .sub (.op .sub (.read a.en (.reg R)) (.read a.st (.reg R))) (.const 1))) s s₁
      ((Expr.op .sub (.op .sub (.read a.en (.reg R)) (.read a.st (.reg R))) (.const 1)).cost +
        mlen) := by
    rw [hs₁]
    exact Exec.alloc (a := a_mk) (eval_sub hdegE (eval_const hw1))
  have hex₂ : Exec w (.assign (R + 2) (.const 0)) s₁ s₂ 2 := by
    rw [hs₂]; exact .assign (eval_const (by omega))
  have hlist₂ : IsListAt a.st a.en a.ent u.val st en lu s₂ :=
    hlist.of_arrs_eq (by simp [hs₂, hs₁, hst_mk]) (by simp [hs₂, hs₁, hen_mk])
      (by simp [hs₂, hs₁, hent_mk])
  let Q : ℕ → State → Prop := fun _ s' =>
    (∀ x, x ≠ a_mk → s'.arrs x = s.arrs x) ∧
    (∀ r < R + 2, s'.regs r = s.regs r)
  have hQ₂ : Q 0 s₂ := ⟨fun x hx => by simp [hs₂, hs₁, hx],
    fun r hr => by simp [hs₂, hs₁, show r ≠ R + 2 by omega]⟩
  have hb₂ : IsBuf a_mk (R + 2) [] mlen s₂ := by
    simp [hs₂, hs₁, IsBuf]
  have hflat : lu.flatMap (fun y => if y = v.val then [] else [y]) =
      lu.filter (fun y => y ≠ v.val) := flatMap_filter_ite lu (fun y => y = v.val)
  obtain ⟨s₃, t₃, hex₃, ht₃, hQ₃, hb₃⟩ := forListEmit_exec (w := w) a.st a.en a.ent R
    (R + 3) (R + 4) (R + 5) a_mk (R + 2)
    (.ite (.op .eq (.reg (R + 5)) (.reg (R + 1))) .skip (emitProg a_mk (R + 2) (.reg (R + 5))))
    u.val st en lu (fun y => if y = v.val then [] else [y]) Q 11
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hw1 hen_w huw hlist₂
    (by simp [hs₂, hs₁, hu]) (fun x hx => by have := hlu_lt x hx; omega) hQ₂ hb₂
    (by rw [hflat]; omega)
    (fun j s₀ st₁ hQ harr hreg => ⟨fun x hx => by rw [harr]; exact hQ.1 x hx,
      fun r hr => by rw [hreg r (by omega) (by omega) (by omega)]; exact hQ.2 r hr⟩)
    (fun j st' hQ => by rw [hQ.1 a.ent hent_mk, hQ₂.1 a.ent hent_mk])
    (by
      intro j hj st' pre' k' hQ hk hh hy hbuf hk1 hlen_pre
      have hyw : lu[j] < 2 ^ w := by have := hlu_lt _ (List.getElem_mem hj); omega
      have hv' : st'.regs (R + 1) = v.val := by rw [hQ.2 (R + 1) (by omega), hv]
      by_cases hyv : lu[j] = v.val
      · refine ⟨st', _, exec_ite_eq_true (w := w) hy (hv'.trans hyv.symm) hyw hw1 (.skip _),
          by simp, hQ, hk, hh, by simpa [hyv] using hbuf⟩
      · simp only [hyv, ↓reduceIte, List.length_singleton] at hk1 ⊢
        simp only [List.length_nil, Nat.zero_add] at hlen_pre
        obtain ⟨s'', hex, hb'', hA'', hR''⟩ := emitReg_exec (w := w) a_mk (R + 2) (R + 5)
          (k := k' - 1) (by rw [show k' - 1 + 1 = k' by omega]; exact hbuf) hy hyw (by omega)
        refine ⟨s'', _, exec_ite_eq_false (w := w) hy hv' hyv hyw hvw hw1 hex, by simp,
          ⟨fun x hx => by rw [hA'' x hx]; exact hQ.1 x hx,
            fun r hr => by rw [hR'' r (by omega)]; exact hQ.2 r hr⟩,
          by rw [hR'' _ (by omega)]; exact hk, by rw [hR'' _ (by omega)]; exact hh, hb''⟩)
  rw [hflat, show mlen - (lu.filter (fun y => y ≠ v.val)).length = 0 by omega] at hb₃
  simp only [List.nil_append] at hb₃
  obtain ⟨M, hM⟩ := exists_fin_list (lu.filter (fun y => y ≠ v.val))
    (fun y hy => hlu_lt y (List.mem_of_mem_filter hy))
  have hM_nd : M.Nodup := List.Nodup.of_map Fin.val (hM ▸ hlu_nd.filter _)
  have hM_mem : ∀ y : Fin N, y ∈ M ↔ y ∈ markers K u v := by
    intro y
    rw [← List.mem_map_of_injective Fin.val_injective, hM, List.mem_filter,
      decide_eq_true_eq, ← hlu, (hadj.2 u).2.2.2 y, markers, Set.mem_ofPred_eq, ne_eq, ← Fin.ext_iff]
  have hM_len : M.length ≤ (K.neighborSet u).ncard := by
    rw [← List.length_map (f := Fin.val), hM, hdeg_eq]
    exact List.length_filter_le _ _
  refine ⟨s₃, _, M, .seq hex₁ (.seq hex₂ hex₃), ?_, hM_nd, hM_mem, hM_len,
    by rw [hb₃.1, List.replicate_zero, List.append_nil, hM], hQ₃.1, hQ₃.2⟩
  dsimp [Expr.cost]
  rw [hdeg_eq]
  omega

/-- Allocate the trial record buffer `a_trec` with capacity
`C_buf * (len(a_mk) + 1) * (len(a.alive) + len(a.ent) + 1)` and set `r_trec := 0`. -/
def allocTrialBufProg (a : InstArrs) (a_mk a_trec r_trec C_buf : ℕ) : Cmd :=
  let szE : Expr := .op .add (.op .add (.len a.alive) (.len a.ent)) (.const 1)
  let mkE : Expr := .op .add (.len a_mk) (.const 1)
  .seq (.alloc a_trec (.op .mul (.const C_buf) (.op .mul mkE szE)))
    (.assign r_trec (.const 0))

theorem allocTrialBufProg_exec {w N : ℕ} (a : InstArrs) (a_mk a_trec r_trec C_buf : ℕ)
    {K : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D M : List (Fin N)} {s : State}
    (hinst : IsInstanceAt a K S D s) (hmk : s.arrs a_mk = M.map Fin.val)
    (hw : (2 * C_buf + 4) * ((M.length + 1) * instSize N K) < 2 ^ w) :
    ∃ (s' : State) (t k₀ : ℕ),
      Exec w (allocTrialBufProg a a_mk a_trec r_trec C_buf) s s' t ∧
      t ≤ (2 * C_buf + 20) * ((M.length + 1) * instSize N K) ∧
      C_buf * (M.length + 1) * instSize N K ≤ k₀ ∧
      k₀ ≤ 2 * C_buf * ((M.length + 1) * instSize N K) ∧
      IsRecBufAt a_trec r_trec ([] : List (CrossRecord (Fin N))) k₀ s' ∧
      (s'.arrs a_trec).length = k₀ ∧
      (∀ x, x ≠ a_trec → s'.arrs x = s.arrs x) ∧
      (∀ r, r ≠ r_trec → s'.regs r = s.regs r) := by
  obtain ⟨-, halive, -, hent, -⟩ := hinst
  have hal_len : (s.arrs a.alive).length = N := by rw [halive]; simp
  have hmk_len : (s.arrs a_mk).length = M.length := by rw [hmk]; simp
  have hsz_def : instSize N K = N + K.edgeSet.ncard + 1 := rfl
  set sz := N + 2 * K.edgeSet.ncard + 1
  have hsz_lo : instSize N K ≤ sz := by omega
  have hsz_hi : sz ≤ 2 * instSize N K := by omega
  have hpos : 1 ≤ (M.length + 1) * instSize N K :=
    Nat.mul_pos (Nat.succ_pos _) (by omega)
  have hw4 : 4 * ((M.length + 1) * instSize N K) < 2 ^ w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hw
  set k₀ := C_buf * ((M.length + 1) * sz)
  have hk₀_lo : C_buf * (M.length + 1) * instSize N K ≤ k₀ := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left C_buf (Nat.mul_le_mul_left (M.length + 1) hsz_lo)
  have hk₀_hi : k₀ ≤ 2 * C_buf * ((M.length + 1) * instSize N K) := by
    calc C_buf * ((M.length + 1) * sz)
        ≤ C_buf * ((M.length + 1) * (2 * instSize N K)) :=
          Nat.mul_le_mul_left C_buf (Nat.mul_le_mul_left (M.length + 1) hsz_hi)
      _ = 2 * C_buf * ((M.length + 1) * instSize N K) := by ring
  have hsz_le : (M.length + 1) * sz ≤ 2 * ((M.length + 1) * instSize N K) := by
    calc (M.length + 1) * sz ≤ (M.length + 1) * (2 * instSize N K) :=
          Nat.mul_le_mul_left _ hsz_hi
      _ = 2 * ((M.length + 1) * instSize N K) := by ring
  have hsz_le_prod : sz ≤ 2 * ((M.length + 1) * instSize N K) := by
    have : instSize N K ≤ (M.length + 1) * instSize N K :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hM_le_prod : M.length + 1 ≤ (M.length + 1) * instSize N K :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hw1 : 1 < 2 ^ w := by omega
  have hsz_ev : (Expr.op .add (.op .add (.len a.alive) (.len a.ent)) (.const 1)).eval w s =
      some sz := by
    have e1 := eval_len (w := w) (s := s) (a := a.alive) halive (by simp; omega)
    have e2 := eval_len (w := w) (s := s) (a := a.ent) rfl (by rw [hent]; omega)
    simp only [List.length_ofFn] at e1
    rw [hent] at e2
    exact eval_add (eval_add e1 e2 (by omega)) (eval_const hw1) (by omega)
  have hmk_ev : (Expr.op .add (.len a_mk) (.const 1)).eval w s = some (M.length + 1) := by
    have e1 := eval_len (w := w) (s := s) (a := a_mk) hmk (by simp; omega)
    simp only [List.length_map] at e1
    exact eval_add e1 (eval_const hw1) (by omega)
  have hk₀_ev : (Expr.op .mul (.const C_buf)
      (.op .mul (.op .add (.len a_mk) (.const 1))
        (.op .add (.op .add (.len a.alive) (.len a.ent)) (.const 1)))).eval w s = some k₀ := by
    have hC_w : C_buf < 2 ^ w := by
      have h1 : C_buf ≤ C_buf * ((M.length + 1) * instSize N K) :=
        Nat.le_mul_of_pos_right _ hpos
      have h2 : C_buf * ((M.length + 1) * instSize N K) ≤
          (2 * C_buf + 4) * ((M.length + 1) * instSize N K) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hk₀_w : k₀ < 2 ^ w := by
      have : 2 * C_buf * ((M.length + 1) * instSize N K) ≤
          (2 * C_buf + 4) * ((M.length + 1) * instSize N K) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    exact eval_mul (eval_const hC_w) (eval_mul hmk_ev hsz_ev (by omega)) hk₀_w
  set s₁ := s.setArr a_trec (List.replicate k₀ 0)
  set s₂ := s₁.setReg r_trec 0
  have hex₁ : Exec w (.alloc a_trec (.op .mul (.const C_buf)
      (.op .mul (.op .add (.len a_mk) (.const 1))
        (.op .add (.op .add (.len a.alive) (.len a.ent)) (.const 1))))) s s₁
      ((Expr.op .mul (.const C_buf)
        (.op .mul (.op .add (.len a_mk) (.const 1))
          (.op .add (.op .add (.len a.alive) (.len a.ent)) (.const 1)))).cost + k₀) :=
    Exec.alloc (a := a_trec) hk₀_ev
  have hex₂ : Exec w (.assign r_trec (.const 0)) s₁ s₂ 2 := .assign (eval_const (by omega))
  have ht_bound : (Expr.op .mul (.const C_buf)
      (.op .mul (.op .add (.len a_mk) (.const 1))
        (.op .add (.op .add (.len a.alive) (.len a.ent)) (.const 1)))).cost + k₀ + 2 ≤
      (2 * C_buf + 20) * ((M.length + 1) * instSize N K) := by
    dsimp [Expr.cost]
    have : (2 * C_buf + 20) * ((M.length + 1) * instSize N K) =
        2 * C_buf * ((M.length + 1) * instSize N K) +
          20 * ((M.length + 1) * instSize N K) := by ring
    omega
  refine ⟨s₂, _, k₀, .seq hex₁ hex₂, ht_bound, hk₀_lo, hk₀_hi,
    ⟨[], .nil, by simp [s₂, s₁], by simp [s₂]⟩, by simp [s₂, s₁],
    fun x hx => by simp [s₂, s₁, hx], fun r hr => by simp [s₂, s₁, hr]⟩

/-! ### The full trial program -/

/-- `wordSize` under a linear scaling `M ≤ K * (n + 1)` of its argument. -/
theorem wordSize_le_of_le_mul' {c K M n : ℕ} (hM : M ≤ K * (n + 1)) :
    wordSize c M ≤ wordSize (c * (K + 3)) n := by
  have h1 : wordSize c M ≤ wordSize c (K * (n + 1)) := wordSize_mono_right c hM
  have hpow_K : K + 2 ≤ 2 ^ (K + 2) := Nat.le_of_lt Nat.lt_two_pow_self
  have h2 : K * (n + 1) + 2 ≤ (n + 2) * (K + 2) := by nlinarith
  have h3 : K * (n + 1) + 2 ≤ (n + 2) * 2 ^ (K + 2) :=
    le_trans h2 (Nat.mul_le_mul_left (n + 2) hpow_K)
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have h4 : (n + 2) * 2 ^ (K + 2) < 2 ^ (Nat.log 2 (n + 2) + 1 + (K + 2)) := by
    calc (n + 2) * 2 ^ (K + 2) < 2 ^ (Nat.log 2 (n + 2) + 1) * 2 ^ (K + 2) :=
          Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
      _ = 2 ^ (Nat.log 2 (n + 2) + 1 + (K + 2)) := (Nat.pow_add 2 _ (K + 2)).symm
  have hlog : Nat.log 2 (K * (n + 1) + 2) < Nat.log 2 (n + 2) + 1 + (K + 2) :=
    Nat.log_lt_of_lt_pow (by omega) (Nat.lt_of_le_of_lt h3 h4)
  have hlog_le : Nat.log 2 (K * (n + 1) + 2) + 1 ≤ (K + 3) * (Nat.log 2 (n + 2) + 1) := by
    nlinarith
  dsimp [wordSize] at h1 ⊢
  calc c * (Nat.log 2 (M + 2) + 1) ≤ c * (Nat.log 2 (K * (n + 1) + 2) + 1) := h1
    _ ≤ c * ((K + 3) * (Nat.log 2 (n + 2) + 1)) := Nat.mul_le_mul_left c hlog_le
    _ = c * (K + 3) * (Nat.log 2 (n + 2) + 1) := by ring

/-- `wordSize` under a linear scaling `M ≤ K * n` of its argument. -/
theorem wordSize_le_of_le_mul_self {c K M n : ℕ} (hM : M ≤ K * n) :
    wordSize c M ≤ wordSize (c * (K + 3)) n :=
  wordSize_le_of_le_mul' (hM.trans (Nat.mul_le_mul_left K (Nat.le_succ n)))

/-- A number at most `K * (n + 1)` is a word when `w` is at least `wordSize (K + 3) n`. -/
theorem lt_two_pow_of_le_mul {K n V w : ℕ} (hV : V ≤ K * (n + 1))
    (hw : wordSize (K + 3) n ≤ w) : V < 2 ^ w := by
  have h1 : V < 2 ^ wordSize 1 V := lt_two_pow_wordSize_of_le le_rfl (by omega)
  have h2 : wordSize 1 V ≤ wordSize (1 * (K + 3)) n := wordSize_le_of_le_mul' hV
  rw [Nat.one_mul] at h2
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (h2.trans hw))

/-- **One trial with full guarantees** (Section 10, step 4): `TrialRecProgClaim` together with
the three properties of a trial that `LoopRecProgClaim` uses:
* `S' ⊆ S.erase u` (so `S'.card < S.card` since `u ∈ S`);
* restoration preserves crossing existence (`HP25.IsCrossed (contractGraph K u v) (contractCycle D u) ↔ HP25.IsCrossed H (contractCycle D u)`, from Lemma 7);
* `(s'.arrs a_trec).length ≤ C * ((K.neighborSet u).ncard + 1) * instSize N K` (so appending the
  trial's records into `a_rec` fits in the buffer and runs in linear time). -/
def TrialRecFullProgClaim : Prop :=
  ∀ (prog : Cmd) (Cp cp_w : ℕ), IsPlanarityProg prog Cp cp_w →
  ∀ (a b : InstArrs) (a_trec r_trec a_Q a_R a_base r_base : ℕ),
    ArrsOk (a.list ++ b.list ++ [a_trec, a_Q, a_R]) a_base → r_trec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (K : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (u v : Fin N) (s : State),
      wordSize c ((N + 1) * instSize N K) ≤ w → IsInstanceAt a K S D s →
      HP25.IsCycleList K D → IsClean K (S : Set (Fin N)) D → IsTrialEdge K D u v →
      (u ∈ D → 4 < D.length) → s.regs r_base = u.val → s.regs (r_base + 1) = v.val →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * ((K.neighborSet u).ncard + 1) * instSize N K ∧
        KeepsBelow r_base a_base [r_trec] (b.list ++ [a_trec, a_Q, a_R]) s s' ∧
        ∃ (H : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (recs : List (CrossRecord (Fin N)))
          (k' : ℕ),
          IsInstanceAt b H S' (contractCycle D u) s' ∧
          IsHistoryFin K S D recs H S' (contractCycle D u) ∧ ContractionsLong recs ∧
          IsRecBufAt a_trec r_trec recs k' s' ∧ IsClean H (S' : Set (Fin N)) (contractCycle D u) ∧
          S' ⊆ S.erase u ∧
          (HP25.IsCrossed (contractGraph K u v) (contractCycle D u) ↔
            HP25.IsCrossed H (contractCycle D u)) ∧
          (s'.arrs a_trec).length ≤ C * ((K.neighborSet u).ncard + 1) * instSize N K ∧
          H.edgeSet.ncard ≤ K.edgeSet.ncard + 3 * (K.neighborSet u).ncard ∧
          ((s'.regs r_base = 2 ∧ IsCrossingPairAt H (contractCycle D u) a_Q a_R s') ∨
            (s'.regs r_base = 0 ∧ Nonempty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂) ∨
            (s'.regs r_base = 1 ∧ IsEmpty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂))

set_option maxHeartbeats 1000000 in
/-- **One trial with full guarantees** (Section 10, step 4) from `RestoreRecNeProgClaim` and
`ClassifyProgClaim`. -/
theorem trialRecFullProgClaim_of :
    TrialRecFullProgClaim := by
  intro prog Cp cp_w hprog a b a_trec r_trec a_Q a_R A R hok hrt
  let a_mk := A
  have hok_all : ArrsOk ((a.list ++ b.list ++ [a_trec, a_Q, a_R]) ++ [a_mk]) (A + 1) := by
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hok.1, List.nodup_singleton a_mk, fun x hx y hy e => ?_⟩
      simp only [List.mem_singleton] at hy
      rw [e, hy] at hx
      exact Nat.lt_irrefl A (hok.2 a_mk hx)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have := hok.2 x hx; omega
      · simp only [List.mem_singleton] at hx; omega
  have hsub_ab : List.Sublist (a.list ++ b.list)
      ((a.list ++ b.list ++ [a_trec, a_Q, a_R]) ++ [a_mk]) :=
    (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)
  have hsub_amk : List.Sublist (a.list ++ [a_mk])
      ((a.list ++ b.list ++ [a_trec, a_Q, a_R]) ++ [a_mk]) := by
    rw [List.append_assoc, List.append_assoc]
    exact List.Sublist.append (List.Sublist.refl a.list)
      (List.sublist_append_right (b.list ++ [a_trec, a_Q, a_R]) [a_mk])
  have hsub_ct : List.Sublist (b.list ++ [a_trec])
      ((a.list ++ b.list ++ [a_trec, a_Q, a_R]) ++ [a_mk]) := by
    have h1 : List.Sublist (b.list ++ [a_trec]) (b.list ++ [a_trec, a_Q, a_R]) :=
      List.Sublist.append (List.Sublist.refl b.list) (by simp)
    have h2 : List.Sublist (b.list ++ [a_trec]) (a.list ++ (b.list ++ [a_trec, a_Q, a_R])) :=
      (h1.trans (List.sublist_append_right a.list _))
    rw [← List.append_assoc] at h2
    exact h2.trans (List.sublist_append_left _ [a_mk])
  have hsub_cl : List.Sublist (b.list ++ [a_Q, a_R])
      ((a.list ++ b.list ++ [a_trec, a_Q, a_R]) ++ [a_mk]) := by
    have h1 : List.Sublist (b.list ++ [a_Q, a_R]) (b.list ++ [a_trec, a_Q, a_R]) :=
      List.Sublist.append (List.Sublist.refl b.list) (by simp)
    have h2 : List.Sublist (b.list ++ [a_Q, a_R]) (a.list ++ (b.list ++ [a_trec, a_Q, a_R])) :=
      h1.trans (List.sublist_append_right a.list _)
    rw [← List.append_assoc] at h2
    exact h2.trans (List.sublist_append_left _ [a_mk])
  have hok_ab : ArrsOk (a.list ++ b.list) (A + 1) :=
    ⟨hok_all.1.sublist hsub_ab, fun x hx => hok_all.2 x (hsub_ab.subset hx)⟩
  have hok_amk : ArrsOk (a.list ++ [a_mk]) (A + 1) :=
    ⟨hok_all.1.sublist hsub_amk, fun x hx => hok_all.2 x (hsub_amk.subset hx)⟩
  have hok_ct : ArrsOk (b.list ++ [a_trec]) (A + 1) :=
    ⟨hok_all.1.sublist hsub_ct, fun x hx => hok_all.2 x (hsub_ct.subset hx)⟩
  have hok_rs : ArrsOk (b.list ++ [a_mk, a_trec]) (A + 1) := by
    refine ⟨?_, fun x hx => ?_⟩
    · have hperm : List.Perm (b.list ++ [a_mk, a_trec]) ((b.list ++ [a_trec]) ++ [a_mk]) := by
        rw [List.append_assoc]
        exact List.Perm.append_left b.list (List.Perm.swap a_trec a_mk [])
      rw [hperm.nodup_iff, List.nodup_append]
      refine ⟨hok_ct.1, List.nodup_singleton a_mk, fun x hx y hy e => ?_⟩
      simp only [List.mem_singleton] at hy
      rw [e, hy] at hx
      have hxA : a_mk < A := by
        rcases List.mem_append.mp hx with h | h
        · exact hok.2 a_mk (List.mem_append_left _ (List.mem_append_right _ h))
        · simp only [List.mem_singleton] at h
          exact h ▸ hok.2 a_trec (by simp)
      exact Nat.lt_irrefl A hxA
    · rcases List.mem_append.mp hx with h | h
      · exact hok_all.2 x (hsub_ct.subset (List.mem_append_left _ h))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · omega
        · exact hok_all.2 x (hsub_ct.subset (by simp))
  have hok_cl : ArrsOk (b.list ++ [a_Q, a_R]) (A + 1) :=
    ⟨hok_all.1.sublist hsub_cl, fun x hx => hok_all.2 x (hsub_cl.subset hx)⟩
  obtain ⟨P_cp, C_cp, c_cp, hP_cp⟩ :=
    copyInstanceRecProgClaim_proved a b (A + 1) (R + 2) hok_ab
  obtain ⟨P_ct, C_ct, c_ct, hP_ct⟩ :=
    contractRecProgClaim_proved b a_trec r_trec (A + 1) (R + 2) hok_ct (by omega)
  obtain ⟨P_rs, C_rs, c_rs, hP_rs⟩ :=
    restoreRecNeProgClaim_of b a_mk a_trec r_trec (A + 1) (R + 1) hok_rs (by omega)
  obtain ⟨P_cl, C_cl, c_cl, hP_cl⟩ :=
    classifyProgClaim_proved prog Cp cp_w hprog b a_Q a_R (A + 1) R hok_cl
  set C_buf := C_ct + C_rs + 1
  set P_all : Cmd :=
    .seq P_cp
      (.seq (buildMarkersProg a a_mk R)
        (.seq (allocTrialBufProg a a_mk a_trec r_trec C_buf)
          (.seq (.assign (R + 2) (.reg R))
            (.seq (.assign (R + 3) (.reg (R + 1)))
              (.seq P_ct (.seq P_rs P_cl))))))
  set c_max :=
    c_cp + c_ct * (2 * C_buf + 1 + 3) + c_rs * (2 * C_buf + 1 + 3) + c_cl * (4 + 3) +
      2 * C_buf + 20
  refine ⟨P_all, C_cp + 25 + (2 * C_buf + 20) + C_ct + C_rs + 4 * C_cl + 10, c_max, ?_⟩
  intro w N inst K S D u v s hw hinst hcyc hclean htrial hlong hu hv
  obtain rfl : inst = instDecidableEqFin N := Subsingleton.elim _ _
  -- Disjointness facts from `hok`
  have hnd := hok.1
  have ha_not_b : ∀ x ∈ a.list, x ∉ b.list := by
    intro x hx hxb
    have hnd_ab := hnd.sublist ((List.sublist_append_left _ _))
    rw [List.nodup_append] at hnd_ab
    exact hnd_ab.2.2 x hx x hxb rfl
  have ha_ne_trec : ∀ x ∈ a.list, x ≠ a_trec := by
    intro x hx rfl
    rw [List.nodup_append] at hnd
    exact hnd.2.2 x (List.mem_append_left _ hx) x (by simp) rfl
  have hb_ne_trec : ∀ x ∈ b.list, x ≠ a_trec := by
    intro x hx rfl
    rw [List.nodup_append] at hnd
    exact hnd.2.2 x (List.mem_append_right _ hx) x (by simp) rfl
  have hb_ne_mk : ∀ x ∈ b.list, x ≠ a_mk := by
    intro x hx rfl
    have := hok.2 x (List.mem_append_left _ (List.mem_append_right _ hx))
    omega
  have htrec_ne_mk : a_trec ≠ a_mk := by
    intro e
    have := hok.2 a_trec (by simp)
    omega
  have htrec_not_QR : a_trec ∉ [a_Q, a_R] := by
    have hnd_tail := hnd.sublist (List.sublist_append_right _ _)
    simp only [List.nodup_cons] at hnd_tail
    exact hnd_tail.1
  have hb_not_QR : ∀ x ∈ b.list, x ∉ [a_Q, a_R] := by
    intro x hxb hxQR
    rw [List.nodup_append] at hnd
    exact hnd.2.2 x (List.mem_append_right _ hxb) x (List.mem_cons_of_mem a_trec hxQR) rfl
  -- Word size bounds
  have hsz_pos : 1 ≤ instSize N K := by unfold instSize; omega
  have hN_le_sz : N + 1 ≤ instSize N K := by unfold instSize; omega
  have hw4 : 4 * instSize N K + 4 < 2 ^ w := by
    apply lt_two_pow_of_le_mul (K := 4) (n := (N + 1) * instSize N K)
    · have : instSize N K ≤ (N + 1) * instSize N K := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · exact (wordSize_mono_left (by omega) _).trans hw
  have huw : u.val < 2 ^ w := by have := u.2; omega
  have hvw : v.val < 2 ^ w := by have := v.2; omega
  -- Step 1: Copy `a` to `b`
  have hw_cp : wordSize c_cp (instSize N K) ≤ w :=
    (wordSize_mono_right _ (Nat.le_mul_of_pos_left _ (by omega))).trans
      ((wordSize_mono_left (by omega) _).trans hw)
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hinst_b₁⟩ := hP_cp w N K S D s hw_cp hinst hcyc
  have hinst_a₁ : IsInstanceAt a K S D s₁ :=
    hinst.of_arrs_eq fun x hx =>
      hk₁.2 x ((hok.2 x (List.mem_append_left _ (List.mem_append_left _ hx))).le.trans_lt
        (Nat.lt_succ_self A)) (ha_not_b x hx)
  have hu₁ : s₁.regs R = u.val := by
    rw [hk₁.1 R (by omega) (by simp)]; exact hu
  have hv₁ : s₁.regs (R + 1) = v.val := by
    rw [hk₁.1 (R + 1) (by omega) (by simp)]; exact hv
  -- Step 2: Build markers `M` in `a_mk`
  obtain ⟨s₂, t₂, M, hex₂, ht₂, hM_nd, hM_mem, hM_len, hmk₂, harr₂, hreg₂⟩ :=
    buildMarkersProg_exec a a_mk R hok_amk hinst_a₁ htrial.1 hu₁ hv₁ hw4
  have hinst_a₂ : IsInstanceAt a K S D s₂ :=
    hinst_a₁.of_arrs_eq fun x hx => harr₂ x fun e => by
      have := hok.2 x (List.mem_append_left _ (List.mem_append_left _ hx))
      omega
  have hinst_b₂ : IsInstanceAt b K S D s₂ :=
    hinst_b₁.of_arrs_eq fun x hx => harr₂ x (hb_ne_mk x hx)
  have hu₂ : s₂.regs R = u.val := by rw [hreg₂ R (by omega)]; exact hu₁
  have hv₂ : s₂.regs (R + 1) = v.val := by rw [hreg₂ (R + 1) (by omega)]; exact hv₁
  have hM_N : M.length ≤ N := by
    have : (K.neighborSet u).ncard ≤ N := by
      have := Set.ncard_le_ncard (Set.subset_univ (K.neighborSet u)) (Set.toFinite _)
      simpa using this
    omega
  -- Step 3: Allocate `a_trec` and `r_trec`
  have hw_alloc : (2 * C_buf + 4) * ((M.length + 1) * instSize N K) < 2 ^ w := by
    apply lt_two_pow_of_le_mul (K := 2 * C_buf + 4) (n := (N + 1) * instSize N K)
    · have h1 : (M.length + 1) * instSize N K ≤ (N + 1) * instSize N K + 1 :=
        (Nat.mul_le_mul_right _ (by omega)).trans (Nat.le_succ _)
      exact Nat.mul_le_mul_left _ h1
    · exact (wordSize_mono_left (by omega) _).trans hw
  obtain ⟨s₃, t₃, k₀, hex₃, ht₃, hk₀_lo, hk₀_hi, hbuf₃, hlen_trec₃, harr₃, hreg₃⟩ :=
    allocTrialBufProg_exec a a_mk a_trec r_trec C_buf hinst_a₂ hmk₂ hw_alloc
  have hinst_b₃ : IsInstanceAt b K S D s₃ :=
    hinst_b₂.of_arrs_eq fun x hx => harr₃ x (hb_ne_trec x hx)
  have hmk₃ : s₃.arrs a_mk = M.map Fin.val := by
    rw [harr₃ a_mk htrec_ne_mk.symm, hmk₂]
  have hu₃ : s₃.regs R = u.val := by rw [hreg₃ R (by omega)]; exact hu₂
  have hv₃ : s₃.regs (R + 1) = v.val := by rw [hreg₃ (R + 1) (by omega)]; exact hv₂
  -- Step 3b: Copy `u` to `R + 2` and `v` to `R + 3`
  set s₃a := s₃.setReg (R + 2) u.val
  set s₃b := s₃a.setReg (R + 3) v.val
  have hex₃a : Exec w (.assign (R + 2) (.reg R)) s₃ s₃a 2 :=
    .assign (eval_reg hu₃ huw)
  have hex₃b : Exec w (.assign (R + 3) (.reg (R + 1))) s₃a s₃b 2 :=
    .assign (eval_reg (by simp [s₃a, hv₃]) hvw)
  have hinst_b₃b : IsInstanceAt b K S D s₃b := hinst_b₃.of_arrs_eq fun _ _ => rfl
  have hbuf₃b : IsRecBufAt a_trec r_trec ([] : List (CrossRecord (Fin N))) k₀ s₃b := by
    obtain ⟨ls, hls, he, hr⟩ := hbuf₃
    exact ⟨ls, hls, he, by simp [s₃b, s₃a, show r_trec ≠ R + 3 by omega,
      show r_trec ≠ R + 2 by omega, hr]⟩
  -- Step 4: Contract `uv` on `b`
  have hM_mul_N : (M.length + 1) * instSize N K ≤ (N + 1) * instSize N K :=
    Nat.mul_le_mul_right _ (by omega)
  have hk₀_N' : k₀ ≤ 2 * C_buf * ((N + 1) * instSize N K) :=
    hk₀_hi.trans (Nat.mul_le_mul_left _ hM_mul_N)
  have hk₀_N : instSize N K + k₀ ≤ (2 * C_buf + 1) * ((N + 1) * instSize N K) := by
    have h2 : instSize N K ≤ (N + 1) * instSize N K := Nat.le_mul_of_pos_left _ (by omega)
    rw [Nat.succ_mul]
    omega
  have hw_ct : wordSize c_ct (instSize N K + (s₃b.arrs a_trec).length) ≤ w := by
    change wordSize c_ct (instSize N K + (s₃.arrs a_trec).length) ≤ w
    rw [hlen_trec₃]
    exact (wordSize_le_of_le_mul_self (K := 2 * C_buf + 1) hk₀_N).trans
      ((wordSize_mono_left (by omega) _).trans hw)
  have hk₀_ct : C_ct * instSize N K ≤ k₀ := by
    have : C_ct * instSize N K ≤ C_buf * (M.length + 1) * instSize N K := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))
    omega
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hinst_b₄, k₁, hbuf₄, hlen_trec₄, hk₁_lo⟩ :=
    hP_ct w N K S D u v [] k₀ s₃b hw_ct hinst_b₃b hcyc htrial
      (by simp [s₃b, s₃a]) (by simp [s₃b]) hbuf₃b hk₀_ct
  set H₁ := contractGraph K u v
  set S₁ := S.erase u
  set D' := contractCycle D u
  set c_rec : ContractRecord (Fin N) :=
    { graph := K, verts := (S : Set (Fin N)), cycle := D, u := u, v := v }
  have hmk₄ : s₄.arrs a_mk = M.map Fin.val := by
    rw [hk₄.2 a_mk (by omega) (by
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨fun h => hb_ne_mk a_mk h rfl, htrec_ne_mk.symm⟩)]
    exact hmk₃
  have hv₄ : s₄.regs (R + 1) = v.val := by
    rw [hk₄.1 (R + 1) (by omega) (by simp [show R + 1 ≠ r_trec by omega])]
    simp [s₃b, s₃a, hv₃]
  -- Step 5: Restore `b` with `M`
  obtain ⟨lists_K, hadj_K⟩ := hinst.2.2.1
  have hsz_H₁ : instSize N H₁ ≤ instSize N K := instSize_contractGraph_le hadj_K.2 htrial.1
  have hcyc_H₁ : HP25.IsCycleList H₁ D' := isCycleList_contractGraph hcyc htrial hlong
  have hv_S₁ : v ∈ S₁ :=
    Finset.mem_erase.mpr ⟨htrial.1.ne.symm, hinst.1 htrial.1.symm⟩
  obtain ⟨hR3, -, hR2, -⟩ :=
    sec91_proved K (S : Set (Fin N)) D u v (Set.toFinite _) hinst.1 hcyc hclean htrial
  have hS₁_coe : ((S₁ : Finset (Fin N)) : Set (Fin N)) = (S : Set (Fin N)) \ {u} := by
    simp [S₁]
  have hR3' : RootedConn (apex H₁ D') (apexVerts (S₁ : Set (Fin N))) none 3 := by
    rwa [hS₁_coe]
  have hR2' : RootedConn (apex H₁ D') (restoreVerts (S₁ : Set (Fin N)) v) none 2 := by
    rwa [restoreVerts, hS₁_coe]
  have hk₁_rs : C_rs * (M.length + 1) * instSize N H₁ ≤ k₁ := by
    have h1 : C_rs * (M.length + 1) * instSize N H₁ ≤
        C_rs * ((M.length + 1) * instSize N K) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hsz_H₁
    have h2 : C_ct * instSize N K ≤ C_ct * ((M.length + 1) * instSize N K) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    have h3 : C_ct * ((M.length + 1) * instSize N K) +
        C_rs * ((M.length + 1) * instSize N K) ≤ k₀ := by
      calc C_ct * ((M.length + 1) * instSize N K) +
            C_rs * ((M.length + 1) * instSize N K)
        _ = (C_ct + C_rs) * ((M.length + 1) * instSize N K) := (Nat.add_mul _ _ _).symm
        _ ≤ C_buf * ((M.length + 1) * instSize N K) := Nat.mul_le_mul_right _ (by omega)
        _ = C_buf * (M.length + 1) * instSize N K := (Nat.mul_assoc _ _ _).symm
        _ ≤ k₀ := hk₀_lo
    omega
  have hw_rs : wordSize c_rs ((M.length + 1) * instSize N H₁ + (s₄.arrs a_trec).length) ≤ w := by
    have hlen4 : (s₄.arrs a_trec).length = k₀ := hlen_trec₄.trans hlen_trec₃
    rw [hlen4]
    have hle : (M.length + 1) * instSize N H₁ + k₀ ≤
        (2 * C_buf + 1) * ((N + 1) * instSize N K) := by
      have h1 : (M.length + 1) * instSize N H₁ ≤ (M.length + 1) * instSize N K :=
        Nat.mul_le_mul_left _ hsz_H₁
      rw [Nat.succ_mul (2 * C_buf)]
      omega
    exact (wordSize_le_of_le_mul_self (K := 2 * C_buf + 1) hle).trans
      ((wordSize_mono_left (by omega) _).trans hw)
  have hv_not_M : v ∉ M := by
    rw [hM_mem v]
    simp [markers]
  obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, H, S', rs, k₂, hrun, hinst_b₅, hbuf₅, hlen_trec₅, -⟩ :=
    hP_rs w N H₁ S₁ D' v M [CrossRecord.contr c_rec] k₁ s₄ hw_rs hinst_b₄ hcyc_H₁ hv_S₁ hv_not_M
      hR3' hR2' hv₄ hmk₄ (by simpa using hbuf₄) hk₁_rs
  -- Step 6: Mathematical properties from Lemma 7 and restoration run
  have hrun_diff : IsRestoreRun D' v M H₁ ((S : Set (Fin N)) \ {u}) H (S' : Set (Fin N)) rs := by
    rwa [← hS₁_coe]
  obtain ⟨-, hlem7⟩ :=
    lemma7_proved K (S : Set (Fin N)) D u v M (Set.toFinite _) hinst.1 hcyc hclean htrial hlong
      hM_nd hM_mem
  obtain ⟨hclean_H, hcrossed_iff, hval_rs, hlen_rs⟩ := hlem7 H (S' : Set (Fin N)) rs hrun_diff
  obtain ⟨hhist_rs, hcyc_H, hsub_S', hedge_H⟩ :=
    isHistory_and_bounds_of_isRestoreRun M hcyc_H₁ hrun hval_rs
  have hS'_sub : S' ⊆ S.erase u := Finset.coe_subset.mp hsub_S'
  have hedge_H₁ : H₁.edgeSet.ncard ≤ K.edgeSet.ncard :=
    ncard_edgeSet_contractGraph_le hadj_K.2 htrial.1
  have hedge_bound : H.edgeSet.ncard ≤ K.edgeSet.ncard + 3 * (K.neighborSet u).ncard := by
    omega
  have hsz_H : instSize N H ≤ 4 * instSize N K := by
    have : (K.neighborSet u).ncard ≤ N := by
      have := Set.ncard_le_ncard (Set.subset_univ (K.neighborSet u)) (Set.toFinite _)
      simpa using this
    unfold instSize
    omega
  -- Step 7: Classify `(H, S', D')` at `b`
  have hw_cl : wordSize c_cl (instSize N H) ≤ w := by
    have hle : instSize N H ≤ 4 * ((N + 1) * instSize N K) := by
      have : instSize N K ≤ (N + 1) * instSize N K := Nat.le_mul_of_pos_left _ (by omega)
      omega
    exact (wordSize_le_of_le_mul_self (K := 4) hle).trans
      ((wordSize_mono_left (by omega) _).trans hw)
  obtain ⟨s₆, t₆, hex₆, ht₆, hk₆, hcl_out⟩ :=
    hP_cl w N H S' D' s₅ hw_cl hinst_b₅ hcyc_H
  -- Combine executions and verify all postconditions
  have hex_all : Exec w P_all s s₆
      (t₁ + (t₂ + (t₃ + (2 + (2 + (t₄ + (t₅ + t₆))))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₃a (.seq hex₃b (.seq hex₄ (.seq hex₅ hex₆))))))
  have hlen_trec₆ : (s₆.arrs a_trec).length ≤
      (C_cp + 25 + (2 * C_buf + 20) + C_ct + C_rs + 4 * C_cl + 10) *
        ((K.neighborSet u).ncard + 1) * instSize N K := by
    rw [hk₆.2 a_trec (Nat.lt_succ_of_lt (hok.2 a_trec (by simp))) htrec_not_QR,
      hlen_trec₅, hlen_trec₄, show (s₃b.arrs a_trec).length = k₀ from hlen_trec₃]
    have h1 : k₀ ≤ 2 * C_buf * (((K.neighborSet u).ncard + 1) * instSize N K) :=
      hk₀_hi.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
    have h2 : 2 * C_buf * (((K.neighborSet u).ncard + 1) * instSize N K) ≤
        (C_cp + 25 + (2 * C_buf + 20) + C_ct + C_rs + 4 * C_cl + 10) *
          (((K.neighborSet u).ncard + 1) * instSize N K) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_assoc]
    exact h1.trans h2
  refine ⟨s₆, _, hex_all, ?_, ?_, H, S', CrossRecord.contr c_rec :: rs.map CrossRecord.repl,
    k₂, ?_, ?_, ?_, ?_, hclean_H, hS'_sub, hcrossed_iff, hlen_trec₆, hedge_bound, hcl_out⟩
  · -- Time bound
    set X := ((K.neighborSet u).ncard + 1) * instSize N K
    have hX_sz : instSize N K ≤ X := Nat.le_mul_of_pos_left _ (by omega)
    have hX_deg : (K.neighborSet u).ncard + 1 ≤ X := Nat.le_mul_of_pos_right _ (by omega)
    have hX_M : (M.length + 1) * instSize N K ≤ X := Nat.mul_le_mul_right _ (by omega)
    have ht₁' : t₁ ≤ C_cp * X := ht₁.trans (Nat.mul_le_mul_left _ hX_sz)
    have ht₂' : t₂ ≤ 25 * X := ht₂.trans (Nat.mul_le_mul_left _ hX_deg)
    have ht₃' : t₃ ≤ (2 * C_buf + 20) * X := ht₃.trans (Nat.mul_le_mul_left _ hX_M)
    have ht₄' : t₄ ≤ C_ct * X := ht₄.trans (Nat.mul_le_mul_left _ hX_sz)
    have ht₅' : t₅ ≤ C_rs * X := by
      calc t₅ ≤ C_rs * (M.length + 1) * instSize N H₁ := ht₅
        _ ≤ C_rs * (M.length + 1) * instSize N K := Nat.mul_le_mul_left _ hsz_H₁
        _ = C_rs * ((M.length + 1) * instSize N K) := Nat.mul_assoc _ _ _
        _ ≤ C_rs * X := Nat.mul_le_mul_left _ hX_M
    have ht₆' : t₆ ≤ 4 * C_cl * X := by
      calc t₆ ≤ C_cl * instSize N H := ht₆
        _ ≤ C_cl * (4 * instSize N K) := Nat.mul_le_mul_left _ hsz_H
        _ = 4 * C_cl * instSize N K := by ring
        _ ≤ 4 * C_cl * X := Nat.mul_le_mul_left _ hX_sz
    have hX_pos : 1 ≤ X := by omega
    calc t₁ + (t₂ + (t₃ + (2 + (2 + (t₄ + (t₅ + t₆))))))
      _ ≤ C_cp * X + (25 * X + ((2 * C_buf + 20) * X +
          (10 * X + (C_ct * X + (C_rs * X + 4 * C_cl * X))))) := by omega
      _ = (C_cp + 25 + (2 * C_buf + 20) + C_ct + C_rs + 4 * C_cl + 10) *
          ((K.neighborSet u).ncard + 1) * instSize N K := by dsimp [X]; ring
  · -- KeepsBelow R A [r_trec] (b.list ++ [a_trec, a_Q, a_R]) s s₆
    refine ⟨fun r hr hrt' => ?_, fun x hx hxl => ?_⟩
    · simp only [List.mem_singleton] at hrt'
      rw [hk₆.1 r hr (by simp),
        hk₅.1 r (by omega) (by simp [hrt']),
        hk₄.1 r (by omega) (by simp [hrt'])]
      simp only [s₃b, s₃a, State.setReg_regs_ne _ _ (show r ≠ R + 3 by omega),
        State.setReg_regs_ne _ _ (show r ≠ R + 2 by omega)]
      rw [hreg₃ r hrt', hreg₂ r (by omega), hk₁.1 r (by omega) (by simp)]
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hxl
      obtain ⟨hxb, hxtrec, hxQ, hxR⟩ := hxl
      have hxA1 : x < A + 1 := by omega
      have hx_ne_mk : x ≠ a_mk := by omega
      rw [hk₆.2 x hxA1 (by simp [hxQ, hxR]),
        hk₅.2 x hxA1 (by simp [hxb, hxtrec]),
        hk₄.2 x hxA1 (by simp [hxb, hxtrec])]
      change s₃.arrs x = s.arrs x
      rw [harr₃ x hxtrec, harr₂ x hx_ne_mk, hk₁.2 x hxA1 hxb]
  · -- IsInstanceAt b H S' D' s₆
    exact hinst_b₅.of_arrs_eq fun x hxb =>
      hk₆.2 x (Nat.lt_succ_of_lt (hok.2 x (List.mem_append_left _ (List.mem_append_right _ hxb))))
        (hb_not_QR x hxb)
  · -- IsHistoryFin K S D (CrossRecord.contr c_rec :: rs.map CrossRecord.repl) H S' D'
    have hhist_rs' : IsHistory (c_rec.newGraph, c_rec.newVerts, c_rec.newCycle)
        (rs.map CrossRecord.repl) (H, (S' : Set (Fin N)), D') := by
      change IsHistory (H₁, (S : Set (Fin N)) \ {u}, D') (rs.map CrossRecord.repl)
        (H, (S' : Set (Fin N)), D')
      rwa [← hS₁_coe]
    exact ⟨rfl, rfl, rfl, ⟨hinst.1, hcyc, htrial⟩, hhist_rs'⟩
  · -- ContractionsLong (CrossRecord.contr c_rec :: rs.map CrossRecord.repl)
    intro r hr
    rcases List.mem_cons.mp hr with h | hr
    · injection h with h
      subst h
      exact hlong
    · obtain ⟨r', -, h⟩ := List.mem_map.mp hr
      nomatch h
  · -- IsRecBufAt a_trec r_trec (CrossRecord.contr c_rec :: rs.map CrossRecord.repl) k₂ s₆
    obtain ⟨ls, hls, he, hr⟩ := hbuf₅
    refine ⟨ls, by simpa using hls, ?_, ?_⟩
    · rw [hk₆.2 a_trec (Nat.lt_succ_of_lt (hok.2 a_trec (by simp))) htrec_not_QR, he]
    · rw [hk₆.1 r_trec hrt (by simp), hr]

/-- **One trial** (Section 10, step 4) from `RestoreRecNeProgClaim` and `ClassifyProgClaim`. -/
theorem trialRecProgClaim_of :
    TrialRecProgClaim := by
  intro prog Cp cp_w hprog a b a_trec r_trec a_Q a_R A R hok hrt
  obtain ⟨P, C, c, hP⟩ :=
    trialRecFullProgClaim_of prog Cp cp_w hprog a b a_trec r_trec a_Q a_R A R hok hrt
  refine ⟨P, C, c, fun w N inst K S D u v s hw hinst hcyc hclean htrial hlong hu hv => ?_⟩
  obtain ⟨s', t, hex, ht, hk, H, S', recs, k', hinst', hhist, hclong, hbuf, hclean', -, -, -,
    hedge, hout⟩ :=
    hP w N K S D u v s hw hinst hcyc hclean htrial hlong hu hv
  exact ⟨s', t, hex, ht, hk, H, S', recs, k', hinst', hhist, hclong, hbuf, hclean', hedge, hout⟩

end GraphMinor.Compute.Crossing

