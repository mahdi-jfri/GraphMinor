module

public import GraphMinor.Compute.GM06Alg511StoredPathRow
import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.GM06RefreshContractedMasks
import Mathlib.Tactic

/-!
# Materializing every initial linkage row

The linkage used by VI (5.11), page 134, must be passed to (5.7)
as ordinary directed path rows. Start with an empty row for each
supplied cuff source. Visit those sources in their supplied order,
materialize their stored flow paths and replace the corresponding
rows. The invariant retains the completed prefix and leaves every
later row empty. The output is the exact length-prefixed row table,
with the original raw flow and edge choices preserved. Its bound
is polynomial even using the separate vertex bound for each path.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Surface TwoPaths

/-- The table of computed source paths in the supplied cuff order. -/
def gm06Alg511StoredPathRows (x : GM06Alg511Input) (out choices : List ℕ)
    (sources : List (Fin x.vertexCount)) : List (List ℕ) :=
  sources.map (fun u => gm06Alg511StoredPathRow x out choices u.val)

private def pathPrefix (rows : List (List ℕ)) (i : ℕ) : List (List ℕ) :=
  rows.take i ++ List.replicate (rows.length - i) []

private theorem prefix_length (rows : List (List ℕ)) (i : ℕ) :
    (pathPrefix rows i).length = rows.length := by
  simp only [pathPrefix, List.length_append, List.length_take, List.length_replicate]
  omega

private theorem prefix_zero (rows : List (List ℕ)) :
    pathPrefix rows 0 = List.replicate rows.length [] := by simp [pathPrefix]

private theorem prefix_last (rows : List (List ℕ)) : pathPrefix rows rows.length = rows := by
  simp [pathPrefix]

private theorem prefix_get (rows : List (List ℕ)) {i : ℕ} (hi : i < rows.length) :
    (pathPrefix rows i)[i]'(by rw [prefix_length]; exact hi) = [] := by
  have ht : (rows.take i).length = i := List.length_take_of_le hi.le
  have hr : List.replicate (rows.length - i) ([] : List ℕ) =
      [] :: List.replicate (rows.length - (i + 1)) [] := by
    rw [show rows.length - i = rows.length - (i + 1) + 1 by omega, List.replicate_succ]
  unfold pathPrefix
  rw [List.getElem_append_right (by rw [ht])]
  simp only [ht, Nat.sub_self, hr, List.getElem_cons_zero]

private theorem prefix_step (rows : List (List ℕ)) {i : ℕ} (hi : i < rows.length) :
    (pathPrefix rows i).set i rows[i] = pathPrefix rows (i + 1) := by
  have ht : (rows.take i).length = i := List.length_take_of_le hi.le
  have hr : List.replicate (rows.length - i) ([] : List ℕ) =
      [] :: List.replicate (rows.length - (i + 1)) [] := by
    rw [show rows.length - i = rows.length - (i + 1) + 1 by omega, List.replicate_succ]
  unfold pathPrefix
  rw [List.set_append_right _ _ (by rw [ht]), ht, Nat.sub_self, hr, List.set_cons_zero,
    List.take_succ_eq_append_getElem hi]
  simp only [List.singleton_append, List.append_assoc]

private theorem prefix_member {rows : List (List ℕ)} {i : ℕ} {row : List ℕ}
    (hrow : row ∈ pathPrefix rows i) : row ∈ rows ∨ row = [] := by
  rcases List.mem_append.mp hrow with h | h
  · exact Or.inl (List.mem_of_mem_take h)
  · exact Or.inr (List.mem_replicate.mp h).2

private theorem flatten_length_bound (rows : List (List ℕ)) (n : ℕ)
    (hrows : ∀ row ∈ rows, row.length ≤ n) : rows.flatten.length ≤ rows.length * n := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hh := hrows row (by simp)
    have ht := ih (fun r hr => hrows r (by simp [hr]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    calc
      row.length + rows.flatten.length ≤ n + rows.length * n := Nat.add_le_add hh ht
      _ = (rows.length + 1) * n := by ring

private theorem prefix_code_length (rows : List (List ℕ)) (n i : ℕ)
    (hrows : ∀ row ∈ rows, row.length ≤ n) :
    (gm06EncodeRows (pathPrefix rows i)).length ≤ 1 + rows.length + rows.length * n := by
  have hb : ∀ row ∈ pathPrefix rows i, row.length ≤ n := by
    intro row hrow
    rcases prefix_member hrow with h | rfl
    · exact hrows row h
    · simp
  rw [gm06EncodeRows_length, prefix_length]
  have hflat := flatten_length_bound (pathPrefix rows i) n hb
  rw [prefix_length] at hflat
  exact Nat.add_le_add_left hflat _

private theorem prefix_code_words {w : ℕ} (rows : List (List ℕ)) (n i : ℕ)
    (hk : rows.length < 2 ^ w) (hn : n < 2 ^ w)
    (hrows : ∀ row ∈ rows, row.length ≤ n ∧ ∀ d ∈ row, d < 2 ^ w) :
    ∀ d ∈ gm06EncodeRows (pathPrefix rows i), d < 2 ^ w := by
  intro d hd
  rcases List.mem_cons.mp hd with h | hd
  · subst d
    rw [prefix_length]
    exact hk
  · obtain ⟨row, hrow, hd⟩ := List.mem_flatMap.mp hd
    have hb : row.length ≤ n ∧ ∀ v ∈ row, v < 2 ^ w := by
      rcases prefix_member hrow with h | rfl
      · exact hrows row h
      · exact ⟨Nat.zero_le _, by simp⟩
    rcases List.mem_cons.mp hd with h | hd
    · subst d
      exact hb.1.trans_lt hn
    · exact hb.2 d hd

private theorem encode_empty_rows (k : ℕ) :
    gm06EncodeRows (List.replicate k []) = k :: List.replicate k 0 := by
  have hp : gm06EncodeRowsPayload (List.replicate k []) = List.replicate k 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.replicate_succ, gm06EncodeRowsPayload, List.flatMap_cons,
        gm06EncodeNatList, List.length_nil, List.singleton_append]
      exact congrArg (List.cons 0) ih
  simp only [gm06EncodeRows, List.length_replicate, hp]

/-- Initialize one empty path row per cuff source and materialize
all sources, in order, using the stored flow and edge choices. -/
def gm06Alg511StoredPathRowsProg : Cmd :=
  .seq (.alloc 8 (.op .add (.len 1210) (.const 1)))
    (.seq (.write 8 (.const 0) (.len 1210))
      (.seq (.assign 1601 (.const 0))
        (forUp 1601 (.len 1210) gm06Alg511StoreSourcePathProg)))

/-- Every source path is computed from the retained raw flow and
choices. The output is exactly the successor procedure's ordinary
path-row code, with a uniform polynomial bound and all other input
arrays retained. No path rows or edge selections are supplied. -/
theorem gm06Alg511StoredPathRowsProg_exec {w : ℕ} (x : GM06Alg511Input)
    (out choices : List ℕ)
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (sources : List (Fin x.vertexCount))
    (hstarts : ∀ u ∈ sources, u ∈ pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out))
    (s : State) (hw : 1 < 2 ^ w) (hword : 1 + 3 * x.vertexCount < 2 ^ w)
    (hcap : 1 + sources.length + sources.length * x.vertexCount < 2 ^ w)
    (hchoiceLen : choices.length = x.vertexCount) (hchoiceWords : ∀ d ∈ choices, d < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.vertexCount)
    (hout : s.arrs outArr = out) (hchoices : s.arrs 1300 = choices)
    (hsources : s.arrs 1210 = sources.map Fin.val) (hN : s.regs 41 = x.vertexCount) :
    ∃ s' t, Exec w gm06Alg511StoredPathRowsProg s s' t ∧
      t ≤ 12 + sources.length * (208 + 150 * x.vertexCount +
        100 * (1 + sources.length + sources.length * x.vertexCount)) ∧
      Keeps [1601, 40, 42, 20, 31, 7, 4, 9, 11, 323, 324, 313, 98] [12, 13, 27, 25, 8, 28] s s' ∧
      s'.arrs 8 = gm06EncodeRows (gm06Alg511StoredPathRows x out choices sources) := by
  let rows := gm06Alg511StoredPathRows x out choices sources
  let k := sources.length
  let n := x.vertexCount
  let C := 1 + k + k * n
  let R := [1601, 40, 42, 20, 31, 7, 4, 9, 11, 323, 324, 313, 98]
  let A := [12, 13, 27, 25, 8, 28]
  have hn : n < 2 ^ w := by dsimp [n]; omega
  have hk : k < 2 ^ w := by dsimp [k] at *; omega
  have hk1 : k + 1 < 2 ^ w := by dsimp [k] at *; omega
  have hrowslen : rows.length = k := List.length_map _
  have hrowBounds : ∀ row ∈ rows, row.length ≤ n ∧ ∀ d ∈ row, d < 2 ^ w := by
    intro row hrow
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hrow
    exact gm06Alg511StoredPathRow_bounds x out choices hsys u (hstarts u hu) hchoiceLen hchoiceWords
  let s₀ := s.setArr 8 (List.replicate (k + 1) 0)
  have he₀ : Exec w (.alloc 8 (.op .add (.len 1210) (.const 1))) s s₀ (k + 4) := by
    have hh := Crossing.eval_add (Crossing.eval_len hsources (by simpa [List.length_map] using hk))
      (Crossing.eval_const hw) (by simpa only [List.length_map] using hk1)
    simpa only [List.length_map, Expr.cost, Nat.reduceAdd, Nat.add_comm] using Exec.alloc (a := 8) hh
  let s₁ := s₀.writeArr 8 0 k
  have he₁ : Exec w (.write 8 (.const 0) (.len 1210)) s₀ s₁ 3 := by
    have hs₀ : s₀.arrs 1210 = sources.map Fin.val := by simpa [s₀] using hsources
    have hlenEval : Expr.eval w s₀ (.len 1210) = some k := by
      simpa only [List.length_map] using Crossing.eval_len hs₀ (by simpa only [List.length_map] using hk)
    exact .write (Crossing.eval_const (Nat.two_pow_pos w)) hlenEval (by simp [s₀])
  have hcode₁ : s₁.arrs 8 = gm06EncodeRows (List.replicate k []) := by
    rw [encode_empty_rows]
    simp only [s₁, s₀, State.writeArr, State.setArr_arrs_self, List.replicate_succ, List.set_cons_zero]
  let s₂ := s₁.setReg 1601 0
  have he₂ : Exec w (.assign 1601 (.const 0)) s₁ s₂ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have hk₂ : Keeps R A s s₂ :=
    (((Keeps.refl _ _ s).setArr (by simp [A]) _).writeArr (by simp [A]) 0 k).setReg (by simp [R]) 0
  let I : ℕ → State → Prop := fun i st =>
    st.regs 1601 = i ∧ st.regs 41 = n ∧ st.arrs outArr = out ∧ st.arrs 1300 = choices ∧
      st.arrs 1210 = sources.map Fin.val ∧ st.arrs 8 = gm06EncodeRows (pathPrefix rows i) ∧ Keeps R A s st
  have hI₂ : I 0 s₂ := by
    refine ⟨by simp [s₂], ?_, ?_, ?_, ?_, ?_, hk₂⟩
    · exact (hk₂.1 41 (by decide)).trans hN
    · exact (hk₂.2 outArr (by decide)).trans hout
    · exact (hk₂.2 1300 (by decide)).trans hchoices
    · exact (hk₂.2 1210 (by decide)).trans hsources
    · simpa only [s₂, State.setReg_arrs, prefix_zero, hrowslen] using hcode₁
  obtain ⟨st, tt, he, ht, hI⟩ := Crossing.forUp_exec' (r_i := 1601) (hi := .len 1210) (body := gm06Alg511StoreSourcePathProg) I k (200 + 150 * n + 100 * C) hw hk
    (fun i hi st hI => ⟨hI.1, by
      simpa only [List.length_map] using Crossing.eval_len hI.2.2.2.2.1 (by simpa only [List.length_map] using hk)⟩)
    (by
      intro i hi st hI
      rcases hI with ⟨hindex, hN', hout', hchoices', hsources', h8', hkeep⟩
      have his : i < sources.length := hi
      let u := sources[i]
      have hur : u ∈ sources := List.getElem_mem his
      have hir : i < rows.length := by rw [hrowslen]; exact hi
      have hpi : i < (pathPrefix rows i).length := by rw [prefix_length, hrowslen]; exact hi
      have hplen := prefix_code_length rows n i (fun row hm => (hrowBounds row hm).1)
      have hplen' := prefix_code_length rows n (i + 1) (fun row hm => (hrowBounds row hm).1)
      rw [hrowslen] at hplen hplen'
      have hstep : (pathPrefix rows i).set i (gm06Alg511StoredPathRow x out choices u.val) =
          pathPrefix rows (i + 1) := by
        have hr : rows[i] = gm06Alg511StoredPathRow x out choices u.val := List.getElem_map _
        rw [← hr]
        exact prefix_step rows hir
      obtain ⟨su, tu, heu, htu, hku, h8u⟩ := gm06Alg511StoreSourcePathProg_exec
        x out choices hsys (pathPrefix rows i) i hpi u (hstarts u hur) st hw hword
        hchoiceLen hchoiceWords hlen hout' hchoices' hN' hindex
        (by rw [hsources', List.length_map]; exact his)
        (by simp only [hsources', List.getElem_map]; rfl) h8'
        (hplen.trans_lt hcap) (by rw [hstep]; exact hplen'.trans_lt hcap)
        (prefix_code_words rows n i (hrowslen ▸ hk) hn hrowBounds)
      have hku' : Keeps R A st su := hku.mono (by simp [R]) (by simp [A])
      have htot := hkeep.trans hku' (by simp [R]) (by simp [A])
      have hki : su.regs 1601 = i := (hku.1 1601 (by decide)).trans hindex
      have htot' := htot.setReg (show 1601 ∈ R by simp [R]) (i + 1)
      refine ⟨su, tu, heu, ?_, ?_, hki⟩
      · rw [prefix_get rows hir] at htu
        simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at htu
        dsimp only [C]
        nlinarith only [htu, hplen, hi]
      · refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, htot'⟩
        · exact (htot'.1 41 (by decide)).trans hN
        · exact (htot'.2 outArr (by decide)).trans hout
        · exact (htot'.2 1300 (by decide)).trans hchoices
        · exact (htot'.2 1210 (by decide)).trans hsources
        · simpa only [State.setReg_arrs, hstep] using h8u) s₂ hI₂
  refine ⟨st, (k + 4) + (3 + (2 + tt)), .seq he₀ (.seq he₁ (.seq he₂ he)), ?_, hI.2.2.2.2.2.2, ?_⟩
  · simp only [Expr.cost] at ht
    dsimp only [k, n, C] at ht ⊢
    nlinarith only [ht]
  · simpa only [← hrowslen, prefix_last] using hI.2.2.2.2.2.1

end GraphMinor.Compute
