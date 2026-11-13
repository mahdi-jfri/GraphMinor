module

public import GraphMinor.Compute.CrossingOpsReplLists
public import GraphMinor.Compute.CrossingOpsEmitSum

/-!
# Scanning the vertices of a replacement record

The outer loop reads the recorded vertices from an array. For each vertex it scans its
adjacency list and emits the pairs with marked endpoints. The running time sums the lengths
of the lists scanned, so that a large degree does not increase the cost of other iterations.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Emit the marked pairs from every vertex in the source array. -/
def emitPairsProg (a a_s a_e a_ent a_mark a_buf R : ℕ) : Cmd :=
  forArrProg a (R + 5) (R + 6) R (emitPairListProg a_s a_e a_ent a_mark a_buf R)

/-- The nested record loop emits exactly the filtered pairs and sums the lengths scanned.
The source lists, mark array, capacity, and word bounds are the preconditions. -/
theorem emitPairsProg_exec {w N : ℕ} (a a_s a_e a_ent a_mark a_buf R : ℕ)
    (xs rb : List ℕ) (lists : ℕ → List ℕ) (st en : ℕ → ℕ)
    {s : State} {pre : List ℕ} {k : ℕ}
    (ha : a ≠ a_buf) (hs : a_s ≠ a_buf) (he : a_e ≠ a_buf)
    (hent : a_ent ≠ a_buf) (hm : a_mark ≠ a_buf)
    (hxs : s.arrs a = xs)
    (hl : ∀ x ∈ xs, IsListAt a_s a_e a_ent x (st x) (en x) (lists x) s)
    (hmark : s.arrs a_mark = setAt (List.replicate N 0) rb 1)
    (hb : IsBuf a_buf (R + 4) pre k s)
    (hk : (xs.flatMap (fun x => ((lists x).filter (fun y => y ∈ rb)).flatMap
      (fun y => [x, y]))).length ≤ k)
    (hxw : ∀ x ∈ xs, x < 2 ^ w) (hlen : xs.length < 2 ^ w)
    (hlt : ∀ x ∈ xs, ∀ y ∈ lists x, y < N)
    (hen : ∀ x ∈ xs, en x < 2 ^ w)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) (hcap : pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (emitPairsProg a a_s a_e a_ent a_mark a_buf R) s s' t ∧
      t ≤ 7 + ∑ j ∈ Finset.range xs.length, (19 + 28 * (lists (xs[j]?.getD 0)).length) ∧
      IsBuf a_buf (R + 4)
        (pre ++ xs.flatMap (fun x => ((lists x).filter (fun y => y ∈ rb)).flatMap
          (fun y => [x, y])))
        (k - (xs.flatMap (fun x => ((lists x).filter (fun y => y ∈ rb)).flatMap
          (fun y => [x, y]))).length) s' ∧
      (∀ b, b ≠ a_buf → s'.arrs b = s.arrs b) ∧
      (∀ r, r ≠ R → r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
        r ≠ R + 5 → r ≠ R + 6 → s'.regs r = s.regs r) := by
  classical
  let g : ℕ → List ℕ := fun x => ((lists x).filter (fun y => y ∈ rb)).flatMap
    (fun y => [x, y])
  let Q : ℕ → State → Prop := fun _ z =>
    (∀ b, b ≠ a_buf → z.arrs b = s.arrs b) ∧
    (∀ r, r ≠ R → r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
      r ≠ R + 5 → r ≠ R + 6 → z.regs r = s.regs r)
  obtain ⟨s', t, hex, ht, hQ, hb'⟩ := forArrEmitSum_exec a (R + 5) (R + 6) R a_buf (R + 4)
    (emitPairListProg a_s a_e a_ent a_mark a_buf R) g Q
    (fun j => 9 + 28 * (lists ((s.arrs a)[j]?.getD 0)).length)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hw
    (by simpa [hxs] using hlen) (by simpa [hxs] using hxw)
    ⟨fun _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩ hb (by simpa only [hxs] using hk)
    (fun j z z' h harr hreg => ⟨fun b hb => by rw [harr]; exact h.1 b hb,
      fun r h0 h1 h2 h3 h4 h5 h6 => (hreg r h5 h6 h0).trans
        (h.2 r h0 h1 h2 h3 h4 h5 h6)⟩)
    (fun _ z h => h.1 a ha)
    (fun j hj z pre' k' hQ hri hrn hrx hbuf hk' hlen' => by
      have hj' : j < xs.length := by simpa [hxs] using hj
      have hmem : (s.arrs a)[j] ∈ xs := by simpa [hxs] using List.getElem_mem hj
      have hlist := IsListAt.of_arrs_eq (hl _ hmem) (hQ.1 a_s hs)
        (hQ.1 a_e he) (hQ.1 a_ent hent)
      obtain ⟨z', t', hex', ht', hb'', harr, hreg⟩ := emitPairListProg_exec
        a_s a_e a_ent a_mark a_buf R hent hm hlist hrx
        (by rw [hQ.1 a_mark hm]; exact hmark) hbuf hk' (hlt _ hmem) hN
        (hxw _ hmem) (hen _ hmem) (by omega)
      refine ⟨z', t', hex', ?_, ?_, ?_, ?_, hb''⟩
      · simpa only [List.getElem?_eq_getElem hj, Option.getD_some] using ht'
      · exact ⟨fun b hb => (harr b hb).trans (hQ.1 b hb),
          fun r h0 h1 h2 h3 h4 h5 h6 => (hreg r h1 h2 h3 h4).trans
            (hQ.2 r h0 h1 h2 h3 h4 h5 h6)⟩
      · exact (hreg (R + 5) (by omega) (by omega) (by omega) (by omega)).trans hri
      · exact (hreg (R + 6) (by omega) (by omega) (by omega) (by omega)).trans hrn)
  refine ⟨s', t, hex, ?_, by simpa [hxs, g] using hb', hQ.1, hQ.2⟩
  rw [hxs] at ht
  convert ht using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  omega

/-- Summing costs by array indices agrees with summing costs over the array contents. -/
theorem sum_range_getD (xs : List ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ Finset.range xs.length, f (xs[j]?.getD 0)) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getElem?_cons_zero,
      Option.getD_some, List.getElem?_cons_succ, List.map_cons, List.sum_cons]
    rw [ih, Nat.add_comm]

/-- Distinct recorded vertices scan at most all adjacency entries. -/
theorem emitPairs_cost_linear {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) {xs : List ℕ}
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < N) :
    7 + (∑ j ∈ Finset.range xs.length,
      (19 + 28 * (listOf lists (xs[j]?.getD 0)).length)) ≤
      7 + 19 * N + 56 * G.edgeSet.ncard := by
  have hsum : (∑ x ∈ Finset.range N, (listOf lists x).length) =
      2 * G.edgeSet.ncard := by
    have heq := length_flatUpTo_eq (H := G) (L := listOf lists) (by
      intro x; simpa [listOf_fin] using h x)
    rw [← heq, length_flatUpTo]
  rw [sum_range_getD xs (fun x => 19 + 28 * (listOf lists x).length)]
  have hb := sum_map_le_of_nodup (fun x => 19 + 28 * (listOf lists x).length) hnd hlt
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum, hsum] at hb
  omega

/-- On an adjacency-list encoding, the pair scan takes linear time. The source vertices
are distinct and below `N`, the marks represent `rb`, and the buffer has enough space. -/
theorem emitPairsProg_linear_exec {w N : ℕ} (a a_s a_e a_ent a_mark a_buf R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {xs rb pre : List ℕ}
    {s : State} {k : ℕ}
    (ha : a ≠ a_buf) (hs : a_s ≠ a_buf) (he : a_e ≠ a_buf)
    (hent : a_ent ≠ a_buf) (hm : a_mark ≠ a_buf)
    (hxs : s.arrs a = xs) (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < N)
    (hadj : IsAdjList G a_s a_e a_ent lists s)
    (hmark : s.arrs a_mark = setAt (List.replicate N 0) rb 1)
    (hb : IsBuf a_buf (R + 4) pre k s)
    (hk : (xs.flatMap (pairsOf lists rb)).length ≤ k)
    (hw : N + (s.arrs a_ent).length + pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (emitPairsProg a a_s a_e a_ent a_mark a_buf R) s s' t ∧
      t ≤ 7 + 19 * N + 56 * G.edgeSet.ncard ∧
      IsBuf a_buf (R + 4) (pre ++ xs.flatMap (pairsOf lists rb))
        (k - (xs.flatMap (pairsOf lists rb)).length) s' ∧
      (∀ b, b ≠ a_buf → s'.arrs b = s.arrs b) ∧
      (∀ r, r ≠ R → r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
        r ≠ R + 5 → r ≠ R + 6 → s'.regs r = s.regs r) := by
  classical
  have hl : ∀ x, ∃ st en, x ∈ xs →
      IsListAt a_s a_e a_ent x st en (listOf lists x) s ∧
      en ≤ (s.arrs a_ent).length := by
    intro x
    by_cases hx : x ∈ xs
    · obtain ⟨st, en, h, hb⟩ := exists_isListAt hadj (hlt x hx)
      exact ⟨st, en, fun _ => ⟨h, hb⟩⟩
    · exact ⟨0, 0, fun h => False.elim (hx h)⟩
  choose st en hl using hl
  have hfun : pairsOf lists rb = fun x =>
      ((listOf lists x).filter (fun y => y ∈ rb)).flatMap (fun y => [x, y]) := by
    funext x
    rfl
  rw [hfun] at hk ⊢
  obtain ⟨s', t, hex, ht, hb', harr, hreg⟩ := emitPairsProg_exec (w := w) (N := N)
    a a_s a_e a_ent a_mark a_buf R xs rb (listOf lists) st en ha hs he hent hm hxs
    (fun x hx => (hl x hx).1) hmark hb hk
    (fun x hx => by have := hlt x hx; omega)
    (by have := length_le_of_nodup_lt hnd hlt; omega)
    (fun x _ => listOf_lt hadj.2 x) (fun x hx => by have := (hl x hx).2; omega)
    (by omega) (by omega) (by omega)
  refine ⟨s', t, hex, ht.trans (emitPairs_cost_linear hadj.2 hnd hlt), ?_, harr, hreg⟩
  exact hb'

end GraphMinor.Compute.Crossing
