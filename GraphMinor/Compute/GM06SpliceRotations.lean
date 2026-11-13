module

public import GraphMinor.Compute.GM06FindLabel
public import GraphMinor.Compute.Join13Write72
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Splicing the two rotations at a contracted initial edge

For Reduction 3 in VI (5.7), page 133, replace the initial edge
end in the cuff rotation by the neighbour's other ends. Read the
neighbour's cyclic order starting just after the opposite edge end.
Four slice copies form the new row. The command finds the two edge
ends itself, preserves both old rows and writes their splice to a
fresh array. This is the local row operation used by the contraction.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- The rotation obtained by deleting the two ends of the contracted
edge and inserting the neighbour's remaining order at its initial end. -/
@[expose] def gm06SplicedRotation (xs ys : List ℕ) (p q : ℕ) : List ℕ :=
  xs.take p ++ ys.drop (q + 1) ++ ys.take q ++ xs.drop (p + 1)

/-- Splicing at two valid positions removes exactly two edge ends. -/
theorem gm06SplicedRotation_length (xs ys : List ℕ) {p q : ℕ}
    (hp : p < xs.length) (hq : q < ys.length) :
    (gm06SplicedRotation xs ys p q).length + 2 = xs.length + ys.length := by
  simp only [gm06SplicedRotation, List.length_append, List.length_take,
    List.length_drop, Nat.min_eq_left hp.le, Nat.min_eq_left hq.le]
  omega

/-- Every remaining label in the splice came from one of the two old rows. -/
theorem gm06SplicedRotation_mem {xs ys : List ℕ} {p q v : ℕ}
    (hv : v ∈ gm06SplicedRotation xs ys p q) : v ∈ xs ∨ v ∈ ys := by
  simp only [gm06SplicedRotation, List.mem_append] at hv
  rcases hv with ((hv | hv) | hv) | hv
  · exact Or.inl (List.mem_of_mem_take hv)
  · exact Or.inr (List.mem_of_mem_drop hv)
  · exact Or.inr (List.mem_of_mem_take hv)
  · exact Or.inl (List.mem_of_mem_drop hv)

/-- Copy one slice into the next unused part of the splice buffer. -/
@[expose] def gm06RotationSliceProg (src dst : Arr) (count start offset : Expr) : Cmd :=
  fillModelPart72Prog 313 count offset (.read src (.op .add start (.reg 313))) dst

/-- A slice copy fills the next part of a zero-padded buffer and
preserves its source, with a bound in the copied length. -/
theorem gm06RotationSliceProg_exec {w : ℕ} (src dst : Arr) (hne : src ≠ dst)
    (count start offset : Expr) (xs pre : List ℕ) (pos len rem : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : xs.length < 2 ^ w) (hbound : pos + len ≤ xs.length)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hrem : len ≤ rem)
    (hcap : pre.length + rem < 2 ^ w) (ha : s.arrs src = xs)
    (hdst : s.arrs dst = pre ++ List.replicate rem 0)
    (hc : ∀ st, Keeps [313] [dst] s st → count.eval w st = some len)
    (hs : ∀ st, Keeps [313] [dst] s st → start.eval w st = some pos)
    (hoff : ∀ st, Keeps [313] [dst] s st → offset.eval w st = some pre.length) :
    ∃ s' t, Exec w (gm06RotationSliceProg src dst count start offset) s s' t ∧
      t ≤ 4 + count.cost + len * (count.cost + offset.cost + start.cost + 12) ∧
      Keeps [313] [dst] s s' ∧
      s'.arrs dst = pre ++ (xs.drop pos).take len ++ List.replicate (rem - len) 0 := by
  have hlength : ((xs.drop pos).take len).length = len := by
    simp only [List.length_take, List.length_drop]
    omega
  obtain ⟨s', t, he, ht, hk, hout, _⟩ := fillModelPart72Prog_exec
    313 count offset (.read src (.op .add start (.reg 313))) dst
    ((xs.drop pos).take len) pre rem s hw (by simpa only [hlength] using hrem)
    hcap (fun st hk => by simpa only [hlength] using hc st hk) hoff
    (fun st i hi hk hr => by
      have hi' : i < len := by simpa only [hlength] using hi
      have hp : pos + i < xs.length := by omega
      have ha' : st.arrs src = xs := (hk.2 src (by simpa using hne)).trans ha
      have hidx := GraphMinor.Compute.Crossing.eval_add (hs st hk)
        (GraphMinor.Compute.Crossing.eval_reg hr (by omega)) (hp.trans hn)
      have hread := GraphMinor.Compute.Crossing.eval_read (a := src) hidx
        (by simpa only [ha'] using hp) (by simpa only [ha'] using hx _ (List.getElem_mem hp))
      simpa only [ha', List.getElem_take, List.getElem_drop] using hread)
    hdst
  refine ⟨s', t, he, ?_, hk, ?_⟩
  · simpa only [hlength, Expr.cost, Nat.add_assoc, Nat.reduceAdd] using ht
  · simpa only [hlength] using hout

/-- With splice positions in registers 317 and 319, form the new
rotation from source rows 25 and 26 in scratch array 27. -/
@[expose] def gm06SpliceRotationRowsCore : Cmd :=
  .seq (.alloc 27 (.op .sub (.op .add (.len 25) (.len 26)) (.const 2)))
    (.seq (gm06RotationSliceProg 25 27 (.reg 317) (.const 0) (.const 0))
      (.seq (gm06RotationSliceProg 26 27
        (.op .sub (.len 26) (.op .add (.reg 319) (.const 1)))
        (.op .add (.reg 319) (.const 1)) (.reg 317))
        (.seq (gm06RotationSliceProg 26 27 (.reg 319) (.const 0)
          (.op .add (.reg 317) (.op .sub (.len 26) (.op .add (.reg 319) (.const 1)))))
          (gm06RotationSliceProg 25 27 (.op .sub (.len 25) (.op .add (.reg 317) (.const 1)))
            (.op .add (.reg 317) (.const 1))
            (.op .add (.reg 317) (.op .sub (.len 26) (.const 1)))))))

/-- The four concrete slice copies compute exactly the cyclic
splice, preserving the old rotation arrays and the positions. -/
theorem gm06SpliceRotationRowsCore_exec {w : ℕ} (xs ys : List ℕ) (p q : ℕ)
    (hp : p < xs.length) (hq : q < ys.length) (s : State)
    (hw : 2 < 2 ^ w) (hn : xs.length + ys.length < 2 ^ w)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hy : ∀ y ∈ ys, y < 2 ^ w)
    (h25 : s.arrs 25 = xs) (h26 : s.arrs 26 = ys)
    (h317 : s.regs 317 = p) (h319 : s.regs 319 = q) :
    ∃ s' t, Exec w gm06SpliceRotationRowsCore s s' t ∧
      t ≤ 50 + 40 * (xs.length + ys.length) ∧ Keeps [313] [27] s s' ∧
      s'.arrs 27 = gm06SplicedRotation xs ys p q := by
  have hw1 : 1 < 2 ^ w := by omega
  have hxw : xs.length < 2 ^ w := by omega
  have hyw : ys.length < 2 ^ w := by omega
  have hpw : p < 2 ^ w := hp.trans hxw
  have hqw : q < 2 ^ w := hq.trans hyw
  let n := xs.length + ys.length - 2
  let s₀ := s.setArr 27 (List.replicate n 0)
  have he₀ : Exec w (.alloc 27 (.op .sub (.op .add (.len 25) (.len 26)) (.const 2)))
      s s₀ (5 + n) := .alloc (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_len h25 hxw)
          (GraphMinor.Compute.Crossing.eval_len h26 hyw) hn)
        (GraphMinor.Compute.Crossing.eval_const hw))
  have hk₀ : Keeps [313] [27] s s₀ := (Keeps.refl _ _ s).setArr (by simp) _
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06RotationSliceProg_exec
    25 27 (by decide) (.reg 317) (.const 0) (.const 0) xs [] 0 p n s₀ hw1 hxw
    (by omega) hx (by dsimp only [n]; omega) (by dsimp only [n]; simp only [List.length_nil]; omega)
    (by simpa [s₀] using h25) (by simp [s₀])
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg
      ((hk.1 317 (by decide)).trans (by simpa [s₀] using h317)) hpw)
    (fun _ _ => GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
    (fun _ _ => by simp [Expr.eval, checkWord])
  have hk₁' : Keeps [313] [27] s s₁ := hk₀.trans hk₁ (by simp) (by simp)
  have htakep : (xs.take p).length = p := List.length_take_of_le hp.le
  have hd₁' : s₁.arrs 27 = xs.take p ++ List.replicate (n - p) 0 := by simpa using hd₁
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06RotationSliceProg_exec
    26 27 (by decide) (.op .sub (.len 26) (.op .add (.reg 319) (.const 1)))
    (.op .add (.reg 319) (.const 1)) (.reg 317) ys (xs.take p)
    (q + 1) (ys.length - (q + 1)) (n - p) s₁ hw1 hyw (by omega) hy
    (by dsimp only [n]; omega) (by rw [htakep]; dsimp only [n]; omega)
    ((hk₁'.2 26 (by decide)).trans h26) hd₁'
    (fun st hk => GraphMinor.Compute.Crossing.eval_sub
      (GraphMinor.Compute.Crossing.eval_len ((hk.2 26 (by decide)).trans ((hk₁'.2 26 (by decide)).trans h26)) hyw)
      (GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_reg ((hk.1 319 (by decide)).trans ((hk₁'.1 319 (by decide)).trans h319)) hqw)
        (GraphMinor.Compute.Crossing.eval_const hw1) (by omega)))
    (fun st hk => GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg ((hk.1 319 (by decide)).trans ((hk₁'.1 319 (by decide)).trans h319)) hqw)
      (GraphMinor.Compute.Crossing.eval_const hw1) (by omega))
    (fun st hk => by
      rw [htakep]
      exact GraphMinor.Compute.Crossing.eval_reg
        ((hk.1 317 (by decide)).trans ((hk₁'.1 317 (by decide)).trans h317)) hpw)
  have hk₂' : Keeps [313] [27] s s₂ := hk₁'.trans hk₂ (by simp) (by simp)
  have hdropq : (ys.drop (q + 1)).length = ys.length - (q + 1) := List.length_drop
  have hd₂' : s₂.arrs 27 = (xs.take p ++ ys.drop (q + 1)) ++
      List.replicate (n - p - (ys.length - (q + 1))) 0 := by
    simpa only [← hdropq, List.take_length] using hd₂
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm06RotationSliceProg_exec
    26 27 (by decide) (.reg 319) (.const 0)
    (.op .add (.reg 317) (.op .sub (.len 26) (.op .add (.reg 319) (.const 1))))
    ys (xs.take p ++ ys.drop (q + 1)) 0 q (n - p - (ys.length - (q + 1))) s₂
    hw1 hyw (by omega) hy (by dsimp only [n]; omega)
    (by simp only [List.length_append, htakep, hdropq]; dsimp only [n]; omega)
    ((hk₂'.2 26 (by decide)).trans h26) hd₂'
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg
      ((hk.1 319 (by decide)).trans ((hk₂'.1 319 (by decide)).trans h319)) hqw)
    (fun _ _ => GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
    (fun st hk => by
      simp only [List.length_append, htakep, hdropq]
      exact GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_reg ((hk.1 317 (by decide)).trans ((hk₂'.1 317 (by decide)).trans h317)) hpw)
        (GraphMinor.Compute.Crossing.eval_sub
          (GraphMinor.Compute.Crossing.eval_len ((hk.2 26 (by decide)).trans ((hk₂'.2 26 (by decide)).trans h26)) hyw)
          (GraphMinor.Compute.Crossing.eval_add
            (GraphMinor.Compute.Crossing.eval_reg ((hk.1 319 (by decide)).trans ((hk₂'.1 319 (by decide)).trans h319)) hqw)
            (GraphMinor.Compute.Crossing.eval_const hw1) (by omega))) (by omega))
  have hk₃' : Keeps [313] [27] s s₃ := hk₂'.trans hk₃ (by simp) (by simp)
  have htakeq : (ys.take q).length = q := List.length_take_of_le hq.le
  have hd₃' : s₃.arrs 27 = (xs.take p ++ ys.drop (q + 1) ++ ys.take q) ++
      List.replicate (xs.length - (p + 1)) 0 := by
    have hrem : n - p - (ys.length - (q + 1)) - q = xs.length - (p + 1) := by
      dsimp only [n]; omega
    simpa only [List.drop_zero, hrem] using hd₃
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hd₄⟩ := gm06RotationSliceProg_exec
    25 27 (by decide) (.op .sub (.len 25) (.op .add (.reg 317) (.const 1)))
    (.op .add (.reg 317) (.const 1)) (.op .add (.reg 317) (.op .sub (.len 26) (.const 1)))
    xs (xs.take p ++ ys.drop (q + 1) ++ ys.take q)
    (p + 1) (xs.length - (p + 1)) (xs.length - (p + 1)) s₃ hw1 hxw (by omega) hx
    (Nat.le_refl _) (by simp only [List.length_append, htakep, hdropq, htakeq]; omega)
    ((hk₃'.2 25 (by decide)).trans h25) hd₃'
    (fun st hk => GraphMinor.Compute.Crossing.eval_sub
      (GraphMinor.Compute.Crossing.eval_len ((hk.2 25 (by decide)).trans ((hk₃'.2 25 (by decide)).trans h25)) hxw)
      (GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_reg ((hk.1 317 (by decide)).trans ((hk₃'.1 317 (by decide)).trans h317)) hpw)
        (GraphMinor.Compute.Crossing.eval_const hw1) (by omega)))
    (fun st hk => GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg ((hk.1 317 (by decide)).trans ((hk₃'.1 317 (by decide)).trans h317)) hpw)
      (GraphMinor.Compute.Crossing.eval_const hw1) (by omega))
    (fun st hk => by
      have heq : (xs.take p ++ ys.drop (q + 1) ++ ys.take q).length = p + (ys.length - 1) := by
        simp only [List.length_append, htakep, hdropq, htakeq]; omega
      rw [heq]
      exact GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_reg ((hk.1 317 (by decide)).trans ((hk₃'.1 317 (by decide)).trans h317)) hpw)
        (GraphMinor.Compute.Crossing.eval_sub
          (GraphMinor.Compute.Crossing.eval_len ((hk.2 26 (by decide)).trans ((hk₃'.2 26 (by decide)).trans h26)) hyw)
          (GraphMinor.Compute.Crossing.eval_const hw1)) (by omega))
  refine ⟨s₄, (5 + n) + (t₁ + (t₂ + (t₃ + t₄))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄))), ?_,
    hk₃'.trans hk₄ (by simp) (by simp), ?_⟩
  · simp only [Expr.cost] at ht₁ ht₂ ht₃ ht₄
    dsimp only [n] at *
    omega
  · simpa only [Nat.sub_self, List.replicate_zero, List.append_nil,
      ← List.length_drop (i := p + 1) (l := xs), List.take_length, gm06SplicedRotation] using hd₄

/-- Find the two contracted ends in the supplied rotations before
splicing. No positions chosen by a proof are supplied to this program. -/
@[expose] def gm06SpliceRotationRowsProg : Cmd :=
  .seq (gm06FindLabelProg 25 23 320 317)
    (.seq (gm06FindLabelProg 26 24 320 319) gm06SpliceRotationRowsCore)

/-- For two ordinary rotation rows, the local contraction command
finds both edge ends and returns their exact splice in linear time. -/
theorem gm06SpliceRotationRowsProg_exec {w : ℕ} (xs ys : List ℕ) (d e : ℕ)
    (hndx : xs.Nodup) (hndy : ys.Nodup) (hd : d ∈ xs) (he : e ∈ ys)
    (s : State) (hw : 2 < 2 ^ w) (hn : xs.length + ys.length < 2 ^ w)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hy : ∀ y ∈ ys, y < 2 ^ w)
    (h25 : s.arrs 25 = xs) (h26 : s.arrs 26 = ys)
    (h23 : s.regs 23 = d) (h24 : s.regs 24 = e) :
    ∃ s' t, Exec w gm06SpliceRotationRowsProg s s' t ∧
      t ≤ 64 + 53 * (xs.length + ys.length) ∧ Keeps [320, 317, 319, 313] [27] s s' ∧
      s'.arrs 27 = gm06SplicedRotation xs ys (xs.idxOf d) (ys.idxOf e) ∧
      (s'.arrs 27).length + 2 = xs.length + ys.length := by
  have hxw : xs.length < 2 ^ w := by omega
  have hyw : ys.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hp⟩ := gm06FindLabelProg_exec_nodup
    25 23 320 317 (by decide) (by decide) (by decide) xs d s (by omega)
    hxw hx hndx hd h25 h23
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hq⟩ := gm06FindLabelProg_exec_nodup
    26 24 320 319 (by decide) (by decide) (by decide) ys e s₁ (by omega)
    hyw hy hndy he ((hk₁.2 26 (by decide)).trans h26) ((hk₁.1 24 (by decide)).trans h24)
  have hp' : s₂.regs 317 = xs.idxOf d := (hk₂.1 317 (by decide)).trans hp
  have hpx : xs.idxOf d < xs.length := List.idxOf_lt_length_iff.mpr hd
  have hqy : ys.idxOf e < ys.length := List.idxOf_lt_length_iff.mpr he
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hout⟩ := gm06SpliceRotationRowsCore_exec
    xs ys (xs.idxOf d) (ys.idxOf e) hpx hqy s₂ hw hn hx hy
    ((hk₂.2 25 (by decide)).trans ((hk₁.2 25 (by decide)).trans h25))
    ((hk₂.2 26 (by decide)).trans ((hk₁.2 26 (by decide)).trans h26)) hp' hq
  let R := [320, 317, 319, 313]
  have hk₁' : Keeps R [27] s s₁ := hk₁.mono (by simp [R]) (by simp)
  have hk₂' : Keeps R [27] s s₂ := hk₁'.trans hk₂ (by simp [R]) (by simp)
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), by omega,
    hk₂'.trans hk₃ (by simp [R]) (by simp), hout, ?_⟩
  rw [hout]
  exact gm06SplicedRotation_length xs ys hpx hqy

end GraphMinor.Compute
