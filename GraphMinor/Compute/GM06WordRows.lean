module

public import GraphMinor.Compute.GM06Alg34FilterMapArray
public import GraphMinor.Compute.TwoPathsCyc

/-!
# Copying word rows for the Reduction 4 splice

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) copies the
projected replacement followed by the retained old suffix. These
programs append whole word rows without adding headers or removing
an endpoint. The buffer invariant records the exact copied prefix.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Append every source word into a buffer at cursor 655. -/
def gm06AppendWordsProg (src dst : Arr) : Cmd :=
  gm06FilterMapArrayProg src dst 650 651 652 655 (.const 1) (.reg 652)

/-- An unconditional word scan appends exactly its input row. -/
theorem gm06AppendWordsProg_exec {w src dst cap : ℕ} (hne : src ≠ dst)
    (words pre : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hwords : ∀ x ∈ words, x < 2 ^ w) (hsource : s.arrs src = words)
    (hcap : words.length ≤ cap) (hfit : pre.length + cap + 2 < 2 ^ w)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf dst 655 pre cap s) :
    ∃ sf t, Exec w (gm06AppendWordsProg src dst) s sf t ∧ t ≤ 7 + 18 * words.length ∧
      Keeps [650, 651, 652, 655] [dst] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf dst 655 (pre ++ words) (cap - words.length) sf := by
  obtain ⟨sf, t, he, ht, hb, ha, hr⟩ := gm06FilterMapArrayProg_exec
    src dst 650 651 652 655 (.const 1) (.reg 652) (fun _ => true) id
    hne (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hw hsource (by omega) hwords hbuf (by simpa using hcap) hfit
    (fun _ _ _ _ _ _ => GraphMinor.Compute.Crossing.eval_const hw)
    (fun _ x hx _ _ _ hr => GraphMinor.Compute.Crossing.eval_reg hr (hwords x hx))
  refine ⟨sf, t, he, by simp only [Expr.cost] at ht; omega, ⟨?_, ?_⟩, by simpa using hb⟩
  · intro r hnot
    have hh : r ≠ 650 ∧ r ≠ 651 ∧ r ≠ 652 ∧ r ≠ 655 := by simpa using hnot
    exact hr r hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  · intro a ha'
    exact ha a (by simpa using ha')

/-- Allocate an exact row and append both input arrays in order. -/
def gm06ConcatWordsProg (first second dst : Arr) : Cmd :=
  .seq (.alloc dst (.op .add (.len first) (.len second)))
    (.seq (.assign 655 (.const 0))
      (.seq (gm06AppendWordsProg first dst) (gm06AppendWordsProg second dst)))

/-- Concatenation returns exactly both lists, with linear cost and
without changing either source or any unrelated memory. -/
theorem gm06ConcatWordsProg_exec {w first second dst : ℕ}
    (hfirst : first ≠ dst) (hsecond : second ≠ dst)
    (xs ys : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hfit : xs.length + ys.length + 2 < 2 ^ w)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hy : ∀ y ∈ ys, y < 2 ^ w)
    (ha : s.arrs first = xs) (hb : s.arrs second = ys) :
    ∃ sf t, Exec w (gm06ConcatWordsProg first second dst) s sf t ∧
      t ≤ 19 + 19 * (xs.length + ys.length) ∧ Keeps [650, 651, 652, 655] [dst] s sf ∧
      sf.arrs dst = xs ++ ys ∧ sf.regs 655 = (xs ++ ys).length := by
  let size := xs.length + ys.length
  let s₀ := s.setArr dst (List.replicate size 0)
  let s₁ := s₀.setReg 655 0
  have he₀ : Exec w (.alloc dst (.op .add (.len first) (.len second))) s s₀ (3 + size) :=
    .alloc (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_len ha (by omega))
      (GraphMinor.Compute.Crossing.eval_len hb (by omega)) (by omega))
  have he₁ : Exec w (.assign 655 (.const 0)) s₀ s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk₁ : Keeps [650, 651, 652, 655] [dst] s s₁ :=
    ((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hb₂⟩  := gm06AppendWordsProg_exec (cap := size) hfirst xs [] s₁ hw hx
    ((hk₁.2 first (by simpa using hfirst)).trans ha) (by change xs.length ≤ xs.length + ys.length; omega)
    (by simpa only [List.length_nil, Nat.zero_add, size] using hfit)
    (by simp [GraphMinor.Compute.Crossing.IsBuf, s₁, s₀])
  have hk₁₂ := hk₁.trans hk₂ (fun _ h => h) (fun _ h => h)
  obtain ⟨sf, tf, hef, htf, hkf, hbf⟩  := gm06AppendWordsProg_exec (cap := ys.length) hsecond ys xs s₂ hw hy
    ((hk₁₂.2 second (by simpa using hsecond)).trans hb) le_rfl
    hfit (by simpa only [List.nil_append, size, Nat.add_sub_cancel_left] using hb₂)
  refine ⟨sf, (3 + size) + (2 + (t₂ + tf)), .seq he₀ (.seq he₁ (.seq he₂ hef)), ?_,
    hk₁₂.trans hkf (fun _ h => h) (fun _ h => h), ?_, hbf.2⟩
  · dsimp only [size]
    omega
  · simpa only [size, Nat.add_sub_cancel_left, Nat.sub_self, List.replicate_zero,
      List.append_nil] using hbf.1

end GraphMinor.Compute
