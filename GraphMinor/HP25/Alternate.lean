module

public import GraphMinor.HP25.Defs
import GraphMinor.HP25.CrossTools

/-!
# Alternating vertices on a cycle

Four vertices `a, c, b, d` of a tuple `T` *alternate* (`Alternate T a b c d`) when some rotation of
`T` reads `a L₁ b L₂` with `c ∈ L₁` and `d ∈ L₂`. This is the order condition of a crossing
(Definition 2.4, page 7: paths "from $x_i$ to $x_j$ and $x_r$ to $x_s$, respectively, such that
$i<r<j<s$"), read up to rotation. This file proves:

* `IsCrossing.alternate`: the ends of a crossing alternate;
* `Alternate.swap`, `Alternate.comm`: alternation does not depend on which pair or which end is named
  first;
* `Alternate.mem_of_rotate`: when `T` has no repeated entry, the rotation is determined by `a` and
  `b`, so every split `a A b B` of a rotation of `T` has `c ∈ A` and `d ∈ B`;
* `isCrossed_of_alternate'`: alternating ends of two disjoint `T`-paths give a crossing.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `a, c, b, d` appear in this cyclic order on `T`: some rotation of `T` is `a L₁ b L₂` with
`c ∈ L₁` and `d ∈ L₂`. -/
@[expose] def Alternate (T : List V) (a b c d : V) : Prop :=
  ∃ k L₁ L₂, T.rotate k = a :: L₁ ++ b :: L₂ ∧ c ∈ L₁ ∧ d ∈ L₂

/-- Two rotations of a list without repetition that start with the same entry are equal. -/
theorem rotate_eq_of_head {T : List V} (hnd : T.Nodup) {k k' : ℕ} {a : V} {X Y : List V}
    (h : T.rotate k = a :: X) (h' : T.rotate k' = a :: Y) : X = Y := by
  have hn : 0 < T.length := by
    have := congrArg List.length h
    simp at this
    omega
  have e : ∀ {m : ℕ} {Z : List V}, T.rotate m = a :: Z → T[m % T.length]'(Nat.mod_lt _ hn) = a :=
    fun {m Z} hm => by
      have h0 : 0 < (T.rotate m).length := by simp; omega
      have := List.getElem_rotate T m 0 h0
      simp only [zero_add] at this
      rw [← this]
      simp [hm]
  have hk := e h
  have hk' := e h'
  have hmod : k % T.length = k' % T.length :=
    (List.Nodup.getElem_inj_iff hnd).mp (hk.trans hk'.symm)
  have : T.rotate k = T.rotate k' := by rw [← List.rotate_mod, hmod, List.rotate_mod]
  rw [h, h'] at this
  exact List.cons_injective this

/-- The split of a list without repetition at an entry is unique. -/
theorem split_unique {b : V} {L₁ L₂ A B : List V} (h : L₁ ++ b :: L₂ = A ++ b :: B)
    (hnd : (L₁ ++ b :: L₂).Nodup) : L₁ = A ∧ L₂ = B := by
  classical
  have hb1 : b ∉ L₁ := fun hb => (List.nodup_append.mp hnd).2.2 b hb b (by simp) rfl
  have hb2 : b ∉ A := by
    rw [h] at hnd
    exact fun hb => (List.nodup_append.mp hnd).2.2 b hb b (by simp) rfl
  have hlen : L₁.length = A.length := by
    have e1 := List.idxOf_append_of_notMem hb1 (l₂ := b :: L₂) (a := b)
    have e2 := List.idxOf_append_of_notMem hb2 (l₂ := b :: B) (a := b)
    rw [h] at e1
    rw [e1] at e2
    simpa [List.idxOf_cons_self] using e2
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  exact ⟨h1, List.cons_injective h2⟩

/-- **Alternation does not depend on the rotation.** If `a, c, b, d` alternate on `T` and a rotation
of `T` is `a A b B`, then `c ∈ A` and `d ∈ B`. -/
theorem Alternate.mem_of_rotate {T : List V} (hnd : T.Nodup) {a b c d : V}
    (h : Alternate T a b c d) {k : ℕ} {A B : List V} (hrot : T.rotate k = a :: A ++ b :: B) :
    c ∈ A ∧ d ∈ B := by
  obtain ⟨k', L₁, L₂, hrot', hc, hd⟩ := h
  have e := rotate_eq_of_head hnd hrot' hrot
  have hnd' : (L₁ ++ b :: L₂).Nodup := by
    have := (List.nodup_rotate (n := k')).mpr hnd
    rw [hrot'] at this
    exact (List.nodup_cons.mp this).2
  obtain ⟨rfl, rfl⟩ := split_unique e hnd'
  exact ⟨hc, hd⟩

/-- The rotation of `a A b B` that starts at `b`. -/
theorem rotate_cons_append_cons' (a b : V) (A B : List V) :
    (a :: A ++ b :: B).rotate (A.length + 1) = b :: B ++ a :: A := by
  rw [List.rotate_eq_drop_append_take (by simp)]
  simp

/-- Alternation, starting from the other end of the first pair. -/
theorem Alternate.swap {T : List V} {a b c d : V} (h : Alternate T a b c d) :
    Alternate T b a d c := by
  obtain ⟨k, L₁, L₂, hrot, hc, hd⟩ := h
  refine ⟨k + (L₁.length + 1), L₂, L₁, ?_, hd, hc⟩
  rw [← List.rotate_rotate, hrot, rotate_cons_append_cons']

/-- Alternation, starting from the second pair. -/
theorem Alternate.comm {T : List V} {a b c d : V} (h : Alternate T a b c d) :
    Alternate T c d b a := by
  obtain ⟨k, L₁, L₂, hrot, hc, hd⟩ := h
  obtain ⟨X, Y, rfl⟩ := List.append_of_mem hc
  obtain ⟨Z, W, rfl⟩ := List.append_of_mem hd
  refine ⟨k + (X.length + 1), Y ++ b :: Z, W ++ a :: X, ?_, by simp, by simp⟩
  rw [← List.rotate_rotate, hrot]
  have e : a :: (X ++ c :: Y) ++ b :: (Z ++ d :: W) = a :: X ++ c :: (Y ++ b :: Z ++ d :: W) := by
    simp
  rw [e, rotate_cons_append_cons']
  simp

/-- The ends of a crossing alternate. -/
theorem IsCrossing.alternate {T : List V} {a b c d : V} {Q : G.Walk a b} {R : G.Walk c d}
    (h : IsCrossing G T Q R) : Alternate T a b c d := by
  obtain ⟨⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, -⟩ := h
  obtain ⟨hil, hi'⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hrl, hr'⟩ := List.getElem?_eq_some_iff.mp hr
  obtain ⟨hjl, hj'⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hsl, hs'⟩ := List.getElem?_eq_some_iff.mp hs
  refine ⟨i, (T.drop (i + 1)).take (j - i - 1), T.drop (j + 1) ++ T.take i, ?_, ?_, ?_⟩
  · rw [List.rotate_eq_drop_append_take (by omega)]
    have e1 : T.drop i = T[i] :: T.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
    have e2 : T.drop (i + 1) = (T.drop (i + 1)).take (j - i - 1) ++ T[j] :: T.drop (j + 1) := by
      conv_lhs => rw [← List.take_append_drop (j - i - 1) (T.drop (i + 1))]
      congr 1
      rw [List.drop_drop, List.drop_eq_getElem_cons (by omega)]
      congr 2 <;> omega
    rw [e1, hi']
    nth_rw 1 [e2]
    rw [hj']
    simp
  · rw [← hr', List.mem_iff_getElem]
    exact ⟨r - i - 1, by simp; omega, by simp; congr 1; omega⟩
  · rw [← hs']
    refine List.mem_append_left _ (List.mem_iff_getElem.mpr ⟨s - j - 1, by simp; omega, ?_⟩)
    simp
    congr 1
    omega

/-- **Alternating ends give a crossing.** -/
theorem isCrossed_of_alternate' {T : List V} {a b c d : V} (h : Alternate T a b c d)
    (Q : G.Walk a b) (R : G.Walk c d) (hQ : IsTPath G T Q) (hR : IsTPath G T R)
    (hdisj : Q.support.Disjoint R.support) : IsCrossed G T := by
  obtain ⟨k, L₁, L₂, hrot, hc, hd⟩ := h
  exact isCrossed_of_alternate hrot hc hd Q R hQ hR hdisj

/-- The two ends of the second pair of alternating vertices are distinct. -/
theorem Alternate.ne {T : List V} (hnd : T.Nodup) {a b c d : V} (h : Alternate T a b c d) :
    c ≠ d := by
  obtain ⟨k, L₁, L₂, hrot, hc, hd⟩ := h
  have := (List.nodup_rotate (n := k)).mpr hnd
  rw [hrot, List.cons_append, List.nodup_cons, List.nodup_append] at this
  rintro rfl
  exact this.2.2.2 c hc c (List.mem_cons_of_mem _ hd) rfl

end GraphMinor.HP25
