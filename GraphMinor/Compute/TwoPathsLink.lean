module

public import GraphMinor.Compute.TwoPathsExtSplice

/-!
# Two disjoint paths as a successor array

The program that undoes the collapse edges keeps the two paths `Q`, `R` of a crossing as one
successor array: entry `v` is one more than the vertex after `v` on its path, or `0` when `v` is the
last vertex of its path or on neither path (`linkArr`). Splicing a window into a path then costs
one write per vertex of the window (`nextOf_insert`), and the test whether `y z` is an edge of one
of the paths costs two reads (`linkArr_edge`).

* `nextOf l v`: one more than the entry after `v` in `l`, or `0`;
* `nextOf_insert`: putting `x` right after `p` changes the successors of `p` and `x` only;
* `nextOf_append`: putting `x` at the end changes the successor of the old last entry only;
* `nextOf_getElem`, `nextOf_last`: reading a path back from its successors.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- One more than the entry right after `v` in `l`, or `0` when there is none. For a list without
repeats this is the successor of `v`. -/
def nextOf : List ℕ → ℕ → ℕ
  | x :: y :: r, v => if v = x then y + 1 else nextOf (y :: r) v
  | _, _ => 0

/-- One more than the first entry of `B`, or `0` when `B` is empty. -/
def headSucc (B : List ℕ) : ℕ := (B.head?.map (· + 1)).getD 0

/-- The successor array of two disjoint lists `Q`, `R` of vertices below `V`. -/
def linkArr (V : ℕ) (Q R : List ℕ) : List ℕ := List.ofFn fun v : Fin V => nextOf Q v.1 + nextOf R v.1

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

public section

theorem nextOf_cons_self (x : ℕ) (B : List ℕ) : nextOf (x :: B) x = headSucc B := by
  cases B with
  | nil => rfl
  | cons y r => simp [nextOf, headSucc]

theorem nextOf_cons_ne {x v : ℕ} (B : List ℕ) (h : v ≠ x) : nextOf (x :: B) v = nextOf B v := by
  cases B with
  | nil => rfl
  | cons y r => simp [nextOf, h]

theorem nextOf_of_not_mem {v : ℕ} : ∀ {l : List ℕ}, v ∉ l → nextOf l v = 0
  | [], _ => rfl
  | x :: B, h => by
    rw [nextOf_cons_ne B (fun e => h (by subst e; exact List.mem_cons_self))]
    exact nextOf_of_not_mem (fun h' => h (List.mem_cons_of_mem _ h'))

theorem headSucc_append_cons (A B : List ℕ) (p : ℕ) (C : List ℕ) :
    headSucc (A ++ p :: B) = headSucc (A ++ p :: C) := by
  cases A <;> rfl

/-- **Putting `x` right after `p`.** -/
theorem nextOf_insert {p x : ℕ} {B : List ℕ} :
    ∀ {A : List ℕ}, (A ++ p :: x :: B).Nodup → ∀ v,
      nextOf (A ++ p :: x :: B) v =
        if v = p then x + 1 else if v = x then nextOf (A ++ p :: B) p else nextOf (A ++ p :: B) v
  | [], hnd, v => by
    have hpx : p ≠ x := fun h => by simp [h] at hnd
    simp only [List.nil_append]
    by_cases hvp : v = p
    · subst hvp; simp [nextOf]
    · rw [nextOf_cons_ne _ hvp, nextOf_cons_ne _ hvp]
      by_cases hvx : v = x
      · subst hvx; rw [nextOf_cons_self, nextOf_cons_self]; simp [hvp]
      · rw [nextOf_cons_ne _ hvx]; simp [hvp, hvx]
  | a :: A, hnd, v => by
    have ha : a ∉ A ++ p :: x :: B := (List.nodup_cons.mp hnd).1
    have hap : a ≠ p := fun h => ha (by simp [h])
    have hax : a ≠ x := fun h => ha (by simp [h])
    have ih := nextOf_insert (A := A) (List.nodup_cons.mp hnd).2
    simp only [List.cons_append]
    by_cases hva : v = a
    · subst hva
      rw [nextOf_cons_self, nextOf_cons_self, headSucc_append_cons A (x :: B) p B]
      simp [hap, hax]
    · rw [nextOf_cons_ne _ hva, ih v, nextOf_cons_ne _ hva, nextOf_cons_ne _ (Ne.symm hap)]

/-- **Putting `x` at the end.** -/
theorem nextOf_append {p x : ℕ} {A : List ℕ} (hnd : (A ++ [p, x]).Nodup) (v : ℕ) :
    nextOf (A ++ [p, x]) v = if v = p then x + 1 else nextOf (A ++ [p]) v := by
  rw [nextOf_insert (B := []) hnd v]
  have hx : x ∉ A ++ [p] := fun h => by
    have := (List.nodup_append.mp (show (A ++ [p] ++ [x]).Nodup by simpa using hnd)).2.2 x h x
      (by simp); exact this rfl
  by_cases hvp : v = p
  · simp [hvp]
  · by_cases hvx : v = x
    · subst hvx
      have h1 : nextOf (A ++ [p]) p = 0 := by
        induction A with
        | nil => rfl
        | cons a A ih =>
          have hap : p ≠ a := fun h => by simp [h] at hnd
          simp only [List.cons_append]
          rw [nextOf_cons_ne _ hap]
          exact ih (List.nodup_cons.mp hnd).2 (fun h => hx (List.mem_cons_of_mem _ h))
      simp [hvp, h1, nextOf_of_not_mem hx]
    · simp [hvp, hvx]

/-- The successor of an entry of a list without repeats. -/
theorem nextOf_mid {v : ℕ} {B : List ℕ} : ∀ {A : List ℕ}, (A ++ v :: B).Nodup →
    nextOf (A ++ v :: B) v = headSucc B
  | [], _ => nextOf_cons_self v B
  | a :: A, hnd => by
    have hva : v ≠ a := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
    simp only [List.cons_append]
    rw [nextOf_cons_ne _ hva]
    exact nextOf_mid (List.nodup_cons.mp hnd).2

theorem nextOf_getElem {l : List ℕ} (hnd : l.Nodup) {i : ℕ} (hi : i + 1 < l.length) :
    nextOf l l[i] = l[i + 1] + 1 := by
  have hsplit : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons]; simp
  have h := nextOf_mid (hsplit ▸ hnd)
  rw [← hsplit] at h
  rw [h, List.drop_eq_getElem_cons hi]
  rfl

theorem nextOf_last {l : List ℕ} (hnd : l.Nodup) (hl : l ≠ []) : nextOf l (l.getLast hl) = 0 := by
  have hsplit : l = l.dropLast ++ [l.getLast hl] := (List.dropLast_append_getLast hl).symm
  have h := nextOf_mid (B := []) (A := l.dropLast) (v := l.getLast hl) (by rw [← hsplit]; exact hnd)
  rw [← hsplit] at h
  rw [h]; rfl

theorem length_linkArr (V : ℕ) (Q R : List ℕ) : (linkArr V Q R).length = V := by simp [linkArr]

theorem linkArr_getElem {V : ℕ} {Q R : List ℕ} {v : ℕ} (hv : v < (linkArr V Q R).length) :
    (linkArr V Q R)[v] = nextOf Q v + nextOf R v := by
  simp [linkArr]

theorem linkArr_comm (V : ℕ) (Q R : List ℕ) : linkArr V Q R = linkArr V R Q := by
  simp only [linkArr, Nat.add_comm]

theorem linkArr_nil (V : ℕ) : linkArr V [] [] = List.replicate V 0 := by
  apply List.ext_getElem (by simp [linkArr])
  intro i h1 h2
  simp [linkArr, nextOf]

theorem linkArr_single (V : ℕ) (x : ℕ) (R : List ℕ) : linkArr V [x] R = linkArr V [] R := by
  simp [linkArr, nextOf]

/-- The successor array after putting `x` right after `p` in the first list. -/
theorem linkArr_insert {V p x : ℕ} {A B R : List ℕ} (hnd : (A ++ p :: x :: B).Nodup)
    (hpR : p ∉ R) (hxR : x ∉ R) (hp : p < V) (hx : x < V) :
    ((linkArr V (A ++ p :: B) R).set x (linkArr V (A ++ p :: B) R)[p]!).set p (x + 1) =
      linkArr V (A ++ p :: x :: B) R := by
  have hpx : p ≠ x := fun h => by
    have := (List.nodup_append.mp hnd).2.1; simp [h] at this
  have hget : (linkArr V (A ++ p :: B) R)[p]! = nextOf (A ++ p :: B) p := by
    rw [getElem!_pos (linkArr V (A ++ p :: B) R) p (by simp [length_linkArr, hp]),
      linkArr_getElem, nextOf_of_not_mem hpR, Nat.add_zero]
  rw [hget]
  apply List.ext_getElem (by simp [length_linkArr])
  intro i h1 h2
  rw [List.getElem_set, List.getElem_set, linkArr_getElem, linkArr_getElem, nextOf_insert hnd]
  by_cases hip : i = p
  · subst hip; simp [nextOf_of_not_mem hpR]
  · by_cases hix : i = x
    · subst hix; simp [Ne.symm hip, hip, nextOf_of_not_mem hxR]
    · simp [Ne.symm hip, Ne.symm hix, hip, hix]

/-- `y z` is a forward edge of one of two lists without repeats exactly when the successor of `y`
is `z`. -/
theorem nextOf_eq_iff {l : List ℕ} (hnd : l.Nodup) {y z : ℕ} :
    nextOf l y = z + 1 ↔ ∃ l₀ l₁, l = l₀ ++ y :: z :: l₁ := by
  constructor
  · intro h
    have hy : y ∈ l := by
      by_contra hy; rw [nextOf_of_not_mem hy] at h; omega
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hy
    rw [nextOf_mid hnd] at h
    cases B with
    | nil => simp [headSucc] at h
    | cons c B =>
      simp only [headSucc, List.head?_cons, Option.map_some, Option.getD_some,
        Nat.add_right_cancel_iff] at h
      exact ⟨A, B, by rw [h]⟩
  · rintro ⟨l₀, l₁, rfl⟩
    rw [nextOf_mid hnd]; rfl

end

end GraphMinor.Compute.TwoPaths

namespace GraphMinor.Compute.TwoPaths

public section

theorem nextOf_le {V : ℕ} : ∀ {l : List ℕ}, (∀ u ∈ l, u < V) → ∀ v, nextOf l v ≤ V
  | [], _, _ => Nat.zero_le _
  | [_], _, _ => Nat.zero_le _
  | x :: y :: r, h, v => by
    simp only [nextOf]
    split_ifs
    · have := h y (by simp); omega
    · exact nextOf_le (fun u hu => h u (List.mem_cons_of_mem _ hu)) v

end

end GraphMinor.Compute.TwoPaths
