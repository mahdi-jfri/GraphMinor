module

public import GraphMinor.Compute.TwoPathsUndoRec

/-!
# The record layout and the splice over many records

Facts about lists used by the program that undoes all collapse records (`TwoPathsUndoProg.lean`):

* `offT2 rs j`: the offset of record `j` in `encodeT2 rs`, and `drop_offT2`: the records from `j`
  on start there;
* `spliceT2All_take_succ`, `SpliceAllOK.get`: the splice of the first `m + 1` records is one more
  step after the first `m`, and `SpliceOK` holds at each step;
* `spliceT2All_mem`, `spliceT2All_head?`: the vertices after the splices are old vertices or
  vertices of windows, and the first vertex of each path does not change.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- The offset of record `j` in `encodeT2 rs`. -/
def offT2 (rs : List (ℕ × ℕ × List ℕ)) (j : ℕ) : ℕ :=
  ((rs.take j).map fun r => 3 + r.2.2.length).sum

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

public section

theorem offT2_zero (rs : List (ℕ × ℕ × List ℕ)) : offT2 rs 0 = 0 := by simp [offT2]

theorem encodeT2_append : ∀ (l l' : List (ℕ × ℕ × List ℕ)),
    encodeT2 (l ++ l') = encodeT2 l ++ encodeT2 l'
  | [], _ => rfl
  | (y, z, N) :: l, l' => by simp [encodeT2, encodeT2_append l l']

theorem length_encodeT2 : ∀ (l : List (ℕ × ℕ × List ℕ)),
    (encodeT2 l).length = (l.map fun r => 3 + r.2.2.length).sum
  | [] => rfl
  | (y, z, N) :: l => by simp [encodeT2, length_encodeT2 l]; omega

theorem offT2_eq (rs : List (ℕ × ℕ × List ℕ)) (j : ℕ) :
    offT2 rs j = (encodeT2 (rs.take j)).length := by
  rw [length_encodeT2]; rfl

theorem drop_offT2 (rs : List (ℕ × ℕ × List ℕ)) (j : ℕ) :
    (encodeT2 rs).drop (offT2 rs j) = encodeT2 (rs.drop j) := by
  have h : encodeT2 rs = encodeT2 (rs.take j) ++ encodeT2 (rs.drop j) := by
    rw [← encodeT2_append, List.take_append_drop]
  rw [offT2_eq, h, List.drop_left]

theorem offT2_length (rs : List (ℕ × ℕ × List ℕ)) :
    offT2 rs rs.length = (encodeT2 rs).length := by
  rw [offT2_eq, List.take_length]

/-- Record `j` starts at `offT2 rs j`. -/
theorem drop_offT2_get {rs : List (ℕ × ℕ × List ℕ)} {j : ℕ} (hj : j < rs.length) :
    (encodeT2 rs).drop (offT2 rs j) =
      rs[j].1 :: rs[j].2.1 :: rs[j].2.2.length :: (rs[j].2.2 ++ encodeT2 (rs.drop (j + 1))) := by
  rw [drop_offT2, List.drop_eq_getElem_cons hj]
  rfl

theorem offT2_succ {rs : List (ℕ × ℕ × List ℕ)} {j : ℕ} (hj : j < rs.length) :
    offT2 rs (j + 1) = offT2 rs j + 3 + rs[j].2.2.length := by
  simp only [offT2, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem offT2_lt {rs : List (ℕ × ℕ × List ℕ)} {j : ℕ} (hj : j < rs.length) :
    offT2 rs j < (encodeT2 rs).length := by
  have h := congrArg List.length (drop_offT2_get hj)
  simp only [List.length_drop, List.length_cons] at h
  omega

theorem length_le_encodeT2 (rs : List (ℕ × ℕ × List ℕ)) : 3 * rs.length ≤ (encodeT2 rs).length := by
  induction rs with
  | nil => simp [encodeT2]
  | cons r rs ih => obtain ⟨y, z, N⟩ := r; simp [encodeT2]; omega

/-- The splice of the first `m + 1` steps. -/
theorem spliceT2All_take_succ : ∀ (l : List (ℕ × ℕ × List ℕ)) (qr : List ℕ × List ℕ) {m : ℕ}
    (hm : m < l.length), spliceT2All (l.take (m + 1)) qr =
      spliceT2Lists l[m].1 l[m].2.1 l[m].2.2 (spliceT2All (l.take m) qr).1
        (spliceT2All (l.take m) qr).2
  | [], _, _, hm => by simp at hm
  | (y, z, N) :: l, qr, 0, _ => by simp [spliceT2All]
  | (y, z, N) :: l, qr, m + 1, hm => by
    simp only [List.take_succ_cons, spliceT2All, List.getElem_cons_succ]
    exact spliceT2All_take_succ l _ (by simpa using hm)

theorem SpliceAllOK.get : ∀ {l : List (ℕ × ℕ × List ℕ)} {qr : List ℕ × List ℕ},
    SpliceAllOK l qr → ∀ {m : ℕ} (hm : m < l.length),
      SpliceOK l[m].1 l[m].2.1 l[m].2.2 (spliceT2All (l.take m) qr).1 (spliceT2All (l.take m) qr).2
  | [], _, _, _, hm => by simp at hm
  | (y, z, N) :: l, qr, h, 0, _ => by simpa [spliceT2All] using h.1
  | (y, z, N) :: l, qr, h, m + 1, hm => by
    simp only [List.take_succ_cons, spliceT2All, List.getElem_cons_succ]
    exact SpliceAllOK.get h.2 (by simpa using hm)

theorem SpliceAllOK.final : ∀ {l : List (ℕ × ℕ × List ℕ)} {qr : List ℕ × List ℕ},
    SpliceAllOK l qr → (spliceT2All l qr).1.Nodup ∧ (spliceT2All l qr).2.Nodup ∧
      (spliceT2All l qr).1.Disjoint (spliceT2All l qr).2
  | [], _, h => h
  | (y, z, N) :: l, qr, h => SpliceAllOK.final (l := l) h.2

theorem rule2PocketChain_mem {y z v : ℕ} {N l : List ℕ} (hv : v ∈ HP25.rule2PocketChain y z N l)
    (hy : y ∈ l) (hz : z ∈ l) : v ∈ l ∨ v ∈ N := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  have hy' : v ≠ y := fun e => h1 (e ▸ hy)
  have hz' : v ≠ z := fun e => h1 (e ▸ hz)
  have ht : ∀ n, v ∉ l.take n := fun _ h => h1 (List.mem_of_mem_take h)
  have hd : ∀ n, v ∉ l.drop n := fun _ h => h1 (List.mem_of_mem_drop h)
  unfold HP25.rule2PocketChain at hv
  split_ifs at hv <;> simp [h2, hy', hz', ht, hd] at hv

theorem spliceT2Lists_mem {y z v : ℕ} {N Q R : List ℕ}
    (hv : v ∈ (spliceT2Lists y z N Q R).1 ∨ v ∈ (spliceT2Lists y z N Q R).2) :
    v ∈ Q ∨ v ∈ R ∨ v ∈ N := by
  unfold spliceT2Lists at hv
  split_ifs at hv with h1 h2
  · have he := ((t2Uses_iff _ _ _ _).mp h1).2
    rcases hv with hv | hv
    · rcases rule2PocketChain_mem hv he.mem_left he.mem_right with h | h <;> simp [h]
    · exact Or.inr (Or.inl hv)
  · have he := ((t2Uses_iff _ _ _ _).mp h2).2
    rcases hv with hv | hv
    · exact Or.inl hv
    · rcases rule2PocketChain_mem hv he.mem_left he.mem_right with h | h <;> simp [h]
  · rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)

theorem spliceT2All_mem : ∀ {l : List (ℕ × ℕ × List ℕ)} {qr : List ℕ × List ℕ} {v : ℕ},
    v ∈ (spliceT2All l qr).1 ∨ v ∈ (spliceT2All l qr).2 →
      v ∈ qr.1 ∨ v ∈ qr.2 ∨ ∃ r ∈ l, v ∈ r.2.2
  | [], _, _, hv => by
    rcases hv with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | (y, z, N) :: l, qr, v, hv => by
    rcases spliceT2All_mem (l := l) hv with h | h | ⟨r, hr, h⟩
    · rcases spliceT2Lists_mem (Or.inl h) with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨(y, z, N), by simp, h'⟩)
    · rcases spliceT2Lists_mem (Or.inr h) with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨(y, z, N), by simp, h'⟩)
    · exact Or.inr (Or.inr ⟨r, by simp [hr], h⟩)

theorem head?_take_idxOf_append {a : ℕ} {l : List ℕ} (ha : a ∈ l) (X : List ℕ) :
    (l.take (l.idxOf a) ++ a :: X).head? = l.head? := by
  cases l with
  | nil => simp at ha
  | cons b l =>
    by_cases hab : b = a
    · subst hab; simp
    · simp [List.idxOf_cons_ne _ hab]

theorem rule2PocketChain_head? {y z : ℕ} {N l : List ℕ} (hy : y ∈ l) (hz : z ∈ l) :
    (HP25.rule2PocketChain y z N l).head? = l.head? := by
  unfold HP25.rule2PocketChain
  split_ifs
  · have := head?_take_idxOf_append hy (N ++ [z] ++ l.drop (l.idxOf z + 1))
    simpa using this
  · have := head?_take_idxOf_append hz (N.reverse ++ [y] ++ l.drop (l.idxOf y + 1))
    simpa using this

theorem spliceT2Lists_head? {y z : ℕ} {N Q R : List ℕ} :
    (spliceT2Lists y z N Q R).1.head? = Q.head? ∧ (spliceT2Lists y z N Q R).2.head? = R.head? := by
  unfold spliceT2Lists
  split_ifs with h1 h2
  · have he := ((t2Uses_iff _ _ _ _).mp h1).2
    exact ⟨rule2PocketChain_head? he.mem_left he.mem_right, rfl⟩
  · have he := ((t2Uses_iff _ _ _ _).mp h2).2
    exact ⟨rfl, rule2PocketChain_head? he.mem_left he.mem_right⟩
  · exact ⟨rfl, rfl⟩

theorem spliceT2All_head? : ∀ (l : List (ℕ × ℕ × List ℕ)) (qr : List ℕ × List ℕ),
    (spliceT2All l qr).1.head? = qr.1.head? ∧ (spliceT2All l qr).2.head? = qr.2.head?
  | [], _ => ⟨rfl, rfl⟩
  | (y, z, N) :: l, qr => by
    obtain ⟨h1, h2⟩ := spliceT2All_head? l (spliceT2Lists y z N qr.1 qr.2)
    exact ⟨h1.trans spliceT2Lists_head?.1, h2.trans spliceT2Lists_head?.2⟩

end

end GraphMinor.Compute.TwoPaths
