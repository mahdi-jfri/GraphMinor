module

public import GraphMinor.Compute.F92SegmentArrays

/-!
# Building the stored segments in reverse input order

The segment vertex bitset describes the already processed suffix of subwalls. Each new
step reads its stored path, cuts it at the first meeting outside the wall, extends the
bitset and writes its own segment array. Thus the resulting arrays are the segments of
the segment-only computation, in their original input order.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Process `j` paths from the last input index towards the first. -/
def f92BuildUpTo (k a_base r_base : ℕ) : ℕ → Cmd
  | 0 => .skip
  | j + 1 => .seq (f92BuildUpTo k a_base r_base j)
      (f92SegmentStepProg (aPath a_base (k - (j + 1))) (aHV a_base) (aFset a_base)
        (aSeg92 a_base k (k - (j + 1))) r_base)

/-- Every stored segment is the prefix prescribed by `f92Segments`, and the bitset
contains exactly the processed segment vertices. Only the actual path inputs are assumed. -/
theorem f92BuildUpTo_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (P : Fin k → List (Fin x.n))
    (hP : ∀ i, IsSubwallHPath x.W (x.W_sub i) (P i)) (a_base r_base : ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) :
    ∀ j (_hj : j ≤ k) {s : State}
      (_hH : IsBitSet x.W.vertexFinset (aHV a_base) s)
      (_hF : IsBitSet (∅ : Finset (Fin x.n)) (aFset a_base) s)
      (_hpaths : ∀ i : Fin k, s.arrs (aPath a_base i.val) = (P i).map Fin.val),
    ∃ s' t, Exec w (f92BuildUpTo k a_base r_base j) s s' t ∧
      t ≤ 1 + j * (25 + 60 * x.n) ∧
      IsBitSet (f92Segments x.W P ((List.finRange k).drop (k - j))).flatten.toFinset
        (aFset a_base) s' ∧
      (∀ i : Fin k, k - j ≤ i.val →
        s'.arrs (aSeg92 a_base k i.val) = (f92SegmentAt x.W P i).map Fin.val) ∧
      (∀ a : ℕ, a ≠ aFset a_base →
        (∀ i : ℕ, k - j ≤ i → i < k → a ≠ aSeg92 a_base k i) → s'.arrs a = s.arrs a) ∧
      (∀ q < r_base, s'.regs q = s.regs q)
  | 0, _, s, _, hF, _ => by
    refine ⟨s, 1, .skip s, by omega, ?_, fun i hi => by omega,
      fun _ _ _ => rfl, fun _ _ => rfl⟩
    simpa [List.drop_of_length_le (show (List.finRange k).length ≤ k by simp), f92Segments] using hF
  | j + 1, hj, s, hH, hF, hpaths => by
    have hjk : j < k := by omega
    let i := k - (j + 1)
    have hi : i < k := by dsimp [i]; omega
    have hi_next : i + 1 = k - j := by dsimp [i]; omega
    obtain ⟨s₁, t₁, hex₁, ht₁, hF₁, hsegs₁, harr₁, hreg₁⟩ :=
      f92BuildUpTo_exec x P hP a_base r_base hw hn j (by omega) hH hF hpaths
    have hH₁ : IsBitSet x.W.vertexFinset (aHV a_base) s₁ :=
      hH.of_arr_eq (harr₁ _ (by f92_omega)
        (fun z _ _ => by dsimp [aSeg92]; f92_omega))
    have hpath₁ : s₁.arrs (aPath a_base i) = (P ⟨i, hi⟩).map Fin.val := by
      rw [harr₁ _ (by f92_omega) (fun z _ _ => by dsimp [aSeg92]; f92_omega)]
      exact hpaths ⟨i, hi⟩
    have hPlen : (P ⟨i, hi⟩).length ≤ x.n := by
      obtain ⟨_, _, hnd, _⟩ := (hP ⟨i, hi⟩).1
      simpa using hnd.length_le_card
    let F := (f92Segments x.W P ((List.finRange k).drop (k - j))).flatten.toFinset
    obtain ⟨s₂, t₂, hex₂, ht₂, hF₂, hout₂, harr₂, hreg₂⟩ :=
      f92SegmentStepProg_exec x.W F (P ⟨i, hi⟩) (aPath a_base i) (aHV a_base)
        (aFset a_base) (aSeg92 a_base k i) r_base
        (by f92_omega) (by dsimp [aSeg92]; f92_omega)
        (by dsimp [aSeg92]; f92_omega) hw hn (hPlen.trans_lt hn) hpath₁ hH₁ hF₁
    have hQ : f92Prefix x.W F (P ⟨i, hi⟩) = f92SegmentAt x.W P ⟨i, hi⟩ := by
      simp only [f92SegmentAt, hi_next, F]
    have hvertices : F ∪ (f92Prefix x.W F (P ⟨i, hi⟩)).toFinset =
        (f92Segments x.W P ((List.finRange k).drop i)).flatten.toFinset := by
      rw [hQ, f92Segments_suffix_vertices x.W P hi, hi_next]
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul]
      have := Nat.mul_le_mul_left 60 hPlen
      omega
    · exact hvertices ▸ hF₂
    · intro b hb
      by_cases hbi : b.val = i
      · have heq : b = ⟨i, hi⟩ := Fin.ext hbi
        subst b
        simpa only [hQ] using hout₂
      · have hbp : k - j ≤ b.val := by dsimp [i] at hbi; omega
        rw [harr₂ _ (by dsimp [aSeg92]; f92_omega)
          (by dsimp [aSeg92]; omega)]
        exact hsegs₁ b hbp
    · intro a haF hprev
      exact (harr₂ a haF (hprev i (by rfl) hi)).trans
        (harr₁ a haF (fun z hz hzk => hprev z (by omega) hzk))
    · intro q hq
      exact (hreg₂ q hq).trans (hreg₁ q hq)

/-- Initialize the segment bitset and build all segment arrays. -/
def f92BuildProg (k a_base r_n r_base : ℕ) : Cmd :=
  .seq (.alloc (aFset a_base) (.reg r_n)) (f92BuildUpTo k a_base r_base k)

/-- The final segment arrays encode exactly `fSegs x P`, one array for each input index.
Only the previously computed path family and its array representation are required. -/
theorem f92BuildProg_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (hr : 1 ≤ r) (P : Fin k → List (Fin x.n))
    (hP : ∀ i, IsSubwallHPath x.W (x.W_sub i) (P i))
    (a_base r_n r_base : ℕ) (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    {s : State} (hrn : s.regs r_n = x.n)
    (hH : IsBitSet x.W.vertexFinset (aHV a_base) s)
    (hpaths : ∀ i : Fin k, s.arrs (aPath a_base i.val) = (P i).map Fin.val) :
    ∃ s' t, Exec w (f92BuildProg k a_base r_n r_base) s s' t ∧
      t ≤ 2 + x.n + k * (25 + 60 * x.n) ∧
      (∀ i : Fin k, s'.arrs (aSeg92 a_base k i.val) = (f92SegmentAt x.W P i).map Fin.val) ∧
      List.ofFn (f92SegmentAt x.W P) = fSegs x P ∧
      (∀ a : ℕ, a ≠ aFset a_base →
        (∀ i < k, a ≠ aSeg92 a_base k i) → s'.arrs a = s.arrs a) ∧
      (∀ q < r_base, s'.regs q = s.regs q) := by
  let s₁ := s.setArr (aFset a_base) (List.replicate x.n 0)
  have hex₁ : Exec w (.alloc (aFset a_base) (.reg r_n)) s s₁ (1 + x.n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn])
  have hH₁ : IsBitSet x.W.vertexFinset (aHV a_base) s₁ :=
    hH.of_arr_eq (by simp [s₁])
  have hF₁ : IsBitSet (∅ : Finset (Fin x.n)) (aFset a_base) s₁ :=
    IsBitSet.empty_of_replicate (by simp [s₁])
  have hpaths₁ (i : Fin k) : s₁.arrs (aPath a_base i.val) = (P i).map Fin.val := by
    rw [show s₁.arrs (aPath a_base i.val) = s.arrs (aPath a_base i.val) by
      simp [s₁, show aPath a_base i.val ≠ aFset a_base by f92_omega]]
    exact hpaths i
  obtain ⟨s₂, t₂, hex₂, ht₂, _, hsegs₂, harr₂, hreg₂⟩ :=
    f92BuildUpTo_exec x P hP a_base r_base hw hn k le_rfl hH₁ hF₁ hpaths₁
  refine ⟨s₂, (1 + x.n) + t₂, .seq hex₁ hex₂, by omega,
    fun i => hsegs₂ i (by omega), ?_, ?_, hreg₂⟩
  · exact (f92Segments_eq_ofFn x.W P).symm.trans (f92Segments_eq_fSegs x hr P hP)
  · intro a haF haseg
    rw [harr₂ a haF (fun i _ hi => haseg i hi)]
    simp [s₁, haF]

end GraphMinor.Compute.Alg92
