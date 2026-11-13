module

public import GraphMinor.Compute.F92EncodeStep

/-!
# Encoding all segments

Append the stored segments in input order, each with its length, then prepend the segment
count. The resulting array is exactly `encSegs92`. The number of segments is a fixed input
parameter, so the repeated body copies have a cost bounded by a constant times the vertex count.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- The body encoding of the first `j` stored segments. -/
def f92EncodedUpTo {n k : ℕ} (Q : Fin k → List (Fin n)) (j : ℕ) : List ℕ :=
  ((List.finRange k).take j).flatMap (fun i => (Q i).length :: (Q i).map Fin.val)

theorem f92EncodedUpTo_succ {n k j : ℕ} (Q : Fin k → List (Fin n)) (hj : j < k) :
    f92EncodedUpTo Q (j + 1) = f92EncodedUpTo Q j ++
      ((Q ⟨j, hj⟩).length :: (Q ⟨j, hj⟩).map Fin.val) :=
  Alg91.flatMap_take_succ_finRange _ hj

theorem length_f92EncodedUpTo_le {n k : ℕ} (Q : Fin k → List (Fin n))
    (hQlen : ∀ i, (Q i).length ≤ n) :
    ∀ j, j ≤ k → (f92EncodedUpTo Q j).length ≤ j * (n + 1)
  | 0, _ => by simp [f92EncodedUpTo]
  | j + 1, hj => by
    rw [f92EncodedUpTo_succ Q (by omega), List.length_append, List.length_cons,
      List.length_map, Nat.add_mul, Nat.one_mul]
    have := length_f92EncodedUpTo_le Q hQlen j (by omega)
    have := hQlen ⟨j, by omega⟩
    omega

theorem words_f92EncodedUpTo {w n k : ℕ} (Q : Fin k → List (Fin n))
    (hQlen : ∀ i, (Q i).length ≤ n) (hn : n < 2 ^ w) (j : ℕ) :
    ∀ v ∈ f92EncodedUpTo Q j, v < 2 ^ w := by
  intro v hv
  obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact (hQlen i).trans_lt hn
  · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
    exact u.isLt.trans hn

/-- Append the first `j` segment records to the body. -/
def f92EncodeUpTo (k a_base r_base : ℕ) : ℕ → Cmd
  | 0 => .skip
  | j + 1 => .seq (f92EncodeUpTo k a_base r_base j) (f92EncodeOneProg k j a_base r_base)

/-- The body loop writes exactly the length-prefixed records in their input order. -/
theorem f92EncodeUpTo_exec {w n k : ℕ} (Q : Fin k → List (Fin n))
    (hQlen : ∀ i, (Q i).length ≤ n) (a_base r_base : ℕ)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hcap : 1 + k * (n + 1) < 2 ^ w) :
    ∀ j (_hj : j ≤ k) {s : State}
      (_hbody : s.arrs (aFbody a_base) = []) (_hrbody : s.regs r_base = 0)
      (_hQ : ∀ i : Fin k, s.arrs (aSeg92 a_base k i.val) = (Q i).map Fin.val),
    ∃ s' t, Exec w (f92EncodeUpTo k a_base r_base j) s s' t ∧
      t ≤ 1 + j * (34 * (k * (n + 1)) + 36 * n + 78) ∧
      s'.arrs (aFbody a_base) = f92EncodedUpTo Q j ∧
      s'.regs r_base = (f92EncodedUpTo Q j).length ∧
      (∀ a : ℕ, a ≠ aFbody a_base → a ≠ aTmp1 a_base → a ≠ aTmp2 a_base →
        s'.arrs a = s.arrs a) ∧ (∀ q < r_base, s'.regs q = s.regs q)
  | 0, _, s, hbody, hrbody, _ => by
    exact ⟨s, 1, .skip s, by omega, by simpa [f92EncodedUpTo] using hbody,
      by simpa [f92EncodedUpTo] using hrbody, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | j + 1, hj, s, hbody, hrbody, hQ => by
    have hjk : j < k := by omega
    obtain ⟨s₁, t₁, hex₁, ht₁, hbody₁, hrbody₁, harr₁, hreg₁⟩ :=
      f92EncodeUpTo_exec Q hQlen a_base r_base hw hn hcap j (by omega) hbody hrbody hQ
    have hQ₁ : s₁.arrs (aSeg92 a_base k j) = (Q ⟨j, hjk⟩).map Fin.val := by
      rw [harr₁ _ (by dsimp [aSeg92]; f92_omega) (by dsimp [aSeg92]; f92_omega)
        (by dsimp [aSeg92]; f92_omega)]
      exact hQ ⟨j, hjk⟩
    have hlennew := length_f92EncodedUpTo_le Q hQlen (j + 1) hj
    rw [f92EncodedUpTo_succ Q hjk, List.length_append, List.length_cons, List.length_map] at hlennew
    have hmul := Nat.mul_le_mul_right (n + 1) hj
    obtain ⟨s₂, t₂, hex₂, ht₂, hbody₂, hrbody₂, harr₂, hreg₂⟩ :=
      f92EncodeOneProg_exec Q ⟨j, hjk⟩ (f92EncodedUpTo Q j) a_base r_base hw hn
        (words_f92EncodedUpTo Q hQlen hn j) (by omega) hbody₁ hQ₁ hrbody₁
    have hlenold : (f92EncodedUpTo Q j).length ≤ k * (n + 1) :=
      (length_f92EncodedUpTo_le Q hQlen j (by omega)).trans
        (Nat.mul_le_mul_right (n + 1) (by omega))
    have hcost : t₂ ≤ 34 * (k * (n + 1)) + 36 * n + 78 := by
      have := Nat.mul_le_mul_left 34 hlenold
      have := Nat.mul_le_mul_left 36 (hQlen ⟨j, hjk⟩)
      omega
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul]; omega
    · simpa only [f92EncodedUpTo_succ Q hjk] using hbody₂
    · simpa only [f92EncodedUpTo_succ Q hjk] using hrbody₂
    · intro a hB h1 h2
      exact (harr₂ a hB h1 h2).trans (harr₁ a hB h1 h2)
    · intro q hq
      exact (hreg₂ q hq).trans (hreg₁ q hq)

/-- Initialize the body, append all records and write the counted encoding. -/
def f92EncodeProg (k a_base a_F r_base : ℕ) : Cmd :=
  .seq (.alloc (aFbody a_base) (.const 0))
    (.seq (.assign r_base (.const 0))
      (.seq (f92EncodeUpTo k a_base r_base k)
        (prependWordProg (.const k) (aFbody a_base) a_F r_base (r_base + 2))))

/-- Serialization gives `encSegs92` of the segment family, with no extra padding. -/
theorem f92EncodeProg_exec {w n k : ℕ} (Q : Fin k → List (Fin n))
    (hQlen : ∀ i, (Q i).length ≤ n) (a_base a_F r_base : ℕ) (haF : a_F < a_base)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hcap : 1 + k * (n + 1) < 2 ^ w)
    {s : State} (hQ : ∀ i : Fin k, s.arrs (aSeg92 a_base k i.val) = (Q i).map Fin.val) :
    ∃ s' t, Exec w (f92EncodeProg k a_base a_F r_base) s s' t ∧
      t ≤ 22 + k * (34 * (k * (n + 1)) + 36 * n + 78) + 18 * (k * (n + 1)) ∧
      s'.arrs a_F = encSegs92 (List.ofFn Q) ∧
      (∀ a : ℕ, a < a_base → a ≠ a_F → s'.arrs a = s.arrs a) ∧
      (∀ q < r_base, s'.regs q = s.regs q) := by
  let s₁ := s.setArr (aFbody a_base) []
  have hex₁ : Exec w (.alloc (aFbody a_base) (.const 0)) s s₁ 1 :=
    Exec.alloc (m := 0) (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hQ₂ (i : Fin k) : s₂.arrs (aSeg92 a_base k i.val) = (Q i).map Fin.val := by
    simp only [s₂, State.setReg_arrs, s₁, State.setArr_arrs_ne _ _
      (show aSeg92 a_base k i.val ≠ aFbody a_base by dsimp [aSeg92]; f92_omega)]
    exact hQ i
  obtain ⟨s₃, t₃, hex₃, ht₃, hbody₃, hrbody₃, harr₃, hreg₃⟩ :=
    f92EncodeUpTo_exec Q hQlen a_base r_base hw hn hcap k le_rfl (s := s₂)
      (by simp [s₂, s₁]) (by simp [s₂]) hQ₂
  have hbodylen := length_f92EncodedUpTo_le Q hQlen k le_rfl
  have hk : k < 2 ^ w := by
    have hk' := Nat.mul_le_mul_left k (show 1 ≤ n + 1 by omega)
    simp only [Nat.mul_one] at hk'
    omega
  obtain ⟨s₄, t₄, hex₄, ht₄, hout₄, harr₄, hreg₄⟩ :=
    prependWordProg_exec (tag := k) (.const k) (aFbody a_base) a_F r_base (r_base + 2)
      (by f92_omega) (by omega) (f92EncodedUpTo Q k)
      (words_f92EncodedUpTo Q hQlen hn k) hw (by omega)
      (by intro v; simp [Expr.eval, checkWord, hk]) hbody₃ hrbody₃
  dsimp only [Expr.cost] at ht₄
  refine ⟨s₄, 1 + (2 + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, ?_, ?_, ?_⟩
  · have := Nat.mul_le_mul_left 18 hbodylen
    omega
  · simpa [encSegs92, f92EncodedUpTo, List.ofFn_eq_map, List.flatMap_map,
      List.drop_of_length_le, List.take_of_length_le (show (List.finRange k).length ≤ k by simp)] using hout₄
  · intro a haa haout
    rw [harr₄ a haout, harr₃ a (by f92_omega) (by f92_omega) (by f92_omega)]
    simp [s₂, s₁, show a ≠ aFbody a_base by f92_omega]
  · intro q hq
    rw [hreg₄ q (Or.inl (by omega)), hreg₃ q hq]
    simp [s₂, s₁, State.setReg, show q ≠ r_base by omega]

end GraphMinor.Compute.Alg92
