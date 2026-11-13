module

public import GraphMinor.Compute.Algorithm99OrderCounts
public import GraphMinor.Compute.Algorithm99OrderPrefix
public import GraphMinor.Compute.Algorithm99OrderScatter

/-!
# Stable grouping of the leaf assignments for Algorithm (9.9)

The program counts tails, forms bucket starts, then scatters the leaf
assignments. It takes time linear in the number of vertices and edges. Its
specification records the value at each stable bucket position, so the exact
parallel-edge order is retained.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Arrays `a`, `a + 1` hold the keys and values. Scratch arrays `a + 2`,
`a + 3` hold counts and cursors. Register `r_n` supplies the vertex count
before the counting pass. The result is written to `a + 4`. -/
def alg99TailSortProg (a r r_n : ℕ) : Cmd :=
  .seq (alg99TailCountProg a (a + 2) r r_n)
    (.seq (alg99BucketStartProg (a + 2) (a + 3) r)
      (alg99ScatterProg a (a + 1) (a + 3) (a + 4) r))

/-- The three passes stably group arbitrary word-valued assignments by their
vertex keys. The sources remain intact. The only assumptions are the displayed
input arrays, equal lengths, and word bounds. -/
theorem alg99TailSortProg_exec {w n : ℕ} (keys : List (Fin n)) (vals : List ℕ)
    (a r r_n : ℕ) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlen : keys.length < 2 ^ w)
    (hvlen : vals.length = keys.length) (hvword : ∀ v ∈ vals, v < 2 ^ w)
    (s : State) (hkeys : s.arrs a = keys.map Fin.val) (hvals : s.arrs (a + 1) = vals)
    (hrn : s.regs r_n = n) :
    ∃ s' t, Exec w (alg99TailSortProg a r r_n) s s' t ∧
      t ≤ 50 * (n + keys.length + 1) ∧
      (s'.arrs (a + 4)).length = keys.length ∧
      (∀ i : Fin keys.length, (s'.arrs (a + 4)).getD (alg99BucketPosition keys i) 0 =
        vals[i.1]'(by rw [hvlen]; exact i.2)) ∧
      (∀ b : ℕ, b ≠ a + 2 → b ≠ a + 3 → b ≠ a + 4 → s'.arrs b = s.arrs b) ∧
      (∀ j : ℕ, j ≠ r → j ≠ r + 1 → j ≠ r + 2 → s'.regs j = s.regs j) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hc₁, ha₁, hr₁⟩ :=
    alg99TailCountProg_exec keys a (a + 2) r r_n (by omega) hw hn hlen s hkeys hrn
  obtain ⟨s₂, t₂, hex₂, ht₂, hs₂, _, ha₂, hr₂⟩ :=
    alg99BucketStartProg_exec (List.ofFn (fun v : Fin n => keys.count v))
      (a + 2) (a + 3) r (by omega) hw (by simpa using hn)
      (by simpa only [alg99_sum_counts] using hlen) s₁ hc₁
  have hcursor : s₂.arrs (a + 3) = List.ofFn (alg99BucketStart keys) := by
    rw [hs₂]
    apply List.ext_getElem (by simp)
    intro j hj hj'
    have hjn : j < n := by simpa using hj'
    simp only [List.getElem_ofFn]
    exact alg99_prefix_counts keys j (Nat.le_of_lt hjn)
  obtain ⟨s₃, t₃, hex₃, ht₃, hlen₃, hout₃, _, ha₃, hr₃⟩ :=
    alg99ScatterProg_exec keys vals a (a + 1) (a + 3) (a + 4) r
      (by omega) (by omega) (by omega) (by omega) (by omega)
      hw hn hlen hvlen hvword s₂
      ((ha₂ a (by omega)).trans ((ha₁ a (by omega)).trans hkeys))
      ((ha₂ (a + 1) (by omega)).trans ((ha₁ (a + 1) (by omega)).trans hvals)) hcursor
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), ?_, hlen₃, hout₃, ?_, ?_⟩
  · simp only [List.length_ofFn] at ht₂
    omega
  · intro b hb2 hb3 hb4
    exact (ha₃ b hb3 hb4).trans ((ha₂ b hb3).trans (ha₁ b hb2))
  · intro j hj hj1 hj2
    exact (hr₃ j hj hj1 hj2).trans ((hr₂ j hj hj1).trans (hr₁ j hj hj1 hj2))

end GraphMinor.Compute
