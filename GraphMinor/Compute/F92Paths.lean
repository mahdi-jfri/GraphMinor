module

public import GraphMinor.Compute.F92OnePath

/-!
# One stored path for every input subwall

Run the single-subwall routine in input order. Each path has its own output array. The
marked bitsets and graph representation are preserved, so every later search has the same
input graph and wall data. The output arrays determine a family of `H`-paths.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Search the first `j` subwalls, writing their paths in distinct caller arrays. -/
def f92PathsUpTo (a_base base : ℕ) : ℕ → Cmd
  | 0 => .skip
  | j + 1 => .seq (f92PathsUpTo a_base base j)
      (f92OnePathProg (aHV a_base) (aSubV a_base j) (aSubIn a_base j) (aPath a_base j) base)

/-- Every completed search writes a valid path and preserves the bitsets and graph for
later searches. The input's non-dividing conditions are the only existence assumptions. -/
theorem f92PathsUpTo_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (lists : Fin x.n → List ℕ)
    (a_base base : ℕ) (hb : 100 ≤ base) (hspace : a_base + 13 + 3 * k ≤ base)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) :
    ∀ j (_hj : j ≤ k) {s : State}
      (_hadj : IsAdjList x.G.toSimpleGraph (base + 40) (base + 41) (base + 42) lists s)
      (_hent : (s.arrs (base + 42)).length < 2 ^ w)
      (_hrn : s.regs (base + 40) = x.n)
      (_hH : IsBitSet x.W.vertexFinset (aHV a_base) s)
      (_hsub : ∀ i : Fin k, IsBitSet (x.W_sub i).vertexFinset (aSubV a_base i.val) s ∧
        IsBitSet (x.W_sub i).insideFinset (aSubIn a_base i.val) s),
    ∃ s' t, Exec w (f92PathsUpTo a_base base j) s s' t ∧
      t ≤ 1 + j * (69 + 145 * x.n + 29 * totalAdjEntries lists) ∧
      (∀ i : Fin k, i.val < j → ∃ P, IsSubwallHPath x.W (x.W_sub i) P ∧
        s'.arrs (aPath a_base i.val) = P.map Fin.val) ∧
      IsAdjList x.G.toSimpleGraph (base + 40) (base + 41) (base + 42) lists s' ∧
      s'.regs (base + 40) = x.n ∧
      (s'.arrs (base + 42)).length = (s.arrs (base + 42)).length ∧
      (∀ b : ℕ, b < base → (∀ i < j, b ≠ aPath a_base i) → s'.arrs b = s.arrs b) ∧
      (∀ q < base, s'.regs q = s.regs q)
  | 0, _, s, hadj, _, hrn, _, _ => by
    exact ⟨s, 1, .skip s, by omega, fun _ hi => by omega,
      hadj, hrn, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | j + 1, hj, s, hadj, hent, hrn, hH, hsub => by
    have hjk : j < k := by omega
    obtain ⟨s₁, t₁, hex₁, ht₁, hpaths₁, hadj₁, hrn₁, hent₁, harr₁, hreg₁⟩ :=
      f92PathsUpTo_exec x lists a_base base hb hspace hw hn j (by omega)
        hadj hent hrn hH hsub
    have hH₁ : IsBitSet x.W.vertexFinset (aHV a_base) s₁ :=
      hH.of_arr_eq (harr₁ _ (by f92_omega) (fun i hi => by f92_omega))
    have hS₁ : IsBitSet (x.W_sub ⟨j, hjk⟩).vertexFinset (aSubV a_base j) s₁ :=
      (hsub ⟨j, hjk⟩).1.of_arr_eq
        (harr₁ _ (by f92_omega) (fun i hi => by f92_omega))
    have hI₁ : IsBitSet (x.W_sub ⟨j, hjk⟩).insideFinset (aSubIn a_base j) s₁ :=
      (hsub ⟨j, hjk⟩).2.of_arr_eq
        (harr₁ _ (by f92_omega) (fun i hi => by f92_omega))
    obtain ⟨s₂, t₂, P, hex₂, ht₂, hP, hout₂, hadj₂, hrn₂, hent₂, harr₂, hreg₂⟩ :=
      f92OnePathProg_exec x ⟨j, hjk⟩ lists (aHV a_base) (aSubV a_base j)
        (aSubIn a_base j) (aPath a_base j) base hb
        (by f92_omega) (by f92_omega) (by f92_omega) (by f92_omega)
        s₁ hadj₁ (by rw [hent₁]; exact hent) hrn₁ hw hn hH₁ hS₁ hI₁
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, hadj₂, hrn₂,
      hent₂.trans hent₁, ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul]; omega
    · intro i hi
      by_cases hij : i.val = j
      · have heq : i = ⟨j, hjk⟩ := Fin.ext hij
        subst i
        exact ⟨P, hP, hout₂⟩
      · obtain ⟨Q, hQ, houtQ⟩ := hpaths₁ i (by omega)
        exact ⟨Q, hQ, (harr₂ _ (by have := i.isLt; f92_omega) (by f92_omega)).trans houtQ⟩
    · intro b hbb hprev
      exact (harr₂ b hbb (hprev j (by omega))).trans
        (harr₁ b hbb (fun i hi => hprev i (by omega)))
    · intro q hqb
      exact (hreg₂ q hqb).trans (hreg₁ q hqb)

/-- The complete loop writes a family satisfying exactly the path hypothesis of
`isFSystem_fSegs`. The paths are read from the arrays the searches actually wrote. -/
theorem f92PathsProg_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (lists : Fin x.n → List ℕ)
    (a_base base : ℕ) (hb : 100 ≤ base) (hspace : a_base + 13 + 3 * k ≤ base)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) {s : State}
    (hadj : IsAdjList x.G.toSimpleGraph (base + 40) (base + 41) (base + 42) lists s)
    (hent : (s.arrs (base + 42)).length < 2 ^ w) (hrn : s.regs (base + 40) = x.n)
    (hH : IsBitSet x.W.vertexFinset (aHV a_base) s)
    (hsub : ∀ i : Fin k, IsBitSet (x.W_sub i).vertexFinset (aSubV a_base i.val) s ∧
      IsBitSet (x.W_sub i).insideFinset (aSubIn a_base i.val) s) :
    ∃ s' t, ∃ P : Fin k → List (Fin x.n),
      Exec w (f92PathsUpTo a_base base k) s s' t ∧
      t ≤ 1 + k * (69 + 145 * x.n + 29 * totalAdjEntries lists) ∧
      (∀ i, IsSubwallHPath x.W (x.W_sub i) (P i) ∧
        s'.arrs (aPath a_base i.val) = (P i).map Fin.val) ∧
      (∀ b : ℕ, b < base → (∀ i < k, b ≠ aPath a_base i) → s'.arrs b = s.arrs b) ∧
      (∀ q < base, s'.regs q = s.regs q) := by
  classical
  obtain ⟨s', t, hex, ht, hpaths, _, _, _, harr, hreg⟩ :=
    f92PathsUpTo_exec x lists a_base base hb hspace hw hn k le_rfl hadj hent hrn hH hsub
  let P : Fin k → List (Fin x.n) := fun i => Classical.choose (hpaths i i.isLt)
  exact ⟨s', t, P, hex, ht, fun i => Classical.choose_spec (hpaths i i.isLt), harr, hreg⟩

end GraphMinor.Compute.Alg92
