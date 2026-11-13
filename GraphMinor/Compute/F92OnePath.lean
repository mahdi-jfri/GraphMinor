module

public import GraphMinor.Compute.F92Rename
public import GraphMinor.Compute.F92Labels
public import GraphMinor.Compute.F92Sources

/-!
# Finding and writing one subwall path

Read the main-wall, subwall and inside bitsets, prepare labels and sources, then search and
trace in a disjoint scratch block. Copy the resulting path to the designated output array.
All other caller arrays and all lower registers are preserved, so the routine can be repeated
for the remaining subwalls.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Prepare and run a subwall search using a scratch block whose graph is already stored. -/
def f92OnePathProg (a_H a_S a_I out base : ℕ) : Cmd :=
  .seq (f92LabelsProg a_H a_S a_I (base + 60) (base + 40) (base + 80))
    (.seq (f92SourcesProg a_I (base + 65) (base + 63) (base + 40) (base + 80))
      (.seq (f92SearchHiProg base)
        (copyArrProg (base + 64) out (base + 80) (base + 81))))

/-- For each non-dividing input subwall, the routine writes an `H`-path in linear time.
The graph representation is preserved and no label or source preparation is assumed. -/
theorem f92OnePathProg_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (a : Fin k) (lists : Fin x.n → List ℕ)
    (a_H a_S a_I out base : ℕ) (hb : 100 ≤ base)
    (hHbase : a_H < base) (hSbase : a_S < base) (hIbase : a_I < base) (houtbase : out < base)
    (s : State)
    (hadj : IsAdjList x.G.toSimpleGraph (base + 40) (base + 41) (base + 42) lists s)
    (hent : (s.arrs (base + 42)).length < 2 ^ w) (hrn : s.regs (base + 40) = x.n)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w)
    (hH : IsBitSet x.W.vertexFinset a_H s)
    (hS : IsBitSet (x.W_sub a).vertexFinset a_S s)
    (hI : IsBitSet (x.W_sub a).insideFinset a_I s) :
    ∃ s' t, ∃ P : List (Fin x.n), Exec w (f92OnePathProg a_H a_S a_I out base) s s' t ∧
      t ≤ 69 + 145 * x.n + 29 * totalAdjEntries lists ∧
      IsSubwallHPath x.W (x.W_sub a) P ∧ s'.arrs out = P.map Fin.val ∧
      IsAdjList x.G.toSimpleGraph (base + 40) (base + 41) (base + 42) lists s' ∧
      s'.regs (base + 40) = x.n ∧
      (s'.arrs (base + 42)).length = (s.arrs (base + 42)).length ∧
      (∀ b : ℕ, b < base → b ≠ out → s'.arrs b = s.arrs b) ∧
      (∀ q < base, s'.regs q = s.regs q) := by
  have hn' : x.n < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hlab₁, harr₁, hreg₁⟩ :=
    f92LabelsProg_exec x.W (x.W_sub a) a_H a_S a_I (base + 60) (base + 40) (base + 80)
      (by omega) (by omega) (by omega) (by omega) (by omega) hn' hH hS hI hrn
  obtain ⟨s₂, t₂, hex₂, ht₂, hsrc₂, harr₂, hreg₂⟩ :=
    f92SourcesProg_exec (x.W_sub a).insideFinset a_I (base + 65) (base + 63)
      (base + 40) (base + 80) (by omega) (by omega) (by omega) (by omega) hn'
      (hI.of_arr_eq (harr₁ a_I (by omega)))
      ((hreg₁ (base + 40) (by omega)).trans hrn)
  let src := f92SourcesUpTo (x.W_sub a).insideFinset x.n
  have hsrcLen : src.length ≤ x.n := length_f92SourcesUpTo_le _ _
  have hfixed₂ (b : ℕ) (hb60 : b ≠ base + 60) (hb63 : b ≠ base + 63)
      (hb65 : b ≠ base + 65) : s₂.arrs b = s.arrs b :=
    (harr₂ b hb65 hb63).trans (harr₁ b hb60)
  have hadj₂ := hadj.of_arrs_eq
    (hfixed₂ (base + 40) (by omega) (by omega) (by omega))
    (hfixed₂ (base + 41) (by omega) (by omega) (by omega))
    (hfixed₂ (base + 42) (by omega) (by omega) (by omega))
  obtain ⟨s₃, t₃, P, hex₃, ht₃, hP, hout₃, hreg₃, harr₃⟩ :=
    f92SearchHiProg_exec x a lists base hb src
      (mem_f92SourcesUpTo_full (x.W_sub a).insideFinset)
      (fun v hv => lt_of_mem_f92SourcesUpTo _ hv) s₂ hadj₂
      (by rw [hfixed₂ (base + 42) (by omega) (by omega) (by omega)]; exact hent)
      (by rw [hreg₂ (base + 40) (by omega), hreg₁ (base + 40) (by omega)]; exact hrn)
      hw hn (hsrcLen.trans_lt hn')
      (by rw [harr₂ (base + 60) (by omega) (by omega)]; exact hlab₁) hsrc₂
  have hPlen : P.length ≤ x.n := by
    obtain ⟨_, _, hnd, _⟩ := hP.1
    simpa using hnd.length_le_card
  have hPwords : ∀ v ∈ P.map Fin.val, v < 2 ^ w := by
    intro v hv
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
    exact u.isLt.trans hn'
  obtain ⟨s₄, t₄, hex₄, ht₄, hout₄, harr₄, hreg₄⟩ :=
    copyArrProg_exec (base + 64) out (base + 80) (base + 81) (by omega) (by omega)
      (P.map Fin.val) hPwords (by omega) (by simpa using hPlen.trans_lt hn') hout₃
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), P, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    ?_, hP, hout₄, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map] at ht₄
    omega
  · apply hadj.of_arrs_eq
    all_goals
      exact (harr₄ _ (by omega)).trans
        ((harr₃ _ (by omega) (by omega) (by omega) (by omega)).trans
          (hfixed₂ _ (by omega) (by omega) (by omega)))
  · rw [hreg₄ (base + 40) (by omega), hreg₃ (base + 40) (Or.inl (by omega)),
      hreg₂ (base + 40) (by omega), hreg₁ (base + 40) (by omega), hrn]
  · rw [harr₄ (base + 42) (by omega),
      harr₃ (base + 42) (by omega) (by omega) (by omega) (by omega),
      hfixed₂ (base + 42) (by omega) (by omega) (by omega)]
  · intro b hbb hbo
    exact (harr₄ b hbo).trans
      ((harr₃ b (by omega) (by omega) (by omega) (by omega)).trans
        (hfixed₂ b (by omega) (by omega) (by omega)))
  · intro q hqb
    rw [hreg₄ q (by omega), hreg₃ q (Or.inl (by omega)), hreg₂ q (by omega), hreg₁ q (by omega)]

end GraphMinor.Compute.Alg92
