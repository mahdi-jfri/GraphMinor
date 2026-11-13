module

public import GraphMinor.Compute.CrossingOpsBasic
public import GraphMinor.Compute.SpecsCrossingRec

/-!
# The copy of an instance

Section 10 of `docs/crossing/crossing_extractor.tex` begins each trial with "copy the current
instance". This
file gives the program that copies the five arrays of an instance (`copyInstanceProg`) and proves
what it does.

`CopyInstanceProgClaim` of `SpecsCrossing.lean` is false as stated (`not_copyInstanceProgClaim`):
it does not assume that `D` is a cycle, so the array of `D` may be much longer than
`N + |E(G)| + 1`, and every copy of it takes at least its length in steps (`Exec.length_le`).
The corrected claim `CopyInstanceCycleProgClaim` adds the hypothesis that `D` is a cycle, as the
other claims of `SpecsCrossing.lean` do, and it is proved (`copyInstanceCycleProgClaim_proved`).
The proof uses only that `D` has no repeated vertex, so that `|D| ≤ N`.

The program copies each array with `copyMinProg`, which caps the entries at
`|ent| + N`. Every entry that the instance describes is below this cap, so the copy describes the
same instance. The cap is needed because the entries array may hold entries outside the slices of
the lists, and such an entry may not fit in a word.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### The claim is false as stated -/

/-- `CopyInstanceProgClaim` is false: with `N = 1`, the empty graph and a list `D` of
`2 C + 1` copies of the vertex `0`, a copy must make an array of length `2 C + 1`, which takes at
least `2 C + 1` steps, while the time bound is `C (N + |E(G)| + 1) = 2 C`. -/
theorem not_copyInstanceProgClaim : ¬ CopyInstanceProgClaim := by
  intro h
  obtain ⟨P, C, c, hP⟩ := h ⟨0, 1, 2, 3, 4⟩ ⟨5, 6, 7, 8, 9⟩ 10 0
    ⟨by decide, by simp [InstArrs.list]⟩
  set M := 2 * C + 1
  let D : List (Fin 1) := List.replicate M 0
  let s : State := ⟨fun _ => 0, fun i => if i = 4 then List.replicate M 0
    else if i = 0 ∨ i = 1 ∨ i = 2 then [0] else []⟩
  have hE : (⊥ : SimpleGraph (Fin 1)).edgeSet.ncard = 0 := by simp
  have hinst : IsInstanceAt ⟨0, 1, 2, 3, 4⟩ (⊥ : SimpleGraph (Fin 1)) ∅ D s := by
    refine ⟨fun x y h => absurd h (by simp), ?_, ⟨fun _ => [], ?_, ?_⟩, ?_, ?_⟩
    · simp [s]
    · refine ⟨by simp [s], by simp [s], fun u => ⟨0, 0, ?_⟩⟩
      have hu : u.1 = 0 := by omega
      refine ⟨by simp [s, hu], by simp [s, hu], by simp [s], by simp, by simp [s, hu],
        by simp [s, hu], le_rfl, fun k hk => absurd hk (by simp)⟩
    · intro u
      refine ⟨by simp, by simp, by simp, fun v => ?_⟩
      simp
    · simp [s, hE]
    · simp [s, D]
  obtain ⟨s', t, hex, ht, -, hb⟩ := hP (wordSize c (instSize 1 ⊥)) 1 ⊥ ∅ D s le_rfl hinst
  have hlen := Exec.length_le hex 9
  rw [hb.2.2.2.2] at hlen
  have hs9 : s.arrs 9 = [] := by simp [s]
  rw [hs9] at hlen
  have hsize : instSize 1 (⊥ : SimpleGraph (Fin 1)) = 2 := by simp [instSize, hE]
  rw [hsize] at ht
  simp [D, M] at hlen
  omega

/-! ### The corrected claim -/

/-- **The copy of an instance** (Section 10: "copy the current instance"), for an instance whose
cycle `D` is a cycle: from the arrays `a` to the arrays `b`, in `C (N + |E(G)| + 1)` steps. This
is `CopyInstanceProgClaim` with the hypothesis `HP25.IsCycleList G D` added. -/
def CopyInstanceCycleProgClaim : Prop :=
  ∀ (a b : InstArrs) (a_base r_base : ℕ), ArrsOk (a.list ++ b.list) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (s : State),
      wordSize c (instSize N G) ≤ w → IsInstanceAt a G S D s → HP25.IsCycleList G D →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧ KeepsBelow r_base a_base [] b.list s s' ∧
        IsInstanceAt b G S D s'

/-! ### The program -/

/-- Copy the five arrays of an instance from `a` to `b`, capping every entry at `|ent| + N`
(kept in register `r_base`). Registers `r_base + 1` and `r_base + 2` count. -/
def copyInstanceProg (a b : InstArrs) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.op .add (.len a.ent) (.len a.alive)))
    (.seq (copyMinProg a.alive b.alive r_base (r_base + 1) (r_base + 2))
      (.seq (copyMinProg a.st b.st r_base (r_base + 1) (r_base + 2))
        (.seq (copyMinProg a.en b.en r_base (r_base + 1) (r_base + 2))
          (.seq (copyMinProg a.ent b.ent r_base (r_base + 1) (r_base + 2))
            (copyMinProg a.cyc b.cyc r_base (r_base + 1) (r_base + 2))))))

/-- The entries of the start and end arrays of adjacency lists are at most the length of the
entries array. -/
theorem IsListFamily.start_le {n : ℕ} {a_s a_e a_ent : Arr} {lists : Fin n → List ℕ}
    {s : State} (h : IsListFamily n a_s a_e a_ent lists s) :
    (∀ x ∈ s.arrs a_s, x ≤ (s.arrs a_ent).length) ∧
      (∀ x ∈ s.arrs a_e, x ≤ (s.arrs a_ent).length) := by
  obtain ⟨hls, hle, hfam⟩ := h
  constructor
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨st, en, hu_st, hu_en, hen, -, hst, -, hle', -⟩ := hfam ⟨i, by omega⟩
    simp only at hst
    rw [hst]; omega
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨st, en, hu_st, hu_en, hen, -, -, hen', -, -⟩ := hfam ⟨i, by omega⟩
    simp only at hen'
    rw [hen']; omega

/-- Capping every entry at a bound above all of them changes nothing. -/
theorem map_min_of_le {L : List ℕ} {B : ℕ} (h : ∀ x ∈ L, x ≤ B) : L.map (fun x => min x B) = L := by
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left (fun x hx => min_eq_left (h x hx))

/-- The adjacency lists survive a capped copy of the entries array, when the cap is at least
`n`. -/
theorem IsAdjList.of_capped {n : ℕ} {G : SimpleGraph (Fin n)} {a_s a_e a_ent b_s b_e b_ent : Arr}
    {lists : Fin n → List ℕ} {s s' : State} {B : ℕ} (h : IsAdjList G a_s a_e a_ent lists s)
    (hB : n ≤ B) (hs : s'.arrs b_s = s.arrs a_s) (he : s'.arrs b_e = s.arrs a_e)
    (hent : s'.arrs b_ent = (s.arrs a_ent).map (fun x => min x B)) :
    IsAdjList G b_s b_e b_ent lists s' := by
  obtain ⟨⟨hls, hle, hfam⟩, hlists⟩ := h
  refine ⟨⟨by rw [hs, hls], by rw [he, hle], fun u => ?_⟩, hlists⟩
  obtain ⟨st, en, hu_st, hu_en, hen, hdiff, hst, hen', hle', helem⟩ := hfam u
  refine ⟨st, en, by rw [hs]; exact hu_st, by rw [he]; exact hu_en,
    by rw [hent, List.length_map]; exact hen, hdiff, by simp only [hs]; exact hst,
    by simp only [he]; exact hen', hle', fun k hk => ?_⟩
  have hlt : (lists u)[k] < n := (hlists u).1 _ (List.getElem_mem hk)
  simp only [hent, List.getElem_map, helem k hk]
  exact min_eq_left (by omega)

set_option hygiene false in
/-- `ne! i j`: entries `i` and `j` of `a.list ++ b.list` differ. -/
local macro "ne! " i:num j:num : term => `(hne $i $j (by decide) (by decide) (by decide))

theorem copyInstanceProg_exec {w N : ℕ} (a b : InstArrs) (a_base r_base : ℕ)
    (hok : ArrsOk (a.list ++ b.list) a_base) {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {s : State} (hinst : IsInstanceAt a G S D s) (hD : D.length ≤ N)
    (hw : 4 * instSize N G + 4 < 2 ^ w) :
    ∃ s' t, Exec w (copyInstanceProg a b r_base) s s' t ∧ t ≤ 60 * instSize N G ∧
      KeepsBelow r_base a_base [] b.list s s' ∧ IsInstanceAt b G S D s' := by
  obtain ⟨hsupp, halive, ⟨lists, hadj⟩, hentlen, hcyc⟩ := hinst
  have hne : ∀ i j (hi : i < 10) (hj : j < 10), i ≠ j →
      (a.list ++ b.list)[i]'(by simp [InstArrs.list]; omega) ≠
        (a.list ++ b.list)[j]'(by simp [InstArrs.list]; omega) :=
    fun i j _ _ hij e => hij ((hok.1.getElem_inj_iff).mp e)
  set E := G.edgeSet.ncard
  have hsz : instSize N G = N + E + 1 := rfl
  have hls : (s.arrs a.st).length = N := hadj.1.1
  have hle : (s.arrs a.en).length = N := hadj.1.2.1
  have hal : (s.arrs a.alive).length = N := by rw [halive]; simp
  have hcl : (s.arrs a.cyc).length = D.length := by rw [hcyc]; simp
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨B, hB⟩ : ∃ B, B = (s.arrs a.ent).length + N := ⟨_, rfl⟩
  have hBw : B < 2 ^ w := by omega
  -- the bound
  have hev : (Expr.op .add (.len a.ent) (.len a.alive)).eval w s = some B := by
    rw [eval_add (eval_len rfl (by omega)) (eval_len rfl (by omega)) (by omega), hal, hB]
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ = s.setReg r_base B := ⟨_, rfl⟩
  have hex₀ : Exec w (.assign r_base (.op .add (.len a.ent) (.len a.alive))) s s₀ 4 := by
    rw [hs₀]; exact .assign hev
  have hr₀ : s₀.regs r_base = B := by simp [hs₀]
  have hne1 : r_base ≠ r_base + 1 := by omega
  have hne2 : r_base ≠ r_base + 2 := by omega
  have hne12 : r_base + 1 ≠ r_base + 2 := by omega
  -- the five copies
  obtain ⟨s₁, t₁, hex₁, ht₁, hd₁, ha₁, hr₁⟩ := copyMinProg_exec a.alive b.alive r_base
    (r_base + 1) (r_base + 2) (ne! 0 5) hne1 hne2 hne12 hr₀ hBw hw1 (by rw [hs₀]; simp; omega)
  have hr₁' : s₁.regs r_base = B := by rw [hr₁ _ hne1 hne2, hr₀]
  have hA₁ : ∀ x, x ≠ b.alive → s₁.arrs x = s.arrs x := fun x hx => by rw [ha₁ x hx, hs₀]; rfl
  obtain ⟨s₂, t₂, hex₂, ht₂, hd₂, ha₂, hr₂⟩ := copyMinProg_exec a.st b.st r_base
    (r_base + 1) (r_base + 2) (ne! 1 6) hne1 hne2 hne12 hr₁' hBw hw1
    (by rw [hA₁ a.st (ne! 1 5)]; omega)
  have hr₂' : s₂.regs r_base = B := by rw [hr₂ _ hne1 hne2, hr₁']
  obtain ⟨s₃, t₃, hex₃, ht₃, hd₃, ha₃, hr₃⟩ := copyMinProg_exec a.en b.en r_base
    (r_base + 1) (r_base + 2) (ne! 2 7) hne1 hne2 hne12 hr₂' hBw hw1
    (by rw [ha₂ a.en (ne! 2 6), hA₁ a.en (ne! 2 5)]; omega)
  have hr₃' : s₃.regs r_base = B := by rw [hr₃ _ hne1 hne2, hr₂']
  obtain ⟨s₄, t₄, hex₄, ht₄, hd₄, ha₄, hr₄⟩ := copyMinProg_exec a.ent b.ent r_base
    (r_base + 1) (r_base + 2) (ne! 3 8) hne1 hne2 hne12 hr₃' hBw hw1
    (by rw [ha₃ a.ent (ne! 3 7), ha₂ a.ent (ne! 3 6), hA₁ a.ent (ne! 3 5)]; omega)
  have hr₄' : s₄.regs r_base = B := by rw [hr₄ _ hne1 hne2, hr₃']
  obtain ⟨s₅, t₅, hex₅, ht₅, hd₅, ha₅, hr₅⟩ := copyMinProg_exec a.cyc b.cyc r_base
    (r_base + 1) (r_base + 2) (ne! 4 9) hne1 hne2 hne12 hr₄' hBw hw1
    (by rw [ha₄ a.cyc (ne! 4 8), ha₃ a.cyc (ne! 4 7), ha₂ a.cyc (ne! 4 6), hA₁ a.cyc (ne! 4 5)]; omega)
  -- the arrays of the source are unchanged until they are read
  have hsrc : ∀ x, x ≠ b.alive → x ≠ b.st → x ≠ b.en → x ≠ b.ent → x ≠ b.cyc →
      s₅.arrs x = s.arrs x := fun x h1 h2 h3 h4 h5 => by
    rw [ha₅ x h5, ha₄ x h4, ha₃ x h3, ha₂ x h2, hA₁ x h1]
  have hfam := IsListFamily.start_le hadj.1
  refine ⟨s₅, _, .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))), ?_, ?_, ?_⟩
  · have e₂ : (s₁.arrs a.st).length = N := by rw [hA₁ a.st (ne! 1 5)]; exact hls
    have e₃ : (s₂.arrs a.en).length = N := by rw [ha₂ a.en (ne! 2 6), hA₁ a.en (ne! 2 5)]; exact hle
    have e₄ : (s₃.arrs a.ent).length = 2 * E := by
      rw [ha₃ a.ent (ne! 3 7), ha₂ a.ent (ne! 3 6), hA₁ a.ent (ne! 3 5)]; exact hentlen
    have e₅ : (s₄.arrs a.cyc).length = D.length := by
      rw [ha₄ a.cyc (ne! 4 8), ha₃ a.cyc (ne! 4 7), ha₂ a.cyc (ne! 4 6), hA₁ a.cyc (ne! 4 5)]; exact hcl
    have e₁ : (s₀.arrs a.alive).length = N := by rw [hs₀]; exact hal
    rw [e₁] at ht₁; rw [e₂] at ht₂; rw [e₃] at ht₃; rw [e₄] at ht₄; rw [e₅] at ht₅
    rw [hsz]; omega
  · refine ⟨fun r hr _ => ?_, fun x hx hxb => ?_⟩
    · have h1 : r ≠ r_base + 1 := by omega
      have h2 : r ≠ r_base + 2 := by omega
      rw [hr₅ r h1 h2, hr₄ r h1 h2, hr₃ r h1 h2, hr₂ r h1 h2, hr₁ r h1 h2]
      simp [hs₀, show r ≠ r_base by omega]
    · simp only [InstArrs.list, List.mem_cons, List.not_mem_nil, or_false, not_or] at hxb
      exact hsrc x hxb.1 hxb.2.1 hxb.2.2.1 hxb.2.2.2.1 hxb.2.2.2.2
  · -- the copies
    have c₁ : s₅.arrs b.alive = s.arrs a.alive := by
      rw [ha₅ b.alive (ne! 5 9), ha₄ b.alive (ne! 5 8), ha₃ b.alive (ne! 5 7), ha₂ b.alive (ne! 5 6), hd₁]
      rw [hs₀]
      apply map_min_of_le
      intro x hx
      rw [State.setReg_arrs, halive] at hx
      obtain ⟨v, -, rfl⟩ := List.mem_ofFn.mp hx
      have : 0 < N := Fin.pos v
      split_ifs <;> omega
    have c₂ : s₅.arrs b.st = s.arrs a.st := by
      rw [ha₅ b.st (ne! 6 9), ha₄ b.st (ne! 6 8), ha₃ b.st (ne! 6 7), hd₂, hA₁ a.st (ne! 1 5)]
      exact map_min_of_le fun x hx => by have := hfam.1 x hx; omega
    have c₃ : s₅.arrs b.en = s.arrs a.en := by
      rw [ha₅ b.en (ne! 7 9), ha₄ b.en (ne! 7 8), hd₃, ha₂ a.en (ne! 2 6), hA₁ a.en (ne! 2 5)]
      exact map_min_of_le fun x hx => by have := hfam.2 x hx; omega
    have c₄ : s₅.arrs b.ent = (s.arrs a.ent).map (fun x => min x B) := by
      rw [ha₅ b.ent (ne! 8 9), hd₄, ha₃ a.ent (ne! 3 7), ha₂ a.ent (ne! 3 6), hA₁ a.ent (ne! 3 5)]
    have c₅ : s₅.arrs b.cyc = s.arrs a.cyc := by
      rw [hd₅, ha₄ a.cyc (ne! 4 8), ha₃ a.cyc (ne! 4 7), ha₂ a.cyc (ne! 4 6), hA₁ a.cyc (ne! 4 5)]
      apply map_min_of_le
      intro x hx
      rw [hcyc] at hx
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      have := v.2; omega
    refine ⟨hsupp, by rw [c₁, halive], ⟨lists, IsAdjList.of_capped hadj (by omega) c₂ c₃ c₄⟩,
      by rw [c₄, List.length_map, hentlen], by rw [c₅, hcyc]⟩

/-- The corrected copy claim holds. -/
theorem copyInstanceCycleProgClaim_proved : CopyInstanceCycleProgClaim := by
  intro a b a_base r_base hok
  refine ⟨copyInstanceProg a b r_base, 60, 4, fun w N G S D s hw hinst hcyc => ?_⟩
  have hD : D.length ≤ N := by
    simpa using hcyc.2.1.length_le_card
  have hw' : 4 * instSize N G + 4 < 2 ^ w := by
    have h1 := sq_lt_two_pow_wordSize (c := 4) (n := instSize N G) (by omega)
    have h2 : 2 ^ wordSize 4 (instSize N G) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
    nlinarith
  exact copyInstanceProg_exec a b a_base r_base hok hinst hD hw'

/-- The copy claim of `SpecsCrossingRec.lean` holds; it is `CopyInstanceCycleProgClaim`. -/
theorem copyInstanceRecProgClaim_proved : CopyInstanceRecProgClaim :=
  copyInstanceCycleProgClaim_proved

end GraphMinor.Compute.Crossing
