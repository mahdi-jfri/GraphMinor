module

public import GraphMinor.Compute.Algorithm99Step3
public import GraphMinor.Compute.Algorithm94Unpack

/-!
# Step (3) of Algorithm (9.9): reading `X` and the subwalls `H^1, …, H^s`

Step (3) of the proof of (9.8) in Graph Minors XIII (page 104) goes on: "Otherwise, we obtain a
subset $X \subseteq V(G_i)$ with $|X| < \binom{p}{2}$ and $s$ subwalls $H^1, \dots, H^s$ of $H_i$
of height $h$". The output (ii) of (9.7) is the list
`1 :: (bitSetList X ++ (W_flat 0).encList ++ … ++ (W_flat (s - 1)).encList)`.

Here we show where each piece lies in this list. The bit list of `X` is the slice of length `v`
after the tag (`take_drop_one_alg97Out`). The code of `H^a` starts after the prefix
`alg97OutPrefix X W_flat a` and is followed by the codes of the later subwalls
(`alg97Out_eq_prefix_append`). The prefix of `a + 1` is the prefix of `a` followed by the code of
`H^a` (`alg97OutPrefix_succ`). So the reader `parseFixedWallProg` of `Algorithm94Unpack.lean`,
started at the end of the prefix of `a`, reads the vertex set, the perimeter and the seed vertex
of `H^a` and stops at the end of the prefix of `a + 1` (`alg99ReadSubwall_exec`). Reading the
subwalls one after the other is a loop over `a` with this step.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- A list flat-mapped over `L` splits at position `i` of `L`. -/
theorem flatMap_eq_take_append_getElem_append_drop {α β : Type*} (L : List α) (f : α → List β)
    (i : ℕ) (hi : i < L.length) :
    L.flatMap f = (L.take i).flatMap f ++ f L[i] ++ (L.drop (i + 1)).flatMap f := by
  conv_lhs => rw [← List.take_append_drop i L]
  rw [List.flatMap_append, List.drop_eq_getElem_cons hi, List.flatMap_cons, List.append_assoc]

variable {n h s : ℕ} {G : MultiDigraph n}

/-- The words of the output (ii) of (9.7) before the code of the subwall `H^a`. -/
def alg97OutPrefix (X : Finset (Fin n)) (W_flat : Fin s → WallOfHeight h G) (a : ℕ) :
    List ℕ :=
  1 :: (bitSetList X ++ ((List.finRange s).take a).flatMap (fun b => (W_flat b).encList))

/-- The output (ii) of (9.7) is the prefix of `a`, the code of `H^a`, and the codes of the later
subwalls. -/
theorem alg97Out_eq_prefix_append (X : Finset (Fin n)) (W_flat : Fin s → WallOfHeight h G)
    (a : Fin s) :
    1 :: (bitSetList X ++ (List.finRange s).flatMap (fun b => (W_flat b).encList)) =
      alg97OutPrefix X W_flat a.1 ++ (W_flat a).encList ++
        ((List.finRange s).drop (a.1 + 1)).flatMap (fun b => (W_flat b).encList) := by
  have hlen : a.1 < (List.finRange s).length := by simp
  rw [flatMap_eq_take_append_getElem_append_drop (List.finRange s) _ a.1 hlen,
    List.getElem_finRange]
  simp [alg97OutPrefix, List.append_assoc]

/-- The prefix of `a + 1` is the prefix of `a` followed by the code of `H^a`. -/
theorem alg97OutPrefix_succ (X : Finset (Fin n)) (W_flat : Fin s → WallOfHeight h G)
    (a : Fin s) :
    alg97OutPrefix X W_flat (a.1 + 1) = alg97OutPrefix X W_flat a.1 ++ (W_flat a).encList := by
  have hlen : a.1 < (List.finRange s).length := by simp
  simp only [alg97OutPrefix, List.take_add_one, List.getElem?_eq_getElem hlen,
    List.getElem_finRange, Option.toList_some, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.append_assoc]
  rfl

theorem length_alg97OutPrefix_zero (X : Finset (Fin n)) (W_flat : Fin s → WallOfHeight h G) :
    (alg97OutPrefix X W_flat 0).length = 1 + n := by
  simp [alg97OutPrefix, Nat.add_comm]

/-- The bit list of `X` is the slice of length `n` after the tag. -/
theorem take_drop_one_alg97Out (X : Finset (Fin n)) (rest : List ℕ) :
    ((1 :: (bitSetList X ++ rest)).drop 1).take n = bitSetList X := by
  simp

/-- **Reading `H^a`** (step (3) of (9.9), page 104). Started at the end of the prefix of `a`,
`parseFixedWallProg` writes the vertex set and the perimeter of `H^a` as bit sets, puts its seed
vertex in register `14`, and stops at the end of the prefix of `a + 1`. -/
theorem alg99ReadSubwall_exec {w : ℕ} (h2 : 2 ≤ h) (X : Finset (Fin n))
    (W_flat : Fin s → WallOfHeight h G) (a : Fin s) (hW : (W_flat a).IsValid)
    (a_src a_V a_perim r_pos : ℕ)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim) (hr_pos : 14 < r_pos)
    (hw1 : 1 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w) (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (hlen_w : (alg97OutPrefix X W_flat (a.1 + 1)).length < 2 ^ w)
    {st : State}
    (hsrc : st.arrs a_src =
      1 :: (bitSetList X ++ (List.finRange s).flatMap (fun b => (W_flat b).encList)))
    (hr1 : st.regs 1 = n) (hrpos : st.regs r_pos = (alg97OutPrefix X W_flat a.1).length) :
    ∃ s' t,
      Exec w (parseFixedWallProg h h2 false 0 a_src a_V a_perim r_pos) st s' t ∧
      t ≤ parseWallCost h n ∧
      s'.regs r_pos = (alg97OutPrefix X W_flat (a.1 + 1)).length ∧
      s'.regs 14 = ((W_flat a).seedVert h2).1 ∧
      IsBitSet (W_flat a).vertexFinset a_V s' ∧
      IsBitSet (W_flat a).perimeterFinset a_perim s' ∧
      (∀ a' : ℕ, a' ≠ a_V → a' ≠ a_perim → s'.arrs a' = st.arrs a') ∧
      (∀ r : ℕ, (r < 3 ∨ 8 < r) → r ≠ 14 → r ≠ r_pos → s'.regs r = st.regs r) := by
  rw [alg97Out_eq_prefix_append X W_flat a] at hsrc
  rw [alg97OutPrefix_succ X W_flat a] at hlen_w ⊢
  obtain ⟨s', t, hex, ht, hpos, h14, hV, hP, -, harr, hreg⟩ :=
    parseFixedWallProg_exec h2 le_rfl (W_flat a) hW false 0 a_src a_V a_perim r_pos
      hne_sV hne_sP hne_VP (fun h => absurd h (by decide)) hr_pos _ _ hw1 hn1_w hc_w hlen_w hsrc
      hr1 hrpos
  exact ⟨s', t, hex, ht, hpos, h14, hV, hP,
    fun a' h₁ h₂ => harr a' h₁ h₂ (fun h => absurd h (by decide)), hreg⟩

end GraphMinor.Compute
