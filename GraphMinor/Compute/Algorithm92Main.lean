module

public import GraphMinor.Compute.Algorithm92AfterF
public import GraphMinor.Compute.Algorithm92FClaim
public import GraphMinor.Compute.Algorithm92Exists
public import GraphMinor.Compute.Algorithm92Route

/-!
# Graph Minors XIII, (9.2): the algorithm, from the program that finds `F` (`Algorithm92Main.lean`)

**(9.2)** (page 99 of Graph Minors XIII): for every `l ≥ 3` and `m, p ≥ 0` there exist `k, r` such
that an `(l, m)`-star over `H` or a model of `K_p` can be found in time `C ε(G)`, with `C`
depending only on `l, m, p` and the height of `H`.

The algorithm of page 101 first finds `F`, then compresses `H ∪ F`, looks the compressed graph up
in a table and lifts the answer. The first part is the claim `F92ProgClaim`
(`Algorithm92FClaim.lean`); the rest is the program `afterF` (`Algorithm92AfterF.lean`). This file
puts the two together: `algorithm_9_2_of_F92` proves `Algorithm92Statement` from `F92ProgClaim`.

The time of `afterF` is linear in `n`: the layout has length at most `layLen92 h k * (n + 1)`
(`length_layout_le'`), and every other part of the bound depends only on `l, m, p, h, k, r`
(`afterTime_le`, `afterWord_le`).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

variable {l m p h k r : ℕ}

/-- The factor of `n + 1` in the bound on the length of the layout. -/
def layLen92 (h k : ℕ) : ℕ := 5 + 3 * elemWallNumVerts h + 2 * (elemWallEdges h).length + k

theorem length_layout_le' {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}
    (hnd : ∀ P ∈ segs, P.length ≤ x.n) (hs : segs.length ≤ k) :
    (layout x segs).length ≤ layLen92 h k * (x.n + 1) := by
  have h1 := length_layout_le hnd
  have h2 := Nat.mul_le_mul_right (x.n + 1) hs
  unfold layLen92
  nlinarith

variable (l m p h k r) in
/-- The factor of `n + 1` in the time of `afterF`. -/
noncomputable def afterC : ℕ :=
  (61 + 8 * (elemWallEdges h).length + 13 * elemWallNumVerts h + layLen92 h k +
      75 * (elemWallEdges h).length + 76 * k) +
    (22 + 25 * layLen92 h k) + 60 + (50 + 40 * elemWallNumVerts h + 50 * layLen92 h k) +
    (20 + 16 * keyLen92 h k) +
    ((keys92 h k).length * (6 + 5 * keyLen92 h k) + 3 + 4 * tsum92 l m p h k r) + 2 +
    (20 + 46 * p) +
    (111 + 37 * l + 67 * (l * tsum92 l m p h k r) +
      15 * (l * tsum92 l m p h k r * layLen92 h k) + 17 * tsum92 l m p h k r +
      17 * (tsum92 l m p h k r * layLen92 h k))

theorem afterTime_le {n b sl : ℕ} (hb : b ≤ layLen92 h k * (n + 1)) (hs : sl ≤ k) :
    afterTime l m p h k r n b (60 + 8 * (elemWallEdges h).length + 13 * elemWallNumVerts h + n +
      b + (elemWallEdges h).length * (60 + 15 * n) + sl * (61 + 15 * n)) ≤
      afterC l m p h k r * (n + 1) := by
  unfold afterTime afterC
  generalize layLen92 h k = D at hb ⊢
  generalize tsum92 l m p h k r = T
  generalize (elemWallEdges h).length = Eh
  generalize elemWallNumVerts h = V
  generalize keyLen92 h k = Λ
  generalize (keys92 h k).length = nκ
  have e1 := Nat.mul_le_mul_right (61 + 15 * n) hs
  have e2 := Nat.mul_le_mul_left (l * T) hb
  have e3 := Nat.mul_le_mul_left T hb
  have z1 := Nat.zero_le (Eh * n)
  have z2 := Nat.zero_le (V * n)
  have z3 := Nat.zero_le (D * n)
  have z4 := Nat.zero_le (k * n)
  have z5 := Nat.zero_le (Λ * n)
  have z6 := Nat.zero_le (nκ * Λ * n)
  have z7 := Nat.zero_le (nκ * n)
  have z8 := Nat.zero_le (T * n)
  have z9 := Nat.zero_le (p * n)
  have z10 := Nat.zero_le (l * n)
  have z11 := Nat.zero_le (l * T * n)
  have z12 := Nat.zero_le (l * T * D * n)
  have z13 := Nat.zero_le (T * D * n)
  nlinarith

variable (l m p h k r) in
/-- The factor of `n + 1` in the word bound of `afterF`. -/
noncomputable def afterWC : ℕ :=
  2 * (tsum92 l m p h k r * layLen92 h k) + 4 * layLen92 h k + k + 2 * p + 4 * tsum92 l m p h k r +
    6 * elemWallNumVerts h + 2 * keyLen92 h k + 2 * bound92 h k +
    2 * (elemWallEdges h).length + h + 70

theorem afterWord_le {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}
    (hnd : ∀ P ∈ segs, P.length ≤ x.n) (hs : segs.length ≤ k) :
    afterWord l m p h k r x.n (layout x segs).length (bigB x segs) ≤
      afterWC l m p h k r * (x.n + 1) := by
  have hb := length_layout_le' hnd hs
  have hS := length_encSegs92_le hnd
  have hE := length_encList_le (x := x)
  have e1 := Nat.mul_le_mul_right (x.n + 1) hs
  unfold afterWord afterWC bigB
  generalize (layout x segs).length = b at hb ⊢
  generalize layLen92 h k = D at hb ⊢
  generalize tsum92 l m p h k r = T
  have e3 := Nat.mul_le_mul_left T hb
  nlinarith

/-- **The algorithm of Graph Minors XIII, (9.2) (page 99), from the claim on the program that
finds `F`.** The program is the program of `F92ProgClaim` followed by `afterF`; the bound `r` is
`max r₀ 1`, where `k, r₀` come from Theorem (9.2) of the paper (`exists_isAlg92Output`). -/
theorem algorithm_9_2_of_F92 (hF : F92ProgClaim) : Algorithm92Statement := by
  intro l m p hl
  obtain ⟨k, r₀, hex0⟩ := exists_isAlg92Output l m p hl
  refine ⟨k, max r₀ 1, fun h _ _ => ?_⟩
  have hex : ∀ y : Alg92Input l m p h k (max r₀ 1), ∃ out, IsAlg92Output l m p y out := fun y => by
    obtain ⟨out, ho⟩ := hex0 h (y.weaken (le_max_left r₀ 1))
    exact ⟨out, (isAlg92Output_weaken y _ out).mp ho⟩
  obtain ⟨Pf, CF, cF, hPf⟩ := hF l m p h k (max r₀ 1) (le_max_right r₀ 1) aG aW aF 5 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨.seq Pf (afterF l m p h k (max r₀ 1)), CF + afterC l m p h k (max r₀ 1) + 1,
    cF + afterWC l m p h k (max r₀ 1) + 1, by omega, by omega, fun x s hs => ?_⟩
  have hw1 : wordSize cF (alg92Size x) ≤ wordSize (cF + afterWC l m p h k (max r₀ 1) + 1)
      (alg92Size x) := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨s1, t1, ex1, ht1, hG1, hW1, ⟨segs, paths, hFS, hsl, hF1⟩, -, -⟩ := hPf _ x s hw1 hs
  have hnd : ∀ P ∈ segs, P.length ≤ x.n := fun P hP => by
    simpa using (hFS.nodup P hP).length_le_card
  have hsize : x.n + 1 ≤ alg92Size x := by unfold alg92Size; omega
  have hword : afterWord l m p h k (max r₀ 1) x.n (layout x segs).length (bigB x segs) <
      2 ^ wordSize (cF + afterWC l m p h k (max r₀ 1) + 1) (alg92Size x) := by
    have h1 := afterWord_le (r := max r₀ 1) hnd hsl
    have h2 := Alg91.const_mul_lt_two_pow_wordSize (K := afterWC l m p h k (max r₀ 1))
      (c := cF + afterWC l m p h k (max r₀ 1) + 1) (S := alg92Size x) (by omega)
    have h3 := Nat.mul_le_mul_left (afterWC l m p h k (max r₀ 1)) (show x.n + 1 ≤ alg92Size x + 1
      by omega)
    omega
  obtain ⟨s2, t2, ex2, ht2, hout⟩ := afterF_exec hl hex hFS hsl hG1 hW1 hF1 hword
  refine ⟨s2, t1 + t2, .seq ex1 ex2, ?_, hout⟩
  have h4 := afterTime_le (l := l) (m := m) (p := p) (r := max r₀ 1) (n := x.n)
    (length_layout_le' hnd hsl) hsl
  have h5 := Nat.mul_le_mul_left (afterC l m p h k (max r₀ 1)) hsize
  unfold buildTime at ht2
  beta_reduce
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

end Alg92

end GraphMinor.Compute
