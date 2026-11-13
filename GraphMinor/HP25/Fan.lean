module

public import GraphMinor.HP25.WebSplit
import GraphMinor.HP25.Prop22
import GraphMinor.HP25.Prop31

/-!
# Fans of triangles are webs

In the second case of the proof of Lemma 4.3 (Humeau and Pous, page 15), the part of the graph on
the side of the vertex `y` is "an edge subgraph of a web (made of the green triangular shapes and
whose rib is a fan graph) with frame $zyxP$" (Figure 13, right). This file builds that web.

Let `q 0, …, q n` be distinct vertices and `y` another vertex. The block `i < n` is the triangle
`y, q i, q (i+1)` together with a set `K i` of further vertices. The fan graph `fanGraph y q K n`
makes each block a clique. It is a web with frame `y q 0 … q n` (`isWebOn_fanGraph`): its rib is the
fan of the triangles `y q i q (i+1)`, and `K i` is the clique of the triangle `i`. The proof is by
induction on `n`, gluing one triangle at a time along the edge `y q n` with Proposition 3.1, starting
from a single triangle, a web by Proposition 2.2.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*}

/-- The block `i` of the fan: the triangle `y, q i, q (i+1)` and the extra vertices `K i`. -/
@[expose] def fanBlock (y : V) (q : ℕ → V) (K : ℕ → Set V) (i : ℕ) : Set V :=
  {y, q i, q (i + 1)} ∪ K i

/-- The vertices of the fan with `n` blocks. -/
@[expose] def fanSet (y : V) (q : ℕ → V) (K : ℕ → Set V) (n : ℕ) : Set V :=
  {v | ∃ i < n, v ∈ fanBlock y q K i}

/-- The fan graph with `n` blocks: two distinct vertices are adjacent when they lie in a common
block. -/
@[expose] def fanGraph (y : V) (q : ℕ → V) (K : ℕ → Set V) (n : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ i < n, u ∈ fanBlock y q K i ∧ v ∈ fanBlock y q K i
  symm := ⟨fun _ _ ⟨h, i, hi, hu, hv⟩ => ⟨h.symm, i, hi, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The frame of the fan: `y q 0 … q n`. -/
@[expose] def fanFrame (y : V) (q : ℕ → V) (n : ℕ) : List V :=
  y :: (List.range (n + 1)).map q

variable {y : V} {q : ℕ → V} {K : ℕ → Set V}

/-- The conditions on the fan data for `n` blocks: the vertices `q i` are distinct and differ from
`y`, and the sets `K i` are disjoint from each other and from `y` and the `q j`. -/
structure FanData (y : V) (q : ℕ → V) (K : ℕ → Set V) (n : ℕ) : Prop where
  inj : ∀ i ≤ n, ∀ j ≤ n, q i = q j → i = j
  ne : ∀ i ≤ n, q i ≠ y
  Ky : ∀ i < n, y ∉ K i
  Kq : ∀ i < n, ∀ j ≤ n, q j ∉ K i
  KK : ∀ i < n, ∀ j < n, i ≠ j → Disjoint (K i) (K j)

theorem FanData.pred {n : ℕ} (h : FanData y q K (n + 1)) : FanData y q K n where
  inj i hi j hj := h.inj i (by omega) j (by omega)
  ne i hi := h.ne i (by omega)
  Ky i hi := h.Ky i (by omega)
  Kq i hi j hj := h.Kq i (by omega) j (by omega)
  KK i hi j hj := h.KK i (by omega) j (by omega)

theorem fanFrame_succ (y : V) (q : ℕ → V) (n : ℕ) :
    fanFrame y q (n + 1) = fanFrame y q n ++ [q (n + 1)] := by
  simp [fanFrame, List.range_succ]

/-- A vertex of the block `n` that lies in an earlier block is `y` or `q n`. -/
theorem FanData.mem_block_inter {n : ℕ} (h : FanData y q K (n + 1)) {v : V}
    (hv : v ∈ fanBlock y q K n) (hv' : v ∈ fanSet y q K n) : v = y ∨ v = q n := by
  obtain ⟨i, hi, hvi⟩ := hv'
  rcases hv with (rfl | rfl | rfl) | hv
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    rcases hvi with (h1 | h1 | h1) | h1
    · exact h.ne (n + 1) le_rfl h1
    · exact absurd (h.inj (n + 1) le_rfl i (by omega) h1) (by omega)
    · exact absurd (h.inj (n + 1) le_rfl (i + 1) (by omega) h1) (by omega)
    · exact h.Kq i (by omega) (n + 1) le_rfl h1
  · exfalso
    rcases hvi with (rfl | rfl | rfl) | h1
    · exact h.Ky n (by omega) hv
    · exact h.Kq n (by omega) i (by omega) hv
    · exact h.Kq n (by omega) (i + 1) (by omega) hv
    · exact Set.disjoint_left.mp (h.KK n (by omega) i (by omega) (by omega)) hv h1

/-- **The fan is a web.** With `n ≥ 1` blocks, the fan graph is a web on its vertices with frame
`y q 0 … q n`. -/
theorem isWebOn_fanGraph : ∀ {n : ℕ}, 1 ≤ n → FanData y q K n →
    IsWebOn (fanGraph y q K n) (fanSet y q K n) (fanFrame y q n)
  | 0, h0, _ => absurd h0 (by omega)
  | 1, _, h => by
    -- one block: a clique on a triangle and its extra vertices (Proposition 2.2)
    have hS : fanSet y q K 1 = fanBlock y q K 0 := by
      ext v
      exact ⟨fun ⟨i, hi, hv⟩ => by obtain rfl : i = 0 := by omega
                                   exact hv, fun hv => ⟨0, by omega, hv⟩⟩
    have hF : fanFrame y q 1 = [y, q 0, q 1] := by simp [fanFrame, List.range_succ]
    rw [hS, hF]
    refine isWebOn_three_iff.mpr ⟨⟨by simp [fanBlock], by simp [fanBlock], by simp [fanBlock],
      (h.ne 0 (by omega)).symm, fun h' => absurd (h.inj 0 (by omega) 1 le_rfl h') (by omega),
      (h.ne 1 le_rfl).symm⟩, fun u v => ⟨fun ⟨huv, i, hi, hu, hv⟩ => ?_,
      fun ⟨hu, hv, huv⟩ => ⟨huv, 0, by omega, hu, hv⟩⟩⟩
    obtain rfl : i = 0 := by omega
    exact ⟨hu, hv, huv⟩
  | n + 2, _, h => by
    -- glue the block `n + 1` to the fan with `n + 1` blocks along the edge `q (n+1) y`
    have ih := isWebOn_fanGraph (n := n + 1) (by omega) h.pred
    set G := fanGraph y q K (n + 2)
    set S₁ := fanBlock y q K (n + 1)
    set S₂ := fanSet y q K (n + 1)
    have hinter : ∀ v, v ∈ S₁ → v ∈ S₂ → v = y ∨ v = q (n + 1) := fun v hv hv' =>
      h.mem_block_inter hv hv'
    have hyS₂ : y ∈ S₂ := ⟨0, by omega, by simp [fanBlock]⟩
    have hqS₂ : q (n + 1) ∈ S₂ := ⟨n, by omega, by simp [fanBlock]⟩
    have hrot : (fanFrame y q (n + 2)).rotate (n + 1 + 1) =
        q (n + 1) :: [q (n + 2)] ++ y :: (List.range (n + 1)).map q := by
      rw [fanFrame, List.rotate_eq_drop_append_take (by simp)]
      simp [List.range_succ, List.drop_append, List.take_append, List.drop_eq_nil_of_le,
        List.take_of_length_le]
    refine prop_3_1 ⟨q (n + 1), y, [], [q (n + 2)], (List.range (n + 1)).map q, n + 1 + 1, S₁, S₂,
      rfl, hrot, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro u v ⟨-, i, hi, hu, -⟩
      exact ⟨i, hi, hu⟩
    · ext v
      refine ⟨fun hv => ?_, fun ⟨i, hi, hv⟩ => ?_⟩
      · rcases hv with hv | ⟨i, hi, hv⟩
        · exact ⟨n + 1, by omega, hv⟩
        · exact ⟨i, by omega, hv⟩
      · by_cases hin : i = n + 1
        · subst hin; exact Or.inl hv
        · exact Or.inr ⟨i, by omega, hv⟩
    · ext v
      refine ⟨fun ⟨h1, h2⟩ => ?_, fun hv => ?_⟩
      · rcases hinter v h1 h2 with rfl | rfl <;> simp
      · simp only [List.nil_append, List.cons_append, List.mem_cons,
          List.not_mem_nil, or_false, mem_ofPred_eq] at hv
        rcases hv with rfl | rfl
        · exact ⟨by simp [S₁, fanBlock], hqS₂⟩
        · exact ⟨by simp [S₁, fanBlock], hyS₂⟩
    · rintro u hu v hv ⟨-, i, hi, hui, hvi⟩
      by_cases hin : i = n + 1
      · subst hin; exact Or.inr hvi
      · exact Or.inl ⟨i, by omega, hui⟩
    · intro u hu v hv huv
      simp only [List.nil_append, List.cons_append, List.mem_cons,
        List.not_mem_nil, or_false] at hu hv
      have hne := huv.1
      refine ⟨(q (n + 1), y), by simp, ?_⟩
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hne
    · -- the new block: a clique on a triangle (Proposition 2.2)
      refine isWebOn_three_iff.mpr ⟨⟨by simp [S₁, fanBlock], by simp [S₁, fanBlock],
        by simp [S₁, fanBlock], fun h' => absurd (h.inj (n + 1) (by omega) (n + 2) le_rfl h')
        (by omega), h.ne (n + 2) le_rfl, h.ne (n + 1) (by omega)⟩, fun u v =>
        ⟨fun ⟨_, hu, hv⟩ => ⟨hu, hv, (fanGraph y q K (n + 2)).ne_of_adj ‹_›⟩,
        fun ⟨hu, hv, huv⟩ => ⟨⟨huv, n + 1, by omega, hu, hv⟩, hu, hv⟩⟩⟩
    · -- the old fan
      have e : y :: ((List.range (n + 1)).map q ++ q (n + 1) :: []) = fanFrame y q (n + 1) := by
        simp [fanFrame, List.range_succ]
      have hr : restrict G S₂ = fanGraph y q K (n + 1) := by
        ext u v
        constructor
        · rintro ⟨⟨huv, i, hi, hu, hv⟩, hu', hv'⟩
          by_cases hin : i = n + 1
          · subst hin
            refine ⟨huv, n, by omega, ?_, ?_⟩
            · rcases hinter u hu hu' with rfl | rfl <;> simp [fanBlock]
            · rcases hinter v hv hv' with rfl | rfl <;> simp [fanBlock]
          · exact ⟨huv, i, by omega, hu, hv⟩
        · rintro ⟨huv, i, hi, hu, hv⟩
          exact ⟨⟨huv, i, by omega, hu, hv⟩, ⟨i, hi, hu⟩, ⟨i, hi, hv⟩⟩
      rw [hr]
      simpa [e] using ih

end GraphMinor.HP25
