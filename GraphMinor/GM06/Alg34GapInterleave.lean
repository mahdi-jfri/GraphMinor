module

public import GraphMinor.GM06.Alg34GapAngles

/-!
# Interleaving vertices and following gap points

Even positions hold the supplied vertices and odd positions hold their
following gap points. The coordinate bounds for those gaps imply that
the whole interleaved sequence increases. This converts geometric gap
placement into the finite alternating-position order used by the input.
-/

@[expose] public section
namespace GraphMinor.GM06

open Set Surface

/-- The sequence that alternates a vertex and its following gap point. -/
def alg34_interleavedPoint {α : Type*} {n : ℕ} (v p : Fin n → α)
    (k : Fin (2 * n)) : α :=
  if k.val % 2 = 0 then v ⟨k.val / 2, by omega⟩ else p ⟨k.val / 2, by omega⟩

/-- An even position holds its supplied vertex. -/
theorem alg34_interleavedPoint_even {α : Type*} {n : ℕ} (v p : Fin n → α) (i : Fin n) :
    alg34_interleavedPoint v p ⟨2 * i.val, by omega⟩ = v i := by
  have hm : (2 * i.val) % 2 = 0 := by omega
  simp only [alg34_interleavedPoint, hm, ↓reduceIte]
  apply congrArg v
  apply Fin.ext
  change (2 * i.val) / 2 = i.val
  omega

/-- An odd position holds the following gap point. -/
theorem alg34_interleavedPoint_odd {α : Type*} {n : ℕ} (v p : Fin n → α) (i : Fin n) :
    alg34_interleavedPoint v p ⟨2 * i.val + 1, by omega⟩ = p i := by
  have hm : (2 * i.val + 1) % 2 ≠ 0 := by omega
  simp only [alg34_interleavedPoint, ite_eq_right hm]
  apply congrArg p
  apply Fin.ext
  change (2 * i.val + 1) / 2 = i.val
  omega

/-- Strictly increasing vertex coordinates with a gap point before every
later vertex give a strictly increasing interleaved sequence. -/
theorem alg34_interleaved_strictMono {α : Type*} {n : ℕ} (f : α → ℝ)
    (v p : Fin n → α) (hv : StrictMono (fun i => f (v i)))
    (hlo : ∀ i, f (v i) < f (p i))
    (hup : ∀ i j, i < j → f (p i) < f (v j)) :
    StrictMono (fun k => f (alg34_interleavedPoint v p k)) := by
  intro k l hkl
  let i : Fin n := ⟨k.val / 2, by omega⟩
  let j : Fin n := ⟨l.val / 2, by omega⟩
  change f (if k.val % 2 = 0 then v i else p i) <
    f (if l.val % 2 = 0 then v j else p j)
  have hle : i.val ≤ j.val := by dsimp [i, j]; omega
  by_cases he : i = j
  · have heval : k.val / 2 = l.val / 2 := congrArg Fin.val he
    have hk : k.val % 2 = 0 := by omega
    have hl : l.val % 2 ≠ 0 := by omega
    simp only [hk, ↓reduceIte, ite_eq_right hl, ← he]
    exact hlo i
  · have hij : i < j := by
      change i.val < j.val
      have hne : i.val ≠ j.val := fun hh => he (Fin.ext hh)
      omega
    split_ifs with hk hl
    · exact hv hij
    · exact (hv hij).trans (hlo j)
    · exact hup i j hij
    · exact (hup i j hij).trans (hlo j)

/-- The vertices and their following segment points interleave in the
circular coordinate cut at a supplied vertex. -/
theorem alg34_gap_interleaved_strictMono {V : Set Circle} {c : Circle} (hc : c ∈ V)
    {n : ℕ} (v p : Fin n → Circle) (hv : ∀ i, v i ∈ V)
    (horder : StrictMono (fun i => c.angleDiff (v i)))
    (hp : ∀ i, p i ∈ nextSegment V (v i)) :
    StrictMono (fun k => c.angleDiff (alg34_interleavedPoint v p k)) :=
  alg34_interleaved_strictMono (Circle.angleDiff c) v p horder
    (fun i => alg34_gap_angle_lower hc (hp i))
    (fun i j hij => alg34_gap_angle_upper hc (hv j) (hp i) (horder hij))

end GraphMinor.GM06
