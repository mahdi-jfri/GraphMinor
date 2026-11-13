module

public import GraphMinor.Minor.Model
public import GraphMinor.GM09.Defs
import GraphMinor.GM16.ConnectedTripod
import Mathlib.Data.Fintype.EquivFin

/-!
# Branch arms with a path to the distinguished root

The subdivision step in the proof of Graph Minors I, (1.1), page 55,
needs a path from the target root to the source root's branch centre.
There are at most two incident source edges there. Add the target root
as a third attachment and use the proved three-path construction. Its
arms meet only at their common centre, including when attachments
coincide or there is only one incident edge.
-/

public section

namespace GraphMinor.GM01

open Graph GraphMinor.GM09

universe u v w

/-- With at most two edge attachments and one distinguished vertex in a
connected branch, choose a centre, disjoint edge arms, and a root path
meeting every arm only at the centre. The finite index set is nonempty
in the long-comb application because its root has a spine neighbour. -/
theorem exists_rooted_branch_arms {α : Type u} {β : Type v} {ι : Type w}
    [Finite ι] [Nonempty ι] (hcard : Nat.card ι ≤ 2)
    (G : Graph α β) (hG : GraphConnected G) (attach : ι → α)
    (hattach : ∀ i, attach i ∈ V(G)) (root : α) (hroot : root ∈ V(G)) :
    ∃ (m : α) (arm : ι → Graph α β) (R : Graph α β), m ∈ V(G) ∧
      (∀ i, IsGraphPathWithEnds G (arm i) m (attach i)) ∧
      IsGraphPathWithEnds G R m root ∧
      (∀ i j, i ≠ j → V(arm i) ∩ V(arm j) = {m}) ∧
      (∀ i, V(arm i) ∩ V(R) = {m}) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hcard' : Fintype.card ι ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let enc : ι ↪ Fin 2 :=
    { toFun := fun i ↦ Fin.castLE hcard' ((Fintype.equivFin ι) i)
      inj' := fun i j h ↦ (Fintype.equivFin ι).injective ((Fin.castLE_injective hcard') h) }
  let dec : Fin 2 → ι := Function.invFun enc
  have hdecode (i : ι) : dec (enc i) = i := Function.leftInverse_invFun enc.injective i
  have cases_enc (i : ι) : enc i = 0 ∨ enc i = 1 := by
    have hi := (enc i).isLt
    have h : (enc i).val = 0 ∨ (enc i).val = 1 := by omega
    exact h.elim (fun h ↦ Or.inl (Fin.ext h)) (fun h ↦ Or.inr (Fin.ext h))
  obtain ⟨m, P₁, P₂, R, hm, hP₁, hP₂, hR, h12, h1R, h2R⟩ :=
    GM16.exists_connected_tripod hG (hattach (dec 0)) (hattach (dec 1)) hroot
  let arm (i : ι) := if enc i = 0 then P₁ else P₂
  have hzero_one : (0 : Fin 2) ≠ 1 := by decide
  have hone_zero : (1 : Fin 2) ≠ 0 := Ne.symm hzero_one
  refine ⟨m, arm, R, hm, ?_, hR, ?_, ?_⟩
  · intro i
    rcases cases_enc i with hi | hi
    · have hdi : dec 0 = i := by simpa only [hi] using hdecode i
      simpa only [arm, hi, ↓reduceIte, hdi] using hP₁
    · have hdi : dec 1 = i := by simpa only [hi] using hdecode i
      simpa only [arm, hi, hone_zero, ↓reduceIte, hdi] using hP₂
  · intro i j hij
    rcases cases_enc i with hi | hi <;> rcases cases_enc j with hj | hj
    · exact False.elim (hij (enc.injective (hi.trans hj.symm)))
    · simpa only [arm, hi, hj, hone_zero, ↓reduceIte] using h12
    · simpa only [arm, hi, hj, hone_zero, ↓reduceIte] using
        (Set.inter_comm V(P₂) V(P₁)).trans h12
    · exact False.elim (hij (enc.injective (hi.trans hj.symm)))
  · intro i
    by_cases hi : enc i = 0
    · simpa only [arm, hi, ↓reduceIte] using h1R
    · simpa only [arm, hi, ↓reduceIte] using h2R

end GraphMinor.GM01
