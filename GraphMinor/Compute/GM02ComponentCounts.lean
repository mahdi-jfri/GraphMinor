module

public import GraphMinor.Compute.GM02CountIntersection
public import GraphMinor.Compute.GM02ComponentSearch

/-!
# The two terminal counts in the component test

Before a search, vertices with label zero are precisely those outside
the candidate separator. After a search, vertices with label one are
precisely the reached component. Specializing the verified counting
program therefore gives both cardinalities compared in II (3.1).
-/

public section
namespace GraphMinor.Compute
open Graph Set TwoPaths Classical

/-- Count the original terminals left after deleting the candidate separator. -/
theorem gm02CountRemaining_exec {n w : ℕ} (Q X : Finset (Fin n))
    (subset labels : Arr) (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w)
    (hrn : s.regs 40 = n) (hq : s.arrs subset = gm02VertexBits Q)
    (hl : s.arrs labels = List.ofFn (gm02ComponentLabels X)) :
    ∃ s' t, Exec w (gm02CountIntersectionProg subset labels 0) s s' t ∧
      t ≤ 7 + n * 17 ∧ Keeps [182, 183] [] s s' ∧ s'.regs 183 = (Q \ X).card := by
  obtain ⟨s', t, hex, ht, hk, hout⟩ := gm02CountIntersectionProg_exec Q (Finset.univ \ X)
    (gm02ComponentLabels X) 0 (fun v => by unfold gm02ComponentLabels; split_ifs <;> omega)
    (fun v => by by_cases hx : v ∈ X <;> simp [gm02ComponentLabels, hx])
    subset labels s hw hn hrn hq hl (Nat.two_pow_pos w)
  refine ⟨s', t, hex, ht, hk, ?_⟩
  have he : Q ∩ (Finset.univ \ X) = Q \ X := by ext v; simp
  exact hout.trans (congrArg Finset.card he)

/-- Count terminals in the component returned by a completed single-source search. -/
theorem gm02CountComponent_exec {n w : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n)) (a : Fin n) (ha : a ∉ X) (subset : Arr)
    (s₀ s : State) (items : List ℕ)
    (hs : SInv G (gm02ComponentLabels X) [a.val] s₀ items items.length s)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hrn : s.regs 40 = n)
    (hq : s.arrs subset = gm02VertexBits Q) :
    ∃ s' t, Exec w (gm02CountIntersectionProg subset aLab 1) s s' t ∧
      t ≤ 7 + n * 17 ∧ Keeps [182, 183] [] s s' ∧
      s'.regs 183 = (GM02.deletedComponent (Graph.ofSimpleGraph G)
        (X : Set (Fin n)) a ∩ (Q : Set (Fin n))).ncard := by
  let R := Finset.univ.filter (fun v : Fin n => v.val ∈ items)
  let mask : Fin n → ℕ := fun v => if v.val ∈ items then 1 else gm02ComponentLabels X v
  have hm (v : Fin n) : mask v ≤ 2 := by
    dsimp [mask, gm02ComponentLabels]
    split_ifs <;> omega
  have hR (v : Fin n) : mask v = 1 ↔ v ∈ R := by
    by_cases hv : v.val ∈ items <;> by_cases hx : v ∈ X <;>
      simp [mask, gm02ComponentLabels, R, hv, hx]
  obtain ⟨s', t, hex, ht, hk, hout⟩ := gm02CountIntersectionProg_exec Q R mask 1 hm hR
    subset aLab s hw hn hrn hq hs.lab (by omega)
  refine ⟨s', t, hex, ht, hk, ?_⟩
  have he : (↑(Q ∩ R) : Set (Fin n)) =
      GM02.deletedComponent (Graph.ofSimpleGraph G) (X : Set (Fin n)) a ∩
        (Q : Set (Fin n)) := by
    ext v
    simp only [Finset.mem_coe, Finset.mem_inter, R, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_inter_iff]
    rw [← gm02ComponentSearch_mem_iff ha hs]
    exact and_comm
  have hc : (Q ∩ R).card = (GM02.deletedComponent (Graph.ofSimpleGraph G)
      (X : Set (Fin n)) a ∩ (Q : Set (Fin n))).ncard := by
    rw [← Set.ncard_coe_finset, he]
  exact hout.trans hc

end GraphMinor.Compute
