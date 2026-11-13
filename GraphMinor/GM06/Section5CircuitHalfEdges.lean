module

public import GraphMinor.GM11.Corners
public import GraphMinor.GM11.Section4
import GraphMinor.GM11.ThreeCircuits
import GraphMinor.GM11.Walks

/-!
# A circuit supplies two directed ends at each vertex

The cuff rotations in VI (5.7), page 133, have two cuff ends even
when there is only one prescribed vertex on a cuff. A circuit
through a vertex either starts with a loop, whose two ends give
the required pair, or leaves on one edge and returns on a distinct
edge. This proves the bound without requiring a second vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A vertex of a circuit has at least two incident directed ends,
including when the circuit is a single loop. -/
theorem two_le_card_halfEdges_of_circuit_vertex
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ C : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    (hC : C.IsCircuit) (hCΓ : C.IsSubdrawing Γ) {v : S} (hv : v ∈ C.V) :
    2 ≤ Nat.card (halfEdges Γ γ v) := by
  classical
  let H := halfEdges Γ γ v
  let : Finite H := (finite_halfEdges Γ γ v).to_subtype
  have hpair (a b : H) (hab : a ≠ b) : 2 ≤ Nat.card H := by
    have hh := ncard_le_card ({a, b} : Set H)
    rwa [ncard_pair hab] at hh
  obtain ⟨W, ⟨hnd, hed⟩, hpos, _, hE⟩ := exists_walk_at hC hv
  cases W with
  | nil _ => simp at hpos
  | @cons v u _ e hl R =>
    have heC : e ∈ C.E := by rw [hE]; exact List.mem_cons_self
    have heΓ : e ∈ Γ.E := hCΓ.2 heC
    by_cases huv : u = v
    · subst u
      have hlΓ := (hCΓ.isLink_iff heC).mp hl
      have hend (b : Bool) : γ e (endOf b) = v := by
        have hh : γ e (endOf b) ∈ closure e ∩ Γ.V :=
          ⟨end_mem_closure hγ heΓ b, end_mem_V hγ heΓ b⟩
        rw [hlΓ.2.2.2] at hh
        simpa using hh
      let a : H := ⟨(e, false), heΓ, hend false⟩
      let b : H := ⟨(e, true), heΓ, hend true⟩
      apply hpair a b
      intro hh
      have hh' := congrArg (fun c : H => c.1.2) hh
      exact Bool.noConfusion hh'
    · obtain ⟨f, hfR, hvf⟩ := exists_edge_at_end R huv
      have hfC : f ∈ C.E := by rw [hE]; exact List.mem_cons_of_mem _ hfR
      have hef : e ≠ f := fun hh => (List.nodup_cons.mp hed).1 (hh ▸ hfR)
      have hve : v ∈ closure e := by
        have hh : v ∈ closure e ∩ C.V := by rw [hl.2.2.2]; simp
        exact hh.1
      obtain ⟨be, hbe⟩ := exists_end_eq hγ heΓ (hCΓ.1 hv) hve
      obtain ⟨bf, hbf⟩ := exists_end_eq hγ (hCΓ.2 hfC) (hCΓ.1 hv) hvf
      let a : H := ⟨(e, be), heΓ, hbe⟩
      let b : H := ⟨(f, bf), hCΓ.2 hfC, hbf⟩
      apply hpair a b
      intro hh
      exact hef (congrArg (fun c : H => c.1.1) hh)

end GraphMinor.GM06
