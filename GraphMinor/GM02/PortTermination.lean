module

public import GraphMinor.GM02.PortGraph

/-!
# The terminal pairs of the split graph with edge vertices

Keep the paper's `k` pairs of distinct split terminals. Each terminal
has exactly its chosen edge vertex as a neighbor. The two terminals of
a pattern loop have different neighbors, excluding the false two-step
path in the printed construction. For an edgeless pattern there are no
choices to supply and the terminal index is zero.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The empty pattern requires no incident-edge choices, even in an empty host. -/
def PortChoice.empty {α : Type u} {β : Type v} (G : Graph α β)
    (ends : Fin 0 → α × α) : PortChoice G ends where
  edge p := Fin.elim0 p.1
  incident p := Fin.elim0 p.1
  loop_ne i := Fin.elim0 i

/-- The two incident-edge choices for a pattern loop have different original edge names. -/
theorem PortChoice.loop_edges_ne {α : Type u} {β : Type v} {k : ℕ} {G : Graph α β}
    {ends : Fin k → α × α} (choice : PortChoice G ends) (i : Fin k)
    (hloop : (ends i).1 = (ends i).2) :
    (choice.edge (i, false)).val ≠ (choice.edge (i, true)).val :=
  fun h => choice.loop_ne i hloop (Subtype.ext h)

/-- The `k` pairs remain exactly the prescribed split terminal pairs of II, page 319. -/
noncomputable def portTermination {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) : Termination V(portGraph G H choice) where
  pairs := Finset.univ.image fun i => s(portTerminal (i, false), portTerminal (i, true))
  not_diag := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    simp [portTerminal]
  vertex_mem := by
    intro p hp a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    rcases Sym2.mem_iff.1 ha with rfl | rfl
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
  disjoint := by
    intro p hp q hq hpq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hq
    have hij : i ≠ j := fun h => hpq (h ▸ rfl)
    rw [Set.disjoint_left]
    intro a ha ha'
    simp only [Set.mem_ofPred_eq, Sym2.mem_iff, portTerminal] at ha ha'
    rcases ha with rfl | rfl <;> rcases ha' with h | h <;> simp_all

/-- The split termination has exactly the original pattern edge count as its index. -/
theorem portTermination_index {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) : (portTermination G H choice).index = k := by
  have hinj : Function.Injective (fun i : Fin k =>
      s(portTerminal (i, false), portTerminal (i, true)) : Fin k → Sym2 (PortVertex α β k)) := by
    intro i j h
    rcases Sym2.eq_iff.mp h with ⟨he, _⟩ | ⟨he, _⟩
    · simpa only [portTerminal, Sum.inr.injEq, Prod.mk.injEq, and_true] using he
    · simp only [portTerminal, Sum.inr.injEq, Prod.mk.injEq, Bool.false_eq_true, and_false] at he
  change (Finset.univ.image (fun i : Fin k =>
    s(portTerminal (i, false), portTerminal (i, true)))).card = k
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- A pattern loop cannot be represented by the false two-step path using one host edge twice. -/
theorem port_loop_no_common_neighbor {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (i : Fin k)
    (hloop : (ends i).1 = (ends i).2) :
    ¬∃ a, (portGraph G H choice).Adj (portTerminal (i, false)) a ∧
      (portGraph G H choice).Adj a (portTerminal (i, true)) := by
  rintro ⟨a, hL, hR⟩
  rcases a with (a | e) | p
  · exact (portGraph_adj_iff G H choice _ _).1 hL |>.2.2
  · have hleft := (portTerminal_adj_portEdge_iff G H choice (i, false) e).1 hL
    have hright := (portTerminal_adj_portEdge_iff G H choice (i, true) e).1 hR.symm
    exact choice.loop_edges_ne i hloop (hleft.trans hright.symm)
  · exact (portGraph_adj_iff G H choice _ _).1 hL |>.2.2

end GraphMinor.GM02
