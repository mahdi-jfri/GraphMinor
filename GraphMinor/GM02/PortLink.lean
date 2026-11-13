module

public import GraphMinor.GM02.PortProjection

/-!
# Recovering host links from feasible split paths

A split path cannot turn back along one original edge. Old vertices
have different names from branch vertices, and the two terminals of a
pattern loop choose different edges. These two facts make each pair of
successive split incidences into a genuine host link.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Equal projected labels cannot occur on opposite sides of an edge vertex of one split path. -/
theorem portPath_labels_ne {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H))
    (P : ∀ p : {p // p ∈ (portTermination G H choice).pairs}, PairPath (pathGraph (portGraph G H choice)) p.val)
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)
    (i : Fin k) (a b : PortVertex α β k) (e : β) (x y : α)
    (hpa : a ∈ (P (portPair G H choice i)).vertices)
    (hpb : b ∈ (P (portPair G H choice i)).vertices)
    (hab : a ≠ b)
    (ha : (portGraph G H choice).Adj a (portEdge e))
    (hb : (portGraph G H choice).Adj (portEdge e) b)
    (hax : portLabel ends a = some x) (hby : portLabel ends b = some y) : x ≠ y := by
  intro hxy
  subst y
  have ca := portPath_vertex_cases G H choice P hP i a hpa
  have cb := portPath_vertex_cases G H choice P hP i b hpb
  rcases ca with ⟨a, haV, rfl⟩ | ⟨f, hf, rfl⟩ | rfl | rfl
  · rcases cb with ⟨b, hbV, rfl⟩ | ⟨f, hf, rfl⟩ | rfl | rfl
    · have h1 : a = x := Option.some.inj hax
      have h2 : b = x := Option.some.inj hby
      exact hab (congrArg portOld (h1.trans h2.symm))
    · cases hby
    · have h1 : a = x := Option.some.inj hax
      have h2 : (ends i).1 = x := Option.some.inj hby
      exact haV.2 ((h2.trans h1.symm) ▸ (hends i).1)
    · have h1 : a = x := Option.some.inj hax
      have h2 : (ends i).2 = x := Option.some.inj hby
      exact haV.2 ((h2.trans h1.symm) ▸ (hends i).2)
  · cases hax
  · rcases cb with ⟨b, hbV, rfl⟩ | ⟨f, hf, rfl⟩ | rfl | rfl
    · have h1 : (ends i).1 = x := Option.some.inj hax
      have h2 : b = x := Option.some.inj hby
      exact hbV.2 ((h1.trans h2.symm) ▸ (hends i).1)
    · cases hby
    · exact hab rfl
    · have h1 : (ends i).1 = x := Option.some.inj hax
      have h2 : (ends i).2 = x := Option.some.inj hby
      exact port_loop_no_common_neighbor G H choice i (h1.trans h2.symm) ⟨portEdge e, ha, hb⟩
  · rcases cb with ⟨b, hbV, rfl⟩ | ⟨f, hf, rfl⟩ | rfl | rfl
    · have h1 : (ends i).2 = x := Option.some.inj hax
      have h2 : b = x := Option.some.inj hby
      exact hbV.2 ((h1.trans h2.symm) ▸ (hends i).2)
    · cases hby
    · have h1 : (ends i).2 = x := Option.some.inj hax
      have h2 : (ends i).1 = x := Option.some.inj hby
      exact port_loop_no_common_neighbor G H choice i (h2.trans h1.symm) ⟨portEdge e, hb.symm, ha.symm⟩
    · exact hab rfl

end GraphMinor.GM02
