module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
import Mathlib.Order.Minimal

/-!
# Minimal separators and their full components

Two distinct nonadjacent vertices can be separated by deleting neighbors
of the first. Choose a separating set of minimum size. Restoring any one
of its vertices joins the two sides again, so that vertex has a neighbor
in each of the two components. This is the separator construction used to
prove Graph Minors V, (8.4).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V} {a b x : V} {S : Set V}

private abbrev away (G : SimpleGraph V) (S : Set V) : SimpleGraph V :=
  (G.induce Sᶜ).spanningCoe

private lemma away_adj : (away G S).Adj a b ↔ G.Adj a b ∧ a∉S ∧ b∉S := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x,y,h,rfl,rfl⟩
    exact ⟨h,x.2,y.2⟩
  · rintro ⟨h,ha,hb⟩
    exact ⟨⟨a,ha⟩,⟨b,hb⟩,h,rfl,rfl⟩

private lemma reachable_not_mem (ha : a∉S) (hr : (away G S).Reachable a x) : x∉S := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact ha
  | cons h p ih =>
    exact ih (away_adj.mp h).2.2

private lemma minimal_separator [Finite V] (hab : a≠b) (hn : ¬G.Adj a b) :
    ∃ S : Set V, a∉S ∧ b∉S ∧ ¬(away G S).Reachable a b ∧
      ∀ s∈S, (away G (S\{s})).Reachable a b := by
  classical
  let P (S : Set V) := a∉S ∧ b∉S ∧ ¬(away G S).Reachable a b
  have hex : ∃ S, P S := by
    refine ⟨G.neighborSet a, (fun h ↦ h.ne rfl), hn, ?_⟩
    rintro ⟨p⟩
    cases p with
    | nil => exact hab rfl
    | cons h p => exact (away_adj.mp h).2.2 (away_adj.mp h).1
  obtain ⟨S,hS⟩ := exists_minimalFor_of_wellFoundedLT P Set.ncard hex
  refine ⟨S,hS.prop.1,hS.prop.2.1,hS.prop.2.2,?_⟩
  intro s hs
  by_contra hno
  have hP : P (S\{s}) := ⟨fun h ↦ hS.prop.1 h.1,fun h ↦ hS.prop.2.1 h.1,hno⟩
  exact hS.not_lt hP (ncard_sdiff_singleton_lt_of_mem hs (toFinite S))

private lemma full_component_neighbor {S : Set V} {s : V} (ha : a∉S) (_hb : b∉S)
    (hno : ¬(away G S).Reachable a b) (_hs : s∈S)
    (hr : (away G (S\{s})).Reachable a b) :
    ∃ x, (away G S).Reachable a x ∧ G.Adj s x := by
  classical
  by_contra hn
  have hclosed : ∀ x y, (away G S).Reachable a x →
      (away G (S\{s})).Adj x y → (away G S).Reachable a y := by
    intro x y hx hxy
    have hG := (away_adj.mp hxy).1
    by_cases hy : y∈S
    · have hys : y=s := by
        by_contra hne
        exact (away_adj.mp hxy).2.2 ⟨hy,hne⟩
      subst y
      exact (hn ⟨x,hx,hG.symm⟩).elim
    · exact hx.trans (Adj.reachable (away_adj.mpr ⟨hG,reachable_not_mem ha hx,hy⟩))
  obtain ⟨p⟩ := hr
  apply hno
  have walk_closed : ∀ {x y}, (away G (S\{s})).Walk x y →
      (away G S).Reachable a x → (away G S).Reachable a y := by
    intro x y q
    induction q with
    | nil => exact id
    | cons h q ih => exact fun hx ↦ ih (hclosed _ _ hx h)
  exact walk_closed p (Reachable.refl a)

/-- Distinct nonadjacent vertices have a separating set with two disjoint
full components. Every separator vertex has a neighbor in each component;
vertices outside the separator cannot leave either component along an edge. -/
theorem exists_full_components [Finite V] (hab : a≠b) (hn : ¬G.Adj a b) :
    ∃ S A B : Set V,
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ Disjoint A S ∧ Disjoint B S ∧
      (G.induce A).Connected ∧ (G.induce B).Connected ∧
      (∀ s∈S, (∃ x∈A, G.Adj s x) ∧ ∃ y∈B, G.Adj s y) ∧
      (∀ x∈A, ∀ y, G.Adj x y → y∈A ∨ y∈S) ∧
      (∀ x∈B, ∀ y, G.Adj x y → y∈B ∨ y∈S) := by
  classical
  obtain ⟨S,ha,hb,hno,hrestore⟩ := minimal_separator hab hn
  let A := {x | (away G S).Reachable a x}
  let B := {x | (away G S).Reachable b x}
  have hAS : Disjoint A S := Set.disjoint_left.mpr (fun _ h ↦ reachable_not_mem ha h)
  have hBS : Disjoint B S := Set.disjoint_left.mpr (fun _ h ↦ reachable_not_mem hb h)
  have connected_component (c : V) (hc : c∉S) :
      (G.induce {x | (away G S).Reachable c x}).Connected := by
    let C := {x | (away G S).Reachable c x}
    let : Nonempty C := ⟨⟨c,Reachable.refl c⟩⟩
    apply (connected_iff_exists_forall_reachable (G.induce C)).mpr
    refine ⟨⟨c,Reachable.refl c⟩,?_⟩
    intro x
    obtain ⟨p⟩ := x.2
    have lift_walk : ∀ {y z}, (p : (away G S).Walk y z) →
        (hy : (away G S).Reachable c y) →
        Nonempty ((G.induce C).Walk ⟨y,hy⟩ ⟨z,hy.trans p.reachable⟩) := by
      intro y z q
      induction q with
      | nil => exact fun _ ↦ ⟨.nil⟩
      | cons h q ih =>
        intro hy
        obtain ⟨q'⟩ := ih (hy.trans h.reachable)
        exact ⟨.cons (show (G.induce C).Adj ⟨_,hy⟩ ⟨_,hy.trans h.reachable⟩ from
          (away_adj.mp h).1) q'⟩
    exact lift_walk p (Reachable.refl c)
  have closed_component (c : V) (hc : c∉S) : ∀ x,
      (away G S).Reachable c x → ∀ y, G.Adj x y →
      (away G S).Reachable c y ∨ y∈S := by
    intro x hx y hxy
    by_cases hy : y∈S
    · exact Or.inr hy
    · exact Or.inl (hx.trans (Adj.reachable (away_adj.mpr ⟨hxy,reachable_not_mem hc hx,hy⟩)))
  refine ⟨S,A,B,⟨a,Reachable.refl a⟩,⟨b,Reachable.refl b⟩,?_,hAS,hBS,
    connected_component a ha,connected_component b hb,?_,closed_component a ha,closed_component b hb⟩
  · rw [Set.disjoint_left]
    intro x hax hbx
    exact hno (hax.trans hbx.symm)
  · intro s hs
    exact ⟨full_component_neighbor ha hb hno hs (hrestore s hs),
      full_component_neighbor hb ha (fun h ↦ hno h.symm) hs (hrestore s hs).symm⟩

end GraphMinor.GM05
