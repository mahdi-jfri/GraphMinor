module

public import GraphMinor.GM05.ChordalDefs
import GraphMinor.GM05.SubtreeIntersection
import GraphMinor.GM05.IndependentSelection
import Mathlib.Data.Fintype.EquivFin

/-!
# Prescribed numbers of disjoint subtrees

For each family choose `k` disjoint members. Their intersection graph is
chordal by (8.3), and its vertices split into independent color classes.
Apply (8.5) to select the requested number of each color. Relabel the
selected members by finite ordinals. This is Graph Minors V, (8.6).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set
open scoped BigOperators

/-- Graph Minors V, (8.6), page 111: if each of `m` families of subtrees
contains `k` disjoint members, one can select `x i` members of each family,
all disjoint together, whenever the targets sum to `k`. Subtrees are
represented by their nonempty connected vertex sets. The proof applies
(8.5) to the intersection graph, as in the paper. -/
theorem theorem_8_6_proof {ι : Type*} [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {m k : ℕ} (A : Fin m → Set (Set ι))
    (hA : ∀ i S, S∈A i → (T.induce S).Connected)
    (x : Fin m → ℕ) (hsum : ∑ i,x i=k)
    (hpack : ∀ i, ∃ S : Fin k → Set ι, (∀ a,S a∈A i) ∧
      Pairwise (fun a b ↦ Disjoint (S a) (S b))) :
    ∃ B : (i : Fin m) → Fin (x i) → Set ι,
      (∀ i a, B i a∈A i) ∧
      Pairwise (fun a b : (i : Fin m) × Fin (x i) ↦ Disjoint (B a.1 a.2) (B b.1 b.2)) := by
  classical
  choose S hS hdisj using hpack
  let F (p : Fin m × Fin k) := S p.1 p.2
  let G := subtreeIntersectionGraph F
  have hG : IsChordal G := subtreeIntersectionGraph_isChordal hT F
    (fun p ↦ hA p.1 _ (hS p.1 p.2))
  let Z (i : Fin m) : Set (Fin m × Fin k) := {p | p.1=i}
  have hZ : ∀ i,G.IsIndepSet (Z i) := by
    intro i
    rintro ⟨a,b⟩ ha ⟨c,d⟩ hc hne hadj
    change a=i at ha
    change c=i at hc
    subst a
    subst c
    have hbd : b≠d := fun h ↦ hne (Prod.ext rfl h)
    obtain ⟨v,hv,hv'⟩ := hadj.2
    exact Set.disjoint_left.mp (hdisj i hbd) hv hv'
  have hZd : Pairwise (fun i j ↦ Disjoint (Z i) (Z j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro p hp hq
    exact hij (hp.symm.trans hq)
  have hcard : ∀ i,(Z i).ncard=k := by
    intro i
    have he : Z i=range (fun a : Fin k ↦ (i,a)) := by
      ext p
      constructor
      · intro hp
        exact ⟨p.2,Prod.ext hp.symm rfl⟩
      · rintro ⟨a,rfl⟩; rfl
    rw [he,ncard_range_of_injective (fun a b h ↦ congrArg Prod.snd h)]
    simp
  obtain ⟨X,hX,hcounts⟩ := theorem_8_5_proof hG Z hZ hZd hcard x hsum
  let C (i : Fin m) := X∩Z i
  let inst (i : Fin m) : Fintype (C i) := Fintype.ofFinite _
  let e (i : Fin m) : Fin (x i) ≃ C i := by
    let := inst i
    apply Equiv.symm
    apply Fintype.equivFinOfCardEq
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    exact hcounts i
  let f (a : (i : Fin m) × Fin (x i)) : Fin m × Fin k := (e a.1 a.2).1
  have hfcolor (i : Fin m) (a : Fin (x i)) : (f ⟨i,a⟩).1=i := (e i a).2.2
  have hfX (a : (i : Fin m) × Fin (x i)) : f a∈X := (e a.1 a.2).2.1
  have hfinj : Function.Injective f := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hij : i=j := (hfcolor i a).symm.trans ((congrArg Prod.fst he).trans (hfcolor j b))
    subst j
    have hab : a=b := (e i).injective (Subtype.ext he)
    subst b
    rfl
  refine ⟨fun i a ↦ F (f ⟨i,a⟩),?_,?_⟩
  · intro i a
    have hm := hS (f ⟨i,a⟩).1 (f ⟨i,a⟩).2
    rw [hfcolor i a] at hm
    change S (f ⟨i,a⟩).1 (f ⟨i,a⟩).2 ∈ A i
    rw [hfcolor i a]
    exact hm
  · intro a b hab
    rw [Set.disjoint_left]
    intro v hv hv'
    have hneq : f a≠f b := fun h ↦ hab (hfinj h)
    exact hX (hfX a) (hfX b) hneq ⟨hneq,v,hv,hv'⟩

end GraphMinor.GM05
