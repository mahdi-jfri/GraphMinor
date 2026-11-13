module

public import GraphMinor.GM05.Statements
import GraphMinor.GM05.ChordalSeparator

/-!
# Simplicial vertices in chordal graphs

Induct on the number of vertices, keeping a clique whose vertices are to
be avoided. A clique separator has two full components, and the given
clique can meet at most one of them. Apply induction to the other component
together with the separator. A simplicial vertex outside the separator
has all its neighbors on that side, so is simplicial in the whole graph.
This proves the result of Dirac quoted as Graph Minors V, (8.4).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

universe u

/-- A proper clique in a finite chordal graph can be avoided by a
simplicial vertex. This is the strengthened induction for (8.4). -/
theorem exists_simplicial_outside_clique {V : Type u} [Finite V] {G : SimpleGraph V}
    (hG : IsChordal G) {C : Set V} (hC : G.IsClique C) (hproper : ∃ v, v∉C) :
    ∃ v, v∉C ∧ IsSimplicial G v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have main : ∀ n, ∀ (W : Type u) [Fintype W], Fintype.card W=n →
      ∀ (G : SimpleGraph W), IsChordal G → ∀ C : Set W, G.IsClique C →
      (∃ v, v∉C) → ∃ v, v∉C ∧ IsSimplicial G v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ hcard G hG C hC hproper
      by_cases hcomplete : G.IsClique univ
      · obtain ⟨v,hv⟩ := hproper
        refine ⟨v,hv,?_⟩
        intro x hx y hy hxy
        exact hcomplete (mem_univ x) (mem_univ y) hxy
      · have hex : ∃ a b, a≠b ∧ ¬G.Adj a b := by
          by_contra hn
          apply hcomplete
          intro a _ b _ hab
          by_contra hnot
          exact hn ⟨a,b,hab,hnot⟩
        obtain ⟨a,b,hab,hn⟩ := hex
        obtain ⟨S,A,B,hS,hA,hB,hAB,hAS,hBS,hclosedA,hclosedB⟩ :=
          exists_clique_separator hG hab hn
        have hcross : ∀ x∈A, ∀ y∈B, ¬G.Adj x y := by
          intro x hx y hy hxy
          rcases hclosedA x hx y hxy with hyA|hyS
          · exact Set.disjoint_left.mp hAB hyA hy
          · exact Set.disjoint_left.mp hBS hy hyS
        have hchoice : ∃ D E : Set W, D.Nonempty ∧ E.Nonempty ∧
            Disjoint D E ∧ Disjoint D S ∧ Disjoint E S ∧ Disjoint D C ∧
            ∀ x∈D, ∀ y, G.Adj x y → y∈D ∨ y∈S := by
          by_cases hac : Disjoint A C
          · exact ⟨A,B,hA,hB,hAB,hAS,hBS,hac,hclosedA⟩
          · have hBC : Disjoint B C := by
              rw [Set.disjoint_left]
              intro y hyB hyC
              obtain ⟨x,hxA,hxC⟩ := Set.not_disjoint_iff.mp hac
              have hxy : x≠y := fun he ↦ Set.disjoint_left.mp hAB hxA (he ▸ hyB)
              exact hcross x hxA y hyB (hC hxC hyC hxy)
            exact ⟨B,A,hB,hA,hAB.symm,hBS,hAS,hBC,hclosedB⟩
        obtain ⟨D,E,hD,hE,hDE,hDS,hES,hDC,hclosed⟩ := hchoice
        let U := D∪S
        obtain ⟨e,he⟩ := hE
        have heU : e∉U := by
          rintro (heD|heS)
          · exact Set.disjoint_left.mp hDE heD he
          · exact Set.disjoint_left.mp hES he heS
        have hlt : Fintype.card U<n := by
          rw [←hcard]
          exact Fintype.card_subtype_lt (x:=e) heU
        let C' : Set U := {x | x.1∈S}
        have hC' : (G.induce U).IsClique C' := by
          intro x hx y hy hxy
          exact hS hx hy (fun he ↦ hxy (Subtype.ext he))
        have hproper' : ∃ x : U, x∉C' := by
          obtain ⟨d,hd⟩ := hD
          exact ⟨⟨d,Or.inl hd⟩,fun hs ↦ Set.disjoint_left.mp hDS hd hs⟩
        have hGU : IsChordal (G.induce U) := hG.of_embedding (Embedding.induce U)
        obtain ⟨v,hv,hvs⟩ := ih _ hlt U rfl (G.induce U) hGU C' hC' hproper'
        have hvD : v.1∈D := v.2.resolve_right hv
        refine ⟨v.1,fun hc ↦ Set.disjoint_left.mp hDC hvD hc,?_⟩
        intro x hx y hy hxy
        have hxU : x∈U := hclosed v.1 hvD x hx
        have hyU : y∈U := hclosed v.1 hvD y hy
        exact hvs (x:=⟨x,hxU⟩) (y:=⟨y,hyU⟩) hx hy
          (fun he ↦ hxy (congrArg Subtype.val he))
  exact main _ V rfl G hG C hC hproper

/-- Graph Minors V, (8.4), page 110:
"If $G$ is chordal and non-null then $G$ has a vertex $v$ such that the vertices adjacent to $v$ are pairwise adjacent."
The result is quoted from Dirac [3]; the proof here uses minimal clique
separators and induction, with the empty clique as the set to avoid. -/
theorem theorem_8_4_proof {V : Type u} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (hG : IsChordal G) : ∃ v, IsSimplicial G v := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨w,_,hw⟩ := exists_simplicial_outside_clique hG
    (C:=∅) (by intro x hx; exact (notMem_empty x hx).elim) ⟨v,notMem_empty v⟩
  exact ⟨w,hw⟩

/-- The full universally quantified simplicial-vertex statement (8.4). -/
theorem statement84_proved : Theorem84Statement.{u} := fun G hG ↦ theorem_8_4_proof G hG

end GraphMinor.GM05
