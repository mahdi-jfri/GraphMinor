module

public import GraphMinor.Compute.TwoPathsSpec
import GraphMinor.HP25.Method
import GraphMinor.HP25.Completion
import GraphMinor.HP25.Embedding
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Case2
import GraphMinor.HP25.CycleEdges

/-!
# The two subinstances of line 10 of Algorithm 5.1

Humeau and Pous, Proposition 5.1 (page 16), split a graph along a separating `C`-path `P`: "The
graph $G_i$ is defined as the subgraph of $G$ induced by the union of $P$ with the components of
$G-P$ associated with $G_i$". The program splits with the explicit sides `sideOne` and `sideTwo`
of `GraphMinor/Compute/TwoPathsSpec.lean`: the first side is `P` together with what `A` reaches in
`G - P`, the second is `P` together with the rest. `isPathComposition_sides` proves that these
sides give a path composition along `P`, by the argument of `prop_5_1`
(`GraphMinor/HP25/Prop51.lean`), whose statement only says that some sides exist.

`isCrossed_iff_sub` is then line 11 of Algorithm 5.1 for these sides: after a completion `F` with
path `P' = a m b`, the cycle `C = a A b B` is crossed in `H` exactly when the cycle of one of the two
subinstances is crossed in its graph (`isCrossed_iff_of_completion`,
`GraphMinor/HP25/Method.lean`).

`sideOne_inter_cycle` and `sideTwo_inter_cycle` say which vertices of `C` lie on each side. The
count of recursive calls uses them.
-/

public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph Set GraphMinor.HP25

variable {V : Type*} {G : SimpleGraph V}

/-- The vertices that `A` reaches off `P` are not on `P`. -/
theorem notMem_of_mem_reachOff {Pv A : List V} (hA : ∀ v ∈ A, v ∉ Pv) {v : V}
    (hv : v ∈ reachOff G Pv A) : v ∉ Pv := by
  obtain ⟨u, hu, ⟨W⟩⟩ := hv
  by_cases hvu : v = u
  · exact hvu ▸ hA u hu
  · exact mem_of_mem_support_restrict W W.end_mem_support hvu

/-- A vertex of `B` is not reached from `A` off `P` when `P` separates `A` from `B`. -/
theorem notMem_reachOff_of_separates {Pv A B : List V} (hA : ∀ v ∈ A, v ∉ Pv)
    (hsep : Separates G {v | v ∈ Pv} {v | v ∈ A} {v | v ∈ B}) {v : V} (hv : v ∈ B) :
    v ∉ reachOff G Pv A := by
  rintro ⟨u, hu, ⟨W⟩⟩
  obtain ⟨w, hw, hwP⟩ := hsep u hu v hv (W.mapLe (restrict_le G _))
  rw [Walk.support_mapLe_eq_support] at hw
  by_cases hwu : w = u
  · exact hA u hu (hwu ▸ hwP)
  · exact mem_of_mem_support_restrict W hw hwu hwP

/-- The setting of a split: `a A b B` is a cycle, `A` and `B` are not empty, and `P` is a `C`-path
from `a` to `b`. Then no vertex of `A` or `B` is on `P`. -/
theorem notMem_support_of_mem {a b : V} {A B : List V}
    (hC : IsCycleList G (a :: A ++ b :: B)) {P : G.Walk a b} (hP : IsTPath G (a :: A ++ b :: B) P)
    {v : V} (hv : v ∈ A ++ B) : v ∉ P.support := by
  have hnd := hC.2.1
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
  intro hvP
  have hva : v ≠ a := fun e => hnd.1 (by
    subst e
    rcases List.mem_append.mp hv with h | h <;> simp [h])
  have hvb : v ≠ b := fun e => by
    subst e
    rcases List.mem_append.mp hv with hv | hv
    · exact hnd.2.2.2 v hv v (by simp) rfl
    · exact (List.nodup_cons.mp hnd.2.2.1).1 hv
  exact (hP.2.2.2 v hvP hva hvb).1 (by
    rcases List.mem_append.mp hv with hv | hv <;> simp [hv])

/-- **Proposition 5.1 with explicit sides.** If `a A b B` is a cycle with `A`, `B` not empty and
`P` is a `C`-path from `a` to `b` that separates `A` from `B`, then `G` is the path composition
along `P` of the graphs induced by `sideOne` and `sideTwo`, which contain `a A b` and `b B a`. -/
theorem isPathComposition_sides {a b : V} {A B : List V}
    (hC : IsCycleList G (a :: A ++ b :: B)) {P : G.Walk a b}
    (hP : IsTPath G (a :: A ++ b :: B) P)
    (hsep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B}) :
    IsPathComposition G (restrict G (sideOne G P.support A)) (restrict G (sideTwo G P.support A))
        (sideOne G P.support A) (sideTwo G P.support A) P.support ∧
      (a :: A ++ [b]).IsChain (restrict G (sideOne G P.support A)).Adj ∧
      (∀ v ∈ a :: A ++ [b], v ∈ sideOne G P.support A) ∧
      (b :: B ++ [a]).IsChain (restrict G (sideTwo G P.support A)).Adj ∧
      (∀ v ∈ b :: B ++ [a], v ∈ sideTwo G P.support A) := by
  classical
  have hAP : ∀ v ∈ A, v ∉ P.support := fun v hv =>
    notMem_support_of_mem hC hP (List.mem_append_left _ hv)
  have hRP : ∀ v ∈ reachOff G P.support A, v ∉ P.support := fun v hv =>
    notMem_of_mem_reachOff hAP hv
  have hRadj : ∀ u v, u ∈ reachOff G P.support A → v ∉ P.support → G.Adj u v →
      v ∈ reachOff G P.support A := by
    rintro u v ⟨w, hw, hr⟩ hv huv
    exact ⟨w, hw, hr.trans (Adj.reachable ⟨huv, hRP u ⟨w, hw, hr⟩, hv⟩)⟩
  have hBR : ∀ v ∈ B, v ∉ reachOff G P.support A := fun v hv =>
    notMem_reachOff_of_separates hAP hsep hv
  have hP₁ := (hC.isPathList (R := univ) fun _ _ => trivial)
  have e₁ : a :: A ++ b :: B = (a :: A ++ [b]) ++ B := by simp
  rw [e₁] at hP₁
  have hP₂ := ((hC.rotate (A.length + 1)).isPathList (R := univ) fun _ _ => trivial)
  rw [rotate_cons_append_cons] at hP₂
  have e₂ : b :: B ++ a :: A = (b :: B ++ [a]) ++ A := by simp
  rw [e₂] at hP₂
  have haP : a ∈ P.support := P.start_mem_support
  have hbP : b ∈ P.support := P.end_mem_support
  have hin₁ : ∀ v ∈ a :: A ++ [b], v ∈ sideOne G P.support A := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | hv | rfl
    · exact Or.inl haP
    · exact Or.inr ⟨v, hv, Reachable.refl _⟩
    · exact Or.inl hbP
  have hin₂ : ∀ v ∈ b :: B ++ [a], v ∈ sideTwo G P.support A := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | hv | rfl
    · exact Or.inl hbP
    · exact Or.inr (hBR v hv)
    · exact Or.inl haP
  refine ⟨⟨?_, fun _ _ h => h.2.1, fun _ _ h => h.2.1, ?_, ?_,
    isChain_restrict P.isChain_adj_support fun v hv => Or.inl hv,
    isChain_restrict P.isChain_adj_support fun v hv => Or.inl hv⟩,
    isChain_restrict hP₁.prefix.2.1 hin₁, hin₁, isChain_restrict hP₂.prefix.2.1 hin₂, hin₂⟩
  · ext u v
    refine ⟨fun huv => ?_, fun h => ?_⟩
    · by_cases huP : u ∈ P.support
      · by_cases hvR : v ∈ reachOff G P.support A
        · exact Or.inl ⟨huv, Or.inl huP, Or.inr hvR⟩
        · exact Or.inr ⟨huv, Or.inl huP, Or.inr hvR⟩
      · by_cases huR : u ∈ reachOff G P.support A
        · refine Or.inl ⟨huv, Or.inr huR, ?_⟩
          by_cases hvP : v ∈ P.support
          · exact Or.inl hvP
          · exact Or.inr (hRadj u v huR hvP huv)
        · refine Or.inr ⟨huv, Or.inr huR, ?_⟩
          by_cases hvP : v ∈ P.support
          · exact Or.inl hvP
          · exact Or.inr fun hvR => huR (hRadj v u hvR huP huv.symm)
    · rcases h with h | h
      · exact h.1
      · exact h.1
  · ext v
    simp only [sideOne, sideTwo, mem_union, mem_compl_iff, mem_univ, iff_true]
    tauto
  · ext v
    simp only [sideOne, sideTwo, mem_inter_iff, mem_union, mem_compl_iff, mem_ofPred_eq]
    tauto

/-- **Line 11 of Algorithm 5.1, with the program's sides.** Let `a A b B` be a cycle of `H` with `A`,
`B` not empty, `F` safe for it, and `P' = a m b` a `C`-path of `H ⊔ F` that separates `A` from `B`
and whose vertices are all on both sides. Then `C` is crossed in `H` exactly when the cycle of
subinstance `1` or of subinstance `2` is crossed in its graph. -/
theorem isCrossed_iff_sub [Finite V] {H F : SimpleGraph V} {a b : V} {A B m : List V}
    (hC : IsCycleList H (a :: A ++ b :: B)) (hA : A ≠ []) (hB : B ≠ [])
    (hsafe : IsSafe H F (a :: A ++ b :: B)) {P' : (H ⊔ F).Walk a b}
    (hP' : IsTPath (H ⊔ F) (a :: A ++ b :: B) P') (hm : P'.support = a :: m ++ [b])
    (hsides : OnBothSides (H ⊔ F) (a :: A ++ b :: B) A B P')
    (hsep : Separates (H ⊔ F) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B}) :
    IsCrossed H (a :: A ++ b :: B) ↔
      IsCrossed (subGraph (H ⊔ F) P'.support A 1) (subCycle a b A B m 1) ∨
        IsCrossed (subGraph (H ⊔ F) P'.support A 2) (subCycle a b A B m 2) := by
  obtain ⟨hcomp, h1, h2, h3, h4⟩ := isPathComposition_sides (hC.mono le_sup_left) hP' hsep
  exact isCrossed_iff_of_completion hC (k := 0) (by simp) hA hB hsafe hP' hm hsides hsep hcomp
    h1 h2 h3 h4

/-- The vertices of `C = a A b B` on the first side are those of `a A b`. -/
theorem sideOne_inter_cycle {a b : V} {A B : List V}
    (hC : IsCycleList G (a :: A ++ b :: B)) {P : G.Walk a b}
    (hP : IsTPath G (a :: A ++ b :: B) P)
    (hsep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B}) {v : V}
    (hv : v ∈ a :: A ++ b :: B) (h1 : v ∈ sideOne G P.support A) : v ∈ a :: A ++ [b] := by
  have hAP : ∀ v ∈ A, v ∉ P.support := fun v hv =>
    notMem_support_of_mem hC hP (List.mem_append_left _ hv)
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hv ⊢
  rcases hv with rfl | hv | rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr (by simp))
  · exfalso
    rcases h1 with h | h
    · exact notMem_support_of_mem hC hP (List.mem_append_right _ hv) h
    · exact notMem_reachOff_of_separates hAP hsep hv h

/-- The vertices of `C = a A b B` on the second side are those of `b B a`. -/
theorem sideTwo_inter_cycle {a b : V} {A B : List V}
    (hC : IsCycleList G (a :: A ++ b :: B)) {P : G.Walk a b}
    (hP : IsTPath G (a :: A ++ b :: B) P) {v : V}
    (hv : v ∈ a :: A ++ b :: B) (h2 : v ∈ sideTwo G P.support A) : v ∈ b :: B ++ [a] := by
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hv ⊢
  rcases hv with rfl | hv | rfl | hv
  · exact Or.inr (Or.inr (by simp))
  · exfalso
    rcases h2 with h | h
    · exact notMem_support_of_mem hC hP (List.mem_append_left _ hv) h
    · exact h ⟨v, hv, Reachable.refl _⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hv)

end GraphMinor.Compute.TwoPaths
