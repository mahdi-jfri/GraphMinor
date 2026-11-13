module

public import GraphMinor.HP25.Web
public import GraphMinor.HP25.Defs
import GraphMinor.HP25.Completion
import GraphMinor.HP25.Embedding
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Case2
import GraphMinor.HP25.Prop34

/-!
# Proposition 5.1: splitting a graph along a separating `C`-path

Humeau and Pous, Proposition 5.1 (page 16): "Let $P$ be a $C$-path of $G$ between non-consecutive
vertices of $C$, and let $P_1$ and $P_2$ be the two distinct subpaths of $C$ sharing their endpoints
with $P$ and such that $C=P_1\overline{P_2}$. If $P$ separates $\mathring{P_1}$ from
$\mathring{P_2}$ then $P_1$ and $P_2$ are contained in subgraphs $G_1$ and $G_2$ of $G$,
respectively, and $G$ is the path composition of $G_1$ and $G_2$ along $P$."

We write the cycle, up to rotation, as `a A b B`, so that `P₁ = a A b` and `P₂ = a B⁻¹ b`; the
ends `a`, `b` are not consecutive when `A` and `B` are not empty. Path composition along `P`
(Section 3.2, page 8) glues two graphs along a common path. For two subgraphs `G₁`, `G₂` of `G`
with vertex sets `S₁`, `S₂` this means (`IsPathComposition`): `G = G₁ ∪ G₂`, the vertex sets cover
all vertices and meet exactly in `P`, and `P` is a path of both.

The proof follows the paper: `S₁` is `P` together with the vertices that `A` reaches in `G - P`, and
`S₂` is `P` together with all other vertices; `G₁` and `G₂` are the induced subgraphs. The paper
moves each chord of `P` to one side only; we keep the chords on both sides, which changes nothing
since the union of two simple graphs keeps one copy of each edge.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- "A subset $X$ of vertices *separates* two sets of vertices $U$ and $V$ when all $U$-$V$ paths
contain a vertex of $X$" (Section 2.1, page 5). -/
@[expose] def Separates (G : SimpleGraph V) (X U W : Set V) : Prop :=
  ∀ u ∈ U, ∀ w ∈ W, ∀ p : G.Walk u w, ∃ v ∈ p.support, v ∈ X

/-- `G` is the path composition along the path `l` of its subgraphs `G₁` on `S₁` and `G₂` on `S₂`
(Section 3.2, page 8, for subgraphs): `G = G₁ ∪ G₂`, the two vertex sets cover all vertices and
meet in the vertices of `l`, and `l` is a path of both. -/
@[expose] def IsPathComposition (G G₁ G₂ : SimpleGraph V) (S₁ S₂ : Set V) (l : List V) : Prop :=
  G = G₁ ⊔ G₂ ∧ IsSupportedOn G₁ S₁ ∧ IsSupportedOn G₂ S₂ ∧ S₁ ∪ S₂ = univ ∧
    S₁ ∩ S₂ = {v | v ∈ l} ∧ l.IsChain G₁.Adj ∧ l.IsChain G₂.Adj

/-- **Proposition 5.1** (page 16). Let `C` be a cycle of `G` with `C = a A b B` up to rotation, `A`
and `B` not empty, and `P` a `C`-path from `a` to `b`. If `P` separates `A` from `B`, then `G` is
the path composition along `P` of two subgraphs `G₁ ⊇ a A b` and `G₂ ⊇ b B a`. -/
theorem prop_5_1 {C : List V} (hC : IsCycleList G C) {a b : V} {A B : List V} {k : ℕ}
    (hrot : C.rotate k = a :: A ++ b :: B) {P : G.Walk a b} (hP : IsTPath G C P)
    (hsep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B}) :
    ∃ (G₁ G₂ : SimpleGraph V) (S₁ S₂ : Set V), IsPathComposition G G₁ G₂ S₁ S₂ P.support ∧
      (a :: A ++ [b]).IsChain G₁.Adj ∧ (∀ v ∈ a :: A ++ [b], v ∈ S₁) ∧
      (b :: B ++ [a]).IsChain G₂.Adj ∧ (∀ v ∈ b :: B ++ [a], v ∈ S₂) := by
  classical
  have hC' : IsCycleList G (a :: A ++ b :: B) := hrot ▸ hC.rotate k
  have hnd := hC'.2.1
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
  have hmemC : ∀ v, v ∈ a :: A ++ b :: B → v ∈ C := fun v hv =>
    List.mem_rotate.mp (hrot ▸ hv)
  -- the inner vertices of `P₁` and `P₂` are off `P`
  have hoff : ∀ v ∈ A ++ B, v ∉ P.support := by
    intro v hv hvP
    have hva : v ≠ a := fun e => hnd.1 (by
      subst e
      rcases List.mem_append.mp hv with h | h <;> simp [h])
    have hvb : v ≠ b := fun e => by
      subst e
      rcases List.mem_append.mp hv with hv | hv
      · exact hnd.2.2.2 v hv v (by simp) rfl
      · exact (List.nodup_cons.mp hnd.2.2.1).1 hv
    exact (hP.2.2.2 v hvP hva hvb).1 (hmemC v (by
      rcases List.mem_append.mp hv with hv | hv <;> simp [hv]))
  have hAP : ∀ v ∈ A, v ∉ P.support := fun v hv => hoff v (List.mem_append_left _ hv)
  have hBP : ∀ v ∈ B, v ∉ P.support := fun v hv => hoff v (List.mem_append_right _ hv)
  -- the vertices reached from `A` in `G - P`
  set Rch : Set V := {v | ∃ u ∈ A, (restrict G {w | w ∉ P.support}).Reachable u v} with hRch
  have hRP : ∀ v ∈ Rch, v ∉ P.support := by
    rintro v ⟨u, hu, ⟨W⟩⟩
    by_cases hvu : v = u
    · exact hvu ▸ hAP u hu
    · exact mem_of_mem_support_restrict W W.end_mem_support hvu
  have hRadj : ∀ u v, u ∈ Rch → v ∉ P.support → G.Adj u v → v ∈ Rch := by
    rintro u v ⟨w, hw, hr⟩ hv huv
    exact ⟨w, hw, hr.trans (Adj.reachable ⟨huv, hRP u ⟨w, hw, hr⟩, hv⟩)⟩
  have hBR : ∀ v ∈ B, v ∉ Rch := by
    rintro v hv ⟨u, hu, ⟨W⟩⟩
    obtain ⟨w, hw, hwP⟩ := hsep u hu v hv (W.mapLe (restrict_le G _))
    rw [Walk.support_mapLe_eq_support] at hw
    by_cases hwu : w = u
    · exact hAP u hu (hwu ▸ hwP)
    · exact mem_of_mem_support_restrict W hw hwu hwP
  set S₁ : Set V := {v | v ∈ P.support} ∪ Rch with hS₁
  set S₂ : Set V := {v | v ∈ P.support} ∪ Rchᶜ with hS₂
  have hP₁ := (hC'.isPathList (R := univ) fun _ _ => trivial)
  have e₁ : a :: A ++ b :: B = (a :: A ++ [b]) ++ B := by simp
  rw [e₁] at hP₁
  have hP₂ := ((hC'.rotate (A.length + 1)).isPathList (R := univ) fun _ _ => trivial)
  rw [rotate_cons_append_cons] at hP₂
  have e₂ : b :: B ++ a :: A = (b :: B ++ [a]) ++ A := by simp
  rw [e₂] at hP₂
  have haP : a ∈ P.support := P.start_mem_support
  have hbP : b ∈ P.support := P.end_mem_support
  have hin₁ : ∀ v ∈ a :: A ++ [b], v ∈ S₁ := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | hv | rfl
    · exact Or.inl haP
    · exact Or.inr ⟨v, hv, Reachable.refl _⟩
    · exact Or.inl hbP
  have hin₂ : ∀ v ∈ b :: B ++ [a], v ∈ S₂ := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | hv | rfl
    · exact Or.inl hbP
    · exact Or.inr (hBR v hv)
    · exact Or.inl haP
  refine ⟨restrict G S₁, restrict G S₂, S₁, S₂, ⟨?_, fun _ _ h => h.2.1, fun _ _ h => h.2.1,
    ?_, ?_, isChain_restrict P.isChain_adj_support fun v hv => Or.inl hv,
    isChain_restrict P.isChain_adj_support fun v hv => Or.inl hv⟩,
    isChain_restrict hP₁.prefix.2.1 hin₁, hin₁, isChain_restrict hP₂.prefix.2.1 hin₂, hin₂⟩
  · -- every edge lies on one side
    ext u v
    refine ⟨fun huv => ?_, fun h => ?_⟩
    · by_cases huP : u ∈ P.support
      · by_cases hvR : v ∈ Rch
        · exact Or.inl ⟨huv, Or.inl huP, Or.inr hvR⟩
        · exact Or.inr ⟨huv, Or.inl huP, Or.inr hvR⟩
      · by_cases huR : u ∈ Rch
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
    simp only [hS₁, hS₂, mem_union, mem_compl_iff, mem_univ, iff_true]
    tauto
  · ext v
    simp only [hS₁, hS₂, mem_inter_iff, mem_union, mem_compl_iff, mem_ofPred_eq]
    tauto

end GraphMinor.HP25
