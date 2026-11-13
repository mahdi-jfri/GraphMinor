module

public import GraphMinor.GM08.Defs
import GraphMinor.GM08.Section3
import GraphMinor.GM08.Section4
import GraphMinor.GM08.Section13

/-!
# Rootless grafts that are direct sums of many grafts

Page 288 of VIII: "It follows from (3.3) that `𝒞(h, 0)` is well-rooted; for if
`(G, ∅) ∈ 𝒞(h, 0)` there are grafts `(G₁, ∅), …, (G_r, ∅) ∈ 𝒟(h, 0)` such that
`(G, ∅) = (G₁, ∅) ⊕ ⋯ ⊕ (G_r, ∅)`."

We write `IsGraftListSum X L` when `X` is the direct sum of the grafts in the
list `L`, summed from the left, with the empty graft for the empty list. If
the list of `X` is below the list of a rootless `X'` in the order of (3.3)
(a sublist, compared term by term), then `X` is simulated in `X'`
(`isGraftSimulatedIn_of_listSum`). So by (3.3) the rootless direct sums of
members of a well-rooted class form a well-rooted class
(`isWellRooted_of_listSum`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph

universe u v

/-- `X` is the direct sum of the grafts of the list `L`: the empty graft for
the empty list, and `A ⊕ Y` for `A :: L` with `Y` the sum of `L`. -/
inductive IsGraftListSum {α : Type u} {β : Type v} : Graft α β → List (Graft α β) → Prop
  | nil {X : Graft α β} (h : V(X.G) = ∅) : IsGraftListSum X []
  | cons {X A Y : Graft α β} {L : List (Graft α β)} (h : IsGraftDirectSum X A Y)
      (hY : IsGraftListSum Y L) : IsGraftListSum X (A :: L)

/-- A graft with no vertices is simulated in every rootless graft. -/
theorem isGraftSimulatedIn_of_vertexSet_eq_empty {α : Type u} {β : Type v}
    {Y X : Graft α β} (hY : V(Y.G) = ∅) (hX : X.T = ∅) : IsGraftSimulatedIn Y X := by
  have hE : E(Y.G) = ∅ := by
    apply eq_empty_of_forall_notMem
    intro e he
    obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have := hl.left_mem
    rw [hY] at this
    exact this
  have hT : Y.T = ∅ := subset_empty_iff.mp (hY ▸ Y.T_subset)
  refine ⟨fun _ => ∅, id, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hX, hT], ?_⟩ <;>
    simp [hY, hE, hT]

/-- The empty graft and `X` sum to `X`. -/
theorem isGraftDirectSum_empty_left {α : Type u} {β : Type v} (X : Graft α β) :
    ∃ E₀ : Graft α β, V(E₀.G) = ∅ ∧ IsGraftDirectSum X E₀ X := by
  refine ⟨⟨X.G.induce ∅, ∅, empty_subset _, ⟨by simp, by
    refine (X.finite_G.2).subset ?_
    intro e he
    exact (Graph.induce_le (empty_subset _)).edgeSet_mono he⟩⟩, by simp, ∅, empty_subset _,
    fun _ _ _ _ => Iff.rfl, rfl, ?_, by simp, by simp⟩
  rw [sdiff_empty, Graph.induce_vertexSet]

/-- The summands of a rootless sum are rootless. -/
theorem IsGraftDirectSum.T_right_eq_empty {α : Type u} {β : Type v} {X A Y : Graft α β}
    (h : IsGraftDirectSum X A Y) (hX : X.T = ∅) : Y.T = ∅ := by
  obtain ⟨_, _, _, _, _, _, hY⟩ := h
  rw [hY, hX, empty_sdiff]

/-- The summands of a rootless sum are rootless. -/
theorem IsGraftDirectSum.T_left_eq_empty {α : Type u} {β : Type v} {X A Y : Graft α β}
    (h : IsGraftDirectSum X A Y) (hX : X.T = ∅) : A.T = ∅ := by
  obtain ⟨_, _, _, _, _, hA, _⟩ := h
  rw [hA, hX, empty_inter]

/-- **Sums of comparable lists.** If the list of `X` is below the list of the
rootless graft `X'` in the order of (3.3), then `X` is simulated in `X'`. -/
theorem isGraftSimulatedIn_of_listSum {α : Type u} {β : Type v}
    {L L' : List (Graft α β)} (h : List.SublistForall₂ IsGraftSimulatedIn L L') :
    ∀ {X X' : Graft α β}, IsGraftListSum X L → IsGraftListSum X' L' → X'.T = ∅ →
      IsGraftSimulatedIn X X' := by
  induction h with
  | nil =>
    intro X X' hX _ hT
    cases hX with
    | nil hV => exact isGraftSimulatedIn_of_vertexSet_eq_empty hV hT
  | cons hab _ ih =>
    intro X X' hX hX' hT
    cases hX with
    | cons hXs hY =>
      cases hX' with
      | cons hX's hY' =>
        exact isGraftSimulatedIn_of_isGraftDirectSum hXs hX's hab
          (ih hY hY' (hX's.T_right_eq_empty hT))
  | cons_right _ ih =>
    intro X X' hX hX' hT
    cases hX' with
    | cons hX's hY' =>
      obtain ⟨E₀, hE₀, hsum⟩ := isGraftDirectSum_empty_left X
      exact isGraftSimulatedIn_of_isGraftDirectSum hsum hX's
        (isGraftSimulatedIn_of_vertexSet_eq_empty hE₀ (hX's.T_left_eq_empty hT))
        (ih hX hY' (hX's.T_right_eq_empty hT))

/-- The order of (3.3) on a list of members of a subtype, read on the
underlying grafts. -/
theorem sublistForall₂_map_val {α : Type u} {β : Type v} {𝒟 : Set (Graft α β)}
    {l l' : List 𝒟}
    (h : List.SublistForall₂ (fun A B : 𝒟 => IsGraftSimulatedIn A.1 B.1) l l') :
    List.SublistForall₂ IsGraftSimulatedIn (l.map Subtype.val) (l'.map Subtype.val) := by
  induction h with
  | nil => exact List.SublistForall₂.nil
  | cons hab _ ih => exact List.SublistForall₂.cons hab ih
  | cons_right _ ih => exact List.SublistForall₂.cons_right ih

/-- **Rootless sums of a well-rooted class**, from (3.3) (page 288). If every
member of `𝒞` is rootless and is the direct sum of a list of members of the
well-rooted class `𝒟`, then `𝒞` is well-rooted. -/
theorem isWellRooted_of_listSum {α : Type u} {β : Type v} {𝒟 𝒞 : Set (Graft α β)}
    (hD : IsWellRootedGraftClass 𝒟)
    (hC : ∀ X ∈ 𝒞, X.T = ∅ ∧ ∃ L : List (Graft α β), (∀ A ∈ L, A ∈ 𝒟) ∧ IsGraftListSum X L) :
    IsWellRootedGraftClass 𝒞 := by
  intro X hX
  have hWQO : IsWellQuasiOrder (fun (A B : 𝒟) => IsGraftSimulatedIn A.1 B.1) := by
    refine ⟨⟨fun A => IsGraftSimulatedIn.refl A.1, fun _ _ _ => IsGraftSimulatedIn.trans⟩, ?_⟩
    intro q
    exact hD (fun n => (q n).1) (fun n => (q n).2)
  have hL : ∀ n, ∃ l : List 𝒟, IsGraftListSum (X n) (l.map Subtype.val) := by
    intro n
    obtain ⟨-, L, hLD, hsum⟩ := hC _ (hX n)
    refine ⟨L.attach.map (fun A => ⟨A.1, hLD A.1 A.2⟩), ?_⟩
    rw [List.map_map]
    convert hsum
    simp
  choose l hl using hL
  obtain ⟨i, j, hij, hle⟩ := (theorem_3_3_proof hWQO).2 l
  exact ⟨i, j, hij, isGraftSimulatedIn_of_listSum (sublistForall₂_map_val hle) (hl i) (hl j)
    (hC _ (hX j)).1⟩

end GraphMinor.GM08
