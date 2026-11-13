module

public import GraphMinor.Minor.Model
import Mathlib.Combinatorics.Graph.Delete

/-!
# A minor model from connected branches and representing edges

In GM V, (8.14), contract each connected star branch and retain the
middle edge of each original edge. Distinct branches have disjoint
vertex sets, and the representing edges have their ends in the
appropriate branches. The branches avoid all representing edges.
These data give the minor model, including its incidence conditions.
-/

public section
namespace GraphMinor.GM05
open Set Graph
universe u v u' v'

/-- The branch contraction step in GM V, proof of (8.14), page 113,
for a loopless source. The maps retain precisely the given branches
and representing edges on the source support sets. -/
theorem exists_minor_model_of_branches_and_edges
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} [Nonempty β]
    (H : Graph α' β') (G : Graph α β) (u v : E(H) → V(H))
    (hlink : ∀ e, H.IsLink e.val (u e).val (v e).val) (hne : ∀ e, u e ≠ v e)
    (K : V(H) → Graph α β) (ε : E(H) → β) (p q : E(H) → α)
    (hK : ∀ a, K a ≤ G.deleteEdges (range ε)) (hconn : ∀ a, GraphConnected (K a))
    (hdis : Pairwise (fun a b ↦ Disjoint V(K a) V(K b))) (hε : Function.Injective ε)
    (hedge : ∀ e, G.IsLink (ε e) (p e) (q e))
    (hp : ∀ e, p e ∈ V(K (u e))) (hq : ∀ e, q e ∈ V(K (v e))) :
    ∃ ηv ηe, IsMinorModel H G ηv ηe ∧
      (∀ a (ha : a ∈ V(H)), ηv a = V(K ⟨a,ha⟩)) ∧
      ∀ e (he : e ∈ E(H)), ηe e = ε ⟨e,he⟩ := by
  classical
  let ηv : α' → Set α := fun a ↦ if ha : a ∈ V(H) then V(K ⟨a,ha⟩) else ∅
  let ηe : β' → β := fun e ↦ if he : e ∈ E(H) then ε ⟨e,he⟩ else Classical.choice inferInstance
  have hηv : ∀ a (ha : a ∈ V(H)), ηv a = V(K ⟨a,ha⟩) := by
    intro a ha
    simp only [ηv,dite_eq_left ha]
  have hηe : ∀ e (he : e ∈ E(H)), ηe e = ε ⟨e,he⟩ := by
    intro e he
    simp only [ηe,dite_eq_left he]
  have hsame : ∀ a b : V(H), ∀ x, x ∈ V(K a) → x ∈ V(K b) → a = b := by
    intro a b x hxa hxb
    by_contra hab
    exact disjoint_left.mp (hdis hab) hxa hxb
  have himage : ηe '' E(H) = range ε := by
    ext b
    constructor
    · rintro ⟨e,he,rfl⟩
      rw [hηe e he]
      exact ⟨⟨e,he⟩,rfl⟩
    · rintro ⟨e,rfl⟩
      exact ⟨e.val,e.prop,hηe e.val e.prop⟩
  refine ⟨ηv,ηe,?_,hηv,hηe⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a ha
    rw [hηv a ha]
    exact (hconn ⟨a,ha⟩).1
  · intro a ha
    rw [hηv a ha]
    exact ((hK ⟨a,ha⟩).trans Graph.deleteEdges_le).vertexSet_mono
  · intro e he
    rw [hηe e he]
    exact (hedge ⟨e,he⟩).edge_mem
  · intro a ha b hb hab
    rw [hηv a ha,hηv b hb]
    exact hdis (fun he ↦ hab (congrArg Subtype.val he))
  · intro e he f hf hef
    rw [hηe e he,hηe f hf] at hef
    exact congrArg Subtype.val (hε hef)
  · intro a ha e he
    rw [hηv a ha,hηe e he]
    let a₀ : V(H) := ⟨a,ha⟩
    let e₀ : E(H) := ⟨e,he⟩
    constructor
    · intro hinc
      rcases hinc.eq_or_eq_of_isLink (hlink e₀) with hh | hh
      · have hai : a₀ = u e₀ := Subtype.ext hh
        have hpa : p e₀ ∈ V(K a₀) := by rw [hai]; exact hp e₀
        exact ⟨p e₀,hpa,(hedge e₀).inc_left⟩
      · have hai : a₀ = v e₀ := Subtype.ext hh
        have hqa : q e₀ ∈ V(K a₀) := by rw [hai]; exact hq e₀
        exact ⟨q e₀,hqa,(hedge e₀).inc_right⟩
    · rintro ⟨x,hx,hinc⟩
      rcases hinc.eq_or_eq_of_isLink (hedge e₀) with rfl | rfl
      · have hai := hsame a₀ (u e₀) (p e₀) hx (hp e₀)
        have hval : a = (u e₀).val := congrArg Subtype.val hai
        exact hval.symm ▸ (hlink e₀).inc_left
      · have hai := hsame a₀ (v e₀) (q e₀) hx (hq e₀)
        have hval : a = (v e₀).val := congrArg Subtype.val hai
        exact hval.symm ▸ (hlink e₀).inc_right
  · intro a ha e he
    rw [hηv a ha,hηe e he]
    let a₀ : V(H) := ⟨a,ha⟩
    let e₀ : E(H) := ⟨e,he⟩
    constructor
    · intro hloop
      rcases (hlink e₀).eq_and_eq_or_eq_and_eq hloop with ⟨hu,hv⟩ | ⟨hu,hv⟩
      all_goals exact (hne e₀ (Subtype.ext (hu.trans hv.symm))).elim
    · intro hall
      have hau := hsame a₀ (u e₀) (p e₀) (hall (p e₀) (hedge e₀).inc_left) (hp e₀)
      have hav := hsame a₀ (v e₀) (q e₀) (hall (q e₀) (hedge e₀).inc_right) (hq e₀)
      exact (hne e₀ (hau.symm.trans hav)).elim
  · intro a ha
    refine ⟨K ⟨a,ha⟩,?_,(hηv a ha).symm,hconn ⟨a,ha⟩⟩
    rw [himage]
    exact hK ⟨a,ha⟩

end GraphMinor.GM05
