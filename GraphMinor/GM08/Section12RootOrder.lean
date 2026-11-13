module

public import GraphMinor.GM08.Defs

/-!
# Ordering the roots in the disc induction

Section 12 orders each graft's root set before taking a derived portrait.
A finite root set has a list ordering without repetitions, whose length
is its index. A simulation respecting these lists is a simulation of
the original grafts after the order is forgotten. These are the two
root-order steps in the proof on page 274.
-/

public section

namespace GraphMinor.GM08

open Set

universe u v u' v'

/-- The underlying graft of a rooted graph with distinct roots has the
same index. This identifies the indices in VIII, Section 12. -/
theorem graft_index_eq_of_nodup {α : Type u} {β : Type v} (X : RootedGraph α β)
    (hX : X.τ.Nodup) : X.toGraft.index = X.index := by
  classical
  change {v | v ∈ X.τ}.ncard = X.τ.length
  have hs : {v | v ∈ X.τ} = (X.τ.toFinset : Set α) := by ext v; simp
  rw [hs, ncard_coe_finset, List.toFinset_card_of_nodup hX]

/-- Order the finite root set of a graft without repetitions, as in
VIII, Section 12, page 274. The underlying graft and index are unchanged. -/
theorem exists_root_order {α : Type u} {β : Type v} (X : Graft α β) :
    ∃ R : RootedGraph α β, R.toGraft = X ∧ R.τ.Nodup ∧ R.index = X.index := by
  classical
  have hT : X.T.Finite := X.finite_G.1.subset X.T_subset
  let l := hT.toFinset.toList
  have hl : {v | v ∈ l} = X.T := by ext v; simp [l]
  let R : RootedGraph α β := {
    G := X.G
    τ := l
    τ_subset := fun v hv => X.T_subset (hl ▸ hv)
    finite_G := X.finite_G }
  have hR : R.toGraft = X := by
    cases X
    rw [Graft.mk.injEq]
    exact ⟨rfl, hl⟩
  have hn : R.τ.Nodup := Finset.nodup_toList _
  refine ⟨R, hR, hn, ?_⟩
  have heq := graft_index_eq_of_nodup R hn
  rw [hR] at heq
  exact heq.symm

/-- Forgetting the order in a rooted graph simulation with distinct
roots gives a graft simulation. This is the last step of the proof
of the disc case in VIII, Section 12, page 274. -/
theorem isGraftSimulatedIn_of_root_order {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {Y : RootedGraph α' β'} {X : RootedGraph α β}
    (hY : Y.τ.Nodup) (hX : X.τ.Nodup) (h : IsRootedGraphSimulatedIn Y X) :
    IsGraftSimulatedIn Y.toGraft X.toGraft := by
  obtain ⟨ηv, ηe, hg, hlen, hroot, _⟩ := h
  refine ⟨ηv, ηe, hg, ?_, ?_⟩
  · change X.toGraft.index = Y.toGraft.index
    rw [graft_index_eq_of_nodup X hX, graft_index_eq_of_nodup Y hY]
    exact hlen
  · intro u hu
    change u ∈ Y.τ at hu
    obtain ⟨i, hi, hu⟩ := List.mem_iff_getElem.mp hu
    have hiX : i < X.τ.length := hlen.symm ▸ hi
    refine ⟨X.τ[i], ?_, List.getElem_mem _⟩
    have hr := hroot ⟨i, hiX⟩
    change X.τ[i] ∈ ηv (Y.τ[i]) at hr
    rw [hu] at hr
    exact hr

end GraphMinor.GM08
