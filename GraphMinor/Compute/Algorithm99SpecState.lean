module

public import GraphMinor.Compute.Algorithm99Step8

/-!
# The first state of (9.9) when (10.5) calls it on `G_i \ Z_i`

Algorithm (10.5) of Graph Minors XIII (page 108) calls (9.9) on `G_i \ Z_i`, given as the
multigraph `D = G_i.deleteVertices Z_i` on `Fin m` (the vertices of `Z_i` stay, with no edges)
and the set `Z_i` (`Alg99Spec`). We run the loop of (9.9) on `D`, with the vertices outside
`Z_i` renumbered as `0, …, |Z_iᶜ| - 1` (`deleteVerticesCompact`). Then the map `orig` of every
state misses `Z_i`, which `isAlg99SpecIII_of_case3StepsOutputA` needs.

* `Alg99Iter.initCompact`: the first state, `G_1` the renumbered `G_i \ Z_i`, `orig` the
  renumbering, `Z_1 = ∅`, `H_1` the wall of step (1).
* `Alg99Iter.initCompact_isValid`: it is valid for `D`, since no edge of `D` meets `Z_i`.
* `Alg99Iter.step8_orig_not_mem`: step (8) keeps `orig` away from `Z_i`.
-/

@[expose] public section

namespace GraphMinor.Compute

variable {m : ℕ}

/-- The first state of the loop for `D = G_i \ Z_i`: "We set $G_1 = G$, $Z_1 = \emptyset$,
$H_1 = H$" (Graph Minors XIII, (9.9), step (2), page 104), with `G` the renumbered `D`. -/
def Alg99Iter.initCompact {h' : ℕ} (Gi : MultiDigraph m) (Zs : Finset (Fin m))
    (W : WallOfHeight h' ((Gi.deleteVertices Zs).deleteVerticesCompact Zs)) :
    Alg99Iter h' (Gi.deleteVertices Zs) where
  v := Zsᶜ.card
  Gi := (Gi.deleteVertices Zs).deleteVerticesCompact Zs
  orig := compactEmb Zs
  Z := ∅
  H := W

/-- The first state is valid for `D = G_i \ Z_i`. -/
theorem Alg99Iter.initCompact_isValid {h' : ℕ} (Gi : MultiDigraph m) (Zs : Finset (Fin m))
    {W : WallOfHeight h' ((Gi.deleteVertices Zs).deleteVerticesCompact Zs)} (hW : W.IsValid)
    (s : ℕ) : (Alg99Iter.initCompact Gi Zs W).IsValid s := by
  have hpre : ∀ y : Fin m, y ∉ Zs → ∃ w, compactEmb Zs w = y := fun y hy =>
    (mem_range_compactEmb_iff Zs y).mpr hy
  refine ⟨(compactEmb Zs).injective, fun u w => Or.inr ?_, by simp [Alg99Iter.initCompact], ?_,
    ?_, hW⟩
  · exact MultiDigraph.deleteVerticesCompact_edgeMult _ _ u w
  · intro u _ y hy
    have hyZ : y ∉ Zs := by
      intro hyZ
      change 0 < (Gi.deleteVertices Zs).edgeMult _ y at hy
      simp [MultiDigraph.deleteVertices_edgeMult, hyZ] at hy
    obtain ⟨w, rfl⟩ := hpre y hyZ
    exact ⟨w, rfl, MultiDigraph.deleteVerticesCompact_edgeMult _ _ u w⟩
  · intro u _ y hy
    have hyZ : y ∉ Zs := by
      intro hyZ
      change 0 < (Gi.deleteVertices Zs).edgeMult y _ at hy
      simp [MultiDigraph.deleteVertices_edgeMult, hyZ] at hy
    obtain ⟨w, rfl⟩ := hpre y hyZ
    exact ⟨w, rfl, MultiDigraph.deleteVerticesCompact_edgeMult _ _ w u⟩

/-- The renumbering misses `Z_i`. -/
theorem Alg99Iter.initCompact_orig_not_mem {h' : ℕ} (Gi : MultiDigraph m) (Zs : Finset (Fin m))
    (W : WallOfHeight h' ((Gi.deleteVertices Zs).deleteVerticesCompact Zs)) (u) :
    (Alg99Iter.initCompact Gi Zs W).orig u ∉ Zs :=
  compactEmb_not_mem Zs u

/-- Step (8) keeps the map `orig` away from a set that it missed before. -/
theorem Alg99Iter.step8_orig_not_mem {h' n : ℕ} {G : MultiDigraph n} {st : Alg99Iter h' G}
    {Zs : Finset (Fin n)} (hR : ∀ u, st.orig u ∉ Zs) (X V_A Bd : Finset (Fin st.v))
    {A_sub : MultiDigraph st.v} (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ))
    (u : Fin (st.step8 X V_A Bd W_A).v) : (st.step8 X V_A Bd W_A).orig u ∉ Zs :=
  hR _

end GraphMinor.Compute
