module

public import GraphMinor.GM01.PathWidth
import GraphMinor.Minor.Basic

/-!
# Restricting and relabelling path-decompositions

The proof of Graph Minors I, (1.1), applies path-width bounds to induced
pieces and switches between a graph and its graph on the vertex type.
Intersecting bags with a subgraph's vertices restricts a decomposition.
A graph isomorphism transports each bag along its vertex bijection and
preserves its size and interval condition.
-/

public section

namespace GraphMinor.GM01

open Graph

variable {α β γ δ : Type*}

/-- Restrict a decomposition by intersecting each bag with the subgraph's
vertex set. -/
theorem HasPathWidthLE.of_le {G H : Graph α β} {k : ℕ}
    (hG : HasPathWidthLE G k) (hle : H ≤ G) : HasPathWidthLE H k := by
  obtain ⟨D, hD⟩ := hG
  refine ⟨⟨D.length, fun i ↦ D.bag i ∩ V(H), fun _ _ hx ↦ hx.2, ?_, ?_⟩, ?_⟩
  · intro e x y he
    obtain ⟨i, hx, hy⟩ := D.edge_covered e x y (he.mono hle)
    exact ⟨i, ⟨hx, he.left_mem⟩, ⟨hy, he.right_mem⟩⟩
  · intro i j l hij hjl x hx
    exact ⟨D.interval i j l hij hjl ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
  · intro i
    exact ⟨(hD i).1.subset Set.inter_subset_left,
      (Set.ncard_le_ncard Set.inter_subset_left (hD i).1).trans (hD i).2⟩

/-- Transport every bag along the vertex bijection of an isomorphism. -/
theorem HasPathWidthLE.map_iso {H : Graph α β} {G : Graph γ δ} {k : ℕ}
    (hH : HasPathWidthLE H k) (e : GraphMinor.Iso H G) : HasPathWidthLE G k := by
  obtain ⟨D, hD⟩ := hH
  let f : V(H) → γ := fun x ↦ (e.vertexEquiv x).val
  have hf : Function.Injective f := fun x y h ↦ e.vertexEquiv.injective (Subtype.ext h)
  let bag (i : Fin D.length) := f '' (Subtype.val ⁻¹' D.bag i)
  refine ⟨⟨D.length, bag, ?_, ?_, ?_⟩, ?_⟩
  · rintro i x ⟨a, ha, rfl⟩
    exact (e.vertexEquiv a).property
  · intro edge x y hxy
    let edge' : E(H) := e.edgeEquiv.symm ⟨edge, hxy.edge_mem⟩
    let x' : V(H) := e.vertexEquiv.symm ⟨x, hxy.left_mem⟩
    let y' : V(H) := e.vertexEquiv.symm ⟨y, hxy.right_mem⟩
    have hsource : H.IsLink edge' x' y' := by
      apply (e.isLink_iff edge' x' y').mpr
      simpa only [edge', x', y', Equiv.apply_symm_apply] using hxy
    obtain ⟨i, hx, hy⟩ := D.edge_covered edge' x' y' hsource
    refine ⟨i, ⟨x', hx, ?_⟩, ⟨y', hy, ?_⟩⟩
    · exact congrArg Subtype.val (e.vertexEquiv.apply_symm_apply ⟨x, hxy.left_mem⟩)
    · exact congrArg Subtype.val (e.vertexEquiv.apply_symm_apply ⟨y, hxy.right_mem⟩)
  · intro i j l hij hjl x hx
    obtain ⟨a, ha, hfa⟩ := hx.1
    obtain ⟨b, hb, hfb⟩ := hx.2
    have hab : a = b := hf (hfa.trans hfb.symm)
    subst b
    exact ⟨a, D.interval i j l hij hjl ⟨ha, hb⟩, hfa⟩
  · intro i
    have hp : (Subtype.val ⁻¹' D.bag i : Set V(H)).Finite :=
      Set.Finite.preimage Subtype.val_injective.injOn (hD i).1
    have hsubset : D.bag i ⊆ Set.range (Subtype.val : V(H) → α) := by
      intro x hx
      exact ⟨⟨x, D.bag_subset i hx⟩, rfl⟩
    refine ⟨hp.image f, ?_⟩
    change (f '' (Subtype.val ⁻¹' D.bag i)).ncard ≤ k + 1
    calc
      _ ≤ (Subtype.val ⁻¹' D.bag i : Set V(H)).ncard := Set.ncard_image_le hp
      _ = (D.bag i).ncard :=
        Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsubset
      _ ≤ k + 1 := (hD i).2

/-- Isomorphic graphs have the same path-width bounds. -/
theorem hasPathWidthLE_iso_iff {H : Graph α β} {G : Graph γ δ}
    (e : GraphMinor.Iso H G) (k : ℕ) : HasPathWidthLE H k ↔ HasPathWidthLE G k :=
  ⟨fun h ↦ h.map_iso e, fun h ↦ h.map_iso e.symm⟩

end GraphMinor.GM01
