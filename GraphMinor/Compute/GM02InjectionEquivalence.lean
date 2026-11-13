module

public import GraphMinor.Compute.GM02InjectedPatternIso
public import GraphMinor.GM02.FixedVertexIso

/-!
# Trying every injection suffices for II (4.7)

An isomorphism to a topologically contained graph maps the fixed pattern
vertices injectively into the host. Place the pattern at these images.
The resulting labelled pattern differs from the contained graph only
in edge names. Conversely, any successful labelled test supplies an
isomorphic copy of the fixed pattern.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- The vertex map of a topologically contained copy is an injection into the host vertices. -/
@[expose] noncomputable def gm02ContainedVertexInjection (G H : GM02EdgeListInput)
    (L : Graph ℕ ℕ) (ht : TopologicallyContains G.graph L) (φ : Iso H.graph L) :
    Fin H.n ↪ Fin G.n where
  toFun i := ⟨(φ.vertexEquiv ⟨i.val, i.isLt⟩).val,
    ht.vertexSet_subset (φ.vertexEquiv ⟨i.val, i.isLt⟩).property⟩
  inj' i j hij := by
    have h := φ.vertexEquiv.injective (Subtype.ext (congrArg Fin.val hij))
    exact Fin.ext (congrArg Subtype.val h)

/-- The injection search is equivalent to existence of an isomorphic topologically contained copy. -/
theorem gm02_exists_injectedPattern_iff (G H : GM02EdgeListInput) :
    (∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso H.graph L)) ↔
      ∃ f : Fin H.n ↪ Fin G.n, TopologicallyContains G.graph (gm02InjectedPattern G H f).H := by
  constructor
  · rintro ⟨L, ht, ⟨φ⟩⟩
    let f := gm02ContainedVertexInjection G H L ht φ
    let ψ := gm02InjectedPatternIso G H f
    let σ : Iso (gm02InjectedPattern G H f).H L := {
      vertexEquiv := ψ.vertexEquiv.symm.trans φ.vertexEquiv
      edgeEquiv := ψ.edgeEquiv.symm.trans φ.edgeEquiv
      isLink_iff := by
        intro e a b
        have h := ψ.isLink_iff (ψ.edgeEquiv.symm e) (ψ.vertexEquiv.symm a) (ψ.vertexEquiv.symm b)
        simp only [Equiv.apply_symm_apply] at h
        exact h.symm.trans (φ.isLink_iff _ _ _) }
    refine ⟨f, ht.of_fixedVertexIso σ ?_⟩
    intro v
    let a := ψ.vertexEquiv.symm v
    have ha : ψ.vertexEquiv a = v := ψ.vertexEquiv.apply_symm_apply v
    have hv : (φ.vertexEquiv a).val = (ψ.vertexEquiv a).val := by
      rfl
    exact hv.trans (congrArg Subtype.val ha)
  · rintro ⟨f, ht⟩
    exact ⟨(gm02InjectedPattern G H f).H, ht, ⟨gm02InjectedPatternIso G H f⟩⟩

end GraphMinor.Compute
