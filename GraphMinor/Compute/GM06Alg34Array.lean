module

public import GraphMinor.Compute.GM06Alg34Words
public import GraphMinor.Compute.GM06Alg34Graph
public import GraphMinor.GM06.Alg34InputExists

/-!
# Feasibility from the supplied word array

The serializer is injective, and the endpoint and division data determine
feasibility. Combining these facts shows that one array cannot describe
two instances with different answers. The representation witnesses are
used only to interpret the supplied array.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set Surface GM06

universe u v

namespace GM06DrawingRep

/-- Equal supplied arrays give the same feasibility answer. The only
assumptions are representations of the two drawings and that their
supplied blocks are divisions, as in VI, Section 1, page 116. -/
theorem feasible_iff_of_same_words {x y : GM06DrawingData} {S T : Type*}
    [TopologicalSpace S] [TopologicalSpace T] {G : Drawing S} {H : Drawing T}
    {Δ : Set (Set S)} {Ε : Set (Set T)}
    (hG : GM06DrawingRep x G Δ) (hH : GM06DrawingRep y H Ε)
    (hw : x.words = y.words) (hΔ : IsDivision Δ) (hΕ : IsDivision Ε) :
    IsFeasible G.toGraph Δ ↔ IsFeasible H.toGraph Ε := by
  have hxy := GM06DrawingData.words_injective hw
  subst y
  exact hG.feasible_iff_of_same_data hH hΔ hΕ

end GM06DrawingRep

/-- The supplied array describes the drawing and division through finite
labels and the representation bijections. This relation contains no
feasibility answer, realization, or sequence of reductions. -/
def GM06RepresentsArray (w : List ℕ) {S : Type*} [TopologicalSpace S]
    (G : Drawing S) (Δ : Set (Set S)) : Prop :=
  ∃ x : GM06DrawingData, x.words = w ∧ Nonempty (GM06DrawingRep x G Δ)

/-- An array determines feasibility for every instance it represents.
The represented surfaces need not have the same ambient type. -/
theorem GM06RepresentsArray.feasible_iff {w : List ℕ} {S T : Type*}
    [TopologicalSpace S] [TopologicalSpace T] {G : Drawing S} {H : Drawing T}
    {Δ : Set (Set S)} {Ε : Set (Set T)}
    (hG : GM06RepresentsArray w G Δ) (hH : GM06RepresentsArray w H Ε)
    (hΔ : IsDivision Δ) (hΕ : IsDivision Ε) :
    IsFeasible G.toGraph Δ ↔ IsFeasible H.toGraph Ε := by
  obtain ⟨x, hx, ⟨hG⟩⟩ := hG
  obtain ⟨y, hy, ⟨hH⟩⟩ := hH
  exact hG.feasible_iff_of_same_words hH (hx.trans hy.symm) hΔ hΕ

/-- Every intended disc instance is represented by some supplied word
array. This theorem asserts coverage of the input relation in Prop and
does not provide an executable encoder from a geometric instance. -/
theorem GM06RepresentsArray.exists_of_disc_instance (I : DiscDivInstance.{u}) :
    ∃ w : List ℕ, GM06RepresentsArray w I.G I.Δ := by
  obtain ⟨x, hx⟩ := I.exists_drawing_rep
  exact ⟨x.words, x, rfl, hx⟩

/-- All disc instances represented by one supplied array have the same
feasibility answer. Their division hypotheses are part of the paper's
instance conditions. -/
theorem GM06RepresentsArray.disc_feasible_iff {w : List ℕ}
    {I : DiscDivInstance.{u}} {J : DiscDivInstance.{v}}
    (hI : GM06RepresentsArray w I.G I.Δ) (hJ : GM06RepresentsArray w J.G J.Δ) :
    I.IsFeasibleInst ↔ J.IsFeasibleInst :=
  hI.feasible_iff hJ I.hΔ J.hΔ

end GraphMinor.Compute
