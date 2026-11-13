module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15
import GraphMinor.GM07.Section8
import GraphMinor.GM07.Section11

/-!
# Extending a normal line to a boundary vertex

In Case 2 of VIII (16.2), an exceptional hoop may replace the moved hoop.
A normal line reaching that hoop can be extended to its first vertex on
the hoop. If all such vertices are on the old boundary, this adds at most
one vertex to the line. The length therefore drops by at most one.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- Extend a normal line along a normal circle to its first drawing
vertex. This adds at most one vertex. All circle vertices lie in the target
set, and the starting end lies outside that set. This is the extension
needed for the exceptional-hoop alternative in VIII (16.2), page 283. -/
theorem exists_normal_line_extension_to_circle_vertex {S : Type w}
    [TopologicalSpace S] (hS : IsSurface S) (Γ : Drawing S) {H A I : Set S} {u v : S}
    (hH : IsOArc H) (hNH : Γ.IsNormal H) (hHV : (H ∩ Γ.V).Nonempty)
    (hHA : H ∩ Γ.V ⊆ A) (hI : IsLineWithEnds I u v) (hNI : Γ.IsNormal I)
    (hv : v ∈ H) (hu : u ∉ A) :
    ∃ J : Set S, ∃ a : S, IsLineWithEnds J u a ∧ a ∈ A ∧ Γ.IsNormal J ∧
      (J ∩ Γ.V).ncard ≤ (I ∩ Γ.V).ncard + 1 := by
  have : T2Space S := hS.2.1
  by_cases hvV : v ∈ Γ.V
  · exact ⟨I, v, hI, hHA ⟨hv, hvV⟩, hNI, Nat.le_succ _⟩
  have hdis : Disjoint ({v} : Set S) (H ∩ Γ.V) := disjoint_left.mpr (by
    rintro x rfl hx
    exact hvV hx.2)
  obtain ⟨L, v', a, hLH, hv', ha, hL, _, hLa⟩ :=
    GM07.exists_connecting_line_between_disjoint_closed (GM07.IsOArc.isArcConnected hH)
      (singleton_subset_iff.mpr hv) inter_subset_left isClosed_singleton
      (Γ.finite_V.inter_of_right H).isClosed (singleton_nonempty v) hHV hdis
  have heq : v' = v := hv'
  subst v'
  have haA : a ∈ A := hHA ha
  have hLvertices : L ∩ Γ.V ⊆ {a} := by
    intro x hx
    exact hLa.subset ⟨hx.1, hLH hx.1, hx.2⟩
  have hNL : Γ.IsNormal L := fun x hx => hNH ⟨hLH hx.1, hx.2⟩
  have hsolid := GM07.theorem_11_6_proof hS (GM07.IsLineWithEnds.isSolid hI)
    (GM07.IsLineWithEnds.isSolid hL)
  have hconn : IsConnected (I ∪ L) := IsConnected.union ⟨v, hI.right_mem, hL.left_mem⟩
    (GM07.IsLineWithEnds.isConnected hI) (GM07.IsLineWithEnds.isConnected hL)
  have harc := GM07.theorem_11_4_proof hS hconn hsolid.1
  obtain ⟨J, hJsub, hJ⟩ := harc u (Or.inl hI.left_mem) a (Or.inr hL.right_mem)
    (fun he => hu (he.symm ▸ haA))
  have hcountSub : J ∩ Γ.V ⊆ (I ∩ Γ.V) ∪ {a} := by
    intro x hx
    rcases hJsub hx.1 with hxI | hxL
    · exact Or.inl ⟨hxI, hx.2⟩
    · exact Or.inr (hLvertices ⟨hxL, hx.2⟩)
  refine ⟨J, a, hJ, haA, ?_, ?_⟩
  · intro x hx
    rcases hJsub hx.1 with hxI | hxL
    · exact hNI ⟨hxI, hx.2⟩
    · exact hNL ⟨hxL, hx.2⟩
  · calc
      (J ∩ Γ.V).ncard ≤ ((I ∩ Γ.V) ∪ {a}).ncard :=
        ncard_le_ncard hcountSub ((Γ.finite_V.inter_of_right I).union (finite_singleton a))
      _ ≤ (I ∩ Γ.V).ncard + ({a} : Set S).ncard := ncard_union_le _ _
      _ = (I ∩ Γ.V).ncard + 1 := by rw [ncard_singleton]

/-- Replacing a boundary by an inner hoop whose drawing vertices lie on
that boundary loses at most one unit of length, provided the hoop has a
vertex and the original length is at least two. This is the length estimate
for the exceptional-hoop alternative in VIII (16.2), page 283. -/
theorem Tube.length_le_subTube_add_one_of_vertices_on_boundary {S : Type w}
    [TopologicalSpace S] (τ : Tube S) {H : Set S} (hH : IsHoop H)
    (hNH : τ.Γ.IsNormal H) (hsub : H ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hHV : (H ∩ τ.Γ.V).Nonempty) (hHA : H ∩ τ.Γ.V ⊆ τ.F₁)
    (hlen : 2 ≤ τ.length) :
    τ.length ≤ (τ.subTube
      (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).2 hNH τ.isNormal_F₂).length + 1 := by
  have : T2Space S := τ.t2Space
  let hlam := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).2
  let σ := τ.subTube hlam hNH τ.isNormal_F₂
  have hdis := τ.disjoint_of_two_le_length hlen
  have htest : τ.length - 1 ≤ σ.length := by
    apply σ.le_length_iff_sub_cylinderBetween.mpr
    intro I u v hI hu hv hNI hIsub
    have hNI' := (τ.subTube_isNormal_iff hlam hNH τ.isNormal_F₂ hIsub).mp hNI
    have hvA : v ∉ τ.F₁ := fun hv₁ => disjoint_left.mp hdis hv₁ hv
    obtain ⟨J, a, hJ, ha, hNJ, hcount⟩ := exists_normal_line_extension_to_circle_vertex
      τ.isCylinder.1 τ.Γ hH.1 hNH hHV hHA hI.symm hNI' hu hvA
    have hlenJ := (τ.le_length_iff.mp le_rfl) J a v hJ.symm ha hv hNJ
    have hV : σ.Γ.V = τ.Γ.V ∩ cylinderBetween H τ.F₂ :=
      interSet_V_of_isClosed τ.Γ (isClosed_cylinderBetween hlam)
    have hcard : I ∩ σ.Γ.V = I ∩ τ.Γ.V := by
      rw [hV]
      ext x
      exact ⟨fun ⟨hxI, hxV, _⟩ => ⟨hxI, hxV⟩,
        fun ⟨hxI, hxV⟩ => ⟨hxI, hxV, hIsub hxI⟩⟩
    rw [hcard]
    omega
  change τ.length ≤ σ.length + 1
  omega

end GraphMinor.GM08
