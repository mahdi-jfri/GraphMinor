module

public import GraphMinor.Compute.GM06Alg34Input
public import GraphMinor.GM06.Section3Reduction
import GraphMinor.GM06.Alg34Boundary
import GraphMinor.GM06.Alg34CuffOrder

/-!
# Every proper disc instance has finite input data

Choose finite labels for the vertices, edges, and regions. The endpoint
lists come from the drawing's edges. Each region has finite boundary
incidence lists, and an angularly sorted list describes the single cuff.
Division blocks are written using the same vertex labels.

These are existence theorems in Prop. They do not define an encoder from
geometric instances. The executable serializer continues to read only
finite data supplied as its argument.
-/

public section
namespace GraphMinor.GM06

open Set Surface GM11 Compute

universe u
variable {S : Type u} [TopologicalSpace S]

private theorem alg34_exists_division_lists {G : Drawing S} {n : ℕ}
    (v : Fin n ≃ G.V) {Δ : Set (Set S)} (hΔ : IsDivision Δ)
    (hsub : divisionUnion Δ ⊆ G.V) :
    ∃ D : List (List (Fin n)), Δ =
      (fun L => (fun i => (v i).val) '' GM06DrawingData.block L) '' {L | L ∈ D} := by
  classical
  let labels : Set S → List (Fin n) := fun δ =>
    (Finset.univ.filter (fun i => (v i).val ∈ δ)).toList
  have hlabels : ∀ δ ∈ Δ,
      (fun i => (v i).val) '' GM06DrawingData.block (labels δ) = δ := by
    intro δ hδ
    ext p
    constructor
    · rintro ⟨i, hi, rfl⟩
      simpa only [labels, GM06DrawingData.block, mem_ofPred_eq,
        Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    · intro hp
      obtain ⟨i, hi⟩ := v.surjective ⟨p, hsub ⟨δ, hδ, hp⟩⟩
      have hi' := congrArg Subtype.val hi
      refine ⟨i, ?_, hi'⟩
      simpa only [labels, GM06DrawingData.block, mem_ofPred_eq,
        Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, hi'] using hp
  refine ⟨hΔ.1.toFinset.toList.map labels, ?_⟩
  ext δ
  constructor
  · intro hδ
    refine ⟨labels δ, ?_, hlabels δ hδ⟩
    exact List.mem_map.mpr ⟨δ, by simpa only [Finset.mem_toList, hΔ.1.mem_toFinset] using hδ, rfl⟩
  · rintro ⟨L, hL, rfl⟩
    obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hL
    have hδ' : δ ∈ Δ := by simpa only [Finset.mem_toList, hΔ.1.mem_toFinset] using hδ
    dsimp only
    rw [hlabels δ hδ']
    exact hδ'

/-- Every proper disc drawing and division of its vertices has finite
representation data for VI (3.4). Bijections and boundary interpretations
are witnesses of representation, never fields of the supplied word array. -/
theorem alg34_exists_drawing_rep (hS : IsClosedDiscSpace S) (G : Drawing S)
    (hG : G.IsProper) (Δ : Set (Set S)) (hΔ : IsDivision Δ)
    (hsub : divisionUnion Δ ⊆ G.V) :
    ∃ x : GM06DrawingData, Nonempty (GM06DrawingRep x G Δ) := by
  classical
  let : Fintype G.V := G.finite_V.fintype
  let : Fintype G.E := G.finite_edges.fintype
  let : Fintype G.R := (disc_finite_R hS G hG).fintype
  let n := Fintype.card G.V
  let m := Fintype.card G.E
  let r := Fintype.card G.R
  let v : Fin n ≃ G.V := (Fintype.equivFin G.V).symm
  let e₀ : Fin m ≃ G.E := (Fintype.equivFin G.E).symm
  let r₀ : Fin r ≃ G.R := (Fintype.equivFin G.R).symm
  have hend : ∀ i : Fin m, ∃ a b : Fin n,
      closure (e₀ i).val ∩ G.V = {(v a).val, (v b).val} := by
    intro i
    obtain ⟨a, b, hl⟩ := G.toGraph.exists_isLink_of_mem_edgeSet (e₀ i).property
    obtain ⟨j, hj⟩ := v.surjective ⟨a, hl.left_mem⟩
    obtain ⟨k, hk⟩ := v.surjective ⟨b, hl.right_mem⟩
    refine ⟨j, k, ?_⟩
    rw [congrArg Subtype.val hj, congrArg Subtype.val hk]
    exact hl.2.2.2
  choose a b hab using hend
  let ends := List.ofFn (fun i : Fin m => (a i, b i))
  have hlen : ends.length = m := List.length_ofFn
  let e : Fin ends.length ≃ G.E := (finCongr hlen).trans e₀
  have he : ∀ i : Fin ends.length,
      closure (e i).val ∩ G.V = {(v ends[i].1).val, (v ends[i].2).val} := by
    intro i
    change closure (e i).val ∩ G.V = {(v (ends.get i).1).val, (v (ends.get i).2).val}
    have hi : Fin.cast hlen i = finCongr hlen i := Fin.ext (finCongr_apply_coe hlen i).symm
    simpa only [e, Equiv.trans_apply, ends, List.get_ofFn, hi] using hab (finCongr hlen i)
  have hbd : ∀ i : Fin r, ∃ bd : GM06RegionBoundary n ends.length,
      closure (r₀ i).val \ (r₀ i).val =
        {p | ∃ j ∈ bd.vertices, (v j).val = p} ∪ ⋃ j ∈ bd.edges, (e j).val := by
    intro i
    exact alg34_exists_region_boundary hS hG v e (r₀ i).property
  choose bd hbd using hbd
  let regions := List.ofFn bd
  have hrlen : regions.length = r := List.length_ofFn
  let re : Fin regions.length ≃ G.R := (finCongr hrlen).trans r₀
  have hre : ∀ i : Fin regions.length,
      closure (re i).val \ (re i).val =
        {p | ∃ j ∈ regions[i].vertices, (v j).val = p} ∪
          ⋃ j ∈ regions[i].edges, (e j).val := by
    intro i
    change closure (re i).val \ (re i).val =
      {p | ∃ j ∈ (regions.get i).vertices, (v j).val = p} ∪
        ⋃ j ∈ (regions.get i).edges, (e j).val
    have hi : Fin.cast hrlen i = finCongr hrlen i := Fin.ext (finCongr_apply_coe hrlen i).symm
    simpa only [re, Equiv.trans_apply, regions, List.get_ofFn, hi] using hbd (finCongr hrlen i)
  let ve : Fin n ↪ S := ⟨fun i => (v i).val, Subtype.val_injective.comp v.injective⟩
  obtain ⟨L, hnd, hmem, hord⟩ := alg34_exists_cuff_order hS.isOArc_bd ve
  have hconn : IsConnected (Surface.bd S) := isConnected_of_isOArc hS.isOArc_bd
  have hcs : Surface.cuffs S = {Surface.bd S} := by
    ext C
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hconn.2.connectedComponentIn hp
    · rintro rfl
      obtain ⟨p, hp⟩ := hconn.1
      exact ⟨p, hp, hconn.2.connectedComponentIn hp⟩
  have hc : Surface.bd S ∈ Surface.cuffs S := hcs.symm ▸ mem_singleton _
  have hc_eq : ∀ C : Surface.cuffs S, C.val = Surface.bd S := by
    intro C
    exact mem_singleton_iff.mp (hcs ▸ C.property)
  let ce : Fin 1 ≃ Surface.cuffs S := Equiv.ofBijective (fun _ => ⟨Surface.bd S, hc⟩)
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun C => ⟨0, Subtype.ext (hc_eq C).symm⟩⟩
  obtain ⟨D, hD⟩ := alg34_exists_division_lists v hΔ hsub
  let x : GM06DrawingData := ⟨n, ends, regions, [L], D⟩
  refine ⟨x, ⟨{
    vertex := v
    edge := e
    region := re
    ends := he
    boundary := hre
    cuff := ce
    cuff_vertices := ?_
    cuff_nodup := ?_
    order := ?_
    division := hD }⟩⟩
  · intro i
    have hi0 : i.val = 0 := by
      have hip := i.isLt
      change i.val < 1 at hip
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hip)
    have hi : i = 0 := Fin.ext hi0
    subst i
    rw [hc_eq (ce 0)]
    change (fun j => (v j).val) '' GM06DrawingData.block L = G.V ∩ Surface.bd S
    ext p
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(v j).property, (hmem j).mp hj⟩
    · rintro ⟨hpV, hpbd⟩
      obtain ⟨j, hj⟩ := v.surjective ⟨p, hpV⟩
      have hj' := congrArg Subtype.val hj
      refine ⟨j, (hmem j).mpr ?_, hj'⟩
      simpa only [ve, Function.Embedding.coeFn_mk, hj'] using hpbd
  · intro K hK
    have hKL : K = L := List.mem_singleton.mp hK
    exact hKL ▸ hnd
  · intro a c b d
    simpa only [GM06DrawingData.crosses, x, List.any_cons, List.any_nil, Bool.or_false,
      hcs, mem_singleton_iff, exists_eq_left, ve, Function.Embedding.coeFn_mk] using hord a c b d

/-- In particular, every disc instance of VI, Section 3, page 120, has a
representation by supplied finite data. This closes the coverage of the
input relation without adding a way to compute data from a proof. -/
theorem DiscDivInstance.exists_drawing_rep (I : DiscDivInstance.{u}) :
    ∃ x : GM06DrawingData, Nonempty (GM06DrawingRep x I.G I.Δ) :=
  alg34_exists_drawing_rep I.hDisc I.G I.hProper I.Δ I.hΔ
    (I.hΔ_eq.subset.trans inter_subset_left)

end GraphMinor.GM06
