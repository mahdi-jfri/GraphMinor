module

public import GraphMinor.GM03.Defs
import GraphMinor.GM03.Section4a
import GraphMinor.GM03.Section4b
import GraphMinor.GM03.Section4c
import GraphMinor.GM03.Section4d
import GraphMinor.GM09.PlanarNests
import GraphMinor.GM16.LineDrawingPath

/-!
# Graph Minors III, Section 4: Cylinder Minor from `MajorsCylinder`

This file proves `isIsoMinor_cylinderGraph_of_majorsCylinder`, the cylinder minor step in the proof
of Graph Minors III, (4.5) (page 62): if a plane drawing $M$ of $G$ majors the $r \times s$
cylinder, then $G$ has a minor isomorphic to `cylinderGraph r s`.
-/

public section

namespace GraphMinor.GM03

open Set Function Relation Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

private theorem mem_tail_of_isSimple' {H : Graph α β} {p q z : α}
    (U : GraphWalk H p q) (hUs : U.IsSimple) (hz : z ∈ U.support.tail) :
    z ∈ U.support ∧ z ≠ p := by
  have hcons := U.support_eq_cons
  have hnd : (p :: U.support.tail).Nodup := hcons ▸ hUs
  refine ⟨by rw [hcons]; exact List.mem_cons_of_mem _ hz, ?_⟩
  rintro rfl
  exact (List.nodup_cons.mp hnd).1 hz

/-- Cylinder-minor construction in the proof of **Graph Minors III, (4.5)** (page 62):
"Take a drawing $M$ of $G$. If $M$ majors the $r \times s$ cylinder then $G$ has a minor isomorphic
to the $r \times s$ cylinder." -/
theorem isIsoMinor_cylinderGraph_of_majorsCylinder {G : Graph α β} (M : PlanarDrawing G)
    {r s : ℕ} (hMaj : MajorsCylinder M r s) :
    IsIsoMinor (cylinderGraph r s) G := by
  obtain ⟨hs, C, P, hC, hP_disj, hP_path, hP_inter⟩ := hMaj
  by_cases hr : 0 < r
  · let dat := buildOrderedNestedCylinderData M r s hr hs C P hC hP_disj hP_path hP_inter
    obtain ⟨hK_le, hK_conn, hK_disj, he_not_K, he_inj, he_link⟩ :=
      dat.circlePieces_of_emb hC id Function.injective_id (fun j => (hC.1 j).1)
    let u_rad : Fin r → Fin (s - 1) → α := fun k m => dat.y (dat.σ k) ⟨m.1, by omega⟩
    let w_rad : Fin r → Fin (s - 1) → α := fun k m => dat.x (dat.σ k) ⟨m.1 + 1, by omega⟩
    let j_last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
    let u_tail : Fin r → α := fun k => dat.y (dat.σ k) j_last
    have hu_tail_G : ∀ k : Fin r, u_tail k ∈ V(G) :=
      fun k => (hC.1 j_last).1.vertexSet_mono (dat.mem_mid_V_ends (dat.σ k) j_last).2.2
    let R_tail : ∀ k : Fin r, GraphWalk G (u_tail k) (u_tail k) :=
      fun k => GraphWalk.nil (hu_tail_G k)
    have hR_tail_simple : ∀ k : Fin r, (R_tail k).IsSimple :=
      fun _ => List.nodup_singleton _
    have hu_rad_mem : ∀ (k : Fin r) (m : Fin (s - 1)),
        u_rad k m ∈ V(dat.K_circ k ⟨m.1, by omega⟩) :=
      fun k m => dat.inter_sub_K_circ k ⟨m.1, by omega⟩
        (dat.mem_mid_V_ends (dat.σ k) ⟨m.1, by omega⟩).2
    have hw_rad_mem : ∀ (k : Fin r) (m : Fin (s - 1)),
        w_rad k m ∈ V(dat.K_circ k ⟨m.1 + 1, by omega⟩) :=
      fun k m => dat.inter_sub_K_circ k ⟨m.1 + 1, by omega⟩
        (dat.mem_mid_V_ends (dat.σ k) ⟨m.1 + 1, by omega⟩).1
    have hu_tail_mem : ∀ k : Fin r, u_tail k ∈ V(dat.K_circ k j_last) :=
      fun k => dat.inter_sub_K_circ k j_last (dat.mem_mid_V_ends (dat.σ k) j_last).2
    have hK_sub_C : ∀ (k' : Fin r) (j' : Fin s), V(dat.K_circ k' j') ⊆ V(C j') :=
      fun k' j' => ((dat.K_circ_le k' j').trans deleteEdges_le).vertexSet_mono
    obtain ⟨G', hG'_le, C_contr, hC_sub, φ, _, _⟩ :=
      exists_cylinder_contract_of_circle_pieces r s hs dat.K_circ dat.e_circ
        hK_le hK_conn (fun h => hK_disj h) he_not_K (fun h => he_inj h) he_link
        u_rad w_rad (fun k m => dat.R_adj (dat.σ k) m)
        (fun k m => dat.R_adj_simple (dat.σ k) m)
        hu_rad_mem hw_rad_mem
        (fun k m k' j' z hzR hzK => by
          rcases dat.R_adj_inter_C hC (dat.σ k) m j' hzR (hK_sub_C k' j' hzK) with
            ⟨rfl, hzy⟩ | ⟨rfl, hzx⟩
          · have hzu : z = u_rad k m := hzy
            have hk' : k' = k := by
              by_contra hne
              exact disjoint_left.mp (hK_disj (fun h => hne (congrArg Prod.fst h)))
                hzK (hzu ▸ hu_rad_mem k m)
            exact Or.inl ⟨hk', rfl, hzu⟩
          · have hzw : z = w_rad k m := hzx
            have hk' : k' = k := by
              by_contra hne
              exact disjoint_left.mp (hK_disj (fun h => hne (congrArg Prod.fst h)))
                hzK (hzw ▸ hw_rad_mem k m)
            exact Or.inr ⟨hk', rfl, hzw⟩)
        (fun {k₁ k₂ m₁ m₂} hne => by
          refine disjoint_left.mpr fun z hz₁ hz₂ => ?_
          obtain ⟨hz₁_s, hz₁_ne⟩ := mem_tail_of_isSimple' _ (dat.R_adj_simple _ m₁) hz₁
          obtain ⟨hz₂_s, hz₂_ne⟩ := mem_tail_of_isSimple' _ (dat.R_adj_simple _ m₂) hz₂
          by_cases hk : k₁ = k₂
          · subst hk
            have hm_ne : m₁.1 ≠ m₂.1 := fun h => hne (Prod.ext rfl (Fin.ext h))
            rcases lt_trichotomy m₁.1 m₂.1 with hlt | heq | hgt
            · obtain ⟨_, _, hzy⟩ := dat.R_adj_inter hC (dat.σ k₁)
                (Fin.mk_lt_mk.mpr hlt) hz₁_s hz₂_s
              exact hz₂_ne hzy
            · exact hm_ne heq
            · obtain ⟨_, _, hzy⟩ := dat.R_adj_inter hC (dat.σ k₁)
                (Fin.mk_lt_mk.mpr hgt) hz₂_s hz₁_s
              exact hz₁_ne hzy
          · have hzP₁ : z ∈ V(P (dat.σ k₁)) := by
              rw [dat.P_V, mem_ofPred_eq, dat.W_split _ ⟨m₁.1, by omega⟩,
                dat.R_adj_spec _ m₁, GraphWalk.mem_support_append,
                GraphWalk.mem_support_append, GraphWalk.mem_support_append]
              exact Or.inr (Or.inr (Or.inl hz₁_s))
            have hzP₂ : z ∈ V(P (dat.σ k₂)) := by
              rw [dat.P_V, mem_ofPred_eq, dat.W_split _ ⟨m₂.1, by omega⟩,
                dat.R_adj_spec _ m₂, GraphWalk.mem_support_append,
                GraphWalk.mem_support_append, GraphWalk.mem_support_append]
              exact Or.inr (Or.inr (Or.inl hz₂_s))
            exact disjoint_left.mp (hP_disj (dat.σ.injective.ne hk)) hzP₁ hzP₂)
        u_tail u_tail R_tail hR_tail_simple hu_tail_mem
        (fun k k' j' z hzT hzK => by
          have hzu : z = u_tail k := List.mem_singleton.mp hzT
          have hpair : (k', j') = (k, j_last) := by
            by_contra hne
            exact disjoint_left.mp (hK_disj hne) hzK (hzu ▸ hu_tail_mem k)
          exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair, hzu⟩)
        (fun {k₁ k₂} hne => by
          refine disjoint_left.mpr fun z hz₁ hz₂ => ?_
          change z ∈ [u_tail k₁] at hz₁
          change z ∈ [u_tail k₂] at hz₂
          rw [List.mem_singleton] at hz₁ hz₂
          exact disjoint_left.mp (hK_disj (fun h => hne (congrArg Prod.fst h)))
            (hz₁ ▸ hu_tail_mem k₁) (hz₂ ▸ hu_tail_mem k₂))
        (fun k₁ k₂ m z hzT hzR_tail => by
          obtain ⟨hzR, _⟩ := mem_tail_of_isSimple' _ (dat.R_adj_simple _ m) hzR_tail
          have hzu : z = u_tail k₁ := List.mem_singleton.mp hzT
          have hk_eq : k₁ = k₂ := by
            by_contra hne
            have hzP₁ : z ∈ V(P (dat.σ k₁)) :=
              hzu ▸ (dat.mem_mid_V_ends (dat.σ k₁) j_last).2.1
            have hzP₂ : z ∈ V(P (dat.σ k₂)) := by
              rw [dat.P_V, mem_ofPred_eq, dat.W_split _ ⟨m.1, by omega⟩,
                dat.R_adj_spec _ m, GraphWalk.mem_support_append,
                GraphWalk.mem_support_append, GraphWalk.mem_support_append]
              exact Or.inr (Or.inr (Or.inl hzR))
            exact disjoint_left.mp (hP_disj (dat.σ.injective.ne hne)) hzP₁ hzP₂
          subst hk_eq
          have hzC : z ∈ V(C j_last) :=
            hzu ▸ (dat.mem_mid_V_ends (dat.σ k₁) j_last).2.2
          rcases dat.R_adj_inter_C hC (dat.σ k₁) m j_last hzR hzC with
            ⟨hj_eq, _⟩ | ⟨hj_eq, hzx⟩
          · exfalso
            have hval : s - 1 = m.1 := congrArg Fin.val hj_eq
            have hm_lt : m.1 < s - 1 := m.2
            omega
          · have hm_eq : s - 1 = m.1 + 1 := congrArg (fun x : Fin s => x.1) hj_eq
            exact ⟨rfl, hm_eq.symm, hzx⟩)
    exact ⟨G', hG'_le, C_contr, hC_sub, ⟨φ⟩⟩
  · have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    subst hr0
    let G' : Graph α β := G.induce ∅
    have hG'_le : G' ≤ G := G.induce_le (empty_subset _)
    have hVG' : V(G') = ∅ := by simp [G']
    have hEG' : E(G') = ∅ := by
      refine eq_empty_of_forall_notMem fun e he => ?_
      obtain ⟨x, _, hl⟩ := G'.exists_isLink_of_mem_edgeSet he
      have hx := hl.left_mem
      rw [hVG'] at hx; exact hx
    have hVc : V(cylinderGraph 0 s) = ∅ :=
      eq_empty_of_forall_notMem fun p _ => Fin.elim0 p.1
    have hEc : E(cylinderGraph 0 s) = ∅ := by
      refine eq_empty_of_forall_notMem fun e _ => ?_
      rcases e with p | p <;> exact Fin.elim0 p.1
    have hVcG : V(contract G' (∅ : Set β)) = ∅ := by
      refine eq_empty_of_forall_notMem fun _ ⟨x, hx, _⟩ => ?_
      rw [hVG'] at hx; exact hx
    have hEcG : E(contract G' (∅ : Set β)) = ∅ := by
      refine eq_empty_of_forall_notMem fun e he => ?_
      obtain ⟨_, _, hl⟩ := (contract G' (∅ : Set β)).exists_isLink_of_mem_edgeSet he
      obtain ⟨⟨x, _, hlx, _, _⟩, _⟩ := hl
      have hx := hlx.left_mem
      rw [hVG'] at hx; exact hx
    obtain ⟨φ⟩ := isoOfEmpty (cylinderGraph 0 s) (contract G' (∅ : Set β)) hVc hEc hVcG hEcG
    exact ⟨G', hG'_le, ∅, empty_subset _, ⟨φ⟩⟩

end GraphMinor.GM03
end
