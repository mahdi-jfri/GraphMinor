module

public import GraphMinor.GM05.CopyStarDrawings
public import GraphMinor.GM05.DrawingBranchModel
import GraphMinor.GM05.AttachMiddleLines
import GraphMinor.GM11.Walks
import GraphMinor.Surface.SurfaceGraph

/-!
# Models in the union of stars and edge middles

For GM V, (8.14), planarize all stars, then attach their disjoint
edge middles as single edges. Each original vertex is represented
by its connected star subdrawing. The representing edges are the
middle edges. Their endpoints belong to the appropriate branches,
and the star drawing has none of these edges. This proves a model
for every copy, with each branch confined to its chosen star support.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- The finite host construction from the actual star and middle-line
configuration of GM V, (8.14), page 113. Each resulting model has its
vertex branches inside its own local star supports. -/
theorem exists_models_of_star_system {S : Type} [TopologicalSpace S] [T2Space S]
    (D : Drawing S) (m : ℕ) (R : S → Set S)
    (hR : ∀ w ∈ D.V, ∀ z ∈ D.V, w ≠ z → Disjoint (R w) (R z))
    (u v : D.E → S) (hsrc : ∀ e, D.toGraph.IsLink e.val (u e) (v e))
    (hne : ∀ e, u e ≠ v e) (p q : Fin m × D.E → S) (M : Fin m × D.E → Set S)
    (hM : ∀ a, IsLineWithEnds (M a) (p a) (q a))
    (hMu : ∀ a, M a ∩ R (u a.2) = {p a}) (hMv : ∀ a, M a ∩ R (v a.2) = {q a})
    (haway : ∀ a w, w ∈ D.V → w ≠ u a.2 → w ≠ v a.2 → Disjoint (M a) (R w))
    (hMdis : Pairwise (fun a b ↦ Disjoint (M a) (M b)))
    (x : D.V → Fin m → S) (L : ∀ w : D.V, Fin m × IncidentEdge D w → Set S)
    (hx : ∀ w i, x w i ∈ R w.val) (hxne : ∀ w i j, i ≠ j → x w i ≠ x w j)
    (hL : ∀ w a, IsLineWithEnds (L w a) (x w a.1) (vertexPort D u p q w a))
    (hLR : ∀ w a, L w a ⊆ R w.val)
    (hfin : ∀ w a b, a ≠ b → (L w a ∩ L w b).Finite) :
    ∃ H : Drawing S, ∃ ηv : Fin m → S → Set S, ∃ ηe : Fin m → Set S → Set S,
      (∀ i, IsMinorModel D.toGraph H.toGraph (ηv i) (ηe i)) ∧
      ∀ i w (hw : w ∈ D.V), ηv i w ⊆ starSupport (x ⟨w,hw⟩) (L ⟨w,hw⟩) i := by
  classical
  let : Fintype D.E := D.finite_edges.fintype
  obtain ⟨T,K,hTU,hK,hports⟩ := exists_copy_star_drawings D m R hR u p q x L hx hxne hL hLR hfin
  have hstarR : ∀ w i, starSupport (x w) (L w) i ⊆ R w.val := fun w i ↦
    starSupport_subset (x w) (L w) i (hx w i) (fun e ↦ hLR w (i,e))
  have hKVR : ∀ i w, (K (i,w)).V ⊆ R w.val := fun i w ↦
    (K (i,w)).V_subset_U.trans ((hK i w).2.1.subset.trans (hstarR w i))
  have hpK : ∀ i e, p (i,e) ∈ (K (i,⟨u e,(hsrc e).left_mem⟩)).V := by
    intro i e
    have hh := hports ⟨u e,(hsrc e).left_mem⟩ (i,⟨e,(hsrc e).inc_left⟩)
    rw [vertexPort_at_left D u v p q hsrc i e] at hh
    exact hh
  have hqK : ∀ i e, q (i,e) ∈ (K (i,⟨v e,(hsrc e).right_mem⟩)).V := by
    intro i e
    have hh := hports ⟨v e,(hsrc e).right_mem⟩ (i,⟨e,(hsrc e).inc_right⟩)
    rw [vertexPort_at_right D u v p q hsrc hne i e] at hh
    exact hh
  have hpT : ∀ a, p a ∈ T.V := fun a ↦ (hK a.1 ⟨u a.2,(hsrc a.2).left_mem⟩).1.1 (hpK a.1 a.2)
  have hqT : ∀ a, q a ∈ T.V := fun a ↦ (hK a.1 ⟨v a.2,(hsrc a.2).right_mem⟩).1.1 (hqK a.1 a.2)
  have hMT : ∀ a, M a ∩ T.U = {p a,q a} := by
    intro a
    apply subset_antisymm
    · rintro z ⟨hzM,hzT⟩
      rw [hTU] at hzT
      obtain ⟨w,i,hzi⟩ := mem_iUnion₂.mp hzT
      have hzR := hstarR w i hzi
      by_cases hwu : w.val = u a.2
      · exact Or.inl ((hMu a ▸ ⟨hzM,hwu ▸ hzR⟩ : z ∈ ({p a} : Set S)))
      · by_cases hwv : w.val = v a.2
        · exact Or.inr ((hMv a ▸ ⟨hzM,hwv ▸ hzR⟩ : z ∈ ({q a} : Set S)))
        · exact (disjoint_left.mp (haway a w.val w.prop hwu hwv) hzM hzR).elim
    · rintro z (rfl | rfl)
      · exact ⟨(hM a).left_mem,T.V_subset_U (hpT a)⟩
      · exact ⟨(hM a).right_mem,T.V_subset_U (hqT a)⟩
  have hMidNe : ∀ a, p a ≠ q a := by
    intro a he
    obtain ⟨f,h0,h1⟩ := hM a
    exact zero_ne_one (f.injective (Subtype.ext (h0.trans (he.trans h1.symm))))
  obtain ⟨H,hTH,hHV,hHU,hselected,havoid⟩ := exists_drawing_attach_middle_lines
    T p q M hM hMidNe hpT hqT hMT hMdis
  have hε : Function.Injective (fun a ↦ M a \ {p a,q a}) :=
    middle_open_edge_injective H p q M hselected hMdis
  have hdisK : ∀ i, Pairwise (fun w z : D.V ↦ Disjoint (K (i,w)).V (K (i,z)).V) := by
    intro i w z hwz
    exact (hR w.val w.prop z.val z.prop (fun he ↦ hwz (Subtype.ext he))).mono (hKVR i w) (hKVR i z)
  have hex : ∀ i, ∃ ηv ηe, IsMinorModel D.toGraph H.toGraph ηv ηe ∧
      (∀ w (hw : w ∈ D.V), ηv w = (K (i,⟨w,hw⟩)).V) ∧
      ∀ e (he : e ∈ D.E), ηe e = M (i,⟨e,he⟩) \ {p (i,⟨e,he⟩),q (i,⟨e,he⟩)} := by
    intro i
    apply exists_minor_model_of_branch_subdrawings D T H u v hsrc hne (fun w ↦ K (i,w))
      (fun w ↦ (hK i w).1) hTH (fun w ↦ (hK i w).2.2.1) (hdisK i)
      (fun e ↦ M (i,e) \ {p (i,e),q (i,e)})
      (fun e f he ↦ congrArg Prod.snd (hε he)) (fun e ↦ p (i,e)) (fun e ↦ q (i,e))
      (fun e ↦ hselected (i,e)) (hpK i) (hqK i)
    exact havoid.mono_right (by rintro e ⟨a,rfl⟩; exact ⟨(i,a),rfl⟩)
  choose ηv ηe hm hηv hηe using hex
  refine ⟨H,ηv,ηe,hm,?_⟩
  intro i w hw
  rw [hηv i w hw]
  exact (K (i,⟨w,hw⟩)).V_subset_U.trans (hK i ⟨w,hw⟩).2.1.subset

end GraphMinor.GM05
