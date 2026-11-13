module

public import GraphMinor.Surface.DomainPair
public import Mathlib.Data.Finset.Sort
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryParameters
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryTransport
import GraphMinor.LRPlanarity.TreeNeighborhoodOrderedSplice

/-!
# Marked boundary words under one leaf substitution

Part IV, Section 7b of the planarity note replaces a child attachment
marker by the new vertex's boundary incidence list. A boundary match fixes
the complementary arc and sends the attachment interval to the detour.
Pull the new finite markers back to that interval and sort their old
boundary parameters. The ordered interval-substitution lemma then gives
the new boundary word, with every unchanged marker at its old parameter.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: a concrete boundary-interval replacement substitutes
an ordered finite marker list for the old attachment marker. The unchanged
boundary points and their parameters remain fixed. -/
theorem marked_boundary_interval_splice {α : Type*} [DecidableEq α]
    {C C' L J M : Set ℂ} {a b : ℂ} {h k : ℂ → ℂ}
    (hL : IsLineWithEnds L a b) (hcover : L ∪ J = C)
    (hmatch : BdMatch C C' h k) (hfix : ∀ x ∈ J, h x = x) (hdetour : h '' L = M)
    (old : List α) (marker : α) (mark : α → ℂ) (before : α → ℝ) (f : ℝ → ℂ)
    (hmarker : marker ∈ old) (hmarkL : mark marker ∈ L)
    (hf : Continuous f) (hIco : InjOn f (Ico (0 : ℝ) 1)) (hIoc : InjOn f (Ioc (0 : ℝ) 1))
    (himage : f '' Icc (0 : ℝ) 1 = C) (hzero : f 0 ∉ L) (hone : f 1 ∉ L)
    (hbefore : ∀ p ∈ old, before p ∈ Ioo (0 : ℝ) 1 ∧ f (before p) = mark p)
    (hsorted : old.Pairwise (fun p q => before p < before q))
    (hold : ∀ p ∈ old, p ≠ marker → mark p ∈ J ∧ mark p ∉ L)
    (newLabels : Finset α) (hnew : ∀ p ∈ newLabels, mark p ∈ M)
    (hnewinj : InjOn mark (newLabels : Set α)) :
    ∃ (replacement : List α) (g : ℝ → ℂ) (after : α → ℝ),
      replacement.Nodup ∧ (∀ p, p ∈ replacement ↔ p ∈ newLabels) ∧
      Continuous g ∧ InjOn g (Ico (0 : ℝ) 1) ∧ InjOn g (Ioc (0 : ℝ) 1) ∧
      g '' Icc (0 : ℝ) 1 = C' ∧
      (∀ p ∈ old.flatMap (fun e => if e = marker then replacement else [e]),
        after p ∈ Ioo (0 : ℝ) 1 ∧ g (after p) = mark p) ∧
      (old.flatMap (fun e => if e = marker then replacement else [e])).Pairwise
        (fun p q => after p < after q) ∧
      (∀ p ∈ old, p ≠ marker → after p = before p) ∧ g 0 = f 0 ∧ g 1 = f 1 := by
  classical
  have hsub : L ⊆ C := fun x hx => hcover ▸ Or.inl hx
  obtain ⟨lo,hi,hlo,hlohi,hhi,hinterval⟩ :=
    exists_boundary_arc_parameter_interval hL hsub f hf hIco himage hzero hone
  obtain ⟨g,hg,hgIco,hgIoc,hgimage,heval⟩ :=
    exists_transported_boundary_traversal hmatch f hf hIco hIoc himage
  have hleft := hmatch.2.2.1
  have hnewdisjoint : ∀ p ∈ old, p ≠ marker → p ∉ newLabels := by
    intro p hp hpm hpnew
    obtain ⟨x,hx,hxp⟩ := hdetour.symm ▸ hnew p hpnew
    have hpJ := (hold p hp hpm).1
    have hxC : x ∈ C := hsub hx
    have hpC : mark p ∈ C := hcover ▸ Or.inr hpJ
    have he : h x = h (mark p) := hxp.trans (hfix _ hpJ).symm
    have he' := congrArg k he
    rw [hleft hxC,hleft hpC] at he'
    exact (hold p hp hpm).2 (he' ▸ hx)
  let New := {p : α // p ∈ newLabels}
  let : Finite New := newLabels.finite_toSet.to_subtype
  have hparameters : ∀ p : New, ∃ t : ℝ, t ∈ Icc lo hi ∧ g t = mark p.val := by
    intro p
    obtain ⟨x,hx,hxp⟩ := hdetour.symm ▸ hnew p.val p.property
    obtain ⟨t,ht,he⟩ := hinterval.symm ▸ hx
    exact ⟨t,ht,(heval t ⟨hlo.le.trans ht.1,ht.2.trans hhi.le⟩).trans
      ((congrArg h he).trans hxp)⟩
  choose θ hθ using hparameters
  have hθinj : Function.Injective θ := by
    intro p q he
    apply Subtype.ext
    exact hnewinj p.property q.property ((hθ p).2.symm.trans ((congrArg g he).trans (hθ q).2))
  let after := fun p => if hp : p ∈ newLabels then θ ⟨p,hp⟩ else before p
  have hafterNew : ∀ p : New, after p.val = θ p := fun p => dite_eq_left p.property
  have hafterOld : ∀ p ∈ old, p ≠ marker → after p = before p :=
    fun p hp hpm => dite_eq_right (hnewdisjoint p hp hpm)
  let : Fintype New := Fintype.ofFinite New
  let : LinearOrder New := LinearOrder.lift' θ hθinj
  let sorted := (Finset.univ : Finset New).sort (· ≤ ·)
  let replacement := sorted.map Subtype.val
  have hreplacement : ∀ p, p ∈ replacement ↔ p ∈ newLabels := by
    intro p
    constructor
    · intro hp
      obtain ⟨q,_,he⟩ := List.mem_map.mp hp
      exact he ▸ q.property
    · intro hp
      exact List.mem_map.mpr ⟨⟨p,hp⟩,(Finset.mem_sort _).mpr (Finset.mem_univ _),rfl⟩
  have hnewbounds : ∀ p ∈ replacement, after p ∈ Icc lo hi := by
    intro p hp
    have hpnew := (hreplacement p).mp hp
    rw [hafterNew ⟨p,hpnew⟩]
    exact (hθ ⟨p,hpnew⟩).1
  have hnewcoords : ∀ p ∈ replacement, after p ∈ Ioo (0 : ℝ) 1 ∧ g (after p) = mark p := by
    intro p hp
    have hpnew := (hreplacement p).mp hp
    rw [hafterNew ⟨p,hpnew⟩]
    exact ⟨⟨hlo.trans_le (hθ ⟨p,hpnew⟩).1.1,(hθ ⟨p,hpnew⟩).1.2.trans_lt hhi⟩,
      (hθ ⟨p,hpnew⟩).2⟩
  have hnewsorted : replacement.Pairwise (fun p q => after p < after q) := by
    apply List.pairwise_map.mpr
    apply (Finset.sortedLT_sort (Finset.univ : Finset New)).pairwise.imp
    intro p q hpq
    change θ p < θ q at hpq
    rw [hafterNew p,hafterNew q]
    exact hpq
  have hmarkerInterval : before marker ∈ Icc lo hi := by
    obtain ⟨t,ht,he⟩ := hinterval.symm ▸ hmarkL
    have hθm := (hbefore marker hmarker).1
    have heq : before marker = t := hIco ⟨hθm.1.le,hθm.2⟩
      ⟨hlo.le.trans ht.1,ht.2.trans_lt hhi⟩ ((hbefore marker hmarker).2.trans he.symm)
    exact heq.symm ▸ ht
  have houtside : ∀ p ∈ old, p ≠ marker → before p ∉ Icc lo hi ∧ after p = before p := by
    intro p hp hpm
    refine ⟨?_,hafterOld p hp hpm⟩
    intro ht
    have hm : f (before p) ∈ L := hinterval ▸ mem_image_of_mem f ht
    exact (hold p hp hpm).2 ((hbefore p hp).2 ▸ hm)
  have hwordcoords : ∀ p ∈ old.flatMap (fun e => if e = marker then replacement else [e]),
      after p ∈ Ioo (0 : ℝ) 1 ∧ g (after p) = mark p := by
    intro p hp
    obtain ⟨e,he,hpblock⟩ := List.mem_flatMap.mp hp
    by_cases hem : e = marker
    · simp only [hem,ite_true] at hpblock
      exact hnewcoords p hpblock
    · simp only [hem,ite_false] at hpblock
      have hpe : p = e := List.mem_singleton.mp hpblock
      subst p
      rw [hafterOld e he hem]
      refine ⟨(hbefore e he).1,?_⟩
      rw [heval _ ⟨(hbefore e he).1.1.le,(hbefore e he).1.2.le⟩,(hbefore e he).2]
      exact hfix _ (hold e he hem).1
  have hbase : ∀ t ∈ Icc (0 : ℝ) 1, f t ∉ L → g t = f t := by
    intro t ht hnot
    have hm : f t ∈ L ∪ J := hcover.symm ▸ (himage ▸ mem_image_of_mem f ht)
    have htJ : f t ∈ J := hm.resolve_left hnot
    rw [heval t ht,hfix _ htJ]
  exact ⟨replacement,g,after,(Finset.sort_nodup _ _).map Subtype.val_injective,hreplacement,
    hg,hgIco,hgIoc,hgimage,hwordcoords,
    pairwise_parameter_splice old replacement marker before after hsorted hmarkerInterval
      houtside hnewsorted hnewbounds,hafterOld,hbase 0 ⟨le_rfl,zero_le_one⟩ hzero,
    hbase 1 ⟨zero_le_one,le_rfl⟩ hone⟩

end GraphMinor.LRPlanarity
