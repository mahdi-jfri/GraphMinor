module

public import GraphMinor.GM08.Section17RootLeaves
public import GraphMinor.GM08.Section11Transport
import GraphMinor.GM11.Defs
import GraphMinor.GM11.RadialChord

/-!
# Adding a spoke at every root of a drawn graft

Let a drawing `K` carry a graft `X` through a graph bijection. Add, at the point
of each root, a spoke: an arc from that point to a new vertex, meeting `K` only
at its start, with spokes of different roots disjoint. The new drawing then
carries the graft `rootLeafGraft X`, which has one new leaf at each root.

The proof checks the ends of every edge. An old edge has its closure inside the
support of `K`, which contains no new vertex, so its ends do not change. A
spoke without its two ends is a new edge whose closure is the spoke, and the
only vertices on the spoke are its two ends.
-/

public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v

variable {T : Type*} [TopologicalSpace T] [T2Space T]

/-- Adding a spoke at the point of every root gives a drawing of the graft with
one new leaf at each root. -/
theorem isGraphBij_rootLeafGraph_of_spokes {α : Type u} {β : Type v} {X : Graft α β}
    {K H : Drawing T} {f₀ : α → T} {g₀ : β → Set T}
    (hb : IsGraphBij X.G K.toGraph f₀ g₀) (q : T → T) (ℓ : T → Set T)
    (hline : ∀ x ∈ f₀ '' X.T, IsLineWithEnds (ℓ x) x (q x))
    (hne : ∀ x ∈ f₀ '' X.T, x ≠ q x)
    (hK : ∀ x ∈ f₀ '' X.T, ℓ x ∩ K.U ⊆ {x})
    (hdisj : ∀ x ∈ f₀ '' X.T, ∀ y ∈ f₀ '' X.T, x ≠ y → Disjoint (ℓ x) (ℓ y))
    (hV : H.V = K.V ∪ q '' (f₀ '' X.T))
    (hE : H.E = K.E ∪ (fun x => ℓ x \ {x, q x}) '' (f₀ '' X.T)) :
    IsGraphBij (rootLeafGraph X) H.toGraph (Sum.elim f₀ (q ∘ f₀))
      (Sum.elim g₀ (fun t => ℓ (f₀ t) \ {f₀ t, q (f₀ t)})) := by
  classical
  set R := f₀ '' X.T with hRdef
  have hRV : ∀ t ∈ X.T, f₀ t ∈ K.V := fun t ht => hb.bijV.mapsTo (X.T_subset ht)
  have hRU : ∀ t ∈ X.T, f₀ t ∈ K.U := fun t ht => K.V_subset_U (hRV t ht)
  have hstart : ∀ x ∈ R, x ∈ ℓ x := by
    intro x hx
    obtain ⟨φ, h0, -⟩ := hline x hx
    have h := (φ 0).2
    rwa [h0] at h
  have hend : ∀ x ∈ R, q x ∈ ℓ x := by
    intro x hx
    obtain ⟨φ, -, h1⟩ := hline x hx
    have h := (φ 1).2
    rwa [h1] at h
  have hqK : ∀ x ∈ R, q x ∉ K.U := fun x hx h =>
    hne x hx (hK x hx ⟨hend x hx, h⟩).symm
  have hqinj : ∀ x ∈ R, ∀ y ∈ R, q x = q y → x = y := by
    intro x hx y hy hxy
    by_contra h
    exact disjoint_left.mp (hdisj x hx y hy h) (hend x hx) (hxy ▸ hend y hy)
  have hcl : ∀ x ∈ R, closure (ℓ x \ {x, q x}) = ℓ x := fun x hx =>
    GM11.closure_sdiff_pair (hline x hx)
  have hspokeV : ∀ x ∈ R, ℓ x ∩ H.V = {x, q x} := by
    intro x hx
    apply subset_antisymm
    · rintro z ⟨hz, hzV⟩
      rw [hV] at hzV
      rcases hzV with hzK | ⟨y, hy, rfl⟩
      · exact Or.inl (hK x hx ⟨hz, K.V_subset_U hzK⟩)
      · by_cases hxy : x = y
        · exact Or.inr (hxy ▸ rfl)
        · exact absurd hz (disjoint_right.mp (hdisj x hx y hy hxy) (hend y hy))
    · rintro z (rfl | rfl)
      · obtain ⟨t, ht, rfl⟩ := hx
        exact ⟨hstart _ ⟨t, ht, rfl⟩, hV ▸ Or.inl (hRV t ht)⟩
      · exact ⟨hend _ hx, hV ▸ Or.inr ⟨_, hx, rfl⟩⟩
  have hKcl : ∀ e ∈ K.E, closure e ∩ H.V = closure e ∩ K.V := by
    intro e he
    rw [hV, inter_union_distrib_left]
    have : closure e ∩ q '' R = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr ?_
      rintro _ ⟨hz, x, hx, rfl⟩
      exact hqK x hx (K.closure_subset_U he hz)
    rw [this, union_empty]
  have hspoke_ne : ∀ x ∈ R, (ℓ x \ {x, q x}).Nonempty := fun x hx =>
    (GM11.isPathConnected_sdiff_pair (hline x hx)).nonempty
  have hspoke_notK : ∀ x ∈ R, ℓ x \ {x, q x} ∉ K.E := by
    intro x hx hxK
    obtain ⟨z, hz⟩ := hspoke_ne x hx
    have hzU : z ∈ K.U := K.closure_subset_U hxK (subset_closure hz)
    exact hz.2 (Or.inl (hK x hx ⟨hz.1, hzU⟩))
  have hspoke_inj : ∀ x ∈ R, ∀ y ∈ R, ℓ x \ {x, q x} = ℓ y \ {y, q y} → x = y := by
    intro x hx y hy hxy
    by_contra h
    obtain ⟨z, hz⟩ := hspoke_ne x hx
    have hz' : z ∈ ℓ y \ {y, q y} := hxy ▸ hz
    exact disjoint_left.mp (hdisj x hx y hy h) hz.1 hz'.1
  have hVK : ∀ v ∈ V(X.G), f₀ v ∈ K.V := fun v hv => hb.bijV.mapsTo hv
  have hVinj : ∀ v ∈ V(X.G), ∀ w ∈ V(X.G), f₀ v = f₀ w → v = w := fun v hv w hw h =>
    hb.bijV.injOn hv hw h
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro (v | t) hv
    · show f₀ v ∈ H.V
      rw [hV]; exact Or.inl (hVK v ((inl_mem_rootLeafGraph_vertexSet X v).mp hv))
    · show q (f₀ t) ∈ H.V
      rw [hV]; exact Or.inr ⟨f₀ t, ⟨t, (inr_mem_rootLeafGraph_vertexSet X t).mp hv, rfl⟩, rfl⟩
  · rintro (v | t) hv (w | s) hw h
    · have hv' := (inl_mem_rootLeafGraph_vertexSet X v).mp hv
      have hw' := (inl_mem_rootLeafGraph_vertexSet X w).mp hw
      exact congrArg Sum.inl (hVinj v hv' w hw' h)
    · have hs := (inr_mem_rootLeafGraph_vertexSet X s).mp hw
      have hv' := (inl_mem_rootLeafGraph_vertexSet X v).mp hv
      have h' : f₀ v = q (f₀ s) := h
      exact (hqK _ ⟨s, hs, rfl⟩ (by rw [← h']; exact K.V_subset_U (hVK v hv'))).elim
    · have ht := (inr_mem_rootLeafGraph_vertexSet X t).mp hv
      have hw' := (inl_mem_rootLeafGraph_vertexSet X w).mp hw
      have h' : q (f₀ t) = f₀ w := h
      exact (hqK _ ⟨t, ht, rfl⟩ (by rw [h']; exact K.V_subset_U (hVK w hw'))).elim
    · have ht := (inr_mem_rootLeafGraph_vertexSet X t).mp hv
      have hs := (inr_mem_rootLeafGraph_vertexSet X s).mp hw
      have h' := hqinj _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩ h
      exact congrArg Sum.inr (hVinj t (X.T_subset ht) s (X.T_subset hs) h')
  · intro z hz
    change z ∈ H.V at hz
    rw [hV] at hz
    rcases hz with hz | ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := hb.bijV.surjOn hz
      exact ⟨Sum.inl v, (inl_mem_rootLeafGraph_vertexSet X v).mpr hv, rfl⟩
    · exact ⟨Sum.inr t, (inr_mem_rootLeafGraph_vertexSet X t).mpr ht, rfl⟩
  · rintro (e | t) he
    · show g₀ e ∈ H.E
      rw [hE]; exact Or.inl (hb.bijE.mapsTo ((inl_mem_rootLeafGraph_edgeSet X e).mp he))
    · show ℓ (f₀ t) \ {f₀ t, q (f₀ t)} ∈ H.E
      rw [hE]; exact Or.inr ⟨f₀ t, ⟨t, (inr_mem_rootLeafGraph_edgeSet X t).mp he, rfl⟩, rfl⟩
  · rintro (e | t) he (e' | s) he' h
    · exact congrArg Sum.inl (hb.bijE.injOn ((inl_mem_rootLeafGraph_edgeSet X e).mp he)
        ((inl_mem_rootLeafGraph_edgeSet X e').mp he') h)
    · have hs := (inr_mem_rootLeafGraph_edgeSet X s).mp he'
      have hK' : g₀ e ∈ K.E := hb.bijE.mapsTo ((inl_mem_rootLeafGraph_edgeSet X e).mp he)
      have h' : g₀ e = ℓ (f₀ s) \ {f₀ s, q (f₀ s)} := h
      exact (hspoke_notK _ ⟨s, hs, rfl⟩ (h' ▸ hK')).elim
    · have ht := (inr_mem_rootLeafGraph_edgeSet X t).mp he
      have hK' : g₀ e' ∈ K.E := hb.bijE.mapsTo ((inl_mem_rootLeafGraph_edgeSet X e').mp he')
      have h' : ℓ (f₀ t) \ {f₀ t, q (f₀ t)} = g₀ e' := h
      exact (hspoke_notK _ ⟨t, ht, rfl⟩ (h' ▸ hK')).elim
    · have ht := (inr_mem_rootLeafGraph_edgeSet X t).mp he
      have hs := (inr_mem_rootLeafGraph_edgeSet X s).mp he'
      have h' := hspoke_inj _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩ h
      exact congrArg Sum.inr (hVinj t (X.T_subset ht) s (X.T_subset hs) h')
  · intro z hz
    change z ∈ H.E at hz
    rw [hE] at hz
    rcases hz with hz | ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    · obtain ⟨e, he, rfl⟩ := hb.bijE.surjOn hz
      exact ⟨Sum.inl e, (inl_mem_rootLeafGraph_edgeSet X e).mpr he, rfl⟩
    · exact ⟨Sum.inr t, (inr_mem_rootLeafGraph_edgeSet X t).mpr ht, rfl⟩
  · -- the ends of each edge
    have hlinkH : ∀ (E' : Set T) (a b : T), H.toGraph.IsLink E' a b ↔
        E' ∈ H.E ∧ a ∈ H.V ∧ b ∈ H.V ∧ closure E' ∩ H.V = {a, b} := fun _ _ _ => Iff.rfl
    have hpair : ∀ {a b c d : T}, ({a, b} : Set T) = {c, d} → c ∈ ({a, b} : Set T) ∧
        d ∈ ({a, b} : Set T) := fun h => ⟨h ▸ mem_insert _ _, h ▸ mem_insert_of_mem _ rfl⟩
    rintro (e | t) he (x | x) hx (y | y) hy
    · have he' := (inl_mem_rootLeafGraph_edgeSet X e).mp he
      have hx' := (inl_mem_rootLeafGraph_vertexSet X x).mp hx
      have hy' := (inl_mem_rootLeafGraph_vertexSet X y).mp hy
      change X.G.IsLink e x y ↔ _
      rw [hb.isLink e he' x hx' y hy', hlinkH]
      change (g₀ e ∈ K.E ∧ f₀ x ∈ K.V ∧ f₀ y ∈ K.V ∧ closure (g₀ e) ∩ K.V = {f₀ x, f₀ y}) ↔ _
      have heK : g₀ e ∈ K.E := hb.bijE.mapsTo he'
      simp only [Sum.elim_inl]
      rw [hKcl _ heK]
      constructor
      · rintro ⟨-, h1, h2, h3⟩
        exact ⟨hE ▸ Or.inl heK, hV ▸ Or.inl h1, hV ▸ Or.inl h2, h3⟩
      · rintro ⟨-, -, -, h3⟩
        exact ⟨heK, hVK x hx', hVK y hy', h3⟩
    -- an old edge never has a new leaf as an end
    · have he' := (inl_mem_rootLeafGraph_edgeSet X e).mp he
      have hy' := (inr_mem_rootLeafGraph_vertexSet X y).mp hy
      change False ↔ _
      refine ⟨False.elim, ?_⟩
      rintro ⟨-, -, -, h3⟩
      change closure (g₀ e) ∩ H.V = {f₀ x, q (f₀ y)} at h3
      have hm : q (f₀ y) ∈ closure (g₀ e) ∩ H.V := by rw [h3]; exact Or.inr rfl
      exact hqK _ ⟨y, hy', rfl⟩ (K.closure_subset_U (hb.bijE.mapsTo he') hm.1)
    · have he' := (inl_mem_rootLeafGraph_edgeSet X e).mp he
      have hx' := (inr_mem_rootLeafGraph_vertexSet X x).mp hx
      change False ↔ _
      refine ⟨False.elim, ?_⟩
      rintro ⟨-, -, -, h3⟩
      change closure (g₀ e) ∩ H.V = {q (f₀ x), f₀ y} at h3
      have hm : q (f₀ x) ∈ closure (g₀ e) ∩ H.V := by rw [h3]; exact Or.inl rfl
      exact hqK _ ⟨x, hx', rfl⟩ (K.closure_subset_U (hb.bijE.mapsTo he') hm.1)
    · have he' := (inl_mem_rootLeafGraph_edgeSet X e).mp he
      have hx' := (inr_mem_rootLeafGraph_vertexSet X x).mp hx
      change False ↔ _
      refine ⟨False.elim, ?_⟩
      rintro ⟨-, -, -, h3⟩
      change closure (g₀ e) ∩ H.V = {q (f₀ x), q (f₀ y)} at h3
      have hm : q (f₀ x) ∈ closure (g₀ e) ∩ H.V := by rw [h3]; exact Or.inl rfl
      exact hqK _ ⟨x, hx', rfl⟩ (K.closure_subset_U (hb.bijE.mapsTo he') hm.1)
    all_goals
      have ht := (inr_mem_rootLeafGraph_edgeSet X t).mp he
      have htR : f₀ t ∈ R := ⟨t, ht, rfl⟩
      have heq : closure (ℓ (f₀ t) \ {f₀ t, q (f₀ t)}) ∩ H.V = {f₀ t, q (f₀ t)} := by
        rw [hcl _ htR, hspokeV _ htR]
      have hspH : ℓ (f₀ t) \ {f₀ t, q (f₀ t)} ∈ H.E := by
        rw [hE]; exact Or.inr ⟨_, htR, rfl⟩
      have htU : f₀ t ∈ K.U := hRU t ht
    · -- two old ends
      have hx' := (inl_mem_rootLeafGraph_vertexSet X x).mp hx
      have hy' := (inl_mem_rootLeafGraph_vertexSet X y).mp hy
      change False ↔ _
      refine ⟨False.elim, ?_⟩
      rintro ⟨-, -, -, h3⟩
      change closure (ℓ (f₀ t) \ {f₀ t, q (f₀ t)}) ∩ H.V = {f₀ x, f₀ y} at h3
      rw [heq] at h3
      have hm : q (f₀ t) ∈ ({f₀ x, f₀ y} : Set T) := by rw [← h3]; exact Or.inr rfl
      rcases hm with hm | hm
      · exact hqK _ htR (hm ▸ K.V_subset_U (hVK x hx'))
      · exact hqK _ htR (hm ▸ K.V_subset_U (hVK y hy'))
    · -- an old end and a new end
      have hx' := (inl_mem_rootLeafGraph_vertexSet X x).mp hx
      have hy' := (inr_mem_rootLeafGraph_vertexSet X y).mp hy
      change (t ∈ X.T ∧ x = t ∧ y = t) ↔ _
      constructor
      · rintro ⟨-, hxt, hyt⟩
        rw [hxt, hyt]
        refine ⟨hspH, ?_, ?_, heq⟩
        · show f₀ t ∈ H.V
          rw [hV]; exact Or.inl (hVK t (X.T_subset ht))
        · show q (f₀ t) ∈ H.V
          rw [hV]; exact Or.inr ⟨_, htR, rfl⟩
      · rintro ⟨-, -, -, h3⟩
        change closure (ℓ (f₀ t) \ {f₀ t, q (f₀ t)}) ∩ H.V = {f₀ x, q (f₀ y)} at h3
        rw [heq] at h3
        have h1 : f₀ x ∈ ({f₀ t, q (f₀ t)} : Set T) := by rw [h3]; exact Or.inl rfl
        have h2 : q (f₀ y) ∈ ({f₀ t, q (f₀ t)} : Set T) := by rw [h3]; exact Or.inr rfl
        refine ⟨ht, ?_, ?_⟩
        · rcases h1 with h1 | h1
          · exact hVinj x hx' t (X.T_subset ht) h1
          · exact (hqK _ htR (h1 ▸ K.V_subset_U (hVK x hx'))).elim
        · rcases h2 with h2 | h2
          · exact (hqK _ ⟨y, hy', rfl⟩ (h2 ▸ htU)).elim
          · exact hVinj y (X.T_subset hy') t (X.T_subset ht)
              (hqinj _ ⟨y, hy', rfl⟩ _ htR h2)
    · -- a new end and an old end
      have hx' := (inr_mem_rootLeafGraph_vertexSet X x).mp hx
      have hy' := (inl_mem_rootLeafGraph_vertexSet X y).mp hy
      change (t ∈ X.T ∧ y = t ∧ x = t) ↔ _
      constructor
      · rintro ⟨-, hyt, hxt⟩
        rw [hxt, hyt]
        refine ⟨hspH, ?_, ?_, ?_⟩
        · show q (f₀ t) ∈ H.V
          rw [hV]; exact Or.inr ⟨_, htR, rfl⟩
        · show f₀ t ∈ H.V
          rw [hV]; exact Or.inl (hVK t (X.T_subset ht))
        · change closure (ℓ (f₀ t) \ {f₀ t, q (f₀ t)}) ∩ H.V = {q (f₀ t), f₀ t}
          rw [heq, pair_comm]
      · rintro ⟨-, -, -, h3⟩
        change closure (ℓ (f₀ t) \ {f₀ t, q (f₀ t)}) ∩ H.V = {q (f₀ x), f₀ y} at h3
        rw [heq] at h3
        have h1 : f₀ y ∈ ({f₀ t, q (f₀ t)} : Set T) := by rw [h3]; exact Or.inr rfl
        have h2 : q (f₀ x) ∈ ({f₀ t, q (f₀ t)} : Set T) := by rw [h3]; exact Or.inl rfl
        refine ⟨ht, ?_, ?_⟩
        · rcases h1 with h1 | h1
          · exact hVinj y hy' t (X.T_subset ht) h1
          · exact (hqK _ htR (h1 ▸ K.V_subset_U (hVK y hy'))).elim
        · rcases h2 with h2 | h2
          · exact (hqK _ ⟨x, hx', rfl⟩ (h2 ▸ htU)).elim
          · exact hVinj x (X.T_subset hx') t (X.T_subset ht)
              (hqinj _ ⟨x, hx', rfl⟩ _ htR h2)
    · -- two new ends
      have hx' := (inr_mem_rootLeafGraph_vertexSet X x).mp hx
      have hy' := (inr_mem_rootLeafGraph_vertexSet X y).mp hy
      change False ↔ _
      refine ⟨False.elim, ?_⟩
      rintro ⟨-, -, -, h3⟩
      change closure (ℓ (f₀ t) \ {f₀ t, q (f₀ t)}) ∩ H.V = {q (f₀ x), q (f₀ y)} at h3
      rw [heq] at h3
      have hm : f₀ t ∈ ({q (f₀ x), q (f₀ y)} : Set T) := by rw [← h3]; exact Or.inl rfl
      rcases hm with hm | hm
      · exact hqK _ ⟨x, hx', rfl⟩ (hm ▸ htU)
      · exact hqK _ ⟨y, hy', rfl⟩ (hm ▸ htU)

end GraphMinor.GM08
