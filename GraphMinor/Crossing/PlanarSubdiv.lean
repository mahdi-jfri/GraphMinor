module

public import GraphMinor.Crossing.PlanarEuler
public import GraphMinor.HP25.Embedding
import GraphMinor.HP25.SplitTools
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.SurfaceGraph

/-!
# Planarity of subdivisions (`docs/crossing/crossing_extractor.tex`, Sections 1 and 5.3)

This file proves that if a subdivision of a graph `H` is planar, then `H` is planar
(`PlaneEmbedding.of_subdivision`, `planar_of_subdivision`), by joining the arcs of a plane
embedding along each branch path (`PlaneEmbedding.pathImage`). As a consequence, no planar graph
contains a subdivision of `K₃,₃` (`not_planar_of_K33_subdivision`).
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set GraphMinor.HP25 GraphMinor.Surface

variable {V : Type*} {G H : SimpleGraph V} {S B : Set V}

/-! ### Subdivisions on a vertex set -/

/-- `G` on `S` contains a subdivision of `H` on `B ⊆ S` with branch paths `P u v` if:
* for every edge `uv` of `H` on `B`, `P u v` is a path list of `G` on `S` from `u` to `v` with
  `P v u = (P u v).reverse`;
* the branch paths of distinct edges of `H` on `B` meet only at common endpoints;
* no branch path passes through a branch vertex in `B` other than its endpoints. -/
structure IsSubdivisionOn (G : SimpleGraph V) (S : Set V) (H : SimpleGraph V) (B : Set V)
    (P : V → V → List V) : Prop where
  sub : B ⊆ S
  isPath : ∀ u ∈ B, ∀ v ∈ B, H.Adj u v → IsPathList G S (P u v)
  ends : ∀ u ∈ B, ∀ v ∈ B, H.Adj u v → ∃ mid, P u v = u :: mid ++ [v]
  rev : ∀ u ∈ B, ∀ v ∈ B, H.Adj u v → P v u = (P u v).reverse
  inter : ∀ u ∈ B, ∀ v ∈ B, ∀ u' ∈ B, ∀ v' ∈ B, H.Adj u v → H.Adj u' v' →
    s(u, v) ≠ s(u', v') → ∀ x ∈ P u v, x ∈ P u' v' → x ∈ ({u, v} : Set V) ∩ {u', v'}
  avoid : ∀ u ∈ B, ∀ v ∈ B, H.Adj u v → ∀ w ∈ B, w ∈ P u v → w = u ∨ w = v

namespace IsSubdivisionOn

/-- Two distinct edges of `H` on `B` share no edge in their branch paths. -/
theorem edge_ne_of_ne {P : V → V → List V} (h : IsSubdivisionOn G S H B P)
    {u v u' v' : V} (hu : u ∈ B) (hv : v ∈ B) (hu' : u' ∈ B) (hv' : v' ∈ B)
    (huv : H.Adj u v) (huv' : H.Adj u' v') (hne : s(u, v) ≠ s(u', v'))
    {p : V × V} (hp : p ∈ (P u v).zip (P u v).tail)
    {q : V × V} (hq : q ∈ (P u' v').zip (P u' v').tail) :
    s(p.1, p.2) ≠ s(q.1, q.2) := by
  intro he
  have hp1 : p.1 ∈ P u v := (List.of_mem_zip hp).1
  have hp2 : p.2 ∈ P u v := List.mem_of_mem_tail (List.of_mem_zip hp).2
  have hq1 : q.1 ∈ P u' v' := (List.of_mem_zip hq).1
  have hq2 : q.2 ∈ P u' v' := List.mem_of_mem_tail (List.of_mem_zip hq).2
  have hadj : G.Adj p.1 p.2 := isChain_iff_zip.mp (h.isPath u hu v hv huv).2.1 p hp
  have hp12 : p.1 ≠ p.2 := hadj.ne
  have hp1_in : p.1 ∈ ({u, v} : Set V) ∩ {u', v'} := by
    rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h.inter u hu v hv u' hu' v' hv' huv huv' hne p.1 hp1 (h1 ▸ hq1)
    · exact h.inter u hu v hv u' hu' v' hv' huv huv' hne p.1 hp1 (h1 ▸ hq2)
  have hp2_in : p.2 ∈ ({u, v} : Set V) ∩ {u', v'} := by
    rcases Sym2.eq_iff.mp he with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h.inter u hu v hv u' hu' v' hv' huv huv' hne p.2 hp2 (h2 ▸ hq2)
    · exact h.inter u hu v hv u' hu' v' hv' huv huv' hne p.2 hp2 (h2 ▸ hq1)
  have he1 : s(p.1, p.2) = s(u, v) := by
    rcases hp1_in.1 with h1 | h1 <;> rcases hp2_in.1 with h2 | h2
    · exact absurd (h1.trans h2.symm) hp12
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]
    · exact absurd (h1.trans h2.symm) hp12
  have he2 : s(p.1, p.2) = s(u', v') := by
    rcases hp1_in.2 with h1 | h1 <;> rcases hp2_in.2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hp12
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]
    · exact absurd (h1.trans h2.symm) hp12
  exact hne (he1.symm.trans he2)

end IsSubdivisionOn

end GraphMinor.Crossing

namespace GraphMinor.HP25.PlaneEmbedding

open SimpleGraph Set GraphMinor.Surface GraphMinor.Crossing

variable {V : Type*} {G H : SimpleGraph V} {S B : Set V}

/-- If `G` has a plane embedding on `S` and contains a subdivision of `H` on `B ⊆ S`, joining the
arcs along each branch path (`φ.pathImage (P u v)`) yields a plane embedding of `H` on `B`. -/
@[expose] def of_subdivision (φ : PlaneEmbedding G S) {P : V → V → List V}
    (h : IsSubdivisionOn G S H B P) : PlaneEmbedding H B where
  pt := φ.pt
  line u v := φ.pathImage (P u v) ∪ φ.pathImage (P v u)
  finite := φ.finite.subset h.sub
  injOn := φ.injOn.mono h.sub
  line_comm u v := union_comm _ _
  isLine u hu v hv huv := by
    have hrev : φ.pathImage (P v u) = φ.pathImage (P u v) := by
      rw [h.rev u hu v hv huv, φ.pathImage_reverse]
    rw [hrev, union_self]
    obtain ⟨mid, hmid⟩ := h.ends u hu v hv huv
    have hpath := h.isPath u hu v hv huv
    rw [hmid] at hpath ⊢
    have hline := φ.isLine_pathImage (x := u) (l := mid ++ [v]) (by simp) (by simpa using hpath)
    simpa using hline
  inter u hu v hv u' hu' v' hv' huv huv' hne := by
    have hrev : φ.pathImage (P v u) = φ.pathImage (P u v) := by
      rw [h.rev u hu v hv huv, φ.pathImage_reverse]
    have hrev' : φ.pathImage (P v' u') = φ.pathImage (P u' v') := by
      rw [h.rev u' hu' v' hv' huv', φ.pathImage_reverse]
    rw [hrev, hrev', union_self, union_self]
    refine (φ.pathImage_inter_pathImage (h.isPath u hu v hv huv)
      (h.isPath u' hu' v' hv' huv') ?_).trans ?_
    · intro p hp q hq
      exact h.edge_ne_of_ne hu hv hu' hv' huv huv' hne hp hq
    · rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨x, h.inter u hu v hv u' hu' v' hv' huv huv' hne x hx1 hx2, rfl⟩
  avoid u hu v hv huv w hw hpt := by
    have hrev : φ.pathImage (P v u) = φ.pathImage (P u v) := by
      rw [h.rev u hu v hv huv, φ.pathImage_reverse]
    rw [hrev, union_self] at hpt
    exact h.avoid u hu v hv huv w hw
      (φ.mem_of_pt_mem_pathImage (h.isPath u hu v hv huv) (h.sub hw) hpt)

end GraphMinor.HP25.PlaneEmbedding

namespace GraphMinor.Crossing

open SimpleGraph Set GraphMinor.HP25 GraphMinor.Surface

variable {V : Type*} {G H : SimpleGraph V} {S B : Set V}

/-- **Planarity of subdivisions**: if `G` is planar on `S` and contains a subdivision of `H` on
`B ⊆ S`, then `H` is planar on `B`. -/
theorem planar_of_subdivision (hP : Nonempty (PlaneEmbedding G S)) {P : V → V → List V}
    (h : IsSubdivisionOn G S H B P) : Nonempty (PlaneEmbedding H B) :=
  let ⟨φ⟩ := hP
  ⟨φ.of_subdivision h⟩

/-! ### Nonplanarity of `K₃,₃` subdivisions -/

/-- No planar graph contains a subdivision of `K₃,₃`: if `a 0, a 1, a 2` and `b 0, b 1, b 2` are
six distinct vertices in `S` and `L i j` are nine internally disjoint path lists of `G` on `S` from
`a i` to `b j`, then `G` is not planar on `S`. -/
theorem not_planar_of_K33_subdivision {a b : Fin 3 → V} {L : Fin 3 → Fin 3 → List V}
    (hainj : Function.Injective a) (hbinj : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (hpath : ∀ i j, IsPathList G S (L i j))
    (hends : ∀ i j, ∃ mid, L i j = a i :: mid ++ [b j])
    (hdisj : ∀ i j i' j', (i, j) ≠ (i', j') →
      ∀ x ∈ L i j, x ∈ L i' j' → (i = i' ∧ x = a i) ∨ (j = j' ∧ x = b j)) :
    ¬ Nonempty (PlaneEmbedding G S) := by
  rintro ⟨φ⟩
  have haS : ∀ i, a i ∈ S := fun i => by
    obtain ⟨mid, hmid⟩ := hends i 0
    exact (hpath i 0).2.2 (a i) (by simp [hmid])
  have hbS : ∀ j, b j ∈ S := fun j => by
    obtain ⟨mid, hmid⟩ := hends 0 j
    exact (hpath 0 j).2.2 (b j) (by simp [hmid])
  -- Any branch vertex `a k` or `b k` lying on `L i j` must be `a i` or `b j`
  have havoid_a : ∀ i j k, a k ∈ L i j → k = i := by
    intro i j k hmem
    by_contra hne
    obtain ⟨mid, hmid⟩ := hends k 0
    have hak : a k ∈ L k 0 := by simp [hmid]
    have hne_pair : (i, j) ≠ (k, 0) := fun h => hne (Prod.mk.inj h).1.symm
    rcases hdisj i j k 0 hne_pair (a k) hmem hak with ⟨rfl, -⟩ | ⟨-, h2⟩
    · exact hne rfl
    · exact hab k j h2
  have havoid_b : ∀ i j k, b k ∈ L i j → k = j := by
    intro i j k hmem
    by_contra hne
    obtain ⟨mid, hmid⟩ := hends 0 k
    have hbk : b k ∈ L 0 k := by simp [hmid]
    have hne_pair : (i, j) ≠ (0, k) := fun h => hne (Prod.mk.inj h).2.symm
    rcases hdisj i j 0 k hne_pair (b k) hmem hbk with ⟨-, h1⟩ | ⟨rfl, -⟩
    · exact hab i k h1.symm
    · exact hne rfl
  -- Two distinct pairs `(i, j) ≠ (i', j')` share no edge in `L i j` and `L i' j'`
  have hedge_ne : ∀ i j i' j', (i, j) ≠ (i', j') →
      ∀ p ∈ (L i j).zip (L i j).tail, ∀ q ∈ (L i' j').zip (L i' j').tail,
      s(p.1, p.2) ≠ s(q.1, q.2) := by
    intro i j i' j' hne p hp q hq he
    have hp1 : p.1 ∈ L i j := (List.of_mem_zip hp).1
    have hp2 : p.2 ∈ L i j := List.mem_of_mem_tail (List.of_mem_zip hp).2
    have hq1 : q.1 ∈ L i' j' := (List.of_mem_zip hq).1
    have hq2 : q.2 ∈ L i' j' := List.mem_of_mem_tail (List.of_mem_zip hq).2
    have hadj : G.Adj p.1 p.2 := isChain_iff_zip.mp (hpath i j).2.1 p hp
    have hp12 : p.1 ≠ p.2 := hadj.ne
    have hp1_in : (i = i' ∧ p.1 = a i) ∨ (j = j' ∧ p.1 = b j) := by
      rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hdisj i j i' j' hne p.1 hp1 (h1 ▸ hq1)
      · exact hdisj i j i' j' hne p.1 hp1 (h1 ▸ hq2)
    have hp2_in : (i = i' ∧ p.2 = a i) ∨ (j = j' ∧ p.2 = b j) := by
      rcases Sym2.eq_iff.mp he with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact hdisj i j i' j' hne p.2 hp2 (h2 ▸ hq2)
      · exact hdisj i j i' j' hne p.2 hp2 (h2 ▸ hq1)
    rcases hp1_in with ⟨hi, h1⟩ | ⟨hj, h1⟩ <;> rcases hp2_in with ⟨hi', h2⟩ | ⟨hj', h2⟩
    · exact hp12 (h1.trans h2.symm)
    · exact hne (Prod.ext hi hj')
    · exact hne (Prod.ext hi' hj)
    · exact hp12 (h1.trans h2.symm)
  -- Construct a plane embedding of `completeBipartiteGraph (Fin 3) (Fin 3)` on `univ`
  apply not_planar_completeBipartiteGraph_three
  refine ⟨{
    pt := fun u => Sum.casesOn u (fun i => φ.pt (a i)) (fun j => φ.pt (b j))
    line := fun u v =>
      match u, v with
      | Sum.inl i, Sum.inr j => φ.pathImage (L i j)
      | Sum.inr j, Sum.inl i => φ.pathImage (L i j)
      | _, _ => ∅
    finite := toFinite univ
    injOn := by
      rintro (i₁ | j₁) _ (i₂ | j₂) _ he
      · exact congrArg Sum.inl (hainj (φ.injOn (haS i₁) (haS i₂) he))
      · exact False.elim (hab i₁ j₂ (φ.injOn (haS i₁) (hbS j₂) he))
      · exact False.elim (hab i₂ j₁ (φ.injOn (haS i₂) (hbS j₁) he.symm))
      · exact congrArg Sum.inr (hbinj (φ.injOn (hbS j₁) (hbS j₂) he))
    line_comm := by
      rintro (i₁ | j₁) (i₂ | j₂) <;> rfl
    isLine := by
      rintro (i | j) _ (i' | j') _ hadj
      · exact False.elim (by simp [completeBipartiteGraph] at hadj)
      · obtain ⟨mid, hmid⟩ := hends i j'
        have hp := hpath i j'
        dsimp only
        rw [hmid] at hp ⊢
        have hl := φ.isLine_pathImage (x := a i) (l := mid ++ [b j']) (by simp) (by simpa using hp)
        simpa using hl
      · obtain ⟨mid, hmid⟩ := hends i' j
        have hp := hpath i' j
        dsimp only
        rw [hmid] at hp ⊢
        have hl := φ.isLine_pathImage (x := a i') (l := mid ++ [b j]) (by simp) (by simpa using hp)
        simpa using hl.symm
      · exact False.elim (by simp [completeBipartiteGraph] at hadj)
    inter := by
      have hmain : ∀ i j i' j', (i, j) ≠ (i', j') →
          φ.pathImage (L i j) ∩ φ.pathImage (L i' j') ⊆
          (fun u : Fin 3 ⊕ Fin 3 => Sum.casesOn u (fun i => φ.pt (a i)) (fun j => φ.pt (b j))) ''
            (({Sum.inl i, Sum.inr j} : Set (Fin 3 ⊕ Fin 3)) ∩ {Sum.inl i', Sum.inr j'}) := by
        intro i j i' j' hne
        refine (φ.pathImage_inter_pathImage (hpath i j) (hpath i' j')
          (hedge_ne i j i' j' hne)).trans ?_
        rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
        rcases hdisj i j i' j' hne x hx1 hx2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Sum.inl i, ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
        · exact ⟨Sum.inr j, ⟨Or.inr rfl, Or.inr rfl⟩, rfl⟩
      rintro (i | j) _ (i₁ | j₁) _ (i' | j') _ (i₁' | j₁') _ hadj hadj' hne
      all_goals try (exfalso; simp [completeBipartiteGraph] at hadj; done)
      all_goals try (exfalso; simp [completeBipartiteGraph] at hadj'; done)
      · have hne' : (i, j₁) ≠ (i', j₁') := by
          rintro h
          rcases Prod.mk.inj h with ⟨rfl, rfl⟩
          exact hne rfl
        exact hmain i j₁ i' j₁' hne'
      · have hne' : (i, j₁) ≠ (i₁', j') := by
          rintro h
          rcases Prod.mk.inj h with ⟨rfl, rfl⟩
          exact hne (Sym2.eq_swap)
        refine (hmain i j₁ i₁' j' hne').trans (image_mono ?_)
        rw [pair_comm (Sum.inr j') (Sum.inl i₁')]
      · have hne' : (i₁, j) ≠ (i', j₁') := by
          rintro h
          rcases Prod.mk.inj h with ⟨rfl, rfl⟩
          exact hne (Sym2.eq_swap)
        refine (hmain i₁ j i' j₁' hne').trans (image_mono ?_)
        rw [pair_comm (Sum.inr j) (Sum.inl i₁)]
      · have hne' : (i₁, j) ≠ (i₁', j') := by
          rintro h
          rcases Prod.mk.inj h with ⟨rfl, rfl⟩
          exact hne rfl
        refine (hmain i₁ j i₁' j' hne').trans (image_mono ?_)
        rw [pair_comm (Sum.inr j) (Sum.inl i₁), pair_comm (Sum.inr j') (Sum.inl i₁')]
    avoid := by
      rintro (i | j) _ (i₁ | j₁) _ hadj (k | k) _ hpt
      all_goals try (exfalso; simp [completeBipartiteGraph] at hadj; done)
      · exact Or.inl (congrArg Sum.inl (havoid_a i j₁ k
          (φ.mem_of_pt_mem_pathImage (hpath i j₁) (haS k) hpt)))
      · exact Or.inr (congrArg Sum.inr (havoid_b i j₁ k
          (φ.mem_of_pt_mem_pathImage (hpath i j₁) (hbS k) hpt)))
      · exact Or.inr (congrArg Sum.inl (havoid_a i₁ j k
          (φ.mem_of_pt_mem_pathImage (hpath i₁ j) (haS k) hpt)))
      · exact Or.inl (congrArg Sum.inr (havoid_b i₁ j k
          (φ.mem_of_pt_mem_pathImage (hpath i₁ j) (hbS k) hpt)))
  }⟩

end GraphMinor.Crossing
