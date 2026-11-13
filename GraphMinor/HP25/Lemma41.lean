module

public import GraphMinor.HP25.Prop36
public import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Prop22
import GraphMinor.HP25.Prop23
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Lemma 4.1: webs are maximally crossless

Humeau and Pous, arXiv:2505.16431v2, Lemma 4.1 (page 12): "The frame of a web $G$ is crossed in all
edge extensions of $G$."

We follow the paper's proof, by induction on the order of `G`. A web whose frame has length three
is a clique (Proposition 2.2). Otherwise, by Proposition 3.6, `G` is the web composition of two
webs `H` and `K` along an induced `C`-path `P`, and "Claim 4.2. Every vertex of $H$ is
$C_H$-connected to $C_H-P$ in $H$, and similarly in $K$." follows from the third item of
Proposition 3.4 (`claim_4_2`). For the new edge `e = xy`:
* if `x` is in `H - P` and `y` in `K - P`, the paths of Claim 4.2 joined by `e` cross `P`
  (`Setting.cross_two_sides`);
* otherwise `e` lies in `H` (or in `K`), the induction hypothesis gives a crossing `(P₁, P₂)` of
  `C_H` in `H + e`, and the five cases of Figure 11 extend it to a crossing of `C` in `G + e`
  (`Setting.cross_of_side`).

In the five cases we keep the paper's constructions. The paper sorts the cases by the ends of `P₁`
and `P₂` on `P`; we sort them by their positions on the frame `C_H = a A b m⁻¹` of `H`, where
`P = a m b`. The ends at positions in `m` are the ends that need extending. When an end sits on `a`
or `b`, the construction of a case with more ends on `P` applies (for example, if `P₁` runs from `a`
into `m` and `P₂` from `A` into `m`, we use the construction of the fourth case with the roles of
`P₁` and `P₂` exchanged).

A web need not be finite in our setting (a clique could be infinite), so the statement assumes, as
the paper does for all its graphs, that the vertex type is finite.
-/

namespace GraphMinor.HP25

open SimpleGraph Set PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V}

public section

/-- **Claim 4.2** (Humeau and Pous, page 12). "Every vertex of $H$ is $C_H$-connected to $C_H-P$ in
$H$, and similarly in $K$." Here `H` is a web on `T` with frame `C_H = a A b m⁻¹`, the path
`P = a m b` is induced in `H`, and `A` is not empty. The paper's proof: "As $P$ is induced in both
$H$ and $K$, these webs cannot be expressed as some edge composition along some edge between
non-consecutive vertices of $P$. The claim follows by the third item of Proposition 3.4". -/
theorem claim_4_2 {H : SimpleGraph V} {T : Set V} {a b : V} {A m : List V}
    (hH : IsWebOn H T (a :: A ++ b :: m.reverse))
    (hind : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], H.Adj u v → IsListEdge (a :: m ++ [b]) u v)
    (hA : A ≠ []) {x : V} (hx : x ∈ T) :
    IsConnectedAvoiding H {z | z ∈ a :: A ++ b :: m.reverse} x {z | z ∈ A} := by
  have hnd : (a :: A ++ b :: m.reverse).Nodup := by
    obtain ⟨-, -, -, -, ⟨hC, -⟩, -⟩ := hH
    exact hC.2.1
  have hrot : (a :: A ++ b :: m.reverse).rotate 1 = A ++ (b :: m.reverse ++ [a]) := by
    simp [List.rotate_cons_succ]
  rcases prop_3_4_iii hH hx hrot hA with h | ⟨c, c', hc, hc', hcA, hc'A, -, -, -, hcomp⟩
  · exact h
  exfalso
  obtain ⟨hadj, hnot, -, -⟩ := hcomp.chord hnd
  have hl : ∀ v, v ∈ a :: A ++ b :: m.reverse → v ∉ A → v ∈ a :: m ++ [b] := fun v hv hvA => by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse] at hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]
    tauto
  have hedge := hind c (hl c hc hcA) c' (hl c' hc' hc'A) hadj
  refine hnot ?_
  -- an edge of `P` is an edge of the frame `b m⁻¹ a A`, a rotation of `C_H`
  rw [← isCycleEdge_rotate _ (A.length + 1)]
  have hrot' : (a :: A ++ b :: m.reverse).rotate (A.length + 1) = b :: (m.reverse ++ a :: A) := by
    rw [show a :: A ++ b :: m.reverse = (a :: A) ++ (b :: m.reverse) by simp,
      show A.length + 1 = (a :: A).length by simp, List.rotate_append_length_eq]
    simp
  rw [hrot']
  refine isCycleEdge_of_isListEdge ?_
  rw [show b :: (m.reverse ++ a :: A) ++ [b] = (b :: m.reverse ++ [a]) ++ (A ++ [b]) by simp]
  refine IsListEdge.append_left ?_
  have := hedge.reverse
  simpa using this

/-- The paths of Claim 4.2, as lists of vertices of `G`: a path of `G[T]` from a vertex `t` to a
vertex `c` of `A` with no inner vertex on `D` gives such a list. -/
theorem side_path {T : Set V} {D A : List V} {t : V} (ht : t ∈ T)
    (hcl : IsConnectedAvoiding (restrict G T) {z | z ∈ D} t {z | z ∈ A}) :
    ∃ c ∈ A, ∃ P : List V, P.head? = some t ∧ P.getLast? = some c ∧ P.IsChain G.Adj ∧ P.Nodup ∧
      (∀ w ∈ P, w ∈ T) ∧ ∀ w ∈ P, w ∈ D → w = t ∨ w = c := by
  obtain ⟨c, hc, p, hp, hin⟩ := hcl
  refine ⟨c, hc, p.support, ?_, ?_, ?_, (Walk.isPath_def p).mp hp,
    mem_of_support_restrict p ht, fun w hw hwD => ?_⟩
  · rw [← Walk.cons_tail_support]; rfl
  · rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  · have := (p.mapLe (restrict_le G T)).isChain_adj_support
    rwa [support_mapLe] at this
  · by_contra hne
    push Not at hne
    exact hin w hw hne.1 hne.2 hwD

/-- Claim 4.2 for a vertex `t` that is on `D` only if it is in `A`: a list from `t` to a vertex
`c` of `A` whose only vertex on `D` is `c`. -/
theorem side_path' {T : Set V} {D A : List V} {t : V} (ht : t ∈ T)
    (hcl : IsConnectedAvoiding (restrict G T) {z | z ∈ D} t {z | z ∈ A}) (htA : t ∈ D → t ∈ A) :
    ∃ c ∈ A, ∃ P : List V, P.head? = some t ∧ P.getLast? = some c ∧ P.IsChain G.Adj ∧ P.Nodup ∧
      (∀ w ∈ P, w ∈ T) ∧ ∀ w ∈ P, w ∈ D → w = c := by
  by_cases htD : t ∈ D
  · refine ⟨t, htA htD, [t], rfl, rfl, List.isChain_singleton t, List.nodup_singleton t,
      fun w hw => by rw [List.mem_singleton.mp hw]; exact ht, fun w hw _ => List.mem_singleton.mp hw⟩
  · obtain ⟨c, hc, P, hh, hl, hP, hnd, hT, hin⟩ := side_path ht hcl
    refine ⟨c, hc, P, hh, hl, hP, hnd, hT, fun w hw hwD => ?_⟩
    rcases hin w hw hwD with rfl | h
    · exact absurd hwD htD
    · exact h

end

/-! ### The setting of the proof -/

public section

/-- The situation of the proof of Lemma 4.1: `G` contains `H = G[S₁]` with frame `a A b m⁻¹` and
`K = G[S₂]` with frame `b B a m`, meeting in the induced path `P = a m b`, and the frame `C` of `G`
is a rotation of `a A b B` with `A` and `B` nonempty. Of the two webs of the paper we keep only what
the extension of crossings uses: the frames are cycles, and Claim 4.2 holds on each side
(`Setting.of_webs` builds the setting from two webs). -/
structure Setting (G : SimpleGraph V) (S₁ S₂ : Set V) (a b : V) (m A B C : List V)
    (k : ℕ) : Prop where
  inter : S₁ ∩ S₂ = {v | v ∈ a :: m ++ [b]}
  ind : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], G.Adj u v → IsListEdge (a :: m ++ [b]) u v
  cycH : IsCycleList (restrict G S₁) (a :: A ++ b :: m.reverse)
  frameH : ∀ v ∈ a :: A ++ b :: m.reverse, v ∈ S₁
  claimH : ∀ t ∈ S₁, IsConnectedAvoiding (restrict G S₁) {z | z ∈ a :: A ++ b :: m.reverse} t
    {z | z ∈ A}
  cycK : IsCycleList (restrict G S₂) (b :: B ++ a :: m)
  frameK : ∀ v ∈ b :: B ++ a :: m, v ∈ S₂
  claimK : ∀ t ∈ S₂, IsConnectedAvoiding (restrict G S₂) {z | z ∈ b :: B ++ a :: m} t {z | z ∈ B}
  rot : C.rotate k = a :: A ++ b :: B
  neA : A ≠ []
  neB : B ≠ []

namespace Setting

variable {S₁ S₂ : Set V} {a b : V} {m A B C : List V} {k : ℕ}

/-- **The setting from two webs**, as in the paper. Claim 4.2 on each side is `claim_4_2`. -/
theorem of_webs (inter : S₁ ∩ S₂ = {v | v ∈ a :: m ++ [b]})
    (ind : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], G.Adj u v → IsListEdge (a :: m ++ [b]) u v)
    (hH : IsWebOn (restrict G S₁) S₁ (a :: A ++ b :: m.reverse))
    (hK : IsWebOn (restrict G S₂) S₂ (b :: B ++ a :: m)) (rot : C.rotate k = a :: A ++ b :: B)
    (neA : A ≠ []) (neB : B ≠ []) : Setting G S₁ S₂ a b m A B C k := by
  have hK' : IsWebOn (restrict G S₂) S₂ (b :: B ++ a :: m.reverse.reverse) := by
    rw [List.reverse_reverse]; exact hK
  have hind : ∀ u ∈ b :: m.reverse ++ [a], ∀ v ∈ b :: m.reverse ++ [a], G.Adj u v →
      IsListEdge (b :: m.reverse ++ [a]) u v := fun u hu v hv h => by
    have hr : (a :: m ++ [b]).reverse = b :: m.reverse ++ [a] := by simp
    rw [← hr, List.mem_reverse] at hu hv
    rw [← hr]
    exact (ind u hu v hv h).reverse
  refine ⟨inter, ind, (by obtain ⟨-, -, -, -, ⟨hC, -⟩, -⟩ := hH; exact hC), hH.frame_subset,
    fun t ht => claim_4_2 hH (fun u hu v hv h => ind u hu v hv h.1) neA ht, (by obtain ⟨-, -, -, -, ⟨hC, -⟩, -⟩ := hK; exact hC),
    hK.frame_subset, fun t ht => ?_, rot, neA, neB⟩
  have := claim_4_2 hK' (fun u hu v hv h => hind u hu v hv h.1) neB ht
  rwa [List.reverse_reverse] at this

theorem nodupH (hS : Setting G S₁ S₂ a b m A B C k) : (a :: A ++ b :: m.reverse).Nodup :=
  hS.cycH.2.1

theorem nodupK (hS : Setting G S₁ S₂ a b m A B C k) : (b :: B ++ a :: m).Nodup :=
  hS.cycK.2.1

theorem mem_C (hS : Setting G S₁ S₂ a b m A B C k) {v : V} :
    v ∈ C ↔ v = a ∨ v ∈ A ∨ v = b ∨ v ∈ B := by
  rw [← List.mem_rotate (n := k), hS.rot]
  simp

theorem mem_S₁ (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ a :: A ++ b :: m.reverse) :
    v ∈ S₁ :=
  hS.frameH v hv

theorem mem_S₂ (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ b :: B ++ a :: m) :
    v ∈ S₂ :=
  hS.frameK v hv

theorem l_S₁ (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ a :: m ++ [b]) : v ∈ S₁ :=
  hS.mem_S₁ (by simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse,
    List.mem_nil_iff, or_false] at hv ⊢; tauto)

theorem l_S₂ (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ a :: m ++ [b]) : v ∈ S₂ :=
  hS.mem_S₂ (by simp only [List.cons_append, List.mem_cons, List.mem_append,
    List.mem_nil_iff, or_false] at hv ⊢; tauto)

theorem mem_l_of_inter (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (h₁ : v ∈ S₁) (h₂ : v ∈ S₂) :
    v ∈ a :: m ++ [b] := by
  have : v ∈ S₁ ∩ S₂ := ⟨h₁, h₂⟩
  rw [hS.inter] at this
  exact this

/-- The facts on the frames that the proof uses, from `C_H` and `C_K` having no repetition. -/
theorem A_not_l (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ A) :
    v ∉ a :: m ++ [b] := by
  have h := hS.nodupH
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at h
  obtain ⟨ha, -, hbm, hd⟩ := h
  intro hl
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | hl | rfl
  · exact ha (List.mem_append_left _ hv)
  · exact hd v hv v (by simp [hl]) rfl
  · exact hd v hv v (by simp) rfl

theorem B_not_l (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ B) :
    v ∉ a :: m ++ [b] := by
  have h := hS.nodupK
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at h
  obtain ⟨hb, -, -, hd⟩ := h
  intro hl
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | hl | rfl
  · exact hd v hv v (by simp) rfl
  · exact hd v hv v (by simp [hl]) rfl
  · exact hb (List.mem_append_left _ hv)

theorem m_not_C (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ m) : v ∉ C := by
  have h := hS.nodupH
  rw [List.cons_append, List.nodup_cons, List.nodup_append, List.nodup_cons] at h
  obtain ⟨ha, -, ⟨hb, -⟩, hd⟩ := h
  rw [hS.mem_C]
  rintro (rfl | hvA | rfl | hvB)
  · exact ha (by simp [hv])
  · exact hd v hvA v (by simp [hv]) rfl
  · exact hb (by simp [hv])
  · exact hS.B_not_l hvB (by simp [hv])

theorem B_not_S₁ (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ B) : v ∉ S₁ := fun h =>
  hS.B_not_l hv (hS.mem_l_of_inter h (hS.mem_S₂ (by simp [hv])))

theorem A_not_S₂ (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ A) : v ∉ S₂ := fun h =>
  hS.A_not_l hv (hS.mem_l_of_inter (hS.mem_S₁ (by simp [hv])) h)

/-- A vertex of `C` in `H` is on `C_H`. -/
theorem C_S₁ (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ C) (h₁ : v ∈ S₁) :
    v ∈ a :: A ++ b :: m.reverse := by
  rcases hS.mem_C.mp hv with rfl | hvA | rfl | hvB
  · simp
  · simp [hvA]
  · simp
  · exact absurd h₁ (hS.B_not_S₁ hvB)

/-- A vertex of `C` in `K` is on `C_K`. -/
theorem C_S₂ (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ C) (h₂ : v ∈ S₂) :
    v ∈ b :: B ++ a :: m := by
  rcases hS.mem_C.mp hv with rfl | hvA | rfl | hvB
  · simp
  · exact absurd h₂ (hS.A_not_S₂ hvA)
  · simp
  · simp [hvB]

/-- A vertex of `C` on `P` is an end of `P`. -/
theorem C_l (hS : Setting G S₁ S₂ a b m A B C k) {v : V} (hv : v ∈ C) (hl : v ∈ a :: m ++ [b]) :
    v = a ∨ v = b := by
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hl
  rcases hl with h | h | h
  · exact Or.inl h
  · exact absurd hv (hS.m_not_C h)
  · exact Or.inr h

/-- `P` read from `b` to `a`, `b m⁻¹ a`, is a path of `G`. -/
theorem lr_chain (hS : Setting G S₁ S₂ a b m A B C k) :
    (b :: m.reverse ++ [a]).IsChain G.Adj ∧ (b :: m.reverse ++ [a]).Nodup := by
  have hC := hS.cycH
  have hrot : (a :: A ++ b :: m.reverse).rotate (A.length + 1) =
      (b :: m.reverse ++ [a]) ++ A := by
    rw [show a :: A ++ b :: m.reverse = (a :: A) ++ (b :: m.reverse) by simp,
      show A.length + 1 = (a :: A).length by simp, List.rotate_append_length_eq]
    simp
  have hP := (hC.rotate (A.length + 1)).isPathList (R := univ) (fun _ _ => trivial)
  rw [hrot] at hP
  refine ⟨?_, hP.1.sublist (List.sublist_append_left _ _)⟩
  have := (hP.2.1.infix (List.infix_append [] _ A)).imp (fun _ _ h => (h : (restrict G S₁).Adj _ _).1)
  simpa using this

/-- `P = a m b` is a path of `G`. -/
theorem l_chain (hS : Setting G S₁ S₂ a b m A B C k) :
    (a :: m ++ [b]).IsChain G.Adj ∧ (a :: m ++ [b]).Nodup := by
  obtain ⟨h1, h2⟩ := hS.lr_chain
  have hr : (b :: m.reverse ++ [a]).reverse = a :: m ++ [b] := by simp
  refine ⟨?_, ?_⟩
  · rw [← hr, List.isChain_reverse]
    exact h1.imp fun _ _ h => h.symm
  · rw [← hr]
    exact List.nodup_reverse.mpr h2

/-- The paths of Claim 4.2 in `K`: from a vertex `z` of `K` to a vertex `d` of `B`. -/
theorem kpath (hS : Setting G S₁ S₂ a b m A B C k) {z : V} (hz : z ∈ S₂) :
    ∃ d ∈ B, ∃ P : List V, P.head? = some z ∧ P.getLast? = some d ∧ P.IsChain G.Adj ∧ P.Nodup ∧
      (∀ w ∈ P, w ∈ S₂) ∧ ∀ w ∈ P, w ∈ b :: B ++ a :: m → w = z ∨ w = d :=
  side_path hz (hS.claimK z hz)

/-- The paths of Claim 4.2 in `K` from a vertex `z` of `K - P`. -/
theorem kpath' (hS : Setting G S₁ S₂ a b m A B C k) {z : V} (hz : z ∈ S₂)
    (hzl : z ∉ a :: m ++ [b]) :
    ∃ d ∈ B, ∃ P : List V, P.head? = some z ∧ P.getLast? = some d ∧ P.IsChain G.Adj ∧ P.Nodup ∧
      (∀ w ∈ P, w ∈ S₂) ∧ ∀ w ∈ P, w ∈ b :: B ++ a :: m → w = d :=
  side_path' hz (hS.claimK z hz) fun hzD => by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff,
      or_false] at hzl hzD
    tauto

/-- The paths of Claim 4.2 in `H` from a vertex `t` of `H - P`. -/
theorem hpath' (hS : Setting G S₁ S₂ a b m A B C k) {t : V} (ht : t ∈ S₁)
    (htl : t ∉ a :: m ++ [b]) :
    ∃ c ∈ A, ∃ P : List V, P.head? = some t ∧ P.getLast? = some c ∧ P.IsChain G.Adj ∧ P.Nodup ∧
      (∀ w ∈ P, w ∈ S₁) ∧ ∀ w ∈ P, w ∈ a :: A ++ b :: m.reverse → w = c :=
  side_path' ht (hS.claimH t ht) fun htD => by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse,
      List.mem_nil_iff, or_false] at htl htD
    tauto

/-- The extension of a vertex `z` of `P` into `K`: a list `z :: T` to a vertex `d` of `B`, whose
other vertices are off `H` and meet `C` only in `d`. -/
theorem kext (hS : Setting G S₁ S₂ a b m A B C k) {z : V} (hz : z ∈ a :: m ++ [b]) :
    ∃ d ∈ B, ∃ T : List V, (z :: T).IsChain G.Adj ∧ (z :: T).Nodup ∧
      (z :: T).getLast? = some d ∧ (∀ w ∈ T, w ∉ S₁) ∧ ∀ w ∈ T, w ∈ C → w = d := by
  obtain ⟨d, hd, P, hh, hl, hP, hnd, hS₂, hin⟩ := hS.kpath (hS.l_S₂ hz)
  obtain ⟨T, rfl⟩ : ∃ T, P = z :: T := by
    match P, hh with
    | x :: T, hh => exact ⟨T, by rw [Option.some_injective _ hh]⟩
  have hzT : z ∉ T := (List.nodup_cons.mp hnd).1
  have hlK : ∀ w, w ∈ a :: m ++ [b] → w ∈ b :: B ++ a :: m := fun w hw => by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hw ⊢
    tauto
  refine ⟨d, hd, T, hP, hnd, hl, fun w hw hw₁ => ?_, fun w hw hwC => ?_⟩
  · have hwl := hS.mem_l_of_inter hw₁ (hS₂ w (List.mem_cons_of_mem _ hw))
    rcases hin w (List.mem_cons_of_mem _ hw) (hlK w hwl) with rfl | rfl
    · exact hzT hw
    · exact hS.B_not_l hd hwl
  · have hwK := hS.C_S₂ hwC (hS₂ w (List.mem_cons_of_mem _ hw))
    rcases hin w (List.mem_cons_of_mem _ hw) hwK with rfl | rfl
    · exact absurd hw hzT
    · rfl

/-- The same situation with `H` and `K` exchanged. -/
theorem symm (hS : Setting G S₁ S₂ a b m A B C k) :
    Setting G S₂ S₁ b a m.reverse B A C (k + (A.length + 1)) where
  inter := by
    rw [inter_comm, hS.inter]
    ext v
    simp only [mem_ofPred_eq, List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse,
      List.mem_nil_iff, or_false]
    tauto
  ind := fun u hu v hv h => by
    have hr : (a :: m ++ [b]).reverse = b :: m.reverse ++ [a] := by simp
    rw [← hr, List.mem_reverse] at hu hv
    rw [← hr]
    exact (hS.ind u hu v hv h).reverse
  cycH := by rw [List.reverse_reverse]; exact hS.cycK
  frameH := by rw [List.reverse_reverse]; exact hS.frameK
  claimH := by rw [List.reverse_reverse]; exact hS.claimK
  cycK := hS.cycH
  frameK := hS.frameH
  claimK := hS.claimH
  rot := by
    rw [← List.rotate_rotate, hS.rot,
      show a :: A ++ b :: B = (a :: A) ++ (b :: B) by simp,
      show A.length + 1 = (a :: A).length by simp, List.rotate_append_length_eq]
  neA := hS.neB
  neB := hS.neA

theorem l_D {v : V} (hv : v ∈ a :: m ++ [b]) : v ∈ a :: A ++ b :: m.reverse := by
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse, List.mem_nil_iff,
    or_false] at hv ⊢
  tauto

theorem A_D {v : V} (hv : v ∈ A) : v ∈ a :: A ++ b :: m.reverse := by
  simp [hv]

/-- The paths `lp` along which the proof extends: `P` read in either direction. -/
structure IsAlong (hS : Setting G S₁ S₂ a b m A B C k) (lp : List V) (e₀ e₁ : V) : Prop where
  chain : lp.IsChain G.Adj
  nodup : lp.Nodup
  mem : ∀ v, v ∈ lp ↔ v ∈ a :: m ++ [b]
  head : lp.head? = some e₀
  last : lp.getLast? = some e₁
  ends : e₀ = a ∧ e₁ = b ∨ e₀ = b ∧ e₁ = a
  ind : ∀ u ∈ lp, ∀ v ∈ lp, G.Adj u v → IsListEdge lp u v

theorem along_l (hS : Setting G S₁ S₂ a b m A B C k) : hS.IsAlong (a :: m ++ [b]) a b where
  chain := hS.l_chain.1
  nodup := hS.l_chain.2
  mem := fun _ => Iff.rfl
  head := rfl
  last := by rw [List.getLast?_append]; rfl
  ends := Or.inl ⟨rfl, rfl⟩
  ind := hS.ind

theorem IsAlong.reverse {hS : Setting G S₁ S₂ a b m A B C k} {lp : List V} {e₀ e₁ : V}
    (h : hS.IsAlong lp e₀ e₁) : hS.IsAlong lp.reverse e₁ e₀ where
  chain := List.isChain_reverse.mpr (h.chain.imp fun _ _ h => h.symm)
  nodup := List.nodup_reverse.mpr h.nodup
  mem := fun v => by rw [List.mem_reverse]; exact h.mem v
  head := by rw [List.head?_reverse]; exact h.last
  last := by rw [List.getLast?_reverse]; exact h.head
  ends := h.ends.elim (fun h' => Or.inr ⟨h'.2, h'.1⟩) (fun h' => Or.inl ⟨h'.2, h'.1⟩)
  ind := fun u hu v hv huv => by
    have := (h.ind u (List.mem_reverse.mp hu) v (List.mem_reverse.mp hv) huv).reverse
    exact this

/-- An inner entry of `lp` is not on `C`. -/
theorem IsAlong.not_C {hS : Setting G S₁ S₂ a b m A B C k} {lp : List V} {e₀ e₁ : V}
    (h : hS.IsAlong lp e₀ e₁) {q : ℕ} {w : V} (hw : lp[q]? = some w) (h0 : 0 < q)
    (h1 : q + 1 < lp.length) : w ∉ C := by
  intro hwC
  obtain ⟨hq, rfl⟩ := List.getElem?_eq_some_iff.mp hw
  have hwl := (h.mem _).mp (List.getElem_mem hq)
  have he₀ : lp[0]'(by omega) = e₀ := by
    have := h.head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at this
    exact Option.some_injective _ this
  have he₁ : lp[lp.length - 1]'(by omega) = e₁ := by
    have := h.last
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at this
    exact Option.some_injective _ this
  have hab : lp[q] = e₀ ∨ lp[q] = e₁ := by
    rcases hS.C_l hwC hwl with h' | h' <;> rcases h.ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  rcases hab with h' | h'
  · have := (h.nodup.getElem_inj_iff).mp (h'.trans he₀.symm)
    omega
  · have := (h.nodup.getElem_inj_iff).mp (h'.trans he₁.symm)
    omega

/-- **The fourth case of Figure 11.** `Xh` runs in `H` from a vertex `c` of `A` to the entry
`z₃ = lp[p₃]` of `P`, and `Y₀` runs in `H` between the entries `z₂ = lp[p₂]` and `z₄ = lp[p₄]`, with
`p₂ < p₃ < p₄`. Then `(P z₂ Y₀ z₄ P, Xh z₃ P')`, with `P'` a path of Claim 4.2 from `z₃` into `K`,
is a crossing of `C`: "the pair $(PxP_2yP,P_1zP')$ is a crossing of $C$ in $G+e$". -/
theorem case4 (hS : Setting G S₁ S₂ a b m A B C k) {x y : V} {lp : List V} {e₀ e₁ : V}
    (hlp : hS.IsAlong lp e₀ e₁) {p₂ p₃ p₄ : ℕ} (h23 : p₂ < p₃) (h34 : p₃ < p₄)
    (h4 : p₄ < lp.length) {c z₂ z₃ z₄ : V} (hz₂ : lp[p₂]? = some z₂) (hz₃ : lp[p₃]? = some z₃)
    (hz₄ : lp[p₄]? = some z₄) (hc : c ∈ A) {Xh Y₀ : List V}
    (hXc : Xh.IsChain (G ⊔ edge x y).Adj) (hXnd : Xh.Nodup) (hXh : Xh.head? = some c)
    (hXl : Xh.getLast? = some z₃) (hXS : ∀ w ∈ Xh, w ∈ S₁)
    (hXl' : ∀ w ∈ Xh, w ∈ a :: m ++ [b] → w = z₃) (hXC : ∀ w ∈ Xh, w ∈ C → w = c)
    (hYc : Y₀.IsChain (G ⊔ edge x y).Adj) (hYnd : Y₀.Nodup) (hYh : Y₀.head? = some z₂)
    (hYl : Y₀.getLast? = some z₄) (hYS : ∀ w ∈ Y₀, w ∈ S₁)
    (hYl' : ∀ w ∈ Y₀, w ∈ a :: m ++ [b] → w = z₂ ∨ w = z₄)
    (hYC : ∀ w ∈ Y₀, w ∈ C → w ∈ a :: m ++ [b]) (hdisj : Xh.Disjoint Y₀) :
    IsCrossed (G ⊔ edge x y) C := by
  have hle : G ≤ G ⊔ edge x y := le_sup_left
  have hz₃l : z₃ ∈ a :: m ++ [b] := (hlp.mem z₃).mp (List.mem_of_getElem? hz₃)
  obtain ⟨d, hd, T, hTc, hTnd, hTl, hTS, hTC⟩ := hS.kext hz₃l
  obtain ⟨hYc', hYnd', hYh', hYl'', hYm⟩ := splice (hlp.chain.imp fun _ _ h => hle h) hlp.nodup
    (by omega) h4 hz₂ hz₄ hYc hYnd hYh hYl (fun w hw hwl => hYl' w hw ((hlp.mem w).mp hwl))
  have hT : T ≠ [] := by
    rintro rfl
    have hzd : z₃ = d := by simpa using hTl
    exact hS.B_not_l hd (hzd ▸ hz₃l)
  have hXc' : (Xh ++ T).IsChain (G ⊔ edge x y).Adj :=
    isChain_append_of_last hXc hXl (hTc.imp fun _ _ h => hle h)
  have hXnd' : (Xh ++ T).Nodup := List.nodup_append.mpr ⟨hXnd, (List.nodup_cons.mp hTnd).2,
    fun u hu v hv huv => hTS v hv (huv ▸ hXS u hu)⟩
  have hXh' : (Xh ++ T).head? = some c := by rw [List.head?_append, hXh]; rfl
  have hXl'' : (Xh ++ T).getLast? = some d := by
    obtain ⟨t, T', rfl⟩ := List.exists_cons_of_ne_nil hT
    rw [List.getLast?_cons_cons] at hTl
    rw [List.getLast?_append, hTl]
    rfl
  have hXin : ∀ w ∈ Xh ++ T, w ∈ C → w = c ∨ w = d := fun w hw hwC => by
    rcases List.mem_append.mp hw with hw | hw
    · exact Or.inl (hXC w hw hwC)
    · exact Or.inr (hTC w hw hwC)
  have hYS' : ∀ w ∈ lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1), w ∈ S₁ := fun w hw => by
    rcases hYm w hw with h | ⟨q, hq, he, -⟩
    · exact hYS w h
    · exact hS.l_S₁ ((hlp.mem w).mp (he ▸ List.getElem_mem hq))
  have hdisj' : (Xh ++ T).Disjoint (lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1)) := by
    intro w hwX hwY
    rcases List.mem_append.mp hwX with hw | hw
    · rcases hYm w hwY with hw' | ⟨q, hq, he, hq'⟩
      · exact hdisj hw hw'
      · have hwz := hXl' w hw ((hlp.mem w).mp (he ▸ List.getElem_mem hq))
        obtain ⟨h3, hz₃'⟩ := List.getElem?_eq_some_iff.mp hz₃
        have : q = p₃ := (hlp.nodup.getElem_inj_iff).mp (he.trans (hwz.trans hz₃'.symm))
        omega
    · exact hTS w hw (hYS' w hwY)
  have hYin : ∀ w ∈ lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1), w ∈ C → w = a ∨ w = b :=
    fun w hw hwC => hS.C_l hwC (by
      rcases hYm w hw with h | ⟨q, hq, he, -⟩
      · exact hYC w h hwC
      · exact (hlp.mem w).mp (he ▸ List.getElem_mem hq))
  rw [hlp.head] at hYh'
  rw [hlp.last] at hYl''
  rcases hlp.ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact isCrossed_of_lists hS.rot hc hd hYc' hYnd' hYh' hYl'' hYin hXc' hXnd' hXh' hXl'' hXin
      hdisj'.symm
  · refine isCrossed_of_lists hS.rot hc hd
      (List.isChain_reverse.mpr (hYc'.imp fun _ _ h => h.symm)) (List.nodup_reverse.mpr hYnd')
      (by rw [List.head?_reverse]; exact hYl'') (by rw [List.getLast?_reverse]; exact hYh')
      (fun w hw hwC => hYin w (List.mem_reverse.mp hw) hwC) hXc' hXnd' hXh' hXl'' hXin
      (fun w hw hw' => hdisj' hw' (List.mem_reverse.mp hw))

/-- **Rerouting through `H` (the fifth case of Figure 11).** A path `Ph` of Claim 4.2 leaves the
path `P` at its inner vertex `u` for the last time and ends at `c ∈ A`. Following `Ph` back from `c`
to `u`, then `P` from `u` to its end `z`, gives a path `P' u P z` from `c` to `z`. -/
theorem reroute (hS : Setting G S₁ S₂ a b m A B C k) {x y : V} {P Y₀ α β : List V}
    {h₀ z u c : V} (hPc : P.IsChain (G ⊔ edge x y).Adj) (hPnd : P.Nodup)
    (hPh : P.head? = some h₀) (hPl : P.getLast? = some z) (hPS : ∀ w ∈ P, w ∈ S₁)
    (hPD : ∀ w ∈ P, w ∈ a :: A ++ b :: m.reverse → w = h₀ ∨ w = z)
    (hh₀ : h₀ ∈ a :: m ++ [b]) (hz : z ∈ a :: m ++ [b]) (hzC : z ∉ C)
    (hu : u ∈ P) (huD : u ∉ a :: A ++ b :: m.reverse) (huY : u ∉ Y₀) (hPY : P.Disjoint Y₀)
    (hPhc : (α ++ u :: β).IsChain G.Adj) (hPhnd : (α ++ u :: β).Nodup)
    (hPhl : (α ++ u :: β).getLast? = some c) (hPhS : ∀ w ∈ α ++ u :: β, w ∈ S₁)
    (hPhD : ∀ w ∈ α ++ u :: β, w ∈ a :: A ++ b :: m.reverse → w = c) (hc : c ∈ A)
    (hβ : ∀ w ∈ β, w ∉ P ∧ w ∉ Y₀) :
    ∃ Xh : List V, Xh.IsChain (G ⊔ edge x y).Adj ∧ Xh.Nodup ∧ Xh.head? = some c ∧
      Xh.getLast? = some z ∧ (∀ w ∈ Xh, w ∈ S₁) ∧ (∀ w ∈ Xh, w ∈ a :: m ++ [b] → w = z) ∧
      (∀ w ∈ Xh, w ∈ C → w = c) ∧ Xh.Disjoint Y₀ := by
  have hle : G ≤ G ⊔ edge x y := le_sup_left
  obtain ⟨γ, δ, rfl⟩ := List.append_of_mem hu
  have huδ : u ∉ δ := by
    have := hPnd
    rw [List.nodup_append, List.nodup_cons] at this
    exact this.2.1.1
  have hh₀δ : h₀ ∉ δ := by
    intro hh
    cases γ with
    | nil =>
      simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hPh
      exact huD (hPh ▸ l_D hh₀)
    | cons g γ =>
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hPh
      subst hPh
      have := hPnd
      rw [List.cons_append, List.nodup_cons] at this
      exact this.1 (by simp [hh])
  have hδ : δ ≠ [] := by
    rintro rfl
    rw [List.getLast?_append] at hPl
    simp only [List.getLast?_singleton, Option.some_or, Option.some.injEq] at hPl
    exact huD (hPl ▸ l_D hz)
  have huβ : (u :: β).IsChain G.Adj := hPhc.infix ⟨α, [], by simp⟩
  have huδc : (u :: δ).IsChain (G ⊔ edge x y).Adj :=
    hPc.infix ⟨γ, [], by simp⟩
  have hrc : ((u :: β).reverse).IsChain (G ⊔ edge x y).Adj :=
    List.isChain_reverse.mpr (huβ.imp fun _ _ h => (hle h).symm)
  have hrl : ((u :: β).reverse).getLast? = some u := by rw [List.getLast?_reverse]; rfl
  have hPhnd' : (u :: β).Nodup := hPhnd.sublist (List.sublist_append_right _ _)
  have hδnd : δ.Nodup := (hPnd.sublist (List.sublist_append_right _ _)).sublist
    (List.sublist_cons_self _ _)
  refine ⟨(u :: β).reverse ++ δ, isChain_append_of_last hrc hrl huδc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨List.nodup_reverse.mpr hPhnd', hδnd, fun w hw w' hw' hww => ?_⟩
    subst hww
    rcases List.mem_cons.mp (List.mem_reverse.mp hw) with rfl | hw
    · exact huδ hw'
    · exact (hβ w hw).1 (by simp [hw'])
  · rw [List.head?_append, List.head?_reverse]
    have : (u :: β).getLast? = some c := by
      rw [List.getLast?_append] at hPhl
      cases h : (u :: β).getLast? with
      | none => simp at h
      | some v => rw [h] at hPhl; exact hPhl
    rw [this]
    rfl
  · rw [List.getLast?_append]
    have : δ.getLast? = some z := by
      rw [List.getLast?_append] at hPl
      obtain ⟨t, δ', rfl⟩ := List.exists_cons_of_ne_nil hδ
      rw [List.getLast?_cons_cons] at hPl
      cases h : (t :: δ').getLast? with
      | none => simp at h
      | some v => rw [h] at hPl; exact hPl
    rw [this]
    rfl
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hPhS w (List.mem_append_right _ (List.mem_reverse.mp hw))
    · exact hPS w (by simp [hw])
  · intro w hw hwl
    rcases List.mem_append.mp hw with hw | hw
    · have := hPhD w (List.mem_append_right _ (List.mem_reverse.mp hw)) (l_D hwl)
      subst this
      exact absurd hwl (hS.A_not_l hc)
    · rcases hPD w (by simp [hw]) (l_D hwl) with rfl | rfl
      · exact absurd hw hh₀δ
      · rfl
  · intro w hw hwC
    rcases List.mem_append.mp hw with hw | hw
    · have hw' := List.mem_append_right α (List.mem_reverse.mp hw)
      exact hPhD w hw' (hS.C_S₁ hwC (hPhS w hw'))
    · have hwP : w ∈ γ ++ u :: δ := by simp [hw]
      rcases hPD w hwP (hS.C_S₁ hwC (hPS w hwP)) with rfl | rfl
      · exact absurd hw hh₀δ
      · exact absurd hwC hzC
  · intro w hw hwY
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_cons.mp (List.mem_reverse.mp hw) with rfl | hw
      · exact huY hwY
      · exact (hβ w hw).2 hwY
    · exact hPY (by simp [hw]) hwY

/-- A path whose vertices are all among its two ends is one edge. -/
theorem adj_of_ends {R : V → V → Prop} {P : List V} {u v : V} (hc : P.IsChain R) (hnd : P.Nodup)
    (hh : P.head? = some u) (hl : P.getLast? = some v) (huv : u ≠ v)
    (hall : ∀ w ∈ P, w = u ∨ w = v) : R u v := by
  match P, hh, hl with
  | [w], hh, hl =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hh hl
    exact absurd (hh.symm.trans hl) huv
  | w :: w' :: P', hh, hl =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hw' : w' = v := by
      rcases hall w' (by simp) with h | h
      · exact absurd (h ▸ (List.nodup_cons.mp hnd).1) (by simp)
      · exact h
    subst hw'
    exact (List.isChain_cons_cons.mp hc).1

/-- Two entries of `lp` at positions at least two apart are not adjacent in `G + xy`, unless they
are `x` and `y`. -/
theorem IsAlong.edge {hS : Setting G S₁ S₂ a b m A B C k} {lp : List V} {e₀ e₁ : V}
    (hlp : hS.IsAlong lp e₀ e₁) {x y : V} {p q : ℕ} (hpq : p + 1 < q) (hq : q < lp.length)
    (h : (G ⊔ edge x y).Adj lp[p] lp[q]) : lp[p] = x ∧ lp[q] = y ∨ lp[p] = y ∧ lp[q] = x := by
  classical
  rcases (sup_adj _ _ _ _).mp h with h | h
  · have := (hlp.ind _ (List.getElem_mem _) _ (List.getElem_mem _) h).idxOf hlp.nodup
    rw [hlp.nodup.idxOf_getElem, hlp.nodup.idxOf_getElem] at this
    omega
  · exact ((edge_adj _ _ _ _).mp h).1

/-- **The fifth case of Figure 11** (and the cases where all four ends of the crossing of `C_H` are
on `P`). `P₁` runs in `H` between the entries `lp[p₁]` and `lp[p₃]` of `P`, and `P₂` between `lp[p₂]`
and `lp[p₄]`, with `p₁ < p₂ < p₃ < p₄`. "we first observe that $P_1$ and $P_2$ cannot be reduced to
edges as $P$ is induced": one of them has an inner vertex. A path of Claim 4.2 from it leaves
`P₁ ∪ P₂` for the last time at an inner vertex `u`; we then build the crossing of the fourth case
(`reroute`, `case4`). -/
theorem case5 (hS : Setting G S₁ S₂ a b m A B C k) {x y : V} {lp : List V} {e₀ e₁ : V}
    (hlp : hS.IsAlong lp e₀ e₁) {p₁ p₂ p₃ p₄ : ℕ} (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄)
    (h4 : p₄ < lp.length) {z₁ z₂ z₃ z₄ : V} (hz₁ : lp[p₁]? = some z₁) (hz₂ : lp[p₂]? = some z₂)
    (hz₃ : lp[p₃]? = some z₃) (hz₄ : lp[p₄]? = some z₄) {P₁ P₂ : List V}
    (h1c : P₁.IsChain (G ⊔ edge x y).Adj) (h1nd : P₁.Nodup) (h1h : P₁.head? = some z₁)
    (h1l : P₁.getLast? = some z₃) (h1S : ∀ w ∈ P₁, w ∈ S₁)
    (h1D : ∀ w ∈ P₁, w ∈ a :: A ++ b :: m.reverse → w = z₁ ∨ w = z₃)
    (h2c : P₂.IsChain (G ⊔ edge x y).Adj) (h2nd : P₂.Nodup) (h2h : P₂.head? = some z₂)
    (h2l : P₂.getLast? = some z₄) (h2S : ∀ w ∈ P₂, w ∈ S₁)
    (h2D : ∀ w ∈ P₂, w ∈ a :: A ++ b :: m.reverse → w = z₂ ∨ w = z₄)
    (hdisj : P₁.Disjoint P₂) : IsCrossed (G ⊔ edge x y) C := by
  have hl : ∀ {q : ℕ} {w : V}, lp[q]? = some w → w ∈ a :: m ++ [b] := fun hw =>
    (hlp.mem _).mp (List.mem_of_getElem? hw)
  obtain ⟨hp₁, rfl⟩ := List.getElem?_eq_some_iff.mp hz₁
  obtain ⟨hp₂, rfl⟩ := List.getElem?_eq_some_iff.mp hz₂
  obtain ⟨hp₃, rfl⟩ := List.getElem?_eq_some_iff.mp hz₃
  obtain ⟨hp₄, rfl⟩ := List.getElem?_eq_some_iff.mp hz₄
  have hinj : ∀ {q q' : ℕ} (hq : q < lp.length) (hq' : q' < lp.length), lp[q] = lp[q'] → q = q' :=
    fun hq hq' h => (hlp.nodup.getElem_inj_iff).mp h
  -- one of the two paths has an inner vertex
  obtain ⟨t, ht, htD⟩ : ∃ t, (t ∈ P₁ ∨ t ∈ P₂) ∧ t ∉ a :: A ++ b :: m.reverse := by
    by_contra hno
    push Not at hno
    have e13 := hlp.edge (by omega) hp₃ (adj_of_ends h1c h1nd h1h h1l
      (fun h => by have := hinj _ _ h; omega) (fun w hw => h1D w hw (hno w (Or.inl hw))))
    have e24 := hlp.edge (by omega) hp₄ (adj_of_ends h2c h2nd h2h h2l
      (fun h => by have := hinj _ _ h; omega) (fun w hw => h2D w hw (hno w (Or.inr hw))))
    rcases e13 with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;> rcases e24 with ⟨h2, -⟩ | ⟨h2, -⟩
    · have := hinj _ _ (h2.trans h1.symm); omega
    · have := hinj _ _ (h2.trans h3.symm); omega
    · have := hinj _ _ (h2.trans h3.symm); omega
    · have := hinj _ _ (h2.trans h1.symm); omega
  have htS : t ∈ S₁ := ht.elim (h1S t) (h2S t)
  obtain ⟨c, hc, Ph, hPhh, hPhl, hPhc, hPhnd, hPhS, hPhD⟩ := hS.hpath' htS (fun h => htD (l_D h))
  -- the last vertex of `Ph` on `P₁ ∪ P₂`
  obtain ⟨α, u, β, rfl, hu, hβ⟩ := exists_last_mem (Z := {w | w ∈ P₁ ∨ w ∈ P₂}) _
    ⟨t, List.mem_of_mem_head? hPhh, ht⟩
  have huD : u ∉ a :: A ++ b :: m.reverse := by
    intro huD
    have huc := hPhD u (by simp) huD
    subst huc
    have hul : u ∈ a :: m ++ [b] := by
      rcases hu with hu | hu
      · rcases h1D u hu huD with h | h <;> rw [h] <;> exact hl (List.getElem?_eq_getElem _)
      · rcases h2D u hu huD with h | h <;> rw [h] <;> exact hl (List.getElem?_eq_getElem _)
    exact hS.A_not_l hc hul
  have hβ' : ∀ w ∈ β, w ∉ P₁ ∧ w ∉ P₂ := fun w hw => by
    have := hβ w hw
    simp only [mem_ofPred_eq, not_or] at this
    exact this
  have hP2l : ∀ w ∈ P₂, w ∈ a :: m ++ [b] → w = lp[p₂] ∨ w = lp[p₄] :=
    fun w hw hwl => h2D w hw (l_D hwl)
  have hP2C : ∀ w ∈ P₂, w ∈ C → w ∈ a :: m ++ [b] := fun w hw hwC => by
    rcases h2D w hw (hS.C_S₁ hwC (h2S w hw)) with rfl | rfl <;>
      exact hl (List.getElem?_eq_getElem _)
  have hP1l : ∀ w ∈ P₁, w ∈ a :: m ++ [b] → w = lp[p₃] ∨ w = lp[p₁] :=
    fun w hw hwl => (h1D w hw (l_D hwl)).symm
  have hP1C : ∀ w ∈ P₁, w ∈ C → w ∈ a :: m ++ [b] := fun w hw hwC => by
    rcases h1D w hw (hS.C_S₁ hwC (h1S w hw)) with rfl | rfl <;>
      exact hl (List.getElem?_eq_getElem _)
  rcases hu with hu | hu
  · -- `u` is inside `P₁`: go from `c` to `u`, along `P₁` to `lp[p₃]`, then into `K`
    obtain ⟨Xh, hXc, hXnd, hXh, hXl, hXS, hXl', hXC, hXY⟩ := hS.reroute h1c h1nd h1h h1l h1S h1D
      (hl (List.getElem?_eq_getElem _)) (hl (List.getElem?_eq_getElem _))
      (hlp.not_C (List.getElem?_eq_getElem _) (by omega) (by omega)) hu huD
      (fun h => hdisj hu h) hdisj hPhc hPhnd hPhl hPhS hPhD hc
      (fun w hw => ⟨(hβ' w hw).1, (hβ' w hw).2⟩)
    exact hS.case4 hlp h23 h34 h4 (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _)
      (List.getElem?_eq_getElem _) hc hXc hXnd hXh hXl hXS hXl' hXC h2c h2nd h2h h2l h2S hP2l
      hP2C hXY
  · -- `u` is inside `P₂`: the same with `P` read backwards
    have hrev : ∀ {q : ℕ} (hq : q < lp.length), lp.reverse[lp.length - 1 - q]? = some lp[q] :=
      fun {q} hq => by
        rw [List.getElem?_reverse (by omega), show lp.length - 1 - (lp.length - 1 - q) = q by omega]
        exact List.getElem?_eq_getElem _
    obtain ⟨Xh, hXc, hXnd, hXh, hXl, hXS, hXl', hXC, hXY⟩ := hS.reroute (P := P₂.reverse)
      (Y₀ := P₁) (List.isChain_reverse.mpr (h2c.imp fun _ _ h => h.symm))
      (List.nodup_reverse.mpr h2nd) (by rw [List.head?_reverse]; exact h2l)
      (by rw [List.getLast?_reverse]; exact h2h) (fun w hw => h2S w (List.mem_reverse.mp hw))
      (fun w hw hwD => (h2D w (List.mem_reverse.mp hw) hwD).symm)
      (hl (List.getElem?_eq_getElem _)) (hl (List.getElem?_eq_getElem _))
      (hlp.not_C (List.getElem?_eq_getElem _) (by omega) (by omega)) (List.mem_reverse.mpr hu)
      huD (fun h => hdisj h hu) (fun w hw hw' => hdisj hw' (List.mem_reverse.mp hw)) hPhc hPhnd
      hPhl hPhS hPhD hc (fun w hw => ⟨fun h => (hβ' w hw).2 (List.mem_reverse.mp h),
        (hβ' w hw).1⟩)
    exact hS.case4 hlp.reverse (p₂ := lp.length - 1 - p₃) (p₃ := lp.length - 1 - p₂)
      (p₄ := lp.length - 1 - p₁) (by omega) (by omega) (by simp; omega) (hrev hp₃) (hrev hp₂)
      (hrev hp₁) hc hXc hXnd hXh hXl hXS hXl' hXC
      (List.isChain_reverse.mpr (h1c.imp fun _ _ h => h.symm)) (List.nodup_reverse.mpr h1nd)
      (by rw [List.head?_reverse]; exact h1l) (by rw [List.getLast?_reverse]; exact h1h)
      (fun w hw => h1S w (List.mem_reverse.mp hw))
      (fun w hw hwl => hP1l w (List.mem_reverse.mp hw) hwl)
      (fun w hw hwC => hP1C w (List.mem_reverse.mp hw) hwC)
      (fun w hw hw' => hXY hw (List.mem_reverse.mp hw'))

/-- The vertices of a walk of `H + xy` that starts in `H` are in `H`. -/
theorem support_S₁ {x y : V} (hx : x ∈ S₁) (hy : y ∈ S₁) :
    ∀ {u v : V} (W : (restrict G S₁ ⊔ edge x y).Walk u v), u ∈ S₁ → ∀ w ∈ W.support, w ∈ S₁
  | _, _, .nil, hu, w, hw => by simp at hw; rw [hw]; exact hu
  | _, _, .cons h p, hu, w, hw => by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hu
    · refine support_S₁ hx hy p ?_ w hw
      rcases (sup_adj _ _ _ _).mp h with h | h
      · exact h.2.2
      · rcases ((edge_adj _ _ _ _).mp h).1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption

/-- The lists of the paths of a crossing of `C_H` in `H + xy`. -/
theorem walk_facts (hS : Setting G S₁ S₂ a b m A B C k) {x y : V} (hx : x ∈ S₁) (hy : y ∈ S₁)
    {u v : V} (W : (restrict G S₁ ⊔ edge x y).Walk u v)
    (hW : IsTPath (restrict G S₁ ⊔ edge x y) (a :: A ++ b :: m.reverse) W) :
    W.support.IsChain (G ⊔ edge x y).Adj ∧ W.support.Nodup ∧ W.support.head? = some u ∧
      W.support.getLast? = some v ∧ (∀ w ∈ W.support, w ∈ S₁) ∧
      ∀ w ∈ W.support, w ∈ a :: A ++ b :: m.reverse → w = u ∨ w = v := by
  have hle : restrict G S₁ ⊔ edge x y ≤ G ⊔ edge x y := sup_le_sup_right (restrict_le G S₁) _
  refine ⟨?_, (Walk.isPath_def W).mp hW.1, by rw [← Walk.cons_tail_support]; rfl,
    by rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support],
    support_S₁ hx hy W (hS.mem_S₁ hW.2.1), fun w hw hwD => ?_⟩
  · have := (W.mapLe hle).isChain_adj_support
    rwa [support_mapLe] at this
  · by_contra hne
    push Not at hne
    exact (hW.2.2.2 w hw hne.1 hne.2).1 hwD

/-- **The case analysis of Figure 11.** If the new edge `xy` lies in `H`, a crossing of `C_H` in
`H + xy` extends to a crossing of `C` in `G + xy`. We sort the crossing `(P₁, P₂)` by the positions
of its ends on `C_H = a A b m⁻¹`: at most the last few of the four ends are in `m`. -/
theorem cross_of_side (hS : Setting G S₁ S₂ a b m A B C k) {x y : V} (hx : x ∈ S₁) (hy : y ∈ S₁)
    (hc : IsCrossed (restrict G S₁ ⊔ edge x y) (a :: A ++ b :: m.reverse)) :
    IsCrossed (G ⊔ edge x y) C := by
  have hle : G ≤ G ⊔ edge x y := le_sup_left
  obtain ⟨u₁, v₁, u₂, v₂, Q, R, ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisj⟩ := hc
  obtain ⟨hQc, hQnd, hQh, hQl, hQS, hQD⟩ := hS.walk_facts hx hy Q hQ
  obtain ⟨hRc, hRnd, hRh, hRl, hRS, hRD⟩ := hS.walk_facts hx hy R hR
  -- positions on `C_H`, on the target `a A b B`, and on `P` read from `b` to `a`
  obtain ⟨n, hn⟩ : ∃ n, n = A.length := ⟨_, rfl⟩
  have hDlen : (a :: A ++ b :: m.reverse).length = n + 2 + m.length := by simp [hn]; omega
  have hsD : s < n + 2 + m.length := by
    rw [← hDlen]; exact (List.getElem?_eq_some_iff.mp hs).1
  have hlr := hS.along_l.reverse
  have hlrlen : (a :: m ++ [b]).reverse.length = m.length + 2 := by simp
  have hlr' : (a :: m ++ [b]).reverse = (b :: m.reverse) ++ [a] := by simp
  have hD1 : a :: A ++ b :: m.reverse = (a :: A) ++ (b :: m.reverse) := rfl
  have hD2 : a :: A ++ b :: m.reverse = (a :: A ++ [b]) ++ m.reverse := by simp
  have hT2 : a :: A ++ b :: B = (a :: A ++ [b]) ++ B := by simp
  have hlrD : ∀ {p : ℕ} {w : V}, n + 1 ≤ p → (a :: A ++ b :: m.reverse)[p]? = some w →
      (a :: m ++ [b]).reverse[p - (n + 1)]? = some w := fun {p w} hp hw => by
    have hpl : p < n + 2 + m.length := by rw [← hDlen]; exact (List.getElem?_eq_some_iff.mp hw).1
    have h1 : (a :: A).length ≤ p := by simp [hn] at hp ⊢; omega
    rw [hD1, List.getElem?_append_right h1] at hw
    have h2 : p - (n + 1) < (b :: m.reverse).length := by simp; omega
    rw [hlr', List.getElem?_append_left h2]
    have h3 : p - (a :: A).length = p - (n + 1) := by simp [hn]
    rwa [h3] at hw
  have hlra : (a :: m ++ [b]).reverse[m.length + 1]? = some a := by
    rw [hlr', List.getElem?_append_right (by simp)]
    simp
  have hlrb : (a :: m ++ [b]).reverse[0]? = some b := by simp
  have hDT : ∀ {p : ℕ}, p ≤ n + 1 →
      (a :: A ++ b :: m.reverse)[p]? = (a :: A ++ b :: B)[p]? := fun {p} hp => by
    have h1 : p < (a :: A ++ [b]).length := by simp [hn] at hp ⊢; omega
    rw [hD2, hT2, List.getElem?_append_left h1, List.getElem?_append_left h1]
  have hTB : ∀ q, (a :: A ++ b :: B)[n + 2 + q]? = B[q]? := fun q => by
    have h1 : (a :: A ++ [b]).length ≤ n + 2 + q := by simp [hn]
    rw [hT2, List.getElem?_append_right h1]
    congr 1
    simp [hn]
  have hTb : (a :: A ++ b :: B)[n + 1]? = some b := by
    have h1 : (a :: A).length ≤ n + 1 := by simp [hn]
    rw [show a :: A ++ b :: B = (a :: A) ++ (b :: B) from rfl, List.getElem?_append_right h1]
    simp [hn]
  have hTlen : (a :: A ++ b :: B).length = n + 2 + B.length := by simp [hn]; omega
  have hDA : ∀ {p : ℕ} {w : V}, 1 ≤ p → p ≤ n → (a :: A ++ b :: m.reverse)[p]? = some w →
      w ∈ A := fun {p w} h1 h2 hw => by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [List.cons_append, List.getElem?_cons_succ,
      List.getElem?_append_left (show p' < A.length by omega)] at hw
    exact List.mem_of_getElem? hw
  have hD0 : ∀ {w : V}, (a :: A ++ b :: m.reverse)[0]? = some w → w = a := fun hw => by
    simpa using hw.symm
  have hDb : ∀ {w : V}, (a :: A ++ b :: m.reverse)[n + 1]? = some w → w = b := fun {w} hw => by
    have h1 : (a :: A).length ≤ n + 1 := by simp [hn]
    rw [hD1, List.getElem?_append_right h1] at hw
    simpa [hn] using hw.symm
  have hlrl : ∀ {p : ℕ} {w : V}, n + 1 ≤ p → (a :: A ++ b :: m.reverse)[p]? = some w →
      w ∈ a :: m ++ [b] := fun hp hw =>
    (hlr.mem _).mp (List.mem_of_getElem? (hlrD hp hw))
  have hlrC : ∀ {p : ℕ} {w : V}, n + 2 ≤ p → (a :: A ++ b :: m.reverse)[p]? = some w → w ∉ C :=
    fun {p w} hp hw => by
      have hpl : p < n + 2 + m.length := by
        rw [← hDlen]; exact (List.getElem?_eq_some_iff.mp hw).1
      exact hlr.not_C (hlrD (by omega) hw) (by omega) (by rw [hlrlen]; omega)
  -- the facts of the reversed paths
  have hQc' := List.isChain_reverse.mpr (hQc.imp fun _ _ h => h.symm)
  have hQnd' := List.nodup_reverse.mpr hQnd
  have hQh' : Q.support.reverse.head? = some v₁ := by rw [List.head?_reverse]; exact hQl
  have hQl' : Q.support.reverse.getLast? = some u₁ := by rw [List.getLast?_reverse]; exact hQh
  have hQS' : ∀ w ∈ Q.support.reverse, w ∈ S₁ := fun w hw => hQS w (List.mem_reverse.mp hw)
  have hQD' : ∀ w ∈ Q.support.reverse, w ∈ a :: A ++ b :: m.reverse → w = v₁ ∨ w = u₁ :=
    fun w hw hwD => (hQD w (List.mem_reverse.mp hw) hwD).symm
  have hdisj' : R.support.Disjoint Q.support.reverse := fun w hw hw' =>
    hdisj (List.mem_reverse.mp hw') hw
  -- inner conditions for paths into `C`
  have hCQ : ∀ w ∈ Q.support, w ∈ C → w = u₁ ∨ w = v₁ := fun w hw hwC =>
    hQD w hw (hS.C_S₁ hwC (hQS w hw))
  have hCR : ∀ w ∈ R.support, w ∈ C → w = u₂ ∨ w = v₂ := fun w hw hwC =>
    hRD w hw (hS.C_S₁ hwC (hRS w hw))
  rcases (by omega : s ≤ n + 1 ∨ (j ≤ n + 1 ∧ n + 2 ≤ s) ∨ (r ≤ n + 1 ∧ n + 2 ≤ j) ∨
      (i ≤ n + 1 ∧ n + 2 ≤ r) ∨ n + 2 ≤ i) with h | ⟨hj', hs'⟩ | ⟨hr', hj'⟩ | ⟨hi', hr'⟩ | hi'
  · -- first case: no end in `m`
    refine isCrossed_of_lists_idx hS.rot hir hrj hjs (by omega) hQc hQnd (by rw [hQh, ← hi, hDT (by omega)])
      (by rw [hQl, ← hj, hDT (by omega)]) (fun w hw hwC => ?_) hRc hRnd
      (by rw [hRh, ← hr, hDT (by omega)]) (by rw [hRl, ← hs, hDT h]) (fun w hw hwC => ?_) hdisj
    · rcases hCQ w hw hwC with rfl | rfl
      · exact Or.inl hQh
      · exact Or.inr hQl
    · rcases hCR w hw hwC with rfl | rfl
      · exact Or.inl hRh
      · exact Or.inr hRl
  · -- second case: the end `v₂` of `R` is in `m`; extend `R` into `K`
    obtain ⟨d, hd, T, hTc, hTnd, hTl, hTS, hTC⟩ := hS.kext (hlrl (by omega) hs)
    obtain ⟨qd, hqd, rfl⟩ := List.getElem_of_mem hd
    have hT : T ≠ [] := by
      rintro rfl
      have hzd : v₂ = B[qd] := by simpa using hTl
      exact hS.B_not_l hd (hzd ▸ hlrl (by omega) hs)
    refine isCrossed_of_lists_idx hS.rot (s := n + 2 + qd) hir hrj (by omega) (by omega) hQc hQnd
      (by rw [hQh, ← hi, hDT (by omega)]) (by rw [hQl, ← hj, hDT (by omega)])
      (fun w hw hwC => ?_) (isChain_append_of_last hRc hRl (hTc.imp fun _ _ h => hle h))
      (List.nodup_append.mpr ⟨hRnd, (List.nodup_cons.mp hTnd).2,
        fun u hu v hv huv => hTS v hv (huv ▸ hRS u hu)⟩)
      (by rw [List.head?_append, hRh, Option.some_or, ← hr, hDT (by omega)]) ?_ (fun w hw hwC => ?_) ?_
    · rcases hCQ w hw hwC with rfl | rfl
      · exact Or.inl hQh
      · exact Or.inr hQl
    · obtain ⟨t, T', rfl⟩ := List.exists_cons_of_ne_nil hT
      rw [List.getLast?_cons_cons] at hTl
      rw [List.getLast?_append, hTl, hTB, List.getElem?_eq_getElem hqd]
      rfl
    · have hl' : (R.support ++ T).getLast? = some B[qd] := by
        obtain ⟨t, T', rfl⟩ := List.exists_cons_of_ne_nil hT
        rw [List.getLast?_cons_cons] at hTl
        rw [List.getLast?_append, hTl]
        rfl
      rcases List.mem_append.mp hw with hw | hw
      · rcases hCR w hw hwC with rfl | rfl
        · left; rw [List.head?_append, hRh]; rfl
        · exact absurd hwC (hlrC (by omega) hs)
      · right; rw [hl', hTC w hw hwC]
    · intro w hw hw'
      rcases List.mem_append.mp hw' with hw' | hw'
      · exact hdisj hw hw'
      · exact hTS w hw' (hQS w hw)
  · -- third case: `v₁` and `v₂` are in `m`
    have hv₁ := hlrD (by omega) hj
    have hv₂ := hlrD (by omega) hs
    rcases (by omega : r ≤ n ∨ r = n + 1) with hr'' | hr''
    · have hu₂ : u₂ ∈ A := hDA (by omega) hr'' hr
      have hRl' : ∀ w ∈ R.support, w ∈ a :: m ++ [b] → w = v₂ := fun w hw hwl => by
        rcases hRD w hw (l_D hwl) with rfl | rfl
        · exact absurd hwl (hS.A_not_l hu₂)
        · rfl
      have hRC : ∀ w ∈ R.support, w ∈ C → w = u₂ := fun w hw hwC => by
        rcases hCR w hw hwC with rfl | rfl
        · rfl
        · exact absurd hwC (hlrC (by omega) hs)
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · -- `u₁ = a`: the fourth case with the roles of the paths exchanged
        subst hi0
        have hu₁ := hD0 hi
        subst hu₁
        exact hS.case4 hlr (p₂ := j - (n + 1)) (p₃ := s - (n + 1)) (p₄ := m.length + 1)
          (by omega) (by omega) (by rw [hlrlen]; omega) hv₁ hv₂ hlra hu₂ hRc hRnd hRh hRl hRS hRl'
          hRC hQc' hQnd' hQh' hQl' hQS' (fun w hw hwl => hQD' w hw (l_D hwl))
          (fun w hw hwC => by
            rcases hQD' w hw (hS.C_S₁ hwC (hQS' w hw)) with rfl | rfl
            · exact hlrl (by omega) hj
            · simp)
          hdisj'
      · -- `u₁` and `u₂` are in `A`: extend `Q` to `b` and `R` into `K`
        have hu₁ : u₁ ∈ A := hDA hi0 (by omega) hi
        obtain ⟨hEc, hEnd, hEh, hEl, hEm⟩ := extend_start (fun _ _ h => h.symm)
          (hlr.chain.imp fun _ _ h => hle h) hlr.nodup (p := j - (n + 1)) (by rw [hlrlen]; omega)
          hv₁ hQc hQnd hQl (fun w hw hwl => by
            rcases hQD w hw (l_D ((hlr.mem w).mp hwl)) with rfl | rfl
            · exact absurd ((hlr.mem _).mp hwl) (hS.A_not_l hu₁)
            · rfl)
        rw [hlr.head] at hEl
        obtain ⟨d, hd, T, hTc, hTnd, hTl, hTS, hTC⟩ := hS.kext (hlrl (by omega) hs)
        obtain ⟨qd, hqd, rfl⟩ := List.getElem_of_mem hd
        have hT : T ≠ [] := by
          rintro rfl
          have hzd : v₂ = B[qd] := by simpa using hTl
          exact hS.B_not_l hd (hzd ▸ hlrl (by omega) hs)
        have hYl : (R.support ++ T).getLast? = some B[qd] := by
          obtain ⟨t, T', rfl⟩ := List.exists_cons_of_ne_nil hT
          rw [List.getLast?_cons_cons] at hTl
          rw [List.getLast?_append, hTl]
          rfl
        have hlrS : ∀ {w : V} {q : ℕ} (hq : q < (a :: m ++ [b]).reverse.length),
            (a :: m ++ [b]).reverse[q] = w → w ∈ S₁ := fun hq he =>
          hS.l_S₁ ((hlr.mem _).mp (he ▸ List.getElem_mem hq))
        refine isCrossed_of_lists_idx hS.rot (i := i) (r := r) (j := n + 1) (s := n + 2 + qd)
          hir (by omega) (by omega) (by omega) hEc hEnd
          (by rw [hEh, hQh, ← hi, hDT (by omega)]) (by rw [hEl, hTb])
          (fun w hw hwC => ?_) (isChain_append_of_last hRc hRl (hTc.imp fun _ _ h => hle h))
          (List.nodup_append.mpr ⟨hRnd, (List.nodup_cons.mp hTnd).2,
            fun u hu v hv huv => hTS v hv (huv ▸ hRS u hu)⟩)
          (by rw [List.head?_append, hRh, Option.some_or, ← hr, hDT (by omega)])
          (by rw [hYl, hTB, List.getElem?_eq_getElem hqd]) (fun w hw hwC => ?_) ?_
        · rcases hEm w hw with hw | ⟨q, hq, rfl, hlt⟩
          · rcases hCQ w hw hwC with rfl | rfl
            · left; rw [hEh, hQh]
            · exact absurd hwC (hlrC (by omega) hj)
          · right
            rw [hEl]
            rcases hS.C_l hwC ((hlr.mem _).mp (List.getElem_mem hq)) with h | h
            · exfalso
              obtain ⟨ha0, ha'⟩ := List.getElem?_eq_some_iff.mp hlra
              have := (hlr.nodup.getElem_inj_iff).mp (h.trans ha'.symm)
              omega
            · rw [h]
        · rcases List.mem_append.mp hw with hw | hw
          · rcases hCR w hw hwC with rfl | rfl
            · left; rw [List.head?_append, hRh]; rfl
            · exact absurd hwC (hlrC (by omega) hs)
          · right; rw [hYl, hTC w hw hwC]
        · intro w hw hw'
          rcases List.mem_append.mp hw' with hw' | hw'
          · rcases hEm w hw with hw | ⟨q, hq, rfl, hlt⟩
            · exact hdisj hw hw'
            · have h1 := hRl' _ hw' ((hlr.mem _).mp (List.getElem_mem hq))
              obtain ⟨h20, h2⟩ := List.getElem?_eq_some_iff.mp hv₂
              have := (hlr.nodup.getElem_inj_iff).mp (h1.trans h2.symm)
              omega
          · rcases hEm w hw with hw | ⟨q, hq, rfl, hlt⟩
            · exact hTS _ hw' (hQS _ hw)
            · exact hTS _ hw' (hlrS hq rfl)
    · subst hr''
      have hu₂ := hDb hr
      subst hu₂
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · -- all four ends on `P`
        subst hi0
        have hu₁ := hD0 hi
        subst hu₁
        exact hS.case5 hlr (p₁ := 0) (p₂ := j - (n + 1)) (p₃ := s - (n + 1))
          (p₄ := m.length + 1) (by omega) (by omega) (by omega) (by rw [hlrlen]; omega) hlrb hv₁
          hv₂ hlra hRc hRnd hRh hRl hRS hRD hQc' hQnd' hQh' hQl' hQS' hQD' hdisj'
      · -- `u₁ ∈ A`, `R` starts at `b`: the fourth case
        have hu₁ : u₁ ∈ A := hDA hi0 (by omega) hi
        exact hS.case4 hlr (p₂ := 0) (p₃ := j - (n + 1)) (p₄ := s - (n + 1)) (by omega)
          (by omega) (by rw [hlrlen]; omega) hlrb hv₁ hv₂ hu₁ hQc hQnd hQh hQl hQS
          (fun w hw hwl => by
            rcases hQD w hw (l_D hwl) with rfl | rfl
            · exact absurd hwl (hS.A_not_l hu₁)
            · rfl)
          (fun w hw hwC => by
            rcases hCQ w hw hwC with rfl | rfl
            · rfl
            · exact absurd hwC (hlrC (by omega) hj))
          hRc hRnd hRh hRl hRS (fun w hw hwl => hRD w hw (l_D hwl))
          (fun w hw hwC => by
            rcases hCR w hw hwC with rfl | rfl
            · simp
            · exact hlrl (by omega) hs)
          hdisj
  · -- fourth case: `u₂`, `v₁`, `v₂` are in `m`
    have hu₂ := hlrD (by omega) hr
    have hv₁ := hlrD (by omega) hj
    have hv₂ := hlrD (by omega) hs
    rcases (by omega : i = 0 ∨ (1 ≤ i ∧ i ≤ n) ∨ i = n + 1) with hi0 | ⟨hi1, hi2⟩ | hi0
    · subst hi0
      have hu₁ := hD0 hi
      subst hu₁
      exact hS.case5 hlr (p₁ := r - (n + 1)) (p₂ := j - (n + 1)) (p₃ := s - (n + 1))
        (p₄ := m.length + 1) (by omega) (by omega) (by omega) (by rw [hlrlen]; omega) hu₂ hv₁
        hv₂ hlra hRc hRnd hRh hRl hRS hRD hQc' hQnd' hQh' hQl' hQS' hQD' hdisj'
    · have hu₁ : u₁ ∈ A := hDA hi1 hi2 hi
      exact hS.case4 hlr (p₂ := r - (n + 1)) (p₃ := j - (n + 1)) (p₄ := s - (n + 1)) (by omega)
        (by omega) (by rw [hlrlen]; omega) hu₂ hv₁ hv₂ hu₁ hQc hQnd hQh hQl hQS
        (fun w hw hwl => by
          rcases hQD w hw (l_D hwl) with rfl | rfl
          · exact absurd hwl (hS.A_not_l hu₁)
          · rfl)
        (fun w hw hwC => by
          rcases hCQ w hw hwC with rfl | rfl
          · rfl
          · exact absurd hwC (hlrC (by omega) hj))
        hRc hRnd hRh hRl hRS (fun w hw hwl => hRD w hw (l_D hwl))
        (fun w hw hwC => by
          rcases hCR w hw hwC with rfl | rfl
          · exact hlrl (by omega) hr
          · exact hlrl (by omega) hs)
        hdisj
    · subst hi0
      have hu₁ := hDb hi
      subst hu₁
      exact hS.case5 hlr (p₁ := 0) (p₂ := r - (n + 1)) (p₃ := j - (n + 1)) (p₄ := s - (n + 1))
        (by omega) (by omega) (by omega) (by rw [hlrlen]; omega) hlrb hu₂ hv₁ hv₂ hQc hQnd hQh
        hQl hQS hQD hRc hRnd hRh hRl hRS hRD hdisj
  · -- fifth case: all four ends in `m`
    exact hS.case5 hlr (p₁ := i - (n + 1)) (p₂ := r - (n + 1)) (p₃ := j - (n + 1))
      (p₄ := s - (n + 1)) (by omega) (by omega) (by omega) (by rw [hlrlen]; omega)
      (hlrD (by omega) hi) (hlrD (by omega) hr) (hlrD (by omega) hj) (hlrD (by omega) hs) hQc hQnd
      hQh hQl hQS hQD hRc hRnd hRh hRl hRS hRD hdisj

/-- **The first case of the proof.** "Assume that $x$ and $y$ are in $H-P$ and $K-P$,
respectively. As $x$ is $C_H$-connected to $C_H-P$ in $H$ and $y$ is $C_K$-connected to $C_K-P$ in
$K$, we can assume to have an $x$-$(C_H-P)$ (resp. $y$-$(C_K-P)$) path $P_x$ in $H$ (resp. $P_y$ in
$K$) disjoint from $P$. The pair $(P_xeP_y,P)$ is a crossing of $C$ in $G+e$." -/
theorem cross_two_sides (hS : Setting G S₁ S₂ a b m A B C k) {x y : V} (hx : x ∈ S₁)
    (hxl : x ∉ a :: m ++ [b]) (hy : y ∈ S₂) (hyl : y ∉ a :: m ++ [b]) :
    IsCrossed (G ⊔ edge x y) C := by
  have hle : G ≤ G ⊔ edge x y := le_sup_left
  obtain ⟨c, hc, Px, hPxh, hPxl, hPxc, hPxnd, hPxS, hPxD⟩ := hS.hpath' hx hxl
  obtain ⟨d, hd, Py, hPyh, hPyl, hPyc, hPynd, hPyS, hPyK⟩ := hS.kpath' hy hyl
  have hxy : x ≠ y := fun h => hxl (hS.mem_l_of_inter hx (h ▸ hy))
  have hlK : ∀ w, w ∈ a :: m ++ [b] → w ∈ b :: B ++ a :: m := fun w hw => by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff,
      or_false] at hw ⊢
    tauto
  have hPxl' : ∀ w ∈ Px, w ∉ a :: m ++ [b] := fun w hw hwl => by
    have := hPxD w hw (l_D hwl)
    subst this
    exact hS.A_not_l hc hwl
  have hPyl' : ∀ w ∈ Py, w ∉ a :: m ++ [b] := fun w hw hwl => by
    have := hPyK w hw (hlK w hwl)
    subst this
    exact hS.B_not_l hd hwl
  have hXc : (Px.reverse ++ Py).IsChain (G ⊔ edge x y).Adj := by
    rw [List.isChain_append]
    refine ⟨List.isChain_reverse.mpr (hPxc.imp fun _ _ h => (hle h).symm),
      hPyc.imp fun _ _ h => hle h, fun u hu v hv => ?_⟩
    rw [List.getLast?_reverse, hPxh, Option.mem_some_iff] at hu
    rw [hPyh, Option.mem_some_iff] at hv
    subst hu hv
    exact (sup_adj _ _ _ _).mpr (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩))
  have hXnd : (Px.reverse ++ Py).Nodup := by
    rw [List.nodup_append]
    refine ⟨List.nodup_reverse.mpr hPxnd, hPynd, fun u hu v hv huv => ?_⟩
    subst huv
    rw [List.mem_reverse] at hu
    exact hPxl' u hu (hS.mem_l_of_inter (hPxS u hu) (hPyS u hv))
  have hXh : (Px.reverse ++ Py).head? = some c := by
    rw [List.head?_append, List.head?_reverse, hPxl]
    rfl
  have hXl : (Px.reverse ++ Py).getLast? = some d := by
    rw [List.getLast?_append, hPyl]
    rfl
  have hXin : ∀ w ∈ Px.reverse ++ Py, w ∈ C → w = c ∨ w = d := fun w hw hwC => by
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_reverse] at hw
      exact Or.inl (hPxD w hw (hS.C_S₁ hwC (hPxS w hw)))
    · exact Or.inr (hPyK w hw (hS.C_S₂ hwC (hPyS w hw)))
  refine isCrossed_of_lists hS.rot hc hd (hS.l_chain.1.imp fun _ _ h => hle h) hS.l_chain.2 rfl
    (by rw [List.getLast?_append]; rfl) (fun w hw hwC => hS.C_l hwC hw) hXc hXnd hXh hXl hXin
    (fun w hw hw' => ?_)
  rcases List.mem_append.mp hw' with hw' | hw'
  · exact hPxl' w (List.mem_reverse.mp hw') hw
  · exact hPyl' w hw' hw

end Setting

end

end GraphMinor.HP25

namespace GraphMinor.HP25

open SimpleGraph Set PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V}

public section

/-- **Lemma 4.1** (Humeau and Pous, page 12). "The frame of a web $G$ is crossed in all edge
extensions of $G$." Here `G` is a web on the vertex set `S` with frame `C`, and `xy` is a new edge
between two vertices of `S`. The graphs of the paper are finite, hence `[Finite V]`. -/
theorem lemma_4_1 [Finite V] {S : Set V} {C : List V} (h : IsWebOn G S C) {x y : V} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : x ≠ y) (hn : ¬ G.Adj x y) : IsCrossed (G ⊔ edge x y) C := by
  induction hN : S.ncard using Nat.strong_induction_on generalizing G S C x y with
  | _ N ih =>
  have hC : IsCycleList G C := by
    obtain ⟨-, -, -, -, ⟨hC, -⟩, -⟩ := h
    exact hC
  by_cases h4 : 4 ≤ C.length
  · -- "by Proposition 3.6, that $G$ is the web composition of two webs $H$ and $K$"
    obtain ⟨a', b', m', hnot, a, b, m, A, B, k, S₁, S₂, hl, hrot, -, hU, hI, -, hind, hH, hK⟩ :=
      prop_3_6 h h4
    have ha : a' = a := by simpa using congrArg List.head? hl
    have hb : b' = b := by
      have := congrArg List.getLast? hl
      rw [List.getLast?_append, List.getLast?_append] at this
      simpa using this
    subst ha hb
    have hnd : (a' :: A ++ b' :: B).Nodup := by rw [← hrot]; exact List.nodup_rotate.mpr hC.2.1
    have hAB : A ≠ [] ∧ B ≠ [] := by
      rw [← isCycleEdge_rotate C k, hrot, isCycleEdge_cons_append_cons_iff hnd] at hnot
      push Not at hnot
      exact hnot
    have hm : m' = m := by
      have := congrArg (fun l => l.tail.dropLast) hl
      simpa using this
    subst hm
    have hS : Setting G S₁ S₂ a' b' m' A B C k := Setting.of_webs hI hind hH hK hrot hAB.1 hAB.2
    have hK' : IsWebOn (restrict G S₂) S₂ (b' :: B ++ a' :: m'.reverse.reverse) := by
      rw [List.reverse_reverse]; exact hK
    have hS₁ : S₁ ⊆ S := fun v hv => hU ▸ Or.inl hv
    have hS₂ : S₂ ⊆ S := fun v hv => hU ▸ Or.inr hv
    obtain ⟨β, hβ⟩ := List.exists_mem_of_ne_nil B hAB.2
    obtain ⟨α, hα⟩ := List.exists_mem_of_ne_nil A hAB.1
    have hlt₁ : S₁.ncard < N := hN ▸ Set.ncard_lt_ncard
      ⟨hS₁, fun h' => hS.B_not_S₁ hβ (h' (hS₂ (hS.mem_S₂ (by simp [hβ]))))⟩
    have hlt₂ : S₂.ncard < N := hN ▸ Set.ncard_lt_ncard
      ⟨hS₂, fun h' => hS.A_not_S₂ hα (h' (hS₁ (hS.mem_S₁ (by simp [hα]))))⟩
    have hmem : ∀ v ∈ S, v ∈ S₁ ∨ v ∈ S₂ := fun v hv => by rw [← hU] at hv; exact hv
    have hlS₂ : ∀ v, v ∈ a' :: m' ++ [b'] → v ∈ S₂ := fun v hv => hS.l_S₂ hv
    have hlS₁ : ∀ v, v ∈ a' :: m' ++ [b'] → v ∈ S₁ := fun v hv => hS.l_S₁ hv
    by_cases hx₁ : x ∈ S₁ <;> by_cases hy₁ : y ∈ S₁
    · -- "Otherwise $e$ has both its endpoints in either $H$ or $K$, say in $H$."
      exact hS.cross_of_side hx₁ hy₁ (ih _ hlt₁ hH hx₁ hy₁ hxy (fun h' => hn h'.1) rfl)
    · have hy₂ : y ∈ S₂ := (hmem y hy).resolve_left hy₁
      by_cases hx₂ : x ∈ S₂
      · exact hS.symm.cross_of_side hx₂ hy₂
          (ih _ hlt₂ hK' hx₂ hy₂ hxy (fun h' => hn h'.1) rfl)
      · exact hS.cross_two_sides hx₁ (fun h' => hx₂ (hlS₂ x h')) hy₂ (fun h' => hy₁ (hlS₁ y h'))
    · have hx₂ : x ∈ S₂ := (hmem x hx).resolve_left hx₁
      by_cases hy₂ : y ∈ S₂
      · exact hS.symm.cross_of_side hx₂ hy₂
          (ih _ hlt₂ hK' hx₂ hy₂ hxy (fun h' => hn h'.1) rfl)
      · rw [edge_comm]
        exact hS.cross_two_sides hy₁ (fun h' => hy₂ (hlS₂ y h')) hx₂ (fun h' => hx₁ (hlS₁ x h'))
    · have hx₂ : x ∈ S₂ := (hmem x hx).resolve_left hx₁
      have hy₂ : y ∈ S₂ := (hmem y hy).resolve_left hy₁
      exact hS.symm.cross_of_side hx₂ hy₂
        (ih _ hlt₂ hK' hx₂ hy₂ hxy (fun h' => hn h'.1) rfl)
  · -- "Since $3$-webs are cliques (Proposition 2.2) they cannot be extended with a new edge."
    exfalso
    have h3 : C.length = 3 := by have := hC.1; omega
    match C, h3, h with
    | [c₀, c₁, c₂], _, h =>
      exact hn (((isWebOn_three_iff.mp h).2 x y).mpr ⟨hx, hy, hxy⟩)

/-- **Lemma 4.1** for webs on all the vertices: the frame of a web is crossed in every edge
extension. -/
theorem IsWeb.isCrossed_sup_edge [Finite V] {C : List V} (h : IsWeb G C) {x y : V} (hxy : x ≠ y)
    (hn : ¬ G.Adj x y) : IsCrossed (G ⊔ edge x y) C :=
  lemma_4_1 h (mem_univ x) (mem_univ y) hxy hn

/-- Webs are maximally crossless (Proposition 3.2 and Lemma 4.1): the direction from (iii) to (ii)
of Theorem 1.3. -/
theorem IsWeb.isMaximallyCrossless [Finite V] {C : List V} (h : IsWeb G C) :
    IsMaximallyCrossless G C :=
  ⟨h.not_isCrossed, fun _ _ hxy hn => h.isCrossed_sup_edge hxy hn⟩

end

end GraphMinor.HP25
