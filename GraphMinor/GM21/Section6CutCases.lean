module

public import GraphMinor.GM21.Section6CutSystem
public import GraphMinor.GM21.Section6CutHalves
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM21.Section6ClaimFourGap

/-!
# Graph Minors XXI, (6.3), claim (2): the two systems of pieces

Claim (2) of the proof of (6.3) (page 28 of the preprint) says "Let $a \in F_1^*, b \in F_2^*$
say. Let $F_1^*$ have ends $u_1, u_2$, and let $I_i \subseteq F_1^*$ be the support with ends
$u_1, a$." The print's $u_1$ is a misprint for $u_i$ (see the correction to the proof of (6.3) in
`corrections/GM21.md`). We give the
pieces of the supports in the two cases.

* `isPieceSystem_D`: `a` and `b` lie in different supports `F_{ja}*`, `F_{jb}*`. The pieces are
  the halves `A₋, A₊` of `F_{ja}*` at `a`, the halves `B₋, B₊` of `F_{jb}*` at `b`, and the other
  supports. This is the case of the paper.
* `isPieceSystem_S`: `a` and `b` lie in one support `F_{ja}*`. The paper's sentence does not cover
  this case (see the correction to the proof of (6.3) in `corrections/GM21.md`). The pieces are
  the half `A₋` at `a`, the piece `M` from `a` to `b`, the half `B₊` at `b`, and the other
  supports. A vertex of `μ(a) ∩ μ(b)` then has three copies, one in each of `μ(A₋)`, `μ(M)`,
  `μ(B₊)`.

The pieces are indexed by `Option (Option (Fin r))`: `none` and `some none` are the two new pieces,
and `some (some j)` is the piece that replaces `F_j*`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM21.Split

universe u v

variable {α : Type u} {β : Type v} {S : Type}

/-- The old supports, with `F_{ja}*` replaced by `Am` and `F_{jb}*` by `Bm`. -/
def oldPiece {r : ℕ} (F_star : Fin r → Set S) (ja jb : Fin r) (Am Bm : Set S) (j : Fin r) :
    Set S :=
  if j = ja then Am else if j = jb then Bm else F_star j

/-- The pieces when `a ∈ F_{ja}*` and `b ∈ F_{jb}*` with `ja ≠ jb`. -/
def piecesD {r : ℕ} (F_star : Fin r → Set S) (ja jb : Fin r) (Am Ap Bm Bp : Set S) :
    Option (Option (Fin r)) → Set S
  | none => Ap
  | some none => Bp
  | some (some j) => oldPiece F_star ja jb Am Bm j

/-- The support holding each piece, when `ja ≠ jb`. -/
def tauD {r : ℕ} (ja jb : Fin r) : Option (Option (Fin r)) → Fin r
  | none => ja
  | some none => jb
  | some (some j) => j

/-- The sides of the pieces, when `ja ≠ jb`: `A₊` is on the plus side at `a`, `B₊` on the plus
side at `b`. -/
def colD {r : ℕ} : Option (Option (Fin r)) → Bool × Bool
  | none => (true, false)
  | some none => (false, true)
  | some (some _) => (false, false)

/-- The pieces when `a, b ∈ F_{ja}*`: `M` from `a` to `b`, the half `Bp` at `b`, and `Am` in place
of `F_{ja}*`. -/
def piecesS {r : ℕ} (F_star : Fin r → Set S) (ja : Fin r) (Am M Bp : Set S) :
    Option (Option (Fin r)) → Set S
  | none => M
  | some none => Bp
  | some (some j) => oldPiece F_star ja ja Am Am j

/-- The support holding each piece, when `a, b ∈ F_{ja}*`. -/
def tauS {r : ℕ} (ja : Fin r) : Option (Option (Fin r)) → Fin r
  | none => ja
  | some none => ja
  | some (some j) => j

/-- The sides of the pieces, when `a, b ∈ F_{ja}*`: `M` is on the plus side at `a` and the minus
side at `b`, and `Bp` is on the plus side at both. -/
def colS {r : ℕ} : Option (Option (Fin r)) → Bool × Bool
  | none => (true, false)
  | some none => (true, true)
  | some (some _) => (false, false)

variable [TopologicalSpace S] {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

/-! ## Pieces of different supports -/

/-- The graph of a part of `F_j*` is a subgraph of `H_j`. -/
theorem supportGraph_le_H (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {P : Set S}
    {j : Fin r} (hPj : P ⊆ F_star j) : supportGraph G Γ μ P ≤ H j := by
  rw [hP.v2_eq j]
  exact GM21.supportGraph_mono hP j subset_rfl hPj

/-- Parts of different supports have disjoint graphs. -/
theorem vertex_notMem_of_ne (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {P A : Set S}
    {j k : Fin r} (hPj : P ⊆ F_star j) (hAk : A ⊆ F_star k) (hjk : j ≠ k) {v : α}
    (hv : v ∈ (supportGraph G Γ μ P).vertexSet) : v ∉ (supportGraph G Γ μ A).vertexSet :=
  fun hv' => disjoint_left.mp (hP.v1_disjoint hjk)
    ((supportGraph_le_H hP hPj).vertexSet_subset hv) ((supportGraph_le_H hP hAk).vertexSet_subset hv')

/-- Parts of different supports have no common edge. -/
theorem edge_notMem_of_ne (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (hG : G.IsGraph)
    {P A : Set S} {j k : Fin r} (hPj : P ⊆ F_star j) (hAk : A ⊆ F_star k) (hjk : j ≠ k) {e : β}
    (he : e ∈ (supportGraph G Γ μ P).edgeSet) : e ∉ (supportGraph G Γ μ A).edgeSet :=
  fun he' => disjoint_left.mp (ClaimFour.disjoint_edgeSet_H hP hG hjk)
    ((supportGraph_le_H hP hPj).edgeSet_subset he) ((supportGraph_le_H hP hAk).edgeSet_subset he')

/-- A vertex of `μ(x)` for a vertex `x` of `Γ` in `P` is a vertex of `μ(P)`. -/
theorem mem_supportGraph_of_vertex (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    {P : Set S} {j : Fin r} (hPj : P ⊆ F_star j) {x : S} (hx : x ∈ Γ.V ∩ P) {v : α}
    (hv : v ∈ (μ (.vertex x)).vertexSet) : v ∈ (supportGraph G Γ μ P).vertexSet :=
  (GM21.μ_vertex_le_supportGraph_of_subset hP j hPj hx).vertexSet_subset hv

/-- The vertices of `μ(x)` for `x ∈ F_j*` are vertices of `H_j`. -/
theorem μ_vertex_subset_H (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {j : Fin r} {x : S}
    (hx : x ∈ Γ.V ∩ F_star j) : (μ (.vertex x)).vertexSet ⊆ (H j).vertexSet :=
  (hP.μ_vertex_sub j x hx).1.vertexSet_subset

/-- A space inside the union of a support `A` and a set `B` lies in `A` or in `B`. -/
theorem space_subset_of_union (hS : IsSurface S) {s A B : Set S} {u w : S}
    (hs : s ∈ drawingSpaces Γ) (hA : SupportHasEnds Γ A u w) (hsAB : s ⊆ A ∪ B) :
    s ⊆ A ∨ s ⊆ B := by
  rcases GM21.Supports.space_subset_or_disjoint_of_supportHasEnds hS hs hA with h | h
  · exact Or.inl h.1
  · exact Or.inr fun x hx => (hsAB hx).resolve_left (disjoint_left.mp h hx)

/-! ## The case of two supports -/

/-- **The pieces when `a` and `b` lie in different supports.** -/
theorem isPieceSystem_D (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (hG : G.IsGraph)
    {a b : S} {ja jb : Fin r} (ha : a ∈ Γ.V ∩ F_star ja) (hb : b ∈ Γ.V ∩ F_star jb)
    (hj : ja ≠ jb) {Am Ap Bm Bp : Set S} (hHa : IsHalves Γ (F_star ja) Am Ap a)
    (hMa : HalvesMeetIn G Γ μ Am Ap a) (hHb : IsHalves Γ (F_star jb) Bm Bp b)
    (hMb : HalvesMeetIn G Γ μ Bm Bp b) :
    IsPieceSystem G Γ Γ_sub μ F_star a b false Ap Bp (piecesD F_star ja jb Am Ap Bm Bp)
      (tauD ja jb) colD := by
  have hS := hP.is_surface
  set P := piecesD F_star ja jb Am Ap Bm Bp with hPdef
  have hPa : P (some (some ja)) = Am := by simp [hPdef, piecesD, oldPiece]
  have hPb : P (some (some jb)) = Bm := by simp [hPdef, piecesD, oldPiece, hj.symm]
  have hPo : ∀ j, j ≠ ja → j ≠ jb → P (some (some j)) = F_star j := fun j h1 h2 => by
    simp [hPdef, piecesD, oldPiece, h1, h2]
  have hPn : P none = Ap := rfl
  have hPsn : P (some none) = Bp := rfl
  have hsub : ∀ i, P i ⊆ F_star (tauD ja jb i) := by
    rintro (_ | _ | j)
    · exact hHa.right_subset
    · exact hHb.right_subset
    · by_cases h1 : j = ja
      · rw [h1, hPa]
        exact hHa.left_subset
      by_cases h2 : j = jb
      · rw [h2, hPb]
        exact hHb.left_subset
      rw [hPo j h1 h2]
      rfl
  have hτ : ∀ i x j, x ∈ P i → x ∈ F_star j → tauD ja jb i = j := fun i x j hx hxj => by
    by_contra hne
    exact disjoint_left.mp (hP.supports_disjoint hne) (hsub i hx) hxj
  have hτa : ∀ i, tauD ja jb i = ja → i = none ∨ i = some (some ja) := by
    rintro (_ | _ | j) h
    · exact Or.inl rfl
    · exact absurd h hj.symm
    · exact Or.inr (by rw [show j = ja from h])
  have hτb : ∀ i, tauD ja jb i = jb → i = some none ∨ i = some (some jb) := by
    rintro (_ | _ | j) h
    · exact absurd h hj
    · exact Or.inl rfl
    · exact Or.inr (by rw [show j = jb from h])
  have haP : ∀ i, a ∈ P i → i = none ∨ i = some (some ja) := fun i hi => hτa i (hτ i a ja hi ha.2)
  have hbP : ∀ i, b ∈ P i → i = some none ∨ i = some (some jb) := fun i hi =>
    hτb i (hτ i b jb hi hb.2)
  have hpair : ∀ i i', i ≠ i' → tauD ja jb i = tauD ja jb i' →
      (i = some (some ja) ∧ i' = none) ∨ (i = none ∧ i' = some (some ja)) ∨
        (i = some (some jb) ∧ i' = some none) ∨ (i = some none ∧ i' = some (some jb)) := by
    intro i i' hii h
    rcases i with _ | _ | j
    · rcases hτa i' h.symm with rfl | rfl
      · exact absurd rfl hii
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hτb i' h.symm with rfl | rfl
      · exact absurd rfl hii
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · rcases i' with _ | _ | j'
      · exact Or.inl ⟨by rw [show j = ja from h], rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by rw [show j = jb from h], rfl⟩))
      · exact absurd (by rw [show j = j' from h]) hii
  have haA : a ∈ Γ.V ∩ Am := ⟨ha.1, hHa.mem_left⟩
  have haA' : a ∈ Γ.V ∩ Ap := ⟨ha.1, hHa.mem_right⟩
  have hbB : b ∈ Γ.V ∩ Bm := ⟨hb.1, hHb.mem_left⟩
  have hbB' : b ∈ Γ.V ∩ Bp := ⟨hb.1, hHb.mem_right⟩
  have hab_disj : ∀ v, v ∈ (μ (.vertex a)).vertexSet → v ∉ (μ (.vertex b)).vertexSet :=
    fun v hva hvb => disjoint_left.mp (hP.v1_disjoint hj) (μ_vertex_subset_H hP ha hva)
      (μ_vertex_subset_H hP hb hvb)
  refine
    { sup := ?_, sub := hsub, inter := ?_, notBoth := ?_, diffA := ?_, diffB := ?_,
      bothA := ?_, bothB := ?_, coverV := ?_, coverS := ?_, colA := ?_, colB := ?_,
      cover := ?_, disj := ?_ }
  · -- Each piece is a support, and holds `a` or `b` only as an end.
    have hends : ∀ i, ∀ {x u w : S}, SupportHasEnds Γ (P i) u w → (a ∈ P i → a = u ∨ a = w) →
        (b ∈ P i → b = u ∨ b = w) → ∃ u w, SupportHasEnds Γ (P i) u w ∧ P i ∩ {a, b} ⊆ {u, w} :=
      fun i _ u w hs h1 h2 => ⟨u, w, hs, fun y ⟨hy, hy'⟩ => by
        rcases hy' with rfl | rfl
        · exact h1 hy
        · exact h2 hy⟩
    rintro (_ | _ | j)
    · obtain ⟨w, hw⟩ := hHa.right
      exact hends none (x := a) hw (fun _ => Or.inl rfl) fun hbi => absurd (hτ none b jb hbi hb.2) hj
    · obtain ⟨w, hw⟩ := hHb.right
      exact hends (some none) (x := a) hw (fun hai => absurd (hτ _ a ja hai ha.2) hj.symm)
        fun _ => Or.inl rfl
    · by_cases h1 : j = ja
      · subst h1
        obtain ⟨w, hw⟩ := hHa.left
        exact hends _ (x := a) (hPa ▸ hw) (fun _ => Or.inl rfl)
          fun hbi => absurd (hτ _ b jb hbi hb.2) hj
      by_cases h2 : j = jb
      · subst h2
        obtain ⟨w, hw⟩ := hHb.left
        exact hends _ (x := a) (hPb ▸ hw) (fun hai => absurd (hτ _ a ja hai ha.2) hj.symm)
          fun _ => Or.inl rfl
      obtain ⟨u, w, hw⟩ := hP.supports_isSupport j
      exact hends _ (x := a) (hPo j h1 h2 ▸ hw) (fun hai => absurd (hτ _ a ja hai ha.2) h1)
        fun hbi => absurd (hτ _ b jb hbi hb.2) h2
  · -- Two pieces meet only in `a` or `b`.
    intro i i' hii z hz
    by_cases hτi : tauD ja jb i = tauD ja jb i'
    · rcases hpair i i' hii hτi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hPa, hPn, hHa.inter] at hz
        exact Or.inl hz
      · rw [hPa, hPn, Set.inter_comm, hHa.inter] at hz
        exact Or.inl hz
      · rw [hPb, hPsn, hHb.inter] at hz
        exact Or.inr hz
      · rw [hPb, hPsn, Set.inter_comm, hHb.inter] at hz
        exact Or.inr hz
    · exact absurd (hτ i' z _ hz.2 (hsub i hz.1)).symm hτi
  · -- No two pieces both hold `a` and `b`.
    intro i i' _ hai _ hbi
    rcases haP i hai with rfl | rfl <;> rcases hbP _ hbi with h | h <;> simp_all
  · intro i i' hii hai hai'
    rcases haP i hai with rfl | rfl <;> rcases haP i' hai' with rfl | rfl <;> simp_all [colD]
  · intro i i' hii hbi hbi'
    rcases hbP i hbi with rfl | rfl <;> rcases hbP i' hbi' with rfl | rfl <;> simp_all [colD]
  · rintro (_ | _)
    · exact ⟨some (some ja), hPa ▸ hHa.mem_left, rfl⟩
    · exact ⟨none, hHa.mem_right, rfl⟩
  · rintro (_ | _)
    · exact ⟨some (some jb), hPb ▸ hHb.mem_left, rfl⟩
    · exact ⟨some none, hHb.mem_right, rfl⟩
  · -- The pieces of `F_j*` hold its vertices.
    intro j u hu
    by_cases h1 : j = ja
    · subst h1
      rcases (hHa.union ▸ hu.2 : u ∈ Am ∪ Ap) with h | h
      · exact ⟨some (some j), rfl, hPa ▸ h⟩
      · exact ⟨none, rfl, h⟩
    by_cases h2 : j = jb
    · subst h2
      rcases (hHb.union ▸ hu.2 : u ∈ Bm ∪ Bp) with h | h
      · exact ⟨some (some j), rfl, hPb ▸ h⟩
      · exact ⟨some none, rfl, h⟩
    exact ⟨some (some j), rfl, (hPo j h1 h2).symm ▸ hu.2⟩
  · -- The pieces of `F_j*` hold its spaces.
    intro j s hs hsj
    by_cases h1 : j = ja
    · subst h1
      obtain ⟨w, hw⟩ := hHa.left
      rcases space_subset_of_union hS hs hw (hHa.union ▸ hsj) with h | h
      · exact ⟨some (some j), rfl, hPa ▸ h⟩
      · exact ⟨none, rfl, h⟩
    by_cases h2 : j = jb
    · subst h2
      obtain ⟨w, hw⟩ := hHb.left
      rcases space_subset_of_union hS hs hw (hHb.union ▸ hsj) with h | h
      · exact ⟨some (some j), rfl, hPb ▸ h⟩
      · exact ⟨some none, rfl, h⟩
    exact ⟨some (some j), rfl, (hPo j h1 h2).symm ▸ hsj⟩
  · -- The edges on the plus side at `a` are those of `μ(A₊)`.
    rintro (_ | _ | j) e he
    · exact iff_of_true he rfl
    · exact iff_of_false (edge_notMem_of_ne hP hG (hsub (some none)) hHa.right_subset hj.symm he)
        (by simp [colD])
    · refine iff_of_false ?_ (by simp [colD])
      by_cases h1 : j = ja
      · subst h1
        rw [hPa] at he
        exact disjoint_left.mp hMa.2 he
      exact edge_notMem_of_ne hP hG (hsub (some (some j))) hHa.right_subset h1 he
  · -- The edges on the plus side at `b` are those of `μ(B₊)`.
    rintro (_ | _ | j) e he
    · exact iff_of_false (edge_notMem_of_ne hP hG (hsub none) hHb.right_subset hj he)
        (by simp [colD])
    · exact iff_of_true he rfl
    · refine iff_of_false ?_ (by simp [colD])
      by_cases h2 : j = jb
      · subst h2
        rw [hPb] at he
        exact disjoint_left.mp hMb.2 he
      exact edge_notMem_of_ne hP hG (hsub (some (some j))) hHb.right_subset h2 he
  · -- Every copy of a vertex of `μ(a)` or `μ(b)` lies in some piece.
    intro c v hv _
    by_cases hva : v ∈ (μ (.vertex a)).vertexSet
    · have hvb := hab_disj v hva
      have h2 : ∀ d, splitName (μ (.vertex a)).vertexSet d v ∈ splitB μ a b false → False :=
        fun d hd => hvb (splitName_mem_splitB_iff'.mp hd).1
      cases hc : c.1
      · refine ⟨some (some ja), mem_supportGraph_of_vertex hP (hsub _) (hPa ▸ haA) hva, ?_⟩
        exact nm2_eq_of_sides (fun _ => hc.symm) fun hd => (h2 _ hd).elim
      · exact ⟨none, mem_supportGraph_of_vertex hP (hsub _) haA' hva,
          nm2_eq_of_sides (fun _ => hc.symm) fun hd => (h2 _ hd).elim⟩
    · have hvb : v ∈ (μ (.vertex b)).vertexSet := hv.resolve_left hva
      cases hc : c.2
      · refine ⟨some (some jb), mem_supportGraph_of_vertex hP (hsub _) (hPb ▸ hbB) hvb, ?_⟩
        exact nm2_eq_of_sides (fun h => (hva h).elim) fun _ => hc.symm
      · exact ⟨some none, mem_supportGraph_of_vertex hP (hsub _) hbB' hvb,
          nm2_eq_of_sides (fun h => (hva h).elim) fun _ => hc.symm⟩
  · -- Copies of a vertex in two pieces differ.
    intro i i' hii v hv hv'
    by_cases hτi : tauD ja jb i = tauD ja jb i'
    · rcases hpair i i' hii hτi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hPa] at hv
        exact nm2_ne_of_mem_left (by simp [colD]) (hMa.1 ⟨hv, hv'⟩)
      · rw [hPa] at hv'
        exact nm2_ne_of_mem_left (by simp [colD]) (hMa.1 ⟨hv', hv⟩)
      · rw [hPb] at hv
        exact nm2_ne_of_mem_right (c := colD (some (some jb))) (c' := colD (some none)) rfl
          Bool.false_ne_true
          (splitName_mem_splitB_iff'.mpr ⟨hMb.1 ⟨hv, hv'⟩, fun _ => rfl⟩)
      · rw [hPb] at hv'
        exact nm2_ne_of_mem_right (c := colD (some none)) (c' := colD (some (some jb))) rfl
          Bool.false_ne_true.symm
          (splitName_mem_splitB_iff'.mpr ⟨hMb.1 ⟨hv', hv⟩, fun _ => rfl⟩)
    · exact absurd hv' (vertex_notMem_of_ne hP (hsub i) (hsub i') hτi hv)

/-! ## The case of one support -/

/-- **The pieces when `a` and `b` lie in one support**, from the halves of `exists_halves_pair`. -/
theorem isPieceSystem_S (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (hG : G.IsGraph)
    {a b : S} {ja : Fin r} (ha : a ∈ Γ.V ∩ F_star ja) (hb : b ∈ Γ.V ∩ F_star ja) (hab : a ≠ b)
    {Am Ap Bm Bp M : Set S} (hHa : IsHalves Γ (F_star ja) Am Ap a)
    (hMa : HalvesMeetIn G Γ μ Am Ap a) (hHb : IsHalves Γ (F_star ja) Bm Bp b)
    (hMb : HalvesMeetIn G Γ μ Bm Bp b) (hM : SupportHasEnds Γ M a b) (hAmM : Am ∪ M = Bm)
    (hAmM' : Am ∩ M = {a}) (hMBp : M ∪ Bp = Ap) (hMBp' : M ∩ Bp = {b}) (hAB : Disjoint Am Bp) :
    IsPieceSystem G Γ Γ_sub μ F_star a b true Ap Bp (piecesS F_star ja Am M Bp) (tauS ja)
      colS := by
  have hS := hP.is_surface
  set P := piecesS F_star ja Am M Bp with hPdef
  have hPa : P (some (some ja)) = Am := by simp [hPdef, piecesS, oldPiece]
  have hPo : ∀ j, j ≠ ja → P (some (some j)) = F_star j := fun j h1 => by
    simp [hPdef, piecesS, oldPiece, h1]
  have hPn : P none = M := rfl
  have hPsn : P (some none) = Bp := rfl
  have hMAp : M ⊆ Ap := hMBp ▸ subset_union_left
  have hBpAp : Bp ⊆ Ap := hMBp ▸ subset_union_right
  have hMBm : M ⊆ Bm := hAmM ▸ subset_union_right
  have hAmBm : Am ⊆ Bm := hAmM ▸ subset_union_left
  have hApF : Ap ⊆ F_star ja := hHa.right_subset
  have hBmF : Bm ⊆ F_star ja := hHb.left_subset
  obtain ⟨haM, hbM, -, -, -⟩ := GM21.Supports.ends_mem_of_supportHasEnds hM
  have hbAm : b ∉ Am := fun h => hab (by
    have : b ∈ Am ∩ M := ⟨h, hbM⟩
    rw [hAmM'] at this
    exact this.symm)
  have haBp : a ∉ Bp := fun h => disjoint_left.mp hAB hHa.mem_left h
  have hsub : ∀ i, P i ⊆ F_star (tauS ja i) := by
    rintro (_ | _ | j)
    · exact hMAp.trans hApF
    · exact hBpAp.trans hApF
    · by_cases h1 : j = ja
      · rw [h1, hPa]
        exact hHa.left_subset
      rw [hPo j h1]
      rfl
  have hτ : ∀ i x j, x ∈ P i → x ∈ F_star j → tauS ja i = j := fun i x j hx hxj => by
    by_contra hne
    exact disjoint_left.mp (hP.supports_disjoint hne) (hsub i hx) hxj
  have hτa : ∀ i, tauS ja i = ja → i = none ∨ i = some none ∨ i = some (some ja) := by
    rintro (_ | _ | j) h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (by rw [show j = ja from h]))
  have hτne : ∀ i i', i ≠ i' → ¬ (tauS ja i = ja ∧ tauS ja i' = ja) → tauS ja i ≠ tauS ja i' := by
    intro i i' hii hnot heq
    rcases i with _ | _ | j
    · exact hnot ⟨rfl, heq.symm⟩
    · exact hnot ⟨rfl, heq.symm⟩
    · rcases i' with _ | _ | j'
      · exact hnot ⟨heq, rfl⟩
      · exact hnot ⟨heq, rfl⟩
      · exact hii (by rw [show j = j' from heq])
  have haP : ∀ i, a ∈ P i → i = none ∨ i = some (some ja) := by
    intro i hi
    rcases hτa i (hτ i a ja hi ha.2) with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hi haBp
    · exact Or.inr rfl
  have hbP : ∀ i, b ∈ P i → i = none ∨ i = some none := by
    intro i hi
    rcases hτa i (hτ i b ja hi hb.2) with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (hPa ▸ hi) hbAm
  have haA : a ∈ Γ.V ∩ Am := ⟨ha.1, hHa.mem_left⟩
  have haM' : a ∈ Γ.V ∩ M := ⟨ha.1, haM⟩
  have hbM' : b ∈ Γ.V ∩ M := ⟨hb.1, hbM⟩
  have hbB' : b ∈ Γ.V ∩ Bp := ⟨hb.1, hHb.mem_right⟩
  have hVM : ∀ v, v ∈ (supportGraph G Γ μ M).vertexSet → v ∈ (supportGraph G Γ μ Ap).vertexSet :=
    fun v hv => (GM21.supportGraph_mono hP ja hApF hMAp).vertexSet_subset hv
  have hVBp : ∀ v, v ∈ (supportGraph G Γ μ Bp).vertexSet →
      v ∈ (supportGraph G Γ μ Ap).vertexSet :=
    fun v hv => (GM21.supportGraph_mono hP ja hApF hBpAp).vertexSet_subset hv
  have hVM' : ∀ v, v ∈ (supportGraph G Γ μ M).vertexSet → v ∈ (supportGraph G Γ μ Bm).vertexSet :=
    fun v hv => (GM21.supportGraph_mono hP ja hBmF hMBm).vertexSet_subset hv
  refine
    { sup := ?_, sub := hsub, inter := ?_, notBoth := ?_, diffA := ?_, diffB := ?_,
      bothA := ?_, bothB := ?_, coverV := ?_, coverS := ?_, colA := ?_, colB := ?_,
      cover := ?_, disj := ?_ }
  · have hends : ∀ i, ∀ {u w : S}, SupportHasEnds Γ (P i) u w → (a ∈ P i → a = u ∨ a = w) →
        (b ∈ P i → b = u ∨ b = w) → ∃ u w, SupportHasEnds Γ (P i) u w ∧ P i ∩ {a, b} ⊆ {u, w} :=
      fun i u w hs h1 h2 => ⟨u, w, hs, fun y ⟨hy, hy'⟩ => by
        rcases hy' with rfl | rfl
        · exact h1 hy
        · exact h2 hy⟩
    rintro (_ | _ | j)
    · exact hends none hM (fun _ => Or.inl rfl) fun _ => Or.inr rfl
    · obtain ⟨w, hw⟩ := hHb.right
      exact hends (some none) hw (fun h => absurd h haBp) fun _ => Or.inl rfl
    · by_cases h1 : j = ja
      · subst h1
        obtain ⟨w, hw⟩ := hHa.left
        exact hends _ (hPa ▸ hw) (fun _ => Or.inl rfl) fun h => absurd (hPa ▸ h) hbAm
      obtain ⟨u, w, hw⟩ := hP.supports_isSupport j
      exact hends _ (hPo j h1 ▸ hw) (fun hai => absurd (hτ _ a ja hai ha.2) h1)
        fun hbi => absurd (hτ _ b ja hbi hb.2) h1
  · intro i i' hii z hz
    by_cases hτi : tauS ja i = ja ∧ tauS ja i' = ja
    · rcases hτa i hτi.1 with rfl | rfl | rfl <;> rcases hτa i' hτi.2 with rfl | rfl | rfl
      · exact absurd rfl hii
      · rw [hPn, hPsn, hMBp'] at hz
        exact Or.inr hz
      · rw [hPn, hPa, Set.inter_comm, hAmM'] at hz
        exact Or.inl hz
      · rw [hPn, hPsn, Set.inter_comm, hMBp'] at hz
        exact Or.inr hz
      · exact absurd rfl hii
      · rw [hPsn, hPa] at hz
        exact absurd hz.1 (disjoint_left.mp hAB hz.2)
      · rw [hPn, hPa, hAmM'] at hz
        exact Or.inl hz
      · rw [hPsn, hPa] at hz
        exact absurd hz.2 (disjoint_left.mp hAB hz.1)
      · exact absurd rfl hii
    · exact absurd (hτ i' z _ hz.2 (hsub i hz.1)).symm (hτne i i' hii hτi)
  · intro i i' hii hai hai' hbi
    rcases haP i hai with rfl | rfl
    · rcases haP i' hai' with rfl | rfl
      · exact absurd rfl hii
      · exact hPa ▸ hbAm
    · rcases hbP _ hbi with h | h <;> simp at h
  · intro i i' hii hai hai'
    rcases haP i hai with rfl | rfl <;> rcases haP i' hai' with rfl | rfl <;> simp_all [colS]
  · intro i i' hii hbi hbi'
    rcases hbP i hbi with rfl | rfl <;> rcases hbP i' hbi' with rfl | rfl <;> simp_all [colS]
  · rintro (_ | _)
    · exact ⟨some (some ja), hPa ▸ hHa.mem_left, rfl⟩
    · exact ⟨none, haM, rfl⟩
  · rintro (_ | _)
    · exact ⟨none, hbM, rfl⟩
    · exact ⟨some none, hHb.mem_right, rfl⟩
  · intro j u hu
    by_cases h1 : j = ja
    · subst h1
      rcases (hHa.union ▸ hu.2 : u ∈ Am ∪ Ap) with h | h
      · exact ⟨some (some j), rfl, hPa ▸ h⟩
      · rcases (hMBp ▸ h : u ∈ M ∪ Bp) with h' | h'
        · exact ⟨none, rfl, h'⟩
        · exact ⟨some none, rfl, h'⟩
    exact ⟨some (some j), rfl, (hPo j h1).symm ▸ hu.2⟩
  · intro j s hs hsj
    by_cases h1 : j = ja
    · subst h1
      obtain ⟨w, hw⟩ := hHa.left
      rcases space_subset_of_union hS hs hw (hHa.union ▸ hsj) with h | h
      · exact ⟨some (some j), rfl, hPa ▸ h⟩
      · rcases space_subset_of_union hS hs hM (hMBp ▸ h) with h' | h'
        · exact ⟨none, rfl, h'⟩
        · exact ⟨some none, rfl, h'⟩
    exact ⟨some (some j), rfl, (hPo j h1).symm ▸ hsj⟩
  · rintro (_ | _ | j) e he
    · exact iff_of_true ((GM21.supportGraph_mono hP ja hApF hMAp).edgeSet_subset he) rfl
    · exact iff_of_true ((GM21.supportGraph_mono hP ja hApF hBpAp).edgeSet_subset he) rfl
    · refine iff_of_false ?_ (by simp [colS])
      by_cases h1 : j = ja
      · subst h1
        rw [hPa] at he
        exact disjoint_left.mp hMa.2 he
      exact edge_notMem_of_ne hP hG (hsub (some (some j))) hApF h1 he
  · rintro (_ | _ | j) e he
    · refine iff_of_false ?_ (by simp [colS])
      exact disjoint_left.mp hMb.2 ((GM21.supportGraph_mono hP ja hBmF hMBm).edgeSet_subset he)
    · exact iff_of_true he rfl
    · refine iff_of_false ?_ (by simp [colS])
      by_cases h1 : j = ja
      · subst h1
        rw [hPa] at he
        exact disjoint_left.mp hMb.2 ((GM21.supportGraph_mono hP j hBmF hAmBm).edgeSet_subset he)
      exact edge_notMem_of_ne hP hG (hsub (some (some j))) hHb.right_subset h1 he
  · intro c v hv _
    by_cases hA : v ∈ (μ (.vertex a)).vertexSet ∧ c.1 = false
    · refine ⟨some (some ja), mem_supportGraph_of_vertex hP (hsub _) (hPa ▸ haA) hA.1, ?_⟩
      refine nm2_eq_of_sides (fun _ => hA.2.symm) fun hd => ?_
      exact absurd ((splitName_mem_splitB_iff'.mp hd).2 hA.1) Bool.false_ne_true
    have h1 : v ∈ (μ (.vertex a)).vertexSet → true = c.1 := fun hva => by
      cases hc : c.1
      · exact absurd ⟨hva, hc⟩ hA
      · rfl
    by_cases hB : v ∈ (μ (.vertex b)).vertexSet ∧ c.2 = true
    · exact ⟨some none, mem_supportGraph_of_vertex hP (hsub _) hbB' hB.1,
        nm2_eq_of_sides h1 fun _ => hB.2.symm⟩
    refine ⟨none, ?_, nm2_eq_of_sides h1 fun hd => ?_⟩
    · rcases hv with hva | hvb
      · exact mem_supportGraph_of_vertex hP (hsub none) haM' hva
      · exact mem_supportGraph_of_vertex hP (hsub none) hbM' hvb
    · have hvb := (splitName_mem_splitB_iff'.mp hd).1
      cases hc : c.2
      · rfl
      · exact absurd ⟨hvb, hc⟩ hB
  · intro i i' hii v hv hv'
    by_cases hτi : tauS ja i = ja ∧ tauS ja i' = ja
    · rcases hτa i hτi.1 with rfl | rfl | rfl <;> rcases hτa i' hτi.2 with rfl | rfl | rfl
      · exact absurd rfl hii
      · exact nm2_ne_of_mem_right (c := colS none) (c' := colS (some none)) rfl
          Bool.false_ne_true (splitName_mem_splitB_iff'.mpr ⟨hMb.1 ⟨hVM' v hv, hv'⟩, fun _ => rfl⟩)
      · rw [hPa] at hv'
        exact nm2_ne_of_mem_left (c := colS none) (c' := colS (some (some ja)))
          Bool.false_ne_true.symm (hMa.1 ⟨hv', hVM v hv⟩)
      · exact nm2_ne_of_mem_right (c := colS (some none)) (c' := colS none) rfl
          Bool.false_ne_true.symm
          (splitName_mem_splitB_iff'.mpr ⟨hMb.1 ⟨hVM' v hv', hv⟩, fun _ => rfl⟩)
      · exact absurd rfl hii
      · rw [hPa] at hv'
        exact nm2_ne_of_mem_left (c := colS (some none)) (c' := colS (some (some ja)))
          Bool.false_ne_true.symm (hMa.1 ⟨hv', hVBp v hv⟩)
      · rw [hPa] at hv
        exact nm2_ne_of_mem_left (c := colS (some (some ja))) (c' := colS none)
          Bool.false_ne_true (hMa.1 ⟨hv, hVM v hv'⟩)
      · rw [hPa] at hv
        exact nm2_ne_of_mem_left (c := colS (some (some ja))) (c' := colS (some none))
          Bool.false_ne_true (hMa.1 ⟨hv, hVBp v hv'⟩)
      · exact absurd rfl hii
    · exact absurd hv' (vertex_notMem_of_ne hP (hsub i) (hsub i') (hτne i i' hii hτi) hv)

end CutLine
end GM21
end GraphMinor
