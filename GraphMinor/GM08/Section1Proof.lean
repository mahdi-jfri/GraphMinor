module

public import GraphMinor.GM08.Defs
import GraphMinor.GM08.DrawOffBoundary
import GraphMinor.GM08.Section18Main
import GraphMinor.Surface.NormalWord

/-!
# Graph Minors VIII, (1.1) and (1.2) (pages 256–257)

The paper proves (1.2) as the special case of its main theorem (6.1) where the class has index
zero (page 263: "This result clearly implies (1.2), which is its special case when $\mathcal{A}$
has index zero"). It derives (1.1) from (1.2) on page 257: "for any number $g$ there is a finite
list of surfaces such that every graph with genus $\le g$ can be drawn on some surface in the
list".

- `theorem_1_2`: an antichain of graphs drawn in $\Sigma$ gives a class of grafts of index zero,
  and $\Sigma$ embeds this class, since a drawing can be moved off $bd(\Sigma)$
  (`exists_drawing_off_bd`). By (6.1) the class is well-rooted. A simulation of grafts of index
  zero is a minor model, so an infinite antichain would contain two graphs, one a minor of the
  other.
- `theorem_1_1`: a graph of genus at most $g$ can be drawn in $\Sigma(a, b, 0)$ for some
  $a + b \le g$, after pasting discs on the cuffs. There are finitely many such surfaces, and
  (1.2) applies to each.
-/

public section

namespace GraphMinor.GM08

open Set Function Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VIII, (1.2)** (page 257):
"(1.2) *For any surface $\Sigma$, every antichain whose members can all be drawn in $\Sigma$ is
finite.*"
The proof is the paper's: (1.2) is the case of (6.1) (`theorem_6_1`) with index zero (page 263). -/
theorem theorem_1_2_proof {α : Type u} {β : Type v} (S : Type w) [TopologicalSpace S]
    (hS : IsSurface S) {A : Set (Graph α β)}
    (hA : IsGraphAntichain A) (hDraw : ∀ G ∈ A, GM16.CanBeDrawnIn S G) :
    A.Finite := by
  -- The class of grafts `(G, ∅)` with `G ∈ A`.
  let 𝒜 : Set (Graft α β) := {X | X.T = ∅ ∧ X.G ∈ A}
  have hindex : HasGraftClassIndex 𝒜 := ⟨0, fun X hX => by
    simp only [Graft.index, hX.1, ncard_empty, le_refl]⟩
  have hembed : EmbedsGraftClass S 𝒜 := fun X hX =>
    embedsGraft_of_canBeDrawnIn hS X hX.1 (hDraw X.G hX.2)
  have hwr : IsWellRootedGraftClass 𝒜 :=
    theorem_6_1_proof.{u, v, w} α β 𝒜 hindex ⟨S, inferInstance, hS, hembed⟩
  by_contra hInf
  have hInf' : A.Infinite := hInf
  let e : ℕ ↪ A := hInf'.natEmbedding
  let X : ℕ → Graft α β := fun n =>
    { G := (e n).1, T := ∅, T_subset := empty_subset _, finite_G := hA.1 _ (e n).2 }
  obtain ⟨i, j, hij, ηv, ηe, hsim, -, -⟩ := hwr X (fun n => ⟨rfl, (e n).2⟩)
  have hfi := hA.1 _ (e i).2
  have hfj := hA.1 _ (e j).2
  have hminor : IsIsoMinor (e i).1 (e j).1 :=
    isIsoMinor_of_isMinorModel _ _ hfi.1 hfi.2 hfj.1 hfj.2 ηv ηe hsim
  have hne : (e i).1 ≠ (e j).1 := fun heq => hij.ne (e.injective (Subtype.ext heq))
  exact hA.2 _ (e i).2 _ (e j).2 hne hminor

/-- The step from (1.2) to (1.1) on page 257: if every member of an antichain can be drawn in
some $\Sigma(a, b, c)$ with $a + b \le g$, the antichain is finite. Pasting discs on the cuffs
puts each member in one of the finitely many surfaces $\Sigma(a, b, 0)$ with $a, b \le g$. -/
theorem finite_of_forall_drawn_model {α : Type u} {β : Type v} (g : ℕ)
    {A : Set (Graph α β)} (hA : IsGraphAntichain A)
    (hDraw : ∀ G ∈ A, ∃ a b c : ℕ, a + b ≤ g ∧ GM16.CanBeDrawnIn (SurfaceModel a b c) G) :
    A.Finite := by
  let B : Fin (g + 1) → Fin (g + 1) → Set (Graph α β) := fun a b =>
    {G | G ∈ A ∧ GM16.CanBeDrawnIn (SurfaceModel a b 0) G}
  have hB : ∀ a b, (B a b).Finite := by
    intro a b
    refine theorem_1_2_proof (SurfaceModel a b 0) (isSurface_model a b 0).1
      ⟨fun G hG => hA.1 G hG.1, fun G hG H hH => hA.2 G hG.1 H hH.1⟩ ?_
    exact fun G hG => hG.2
  refine (finite_iUnion fun a => finite_iUnion fun b => hB a b).subset ?_
  intro G hG
  obtain ⟨a, b, c, hab, hd⟩ := hDraw G hG
  have hfin := hA.1 G hG
  simp only [mem_iUnion]
  refine ⟨⟨a, by omega⟩, ⟨b, by omega⟩, hG, ?_⟩
  exact canBeDrawnIn_model_cap hfin.1 hfin.2 hd

/-- **Graph Minors VIII, (1.1)** (page 256):
"(1.1) *For any number $g$, every antichain of graphs all of genus $\le g$ is finite.*"
The proof is the paper's (page 257): finitely many surfaces carry every graph of genus at most
$g$, and (1.2) (`theorem_1_2`) applies to each. -/
theorem theorem_1_1_proof {α : Type u} {β : Type v} (g : ℕ)
    {A : Set (Graph α β)} (hA : IsGraphAntichain A)
    (hGenus : ∀ G ∈ A, graphGenus G ≤ g) :
    A.Finite := by
  refine finite_of_forall_drawn_model g hA fun G hG => ?_
  have hfin := hA.1 G hG
  obtain ⟨a, ha⟩ := exists_canBeDrawnIn_model hfin.1 hfin.2
  have hne : {g : ℕ | ∃ a b c : ℕ, a + b ≤ g ∧ GM16.CanBeDrawnIn (SurfaceModel a b c) G}.Nonempty :=
    ⟨a, a, 0, 0, by omega, ha⟩
  obtain ⟨a', b', c', hab, hd⟩ := Nat.sInf_mem hne
  exact ⟨a', b', c', hab.trans (hGenus G hG), hd⟩

/-- Variant of **Graph Minors VIII, (1.1)** (page 256) phrased with `HasGraphGenusLE G g`. -/
theorem theorem_1_1_hasGraphGenusLE {α : Type u} {β : Type v} (g : ℕ)
    {A : Set (Graph α β)} (hA : IsGraphAntichain A)
    (hGenus : ∀ G ∈ A, HasGraphGenusLE G g) :
    A.Finite :=
  finite_of_forall_drawn_model g hA hGenus

end GraphMinor.GM08
