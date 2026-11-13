module

public import GraphMinor.Compute.PlanarityRamComponent
public import GraphMinor.Compute.PlanarityRamRoot
public import GraphMinor.Compute.PlanarityRamRootsFunction
public import GraphMinor.Compute.PlanarityRamInitialWork

/-!
# One action of the outer root scan

Discovered roots are skipped. A fresh root moves its reserved work to one
frame and invokes the proved component loop. Its fixed fuel exceeds the
remaining work. The time bound charges only the work consumed in this
component, so summing over roots stays linear.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- A single root decision and possible component call. -/
def searchRoot (adj : Array (List ℕ)) (fuel root : ℕ) (search : Search) : Option Search :=
  if (search.depth[root]?.join).isNone then
    searchFrames adj fuel { search with depth := search.depth.set! root (some 0) } [⟨root, 0⟩]
  else some search

/-- The recursive root scan is the sequence of its single-root actions. -/
theorem searchRoots_cons (adj : Array (List ℕ)) (fuel root : ℕ) (roots : List ℕ) (search : Search) :
    searchRoots adj fuel (root :: roots) search =
      (searchRoot adj fuel root search).bind fun next => searchRoots adj fuel roots next := by
  rw [searchRoots]
  unfold searchRoot
  split <;> rfl

/-- One root action costs at most eighteen steps plus the work consumed
by its component. The record and work budgets and both functional
invariants are preserved. -/
theorem searchRootProg_refines {N M w : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : State} {search : Search}
    (hadj : IsAdjList G 30 31 32 lists s)
    (h : DfsSearchAt N M s search) (hf : FramesAt N s [])
    (hb : SearchBounded N search) (hs : FrameInvariant (List.ofFn lists).toArray search [])
    (root : ℕ) (hr : root < N) (hroot : s.regs 40 = root)
    (hbudget : search.edges.size + searchWork (List.ofFn lists).toArray 0 search [] ≤ M)
    (hwork : searchWork (List.ofFn lists).toArray 1 search [] ≤ M + N)
    (hw : 2 * (N + M + 2) < 2 ^ w) (hentries : (s.arrs 32).length < 2 ^ w) :
    ∃ next s' t,
      searchRoot (List.ofFn lists).toArray (M + N + 1) root search = some next ∧
      Exec w searchRootProg s s' t ∧
      t ≤ 18 + 201 * (searchWork (List.ofFn lists).toArray 1 search [] -
        searchWork (List.ofFn lists).toArray 1 next []) ∧
      FramesAt N s' [] ∧ DfsSearchAt N M s' next ∧ SearchBounded N next ∧
      FrameInvariant (List.ofFn lists).toArray next [] ∧
      searchWork (List.ofFn lists).toArray 1 next [] ≤ searchWork (List.ofFn lists).toArray 1 search [] ∧
      next.edges.size + searchWork (List.ofFn lists).toArray 0 next [] ≤ M := by
  have hrd : root < search.depth.size := by rw [hb.1]; exact hr
  have hrword : root < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htag := hb.depth_tag_le ⟨root, hr⟩
  have htagArray : optionWord search.depth[root] < 2 ^ w := by
    have hh : optionWord search.depth[root] ≤ N := by
      simpa only [Array.getElem?_eq_getElem hrd, Option.join_some] using htag
    omega
  have dPrefix : PrefixAt s Field.depth.array N (search.depth.toList.map optionWord) := h.2.2.2.2.2.1
  have eread := dPrefix.read_option_reg hrd hroot hrword htagArray
  cases hdepth : search.depth[root]?.join with
  | some d =>
    have hraw : search.depth[root] = some d := by
      simpa only [Array.getElem?_eq_getElem hrd, Option.join_some] using hdepth
    have econd : (Expr.read Field.depth.array (.reg 40)).eval w s = some (d + 1) := by
      simpa only [hraw, optionWord] using eread
    refine ⟨search, s, 3, ?_, Exec.ite_true econd (by omega) (Exec.skip s), by simp,
      hf, h, hb, hs, le_rfl, hbudget⟩
    simp only [searchRoot, hdepth, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  | none =>
    let marked : Search := { search with depth := search.depth.set! root (some 0) }
    have hraw : search.depth[root] = none := by
      simpa only [Array.getElem?_eq_getElem hrd, Option.join_some] using hdepth
    have econd : (Expr.read Field.depth.array (.reg 40)).eval w s = some 0 := by
      simpa only [hraw, optionWord] using eread
    obtain ⟨s1, hx1, hf1, h1⟩ := startRootProg_refines (w := w) h hf root hr hroot hone hrword
    have h1' : DfsSearchAt N M s1 marked := h1
    have hb1 : SearchBounded N marked := hb.set_depth ⟨root, hr⟩ 0
      (Nat.lt_of_le_of_lt (Nat.zero_le root) hr)
    have hs1 : FrameInvariant (List.ofFn lists).toArray marked [⟨root, 0⟩] :=
      hs.push_discovered ⟨root, by simpa using hr⟩ hdepth
    have hwstart (c : ℕ) : searchWork (List.ofFn lists).toArray c marked [⟨root, 0⟩] =
        searchWork (List.ofFn lists).toArray c search [] :=
      searchWork_start _ c search hs.1 ⟨root, by simpa using hr⟩ hdepth
    have hbudget1 : marked.edges.size + searchWork (List.ofFn lists).toArray 0 marked [⟨root, 0⟩] ≤ M := by
      rw [hwstart]
      exact hbudget
    have ha (a : ℕ) (hcases : a = 30 ∨ a = 31 ∨ a = 32) : s1.arrs a = s.arrs a := by
      apply hx1.arrs_eq_of_not_mem_writtenArrs
      rcases hcases with rfl | rfl | rfl <;>
        simp [startRootProg, pushFrameProg, Cmd.writtenArrs, Field.array]
    have hadj1 := hadj.of_arrs_eq (ha 30 (Or.inl rfl)) (ha 31 (Or.inr (Or.inl rfl)))
      (ha 32 (Or.inr (Or.inr rfl)))
    have hentries1 : (s1.arrs 32).length < 2 ^ w := by rw [ha 32 (Or.inr (Or.inr rfl))]; exact hentries
    have hfuel : searchWork (List.ofFn lists).toArray 1 marked [⟨root, 0⟩] < M + N + 1 := by
      rw [hwstart]
      omega
    obtain ⟨next, s2, t2, hresult, hx2, ht2, hf2, h2, hb2, hs2, hwork2, hbudget2⟩ :=
      searchComponentProg_refines (M + N + 1) marked [⟨root, 0⟩] s1 hadj1 h1' hf1 hb1 hs1
        hbudget1 hw hentries1 hfuel
    refine ⟨next, s2, 2 + (15 + t2), ?_, Exec.ite_false econd (Exec.seq hx1 hx2), ?_,
      hf2, h2, hb2, hs2, ?_, hbudget2⟩
    · simp only [searchRoot, hdepth, Option.isNone_none, ↓reduceIte]
      exact hresult
    · rw [hwstart] at ht2
      omega
    · rwa [hwstart] at hwork2

end GraphMinor.Compute.PlanarityRam
