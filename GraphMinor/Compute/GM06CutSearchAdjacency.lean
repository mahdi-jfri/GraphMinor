module

public import GraphMinor.Compute.GM06CutAdjacencyProgram

/-!
# Building search arrays from the four returned cut-data lists

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) computes
components from copied rotations, origins, active darts and live vertices. This
wrapper builds the active-end bitmap from that returned dart list,
then constructs all adjacency rows. Thus its inputs are ordinary
finite graph lists, with no supplied adjacency or membership table.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Build active-end membership from 628, then all search adjacency arrays. -/
def gm06CutSearchAdjacencyProg : Cmd :=
  .seq (gm06IncidenceBitsProg 628 627 647) gm06CutAdjacencyProg

/-- Exact graph-search representation from the four cut-data lists.
All offset and membership tables are constructed by the program. -/
theorem gm06CutSearchAdjacencyProg_exec {w n m : ℕ} (data : GM06CutData) (padding : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : n * n + 2 < 2 ^ w) (hlen : data.rotations.length = n)
    (horgLen : data.origins.length = 2 * m) (hvalues : ∀ v ∈ data.origins, v < n)
    (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hlive : ∀ v ∈ data.vertices, v < n) (hliveFit : data.vertices.length < 2 ^ w)
    (hactive : ∀ d ∈ data.activeDarts, d < 2 * m) (hactiveFit : data.activeDarts.length < 2 ^ w)
    (hproper : ∀ d ∈ data.activeDarts, ∀ u : Fin n,
      data.origins[d]?.getD 0 = u.val ↔ d ∈ data.rotations[u.val]?.getD [])
    (h625 : s.arrs 625 = gm06EncodeRows data.rotations ++ padding)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h626 : s.arrs 626 = data.origins) (h628 : s.arrs 628 = data.activeDarts)
    (h629 : s.arrs 629 = data.vertices) (h620 : s.regs 620 = n) (h647 : s.regs 647 = 2 * m) :
    ∃ sf t, Exec w gm06CutSearchAdjacencyProg s sf t ∧
      t ≤ 40 + 57 * n + 2 * m + 21 * (n * n) + 14 * data.vertices.length +
        14 * data.activeDarts.length + 129 * data.rotations.flatten.length ∧
      Keeps gm06CutAdjacencyRegs (627 :: gm06CutAdjacencyArrs) s sf ∧
      IsAdjList (gm06CutGraph n data) 620 621 622 (gm06CutAdjacencyLists n data) sf ∧
      (sf.arrs 622).length = n * n := by
  have hw1 : 1 < 2 ^ w := by omega
  let darts : List (Fin (2 * m)) := data.activeDarts.attach.map (fun d => ⟨d.val, hactive d.val d.property⟩)
  have hdarts : darts.map Fin.val = data.activeDarts := by simp [darts, List.map_map]
  have hdartsLen : darts.length = data.activeDarts.length := by simp only [darts, List.length_map, List.length_attach]
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06IncidenceBitsProg_exec
    628 627 647 (by decide) darts s hw1 hm (by simpa only [hdartsLen] using hactiveFit)
    h647 (by simpa only [hdarts] using h628)
  obtain ⟨sf, tf, hef, htf, hkf, hsf, hefTab, hbf⟩ := gm06CutAdjacencyProg_exec data padding s₁
    hw hn hm hfit hlen horgLen hvalues hkeys hlive hliveFit
    ((hk₁.2 625 (by decide)).trans h625)
    (by rw [hk₁.2 625 (by decide)]; exact hcode)
    (by rw [hk₁.2 625 (by decide)]; exact hwords)
    ((hk₁.2 626 (by decide)).trans h626) (by simpa only [hdarts] using hd₁)
    ((hk₁.2 629 (by decide)).trans h629) ((hk₁.1 620 (by decide)).trans h620)
  have hlenRows := gm06CutAdjacencyRowsFrom_flatten_length_le n 0 data.origins data.activeDarts data.vertices data.rotations
  rw [hlen] at hlenRows
  refine ⟨sf, t₁ + tf, .seq he₁ hef, ?_,
    (hk₁.mono (by simp [gm06CutAdjacencyRegs]) (by simp)).trans hkf
      (fun _ h => h) (by intro a ha; exact List.mem_cons_of_mem _ ha), gm06CutCSR_isAdjList data _ sf hlen hproper hsf hefTab hbf.1, ?_⟩
  · rw [hdartsLen] at ht₁
    omega
  · rw [hbf.1, List.length_append, List.length_replicate]
    omega

end GraphMinor.Compute
