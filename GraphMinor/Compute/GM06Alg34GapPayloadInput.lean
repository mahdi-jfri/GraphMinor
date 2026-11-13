module

public import GraphMinor.Compute.GM06Alg34GapPayloadBuild
import GraphMinor.Compute.GM06Alg34GapPositionCast

/-!
# Induced payload replacement for supplied region lists

The gap program's positional specification also applies directly to a
supplied region list. Reading that list at finite positions is a plain
finite operation. Equal cuff and gap lengths prove the reader's exact
round trip, so the program needs no map supplied by a geometric proof.
-/

public section
namespace GraphMinor.Compute

/-- The combined payload program accepts plain supplied cuff and gap
lists and installs their exact finite induced update. -/
theorem gm06GapPayloadBuildProg_exec_list (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (R : List (Fin x.regions.length))
    (hL : x.cuffs = [L]) (hlen : R.length = L.length)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hmask : s.arrs 4 = gm06VertexMask vs) (hgap : s.arrs 47 = R.map Fin.val) :
    ∃ s' t, Exec (wordSize c x.size) gm06GapPayloadBuildProg s s' t ∧
      t ≤ 1200 * (x.size + 2) ^ 3 ∧ s'.arrs 0 = (x.inducedData vs).words ∧
      s'.arrs 47 = (x.gapRegionsAfterDeletion vs L R).map Fin.val ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  let g : Fin L.length → Fin x.regions.length := fun i => R.get (Fin.cast hlen.symm i)
  have hg : List.ofFn g = R := (gm06OfFn_cast hlen.symm R.get).trans (List.ofFn_get R)
  have hgapg : s.arrs 47 = List.ofFn (fun j => (g j).val) :=
    hgap.trans ((congrArg (List.map Fin.val) hg.symm).trans
      (List.map_ofFn (f := g) (g := Fin.val)))
  obtain ⟨s', t, he, ht, hbase, hnew, harr⟩ :=
    gm06GapPayloadBuildProg_exec x vs L g hL hc hinput hmask hgapg
  exact ⟨s', t, he, ht, hbase,
    hnew.trans (congrArg (fun Q => (x.gapRegionsAfterDeletion vs L Q).map Fin.val) hg), harr⟩

end GraphMinor.Compute
