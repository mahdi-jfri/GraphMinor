module

public import GraphMinor.GM06.Section5CapDrawing
import GraphMinor.GM06.Section5PuncturedDrawing

/-!
# The connected puncture in the capped cylinder

For the boundary argument of VI (5.1), page 129, the drawing with
cuffs remains connected after deleting an initial vertex. Its closed
embedding in the sphere preserves that punctured point set. This
supplies the connectedness hypothesis for the distinct-corners lemma.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- Removing one cylinder point commutes with the closed embedding
of the drawing in the sphere. -/
theorem cylinderSphereDrawing_punctured_U (F : Drawing ClosedCylinder) (s : ClosedCylinder) :
    (cylinderSphereDrawing F).U \ {cylinderToSphere s} = cylinderToSphere '' (F.U \ {s}) := by
  rw [cylinderSphereDrawing_U]
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro he
    exact hn (congrArg cylinderToSphere he)
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    intro he
    exact hn (injective_cylinderToSphere he)

/-- Capping preserves the connected puncture of an actual retained
barrier, as used in the Reduction 2 enclosures of VI (5.5). -/
theorem isConnected_punctured_cylinderSphereDrawing_of_source
    (F : Drawing ClosedCylinder) (s : ClosedCylinder) (hsource : IsConnected (F.U \ {s})) :
    IsConnected ((cylinderSphereDrawing F).U \ {cylinderToSphere s}) := by
  rw [cylinderSphereDrawing_punctured_U]
  exact hsource.image cylinderToSphere continuous_cylinderToSphere.continuousOn

/-- Accumulation of the punctured barrier at its attachment is
preserved by capping. -/
theorem mem_closure_punctured_cylinderSphereDrawing_of_source
    (F : Drawing ClosedCylinder) (s : ClosedCylinder) (hs : s ∈ closure (F.U \ {s})) :
    cylinderToSphere s ∈ closure ((cylinderSphereDrawing F).U \ {cylinderToSphere s}) := by
  rw [cylinderSphereDrawing_punctured_U]
  exact mem_closure_image continuous_cylinderToSphere.continuousAt hs

/-- The drawing with cuffs, viewed in the sphere, remains connected
after an initial vertex is removed in the unreduced situation of
VI (5.1). -/
theorem isConnected_punctured_cylinderSphereDrawing_of_no_reduction2
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (i : Fin k) :
    IsConnected ((cylinderSphereDrawing F).U \ {cylinderToSphere (cylinderM1Point k i)}) := by
  let s := cylinderM1Point k i
  have hsource : IsConnected (F.U \ {s}) := by
    rw [hFU, union_comm]
    exact isConnected_punctured_drawing_and_cuffs_of_no_reduction2 L hk hG hno i
  exact isConnected_punctured_cylinderSphereDrawing_of_source F s hsource

/-- The unreduced case follows by excluding the specified reduction. -/
theorem isConnected_punctured_cylinderSphereDrawing
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (i : Fin k) :
    IsConnected ((cylinderSphereDrawing F).U \ {cylinderToSphere (cylinderM1Point k i)}) := by
  exact isConnected_punctured_cylinderSphereDrawing_of_no_reduction2 L hk hG
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩) hFU i

end GraphMinor.GM06
