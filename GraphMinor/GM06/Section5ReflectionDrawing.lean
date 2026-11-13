module

public import GraphMinor.GM06.Section5ReflectionMap
import GraphMinor.GM06.Section5ReflectionBoundary
import GraphMinor.GM07.Section9MoveOff
import GraphMinor.GM11.Walks

/-!
# Reflecting a Section 5 drawing

For the orientation reversal in VI (5.10), page 134, transport
the drawing by the plane reflection. Its point, vertex and edge
sets are the corresponding images. The reflection preserves radius
and the prescribed cuff sets, so the reflected drawing satisfies
the same Section 5 conditions. Applying it twice restores the drawing.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The drawing obtained by reversing the plane orientation. -/
noncomputable def section5ReflectedDrawing (k : ℕ) (G : Drawing ClosedCylinder) : Drawing ClosedCylinder :=
  GM07.embedDrawing (section5CylinderReflection k).isClosedEmbedding G

/-- Reflection transports the entire drawing point set. -/
theorem section5ReflectedDrawing_U (k : ℕ) (G : Drawing ClosedCylinder) :
    (section5ReflectedDrawing k G).U = section5CylinderReflection k '' G.U :=
  GM07.embedDrawing_U _ G

/-- Reflection transports the drawing vertex set. -/
theorem section5ReflectedDrawing_V (k : ℕ) (G : Drawing ClosedCylinder) :
    (section5ReflectedDrawing k G).V = section5CylinderReflection k '' G.V :=
  GM07.embedDrawing_V _ G

/-- Reflection transports the drawing edge set. -/
theorem section5ReflectedDrawing_E (k : ℕ) (G : Drawing ClosedCylinder) :
    (section5ReflectedDrawing k G).E = (image (section5CylinderReflection k)) '' G.E := by
  let : Nonempty ClosedCylinder := ⟨cylinderPoint 1 (by simp) 0⟩
  exact GM07.embedDrawing_E _ G

/-- Applying reflection twice fixes any cylinder point set. -/
theorem section5CylinderReflection_image_image (k : ℕ) (A : Set ClosedCylinder) :
    section5CylinderReflection k '' (section5CylinderReflection k '' A) = A := by
  rw [image_image]
  have he : (fun x => section5CylinderReflection k (section5CylinderReflection k x)) = id :=
    funext (section5CylinderReflection_involutive k)
  rw [he, image_id]

/-- Applying reflection twice restores the original drawing. -/
theorem section5ReflectedDrawing_involutive (k : ℕ) (G : Drawing ClosedCylinder) :
    section5ReflectedDrawing k (section5ReflectedDrawing k G) = G := by
  apply Drawing.ext_of_V_E
  · rw [section5ReflectedDrawing_V, section5ReflectedDrawing_V, section5CylinderReflection_image_image]
  · rw [section5ReflectedDrawing_E, section5ReflectedDrawing_E, image_image]
    have he : (fun A : Set ClosedCylinder => section5CylinderReflection k '' (section5CylinderReflection k '' A)) = id :=
      funext (section5CylinderReflection_image_image k)
    rw [he, image_id]

/-- Subdrawings remain subdrawings under reflection. -/
theorem section5ReflectedDrawing_isSubdrawing
    {k : ℕ} {P G : Drawing ClosedCylinder} (hPG : P.IsSubdrawing G) :
    (section5ReflectedDrawing k P).IsSubdrawing (section5ReflectedDrawing k G) := by
  constructor
  · rw [section5ReflectedDrawing_V, section5ReflectedDrawing_V]; exact image_mono hPG.1
  · rw [section5ReflectedDrawing_E, section5ReflectedDrawing_E]; exact image_mono hPG.2

/-- Vertex membership is preserved by simultaneous reflection of
both the point and the drawing. -/
theorem section5ReflectedDrawing_mem_V (k : ℕ) (G : Drawing ClosedCylinder) (p : ClosedCylinder) :
    section5CylinderReflection k p ∈ (section5ReflectedDrawing k G).V ↔ p ∈ G.V := by
  rw [section5ReflectedDrawing_V]
  exact (section5CylinderReflection k).injective.mem_set_image

/-- Drawing-point membership is preserved by simultaneous reflection. -/
theorem section5ReflectedDrawing_mem_U (k : ℕ) (G : Drawing ClosedCylinder) (p : ClosedCylinder) :
    section5CylinderReflection k p ∈ (section5ReflectedDrawing k G).U ↔ p ∈ G.U := by
  rw [section5ReflectedDrawing_U]
  exact (section5CylinderReflection k).injective.mem_set_image

/-- The reflected drawing satisfies the same prescribed cuff and
properness conditions of Section 5. -/
theorem isCylinderSection5Drawing_reflected
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) :
    IsCylinderSection5Drawing k (section5ReflectedDrawing k G) := by
  refine ⟨hG.1, ?_, ?_⟩
  · rintro x ⟨hxb, hxU⟩
    rw [section5ReflectedDrawing_U] at hxU
    obtain ⟨y, hy, rfl⟩ := hxU
    apply (section5ReflectedDrawing_mem_V k G y).mpr
    exact hG.2.1 ⟨(section5CylinderReflection_mem_bd k y).mp hxb, hy⟩
  · have he : (section5CylinderReflection k '' G.V) ∩ bd ClosedCylinder =
        section5CylinderReflection k '' (G.V ∩ bd ClosedCylinder) := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hyb⟩
        exact ⟨y, ⟨hy, (section5CylinderReflection_mem_bd k y).mp hyb⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hyb⟩, rfl⟩
        exact ⟨mem_image_of_mem _ hy, (section5CylinderReflection_mem_bd k y).mpr hyb⟩
    rw [section5ReflectedDrawing_V, he, hG.2.2, image_union,
      section5CylinderReflection_image_M1 hG.1, section5CylinderReflection_image_M2 hG.1]

end GraphMinor.GM06
