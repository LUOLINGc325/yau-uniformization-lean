import Yau.Proofs.C04RayleighScaling

/-! The last scalar comparison in the central Ricci normalization argument. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C04Aux
open Yau Blueprint

/-- A Ricci bound at a smaller clock and its good-window comparison give
the positive lower bound for the actual normalized central metric. -/
theorem normalized_lower_of_clock_comparison {n : ℕ} (X : KahlerManifold n)
    (o : Pt X) (h : Flow X) (t t' b K : ℝ)
    (ht : 0 < t) (hb : 0 < b) (hK : 0 < K)
    (hR : 0 < scalarCurvature (h t) o)
    (hcompare : clockSpeed o h t ≤ K * clockSpeed o h t')
    (hmin : b * clockSpeed o h t' ≤ ricciMin o h t) :
    b / K ≤ relMinEigenvalue
      (gMat (scaleField (scalarCurvature (h t) o) hR (h t)) o)
      (ricci (scaleField (scalarCurvature (h t) o) hR (h t)) o) := by
  apply normalized_ricci_lower X o h t (b / K) ht (div_pos hb hK) hR
  calc
    (b / K) * clockSpeed o h t ≤ (b / K) * (K * clockSpeed o h t') :=
      mul_le_mul_of_nonneg_left hcompare (div_pos hb hK).le
    _ = b * clockSpeed o h t' := by field_simp
    _ ≤ ricciMin o h t := hmin

end Yau.Proofs.C04Aux
