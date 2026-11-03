import Yau.Proofs.G04KahlerCodifferential
import Yau.Proofs.G04ScalarNormalization

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {M : ComplexManifold n}

theorem codifferential_zero (h : HermitianField M) (hs : MetricSmooth h) :
    L03.codifferentialRealForm h (0 : RealForm M (k + 1)) = 0 := by
  apply L03.representsCodifferential_unique h (codifferential_represents h hs _ L03.smoothRealForm_zero)
  intro x z hz I
  simp only [L03.formComponents_zero, L03.codifferentialComponents_zero, Pi.zero_apply]

theorem exterior_closed_eq_zero (A : RealForm M k) (hA : SmoothRealForm A) (hc : ClosedRealForm A) :
    L03.exteriorRealForm A = 0 := by
  apply L03.realForm_eq_of_center_components
  intro x I
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [L03.exteriorRealForm_represents A hA x (chartPt x x) hz I, hc x (chartPt x x) hz I]
  rfl

theorem closed_oneOne_hodge (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (A B : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A) (hc : ClosedRealForm A)
    (hAB : RepresentsHodge h A B) : B = (-2 : ℝ) • ddRealForm (formTrace h A) := by
  have hB : B = L03.hodgeRealForm h 2 A :=
    L03.representsHodge_unique h hAB (hodge_represents h hs A hA)
  rw [hB]
  change L03.exteriorRealForm (L03.codifferentialRealForm h A) +
    L03.codifferentialRealForm h (L03.exteriorRealForm A) = _
  rw [codifferential_closed_oneOne_eq h hs hk A hA h11 hc,
    exterior_closed_eq_zero A hA hc, codifferential_zero h hs, add_zero,
    ddRealForm, smul_smul]
  norm_num

theorem formHermitianMatrix_real_smul (c : ℝ) (A : RealForm M 2) (x : M.Carrier) :
    formHermitianMatrix (c • A) x = (c : ℂ) • formHermitianMatrix A x := by
  ext a b
  apply Complex.ext <;>
    simp [formHermitianMatrix, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring

theorem hodgeNormalization (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) :
    HodgeNormalization h := by
  refine ⟨scalarHodgeNormalization h hs hk, ?_⟩
  intro A B hA h11 hc hAB x
  have hτ := trace_smooth h hs A hA h11
  have hdd := (dd_properties (formTrace h A) hτ).2.2.2
  rw [closed_oneOne_hodge h hs hk A B hA h11 hc hAB,
    formHermitianMatrix_real_smul, formHermitianMatrix_of_representsIota _ _ hdd, smul_smul]
  norm_num

end Yau.NodeProofs.G04Aux
