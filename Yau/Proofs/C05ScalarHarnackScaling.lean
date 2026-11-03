import Yau.Proofs.C05NormalizedHeatOperator
import Yau.Proofs.C05ScalarJetLinearity

/-! The original normalized Harnack sum is the actual spatial KRF source
of the same rescaled metric. The original physical clock is retained. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux Yau.LeafProofs Set
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem ricciNormSq_scaleField (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (x : M.Carrier) :
    ricciNormSq (scaleField c hc k) x = c⁻¹ ^ 2 * ricciNormSq k x := by
  have hg : (gMat k x).PosDef := L18Aux.hMat_posDef k x (chartPt x x) (mem_extChartAt_target x)
  unfold ricciNormSq traceWith
  rw [gMat_scaleField,ricci_scaleField,inverse_real_smul c hc _ hg]
  simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_smul,smul_smul,smul_eq_mul,
    ← Complex.ofReal_inv,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero]
  ring

def scalarHarnackSource (k : HermitianField M) (κ : ℝ) (x : M.Carrier) : ℝ :=
  laplacian k (scalarCurvature k) x + ricciNormSq k x + κ * scalarCurvature k x

theorem normalizedScalarHarnackSum_eq_source (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) (ht : 0 < ti + z / R) :
    scalarHarnackSum h x (ti + z / R) / R ^ 2 =
      scalarHarnackSource (scaleField R hR (h (ti + z / R))) (ti * R + z)⁻¹ x := by
  let t := ti + z / R
  have hclock : ti * R + z = R * t := by dsimp only [t]; field_simp [hR.ne'] <;> ring
  have hs : SmoothFn (scalarCurvature (h t)) :=
    spaceSlice_smoothFn (localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf) ht
  have hsc : scalarCurvature (scaleField R hR (h t)) =
      (fun y => R⁻¹ * scalarCurvature (h t) y) := by
    funext y
    exact scalar_scaleField R hR (h t) y
  change scalarHarnackSum h x t / R ^ 2 =
    scalarHarnackSource (scaleField R hR (h t)) (ti * R + z)⁻¹ x
  unfold scalarHarnackSource
  rw [hsc,laplacian_const_mul _ _ hs,laplacian_scaleField,ricciNormSq_scaleField,hclock]
  unfold scalarHarnackSum
  rw [scalar_time_evolution o h U P ρ hf x (t := t) (show 0 < t from ht)]
  let L := laplacian (h t) (scalarCurvature (h t)) x
  let A := ricciNormSq (h t) x
  let F := scalarCurvature (h t) x
  change (L + A + t⁻¹ * F) / R ^ 2 =
    R⁻¹ * (R⁻¹ * L) + R⁻¹ ^ 2 * A + (R*t)⁻¹ * (R⁻¹ * F)
  field_simp [hR.ne',show t ≠ 0 from ne_of_gt ht]
  <;> ring

end Yau.Proofs.C05Aux
