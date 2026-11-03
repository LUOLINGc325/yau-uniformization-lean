import Yau.Proofs.C05IntrinsicInverseEnergyTime
import Yau.Proofs.C05NormalizedScalarTimeEvolution
import Yau.Proofs.C05ActualInverseEnergyTime
import Yau.Proofs.C05HarnackMinimumScaling

/-! The inverse-energy time derivative uses the same constant normalization
and original affine clock as all three scalar sources. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Yau.LeafProofs Yau.NodeProofs.G01Aux
open Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem normalized_ricciDifferentialEnergyTime_eq (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (t R : ℝ) (ht : 0 < t) (hR : 0 < R) (x : Pt X) :
    ricciDifferentialEnergyTime h x t / R^3 =
      intrinsicInverseEnergyTime (scaleField R hR (h t)) x := by
  let k := scaleField R hR (h t)
  have hk := L23Aux.metricFamilySmooth_slice h hf.1.2.1 ht.le
  obtain ⟨hs, hu, _⟩ := scalar_time_slices_smooth o h U P ρ hf t ht
  have hsc : scalarCurvature k = (fun y => R⁻¹*scalarCurvature (h t) y) := by
    funext y
    exact scalar_scaleField R hR (h t) y
  have hsource : scalarHarnackSource k 0 =
      (fun y => R⁻¹^2 * deriv (fun s => scalarCurvature (h s) y) t) :=
    source1_scaled_function o h U P ρ hf t R ht hR
  have hA : Matrix.of (realRicciCoeff k x (chartPt x x)) =
      Matrix.of (realRicciCoeff (h t) x (chartPt x x)) := by
    ext a b
    exact realRicciCoeff_scale R hR (h t) hk x (mem_extChartAt_target x) a b
  have hB : (2:ℝ) • rawReal (levi (scalarCurvature k) x) =
      R⁻¹ • ((2:ℝ) • rawReal (levi (scalarCurvature (h t)) x)) := by
    rw [hsc,levi_const_mul _ hs]
    ext a b
    simp only [rawReal,Matrix.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero]
    split_ifs <;> ring
  have hp : (fun a => scalarJet k (scalarCurvature k) x 1 (chartPt x x) ![a]) =
      R⁻¹ • realScalarCovector (h t) x := by
    funext a
    rw [scalarJet_one,hsc]
    change rDeriv (fun z => R⁻¹*inChart x (scalarCurvature (h t)) z) (chartPt x x) a = _
    exact L12Aux.rDeriv_const_mul
      (((hs x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
        (mem_extChartAt_target x))).differentiableAt (by simp)) R⁻¹ a
  have hq : (fun a => scalarJet k (scalarHarnackSource k 0) x 1 (chartPt x x) ![a]) =
      R⁻¹^2 • realScalarCovectorTime h x t := by
    funext a
    rw [scalarJet_one,hsource]
    change rDeriv (fun z => R⁻¹^2*inChart x
      (fun y => deriv (fun s => scalarCurvature (h s) y) t) z) (chartPt x x) a = _
    exact L12Aux.rDeriv_const_mul
      (((hu x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
        (mem_extChartAt_target x))).differentiableAt (by simp)) (R⁻¹^2) a
  change _ = intrinsicInverseEnergyTime k x
  unfold intrinsicInverseEnergyTime
  rw [hA,hB,hp,hq]
  rw [ricciDifferentialEnergyTime,inverseEnergyTime_sum_eq]
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mulVec,Matrix.mulVec_smul,
    smul_dotProduct,dotProduct_smul,smul_smul,smul_eq_mul]
  ring

end Yau.Proofs.C05Aux
