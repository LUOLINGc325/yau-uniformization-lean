import Yau.Proofs.C05HarnackSourceJetBounds
import Yau.Proofs.C04RescaledTubeCurvatureScaling

/-! The original normalized minimized Harnack function is the actual
intrinsic source minus inverse Ricci energy for the same rescaled metric. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Yau.LeafProofs Set
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem realRicciDifferentialEnergy_const_mul (k : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (a : ℝ) (x : M.Carrier) :
    realRicciDifferentialEnergy k (fun y => a*f y) x = a^2 * realRicciDifferentialEnergy k f x := by
  have hd : DifferentiableAt ℝ (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x))).differentiableAt (by simp)
  unfold realRicciDifferentialEnergy
  change (1/2:ℝ) * ∑ b, ∑ d, (Matrix.of (realRicciCoeff k x (chartPt x x)))⁻¹ b d *
    rDeriv (fun w => a*inChart x f w) (chartPt x x) b *
      rDeriv (fun w => a*inChart x f w) (chartPt x x) d = _
  simp_rw [L12Aux.rDeriv_const_mul hd]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem realRicciDifferentialEnergy_scaleMetric (c : ℝ) (hc : 0 < c)
    (k : HermitianField M) (hk : MetricSmooth k) (f : M.Carrier → ℝ) (x : M.Carrier) :
    realRicciDifferentialEnergy (scaleField c hc k) f x = realRicciDifferentialEnergy k f x := by
  have hA : Matrix.of (realRicciCoeff (scaleField c hc k) x (chartPt x x)) =
      Matrix.of (realRicciCoeff k x (chartPt x x)) := by
    ext a b
    exact realRicciCoeff_scale c hc k hk x (mem_extChartAt_target x) a b
  simp only [realRicciDifferentialEnergy,hA]

theorem realRicciDifferentialEnergy_scaled_scalar (c : ℝ) (hc : 0 < c)
    (k : HermitianField M) (hk : MetricSmooth k) (hK : KahlerClosed k) (x : M.Carrier) :
    realRicciDifferentialEnergy (scaleField c hc k) (scalarCurvature (scaleField c hc k)) x =
      c⁻¹ ^ 2 * realRicciDifferentialEnergy k (scalarCurvature k) x := by
  have he : scalarCurvature (scaleField c hc k) = (fun y => c⁻¹ * scalarCurvature k y) := by
    funext y
    exact scalar_scaleField c hc k y
  rw [he,realRicciDifferentialEnergy_scaleMetric c hc k hk,
    realRicciDifferentialEnergy_const_mul k _ (scalarCurvature_smoothFn k hk hK)]

def intrinsicHarnackMinimum (k : HermitianField M) (κ : ℝ) (x : M.Carrier) : ℝ :=
  scalarHarnackSource k κ x - realRicciDifferentialEnergy k (scalarCurvature k) x

theorem normalizedHarnackMinimum_eq_intrinsic (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (ti R : ℝ) (hR : 0 < R) (x : Pt X) (z : ℝ) (ht : 0 < ti + z/R) :
    normalizedHarnackMinimum h ti R x z =
      intrinsicHarnackMinimum (scaleField R hR (h (ti+z/R))) (ti*R+z)⁻¹ x := by
  let t := ti + z/R
  have hk := L23Aux.metricFamilySmooth_slice h hf.1.2.1 (show t ∈ Ici (0:ℝ) from ht.le)
  have hK := hf.1.2.2.1 t ht.le
  have hs := spaceSlice_smoothFn (localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf) ht
  have hq : dualNormMat (ricci (h t) x) (scalarCovector (h t) x) =
      realRicciDifferentialEnergy (h t) (scalarCurvature (h t)) x :=
    scalar_differential_ricci_dual_eq (h t) hk hK _ hs x (hH.2.2.1 t ht.le x)
  have hE := realRicciDifferentialEnergy_scaled_scalar R hR (h t) hk hK x
  have hquot : realRicciDifferentialEnergy (h t) (scalarCurvature (h t)) x / R^2 =
      realRicciDifferentialEnergy (scaleField R hR (h t))
        (scalarCurvature (scaleField R hR (h t))) x := by
    rw [hE]
    ring
  unfold normalizedHarnackMinimum minimizedScalarHarnack intrinsicHarnackMinimum
  rw [sub_div,normalizedScalarHarnackSum_eq_source o h U P ρ hf ti R hR x z ht]
  change _ - dualNormMat (ricci (h t) x) (scalarCovector (h t) x) / R^2 = _
  rw [hq,hquot]

theorem intrinsicHarnackMinimum_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (hA : ∀ x, (ricci k x).PosDef) (κ : ℝ) :
    SmoothFn (intrinsicHarnackMinimum k κ) := by
  have hs := scalarHarnackSource_smoothFn k hk hK κ
  have hq := realRicciDifferentialEnergy_smoothFn k hk hK hA _ (scalarCurvature_smoothFn k hk hK)
  intro c
  exact (hs c).sub (hq c)

end Yau.Proofs.C05Aux
