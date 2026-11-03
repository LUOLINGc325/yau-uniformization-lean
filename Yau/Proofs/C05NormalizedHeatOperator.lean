import Yau.Proofs.C05ActualHarnackHeat
import Yau.Proofs.C05NormalizedHarnack
import Yau.Proofs.C04Scaling

/-! The actual heat operator on the original normalized space-time clock. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux Set Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem laplacian_scaleField (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (f : M.Carrier → ℝ) (x : M.Carrier) :
    laplacian (scaleField c hc k) f x = c⁻¹ * laplacian k f x := by
  have hg : (gMat k x).PosDef := L18Aux.hMat_posDef k x (chartPt x x) (mem_extChartAt_target x)
  rw [laplacian,gMat_scaleField,traceWith,inverse_real_smul c hc _ hg]
  simp only [Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,← Complex.ofReal_inv,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,laplacian,traceWith]

def normalizedScalarHeatOp (h : Flow X) (u : STF X) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) : ℝ :=
  deriv (fun w => u x (ti + w / R) / R ^ 2) z -
    laplacian (scaleField R hR (h (ti + z / R)))
      (fun y => u y (ti + z / R) / R ^ 2) x

theorem normalizedScalarHeatOp_eq (h : Flow X) (u : STF X) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ)
    (hu : DifferentiableAt ℝ (u x) (ti + z / R))
    (hs : SmoothFn (fun y => u y (ti + z / R))) :
    normalizedScalarHeatOp h u ti R hR x z =
      (deriv (u x) (ti + z / R) - laplacian (h (ti + z / R))
        (fun y => u y (ti + z / R)) x) / R ^ 3 := by
  have ha : HasDerivAt (fun w => ti + w / R) (1 / R) z :=
    (hasDerivAt_const z ti).add ((hasDerivAt_id z).div_const R) |>.congr_deriv (by ring)
  have hd := (hu.hasDerivAt.comp z ha).div_const (R ^ 2)
  dsimp only [Function.comp_def] at hd
  have he : (fun y => u y (ti + z / R) / R ^ 2) =
      (fun y => (R ^ 2)⁻¹ * u y (ti + z / R)) := by funext y; ring
  unfold normalizedScalarHeatOp
  rw [hd.deriv,he,laplacian_scaleField,laplacian_const_mul _ _ hs]
  field_simp [hR.ne']
  <;> ring

theorem minimizedScalarHarnack_smoothFn (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    {t : ℝ} (ht : 0 < t) : SmoothFn (fun y => minimizedScalarHarnack h y t) := by
  have hk := L23Aux.metricFamilySmooth_slice h hf.1.2.1 (show t ∈ Ici (0 : ℝ) from ht.le)
  have hK := hf.1.2.2.1 t ht.le
  have hs := spaceSlice_smoothFn (localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf) ht
  have hq := realRicciDifferentialEnergy_smoothFn (h t) hk hK (hH.2.2.1 t ht.le)
    (scalarCurvature (h t)) hs
  have he : (fun y => dualNormMat (ricci (h t) y) (scalarCovector (h t) y)) =
      realRicciDifferentialEnergy (h t) (scalarCurvature (h t)) := by
    funext y
    exact scalar_differential_ricci_dual_eq (h t) hk hK _ hs y (hH.2.2.1 t ht.le y)
  intro c
  change ContDiffOn ℝ ∞ (inChart c (fun y => scalarHarnackSum h y t -
    dualNormMat (ricci (h t) y) (scalarCovector (h t) y))) (chartTarget c)
  rw [show (fun y => scalarHarnackSum h y t -
    dualNormMat (ricci (h t) y) (scalarCovector (h t) y)) =
      (fun y => scalarHarnackSum h y t - realRicciDifferentialEnergy (h t) (scalarCurvature (h t)) y)
    by funext y; rw [congrFun he y]]
  exact (scalarHarnackSum_smoothFn o h U P ρ hf ht c).sub (hq c)

theorem normalizedMinimized_heat_eq (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (ti R : ℝ) (hR : 0 < R) (x : Pt X) (z : ℝ) (ht : 0 < ti + z / R) :
    normalizedScalarHeatOp h (fun y s => minimizedScalarHarnack h y s) ti R hR x z =
      minimizedScalarHarnackHeatOp h x (ti + z / R) / R ^ 3 := by
  have hdR := ((scalar_contDiffAt X o h U P ρ hf x ht).differentiableAt (by simp)).hasDerivAt
  have hdS := (scalar_second_hasDerivAt o h U P ρ hf x ht).add
    ((hasDerivAt_inv ht.ne').mul hdR)
  change HasDerivAt (fun s => scalarHarnackSum h x s) _ (ti + z / R) at hdS
  have hdQ := scalarHarnackQuadratic_hasDerivAt o h U P ρ hf hH x ht
  exact normalizedScalarHeatOp_eq h _ ti R hR x z (hdS.sub hdQ).differentiableAt
    (minimizedScalarHarnack_smoothFn o h U P ρ hf hH ht)

end Yau.Proofs.C05Aux
