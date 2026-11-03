import Yau.Proofs.F01RealHessianLeviLinear
import Yau.LeafProofs.L17RicciMatrixHolder

/-! Actual bounded-geometry entry jets give the genuine uniform jets of
the Frobenius realified background and its native Ricci matrix, without
silently changing the matrix norm used by either contract. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance backgroundRealSymNormedSpace (n : ℕ) : NormedSpace ℝ (Sym n) where
  toModule := inferInstance
  norm_smul_le c A := norm_smul_le c (A : Mat n)

local instance backgroundRealSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

theorem background_array_smooth (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun (z : Space n) (ij : Fin n × Fin n) => pullbackMatrix g (A.chart p) z ij.1 ij.2)
      (ball 0 A.radius) :=
  contDiffOn_pi.mpr (fun ij => A.coefficient_smooth p ij.1 ij.2)

theorem background_array_uniform_jets (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k
      (fun p z (ij : Fin n × Fin n) => pullbackMatrix g (A.chart p) z ij.1 ij.2)
      (fun _ => ball 0 A.radius) :=
  UniformJetBounds.pi (fun ij => A.coefficient_uniformJetBounds k ij.1 ij.2)
    (fun _ => isOpen_ball) (fun ij p => A.coefficient_smooth p ij.1 ij.2)

theorem realified_background_smooth (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => iota (pullbackMatrix g (A.chart p) z)) (ball 0 A.radius) :=
  iotaArrayCLM.contDiff.comp_contDiffOn (background_array_smooth A p)

theorem realified_background_uniform_jets (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p z => iota (pullbackMatrix g (A.chart p) z)) (fun _ => ball 0 A.radius) :=
  (background_array_uniform_jets A k).comp_clm (fun _ => isOpen_ball)
    (background_array_smooth A) iotaArrayCLM

theorem realified_backgroundRicci_eq_second (A : BoundedChartFamily g) (p : M.Carrier)
    {z : Space n} (hz : z ∈ ball 0 A.radius) :
    (-realLeviSecondCLM) (backgroundLogDetHessian A p z) =
      iota (backgroundRicci (pullbackMatrix g (A.chart p)) z) := by
  have hq : ContDiffAt ℝ 2 (A.backgroundLogDet p) z :=
    ((A.backgroundLogDet_smooth p).contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp)
  rw [neg_apply]
  change -realLeviSecondCLM (fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) z) = _
  rw [realLeviSecondCLM_eq_native hq]
  change -iota (leviC (A.backgroundLogDet p) z) = iota (-leviC (A.backgroundLogDet p) z)
  have he := iota_real_smul (-1) (leviC (A.backgroundLogDet p) z)
  simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul] using he.symm

theorem realified_backgroundRicci_smooth (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => iota (backgroundRicci (pullbackMatrix g (A.chart p)) z)) (ball 0 A.radius) := by
  have h := (-realLeviSecondCLM).contDiff.comp_contDiffOn (A.backgroundLogDet_hessian_smooth p)
  apply h.congr
  intro z hz
  exact (realified_backgroundRicci_eq_second A p hz).symm

theorem realified_backgroundRicci_uniform_jets (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p z => iota (backgroundRicci (pullbackMatrix g (A.chart p)) z))
      (fun _ => ball 0 A.radius) := by
  have h := (A.backgroundLogDet_hessian_uniformJetBounds k).comp_clm
    (fun _ => isOpen_ball) A.backgroundLogDet_hessian_smooth (-realLeviSecondCLM)
  apply h.congr (fun _ => isOpen_ball)
  intro p z hz
  exact realified_backgroundRicci_eq_second A p hz

end Yau.NodeProofs.F01Aux
