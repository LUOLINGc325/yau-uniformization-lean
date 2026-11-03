import Yau.Proofs.V04WallErrorNormIdentity
import Yau.Proofs.V04WallErrorPullback

/-! A scalar base function contributes only its horizontal Levi block. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem metricSmooth_dualNormChart_contDiffOn
    (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n => dualNormChart h x p.1 p.2)
      (cotangentTarget x) := by
  have hξ (i : Fin n) : ContDiffOn ℝ ∞ (fun p : CotangentCoord n => p.2 i)
      (cotangentTarget x) :=
    ((contDiff_piLp_apply (p := 2) (i := i)).comp contDiff_snd).contDiffOn
  have hinv (i j : Fin n) : ContDiffOn ℝ ∞
      (fun p : CotangentCoord n => (hMat h x p.1)⁻¹ i j) (cotangentTarget x) :=
    (entrywise_matrix_inv_contDiffOn
      (Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth h hs x)
      (fun z hz => (hMat_posDef h x z hz).det_pos.ne') i j).comp
        contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hC : ContDiffOn ℝ ∞ (fun p : CotangentCoord n =>
      ∑ i, star (p.2 i) * ∑ j, (hMat h x p.1)⁻¹ j i * p.2 j)
      (cotangentTarget x) :=
    ContDiffOn.sum fun i _ => (Complex.conjCLE.contDiff.comp_contDiffOn (hξ i)).mul
      (ContDiffOn.sum fun j _ => (hinv j i).mul (hξ j))
  exact Complex.reCLM.contDiff.comp_contDiffOn hC

theorem leviMatrix_fst {f : ComplexVector n → ℝ} {p : CotangentCoord n}
    (hf : ContDiffAt ℝ 2 f p.1) :
    leviMatrix (fun z : CotangentCoord n => f z.1) p cotangentDir =
      Matrix.fromBlocks (leviMatrix f p.1 stdVec) 0 0 0 := by
  have hp := leviMatrix_comp_clm
    (ContinuousLinearMap.fst ℂ (ComplexVector n) (ComplexVector n)) hf cotangentDir
  change leviMatrix (fun z : CotangentCoord n => f z.1) p cotangentDir =
    leviMatrix f p.1 (fun i => (cotangentDir i).1) at hp
  rw [hp]
  ext (i | i) (j | j) <;>
    simp [leviMatrix, cotangentDir, wirt_zero_direction, wirtBar_zero_direction]
  simp [wirt]

theorem spatialHessian_dualNorm_add_base {X : KahlerManifold n}
    (h : HermitianField X.manifold) (hs : MetricSmooth h)
    (y : CotangentPoint X.manifold) (b : Pt X → ℝ)
    (hb : ContDiffAt ℝ ∞ (b ∘ chartInv y.1) (chartPt y.1 y.1)) :
    spatialHessian (fun y' => dualNorm h y'.1 y'.2 + b y'.1) y =
      normChartHessian h y.1 (cotangentChart y.1 y) +
        Matrix.fromBlocks (levi b y.1) 0 0 0 := by
  let p := cotangentChart y.1 y
  have hopen : IsOpen (cotangentTarget y.1) :=
    (isOpen_extChartAt_target (I := ComplexModel n) y.1).prod isOpen_univ
  have hp : p ∈ cotangentTarget y.1 :=
    cotangentChart_mapsTo y.1 (mem_extChartAt_source y.1)
  have hn : ContDiffAt ℝ 2 (fun z : CotangentCoord n => dualNormChart h y.1 z.1 z.2) p :=
    ((metricSmooth_dualNormChart_contDiffOn h hs y.1).contDiffAt
      (hopen.mem_nhds hp)).of_le (by simp)
  have hb2 : ContDiffAt ℝ 2 (fun z => b (chartInv y.1 z)) p.1 := hb.of_le (by simp)
  have hbP : ContDiffAt ℝ 2 (fun z : CotangentCoord n => b (chartInv y.1 z.1)) p :=
    hb2.comp p contDiff_fst.contDiffAt
  have heq : (fun z => dualNorm h (cotangentChartInv y.1 z).1 (cotangentChartInv y.1 z).2 +
      b (cotangentChartInv y.1 z).1) =ᶠ[𝓝 p]
      (fun z => dualNormChart h y.1 z.1 z.2 + b (chartInv y.1 z.1)) := by
    filter_upwards [hopen.mem_nhds hp] with z hz
    rw [dualNorm_cotangentChartInv h y.1 hz]
    rfl
  change leviMatrix _ p cotangentDir = _
  rw [leviMatrix_congr_of_eventuallyEq heq cotangentDir, leviMatrix_add hn hbP cotangentDir,
    leviMatrix_fst hb2]
  rfl

theorem krf_symplecticP_dualNorm_add_base {X : KahlerManifold n}
    {g : HermitianField X.manifold} {h : ℝ → HermitianField X.manifold}
    (hh : IsKahlerRicciFlow g h) {t : ℝ} (ht : 0 ≤ t)
    (y : CotangentPoint X.manifold) (b : Pt X → ℝ)
    (hb : ContDiffAt ℝ ∞ (b ∘ chartInv y.1) (chartPt y.1 y.1)) :
    symplecticP (spatialHessian (fun y' => dualNorm (h t) y'.1 y'.2 + b y'.1) y) =
      derivWithin (fun τ => dualNorm (h τ) y.1 y.2) (Set.Ici 0) t + laplacian (h t) b y.1 := by
  have hs := metricFamilySmooth_slice hh.2.1 ht
  have hv : (normChartHessian (h t) y.1 (cotangentChart y.1 y)).toBlocks₂₂ᵀ =
      (gMat (h t) y.1)⁻¹ := by
    ext i j
    exact normChartHessian_vertical (h t) hs y.1 (p := cotangentChart y.1 y)
      (mem_extChartAt_target y.1) j i
  rw [spatialHessian_dualNorm_add_base (h t) hs y b hb, symplecticP_add_horizontal,
    hv, ← spatialHessian_dualNorm_eq_normChartHessian, krf_symplecticP_dualNorm hh ht y]
  congr 1
  exact congrArg Complex.re (Matrix.trace_mul_comm _ _)

end Yau.Blueprint.V04Proof.WallErrorAux
