import Yau.Proofs.F01SpatialLeviJetLimit
import Yau.Proofs.F01SpatialDilationLevi
import Yau.Proofs.F01ChartMatrixRecovery
import Yau.Proofs.F01ScalarChartSmooth
import Yau.LeafProofs.L17UniformCharts

/-! Actual normalized chart second-jet convergence gives convergence
of the native Levi tensor. The fixed chart Jacobian is computed and
inverted; its frame is not supplied as an extra realization. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem leviC_normalized_spatial_dilation_zero
    (q : Space n → ℝ) {σ : ℝ} (hσ : σ ≠ 0) (hq : ContDiffAt ℝ 2 q 0) :
    leviC (fun z => (σ ^ 2)⁻¹ * q (σ • z)) 0 = leviC q 0 := by
  have hAt : ContDiffAt ℝ 2 q (σ • (0 : Space n)) := by simpa only [smul_zero] using hq
  have hD : ContDiffAt ℝ 2 (fun z : Space n => σ • z) 0 :=
    (σ • ContinuousLinearMap.id ℝ (Space n)).contDiff.contDiffAt
  have hComp : ContDiffAt ℝ 2 (fun z : Space n => q (σ • z)) 0 := hAt.comp 0 hD
  rw [leviC_const_mul hComp ((σ ^ 2)⁻¹), leviC_spatial_dilation hAt,
    smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 2 hσ), Complex.ofReal_one, one_smul, smul_zero]

theorem native_levi_limit_of_scaled_chart_second_jets
    (g : HermitianField M) (A : BoundedChartFamily g)
    (f : ℕ → M.Carrier → ℝ) (u : M.Carrier → ℝ)
    (hf : ∀ m, SmoothFn (f m)) (hu : SmoothFn u)
    {σ : ℝ} (hσ : σ ≠ 0) (a : M.Carrier)
    (hJet : Tendsto
      (fun m => iteratedFDeriv ℝ 2 (fun z => (σ ^ 2)⁻¹ * f m ((A.chart a) (σ • z))) 0)
      atTop (𝓝 (iteratedFDeriv ℝ 2 (fun z => (σ ^ 2)⁻¹ * u ((A.chart a) (σ • z))) 0))) :
    Tendsto (fun m => levi (f m) a) atTop (𝓝 (levi u a)) := by
  classical
  let e := A.chart a
  have hz : (0 : Space n) ∈ e.source :=
    A.closedBall_source a (mem_closedBall_self A.radius_pos.le)
  have hChart (q : M.Carrier → ℝ) (hq : SmoothFn q) :
      ContDiffAt ℝ 2 (fun z => q (e z)) 0 :=
    ((smoothFn_comp_holomorphic_chart q hq e (A.differentiable a)).contDiffAt
      (e.open_source.mem_nhds hz)).of_le (by simp)
  have hScaled (q : M.Carrier → ℝ) (hq : SmoothFn q) :
      ContDiffAt ℝ 2 (fun z => (σ ^ 2)⁻¹ * q (e (σ • z))) 0 := by
    have hD : ContDiffAt ℝ 2 (fun z : Space n => σ • z) 0 :=
      (σ • ContinuousLinearMap.id ℝ (Space n)).contDiff.contDiffAt
    have hAt : ContDiffAt ℝ 2 (fun z => q (e z)) (σ • (0 : Space n)) :=
      by simpa only [smul_zero] using hChart q hq
    exact contDiffAt_const.mul (hAt.comp 0 hD)
  have hEntry (i j : Fin n) := spatial_levi_entry_limit_of_second_jets
    (fun m z => (σ ^ 2)⁻¹ * f m (e (σ • z))) (fun z => (σ ^ 2)⁻¹ * u (e (σ • z))) 0
    (fun m => hScaled (f m) (hf m)) (hScaled u hu) hJet i j
  have hScaleLevi (q : M.Carrier → ℝ) (hq : SmoothFn q) :
      leviC (fun z => (σ ^ 2)⁻¹ * q (e (σ • z))) 0 = leviC (fun z => q (e z)) 0 :=
    leviC_normalized_spatial_dilation_zero (fun z => q (e z)) hσ (hChart q hq)
  have hFScale (m : ℕ) := hScaleLevi (f m) (hf m)
  have hLevi : Tendsto (fun m => leviC (fun z => f m (e z)) 0) atTop
      (𝓝 (leviC (fun z => u (e z)) 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [hFScale, hScaleLevi _ hu] using hEntry i j
  let J := linearMatrix (coordinateDifferential e (e 0) 0)
  have hDet : J.det ≠ 0 := linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e (A.differentiable a) (A.inverse_differentiable a)
      (e 0) hz (mem_extChartAt_source (e 0)))
  have hInv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J (isUnit_iff_ne_zero.mpr hDet)
  have hStar : (J⁻¹)ᴴ * Jᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hInv, Matrix.conjTranspose_one]
  have hRecover (q : M.Carrier → ℝ) (hq : SmoothFn q) :
      levi q a = (J⁻¹)ᴴ * leviC (fun z => q (e z)) 0 * J⁻¹ := by
    rw [leviC_holomorphic_chart q hq e (A.differentiable a) hz]
    change levi q a = (J⁻¹)ᴴ * (Jᴴ * levi q (e 0) * J) * J⁻¹
    rw [show e 0 = a from A.center a]
    calc
      _ = ((J⁻¹)ᴴ * Jᴴ) * levi q a * (J * J⁻¹) := by rw [hStar, hInv]; simp
      _ = _ := by noncomm_ring
  have hh : Tendsto (fun m => (J⁻¹)ᴴ * leviC (fun z => f m (e z)) 0 * J⁻¹) atTop
      (𝓝 ((J⁻¹)ᴴ * leviC (fun z => u (e z)) 0 * J⁻¹)) :=
    (tendsto_const_nhds.mul hLevi).mul tendsto_const_nhds
  have hSeq : (fun m => levi (f m) a) =
      (fun m => (J⁻¹)ᴴ * leviC (fun z => f m (e z)) 0 * J⁻¹) :=
    funext (fun m => hRecover (f m) (hf m))
  rw [hSeq, hRecover u hu]
  exact hh

end Yau.NodeProofs.F01Aux
