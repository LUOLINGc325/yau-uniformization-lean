import Yau.Proofs.F01LocalScalarTimeHeat
import Yau.Proofs.F01LogDetTimeChart
import Yau.Proofs.F01LocalFlowTime
import Yau.Proofs.F01OrdinaryPullback
import Yau.Proofs.F01HeatChartNaturality

/-! The actual derivative of the global determinant quotient is
subcaloric on the genuine solution's open time slab. Every local jet is
transported from that same scalar and the original potential equation. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology Manifold
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem flow_potential_hMat_hasDerivAt
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {I : Set ℝ} (hI : IsOpen I) (hU : SmoothSpaceTime U I)
    (hpot : ∀ s ∈ I, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ I → HasDerivAt (U x)
      (flowLogDetRatio α h x s) s)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    {t : ℝ} (ht : t ∈ I) (i j : Fin n) :
    HasDerivAt (fun s => hMat (h s) a z i j)
      (leviC (logDet (h t) a) z i j) t := by
  let e := ordinaryChart a
  have he := (ordinaryChart_contMDiffOn a).mdifferentiableOn (by simp)
  have hei := (ordinaryChart_inverse_contMDiffOn a).mdifferentiableOn (by simp)
  have hze : z ∈ e.source := by rw [ordinaryChart_source]; exact hz
  have hd := flow_potential_chart_matrix_hasDerivAt α hα h U hI hU hpot hpde e he hei hze ht i j
  have hcurve : (fun s => pullbackMatrix (h s) e z i j) = (fun s => hMat (h s) a z i j) := by
    funext s
    rw [ordinaryChart_pullbackMatrix (h s) a hz]
  rw [hcurve] at hd
  erw [ordinaryChart_logdet_levi (h t) a hz] at hd
  exact hd

theorem native_scalar_time_heat_nonpos
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {I : Set ℝ} (hI : IsOpen I) (hh : MetricFamilySmooth h I) (hU : SmoothSpaceTime U I)
    (hpot : ∀ s ∈ I, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ I → HasDerivAt (U x) (flowLogDetRatio α h x s) s)
    (x : M.Carrier) {t : ℝ} (ht : t ∈ I) :
    fieldHeatWithin h I (fun s y => flowLogDetTime α h I y s) x t ≤ 0 := by
  let H : ComplexVector n × ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun p => hMat (h p.2) x p.1
  let z0 := chartPt x x
  have hz0 : z0 ∈ chartTarget x := mem_extChartAt_target x
  have hS : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have hChart (z : ComplexVector n) (hz : z ∈ chartTarget x) (s : ℝ) (hs : s ∈ I) :
      flowLogDetTime α h I (chartInv x z) s = localMatrixLogDetTime H (z, s) := by
    rw [flowLogDetTime_chart_eq α h hI.uniqueDiffOn hh x hz hs,
      derivWithin_of_isOpen hI hs]
    rfl
  have hlocal := local_logdet_time_heat_nonpos H hS hI
    (fun i j => metricFamily_hMat_contDiffOn h hh x i j)
    (fun p hp => Yau.LeafProofs.L12Aux.hMat_posDef (h p.2) x p.1 hp.1)
    (fun z hz s hs i j => flow_potential_hMat_hasDerivAt α hα h U hI hU hpot hpde x hz hs i j)
    hz0 ht
  have hcenter : chartInv x z0 = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have htime : (fun s => flowLogDetTime α h I x s) =ᶠ[𝓝 t]
      (fun s => localMatrixLogDetTime H (z0, s)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    rw [← hcenter]
    exact hChart z0 hz0 s hs
  have hspace : inChart x (fun y => flowLogDetTime α h I y t) =ᶠ[𝓝 z0]
      (fun z => localMatrixLogDetTime H (z, t)) := by
    filter_upwards [hS.mem_nhds hz0] with z hz
    exact hChart z hz t ht
  unfold fieldHeatWithin laplacian levi
  rw [derivWithin_of_isOpen hI ht, htime.deriv_eq,
    Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq hspace]
  exact hlocal

end Yau.NodeProofs.F01Aux
