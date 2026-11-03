import Yau.Proofs.V03DiscScalars
import Yau.Proofs.V03LeviChain
import Yau.Proofs.P02PlanarComparison

/-! The exact centered dual-Levi inequality implies the actual circle mean on cotangent discs.
This is an explicit conditional transport lemma; the centered Chern inequality remains separate. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ}

theorem initial_disc_mean_of_centered_dual_levi_nonneg
    (X : KahlerManifold n)
    (hcentral : ∀ (x : Pt X) (ξ : ComplexVector n) (v : CotangentCoord n),
      0 ≤ (wirt (fun p => wirtBar (fun q => (dualNormChart X.metric.form x q.1 q.2 : ℂ)) p v)
        (chartPt x x, ξ) v).re)
    (f : ℂ → Pt X) (ξd : ℂ → Covector n) (hd : IsCotangentDisc f ξd) :
    dualNorm X.metric.form (f 0) (ξd 0) ≤ circleAverage (fun θ =>
      dualNorm X.metric.form (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))) := by
  let N : ℂ → ℝ := fun ζ => dualNorm X.metric.form (f ζ) (ξd ζ)
  have hN : ContDiffOn ℝ ∞ N (Metric.closedBall 0 1) :=
    cotangentDisc_dualNorm_contDiffOn X.metric (f := fun ζ => (f ζ, ξd ζ)) hd
  apply P02Aux.planar_submean_of_lower_supports N hN.continuousOn
  intro a ha
  have han : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 a := Metric.closedBall_mem_nhds_of_mem ha
  have hac : a ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall ha
  have hNa : ContDiffAt ℝ 2 N a := ((hN a hac).contDiffAt han).of_le (by simp)
  let x : Pt X := f a
  let T : ℂ → CotangentCoord n := fun ζ => cotangentChart x (f ζ, ξd ζ)
  have hT : ContDiffAt ℂ 2 T a :=
    ((cotangentDisc_centeredCoords_contDiffWithinAt (f := fun ζ => (f ζ, ξd ζ)) hd hac).contDiffAt han).of_le (by simp)
  have htarget : T a ∈ cotangentTarget x :=
    cotangentChart_mapsTo x (mem_extChartAt_source x)
  have htargetOpen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hQ : ContDiffAt ℝ 2 (fun q : CotangentCoord n => dualNormChart X.metric.form x q.1 q.2) (T a) :=
    ((dualNormChart_contDiffOn X.metric x).contDiffAt (htargetOpen.mem_nhds htarget)).of_le (by simp)
  have hfAt : ContinuousAt f a := (hd.1 a hac).continuousWithinAt.continuousAt han
  have hsource : ∀ᶠ ζ in 𝓝 a, f ζ ∈ (extChartAt (ComplexModel n) x).source :=
    hfAt.eventually ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds (mem_extChartAt_source x))
  have hlocal : N =ᶠ[𝓝 a] (fun ζ => dualNormChart X.metric.form x (T ζ).1 (T ζ).2) := by
    filter_upwards [hsource] with ζ hζ
    exact dualNorm_eq_fixed_chart X.metric.form x (f ζ) hζ (ξd ζ)
  have hlocalC : (fun ζ => (N ζ : ℂ)) =ᶠ[𝓝 a]
      (fun ζ => (dualNormChart X.metric.form x (T ζ).1 (T ζ).2 : ℂ)) :=
    hlocal.mono (fun _ hh => congrArg Complex.ofReal hh)
  have hmix : 0 ≤ (wirt (fun y => wirtBar (fun y' => (N y' : ℂ)) y 1) a 1).re := by
    rw [mixedWirt_congr hlocalC 1 1, mixedWirt_holomorphic_comp_re hT hQ]
    exact hcentral x (T a).2 (fderiv ℂ T a 1)
  have hfactor := mixedWirt_real_diagonal hNa (1 : ℂ)
  have htrace : 0 ≤ P02Aux.planarTrace N a := by
    simp only [smul_eq_mul, mul_one] at hfactor
    change _ = (1 / 4 : ℝ) * P02Aux.planarTrace N a at hfactor
    linarith
  exact ⟨N, hNa, rfl, Eventually.of_forall (fun _ => le_rfl), htrace⟩

end Yau.NodeProofs.E01Aux
