import Yau.Proofs.C05GeometricNearMinimumFrame
import Yau.Proofs.C05TaylorSequenceBounds

/-! A local third-jet bound and nonnegativity give the genuine finite-step estimate. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05GeometricNearMinimumAux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.Proofs.C05GeodesicScalarJetsAux Yau.Proofs.C05TaylorSequenceAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem unit_geodesic_second_lower (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
    (hp : realTangentEnergy g.form p = 1) {r J h : ℝ} (hr : 0 < r)
    (hB3 : ∀ x ∈ distBall g.form p.proj r, scalarJetNorm g.form f 3 x ≤ J)
    (hnonneg : ∀ x ∈ distBall g.form p.proj r, 0 ≤ f x)
    (hh : 0 < h) (hhr : h < r) :
    -2 * f p.proj / h^2 - J*h/3 ≤
      realHess g.form f p.proj (realTangentEquiv p.proj p.2)
        (realTangentEquiv p.proj p.2) := by
  have hmem (t : ℝ) (ht : t ∈ Set.Ioo (-r) r) :
      (realGeodesicFlow g p t).proj ∈ distBall g.form p.proj r := by
    rw [mem_distBall_iff g _ _ hr]
    have hd := realGeodesicFlow_distFrom_le g p t
    rw [hp, Real.sqrt_one, one_mul] at hd
    exact hd.trans_lt (abs_lt.mpr ht)
  have hthird (t : ℝ) (ht : t ∈ Set.Ioo (-r) r) :
      |iteratedDeriv 3 (geodesicScalar g f p) t| ≤ J := by
    have H := geodesicScalar_third_abs_le g f hf p t
    rw [hp, Real.sqrt_one, one_pow, mul_one] at H
    exact H.trans (hB3 _ (hmem t ht))
  have H := second_deriv_zero_lower (geodesicScalar g f p) hr
    (((geodesicScalar_contDiff g f hf p).of_le (by simp)).contDiffOn)
    (fun t ht => hnonneg _ (hmem t ht)) hthird hh hhr
  rw [geodesicScalar_iteratedDeriv_two g f hf p 0] at H
  simp only [geodesicScalar] at H
  rw [realGeodesicFlow_zero] at H
  exact H

theorem laplacian_finite_step_lower (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (o : M.Carrier) {r J h : ℝ} (hr : 0 < r)
    (hB3 : ∀ x ∈ distBall g.form o r, scalarJetNorm g.form f 3 x ≤ J)
    (hnonneg : ∀ x ∈ distBall g.form o r, 0 ≤ f x)
    (hh : 0 < h) (hhr : h < r) :
    -(n : ℝ) * (2*f o/h^2 + J*h/3) ≤ laplacian g.form f o := by
  let G := realMetricFn g.form o (chartPt o o)
  obtain ⟨D,hD,hGram⟩ := inverseMetric_exists_orthonormal_factor G
    (realMetricFn_posDef g.form o (chartPt o o) (mem_extChartAt_target o))
  have hj (j : RIdx n) :
      -(2*f o/h^2 + J*h/3) ≤
        realHess g.form f o (realTangentEquiv o (framePhase o D j).2)
          (realTangentEquiv o (framePhase o D j).2) := by
    have H := unit_geodesic_second_lower g f hf (framePhase o D j)
      (framePhase_energy g o D hGram j) hr hB3 hnonneg hh hhr
    dsimp only [framePhase] at H ⊢
    convert H using 1 <;> ring
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hj j)
  have hc : Fintype.card (RIdx n) = 2*n := by simp [RIdx, Nat.mul_comm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc,
    Nat.cast_mul, Nat.cast_ofNat] at hs
  rw [laplacian_frame_trace g f hf o D hD]
  linarith

end Yau.Proofs.C05GeometricNearMinimumAux
