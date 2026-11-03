import Yau.Proofs.F01AffinePotentialNormalization
import Yau.Proofs.F01NormalizedInitialPotential

/-! The actual native potential and affine background on a shifted
positive-time chart. The transformed matrix is identified with the same
native flow, without initial zero data or a replacement matrix field. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def chartAffineBackground (A : BoundedChartFamily g) (a : M.Carrier) (p : Point n) :
    Matrix (Fin n) (Fin n) ℂ :=
  pullbackMatrix g (A.chart a) p.1 - (p.2 : ℂ) • backgroundRicci (pullbackMatrix g (A.chart a)) p.1

def shiftedComplexBackground (A : BoundedChartFamily g) (a : M.Carrier) (ρ τ : ℝ) :
    Point n → Matrix (Fin n) (Fin n) ℂ :=
  fun p => chartAffineBackground A a (affineParabolicPoint ρ 0 τ p)

def shiftedNativePotential (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ)
    (a : M.Carrier) (ρ τ : ℝ) : Point n → ℝ :=
  affineParabolicPotential ρ 0 τ (fun p : Point n => U (A.chart a p.1) p.2)

theorem shifted_clock_maps {ρ τ T : ℝ} (hLower : ρ ^ 2 ≤ τ) (hUpper : τ + ρ ^ 2 ≤ T) :
    MapsTo (fun t : ℝ => τ + ρ ^ 2 * t) (Icc (-1) 1) (Icc 0 T) := by
  intro t ht
  have hl := mul_le_mul_of_nonneg_left ht.1 (sq_nonneg ρ)
  have hu := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg ρ)
  constructor <;> nlinarith

theorem shifted_space_maps (A : BoundedChartFamily g) {ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) :
    MapsTo (fun z : Space n => ρ • z + 0) (ball 0 1) (ball 0 A.radius) := by
  intro z hz
  simpa only [add_zero] using spatialDilation_mem_ball hρ hρr hz

theorem shifted_native_potential_smooth (A : BoundedChartFamily g)
    (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ + ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (shiftedNativePotential A U a ρ τ) (cylinder (ball 0 1) (-1) 1) := by
  have hMap : MapsTo (affineParabolicPoint ρ (0 : Space n) τ)
      (cylinder (ball 0 1) (-1) 1) (ball 0 A.radius ×ˢ Icc 0 T) :=
    fun p hp => ⟨shifted_space_maps A hρ hρr hp.1, shifted_clock_maps hLower hUpper hp.2⟩
  have hAffine : ContDiff ℝ ∞ (affineParabolicPoint (n := n) ρ 0 τ) := by
    unfold affineParabolicPoint
    fun_prop
  exact contDiffOn_const.mul ((bounded_chart_spaceTime_smooth A hU a).comp hAffine.contDiffOn hMap)

theorem shifted_native_flow_matrix
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ + ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) {p : Point n} (hp : p ∈ cylinder (ball 0 1) (-1) 1) :
    chartPotentialMatrix (shiftedComplexBackground A a ρ τ) (shiftedNativePotential A U a ρ τ) p =
      pullbackMatrix (h (affineParabolicPoint ρ 0 τ p).2) (A.chart a)
        (affineParabolicPoint ρ 0 τ p).1 := by
  have hT : 0 < T := by nlinarith [sq_pos_of_pos hρ]
  have hF := closed_slab_parabolic_C2 isOpen_ball (uniqueDiffOn_Icc hT)
    (bounded_chart_spaceTime_smooth A hU a)
  have hSpace := shifted_space_maps A hρ hρr
  have hClock := shifted_clock_maps hLower hUpper
  change chartPotentialMatrix
    (fun q => chartAffineBackground A a (affineParabolicPoint ρ 0 τ q))
    (affineParabolicPotential ρ 0 τ (fun q : Point n => U (A.chart a q.1) q.2)) p = _
  rw [chartPotentialMatrix_affineParabolicPotential (chartAffineBackground A a) hρ.ne'
    (by norm_num : (-1 : ℝ) < 1) hF hSpace hClock hp]
  have hq : affineParabolicPoint ρ (0 : Space n) τ p ∈ ball 0 A.radius ×ˢ Icc 0 T :=
    ⟨hSpace hp.1, hClock hp.2⟩
  have hz := A.closedBall_source a (ball_subset_closedBall hq.1)
  exact (flow_potential_matrix_in_chart g (h (affineParabolicPoint ρ 0 τ p).2) hg
    (fun x => U x (affineParabolicPoint ρ 0 τ p).2) (smoothSpaceTime_slice hU hq.2)
    (affineParabolicPoint ρ 0 τ p).2 (hpot _ hq.2) (A.chart a)
    (A.differentiable a) (A.inverse_differentiable a) hz).symm

end Yau.NodeProofs.F01Aux
