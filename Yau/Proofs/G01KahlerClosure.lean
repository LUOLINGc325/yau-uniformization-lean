import Yau.LeafProofs.L23FieldMetricConnection

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs L12Aux

/-- The actual chart Kähler bilinear form is smooth from coefficient smoothness. -/
theorem chartKahlerBilin_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartKahlerBilin h x) (chartTarget x) :=
  (L23Aux.realMetricInChart_smooth h hs x).clm_comp contDiffOn_const

theorem fderiv_chartKahlerBilin_realVec {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    fderiv ℝ (chartKahlerBilin h x) z (realVec a) (realVec b) (realVec c) =
      rDeriv (fun t => kahlerFormFn h x t b c) z a := by
  have hB : DifferentiableAt ℝ (chartKahlerBilin h x) z :=
    ((chartKahlerBilin_contDiffOn h hs x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun t => chartKahlerBilin h x t (realVec b) (realVec c)) =ᶠ[𝓝 z]
      (fun t => kahlerFormFn h x t b c) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with t ht
    exact chartKahlerBilin_realVec h x ht b c
  rw [← fderiv_bilin_apply_const hB]
  exact congrArg (fun A => A (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))

-- Source: L18Aux.cyclic_chartKahlerBilin_center → L12Aux.cyclic_chartKahlerBilin_center
set_option synthInstance.maxHeartbeats 80000 in
theorem cyclic_chartKahlerBilin_center {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier) (u v w : ComplexVector n) :
    fderiv ℝ (chartKahlerBilin h x) (chartPt x x) u v w +
      fderiv ℝ (chartKahlerBilin h x) (chartPt x x) v w u +
      fderiv ℝ (chartKahlerBilin h x) (chartPt x x) w u v = 0 := by
  apply cyclic_trilinear_zero_of_basis (realVec_basis n)
    (fderiv ℝ (chartKahlerBilin h x) (chartPt x x)) _ u v w
  intro a b c
  simp only [realVec_basis_apply]
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [fderiv_chartKahlerBilin_realVec h hs x hz,
    fderiv_chartKahlerBilin_realVec h hs x hz,
    fderiv_chartKahlerBilin_realVec h hs x hz]
  exact hk x a b c

-- Source: L18Aux.cyclic_chartKahlerBilin_on → L12Aux.cyclic_chartKahlerBilin_on
theorem cyclic_chartKahlerBilin_on {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (u v w : ComplexVector n) :
    fderiv ℝ (chartKahlerBilin h x) z u v w +
      fderiv ℝ (chartKahlerBilin h x) z v w u +
      fderiv ℝ (chartKahlerBilin h x) z w u v = 0 := by
  let y := chartInv x z
  let T : ComplexVector n → ComplexVector n := fun t => chartPt y (chartInv x t)
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) y).source := mem_extChartAt_source y
  have ht : T z ∈ chartTarget y := mem_extChartAt_target y
  have hT : ContDiffAt ℝ 2 T z :=
    ((chartTransition_contDiffAt x y hz hy).restrict_scalars ℝ).of_le (by simp)
  have hBx : DifferentiableAt ℝ (chartKahlerBilin h x) z :=
    ((chartKahlerBilin_contDiffOn h hs x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hBy : DifferentiableAt ℝ (chartKahlerBilin h y) (T z) :=
    ((chartKahlerBilin_contDiffOn h hs y).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds ht)).differentiableAt (by simp)
  have hskew (p q : ComplexVector n) :
      chartKahlerBilin h y (T z) p q = -chartKahlerBilin h y (T z) q p :=
    chartKahlerBilin_skew h y ht p q
  have hi : ContinuousAt (chartInv x) z := continuousAt_extChartAt_symm'' hz
  have hsource : ∀ᶠ t in 𝓝 z, chartInv x t ∈ (extChartAt (ComplexModel n) y).source :=
    hi.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds hy)
  have hpull (p q : ComplexVector n) :
      (fun t => chartKahlerBilin h x t p q) =ᶠ[𝓝 z]
        (fun t => chartKahlerBilin h y (T t) (fderiv ℝ T t p) (fderiv ℝ T t q)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz, hsource]
      with t htx hty
    exact chartKahlerBilin_pullback h x y htx hty p q
  have hderiv (p q r : ComplexVector n) :
      fderiv ℝ (chartKahlerBilin h x) z p q r =
        fderiv ℝ (fun t => chartKahlerBilin h y (T t)
          (fderiv ℝ T t q) (fderiv ℝ T t r)) z p := by
    rw [← fderiv_bilin_apply_const hBx]
    exact congrArg (fun A => A p) ((hpull q r).fderiv_eq (𝕜 := ℝ))
  rw [hderiv u v w, hderiv v w u, hderiv w u v]
  exact (cyclic_derivative_pullback_bilin hT hBy hskew u v w).trans
    (cyclic_chartKahlerBilin_center h hs hk y
      (fderiv ℝ T z u) (fderiv ℝ T z v) (fderiv ℝ T z w))

-- Source: L18Aux.kahlerClosed_in_chart → L12Aux.kahlerClosed_in_chart
theorem kahlerClosed_in_chart {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    rDeriv (fun t => kahlerFormFn h x t b c) z a +
      rDeriv (fun t => kahlerFormFn h x t c a) z b +
      rDeriv (fun t => kahlerFormFn h x t a b) z c = 0 := by
  have hc := cyclic_chartKahlerBilin_on h hs hk x hz (realVec a) (realVec b) (realVec c)
  rw [fderiv_chartKahlerBilin_realVec h hs x hz,
    fderiv_chartKahlerBilin_realVec h hs x hz, fderiv_chartKahlerBilin_realVec h hs x hz] at hc
  exact hc


end Yau.NodeProofs.G01Aux
