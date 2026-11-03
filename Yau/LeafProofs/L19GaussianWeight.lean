import Yau.LeafProofs.L19EndpointEnergySupport
import Yau.LeafProofs.L18

/-! Gaussian weights for the original induced metric.  The compact-test
integrability facts here do not use a heat-kernel mass or growth premise. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ContDiff ComplexOrder

namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual Gaussian in the original metric's distance. -/
def gaussianWeight (g : SmoothMetric M) (o : M.Carrier) (a : ℝ)
    (y : M.Carrier) : ℝ :=
  Real.exp (-(a * inducedDistance g.form o y ^ 2))

theorem gaussianProfile_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(a * s)))
      (-a * Real.exp (-(a * t))) t := by
  have h := (Real.hasDerivAt_exp (-a * t)).comp t
    ((hasDerivAt_id t).const_mul (-a))
  convert h using 1
  · funext s
    dsimp
    congr 1
    ring
  · ring

theorem gaussianProfile_deriv (a t : ℝ) :
    deriv (fun s : ℝ => Real.exp (-(a * s))) t =
      -a * Real.exp (-(a * t)) :=
  (gaussianProfile_hasDerivAt a t).deriv

theorem gaussianProfile_secondDeriv (a t : ℝ) :
    deriv (deriv (fun s : ℝ => Real.exp (-(a * s)))) t =
      a ^ 2 * Real.exp (-(a * t)) := by
  have hfun : deriv (fun s : ℝ => Real.exp (-(a * s))) =
      fun s => -a * Real.exp (-(a * s)) := funext (gaussianProfile_deriv a)
  rw [hfun]
  convert (gaussianProfile_hasDerivAt a t).const_mul (-a) |>.deriv using 1 <;> ring

theorem gaussianProfile_contDiffAt (a t : ℝ) :
    ContDiffAt ℝ 2 (fun s : ℝ => Real.exp (-(a * s))) t := by
  exact Real.contDiff_exp.contDiffAt.comp t
    (contDiffAt_const.mul contDiffAt_id).neg

theorem gaussianWeight_pos (g : SmoothMetric M) (o : M.Carrier)
    (a : ℝ) (y : M.Carrier) : 0 < gaussianWeight g o a y := by
  exact Real.exp_pos _

theorem gaussianWeight_le_one (g : SmoothMetric M) (o : M.Carrier)
    {a : ℝ} (ha : 0 ≤ a) (y : M.Carrier) :
    gaussianWeight g o a y ≤ 1 := by
  unfold gaussianWeight
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg ha (sq_nonneg _)))

theorem gaussianWeight_continuous (g : SmoothMetric M) (o : M.Carrier)
    (a : ℝ) : Continuous (gaussianWeight g o a) := by
  unfold gaussianWeight
  exact Real.continuous_exp.comp
    (continuous_const.mul ((continuous_distFrom g o).pow 2)).neg

theorem gaussianWeight_integrable_compact_test (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (a : ℝ) {ψ : M.Carrier → ℝ}
    (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun y => gaussianWeight g o a y * ψ y) μ := by
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  have hcont : Continuous (fun y => gaussianWeight g o a y * ψ y) :=
    (gaussianWeight_continuous g o a).mul (continuous_of_smoothFn hψ)
  exact hcont.integrable_of_hasCompactSupport hcψ.mul_left

/-- Locality makes the actual project Laplacian compactly supported whenever
the smooth input is. -/
theorem gaussian_laplacian_tsupport_subset (g : SmoothMetric M)
    {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ) :
    tsupport (laplacian g.form ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro q hq
  change laplacian g.form ψ q ≠ 0 at hq
  by_contra hnot
  have hlocal : ψ =ᶠ[𝓝 q] (fun _ => (0 : ℝ)) :=
    notMem_tsupport_iff_eventuallyEq.mp hnot
  have hchart := inChart_eventuallyEq hlocal
  have hdd : fderiv ℝ (fderiv ℝ (inChart q ψ)) (chartPt q q) = 0 := by
    have hd := hchart.fderiv (𝕜 := ℝ)
    rw [hd.fderiv_eq]
    change fderiv ℝ (fderiv ℝ (fun _ : ComplexVector n => (0 : ℝ)))
      (chartPt q q) = 0
    simp
  have hc2 : ContDiffAt ℝ 2 (inChart q ψ) (chartPt q q) :=
    ((hψ q).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) q).mem_nhds
        (mem_extChartAt_target q))).of_le (by simp)
  have hprincipal := principal_realLaplacian_eq_twice_traceWith g.form q
    (mem_extChartAt_target q) hc2
  change fderiv ℝ (fderiv ℝ (inChart q ψ))
    ((extChartAt (ComplexModel n) q) q) = 0 at hdd
  rw [hdd] at hprincipal
  simp at hprincipal
  change laplacian g.form ψ q = 0 at hprincipal
  exact hq hprincipal

theorem gaussianWeight_integrable_laplacian_test (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (a : ℝ) {ψ : M.Carrier → ℝ}
    (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun y => gaussianWeight g o a y * laplacian g.form ψ y) μ := by
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  have hclap : HasCompactSupport (laplacian g.form ψ) :=
    hcψ.of_isClosed_subset (isClosed_tsupport _)
      (gaussian_laplacian_tsupport_subset g hψ)
  have hcont : Continuous (fun y => gaussianWeight g o a y * laplacian g.form ψ y) :=
    (gaussianWeight_continuous g o a).mul
      (continuous_of_smoothFn (smoothFn_laplacian g hψ))
  exact hcont.integrable_of_hasCompactSupport hclap.mul_left

/-- A local lower test for the Gaussian, expressed in the actual physical
orthonormal frame.  The trace is the real Laplacian, twice the project's
complex scalar Laplacian. -/
def GaussianLowerSupport (g : SmoothMetric M) (o : M.Carrier)
    (a : ℝ) (q : M.Carrier) : Prop :=
  letI := underlyingRealTangentNormedAddCommGroup g.form q
  letI := underlyingRealTangentInnerProductSpace g.form q
  ∃ S : M.Carrier → ℝ,
    ∃ b : OrthonormalBasis (Fin (2 * n)) ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) q),
      ContDiffAt ℝ 2 (S ∘ chartInv q) (chartPt q q) ∧
      S q = gaussianWeight g o a q ∧
      (∀ᶠ y in 𝓝 q, S y ≤ gaussianWeight g o a y) ∧
      -(4 * (2 * n : ℕ) * a) * gaussianWeight g o a q ≤
        endpointFrameHessianTrace g q b (S ∘ chartInv q) (chartPt q q)

/-- The actual minimizing midpoint support gives the Gaussian's local
viscosity lower bound, including at the distance center and cut locus. -/
theorem exists_gaussianLowerSupport (g : SmoothMetric M)
    (hK : IsKahler g) (hR : ∀ z, (ricci g.form z).PosSemidef)
    (o : M.Carrier) {a : ℝ} (ha : 0 ≤ a) (q : M.Carrier) :
    GaussianLowerSupport g o a q := by
  obtain ⟨F, b, hF, hval, hupper, hgrad, htrace⟩ :=
    exists_realDistanceSquareUpperSupport g hK hR o q
  let S : M.Carrier → ℝ := fun y => Real.exp (-(a * F y))
  let z := chartPt q q
  have hinv : chartInv q z = q :=
    (extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q)
  have hprofile : ContDiffAt ℝ 2
      (fun t : ℝ => Real.exp (-(a * t))) ((F ∘ chartInv q) z) := by
    simpa only [Function.comp_apply, hinv] using gaussianProfile_contDiffAt a (F q)
  have hS : ContDiffAt ℝ 2 (S ∘ chartInv q) z := by
    exact hprofile.comp z hF
  have hcontact : S q = gaussianWeight g o a q := by
    simp only [S, gaussianWeight, hval]
  have hlower : ∀ᶠ y in 𝓝 q, S y ≤ gaussianWeight g o a y := by
    filter_upwards [hupper] with y hy
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hy ha))
  have htraceS : endpointFrameHessianTrace g q b (S ∘ chartInv q) z =
      (-a * gaussianWeight g o a q) *
        endpointFrameHessianTrace g q b (F ∘ chartInv q) z +
      (a ^ 2 * gaussianWeight g o a q) *
        endpointFrameGradientSq q b (F ∘ chartInv q) z := by
    change endpointFrameHessianTrace g q b
      ((fun t : ℝ => Real.exp (-(a * t))) ∘ (F ∘ chartInv q)) z = _
    rw [endpointFrameHessianTrace_scalar_comp g q b hF hprofile,
      Function.comp_apply, hinv, gaussianProfile_deriv,
      gaussianProfile_secondDeriv]
    dsimp only [z]
    simp only [gaussianWeight, hval]
  refine ⟨S, b, hS, hcontact, hlower, ?_⟩
  rw [htraceS]
  have hW : 0 ≤ gaussianWeight g o a q := (gaussianWeight_pos g o a q).le
  have hneg : -a * gaussianWeight g o a q ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hW
  have hbase := mul_le_mul_of_nonpos_left htrace hneg
  have hquad : 0 ≤ (a ^ 2 * gaussianWeight g o a q) *
      endpointFrameGradientSq q b (F ∘ chartInv q) z := by
    rw [hgrad]
    positivity
  dsimp only [z] at hbase hquad ⊢
  nlinarith

/-- The local, metric-specific hypothesis of a standard viscosity-to-weak
transfer.  Its tests are genuine C² germs; this definition contains no
integral conclusion. -/
def HasPhysicalLowerSupports (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (c : ℝ) : Prop :=
  ∀ q : M.Carrier,
    letI := underlyingRealTangentNormedAddCommGroup g.form q
    letI := underlyingRealTangentInnerProductSpace g.form q
    ∃ S : M.Carrier → ℝ,
      ∃ b : OrthonormalBasis (Fin (2 * n)) ℝ
        (TangentSpace 𝓘(ℝ, ComplexVector n) q),
        ContDiffAt ℝ 2 (S ∘ chartInv q) (chartPt q q) ∧
        S q = f q ∧ (∀ᶠ y in 𝓝 q, S y ≤ f y) ∧
        2 * c * f q ≤
          endpointFrameHessianTrace g q b (S ∘ chartInv q) (chartPt q q)

theorem gaussianWeight_hasPhysicalLowerSupports (g : SmoothMetric M)
    (hK : IsKahler g) (hR : ∀ z, (ricci g.form z).PosSemidef)
    (o : M.Carrier) {a : ℝ} (ha : 0 ≤ a) :
    HasPhysicalLowerSupports g (gaussianWeight g o a)
      (-(2 * (2 * n : ℕ) * a)) := by
  intro q
  obtain ⟨S, b, hS, hcontact, hlower, htrace⟩ :=
    exists_gaussianLowerSupport g hK hR o ha q
  refine ⟨S, b, hS, hcontact, hlower, ?_⟩
  convert htrace using 1 <;> ring

/-- The one missing analytic transfer has a geometry-independent statement:
local C² lower supports for the physical real trace imply the distributional
complex Laplacian inequality for compact smooth tests.  It is kept as an
explicit proposition, not an axiom or a field on the heat kernel. -/
def PhysicalLowerSupportToWeakGap (g : SmoothMetric M)
    (μ : Measure M.Carrier) : Prop :=
  IsKahler g → IsRiemannianVolume g.form μ →
    ∀ (f : M.Carrier → ℝ) (c : ℝ), Continuous f →
      HasPhysicalLowerSupports g f c →
      ∀ (ψ : M.Carrier → ℝ), SmoothFn ψ → HasCompactSupport ψ →
        (∀ y, 0 ≤ ψ y) →
        Integrable (fun y => f y * laplacian g.form ψ y) μ →
        Integrable (fun y => f y * ψ y) μ →
        c * (∫ y, f y * ψ y ∂μ) ≤
          ∫ y, f y * laplacian g.form ψ y ∂μ

/-- Honest conditional assembly of the Gaussian lower bound obtained from
the already proved midpoint support.  The midpoint construction yields the
dimension-only coefficient `4n`; the sharper `2n` requires the independent
radial Jacobian calculation across the cut locus. -/
theorem gaussianWeight_weak_laplacian_of_transfer
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (htransfer : PhysicalLowerSupportToWeakGap g μ)
    (o : M.Carrier) {a : ℝ} (ha : 0 ≤ a)
    {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (hcψ : HasCompactSupport ψ) (hψnonneg : ∀ y, 0 ≤ ψ y) :
    (-(2 * (2 * n : ℕ) * a)) *
      (∫ y, gaussianWeight g o a y * ψ y ∂μ) ≤
      ∫ y, gaussianWeight g o a y * laplacian g.form ψ y ∂μ :=
  htransfer hK hμ _ _ (gaussianWeight_continuous g o a)
    (gaussianWeight_hasPhysicalLowerSupports g hK hR o ha)
    ψ hψ hcψ hψnonneg
    (gaussianWeight_integrable_laplacian_test g μ hμ o a hψ hcψ)
    (gaussianWeight_integrable_compact_test g μ hμ o a hψ hcψ)

end Yau.LeafProofs.L19Aux
