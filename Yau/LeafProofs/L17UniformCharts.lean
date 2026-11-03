import Yau.LeafProofs.L17RicciNaturality
import Yau.LeafProofs.L23FieldMetric

/-!
The original all-orders bounded-geometry witnesses, with their actual chart
frames and uniform quadratic bounds. No covering or flow is supplied as data.
-/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

structure BoundedChartFamily (g : HermitianField M) where
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℕ → ℝ
  bound_pos : ∀ k, 0 < bound k
  chart : M.Carrier → OpenPartialHomeomorph (ComplexVector n) M.Carrier
  center : ∀ p, chart p 0 = p
  closedBall_source : ∀ p, closedBall 0 radius ⊆ (chart p).source
  differentiable : ∀ p,
    MDifferentiableOn (ComplexModel n) (ComplexModel n) (chart p) (chart p).source
  inverse_differentiable : ∀ p,
    MDifferentiableOn (ComplexModel n) (ComplexModel n) (chart p).symm (chart p).target
  comparison : ∀ p z, z ∈ ball 0 radius →
    (pullbackMatrix g (chart p) z - ((bound 0)⁻¹ : ℂ) • 1).PosSemidef ∧
    ((bound 0 : ℂ) • 1 - pullbackMatrix g (chart p) z).PosSemidef
  coefficient_smooth : ∀ p i j,
    ContDiffOn ℝ ∞ (fun z => pullbackMatrix g (chart p) z i j) (ball 0 radius)
  coefficient_bound : ∀ p k z, z ∈ ball 0 radius → ∀ i j,
    ‖iteratedFDeriv ℝ k (fun w => pullbackMatrix g (chart p) w i j) z‖ ≤ bound k

theorem exists_boundedChartFamily (g : HermitianField M)
    (hbg : LeafCandidates.HermitianBoundedGeometry g) :
    Nonempty (BoundedChartFamily g) := by
  classical
  obtain ⟨r, hr, C, hC, h⟩ := hbg
  choose e hcenter hsource he hei hcomp hsmooth hbound using h
  exact ⟨⟨r, hr, C, hC, e, hcenter, hsource, he, hei, hcomp, hsmooth, hbound⟩⟩

theorem chart_real_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source) :
    letI := L12Aux.manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ e e.source := by
  let := L12Aux.manifold_realSmooth M
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_target]
  refine ⟨e.continuousOn.continuousAt (e.open_source.mem_nhds hz), ?_⟩
  rw [contMDiffAt_iff_contDiffAt]
  have hU := (forwardChartDomain_isOpen e (e z)).mem_nhds
    ⟨hz, mem_extChartAt_source (e z)⟩
  exact (forwardChart_real_contDiffOn e he (e z)).contDiffAt hU

theorem inverse_chart_real_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target) :
    letI := L12Aux.manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ e.symm e.target := by
  let := L12Aux.manifold_realSmooth M
  intro y hy
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ,
    contMDiffAt_iff_contDiffAt]
  have hmem : chartPt y y ∈ inverseChartDomain e y := by
    refine ⟨mem_extChartAt_target y, ?_⟩
    change chartInv y (chartPt y y) ∈ e.target
    have heq : chartInv y (chartPt y y) = y :=
      (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
    rwa [heq]
  exact (inverseChart_real_contDiffOn e hei y).contDiffAt
    ((inverseChartDomain_isOpen e y).mem_nhds hmem)

theorem complex_quadratic_one (u : ComplexVector n) :
    star (WithLp.ofLp u) ⬝ᵥ WithLp.ofLp u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  convert! h using 1; norm_cast

theorem matrix_quadratic_comparison
    {G : Matrix (Fin n) (Fin n) ℂ} {C : ℝ}
    (hlo : (G - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef)
    (hhi : ((C : ℂ) • 1 - G).PosSemidef) (u : ComplexVector n) :
    C⁻¹ * ‖u‖ ^ 2 ≤ (star (WithLp.ofLp u) ⬝ᵥ (G *ᵥ WithLp.ofLp u)).re ∧
    (star (WithLp.ofLp u) ⬝ᵥ (G *ᵥ WithLp.ofLp u)).re ≤ C * ‖u‖ ^ 2 := by
  have hl := (Complex.nonneg_iff.mp (hlo.dotProduct_mulVec_nonneg (WithLp.ofLp u))).1
  have hh := (Complex.nonneg_iff.mp (hhi.dotProduct_mulVec_nonneg (WithLp.ofLp u))).1
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, complex_quadratic_one, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hl hh
  constructor <;> linarith

theorem BoundedChartFamily.frame_quadratic_comparison
    {g : HermitianField M} (A : BoundedChartFamily g) (p : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball 0 A.radius) (u : ComplexVector n) :
    (A.bound 0)⁻¹ * ‖u‖ ^ 2 ≤ hermitianNormSq (g (A.chart p z))
      (mfderiv (ComplexModel n) (ComplexModel n) (A.chart p) z u) ∧
    hermitianNormSq (g (A.chart p z))
      (mfderiv (ComplexModel n) (ComplexModel n) (A.chart p) z u) ≤ A.bound 0 * ‖u‖ ^ 2 := by
  have h := matrix_quadratic_comparison (G := pullbackMatrix g (A.chart p) z)
    (C := A.bound 0) (by simpa only [Complex.ofReal_inv] using (A.comparison p z hz).1)
      (A.comparison p z hz).2 u
  rw [pullbackMatrix_sesquilinear g (A.chart p) z u u] at h
  exact h

def realChartFrame
    (e : ComplexVector n → M.Carrier) (z v : ComplexVector n) :
    TangentSpace 𝓘(ℝ, ComplexVector n) (e z) :=
  mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) e z
    ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v)

theorem realTangentEquiv_realChartFrame
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (v : ComplexVector n) :
    L12Aux.realTangentEquiv (e z) (realChartFrame e z v) =
      mfderiv (ComplexModel n) (ComplexModel n) e z v := by
  let S := ComplexEuclideanManifold n
    (Nat.succ_le_iff.mpr (L12Aux.manifold_dimension_pos M))
  have hf : MDifferentiableAt (ComplexModel n) (ComplexModel n)
      (fun u : S.Carrier => e u) z :=
    (he z hz).mdifferentiableAt (e.open_source.mem_nhds hz)
  have hd := L12Aux.mfderiv_real (M := S) (N := M) hf
  have hv := congrArg (fun A => L12Aux.realTangentEquiv (e z)
    (A ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v))) hd
  have hsource : L12Aux.realTangentEquiv (M := S) z
      ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v) =
        (tangentSpaceCastModel (ComplexModel n) z).symm v := rfl
  change L12Aux.realTangentEquiv (e z) (realChartFrame e z v) =
    L12Aux.realTangentEquiv (e z) ((L12Aux.realTangentEquiv (e z)).symm
      (((mfderiv (ComplexModel n) (ComplexModel n) e z).restrictScalars ℝ)
        (L12Aux.realTangentEquiv (M := S) z
          ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm v)))) at hv
  rw [ContinuousLinearEquiv.apply_symm_apply, hsource] at hv
  exact hv

theorem realChartFrame_norm
    (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (v : ComplexVector n) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup g (e z)
    ‖realChartFrame e z v‖ = Real.sqrt (2 * hermitianNormSq (g (e z))
      (mfderiv (ComplexModel n) (ComplexModel n) e z v)) := by
  rw [L12Aux.underlyingRealTangent_norm, realTangentEquiv_realChartFrame e he hz]

theorem BoundedChartFamily.realFrame_norm_comparison
    {g : HermitianField M} (A : BoundedChartFamily g) (p : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball 0 A.radius) (u : ComplexVector n) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup g (A.chart p z)
    Real.sqrt (2 * (A.bound 0)⁻¹) * ‖u‖ ≤ ‖realChartFrame (A.chart p) z u‖ ∧
    ‖realChartFrame (A.chart p) z u‖ ≤ Real.sqrt (2 * A.bound 0) * ‖u‖ := by
  let := L12Aux.underlyingRealTangentNormedAddCommGroup g (A.chart p z)
  have hs : z ∈ (A.chart p).source :=
    A.closedBall_source p (ball_subset_closedBall hz)
  rw [realChartFrame_norm g (A.chart p) (A.differentiable p) hs]
  obtain ⟨hl, hh⟩ := A.frame_quadratic_comparison p hz u
  have hlow := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 2))
  have hhigh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2))
  have hC := (A.bound_pos 0).le
  rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 2 * (A.bound 0)⁻¹),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg u)] at hlow
  rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 2 * A.bound 0),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg u)] at hhigh
  exact ⟨hlow, hhigh⟩

theorem BoundedChartFamily.inverseFrame_norm_le
    {g : HermitianField M} (A : BoundedChartFamily g) (p : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball 0 A.radius)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) (A.chart p z)) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup g (A.chart p z)
    ‖tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z
      (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (A.chart p).symm
        (A.chart p z) v)‖ ≤
      (Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹ * ‖v‖ := by
  let := L12Aux.manifold_realSmooth M
  let := L12Aux.underlyingRealTangentNormedAddCommGroup g (A.chart p z)
  have hs : z ∈ (A.chart p).source := A.closedBall_source p (ball_subset_closedBall hz)
  have he : (A.chart p).MDifferentiable
      𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) :=
    ⟨(chart_real_contMDiffOn (A.chart p) (A.differentiable p)).mdifferentiableOn (by simp),
      (inverse_chart_real_contMDiffOn (A.chart p) (A.inverse_differentiable p)).mdifferentiableOn
        (by simp)⟩
  have hcomp := he.comp_symm_deriv ((A.chart p).map_source hs)
  rw [(A.chart p).left_inv hs] at hcomp
  have hv := congrArg (fun L => L v) hcomp
  change mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (A.chart p) z
    (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (A.chart p).symm
      (A.chart p z) v) = v at hv
  let u := tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z
    (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (A.chart p).symm
      (A.chart p z) v)
  have hframe : realChartFrame (A.chart p) z u = v := by
    change mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (A.chart p) z
      ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm
        ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z)
          (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (A.chart p).symm
            (A.chart p z) v))) = v
    convert! hv using 1
  have hl := (A.realFrame_norm_comparison p hz u).1
  rw [hframe] at hl
  have hC := A.bound_pos 0
  have hc : 0 < Real.sqrt (2 * (A.bound 0)⁻¹) := Real.sqrt_pos.mpr (by positivity)
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hl) |>.trans_eq (div_eq_inv_mul _ _)

end Yau.LeafProofs.L17Aux
