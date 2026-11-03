import Yau.LeafProofs.L19ScalarEnergy

/-! The normed energy domain and its genuine scalar L² inclusion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- A separate type fixes the actual metric and Riemannian measure in
the energy norm.  Its elements remain genuine smooth compact scalars. -/
def ScalarEnergyDomain (g : SmoothMetric M) (μ : Measure M.Carrier)
    (_hμ : IsRiemannianVolume g.form μ) := CompactScalar M

instance (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    AddCommGroup (ScalarEnergyDomain g μ hμ) := inferInstanceAs (AddCommGroup (CompactScalar M))

instance (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    Module ℝ (ScalarEnergyDomain g μ hμ) := inferInstanceAs (Module ℝ (CompactScalar M))

instance (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    CoeFun (ScalarEnergyDomain g μ hμ) (fun _ => M.Carrier → ℝ) := ⟨fun f => f.val⟩

instance (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    InnerProductSpace.Core ℝ (ScalarEnergyDomain g μ hμ) := compactScalarInnerCore g μ hμ

instance (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    NormedAddCommGroup (ScalarEnergyDomain g μ hμ) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    InnerProductSpace ℝ (ScalarEnergyDomain g μ hμ) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (ScalarEnergyDomain g μ hμ))

/-- The energy completion is constructed from the actual norm above. -/
abbrev ScalarEnergySpace (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) := UniformSpace.Completion (ScalarEnergyDomain g μ hμ)

theorem scalarEnergyDomain_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f k : ScalarEnergyDomain g μ hμ) :
    ⟪f, k⟫_ℝ = scalarSobolevPair g μ f k := rfl

theorem scalarEnergyDomain_memLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : ScalarEnergyDomain g μ hμ) :
    MemLp (f : M.Carrier → ℝ) 2 μ := by
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  exact (continuous_of_smoothFn f.2.1).memLp_of_hasCompactSupport f.2.2

/-- The inclusion into the actual scalar L² space, before completion. -/
def scalarEnergyDomainL2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : ScalarEnergyDomain g μ hμ) : Lp ℝ 2 μ :=
  (scalarEnergyDomain_memLp g μ hμ f).toLp f

theorem scalarEnergyDomainL2_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : ScalarEnergyDomain g μ hμ) :
    scalarEnergyDomainL2 g μ hμ f =ᵐ[μ] (f : M.Carrier → ℝ) :=
  (scalarEnergyDomain_memLp g μ hμ f).coeFn_toLp

theorem scalarEnergyDomainL2_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f k : ScalarEnergyDomain g μ hμ) :
    ⟪scalarEnergyDomainL2 g μ hμ f, scalarEnergyDomainL2 g μ hμ k⟫_ℝ =
      ∫ y, f y * k y ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarEnergyDomainL2_coe g μ hμ f, scalarEnergyDomainL2_coe g μ hμ k]
    with y hf hk
  simp only [hf, hk, RCLike.inner_apply, conj_trivial, mul_comm]

theorem scalarEnergyDomainL2_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : ScalarEnergyDomain g μ hμ) :
    ‖scalarEnergyDomainL2 g μ hμ f‖ ≤ ‖f‖ := by
  have hL2 := real_inner_self_eq_norm_sq (scalarEnergyDomainL2 g μ hμ f)
  have hH1 := real_inner_self_eq_norm_sq f
  rw [scalarEnergyDomainL2_inner] at hL2
  rw [scalarEnergyDomain_inner] at hH1
  have hE := scalarEnergyPair_nonneg g μ (f : M.Carrier → ℝ)
  unfold scalarSobolevPair at hH1
  nlinarith [norm_nonneg (scalarEnergyDomainL2 g μ hμ f), norm_nonneg f]

def scalarEnergyDomainL2Linear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : ScalarEnergyDomain g μ hμ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := scalarEnergyDomainL2 g μ hμ
  map_add' f k := by
    apply Lp.ext
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ (f + k),
      scalarEnergyDomainL2_coe g μ hμ f, scalarEnergyDomainL2_coe g μ hμ k,
      Lp.coeFn_add (scalarEnergyDomainL2 g μ hμ f) (scalarEnergyDomainL2 g μ hμ k)]
      with y hsum hf hk hLp
    rw [hsum, hLp]
    change f y + k y = _
    rw [← hf, ← hk]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ (c • f),
      scalarEnergyDomainL2_coe g μ hμ f, Lp.coeFn_smul c (scalarEnergyDomainL2 g μ hμ f)]
      with y hsmul hf hLp
    simp only [RingHom.id_apply]
    rw [hsmul, hLp]
    change c * f y = c * _
    rw [hf]

def scalarEnergyDomainL2CLM (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : ScalarEnergyDomain g μ hμ →L[ℝ] Lp ℝ 2 μ :=
  (scalarEnergyDomainL2Linear g μ hμ).mkContinuous 1 (by
    intro f
    change ‖scalarEnergyDomainL2 g μ hμ f‖ ≤ 1 * ‖f‖
    rw [one_mul]
    exact scalarEnergyDomainL2_norm_le g μ hμ f)

/-- The L² inclusion extends to the actual energy completion. -/
def scalarEnergyL2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : ScalarEnergySpace g μ hμ →L[ℝ] Lp ℝ 2 μ :=
  (scalarEnergyDomainL2CLM g μ hμ).extend UniformSpace.Completion.toComplL

theorem scalarEnergyL2_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : ScalarEnergyDomain g μ hμ) :
    scalarEnergyL2 g μ hμ (f : ScalarEnergySpace g μ hμ) = scalarEnergyDomainL2 g μ hμ f := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) f

theorem scalarEnergyL2_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : ScalarEnergySpace g μ hμ) :
    ‖scalarEnergyL2 g μ hμ f‖ ≤ ‖f‖ := by
  refine UniformSpace.Completion.induction_on f (p := fun v : ScalarEnergySpace g μ hμ =>
    ‖scalarEnergyL2 g μ hμ v‖ ≤ ‖v‖) ?_ ?_
  · exact isClosed_le ((scalarEnergyL2 g μ hμ).continuous.norm) continuous_norm
  · intro k
    rw [scalarEnergyL2_coe, UniformSpace.Completion.norm_coe]
    exact scalarEnergyDomainL2_norm_le g μ hμ k

/-- The true smooth compact scalar `k - Δk`, as an element of the same
fixed domain. -/
def scalarEnergyGreenTest (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ScalarEnergyDomain g μ hμ) :
    ScalarEnergyDomain g μ hμ :=
  ⟨fun y => k y - laplacian g.form k y,
    smoothFn_sub k.2.1 (smoothFn_laplacian g k.2.1),
    k.2.2.sub (laplacian_hasCompactSupport g.form k.2.1 k.2.2)⟩

/-- Green's identity extends by continuity from the true test domain.
This identity supplies closability without introducing a tangent-valued
L² space or an abstract derivative as caller-chosen data. -/
theorem scalarEnergyL2_green (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : ScalarEnergySpace g μ hμ) (k : ScalarEnergyDomain g μ hμ) :
    ⟪f, (k : ScalarEnergySpace g μ hμ)⟫_ℝ =
      ⟪scalarEnergyL2 g μ hμ f,
        scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)⟫_ℝ := by
  refine UniformSpace.Completion.induction_on f (p := fun v : ScalarEnergySpace g μ hμ =>
    ⟪v, (k : ScalarEnergySpace g μ hμ)⟫_ℝ = ⟪scalarEnergyL2 g μ hμ v,
      scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)⟫_ℝ) ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const)
      (((scalarEnergyL2 g μ hμ).continuous).inner continuous_const)
  · intro v
    rw [UniformSpace.Completion.inner_coe, scalarEnergyDomain_inner,
      scalarEnergyL2_coe, scalarEnergyDomainL2_inner]
    exact scalarSobolevPair_eq_green g hK μ hμ v k

/-- The energy completion injects into the actual scalar L² space.
In particular, the original compact scalar Dirichlet energy is closable. -/
theorem scalarEnergyL2_injective (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    Function.Injective (scalarEnergyL2 g μ hμ) := by
  have hzero (f : ScalarEnergySpace g μ hμ) (hf : scalarEnergyL2 g μ hμ f = 0) : f = 0 := by
    have htest (k : ScalarEnergyDomain g μ hμ) : ⟪f, (k : ScalarEnergySpace g μ hμ)⟫_ℝ = 0 := by
      rw [scalarEnergyL2_green g hK μ hμ, hf, inner_zero_left]
    have hall (v : ScalarEnergySpace g μ hμ) : ⟪f, v⟫_ℝ = 0 := by
      refine UniformSpace.Completion.induction_on v
        (p := fun w : ScalarEnergySpace g μ hμ => ⟪f, w⟫_ℝ = 0) ?_ htest
      exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
    exact inner_self_eq_zero.mp (hall f)
  intro f k hfk
  apply sub_eq_zero.mp
  apply hzero
  simp only [map_sub, hfk, sub_self]

end Yau.LeafProofs.L19Aux
