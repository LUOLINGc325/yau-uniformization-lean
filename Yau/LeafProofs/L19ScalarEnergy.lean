import Yau.LeafProofs.L19Differential

/-! The scalar energy on the actual compactly supported smooth functions
and its exact Green representation. -/

noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Manifold ComplexOrder Matrix

namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- This domain consists of genuine functions on the given manifold. -/
def compactScalarSubmodule (M : ComplexManifold n) : Submodule ℝ (M.Carrier → ℝ) where
  carrier := {f | SmoothFn f ∧ HasCompactSupport f}
  zero_mem' := ⟨smoothFn_const 0, by simpa using (HasCompactSupport.zero : HasCompactSupport (0 : M.Carrier → ℝ))⟩
  add_mem' := by
    intro f k hf hk
    exact ⟨fun x => (hf.1 x).add (hk.1 x), hf.2.add hk.2⟩
  smul_mem' := by
    intro c f hf
    exact ⟨fun x => (contDiffOn_const.mul (hf.1 x)), hf.2.smul_left⟩

abbrev CompactScalar (M : ComplexManifold n) := ↥(compactScalarSubmodule M)

instance : CoeFun (CompactScalar M) (fun _ => M.Carrier → ℝ) := ⟨fun f => f.val⟩

theorem compactScalar_smooth (f : CompactScalar M) : SmoothFn (f : M.Carrier → ℝ) := f.2.1

theorem compactScalar_compact (f : CompactScalar M) : HasCompactSupport (f : M.Carrier → ℝ) := f.2.2

/-- The normalization is half the physical scalar energy. -/
def scalarEnergyPair (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f k : M.Carrier → ℝ) : ℝ := (1 / 2 : ℝ) * ∫ y, scalarGradientPair g.form f k y ∂μ

def scalarSobolevPair (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f k : M.Carrier → ℝ) : ℝ := (∫ y, f y * k y ∂μ) + scalarEnergyPair g μ f k

theorem compactScalar_product_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f k : CompactScalar M) :
    Integrable (fun y => f y * k y) μ :=
  smoothFn_integrable_compact g μ hμ (smoothFn_mul f.2.1 k.2.1) f.2.2.mul_right

theorem scalarEnergyPair_symm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f k : M.Carrier → ℝ) : scalarEnergyPair g μ f k = scalarEnergyPair g μ k f := by
  unfold scalarEnergyPair
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (scalarGradientPair_symm g.form f k)

theorem scalarEnergyPair_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : M.Carrier → ℝ) : 0 ≤ scalarEnergyPair g μ f f := by
  exact mul_nonneg (by norm_num) (integral_nonneg (scalarGradientPair_self_nonneg g.form f))

theorem scalarEnergyPair_add_left (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f k v : CompactScalar M) :
    scalarEnergyPair g μ (f + k) v = scalarEnergyPair g μ f v + scalarEnergyPair g μ k v := by
  have hpair : scalarGradientPair g.form (f + k) v =
      fun y => scalarGradientPair g.form f v y + scalarGradientPair g.form k v y := by
    funext y
    change scalarGradientPair g.form (fun z => f z + k z) v y = _
    rw [scalarGradientPair_symm, scalarGradientPair_add_right g.form v f.2.1 k.2.1,
      scalarGradientPair_symm g.form v f, scalarGradientPair_symm g.form v k]
  unfold scalarEnergyPair
  rw [hpair, integral_add (scalarGradientPair_integrable g μ hμ f.2.1 v.2.1 f.2.2)
    (scalarGradientPair_integrable g μ hμ k.2.1 v.2.1 k.2.2)]
  ring

theorem scalarEnergyPair_smul_left (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f k : CompactScalar M) (c : ℝ) :
    scalarEnergyPair g μ (c • f) k = c * scalarEnergyPair g μ f k := by
  have hpair : scalarGradientPair g.form (c • f) k =
      fun y => c * scalarGradientPair g.form f k y := by
    funext y
    change scalarGradientPair g.form (fun z => c * f z) k y = _
    rw [scalarGradientPair_symm, scalarGradientPair_const_mul_right g.form k f.2.1 c,
      scalarGradientPair_symm g.form k f]
  unfold scalarEnergyPair
  rw [hpair, integral_const_mul]
  ring

/-- The actual Green theorem expresses the energy using only the L²
pairing with a fixed smooth compact scalar and its actual Laplacian. -/
theorem scalarSobolevPair_eq_green (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f k : CompactScalar M) :
    scalarSobolevPair g μ f k = ∫ y, f y * (k y - laplacian g.form k y) ∂μ := by
  have hG := integral_scalar_green g hK μ hμ k.2.1 f.2.1 f.2.2
  simp only [mul_sub]
  rw [integral_sub (compactScalar_product_integrable g μ hμ f k) hG.1]
  unfold scalarSobolevPair scalarEnergyPair
  linarith [hG.2.2]

theorem scalarSobolevPair_symm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f k : M.Carrier → ℝ) : scalarSobolevPair g μ f k = scalarSobolevPair g μ k f := by
  unfold scalarSobolevPair
  rw [scalarEnergyPair_symm]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => mul_comm _ _)

theorem scalarSobolevPair_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : M.Carrier → ℝ) : 0 ≤ scalarSobolevPair g μ f f := by
  exact add_nonneg (integral_nonneg (fun _ => mul_self_nonneg _)) (scalarEnergyPair_nonneg g μ f)

theorem scalarSobolevPair_self_eq_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : CompactScalar M)
    (hzero : scalarSobolevPair g μ f f = 0) : f = 0 := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hnonneg := scalarEnergyPair_nonneg g μ (f : M.Carrier → ℝ)
  have hInt : (∫ y, f y * f y ∂μ) = 0 := by
    have hh : 0 ≤ ∫ y, f y * f y ∂μ := integral_nonneg (fun _ => mul_self_nonneg _)
    unfold scalarSobolevPair at hzero
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => mul_self_nonneg (f y))
    (compactScalar_product_integrable g μ hμ f f)).mp hInt
  have hcont := (continuous_of_smoothFn f.2.1).mul (continuous_of_smoothFn f.2.1)
  have hae' : (fun y => f y * f y) =ᵐ[μ.restrict Set.univ] (fun _ => 0) := by
    rw [Measure.restrict_univ]
    filter_upwards [hae] with y hy
    exact hy
  have hevery := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_univ
    hcont.continuousOn continuousOn_const
  apply Subtype.ext
  funext y
  have hy := hevery (Set.mem_univ y)
  exact (mul_self_eq_zero.mp hy)

theorem scalarSobolevPair_add_left (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f k v : CompactScalar M) :
    scalarSobolevPair g μ (f + k) v = scalarSobolevPair g μ f v + scalarSobolevPair g μ k v := by
  unfold scalarSobolevPair
  rw [scalarEnergyPair_add_left g μ hμ f k v]
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (compactScalar_product_integrable g μ hμ f v)
    (compactScalar_product_integrable g μ hμ k v)]
  ring

theorem scalarSobolevPair_smul_left (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f k : CompactScalar M) (c : ℝ) :
    scalarSobolevPair g μ (c • f) k = c * scalarSobolevPair g μ f k := by
  unfold scalarSobolevPair
  rw [scalarEnergyPair_smul_left g μ f k c]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
  ring

/-- All inner-product laws follow from actual integrals, and definiteness
uses the full support of the given Riemannian volume. -/
@[instance_reducible] def compactScalarInnerCore (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : InnerProductSpace.Core ℝ (CompactScalar M) where
  inner := fun f k => scalarSobolevPair g μ f k
  conj_inner_symm := fun f k => scalarSobolevPair_symm g μ k f
  re_inner_nonneg := fun f => scalarSobolevPair_nonneg g μ f
  add_left := scalarSobolevPair_add_left g μ hμ
  smul_left := fun f k c => scalarSobolevPair_smul_left g μ f k c
  definite := scalarSobolevPair_self_eq_zero g μ hμ

/-- The actual project Laplacian is local, so it preserves compact support. -/
theorem laplacian_zero_of_notMem_tsupport (h : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) {x : M.Carrier} (hx : x ∉ tsupport f) : laplacian h f x = 0 := by
  have heq : inChart x f =ᶠ[𝓝 (chartPt x x)] (fun _ => (0 : ℝ)) :=
    inChart_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)
  have hD : fderiv ℝ (fderiv ℝ (inChart x f)) (chartPt x x) = 0 := by
    rw [heq.fderiv.fderiv_eq]
    simp
  have hf2 : ContDiffAt ℝ 2 (inChart x f) (chartPt x x) :=
    (contDiffAt_inChart hf x (mem_extChartAt_target x)).of_le (by simp)
  rw [laplacian_eq_half_principal h hf]
  apply div_eq_zero_iff.mpr
  left
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hzero : rDeriv (fun w => rDeriv (inChart x f) w j) (chartPt x x) i = 0 := by
    exact (rDeriv_rDeriv_eq_hessian hf2 i j).trans (by rw [hD]; rfl)
  exact mul_eq_zero_of_right _ hzero

theorem laplacian_hasCompactSupport (h : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (hcf : HasCompactSupport f) : HasCompactSupport (laplacian h f) := by
  apply (show IsCompact (tsupport f) from hcf).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hxf
  exact hx (laplacian_zero_of_notMem_tsupport h hf hxf)

end Yau.LeafProofs.L19Aux
