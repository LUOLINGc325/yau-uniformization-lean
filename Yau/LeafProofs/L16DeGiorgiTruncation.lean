import Yau.Blueprint.ParabolicSpaces
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Classical divergence equations and genuine positive-part truncations

All derivatives and measures below are the actual ones on `Space n` and
`Point n`. No solution, energy estimate, or regularity conclusion is a field.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators NNReal ENNReal
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
set_option backward.isDefEq.respectTransparency false

/-- The actual coordinate spatial gradient. -/
def dgGradient {n : ℕ} (u : Point n → ℝ) (z : Point n) : Yau.RIdx n → ℝ :=
  fun i => d (fun x => u (x,z.2)) z.1 i

/-- The actual divergence equation on an open region. -/
def ClassicalDivEq {n : ℕ} (U : Set (Point n))
    (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (f u : Point n → ℝ) : Prop :=
  ∀ z ∈ U, deriv (fun t => u (z.1,t)) z.2 -
    (∑ i, d (fun x => ∑ j, A (x,z.2) i j * dgGradient u (x,z.2) j) z.1 i) =
    (∑ i, c z i * dgGradient u z i) + f z

/-- Either of the two signs; arbitrary truncation levels are separate arguments. -/
def DGSign (σ : ℝ) : Prop := σ = 1 ∨ σ = -1

/-- Positive part of a real number, including its value at zero. -/
def dgPositivePart (r : ℝ) : ℝ := max 0 r

/-- Actual positive-part truncation of the signed solution. -/
def dgTruncation {n : ℕ} (σ k : ℝ) (u : Point n → ℝ) : Point n → ℝ :=
  fun z => dgPositivePart (σ * u z - k)

/-- The candidate weak gradient, with the strict active set explicitly specified. -/
def dgTruncationGradient {n : ℕ} (σ k : ℝ) (u : Point n → ℝ)
    (z : Point n) (i : Yau.RIdx n) : ℝ :=
  if k < σ * u z then σ * dgGradient u z i else 0

/-- Squared Euclidean coordinate norm; there are exactly `2*n` coordinates. -/
def dgGradientSq {n : ℕ} (G : Yau.RIdx n → ℝ) : ℝ := ∑ i, (G i)^2

/-- A genuine spatially weighted time slice, used instead of an unchecked supremum. -/
def dgSliceEnergy {n : ℕ} (O : Set (Space n)) (v ζ : Point n → ℝ) (t : ℝ) : ℝ :=
  ∫ x in O, (v (x,t))^2 * (ζ (x,t))^2

/-- Actual product-volume integration on a finite cylinder. -/
def dgCylinderIntegral {n : ℕ} (O : Set (Space n)) (a b : ℝ)
    (g : Point n → ℝ) : ℝ :=
  ∫ z, g z ∂productVolume O (Ioo a b)

@[simp] theorem dgPositivePart_nonneg (r : ℝ) : 0 ≤ dgPositivePart r := le_max_left _ _

@[simp] theorem dgPositivePart_zero : dgPositivePart 0 = 0 := max_self _

@[simp] theorem dgPositivePart_of_nonpos {r : ℝ} (h : r ≤ 0) :
    dgPositivePart r = 0 := max_eq_left h

@[simp] theorem dgPositivePart_of_nonneg {r : ℝ} (h : 0 ≤ r) :
    dgPositivePart r = r := max_eq_right h

theorem dgPositivePart_lipschitz : LipschitzWith 1 dgPositivePart := by
  change LipschitzWith 1 (fun x : ℝ => max 0 x)
  simpa only [max_eq_right (show (0 : ℝ≥0) ≤ 1 by positivity), id_eq] using (LipschitzWith.const 0).max LipschitzWith.id

/-- The totalized actual derivative of the positive part has the strict-active-set
formula even on the zero level. Almost-everywhere differentiability is needed
separately when using this formula for weak derivatives. -/
theorem dgPositivePart_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {x : E} (hu : ContinuousAt u x) :
    fderiv ℝ (fun y => dgPositivePart (u y)) x =
      if 0 < u x then fderiv ℝ u x else 0 := by
  by_cases hx : 0 < u x
  · rw [ite_eq_left hx]
    have hnear : (fun y => dgPositivePart (u y)) =ᶠ[𝓝 x] u := by
      filter_upwards [hu.eventually (Ioi_mem_nhds hx)] with y hy
      exact dgPositivePart_of_nonneg (le_of_lt hy)
    exact hnear.fderiv_eq
  · rw [ite_eq_right hx]
    have hmin : IsLocalMin (fun y => dgPositivePart (u y)) x := by
      apply Filter.Eventually.of_forall
      intro y
      change dgPositivePart (u x) ≤ dgPositivePart (u y)
      rw [dgPositivePart_of_nonpos (le_of_not_gt hx)]
      exact dgPositivePart_nonneg _
    exact hmin.fderiv_eq_zero

/-- The zero level is retained: the gradient of a Lipschitz function vanishes
almost everywhere there. This follows by differentiating its two positive
parts, both of which have a genuine local minimum on that level. -/
theorem dg_fderiv_zero_ae_on_level {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (k : ℝ) :
    ∀ᵐ x ∂μ, u x = k → fderiv ℝ u x = 0 := by
  let w : E → ℝ := fun x => u x - k
  have hw : LipschitzWith K w := by simpa only [w, add_zero] using hu.sub (LipschitzWith.const k)
  have hp := dgPositivePart_lipschitz.comp hw
  have hm := dgPositivePart_lipschitz.comp hw.neg
  filter_upwards [hp.ae_differentiableAt (μ := μ), hm.ae_differentiableAt (μ := μ)] with x hpx hmx
  intro hx
  have hwx : w x = 0 := by simp [w,hx]
  have hdecomp : (fun y => dgPositivePart (w y) - dgPositivePart (-w y)) = w := by
    funext y
    dsimp [dgPositivePart]
    rcases le_total 0 (w y) with hy | hy
    · rw [max_eq_right hy,max_eq_left (neg_nonpos.mpr hy)]; ring
    · rw [max_eq_left hy,max_eq_right (neg_nonneg.mpr hy)]; ring
  have hdiff := fderiv_fun_sub hpx hmx
  simp only [Function.comp_def, Pi.neg_apply] at hdiff
  rw [hdecomp, dgPositivePart_fderiv hw.continuous.continuousAt,
    dgPositivePart_fderiv (u := fun y => -w y) hw.neg.continuous.continuousAt] at hdiff
  simp only [hwx,neg_zero,lt_self_iff_false,ite_false,sub_self] at hdiff
  have hsub := fderiv_sub_const (𝕜 := ℝ) (c := k) (f := u) (x := x)
  simpa only [w,hsub] using hdiff

/-- Genuine weak chain rule, in any direction, for a globally Lipschitz function.
The proof uses Rademacher and Lipschitz integration by parts; it does not discard
the zero level or assume that the truncated function is smooth. -/
theorem dgPositivePart_weak_chain_global {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {u φ : E → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (e : E) :
    (∫ x, dgPositivePart (u x) * fderiv ℝ φ x e ∂μ) =
      -(∫ x, (if 0 < u x then fderiv ℝ u x e else 0) * φ x ∂μ) := by
  have hp := dgPositivePart_lipschitz.comp hu
  obtain ⟨D,hφLip⟩ := hφ.lipschitzWith_of_hasCompactSupport hcφ (by simp)
  have hIBP := hp.integral_lineDeriv_mul_eq (μ := μ) hφLip hcφ e
  simp only [Function.comp_def] at hIBP
  have hleft : (∫ x, lineDeriv ℝ (fun y => dgPositivePart (u y)) x e * φ x ∂μ) =
      ∫ x, (if 0 < u x then fderiv ℝ u x e else 0) * φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp.ae_differentiableAt (μ := μ)] with x hx
    change DifferentiableAt ℝ (fun y => dgPositivePart (u y)) x at hx
    rw [hx.lineDeriv_eq_fderiv,dgPositivePart_fderiv hu.continuous.continuousAt]
    split_ifs <;> rfl
  have hright : (∫ x, lineDeriv ℝ φ x (-e) * dgPositivePart (u x) ∂μ) =
      -(∫ x, dgPositivePart (u x) * fderiv ℝ φ x e ∂μ) := by
    simp_rw [(hφ.differentiable (by simp) _).lineDeriv_eq_fderiv,
      map_neg,neg_mul,mul_comm (fderiv ℝ φ _ e)]
    exact integral_neg _
  rw [hleft,hright] at hIBP
  linarith

/-- Smooth compact localization of an interior smooth function, with equality
on a neighborhood of the whole prescribed compact set. -/
theorem dg_smooth_compact_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ∃ w : E → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      ∀ x ∈ K, w =ᶠ[𝓝 x] u := by
  obtain ⟨V,hV,hKV,hVU,hVC⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W,hW,hVW,hWU,hWC⟩ := exists_open_between_and_isCompact_closure hVC hU hVU
  obtain ⟨η,hη,_hRange,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW
      (isClosed_closure : IsClosed (closure V)) hVW
  have hcη : HasCompactSupport η := by
    change IsCompact (tsupport η)
    simpa only [tsupport,hSupport] using hWC
  have hηU : tsupport η ⊆ U := by simpa only [tsupport,hSupport] using hWU
  let w : E → ℝ := fun x => η x * u x
  have hw : ContDiff ℝ ∞ w := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport η
    · exact hη.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds (hηU hx)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [w,hy,Pi.zero_apply,zero_mul]
  refine ⟨w,hw,hcη.mul_right,?_⟩
  intro x hx
  filter_upwards [hV.mem_nhds (hKV hx)] with y hy
  change η y * u y = u y
  rw [(hOne y).mp (subset_closure hy),one_mul]

/-- Positive-part weak chain rule on an arbitrary open interior region. Its
premises are classical smoothness alone, with no global derivative bound. -/
theorem dgPositivePart_weak_chain_local {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U)
    {u φ : E → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (e : E) :
    (∫ x in U, dgPositivePart (u x) * fderiv ℝ φ x e ∂μ) =
      -(∫ x in U, (if 0 < u x then fderiv ℝ u x e else 0) * φ x ∂μ) := by
  obtain ⟨w,hw,hcw,hwu⟩ := dg_smooth_compact_extension hU hcφ hφU hu
  obtain ⟨C,hC⟩ := hw.lipschitzWith_of_hasCompactSupport hcw (by simp)
  have h := dgPositivePart_weak_chain_global (μ := μ) hC hφ hcφ e
  have hleft : (∫ x, dgPositivePart (w x) * fderiv ℝ φ x e ∂μ) =
      ∫ x in U, dgPositivePart (u x) * fderiv ℝ φ x e ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      by_cases hx : x ∈ tsupport φ
      · rw [(hwu x hx).eq_of_nhds]
      · rw [fderiv_of_notMem_tsupport ℝ hx]; simp
    · intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hφU h))]; simp
  have hright : (∫ x, (if 0 < w x then fderiv ℝ w x e else 0) * φ x ∂μ) =
      ∫ x in U, (if 0 < u x then fderiv ℝ u x e else 0) * φ x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      by_cases hx : x ∈ tsupport φ
      · rw [(hwu x hx).eq_of_nhds,(hwu x hx).fderiv_eq (𝕜 := ℝ)]
      · rw [image_eq_zero_of_notMem_tsupport hx]; simp
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))]; simp
  rw [hleft,hright] at h
  exact h

/-- Spatial slice derivatives agree with the actual joint derivative. -/
theorem dgGradient_eq_joint_fderiv {n : ℕ} {u : Point n → ℝ} {z : Point n}
    (hu : DifferentiableAt ℝ u z) (i : Yau.RIdx n) :
    dgGradient u z i = fderiv ℝ u z (Yau.realVec i,0) := by
  have hMap : HasFDerivAt (fun x : Space n => (x,z.2))
      ((ContinuousLinearMap.id ℝ (Space n)).prod 0) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hSlice := hu.hasFDerivAt.comp z.1 hMap
  change fderiv ℝ (u ∘ (fun x : Space n => (x,z.2))) z.1 (Yau.realVec i) = _
  rw [hSlice.fderiv]
  rfl

/-- Product volume here is the restriction of the actual product Lebesgue measure. -/
theorem dg_productVolume_eq_restrict {n : ℕ} (O : Set (Space n)) (I : Set ℝ) :
    productVolume O I = volume.restrict (O ×ˢ I) := by
  rw [productVolume,Measure.prod_restrict]
  rfl

/-- Every ball and finite interval give a genuinely finite cylinder measure. -/
theorem dg_cylinder_measure_lt_top {n : ℕ} (x : Space n) (r a b : ℝ) :
    productVolume (Metric.ball x r) (Ioo a b) univ < ⊤ := by
  simp only [productVolume,← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top Metric.isBounded_ball.measure_lt_top
    (by simp only [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)

/-- The real coordinate dimension is `2*n`, including the endpoint dimension two. -/
@[simp] theorem dg_dimension (n : ℕ) : Fintype.card (Yau.RIdx n) = 2*n := by
  simp only [Yau.RIdx,Fintype.card_prod,Fintype.card_fin]
  omega

theorem dg_dimension_at_least_two {n : ℕ} (hn : 0 < n) :
    2 ≤ Fintype.card (Yau.RIdx n) := by rw [dg_dimension]; omega

/-- Both signs and every level have exactly the strict-active-set weak gradient.
No PDE, energy estimate, or bound on a derivative of the solution is assumed. -/
theorem dgTruncation_weakGradient {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    (hU : IsOpen (O ×ˢ I)) {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) (σ k : ℝ) :
    WeakGradient O I (dgTruncation σ k u) (dgTruncationGradient σ k u) := by
  intro φ hφ i
  haveI dgTruncationPointVolumeHaar : (volume : Measure (Point n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let w : Point n → ℝ := fun z => σ * u z - k
  have hw : ContDiffOn ℝ ∞ w (O ×ˢ I) := (contDiffOn_const.mul hu).sub contDiffOn_const
  have h := dgPositivePart_weak_chain_local (μ := volume) hU hw hφ.1 hφ.2.1 hφ.2.2
    (Yau.realVec i,0)
  have hderiv (z : Point n) (hz : z ∈ O ×ˢ I) :
      fderiv ℝ w z (Yau.realVec i,0) = σ * dgGradient u z i := by
    have huz := (hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    dsimp only [w]
    rw [fderiv_sub_const,fderiv_const_mul huz,dgGradient_eq_joint_fderiv huz i]
    rfl
  rw [dg_productVolume_eq_restrict]
  have hleft : (∫ z in O ×ˢ I, dgTruncation σ k u z *
      d (fun x => φ (x,z.2)) z.1 i) =
      ∫ z in O ×ˢ I, dgPositivePart (w z) * fderiv ℝ φ z (Yau.realVec i,0) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    change dgPositivePart (w z) * dgGradient φ z i = _
    rw [dgGradient_eq_joint_fderiv (hφ.1.differentiable (by simp) z)]
  have hright : (∫ z in O ×ˢ I, dgTruncationGradient σ k u z i * φ z) =
      ∫ z in O ×ˢ I, (if 0 < w z then fderiv ℝ w z (Yau.realVec i,0) else 0) * φ z := by
    apply setIntegral_congr_fun hU.measurableSet
    intro z hz
    dsimp only [dgTruncationGradient,w]
    have heq : (k < σ * u z) ↔ 0 < σ * u z - k := sub_pos.symm
    change (if k < σ * u z then σ * dgGradient u z i else 0) * φ z =
      (if 0 < w z then fderiv ℝ w z (Yau.realVec i,0) else 0) * φ z
    simp only [w,← heq]
    change (if k < σ * u z then σ * dgGradient u z i else 0) * φ z =
      (if k < σ * u z then fderiv ℝ w z (Yau.realVec i,0) else 0) * φ z
    rw [hderiv z hz]
  rw [hleft,hright]
  exact h

/-- The actual nonnegative spatial mean of the positive part. -/
def dgPositivePartMean {n : ℕ} (O : Set (Space n)) (φ : Space n → ℝ)
    (u : Point n → ℝ) (t : ℝ) : ℝ := ∫ x in O, φ x * dgPositivePart (u (x,t))

/-- Compact spatial tests give continuous positive-part means, including any
closed time faces on which the solution is merely continuous. -/
theorem dgPositivePartMean_continuousOn {n : ℕ} {O : Set (Space n)} {J : Set ℝ}
    (hO : IsOpen O) {u : Point n → ℝ} (hu : ContinuousOn u (O ×ˢ J))
    {φ : Space n → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) : ContinuousOn (dgPositivePartMean O φ u) J := by
  let v : Point n → ℝ := fun z => φ z.1 * dgPositivePart (u z)
  have hv : ContinuousOn v (univ ×ˢ J) := by
    intro z hz
    by_cases hx : z.1 ∈ tsupport φ
    · have hlocal : ContinuousWithinAt v (O ×ˢ J) z :=
        ((hφ.comp continuous_fst).continuousWithinAt).mul
          (dgPositivePart_lipschitz.continuous.continuousAt.comp_continuousWithinAt
            (hu z ⟨hφO hx,hz.2⟩))
      apply hlocal.mono_of_mem_nhdsWithin
      have hnear : ∀ᶠ q : Point n in 𝓝 z, q.1 ∈ O :=
        (hO.preimage continuous_fst).mem_nhds (hφO hx)
      filter_upwards [self_mem_nhdsWithin,hnear.filter_mono nhdsWithin_le_nhds] with q hq hqO
      exact ⟨hqO,hq.2⟩
    · have hzero : v z = 0 := by simp [v,image_eq_zero_of_notMem_tsupport hx]
      apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq _ hzero
      have hnear : ∀ᶠ q : Point n in 𝓝 z, q.1 ∉ tsupport φ :=
        ((isClosed_tsupport φ).isOpen_compl.preimage continuous_fst).mem_nhds hx
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with q hq
      simp only [v,image_eq_zero_of_notMem_tsupport hq,zero_mul]
  have hvc : ContinuousOn (fun p : ℝ × Space n => v (p.2,p.1)) (J ×ˢ univ) :=
    hv.comp continuous_swap.continuousOn (fun p hp => ⟨hp.2,hp.1⟩)
  have hmean : ContinuousOn (fun t => ∫ x, φ x * dgPositivePart (u (x,t))) J :=
    continuousOn_integral_of_compact_support hcφ hvc (fun t x _ hx => by
      simp only [image_eq_zero_of_notMem_tsupport hx,zero_mul])
  apply hmean.congr
  intro t _ht
  change (∫ x in O, φ x * dgPositivePart (u (x,t))) =
    ∫ x, φ x * dgPositivePart (u (x,t))
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφO h)),zero_mul]

/-- Pointwise Young absorption. These numerical constants involve no coefficient
or solution derivative and preserve the linear forcing term for later use. -/
theorem dg_young_absorption {ν x y : ℝ} (hν : 0 < ν) :
    2*x*y ≤ ν/4*x^2 + (4/ν)*y^2 := by
  apply (mul_le_mul_iff_left₀ hν).mp
  have hsq := sq_nonneg (ν*x - 4*y)
  have hν0 : ν ≠ 0 := ne_of_gt hν
  field_simp
  nlinarith

/-- The quadratic cutoff and drift terms consume half of the coercive term. -/
theorem dg_cutoff_drift_absorption {ν L D v ζ g h : ℝ} (hν : 0 < ν) :
    2*L*v*ζ*g*h + D*v*ζ^2*g ≤
      ν/2*(ζ^2*g^2) + (4*L^2/ν*h^2 + D^2/ν*ζ^2)*v^2 := by
  have h1 := dg_young_absorption hν (x := ζ*g) (y := L*v*h)
  have h2 := dg_young_absorption hν (x := ζ*g) (y := D*v*ζ/2)
  convert add_le_add h1 h2 using 1 <;> ring

/-! The two nonlinear PDE contracts below are ordinary explicit propositions.
Their unconditional proofs appear later in this module. -/

/-- Qualitative smoothness of the actual fields on the open equation cylinder. -/
def DGClassicalFields {n : ℕ} (U : Set (Point n))
    (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (f u : Point n → ℝ) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U) ∧
  (∀ i, ContDiffOn ℝ ∞ (fun z => c z i) U) ∧
  ContDiffOn ℝ ∞ f U ∧ ContDiffOn ℝ ∞ u U

/-- Actual ellipticity, drift norm, and forcing bounds; no derivative bound. -/
def DGUniformBounds {n : ℕ} (U : Set (Point n))
    (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (f : Point n → ℝ) (ν L D F : ℝ) : Prop :=
  Elliptic U A ν L ∧
  (∀ z ∈ U, dgGradientSq (c z) ≤ D^2) ∧ ∀ z ∈ U, |f z| ≤ F

/-- A classical cutoff with one compact spatial support throughout the time slab.
It may be nonzero at either time face, so the initial energy term is retained. -/
def DGSpatialCutoff {n : ℕ} (O : Set (Space n)) (a b : ℝ)
    (ζ : Point n → ℝ) : Prop :=
  ContDiff ℝ ∞ ζ ∧
  (∀ z ∈ O ×ˢ Icc a b, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧
  ∃ K : Set (Space n), IsCompact K ∧ K ⊆ O ∧
    ∀ z : Point n, z.2 ∈ Icc a b → z.1 ∉ K → ζ z = 0

/-- Actual weighted energy density of the strict-active-set gradient. -/
def dgTruncationEnergyDensity {n : ℕ} (σ k : ℝ) (u ζ : Point n → ℝ)
    (z : Point n) : ℝ :=
  dgGradientSq (dgTruncationGradient σ k u z) * (ζ z)^2

/-- Exact cutoff-error integrand used by truncation Caccioppoli. -/
def dgTruncationCutoffError {n : ℕ} (σ k : ℝ) (u ζ : Point n → ℝ)
    (z : Point n) : ℝ :=
  (dgTruncation σ k u z)^2 *
    (|deriv (fun t => ζ (z.1,t)) z.2| + dgGradientSq (dgGradient ζ z) + (ζ z)^2)

/-- Forcing stays linear in the positive part, hence retains the active-set gain. -/
def dgTruncationForcingDensity {n : ℕ} (σ k : ℝ) (u ζ : Point n → ℝ)
    (z : Point n) : ℝ := dgTruncation σ k u z * (ζ z)^2

/-- The companion product gradient is explicitly the true weak product formula. -/
def dgTruncationCutoffGradient {n : ℕ} (σ k : ℝ) (u ζ : Point n → ℝ)
    (z : Point n) (i : Yau.RIdx n) : ℝ :=
  ζ z * dgTruncationGradient σ k u z i + dgTruncation σ k u z * dgGradient ζ z i

/-- Universal-before-fields Caccioppoli, with every time slice, full-slab
energy, the exact forcing term, and initial energy. The companion product
estimate has the same numerical constant after enlarging it once. -/
def DGTruncationCaccioppoliGap : Prop :=
  ∀ n : ℕ, 0 < n → ∀ ν L D : ℝ, 0 < ν → ν ≤ L → 0 ≤ D →
  ∃ C : ℝ, 0 < C ∧ ∀ F : ℝ, 0 ≤ F →
  ∀ (x₀ : Space n) (R l r a b : ℝ), 0 < R → l < a → a < b → b ≤ r →
  ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u ζ : Point n → ℝ),
  let O := Metric.ball x₀ R
  let U := O ×ˢ Ioo l r
  DGClassicalFields U A c f u → ClassicalDivEq U A c f u →
  DGUniformBounds U A c f ν L D F → ContinuousOn u (O ×ˢ Icc a b) →
  DGSpatialCutoff O a b ζ → ∀ σ k : ℝ, DGSign σ →
  let v := dgTruncation σ k u
  let H := dgTruncationEnergyDensity σ k u ζ
  let B := C * dgCylinderIntegral O a b (dgTruncationCutoffError σ k u ζ) +
    C * F * dgCylinderIntegral O a b (dgTruncationForcingDensity σ k u ζ) +
    C * dgSliceEnergy O v ζ a
  Integrable H (productVolume O (Ioo a b)) ∧
  Integrable (dgTruncationCutoffError σ k u ζ) (productVolume O (Ioo a b)) ∧
  Integrable (dgTruncationForcingDensity σ k u ζ) (productVolume O (Ioo a b)) ∧
  (∀ t ∈ Icc a b, Integrable (fun x => (v (x,t))^2 * (ζ (x,t))^2) (volume.restrict O) ∧
    dgSliceEnergy O v ζ t + ν * dgCylinderIntegral O a b H ≤ B) ∧
  Integrable (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z))
    (productVolume O (Ioo a b)) ∧
  ν * dgCylinderIntegral O a b
    (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)) ≤ B

/-- Initial energy really disappears when the actual cutoff vanishes initially. -/
theorem dgSliceEnergy_eq_zero_of_cutoff_zero {n : ℕ} (O : Set (Space n))
    (v ζ : Point n → ℝ) (a : ℝ) (hζ : ∀ x ∈ O, ζ (x,a) = 0) :
    dgSliceEnergy O v ζ a = 0 := by
  unfold dgSliceEnergy
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  rw [hζ x hx,zero_pow (by decide : 2 ≠ 0),mul_zero]

/-- Actual nonnegative spatially weighted mean of any signed level truncation. -/
def dgTruncationMean {n : ℕ} (O : Set (Space n)) (φ : Space n → ℝ)
    (σ k : ℝ) (u : Point n → ℝ) (t : ℝ) : ℝ :=
  ∫ x in O, φ x * dgTruncation σ k u (x,t)

/-- The signed-level positive-part mean is continuous under only the actual
closed-slab continuity of the solution. -/
theorem dgTruncationMean_continuousOn {n : ℕ} {O : Set (Space n)} {J : Set ℝ}
    (hO : IsOpen O) {u : Point n → ℝ} (hu : ContinuousOn u (O ×ˢ J))
    {φ : Space n → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (σ k : ℝ) :
    ContinuousOn (dgTruncationMean O φ σ k u) J := by
  have hw : ContinuousOn (fun z => σ * u z - k) (O ×ˢ J) :=
    (continuousOn_const.mul hu).sub continuousOn_const
  exact dgPositivePartMean_continuousOn hO hw hφ hcφ hφO

/-- The actual positive-part subsolution integrand; the matrix is never differentiated
in the estimate and the forcing bound is independent of the solution. -/
def dgTruncationMeanDensity {n : ℕ} (A : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) (φ : Space n → ℝ) (F σ k : ℝ)
    (u : Point n → ℝ) (z : Point n) : ℝ :=
  -(∑ i, ∑ j, A z i j * dgTruncationGradient σ k u z j * d φ z.1 i) +
    (∑ i, c z i * dgTruncationGradient σ k u z i) * φ z.1 + F * φ z.1

/-- Exact spatial L² and L¹ quantities in the time-increment estimate. -/
def dgTestL2 {n : ℕ} (O : Set (Space n)) (φ : Space n → ℝ) : ℝ :=
  Real.sqrt (∫ x in O, (φ x)^2)

def dgTestGradientL2 {n : ℕ} (O : Set (Space n)) (φ : Space n → ℝ) : ℝ :=
  Real.sqrt (∫ x in O, dgGradientSq (fun i => d φ x i))

def dgTestL1 {n : ℕ} (O : Set (Space n)) (φ : Space n → ℝ) : ℝ :=
  ∫ x in O, |φ x|

/-- Positive-part subsolution mean inequality and its one-sided square-root
increment. The energy premise in the second component is the actual integral,
not an assumed DG estimate. It is intended to be supplied by Caccioppoli. -/
def DGTruncationMeanGap : Prop :=
  ∀ n : ℕ, 0 < n → ∀ ν L D F : ℝ, 0 < ν → ν ≤ L → 0 ≤ D → 0 ≤ F →
  ∀ (x₀ : Space n) (R l r s t : ℝ), 0 < R → l < s → s < t → t ≤ r →
  ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ)
    (φ : Space n → ℝ),
  let O := Metric.ball x₀ R
  let U := O ×ˢ Ioo l r
  DGClassicalFields U A c f u → ClassicalDivEq U A c f u →
  DGUniformBounds U A c f ν L D F → ContinuousOn u (O ×ˢ Icc s t) →
  ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O → (∀ x, 0 ≤ φ x) →
  ∀ σ k : ℝ, DGSign σ →
  let h := dgTruncationMean O φ σ k u
  let G := dgTruncationMeanDensity A c φ F σ k u
  Integrable G (productVolume O (Ioo s t)) ∧
  h t - h s ≤ dgCylinderIntegral O s t G ∧
  ContinuousOn h (Icc s t) ∧
  ∀ E : ℝ, 0 ≤ E →
    Integrable (fun z => dgGradientSq (dgTruncationGradient σ k u z))
      (productVolume O (Ioo s t)) →
    dgCylinderIntegral O s t (fun z => dgGradientSq (dgTruncationGradient σ k u z)) ≤ E →
    h t - h s ≤ (L * dgTestGradientL2 O φ + D * dgTestL2 O φ) * Real.sqrt E *
      Real.sqrt (t-s) + F * dgTestL1 O φ * (t-s)

/-- The exact C¹ primitive of the positive part, including zero. -/
def dgPosPrimitive (r : ℝ) : ℝ := ∫ q in (0 : ℝ)..r, dgPositivePart q

theorem dgPosPrimitive_hasDerivAt (r : ℝ) :
    HasDerivAt dgPosPrimitive (dgPositivePart r) r := by
  have hc := dgPositivePart_lipschitz.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem dgPosPrimitive_eq (r : ℝ) :
    dgPosPrimitive r = (dgPositivePart r)^2 / 2 := by
  rcases le_total r 0 with hr | hr
  · have he : (∫ q in (0 : ℝ)..r, dgPositivePart q) = ∫ _q in (0 : ℝ)..r, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_ge hr] at hq
      exact dgPositivePart_of_nonpos hq.2
    rw [dgPosPrimitive,he,dgPositivePart_of_nonpos hr]
    simp
  · have he : (∫ q in (0 : ℝ)..r, dgPositivePart q) = ∫ q in (0 : ℝ)..r, q := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le hr] at hq
      exact dgPositivePart_of_nonneg hq.1
    have hftc : (∫ q in (0 : ℝ)..r, q) = r^2/2 := by
      have hd (q : ℝ) : HasDerivAt (fun x : ℝ => x^2/2) q q := by
        convert ((hasDerivAt_id q).pow 2).div_const 2 using 1 <;>
          simp only [id_eq,Pi.pow_apply] <;> ring
      have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun q _ => hd q) (continuous_id.intervalIntegrable 0 r)
      simpa only [zero_pow (by decide : 2 ≠ 0),zero_div,sub_zero] using hh
    rw [dgPosPrimitive,he,hftc,dgPositivePart_of_nonneg hr]

/-- One-sided smooth derivative of the positive-part approximation. -/
def dgSmoothStep (ε r : ℝ) : ℝ := Real.smoothTransition (r / ε)

/-- A concrete smooth convex approximation, vanishing on the whole negative half-line. -/
def dgSmoothPos (ε r : ℝ) : ℝ := ∫ q in (0 : ℝ)..r, dgSmoothStep ε q

theorem dgSmoothStep_contDiff (ε : ℝ) : ContDiff ℝ ∞ (dgSmoothStep ε) := by
  exact Real.smoothTransition.contDiff.comp (contDiff_id.div_const ε)

theorem dgSmoothPos_hasDerivAt (ε r : ℝ) :
    HasDerivAt (dgSmoothPos ε) (dgSmoothStep ε r) r := by
  have hc := (dgSmoothStep_contDiff ε).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem dgSmoothPos_contDiff (ε : ℝ) : ContDiff ℝ ∞ (dgSmoothPos ε) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun r => (dgSmoothPos_hasDerivAt ε r).differentiableAt,?_⟩
  have he : deriv (dgSmoothPos ε) = dgSmoothStep ε :=
    funext fun r => (dgSmoothPos_hasDerivAt ε r).deriv
  rw [he]
  exact dgSmoothStep_contDiff ε

theorem dgSmoothStep_deriv_nonneg {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    0 ≤ deriv (dgSmoothStep ε) r := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  exact Real.smoothTransition.monotone ((div_le_div_iff_of_pos_right hε).mpr hxy)

theorem dgSmoothStep_bounds (ε r : ℝ) :
    0 ≤ dgSmoothStep ε r ∧ dgSmoothStep ε r ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem dgSmoothStep_zero {ε r : ℝ} (hε : 0 < ε) (hr : r ≤ 0) :
    dgSmoothStep ε r = 0 := Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hr hε.le)

theorem dgSmoothStep_one {ε r : ℝ} (hε : 0 < ε) (hr : ε ≤ r) :
    dgSmoothStep ε r = 1 := Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hε).mpr (by simpa using hr))

/-- The actual principal bilinear expression, with the flux index order. -/
def dgBilinear {n : ℕ} (A : Mat n) (p q : Yau.RIdx n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * p j * q i

theorem dgGradientSq_nonneg {n : ℕ} (p : Yau.RIdx n → ℝ) :
    0 ≤ dgGradientSq p := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Symmetry and quadratic ellipticity give the exact operator bound L. -/
theorem dg_elliptic_bilinear_bound {n : ℕ} {U : Set (Point n)}
    {A : Point n → Mat n} {ν L : ℝ} (hA : Elliptic U A ν L)
    {z : Point n} (hz : z ∈ U) (p q : Yau.RIdx n → ℝ) :
    |dgBilinear (A z) p q| ≤ L * Real.sqrt (dgGradientSq p) * Real.sqrt (dgGradientSq q) := by
  have hquad (v : Yau.RIdx n → ℝ) :
      ν * dgGradientSq v ≤ dgBilinear (A z) v v ∧
      dgBilinear (A z) v v ≤ L * dgGradientSq v := by
    have hh := (hA.2.2 z hz).2 v
    have he : (∑ i, ∑ j, A z i j * v i * v j) = dgBilinear (A z) v v := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    simpa only [he,dgGradientSq] using hh
  have hrepr (v w : Yau.RIdx n → ℝ) :
      v ⬝ᵥ (A z).mulVec w = dgBilinear (A z) w v := by
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,dgBilinear,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpos : (A z).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      simpa only [Matrix.conjTranspose_apply,star_trivial] using (hA.2.2 z hz).1.apply i j
    · intro v hv
      simp only [star_trivial,hrepr]
      obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra! h
        exact hv (funext h)
      have hs : 0 < dgGradientSq v :=
        (sq_pos_of_ne_zero hi).trans_le (Finset.single_le_sum
          (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
      exact (mul_pos hA.1 hs).trans_le (hquad v).1
  have hcs := hpos.star_dotProduct_mulVec_mul_le q p
  simp only [star_trivial,hrepr] at hcs
  have hLq : 0 ≤ L * dgGradientSq q :=
    mul_nonneg (hA.1.le.trans hA.2.1) (dgGradientSq_nonneg q)
  have hQp : 0 ≤ dgBilinear (A z) p p :=
    (mul_nonneg hA.1.le (dgGradientSq_nonneg p)).trans (hquad p).1
  have hQq : 0 ≤ dgBilinear (A z) q q :=
    (mul_nonneg hA.1.le (dgGradientSq_nonneg q)).trans (hquad q).1
  have hprod := mul_le_mul (hquad q).2 (hquad p).2 hQp hLq
  have hL : 0 ≤ L := hA.1.le.trans hA.2.1
  have hsP := Real.sq_sqrt (dgGradientSq_nonneg p)
  have hsQ := Real.sq_sqrt (dgGradientSq_nonneg q)
  have hright : 0 ≤ L * Real.sqrt (dgGradientSq p) * Real.sqrt (dgGradientSq q) := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) hright).mp
  rw [sq_abs]
  calc
    _ ≤ dgBilinear (A z) q q * dgBilinear (A z) p p := by simpa only [pow_two] using hcs
    _ ≤ (L * dgGradientSq q) * (L * dgGradientSq p) := hprod
    _ = (L * Real.sqrt (dgGradientSq p) * Real.sqrt (dgGradientSq q))^2 := by
      rw [mul_pow,mul_pow,hsP,hsQ]
      ring

/-- Prefix restrictions are literal smaller-cylinder product measures. -/
theorem dg_prefix_measure {n : ℕ} {O : Set (Space n)} {a b τ : ℝ}
    (hτ : τ ≤ b) :
    (productVolume O (Ioo a b)).restrict {z : Point n | z.2 < τ} =
      productVolume O (Ioo a τ) := by
  rw [dg_productVolume_eq_restrict,Measure.restrict_restrict
    (isOpen_lt continuous_snd continuous_const).measurableSet,dg_productVolume_eq_restrict]
  congr 1
  ext z
  simp only [mem_inter_iff,mem_setOf_eq,mem_prod,mem_Ioo]
  constructor
  · rintro ⟨hz, hO, ha, _hb⟩
    exact ⟨hO,ha,hz⟩
  · rintro ⟨hO,ha,hz⟩
    exact ⟨hz,hO,ha,hz.trans_le hτ⟩

/-- Nonnegative prefix bounds establish full-slab integrability before taking
any real integral on the top-touching slab. `AECover` uses monotone convergence
for the existence of that integral and dominated convergence only afterwards. -/
theorem dg_fullSlab_integrable_of_prefix_bounds {n : ℕ}
    {O : Set (Space n)} (hO : IsOpen O) {a b M : ℝ} {H : Point n → ℝ}
    (hab : a < b) (hM : 0 ≤ M)
    (hm : AEStronglyMeasurable H (productVolume O (Ioo a b)))
    (hn : ∀ᵐ z ∂productVolume O (Ioo a b), 0 ≤ H z)
    (hp : ∀ τ ∈ Ioo a b,
      Integrable H (productVolume O (Ioo a τ)) ∧ dgCylinderIntegral O a τ H ≤ M) :
    Integrable H (productVolume O (Ioo a b)) ∧ dgCylinderIntegral O a b H ≤ M := by
  let μ := productVolume O (Ioo a b)
  let S : ℝ → Set (Point n) := fun τ => if τ ∈ Ioo a b then {z | z.2 < τ} else ∅
  have hSmeas (τ : ℝ) : MeasurableSet (S τ) := by
    dsimp only [S]
    split_ifs
    · exact (isOpen_lt continuous_snd continuous_const).measurableSet
    · exact MeasurableSet.empty
  have hcover : AECover μ (𝓝[<] b) S := by
    refine ⟨?_,hSmeas⟩
    have hmem : ∀ᵐ z ∂μ, z ∈ O ×ˢ Ioo a b := by
      rw [show μ = volume.restrict (O ×ˢ Ioo a b) from dg_productVolume_eq_restrict O _]
      exact ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet
    filter_upwards [hmem] with z hz
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hab).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds hz.2.2).filter_mono nhdsWithin_le_nhds] with τ hτb haτ hzτ
    simp only [S,ite_eq_left (show τ ∈ Ioo a b from ⟨haτ,hτb⟩),mem_setOf_eq]
    exact hzτ
  have hprefix (τ : ℝ) (hτ : τ ∈ Ioo a b) : μ.restrict (S τ) = productVolume O (Ioo a τ) := by
    rw [show S τ = {z : Point n | z.2 < τ} from if_pos hτ]
    exact dg_prefix_measure hτ.2.le
  have hfi (τ : ℝ) : IntegrableOn H (S τ) μ := by
    by_cases hτ : τ ∈ Ioo a b
    · rw [IntegrableOn,hprefix τ hτ]
      exact (hp τ hτ).1
    · simp only [S,ite_eq_right hτ,integrableOn_empty]
  have hbound : ∀ τ, (∫ z in S τ, H z ∂μ) ≤ M := by
    intro τ
    by_cases hτ : τ ∈ Ioo a b
    · rw [hprefix τ hτ]
      exact (hp τ hτ).2
    · simp only [S,ite_eq_right hτ,setIntegral_empty]
      exact hM
  have hInt : Integrable H μ := hcover.integrable_of_integral_bounded_of_nonneg_ae
    M hfi hn (.of_forall hbound)
  refine ⟨hInt,?_⟩
  exact le_of_tendsto (hcover.integral_tendsto_of_countably_generated hInt) (.of_forall hbound)

theorem dgTimeDeriv_eq_joint_fderiv {n : ℕ} {u : Point n → ℝ} {z : Point n}
    (hu : DifferentiableAt ℝ u z) :
    deriv (fun t => u (z.1,t)) z.2 = fderiv ℝ u z (0,1) := by
  have hMap : HasFDerivAt (fun t : ℝ => (z.1,t))
      ((0 : ℝ →L[ℝ] Space n).prod (ContinuousLinearMap.id ℝ ℝ)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  exact (hu.hasFDerivAt.comp z.2 hMap).hasDerivAt.deriv

theorem dgGradient_contDiffOn {n : ℕ} {U : Set (Point n)} (hU : IsOpen U)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (i : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (fun z => dgGradient u z i) U := by
  have hd := (hu.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Point n => (Yau.realVec i,(0 : ℝ))) U)
  apply hd.congr
  intro z hz
  exact dgGradient_eq_joint_fderiv ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) i

theorem dgTimeDeriv_contDiffOn {n : ℕ} {U : Set (Point n)} (hU : IsOpen U)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (fun z => deriv (fun t => u (z.1,t)) z.2) U := by
  have hd := (hu.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Point n => ((0,1) : Point n)) U)
  apply hd.congr
  intro z hz
  exact dgTimeDeriv_eq_joint_fderiv ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))

/-- A spatially supported continuous function is integrable on the whole slab. -/
theorem dg_integrable_of_compact_spatial_support {n : ℕ} {O K : Set (Space n)}
    (hO : IsOpen O) (hK : IsCompact K) {a b : ℝ} {f : Point n → ℝ}
    (hf : ContinuousOn f (K ×ˢ Icc a b))
    (hz : ∀ z ∈ O ×ˢ Ioo a b, z.1 ∉ K → f z = 0) :
    Integrable f (productVolume O (Ioo a b)) := by
  rw [dg_productVolume_eq_restrict]
  have hcomp := hf.integrableOn_compact (μ := volume) (hK.prod isCompact_Icc)
  apply hcomp.of_ae_sdiff_eq_zero (hO.prod isOpen_Ioo).measurableSet.nullMeasurableSet
  apply Filter.Eventually.of_forall
  intro z hzdiff
  apply hz z hzdiff.1
  intro hx
  exact hzdiff.2 ⟨hx,Ioo_subset_Icc_self hzdiff.1.2⟩

/-- Spatial cutoff derivatives vanish off the same fixed compact set. -/
theorem dg_cutoff_gradient_zero {n : ℕ} {K : Set (Space n)} (hK : IsClosed K)
    {ζ : Point n → ℝ} {a b : ℝ}
    (hz : ∀ z : Point n, z.2 ∈ Icc a b → z.1 ∉ K → ζ z = 0)
    {z : Point n} (ht : z.2 ∈ Icc a b) (hx : z.1 ∉ K) (i : Yau.RIdx n) :
    dgGradient ζ z i = 0 := by
  have he : (fun x => ζ (x,z.2)) =ᶠ[𝓝 z.1] (fun _ => (0 : ℝ)) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with x hxK
    exact hz (x,z.2) ht hxK
  unfold dgGradient d
  rw [he.fderiv_eq]
  simp

theorem dg_cutoff_time_zero {n : ℕ} {K : Set (Space n)} {ζ : Point n → ℝ} {a b : ℝ}
    (hz : ∀ z : Point n, z.2 ∈ Icc a b → z.1 ∉ K → ζ z = 0)
    {z : Point n} (ht : z.2 ∈ Ioo a b) (hx : z.1 ∉ K) :
    deriv (fun t => ζ (z.1,t)) z.2 = 0 := by
  have he : (fun t => ζ (z.1,t)) =ᶠ[𝓝 z.2] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with t htJ
    exact hz (z.1,t) (Ioo_subset_Icc_self htJ) hx
  rw [he.deriv_eq]
  exact deriv_const _ _

/-- Weighted slice energies are continuous at both actual time faces. -/
theorem dgSliceEnergy_continuousOn {n : ℕ} {O : Set (Space n)}
    {a b σ k : ℝ} {u ζ : Point n → ℝ} (hO : IsOpen O)
    (hu : ContinuousOn u (O ×ˢ Icc a b)) (hζ : DGSpatialCutoff O a b ζ) :
    ContinuousOn (dgSliceEnergy O (dgTruncation σ k u) ζ) (Icc a b) := by
  obtain ⟨hζs,_hζr,K,hK,hKO,hzero⟩ := hζ
  let v := dgTruncation σ k u
  have hv : ContinuousOn v (O ×ˢ Icc a b) :=
    dgPositivePart_lipschitz.continuous.comp_continuousOn
      ((continuousOn_const.mul hu).sub continuousOn_const)
  let f : Point n → ℝ := fun z => (v z)^2 * (ζ z)^2
  have hf : ContinuousOn f (univ ×ˢ Icc a b) := by
    intro z hz
    by_cases hx : z.1 ∈ K
    · have hc : ContinuousWithinAt f (O ×ˢ Icc a b) z :=
        ((hv z ⟨hKO hx,hz.2⟩).pow 2).mul (hζs.continuous.continuousWithinAt.pow 2)
      apply hc.mono_of_mem_nhdsWithin
      have hnear : ∀ᶠ q : Point n in 𝓝 z, q.1 ∈ O :=
        (hO.preimage continuous_fst).mem_nhds (hKO hx)
      filter_upwards [self_mem_nhdsWithin,hnear.filter_mono nhdsWithin_le_nhds] with q hq hqO
      exact ⟨hqO,hq.2⟩
    · have hval : f z = 0 := by simp [f,hzero z hz.2 hx]
      apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq _ hval
      have hnear : ∀ᶠ q : Point n in 𝓝 z, q.1 ∉ K :=
        (hK.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hx
      filter_upwards [self_mem_nhdsWithin,hnear.filter_mono nhdsWithin_le_nhds] with q hq hqK
      simp only [f,hzero q hq.2 hqK,zero_pow (by decide : 2 ≠ 0),mul_zero]
  have hfSwap : ContinuousOn (fun p : ℝ × Space n => f (p.2,p.1)) (Icc a b ×ˢ univ) :=
    hf.comp continuous_swap.continuousOn (fun p hp => ⟨hp.2,hp.1⟩)
  have hc : ContinuousOn (fun t => ∫ x, f (x,t)) (Icc a b) :=
    continuousOn_integral_of_compact_support (f := fun t x => f (x,t)) hK hfSwap (fun t x ht hx => by
    simp only [f,hzero (x,t) ht hx,zero_pow (by decide : 2 ≠ 0),mul_zero])
  apply hc.congr
  intro t _ht
  unfold dgSliceEnergy
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hxK : x ∉ K := fun h => hx (hKO h)
  simp only [hzero (x,t) _ht hxK,zero_pow (by decide : 2 ≠ 0),mul_zero]

/-- Taking a strict positive-set indicator preserves actual local integrability. -/
theorem dg_active_integrable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] {μ : Measure E} {O : Set E} (hO : IsOpen O)
    {w H : E → ℝ} (hw : ContinuousOn w O) (hH : Integrable H (μ.restrict O)) :
    Integrable (fun x => if 0 < w x then H x else 0) (μ.restrict O) := by
  let S := O ∩ w ⁻¹' Ioi 0
  have hS : MeasurableSet S := (hw.isOpen_inter_preimage hO isOpen_Ioi).measurableSet
  have hi := hH.indicator hS
  apply hi.congr
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  change S.indicator H x = if 0 < w x then H x else 0
  by_cases hp : 0 < w x
  · rw [indicator_of_mem (show x ∈ S from ⟨hx,hp⟩),ite_eq_left hp]
  · rw [indicator_of_notMem (show x ∉ S from fun h => hp h.2),ite_eq_right hp]

/-- A continuous spatial function with a prescribed compact support is locally
integrable; behavior away from the open spatial region is irrelevant. -/
theorem dg_integrable_spatial {n : ℕ} {O K : Set (Space n)} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) {g : Space n → ℝ}
    (hg : ContinuousOn g O) (hz : ∀ x ∈ O, x ∉ K → g x = 0) :
    Integrable g (volume.restrict O) := by
  have hki : IntegrableOn g K volume := (hg.mono hKO).integrableOn_compact hK
  apply hki.of_ae_sdiff_eq_zero hO.measurableSet.nullMeasurableSet
  exact .of_forall (fun x hx => hz x hx.1 hx.2)

/-- Finite-time FTC integrated in space, with the actual initial and final
slices. All integrability is established before Fubini is invoked. -/
theorem dg_finiteTime_integral_identity {n : ℕ} {O K : Set (Space n)}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O) {a b : ℝ} (hab : a ≤ b)
    {g g' : Point n → ℝ} (hg : ContinuousOn g (O ×ˢ Icc a b))
    (hg' : ContinuousOn g' (O ×ˢ Icc a b))
    (hgzero : ∀ z ∈ O ×ˢ Icc a b, z.1 ∉ K → g z = 0)
    (hg'zero : ∀ z ∈ O ×ˢ Icc a b, z.1 ∉ K → g' z = 0)
    (hd : ∀ x ∈ O, ∀ t ∈ Ioo a b, HasDerivAt (fun q => g (x,q)) (g' (x,t)) t) :
    Integrable g' (productVolume O (Ioo a b)) ∧
    dgCylinderIntegral O a b g' = (∫ x in O, g (x,b)) - ∫ x in O, g (x,a) := by
  have hprod : Integrable g' (productVolume O (Ioo a b)) :=
    dg_integrable_of_compact_spatial_support hO hK
      (hg'.mono (Set.prod_mono hKO Subset.rfl))
      (fun z hz hx => hg'zero z ⟨hz.1,Ioo_subset_Icc_self hz.2⟩ hx)
  have hslice (t : ℝ) (ht : t ∈ Icc a b) : Integrable (fun x => g (x,t)) (volume.restrict O) := by
    apply dg_integrable_spatial hO hK hKO
    · exact hg.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx,ht⟩)
    · exact fun x hx hxK => hgzero (x,t) ⟨hx,ht⟩ hxK
  have hftc (x : Space n) (hx : x ∈ O) :
      (∫ t in Ioo a b, g' (x,t)) = g (x,b) - g (x,a) := by
    have hc := hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hx,ht⟩)
    have hc' := hg'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hx,ht⟩)
    change ContinuousOn (fun t => g (x,t)) (Icc a b) at hc
    change ContinuousOn (fun t => g' (x,t)) (Icc a b) at hc'
    have hint : IntervalIntegrable (fun t => g' (x,t)) volume a b := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le hab] using hc'
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc (hd x hx) hint
    rwa [intervalIntegral.integral_of_le hab,integral_Ioc_eq_integral_Ioo] at h
  refine ⟨hprod,?_⟩
  unfold dgCylinderIntegral productVolume
  rw [integral_prod _ hprod,← integral_sub (hslice b ⟨hab,le_rfl⟩) (hslice a ⟨le_rfl,hab⟩)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  exact hftc x hx

theorem dgSmoothPos_zero {ε r : ℝ} (hε : 0 < ε) (hr : r ≤ 0) :
    dgSmoothPos ε r = 0 := by
  have he : (∫ q in (0 : ℝ)..r, dgSmoothStep ε q) = ∫ _q in (0 : ℝ)..r, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_ge hr] at hq
    exact dgSmoothStep_zero hε hq.2
  exact he.trans (intervalIntegral.integral_zero)

theorem dgSmoothPos_bounds {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    0 ≤ dgSmoothPos ε r ∧ dgSmoothPos ε r ≤ dgPositivePart r := by
  rcases le_total r 0 with hr | hr
  · simp only [dgSmoothPos_zero hε hr,dgPositivePart_of_nonpos hr,le_refl,and_self]
  · have hlo : 0 ≤ dgSmoothPos ε r := intervalIntegral.integral_nonneg_of_forall hr
      (fun q => (dgSmoothStep_bounds ε q).1)
    have hup : dgSmoothPos ε r ≤ ∫ _q in (0 : ℝ)..r, (1 : ℝ) :=
      intervalIntegral.integral_mono_on (μ := volume) hr ((dgSmoothStep_contDiff ε).continuous.intervalIntegrable 0 r)
        (continuous_const.intervalIntegrable 0 r) (fun q _ => (dgSmoothStep_bounds ε q).2)
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hup
    exact ⟨hlo,hup.trans_eq (dgPositivePart_of_nonneg hr).symm⟩

theorem dgSmoothPos_error {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    dgPositivePart r - dgSmoothPos ε r ≤ ε := by
  rcases le_total r 0 with hr | hr
  · rw [dgSmoothPos_zero hε hr,dgPositivePart_of_nonpos hr,sub_self]
    exact hε.le
  · rw [dgPositivePart_of_nonneg hr]
    by_cases hre : r ≤ ε
    · linarith [(dgSmoothPos_bounds hε r).1]
    · have he : ε ≤ r := le_of_not_ge hre
      have htail : (∫ q in ε..r, dgSmoothStep ε q) = r - ε := by
        have hI : (∫ q in ε..r, dgSmoothStep ε q) = ∫ _q in ε..r, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro q hq
          rw [uIcc_of_le he] at hq
          exact dgSmoothStep_one hε hq.1
        rw [hI,intervalIntegral.integral_const]
        simp only [smul_eq_mul,mul_one]
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        ((dgSmoothStep_contDiff ε).continuous.intervalIntegrable 0 ε)
        ((dgSmoothStep_contDiff ε).continuous.intervalIntegrable ε r)
      rw [htail] at hadd
      change dgSmoothPos ε ε + (r-ε) = dgSmoothPos ε r at hadd
      linarith [(dgSmoothPos_bounds hε ε).1]

theorem dgSmoothPos_tendsto {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun j => dgSmoothPos (ε j) r) atTop (𝓝 (dgPositivePart r)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun j => dgPositivePart r - ε j) atTop (𝓝 (dgPositivePart r)) by
      simpa only [sub_zero] using tendsto_const_nhds.sub hlim)
    tendsto_const_nhds
  · intro j
    linarith [dgSmoothPos_error (hε j) r]
  · intro j
    exact (dgSmoothPos_bounds (hε j) r).2

theorem dgSmoothStep_tendsto {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun j => dgSmoothStep (ε j) r) atTop (𝓝 (if 0 < r then 1 else 0)) := by
  by_cases hr : 0 < r
  · rw [ite_eq_left hr]
    apply tendsto_const_nhds.congr'
    filter_upwards [hlim.eventually (gt_mem_nhds hr)] with j hj
    exact (dgSmoothStep_one (hε j) hj.le).symm
  · rw [ite_eq_right hr]
    have he : (fun j => dgSmoothStep (ε j) r) = fun _ => 0 :=
      funext fun j => dgSmoothStep_zero (hε j) (le_of_not_gt hr)
    rw [he]
    exact tendsto_const_nhds

/-- The exact pointwise time-chain identity used by endpoint truncation energy. -/
theorem dgPosPrimitive_mul_square_hasDerivAt {w ζ : ℝ → ℝ} {dw dζ t : ℝ}
    (hw : HasDerivAt w dw t) (hζ : HasDerivAt ζ dζ t) :
    HasDerivAt (fun q => dgPosPrimitive (w q) * (ζ q)^2)
      (dgPositivePart (w t)*dw*(ζ t)^2 + (dgPositivePart (w t))^2*ζ t*dζ) t := by
  have hp : HasDerivAt (fun q => dgPosPrimitive (w q)) (dgPositivePart (w t)*dw) t :=
    (dgPosPrimitive_hasDerivAt (w t)).comp t hw
  convert hp.mul (hζ.pow 2) using 1 <;> simp only [dgPosPrimitive_eq,Pi.pow_apply] <;> ring

/-- Local positive-part IBP with a genuinely smooth compact test. The flux
is smoothly extended only near that test, and no nonsmooth test is licensed. -/
theorem dg_positivepart_flux_ibp {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {w P η : Space n → ℝ} (hw : ContDiffOn ℝ ∞ w O)
    (hP : ContDiffOn ℝ ∞ P O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O) (e : Space n) :
    Integrable (fun x => dgPositivePart (w x)*η x*fderiv ℝ P x e) (volume.restrict O) ∧
    Integrable (fun x => dgPositivePart (w x)*P x*fderiv ℝ η x e) (volume.restrict O) ∧
    Integrable (fun x => (if 0 < w x then fderiv ℝ w x e else 0)*η x*P x) (volume.restrict O) ∧
    (∫ x in O, dgPositivePart (w x)*η x*fderiv ℝ P x e) =
      -(∫ x in O, (if 0 < w x then fderiv ℝ w x e else 0)*η x*P x) -
        ∫ x in O, dgPositivePart (w x)*P x*fderiv ℝ η x e := by
  have hdw : ContinuousOn (fun x => fderiv ℝ w x e) O :=
    ((hw.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hdP : ContinuousOn (fun x => fderiv ℝ P x e) O :=
    ((hP.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hdη : Continuous (fun x => fderiv ℝ η x e) :=
    ((hη.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hv : ContinuousOn (fun x => dgPositivePart (w x)) O :=
    dgPositivePart_lipschitz.continuous.comp_continuousOn hw.continuousOn
  have hIA : Integrable (fun x => dgPositivePart (w x)*η x*fderiv ℝ P x e) (volume.restrict O) := by
    apply dg_integrable_spatial hO hcη hηO ((hv.mul hη.continuous.continuousOn).mul hdP)
    intro x _ hx
    change dgPositivePart (w x)*η x*fderiv ℝ P x e = 0
    simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero,zero_mul]
  have hIB : Integrable (fun x => dgPositivePart (w x)*P x*fderiv ℝ η x e) (volume.restrict O) := by
    apply dg_integrable_spatial hO hcη hηO ((hv.mul hP.continuousOn).mul hdη.continuousOn)
    intro x _ hx
    change dgPositivePart (w x)*P x*fderiv ℝ η x e = 0
    rw [fderiv_of_notMem_tsupport ℝ hx]; simp
  have hIC0 : Integrable (fun x => fderiv ℝ w x e*η x*P x) (volume.restrict O) := by
    apply dg_integrable_spatial hO hcη hηO ((hdw.mul hη.continuous.continuousOn).mul hP.continuousOn)
    intro x _ hx
    change fderiv ℝ w x e*η x*P x = 0
    simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero,zero_mul]
  have hIC : Integrable (fun x => (if 0 < w x then fderiv ℝ w x e else 0)*η x*P x) (volume.restrict O) := by
    apply (dg_active_integrable hO hw.continuousOn hIC0).congr
    apply Filter.Eventually.of_forall
    intro x
    dsimp only
    split_ifs <;> simp
  obtain ⟨Pe,hPe,hcPe,hnear⟩ := dg_smooth_compact_extension hO hcη hηO hP
  let ψ : Space n → ℝ := fun x => η x * Pe x
  have hψ : ContDiff ℝ ∞ ψ := hη.mul hPe
  have hcψ : HasCompactSupport ψ := hcη.mul_right
  have hψO : tsupport ψ ⊆ O := tsupport_mul_subset_left.trans hηO
  have hψval (x : Space n) : ψ x = η x * P x := by
    by_cases hx : x ∈ tsupport η
    · dsimp only [ψ]
      rw [(hnear x hx).eq_of_nhds]
    · simp only [ψ,image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hψderiv (x : Space n) : fderiv ℝ ψ x e =
      η x * fderiv ℝ P x e + P x * fderiv ℝ η x e := by
    dsimp only [ψ]
    rw [fderiv_fun_mul (hη.differentiable (by simp) x) (hPe.differentiable (by simp) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    by_cases hx : x ∈ tsupport η
    · rw [(hnear x hx).eq_of_nhds,(hnear x hx).fderiv_eq (𝕜 := ℝ)]
    · rw [image_eq_zero_of_notMem_tsupport hx,fderiv_of_notMem_tsupport ℝ hx]
      simp
  have hweak := dgPositivePart_weak_chain_local (μ := volume) hO hw hψ hcψ hψO e
  have hL : (∫ x in O, dgPositivePart (w x)*fderiv ℝ ψ x e) =
      (∫ x in O, dgPositivePart (w x)*η x*fderiv ℝ P x e) +
        ∫ x in O, dgPositivePart (w x)*P x*fderiv ℝ η x e := by
    calc
      _ = ∫ x in O, dgPositivePart (w x)*η x*fderiv ℝ P x e +
          dgPositivePart (w x)*P x*fderiv ℝ η x e := by
        apply setIntegral_congr_fun hO.measurableSet
        intro x _
        dsimp only
        rw [hψderiv]; ring
      _ = _ := integral_add hIA hIB
  have hR : (∫ x in O, (if 0 < w x then fderiv ℝ w x e else 0)*ψ x) =
      ∫ x in O, (if 0 < w x then fderiv ℝ w x e else 0)*η x*P x := by
    apply setIntegral_congr_fun hO.measurableSet
    intro x _
    dsimp only
    rw [hψval]; ring
  rw [hL,hR] at hweak
  exact ⟨hIA,hIB,hIC,by linarith⟩

def dgFlux {n : ℕ} (A : Point n → Mat n) (u : Point n → ℝ)
    (z : Point n) (i : Yau.RIdx n) : ℝ := ∑ j, A z i j * dgGradient u z j

theorem dgFlux_contDiffOn {n : ℕ} {U : Set (Point n)} (hU : IsOpen U)
    {A : Point n → Mat n} {u : Point n → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U)
    (hu : ContDiffOn ℝ ∞ u U) (i : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (fun z => dgFlux A u z i) U := by
  apply ContDiffOn.sum
  intro j _
  exact (hA i j).mul (dgGradient_contDiffOn hU hu j)

theorem dgGradient_affine {n : ℕ} {u : Point n → ℝ} {z : Point n}
    (hu : DifferentiableAt ℝ u z) (σ k : ℝ) (i : Yau.RIdx n) :
    dgGradient (fun q => σ*u q-k) z i = σ*dgGradient u z i := by
  rw [dgGradient_eq_joint_fderiv ((hu.const_mul σ).sub_const k) i,
    fderiv_sub_const,fderiv_const_mul hu]
  rw [dgGradient_eq_joint_fderiv hu i]
  rfl

theorem dgTimeDeriv_affine {n : ℕ} {u : Point n → ℝ} {z : Point n}
    (hu : DifferentiableAt ℝ u z) (σ k : ℝ) :
    deriv (fun t => σ*u (z.1,t)-k) z.2 = σ * deriv (fun t => u (z.1,t)) z.2 := by
  have h := dgTimeDeriv_eq_joint_fderiv
    (u := fun q => σ*u q-k) ((hu.const_mul σ).sub_const k)
  change deriv (fun t => σ*u (z.1,t)-k) z.2 = _ at h
  rw [h,fderiv_sub_const,fderiv_const_mul hu,dgTimeDeriv_eq_joint_fderiv hu]
  rfl

/-- Affine sign/level changes preserve the literal classical divergence equation. -/
theorem dgClassicalDivEq_affine {n : ℕ} {U : Set (Point n)} (hU : IsOpen U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hfields : DGClassicalFields U A c f u) (hpde : ClassicalDivEq U A c f u) (σ k : ℝ) :
    ClassicalDivEq U A c (fun z => σ*f z) (fun z => σ*u z-k) := by
  let w : Point n → ℝ := fun z => σ*u z-k
  have hw : ContDiffOn ℝ ∞ w U := (contDiffOn_const.mul hfields.2.2.2).sub contDiffOn_const
  have hFu (i : Yau.RIdx n) := dgFlux_contDiffOn hU hfields.1 hfields.2.2.2 i
  have hFw (i : Yau.RIdx n) := dgFlux_contDiffOn hU hfields.1 hw i
  have hval (z : Point n) (hz : z ∈ U) (i : Yau.RIdx n) :
      dgFlux A w z i = σ*dgFlux A u z i := by
    have huz := (hfields.2.2.2.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have hgradw (j : Yau.RIdx n) : dgGradient w z j = σ*dgGradient u z j := dgGradient_affine huz σ k j
    change (∑ j, A z i j*dgGradient w z j) = σ*(∑ j, A z i j*dgGradient u z j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hgradw]
    ring
  intro z hz
  have huz := (hfields.2.2.2.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hdiv (i : Yau.RIdx n) :
      d (fun x => dgFlux A w (x,z.2) i) z.1 i =
        σ*d (fun x => dgFlux A u (x,z.2) i) z.1 i := by
    have he : (fun q => dgFlux A w q i) =ᶠ[𝓝 z] (fun q => σ*dgFlux A u q i) := by
      filter_upwards [hU.mem_nhds hz] with q hq
      exact hval q hq i
    change dgGradient (fun q => dgFlux A w q i) z i = σ*dgGradient (fun q => dgFlux A u q i) z i
    rw [dgGradient_eq_joint_fderiv ((hFw i).contDiffAt (hU.mem_nhds hz)|>.differentiableAt (by simp)) i,
      he.fderiv_eq,fderiv_const_mul ((hFu i).contDiffAt (hU.mem_nhds hz)|>.differentiableAt (by simp)),
      dgGradient_eq_joint_fderiv ((hFu i).contDiffAt (hU.mem_nhds hz)|>.differentiableAt (by simp)) i]
    rfl
  have hsum := congrArg (fun v : ℝ => σ*v) (hpde z hz)
  change deriv (fun t => σ*u (z.1,t)-k) z.2 -
    (∑ i, d (fun x => dgFlux A w (x,z.2) i) z.1 i) =
      (∑ i, c z i*dgGradient w z i)+σ*f z
  rw [dgTimeDeriv_affine huz]
  have hgradw (j : Yau.RIdx n) : dgGradient w z j = σ*dgGradient u z j := dgGradient_affine huz σ k j
  simp_rw [hdiv,hgradw]
  simp only [Finset.mul_sum,mul_sub,mul_add] at hsum
  have hcsum : (∑ i, c z i*(σ*dgGradient u z i)) = ∑ i, σ*(c z i*dgGradient u z i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcsum]
  exact hsum

/-- Cutoff errors, the linear forcing density, and all endpoint slices are
integrable before the gradient energy estimate is known. -/
theorem dg_cutoff_quantities_integrable {n : ℕ} {O : Set (Space n)}
    {a b σ k : ℝ} {u ζ : Point n → ℝ} (hO : IsOpen O)
    (hu : ContinuousOn u (O ×ˢ Icc a b)) (hζ : DGSpatialCutoff O a b ζ) :
    Integrable (dgTruncationCutoffError σ k u ζ) (productVolume O (Ioo a b)) ∧
    Integrable (dgTruncationForcingDensity σ k u ζ) (productVolume O (Ioo a b)) ∧
    ∀ t ∈ Icc a b,
      Integrable (fun x => (dgTruncation σ k u (x,t))^2*(ζ (x,t))^2) (volume.restrict O) := by
  obtain ⟨hζs,_hζr,K,hK,hKO,hzero⟩ := hζ
  have hv : ContinuousOn (dgTruncation σ k u) (O ×ˢ Icc a b) :=
    dgPositivePart_lipschitz.continuous.comp_continuousOn
      ((continuousOn_const.mul hu).sub continuousOn_const)
  have hKQ : K ×ˢ Icc a b ⊆ O ×ˢ Icc a b := Set.prod_mono hKO Subset.rfl
  have hvK := hv.mono hKQ
  have hGt (i : Yau.RIdx n) : Continuous (fun z => dgGradient ζ z i) :=
    (contDiffOn_univ.mp (dgGradient_contDiffOn isOpen_univ hζs.contDiffOn i)).continuous
  have hGs : Continuous (fun z => dgGradientSq (dgGradient ζ z)) :=
    continuous_finsetSum _ (fun i _ => (hGt i).pow 2)
  have hDt : Continuous (fun z : Point n => deriv (fun t => ζ (z.1,t)) z.2) :=
    (contDiffOn_univ.mp (dgTimeDeriv_contDiffOn isOpen_univ hζs.contDiffOn)).continuous
  have hE : Integrable (dgTruncationCutoffError σ k u ζ) (productVolume O (Ioo a b)) := by
    apply dg_integrable_of_compact_spatial_support hO hK
      ((hvK.pow 2).mul (((hDt.abs.add hGs).add (hζs.continuous.pow 2)).continuousOn))
    intro z hz hx
    have hgzero : dgGradientSq (dgGradient ζ z) = 0 := by
      unfold dgGradientSq
      simp only [dg_cutoff_gradient_zero hK.isClosed hzero (Ioo_subset_Icc_self hz.2) hx,
        zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
    change (dgTruncation σ k u z)^2 * (|deriv (fun t => ζ (z.1,t)) z.2| +
      dgGradientSq (dgGradient ζ z)+(ζ z)^2) = 0
    rw [dg_cutoff_time_zero hzero hz.2 hx,hgzero,hzero z (Ioo_subset_Icc_self hz.2) hx]
    simp
  have hF : Integrable (dgTruncationForcingDensity σ k u ζ) (productVolume O (Ioo a b)) := by
    apply dg_integrable_of_compact_spatial_support hO hK
      (hvK.mul (hζs.continuous.pow 2).continuousOn)
    intro z hz hx
    change dgTruncation σ k u z*(ζ z)^2 = 0
    simp only [hzero z (Ioo_subset_Icc_self hz.2) hx,zero_pow (by decide : 2 ≠ 0),mul_zero]
  refine ⟨hE,hF,?_⟩
  intro t ht
  apply dg_integrable_spatial hO hK hKO
  · exact ((hv.pow 2).mul (hζs.continuous.pow 2).continuousOn).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx,ht⟩)
  · intro x _ hx
    change (dgTruncation σ k u (x,t))^2*(ζ (x,t))^2 = 0
    simp only [hzero (x,t) ht hx,zero_pow (by decide : 2 ≠ 0),mul_zero]

/-- A finite sum of legitimate positive-part flux IBPs at one time. -/
def dgSpatialFluxBalance {n : ℕ} (w η : Space n → ℝ)
    (P : Space n → Yau.RIdx n → ℝ) (x : Space n) : ℝ :=
  ∑ i, (dgPositivePart (w x)*(η x)^2*d (fun y => P y i) x i +
    (if 0 < w x then d w x i else 0)*(η x)^2*P x i +
    dgPositivePart (w x)*P x i*d (fun y => (η y)^2) x i)

theorem dgSpatialFluxBalance_integral_zero {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {w η : Space n → ℝ} {P : Space n → Yau.RIdx n → ℝ}
    (hw : ContDiffOn ℝ ∞ w O) (hP : ∀ i, ContDiffOn ℝ ∞ (fun x => P x i) O)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O) :
    Integrable (dgSpatialFluxBalance w η P) (volume.restrict O) ∧
      (∫ x in O, dgSpatialFluxBalance w η P x) = 0 := by
  have hη2 : ContDiff ℝ ∞ (fun x => (η x)^2) := hη.pow 2
  have hη2supp : tsupport (fun x => (η x)^2) ⊆ tsupport η := by
    have he : (fun x => (η x)^2) = (fun x => η x*η x) := by funext x; ring
    rw [he]
    exact tsupport_mul_subset_left
  have hcη2 : HasCompactSupport (fun x => (η x)^2) :=
    (show IsCompact (tsupport η) from hcη).of_isClosed_subset (isClosed_tsupport _) hη2supp
  have hi (i : Yau.RIdx n) := dg_positivepart_flux_ibp hO hw (hP i) hη2 hcη2 (hη2supp.trans hηO)
    (Yau.realVec i)
  have hInt (i : Yau.RIdx n) : Integrable (fun x =>
      dgPositivePart (w x)*(η x)^2*d (fun y => P y i) x i +
      (if 0 < w x then d w x i else 0)*(η x)^2*P x i +
      dgPositivePart (w x)*P x i*d (fun y => (η y)^2) x i) (volume.restrict O) :=
    ((hi i).1.add (hi i).2.2.1).add (hi i).2.1
  refine ⟨integrable_finsetSum _ (fun i _ => hInt i),?_⟩
  simp only [dgSpatialFluxBalance]
  rw [integral_finsetSum _ (fun i _ => hInt i)]
  apply Finset.sum_eq_zero
  intro i _
  dsimp only [d]
  have hs1 := integral_add ((hi i).1.add (hi i).2.2.1) (hi i).2.1
  have hs2 := integral_add (hi i).1 (hi i).2.2.1
  simp only [Pi.add_apply] at hs1 hs2
  rw [hs1,hs2]
  have hh := (hi i).2.2.2
  linarith

def dgJointFluxBalance {n : ℕ} (w ζ : Point n → ℝ)
    (P : Point n → Yau.RIdx n → ℝ) (z : Point n) : ℝ :=
  ∑ i, (dgPositivePart (w z)*(ζ z)^2*dgGradient (fun q => P q i) z i +
    (if 0 < w z then dgGradient w z i else 0)*(ζ z)^2*P z i +
    dgPositivePart (w z)*P z i*dgGradient (fun q => (ζ q)^2) z i)

/-- Spatial IBP integrated on an interior finite subslab, with all mixed
positive-part flux terms proved integrable before using Fubini. -/
theorem dgJointFluxBalance_integral_zero {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r a b τ : ℝ} (hla : l < a) (haτ : a < τ) (hτb : τ < b) (hbr : b ≤ r)
    {w ζ : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hw : ContDiffOn ℝ ∞ w (O ×ˢ Ioo l r))
    (hP : ∀ i, ContDiffOn ℝ ∞ (fun z => P z i) (O ×ˢ Ioo l r))
    (hζ : DGSpatialCutoff O a b ζ) :
    Integrable (dgJointFluxBalance w ζ P) (productVolume O (Ioo a τ)) ∧
    dgCylinderIntegral O a τ (dgJointFluxBalance w ζ P) = 0 := by
  obtain ⟨hζs,_hζr,K,hK,hKO,hzero⟩ := hζ
  let U := O ×ˢ Ioo l r
  let V := O ×ˢ Ioo a τ
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hV : IsOpen V := hO.prod isOpen_Ioo
  have hclosed : O ×ˢ Icc a τ ⊆ U := by
    intro z hz
    exact ⟨hz.1,hla.trans_le hz.2.1,hz.2.2.trans_lt (hτb.trans_le hbr)⟩
  have hVU : V ⊆ U := (Set.prod_mono Subset.rfl Ioo_subset_Icc_self).trans hclosed
  have hKclosed : K ×ˢ Icc a τ ⊆ U := (Set.prod_mono hKO Subset.rfl).trans hclosed
  have htime (t : ℝ) (ht : t ∈ Icc a τ) : t ∈ Icc a b := ⟨ht.1,ht.2.trans hτb.le⟩
  have hζ2 : ContDiff ℝ ∞ (fun z => (ζ z)^2) := hζs.pow 2
  have hzero2 : ∀ z : Point n, z.2 ∈ Icc a b → z.1 ∉ K → (ζ z)^2 = 0 := by
    intro z hz hx
    rw [hzero z hz hx]; exact zero_pow (by decide : 2 ≠ 0)
  have hv : ContinuousOn (fun z => dgPositivePart (w z)) U :=
    dgPositivePart_lipschitz.continuous.comp_continuousOn hw.continuousOn
  have hA (i : Yau.RIdx n) : Integrable (fun z =>
      dgPositivePart (w z)*(ζ z)^2*dgGradient (fun q => P q i) z i)
      (productVolume O (Ioo a τ)) := by
    apply dg_integrable_of_compact_spatial_support hO hK
      (((hv.mul (hζs.continuous.pow 2).continuousOn).mul
        (dgGradient_contDiffOn hU (hP i) i).continuousOn).mono hKclosed)
    intro z hz hx
    change dgPositivePart (w z)*(ζ z)^2*dgGradient (fun q => P q i) z i = 0
    rw [hzero z (htime _ (Ioo_subset_Icc_self hz.2)) hx]; simp
  have hC0 (i : Yau.RIdx n) : Integrable (fun z =>
      dgGradient w z i*(ζ z)^2*P z i) (productVolume O (Ioo a τ)) := by
    apply dg_integrable_of_compact_spatial_support hO hK
      ((((dgGradient_contDiffOn hU hw i).continuousOn).mul
        (hζs.continuous.pow 2).continuousOn).mul (hP i).continuousOn |>.mono hKclosed)
    intro z hz hx
    change dgGradient w z i*(ζ z)^2*P z i = 0
    rw [hzero z (htime _ (Ioo_subset_Icc_self hz.2)) hx]; simp
  have hC (i : Yau.RIdx n) : Integrable (fun z =>
      (if 0 < w z then dgGradient w z i else 0)*(ζ z)^2*P z i)
      (productVolume O (Ioo a τ)) := by
    have hh : Integrable (fun z => if 0 < w z then dgGradient w z i*(ζ z)^2*P z i else 0)
        (productVolume O (Ioo a τ)) := by
      rw [dg_productVolume_eq_restrict]
      apply dg_active_integrable hV (hw.continuousOn.mono hVU)
      rw [← dg_productVolume_eq_restrict]
      exact hC0 i
    apply hh.congr
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    split_ifs <;> simp
  have hB (i : Yau.RIdx n) : Integrable (fun z =>
      dgPositivePart (w z)*P z i*dgGradient (fun q => (ζ q)^2) z i)
      (productVolume O (Ioo a τ)) := by
    apply dg_integrable_of_compact_spatial_support hO hK
      (((hv.mul (hP i).continuousOn).mul
        (dgGradient_contDiffOn hU hζ2.contDiffOn i).continuousOn).mono hKclosed)
    intro z hz hx
    change dgPositivePart (w z)*P z i*dgGradient (fun q => (ζ q)^2) z i = 0
    rw [dg_cutoff_gradient_zero hK.isClosed hzero2 (htime _ (Ioo_subset_Icc_self hz.2)) hx]
    exact mul_zero _
  have hInt : Integrable (dgJointFluxBalance w ζ P) (productVolume O (Ioo a τ)) :=
    integrable_finsetSum _ (fun i _ => ((hA i).add (hC i)).add (hB i))
  refine ⟨hInt,?_⟩
  unfold dgCylinderIntegral productVolume
  rw [integral_prod_symm _ hInt]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have htU : t ∈ Ioo l r := ⟨hla.trans ht.1,ht.2.trans (hτb.trans_le hbr)⟩
  have hws : ContDiffOn ℝ ∞ (fun x => w (x,t)) O :=
    hw.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun x hx => ⟨hx,htU⟩)
  have hPs (i : Yau.RIdx n) : ContDiffOn ℝ ∞ (fun x => P (x,t) i) O :=
    (hP i).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun x hx => ⟨hx,htU⟩)
  have hζslice : ContDiff ℝ ∞ (fun x => ζ (x,t)) := hζs.comp (contDiff_id.prodMk contDiff_const)
  have hsupp : tsupport (fun x => ζ (x,t)) ⊆ K := by
    apply hK.isClosed.closure_subset_iff.mpr
    intro x hx
    by_contra hxK
    exact hx (hzero (x,t) (htime _ (Ioo_subset_Icc_self ht)) hxK)
  have hcζslice : HasCompactSupport (fun x => ζ (x,t)) := hK.of_isClosed_subset (isClosed_tsupport _) hsupp
  exact (dgSpatialFluxBalance_integral_zero hO hws hPs hζslice hcζslice (hsupp.trans hKO)).2

def dgTruncationPrincipal {n : ℕ} (A : Point n → Mat n) (σ k : ℝ)
    (u ζ : Point n → ℝ) (z : Point n) : ℝ :=
  (ζ z)^2 * dgBilinear (A z) (dgTruncationGradient σ k u z) (dgTruncationGradient σ k u z)

def dgTruncationBalance {n : ℕ} (A : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ) (σ k : ℝ)
    (u ζ : Point n → ℝ) (z : Point n) : ℝ :=
  (dgTruncation σ k u z)^2*ζ z*deriv (fun q => ζ (z.1,q)) z.2 -
    2*dgTruncation σ k u z*ζ z*dgBilinear (A z)
      (dgTruncationGradient σ k u z) (dgGradient ζ z) +
    dgTruncation σ k u z*(ζ z)^2*(∑ i, c z i*dgTruncationGradient σ k u z i) +
    σ*f z*dgTruncation σ k u z*(ζ z)^2

def dgTruncationBalanceUnmasked {n : ℕ} (A : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ) (σ k : ℝ)
    (u ζ : Point n → ℝ) (z : Point n) : ℝ :=
  (dgTruncation σ k u z)^2*ζ z*deriv (fun q => ζ (z.1,q)) z.2 -
    2*dgTruncation σ k u z*ζ z*dgBilinear (A z)
      (fun j => σ*dgGradient u z j) (dgGradient ζ z) +
    dgTruncation σ k u z*(ζ z)^2*(∑ i, c z i*(σ*dgGradient u z i)) +
    σ*f z*dgTruncation σ k u z*(ζ z)^2

theorem dgTruncationBalance_eq_unmasked {n : ℕ} (A : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ) (σ k : ℝ)
    (u ζ : Point n → ℝ) (z : Point n) :
    dgTruncationBalance A c f σ k u ζ z = dgTruncationBalanceUnmasked A c f σ k u ζ z := by
  by_cases h : k < σ*u z
  · have hg : dgTruncationGradient σ k u z = fun j => σ*dgGradient u z j := by
      funext j
      exact ite_eq_left h
    simp only [dgTruncationBalance,dgTruncationBalanceUnmasked,hg]
  · have hv : dgTruncation σ k u z = 0 := dgPositivePart_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))
    simp only [dgTruncationBalance,dgTruncationBalanceUnmasked,hv,zero_pow (by decide : 2 ≠ 0),
      zero_mul,mul_zero,sub_zero,add_zero]

theorem dgGradient_square {n : ℕ} {ζ : Point n → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (z : Point n) (i : Yau.RIdx n) :
    dgGradient (fun q => (ζ q)^2) z i = 2*ζ z*dgGradient ζ z i := by
  rw [dgGradient_eq_joint_fderiv (u := fun q => (ζ q)^2) ((hζ.differentiable (by simp) z).pow 2) i]
  rw [fderiv_fun_pow 2 (hζ.differentiable (by simp) z),
    dgGradient_eq_joint_fderiv (hζ.differentiable (by simp) z) i]
  simp only [smul_apply,smul_eq_mul,Nat.cast_ofNat,show 2-1=1 from rfl,pow_one]
  ring

theorem dgTruncationBalance_continuousOn {n : ℕ} {U : Set (Point n)} (hU : IsOpen U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u ζ : Point n → ℝ}
    (hf : DGClassicalFields U A c f u) (hζ : ContDiff ℝ ∞ ζ) (σ k : ℝ) :
    ContinuousOn (dgTruncationBalance A c f σ k u ζ) U := by
  have hv : ContinuousOn (dgTruncation σ k u) U :=
    dgPositivePart_lipschitz.continuous.comp_continuousOn
      ((continuousOn_const.mul hf.2.2.2.continuousOn).sub continuousOn_const)
  have hG (i : Yau.RIdx n) := (dgGradient_contDiffOn hU hf.2.2.2 i).continuousOn
  have hZ (i : Yau.RIdx n) := (dgGradient_contDiffOn hU hζ.contDiffOn i).continuousOn
  have hB : ContinuousOn (fun z => dgBilinear (A z) (fun j => σ*dgGradient u z j) (dgGradient ζ z)) U :=
    continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      (((hf.1 i j).continuousOn.mul (continuousOn_const.mul (hG j))).mul (hZ i))))
  have hc : ContinuousOn (fun z => ∑ i, c z i*(σ*dgGradient u z i)) U :=
    continuousOn_finsetSum _ (fun i _ => (hf.2.1 i).continuousOn.mul (continuousOn_const.mul (hG i)))
  have htime := (dgTimeDeriv_contDiffOn hU hζ.contDiffOn).continuousOn
  have hb : ContinuousOn (dgTruncationBalanceUnmasked A c f σ k u ζ) U :=
    (((((hv.pow 2).mul hζ.continuous.continuousOn).mul htime).sub
      (((continuousOn_const.mul hv).mul hζ.continuous.continuousOn).mul hB)).add
      ((hv.mul (hζ.continuous.pow 2).continuousOn).mul hc)).add
      ((((continuousOn_const.mul hf.2.2.1.continuousOn).mul hv).mul (hζ.continuous.pow 2).continuousOn))
  exact hb.congr (fun z _ => dgTruncationBalance_eq_unmasked A c f σ k u ζ z)

def dgTruncationTimeDensity {n : ℕ} (σ k : ℝ) (u ζ : Point n → ℝ) (z : Point n) : ℝ :=
  dgTruncation σ k u z*(σ*deriv (fun q => u (z.1,q)) z.2)*(ζ z)^2 +
    (dgTruncation σ k u z)^2*ζ z*deriv (fun q => ζ (z.1,q)) z.2

theorem dgTruncation_flux_balance_pointwise {n : ℕ} {U : Set (Point n)} (hU : IsOpen U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u ζ : Point n → ℝ}
    (hf : DGClassicalFields U A c f u) (hpde : ClassicalDivEq U A c f u)
    (hζ : ContDiff ℝ ∞ ζ) (σ k : ℝ) {z : Point n} (hz : z ∈ U) :
    dgJointFluxBalance (fun q => σ*u q-k) ζ (dgFlux A (fun q => σ*u q-k)) z =
      dgTruncationTimeDensity σ k u ζ z + dgTruncationPrincipal A σ k u ζ z -
        dgTruncationBalance A c f σ k u ζ z := by
  let w : Point n → ℝ := fun q => σ*u q-k
  let v := dgTruncation σ k u z
  let g := dgTruncationGradient σ k u z
  have huz := (hf.2.2.2.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  by_cases ha : k < σ*u z
  · have hwpos : 0 < w z := sub_pos.mpr ha
    have hgw (i : Yau.RIdx n) : dgGradient w z i = g i := by
      rw [dgGradient_affine huz σ k i]
      exact (ite_eq_left ha).symm
    have hflux (i : Yau.RIdx n) : dgFlux A w z i = ∑ j, A z i j*g j := by
      unfold dgFlux
      simp only [hgw]
    have h1 : (∑ i, dgPositivePart (w z)*(ζ z)^2*dgGradient (fun q => dgFlux A w q i) z i) =
        v*(ζ z)^2*(∑ i, dgGradient (fun q => dgFlux A w q i) z i) := by
      rw [Finset.mul_sum]
      rfl
    have h2 : (∑ i, (if 0 < w z then dgGradient w z i else 0)*(ζ z)^2*dgFlux A w z i) =
        (ζ z)^2*dgBilinear (A z) g g := by
      simp only [ite_eq_left hwpos,hgw,hflux,dgBilinear,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h3 : (∑ i, dgPositivePart (w z)*dgFlux A w z i*dgGradient (fun q => (ζ q)^2) z i) =
        2*v*ζ z*dgBilinear (A z) g (dgGradient ζ z) := by
      simp only [hflux,dgGradient_square hζ,dgBilinear,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change v*(A z i j*g j)*(2*ζ z*dgGradient ζ z i) = _
      ring
    have hD : dgJointFluxBalance w ζ (dgFlux A w) z =
        v*(ζ z)^2*(∑ i, dgGradient (fun q => dgFlux A w q i) z i) +
        (ζ z)^2*dgBilinear (A z) g g + 2*v*ζ z*dgBilinear (A z) g (dgGradient ζ z) := by
      simp only [dgJointFluxBalance,Finset.sum_add_distrib]
      rw [h1,h2,h3]
    have heq := dgClassicalDivEq_affine hU hf hpde σ k z hz
    change deriv (fun q => σ*u (z.1,q)-k) z.2 -
      (∑ i, dgGradient (fun q => dgFlux A w q i) z i) =
        (∑ i, c z i*dgGradient w z i)+σ*f z at heq
    rw [dgTimeDeriv_affine huz] at heq
    simp only [hgw] at heq
    have hmul := congrArg (fun x : ℝ => v*(ζ z)^2*x) heq
    change dgJointFluxBalance w ζ (dgFlux A w) z = _
    rw [hD]
    change v*(ζ z)^2*(∑ i, dgGradient (fun q => dgFlux A w q i) z i) +
      (ζ z)^2*dgBilinear (A z) g g + 2*v*ζ z*dgBilinear (A z) g (dgGradient ζ z) =
      v*(σ*deriv (fun q => u (z.1,q)) z.2)*(ζ z)^2 +
      v^2*ζ z*deriv (fun q => ζ (z.1,q)) z.2 + (ζ z)^2*dgBilinear (A z) g g -
      (v^2*ζ z*deriv (fun q => ζ (z.1,q)) z.2 - 2*v*ζ z*dgBilinear (A z) g (dgGradient ζ z) +
        v*(ζ z)^2*(∑ i, c z i*g i)+σ*f z*v*(ζ z)^2)
    nlinarith only [hmul]
  · have hwpos : ¬0 < w z := by simpa only [w,sub_pos] using ha
    have hv : dgTruncation σ k u z = 0 := dgPositivePart_of_nonpos (sub_nonpos.mpr (le_of_not_gt ha))
    have hv' : dgPositivePart (σ*u z-k) = 0 := hv
    have hn' : ¬0 < σ*u z-k := by simpa only [sub_pos] using ha
    simp only [dgJointFluxBalance,dgTruncationTimeDensity,dgTruncationPrincipal,dgTruncationBalance,
      dgTruncationGradient,ite_eq_right ha,ite_eq_right hwpos,ite_eq_right hn',hv',
      show dgPositivePart (w z) = 0 from hv,hv,dgBilinear,
      zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero,add_zero,zero_add,sub_zero,Finset.sum_const_zero]

/-- Exact time FTC for the truncation energy before the terminal face. -/
theorem dgTruncation_time_before_top {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r a b τ σ k : ℝ} (hla : l < a) (haτ : a < τ) (hτb : τ < b) (hbr : b ≤ r)
    {u ζ : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo l r))
    (hζ : DGSpatialCutoff O a b ζ) :
    Integrable (dgTruncationTimeDensity σ k u ζ) (productVolume O (Ioo a τ)) ∧
    dgCylinderIntegral O a τ (dgTruncationTimeDensity σ k u ζ) =
      (1/2 : ℝ)*dgSliceEnergy O (dgTruncation σ k u) ζ τ -
        (1/2 : ℝ)*dgSliceEnergy O (dgTruncation σ k u) ζ a := by
  obtain ⟨hζs,_hζr,K,hK,hKO,hzero⟩ := hζ
  let U := O ×ˢ Ioo l r
  let w : Point n → ℝ := fun z => σ*u z-k
  let g : Point n → ℝ := fun z => dgPosPrimitive (w z)*(ζ z)^2
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hclosed : O ×ˢ Icc a τ ⊆ U := by
    intro z hz
    exact ⟨hz.1,hla.trans_le hz.2.1,hz.2.2.trans_lt (hτb.trans_le hbr)⟩
  have hw : ContinuousOn w U := (continuousOn_const.mul hu.continuousOn).sub continuousOn_const
  have hprimitive : Continuous dgPosPrimitive := continuous_iff_continuousAt.mpr
    (fun x => (dgPosPrimitive_hasDerivAt x).continuousAt)
  have hgc : ContinuousOn g (O ×ˢ Icc a τ) :=
    ((hprimitive.comp_continuousOn hw).mul (hζs.continuous.pow 2).continuousOn).mono hclosed
  have hv : ContinuousOn (dgTruncation σ k u) U := dgPositivePart_lipschitz.continuous.comp_continuousOn hw
  have hutc := (dgTimeDeriv_contDiffOn hU hu).continuousOn
  have hζtc := (dgTimeDeriv_contDiffOn hU hζs.contDiffOn).continuousOn
  have hTc : ContinuousOn (dgTruncationTimeDensity σ k u ζ) (O ×ˢ Icc a τ) :=
    ((((hv.mul (continuousOn_const.mul hutc)).mul (hζs.continuous.pow 2).continuousOn).add
      (((hv.pow 2).mul hζs.continuous.continuousOn).mul hζtc))).mono hclosed
  have hres := dg_finiteTime_integral_identity hO hK hKO haτ.le hgc hTc
    (fun z hz hx => by
      change dgPosPrimitive (w z)*(ζ z)^2 = 0
      simp only [hzero z ⟨hz.2.1,hz.2.2.trans hτb.le⟩ hx,zero_pow (by decide : 2 ≠ 0),mul_zero])
    (fun z hz hx => by
      change dgTruncation σ k u z*(σ*deriv (fun q => u (z.1,q)) z.2)*(ζ z)^2 +
        (dgTruncation σ k u z)^2*ζ z*deriv (fun q => ζ (z.1,q)) z.2 = 0
      simp only [hzero z ⟨hz.2.1,hz.2.2.trans hτb.le⟩ hx,zero_pow (by decide : 2 ≠ 0),mul_zero,
        zero_mul,add_zero]) (fun x hx t ht => by
      have hz : (x,t) ∈ U := hclosed ⟨hx,Ioo_subset_Icc_self ht⟩
      have hud := (hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
      have hζd := hζs.differentiable (by simp) (x,t)
      have hMap : DifferentiableAt ℝ (fun q : ℝ => (x,q)) t :=
        ((hasFDerivAt_const x t).prodMk (hasFDerivAt_id t)).differentiableAt
      have hus := hud.comp t hMap
      have hζsl := hζd.comp t hMap
      have hws := (hus.const_mul σ).sub_const k
      have hd := dgPosPrimitive_mul_square_hasDerivAt hws.hasDerivAt hζsl.hasDerivAt
      have htime := dgTimeDeriv_affine hud σ k
      change deriv (fun q => σ*u (x,q)-k) t = σ*deriv (fun q => u (x,q)) t at htime
      change HasDerivAt (fun q => dgPosPrimitive (σ*u (x,q)-k)*(ζ (x,q))^2)
        (dgPositivePart (σ*u (x,t)-k)*deriv (fun q => σ*u (x,q)-k) t*(ζ (x,t))^2 +
          (dgPositivePart (σ*u (x,t)-k))^2*ζ (x,t)*deriv (fun q => ζ (x,q)) t) t at hd
      rw [htime] at hd
      exact hd)
  have hslice (q : ℝ) : (∫ x in O, g (x,q)) =
      (1/2 : ℝ)*dgSliceEnergy O (dgTruncation σ k u) ζ q := by
    unfold dgSliceEnergy
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only [g,w,dgTruncation]
    rw [dgPosPrimitive_eq]
    ring
  exact ⟨hres.1,hres.2.trans (by rw [hslice τ,hslice a])⟩

/-- Exact nonlinear endpoint balance on every strictly interior terminal time.
The principal and balance terms are proved integrable as part of the theorem. -/
theorem dgTruncation_balance_before_top {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r a b τ σ k : ℝ} (hla : l < a) (haτ : a < τ) (hτb : τ < b) (hbr : b ≤ r)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u ζ : Point n → ℝ}
    (hf : DGClassicalFields (O ×ˢ Ioo l r) A c f u)
    (hpde : ClassicalDivEq (O ×ˢ Ioo l r) A c f u) (hζ : DGSpatialCutoff O a b ζ) :
    Integrable (dgTruncationPrincipal A σ k u ζ) (productVolume O (Ioo a τ)) ∧
    Integrable (dgTruncationBalance A c f σ k u ζ) (productVolume O (Ioo a τ)) ∧
    (1/2 : ℝ)*dgSliceEnergy O (dgTruncation σ k u) ζ τ +
      dgCylinderIntegral O a τ (dgTruncationPrincipal A σ k u ζ) =
    (1/2 : ℝ)*dgSliceEnergy O (dgTruncation σ k u) ζ a +
      dgCylinderIntegral O a τ (dgTruncationBalance A c f σ k u ζ) := by
  let U := O ×ˢ Ioo l r
  let w : Point n → ℝ := fun z => σ*u z-k
  let D := dgJointFluxBalance w ζ (dgFlux A w)
  let T := dgTruncationTimeDensity σ k u ζ
  let B := dgTruncationBalance A c f σ k u ζ
  let P := dgTruncationPrincipal A σ k u ζ
  let μ := productVolume O (Ioo a τ)
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hw : ContDiffOn ℝ ∞ w U := (contDiffOn_const.mul hf.2.2.2).sub contDiffOn_const
  have hD := dgJointFluxBalance_integral_zero hO hla haτ hτb hbr hw
    (fun i => dgFlux_contDiffOn hU hf.1 hw i) hζ
  have hT := dgTruncation_time_before_top hO hla haτ hτb hbr hf.2.2.2 (σ := σ) (k := k) hζ
  have hclosed : O ×ˢ Icc a τ ⊆ U := by
    intro z hz
    exact ⟨hz.1,hla.trans_le hz.2.1,hz.2.2.trans_lt (hτb.trans_le hbr)⟩
  obtain ⟨hζs,_hζr,K,hK,hKO,hzero⟩ := hζ
  have hB : Integrable B μ := by
    apply dg_integrable_of_compact_spatial_support hO hK
      ((dgTruncationBalance_continuousOn hU hf hζs σ k).mono
        ((Set.prod_mono hKO Subset.rfl).trans hclosed))
    intro z hz hx
    change dgTruncationBalance A c f σ k u ζ z = 0
    dsimp only [dgTruncationBalance]
    rw [hzero z ⟨hz.2.1.le,hz.2.2.le.trans hτb.le⟩ hx]
    simp
  have hpoint : ∀ᵐ z ∂μ, D z - T z + B z = P z := by
    rw [show μ = volume.restrict (O ×ˢ Ioo a τ) from dg_productVolume_eq_restrict O _]
    filter_upwards [ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet] with z hz
    have hzU := hclosed ⟨hz.1,Ioo_subset_Icc_self hz.2⟩
    have hh := dgTruncation_flux_balance_pointwise hU hf hpde hζs σ k hzU
    change D z = T z + P z - B z at hh
    linarith
  have hP : Integrable P μ := ((hD.1.sub hT.1).add hB).congr hpoint
  have hPval : dgCylinderIntegral O a τ P = dgCylinderIntegral O a τ D -
      dgCylinderIntegral O a τ T + dgCylinderIntegral O a τ B := by
    unfold dgCylinderIntegral
    calc
      _ = ∫ z, D z-T z+B z ∂μ := integral_congr_ae (Filter.EventuallyEq.symm hpoint)
      _ = _ := by
        have hs := integral_sub hD.1 hT.1
        have ha := integral_add (hD.1.sub hT.1) hB
        simp only [Pi.sub_apply,Pi.add_apply] at hs ha
        rw [ha,hs]
  have hDzero : dgCylinderIntegral O a τ D = 0 := hD.2
  have hTval : dgCylinderIntegral O a τ T =
      (1/2 : ℝ)*dgSliceEnergy O (dgTruncation σ k u) ζ τ -
        (1/2 : ℝ)*dgSliceEnergy O (dgTruncation σ k u) ζ a := hT.2
  rw [hDzero,hTval] at hPval
  exact ⟨hP,hB,by dsimp only [P,B] at hPval; linarith⟩

theorem dg_dot_bound {n : ℕ} (p q : Yau.RIdx n → ℝ) :
    |∑ i, p i*q i| ≤ Real.sqrt (dgGradientSq p)*Real.sqrt (dgGradientSq q) := by
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Real.sqrt (dgGradientSq p)*Real.sqrt (dgGradientSq q))).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt (dgGradientSq_nonneg p),Real.sq_sqrt (dgGradientSq_nonneg q)]
  simpa only [dgGradientSq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p q

theorem dg_drift_bound {n : ℕ} {c : Yau.RIdx n → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hc : dgGradientSq c ≤ D^2) (g : Yau.RIdx n → ℝ) :
    |∑ i, c i*g i| ≤ D*Real.sqrt (dgGradientSq g) := by
  have hs : Real.sqrt (dgGradientSq c) ≤ D := by
    nlinarith [Real.sq_sqrt (dgGradientSq_nonneg c),Real.sqrt_nonneg (dgGradientSq c)]
  exact (dg_dot_bound c g).trans (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))

theorem dg_elliptic_lower {n : ℕ} {U : Set (Point n)} {A : Point n → Mat n}
    {ν L : ℝ} (hA : Elliptic U A ν L) {z : Point n} (hz : z ∈ U)
    (g : Yau.RIdx n → ℝ) : ν*dgGradientSq g ≤ dgBilinear (A z) g g := by
  simpa only [dgGradientSq,dgBilinear,mul_comm,mul_left_comm,mul_assoc] using
    ((hA.2.2 z hz).2 g).1

theorem dg_sign_forcing_bound {σ f F : ℝ} (hσ : DGSign σ) (hf : |f| ≤ F) :
    |σ*f| ≤ F := by
  rcases hσ with rfl | rfl
  · simpa only [one_mul] using hf
  · simpa only [neg_one_mul,abs_neg] using hf

theorem dg_active_aestronglyMeasurable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] {μ : Measure E} {O : Set E} (hO : IsOpen O)
    {w H : E → ℝ} (hw : ContinuousOn w O) (hH : AEStronglyMeasurable H (μ.restrict O)) :
    AEStronglyMeasurable (fun x => if 0 < w x then H x else 0) (μ.restrict O) := by
  let S := O ∩ w ⁻¹' Ioi 0
  have hS : MeasurableSet S := (hw.isOpen_inter_preimage hO isOpen_Ioi).measurableSet
  apply (hH.indicator hS).congr
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  change S.indicator H x = if 0 < w x then H x else 0
  by_cases hp : 0 < w x
  · rw [indicator_of_mem (show x ∈ S from ⟨hx,hp⟩),ite_eq_left hp]
  · rw [indicator_of_notMem (show x ∉ S from fun h => hp h.2),ite_eq_right hp]

theorem dgTruncationEnergyDensity_eq_mask {n : ℕ} (σ k : ℝ) (u ζ : Point n → ℝ) (z : Point n) :
    dgTruncationEnergyDensity σ k u ζ z =
      if k < σ*u z then σ^2*dgGradientSq (dgGradient u z)*(ζ z)^2 else 0 := by
  by_cases h : k < σ*u z
  · simp only [dgTruncationEnergyDensity,dgGradientSq,dgTruncationGradient,ite_eq_left h,mul_pow]
    rw [← Finset.mul_sum]
  · simp only [dgTruncationEnergyDensity,dgGradientSq,dgTruncationGradient,ite_eq_right h,
      zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_mul]

theorem dgTruncation_energy_integrable_before_top {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r a b τ σ k : ℝ} (hla : l < a) (_haτ : a < τ) (hτb : τ < b) (hbr : b ≤ r)
    {u ζ : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo l r))
    (hζ : DGSpatialCutoff O a b ζ) :
    Integrable (dgTruncationEnergyDensity σ k u ζ) (productVolume O (Ioo a τ)) := by
  obtain ⟨hζs,_hζr,K,hK,hKO,hzero⟩ := hζ
  let U := O ×ˢ Ioo l r
  let V := O ×ˢ Ioo a τ
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hV : IsOpen V := hO.prod isOpen_Ioo
  have hclosed : O ×ˢ Icc a τ ⊆ U := by
    intro z hz
    exact ⟨hz.1,hla.trans_le hz.2.1,hz.2.2.trans_lt (hτb.trans_le hbr)⟩
  have hg : ContinuousOn (fun z => dgGradientSq (dgGradient u z)) U :=
    continuousOn_finsetSum _ (fun i _ => (dgGradient_contDiffOn hU hu i).continuousOn.pow 2)
  let H : Point n → ℝ := fun z => σ^2*dgGradientSq (dgGradient u z)*(ζ z)^2
  have hHi : Integrable H (productVolume O (Ioo a τ)) := by
    apply dg_integrable_of_compact_spatial_support hO hK
      (((continuousOn_const.mul hg).mul (hζs.continuous.pow 2).continuousOn).mono
        ((Set.prod_mono hKO Subset.rfl).trans hclosed))
    intro z hz hx
    change σ^2*dgGradientSq (dgGradient u z)*(ζ z)^2 = 0
    rw [hzero z ⟨hz.2.1.le,hz.2.2.le.trans hτb.le⟩ hx]; simp
  have hwm : ContinuousOn (fun z => σ*u z-k) V :=
    ((continuousOn_const.mul hu.continuousOn).sub continuousOn_const).mono
      ((Set.prod_mono Subset.rfl Ioo_subset_Icc_self).trans hclosed)
  have hMask : Integrable (fun z => if 0 < σ*u z-k then H z else 0) (productVolume O (Ioo a τ)) := by
    rw [dg_productVolume_eq_restrict]
    apply dg_active_integrable hV hwm
    rw [← dg_productVolume_eq_restrict]
    exact hHi
  apply hMask.congr
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [dgTruncationEnergyDensity_eq_mask]
  simp only [sub_pos,H]

theorem dgTruncationGradient_aestronglyMeasurable {n : ℕ} {U : Set (Point n)}
    (hU : IsOpen U) {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (σ k : ℝ) (i : Yau.RIdx n) :
    AEStronglyMeasurable (fun z => dgTruncationGradient σ k u z i) (volume.restrict U) := by
  have hw : ContinuousOn (fun z => σ*u z-k) U :=
    (continuousOn_const.mul hu.continuousOn).sub continuousOn_const
  have hc : ContinuousOn (fun z => σ*dgGradient u z i) U :=
    continuousOn_const.mul (dgGradient_contDiffOn hU hu i).continuousOn
  have hh := dg_active_aestronglyMeasurable (μ := volume) hU hw
    (hc.aestronglyMeasurable hU.measurableSet)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  simp only [dgTruncationGradient,sub_pos]

theorem dgTruncation_balance_le {n : ℕ} {U : Set (Point n)}
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u ζ : Point n → ℝ}
    {ν L D F σ k : ℝ} (hν : 0 < ν) (hD : 0 ≤ D)
    (hb : DGUniformBounds U A c f ν L D F) (hσ : DGSign σ)
    {z : Point n} (hz : z ∈ U) (hζ0 : 0 ≤ ζ z) (hζ1 : ζ z ≤ 1) :
    dgTruncationBalance A c f σ k u ζ z ≤
      ν/2*dgTruncationEnergyDensity σ k u ζ z +
      (1+4*L^2/ν+D^2/ν)*dgTruncationCutoffError σ k u ζ z +
      F*dgTruncationForcingDensity σ k u ζ z := by
  let v := dgTruncation σ k u z
  let g := dgTruncationGradient σ k u z
  let q := dgGradient ζ z
  let Z := ζ z
  let t := deriv (fun r => ζ (z.1,r)) z.2
  let G := Real.sqrt (dgGradientSq g)
  let H := Real.sqrt (dgGradientSq q)
  let α := 4*L^2/ν
  let β := D^2/ν
  let K := 1+α+β
  have hv : 0 ≤ v := dgPositivePart_nonneg _
  have hL : 0 ≤ L := hb.1.1.le.trans hb.1.2.1
  have hZZ : |Z| ≤ 1 := by rw [abs_of_nonneg hζ0]; exact hζ1
  have hzt : Z*t ≤ |t| := by
    calc
      _ ≤ |Z*t| := le_abs_self _
      _ = |Z| * |t| := abs_mul _ _
      _ ≤ 1*|t| := mul_le_mul_of_nonneg_right hZZ (abs_nonneg _)
      _ = _ := one_mul _
  have ht : v^2*Z*t ≤ v^2*|t| := by nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hzt)]
  have hcross : -(2*v*Z*dgBilinear (A z) g q) ≤ 2*L*v*Z*G*H := by
    have he := (neg_le_abs (dgBilinear (A z) g q)).trans (dg_elliptic_bilinear_bound hb.1 hz g q)
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2*v*Z by dsimp only [Z]; positivity)
    nlinarith only [hm]
  have hdrift : v*Z^2*(∑ i, c z i*g i) ≤ D*v*Z^2*G := by
    have he := (le_abs_self (∑ i, c z i*g i)).trans (dg_drift_bound hD (hb.2.1 z hz) g)
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ v*Z^2 by positivity)
    nlinarith only [hm]
  have hsource : σ*f z*v*Z^2 ≤ F*v*Z^2 := by
    have he := (le_abs_self (σ*f z)).trans (dg_sign_forcing_bound hσ (hb.2.2 z hz))
    have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ v*Z^2 by positivity)
    nlinarith only [hm]
  have habs := dg_cutoff_drift_absorption (L := L) (D := D) (v := v) (ζ := Z) (g := G) (h := H) hν
  have hGs : G^2 = dgGradientSq g := Real.sq_sqrt (dgGradientSq_nonneg g)
  have hHs : H^2 = dgGradientSq q := Real.sq_sqrt (dgGradientSq_nonneg q)
  rw [hGs,hHs] at habs
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hK1 : 1 ≤ K := by dsimp only [K]; linarith
  have hKα : α ≤ K := by dsimp only [K]; linarith
  have hKβ : β ≤ K := by dsimp only [K]; linarith
  have hd0 := mul_le_mul_of_nonneg_right hK1 (mul_nonneg (sq_nonneg v) (abs_nonneg t))
  have hg0 := mul_le_mul_of_nonneg_right hKα (mul_nonneg (sq_nonneg v) (dgGradientSq_nonneg q))
  have hz0 := mul_le_mul_of_nonneg_right hKβ (mul_nonneg (sq_nonneg v) (sq_nonneg Z))
  have herr : v^2*|t| + (α*dgGradientSq q+β*Z^2)*v^2 ≤
      K*(v^2*(|t|+dgGradientSq q+Z^2)) := by nlinarith only [hd0,hg0,hz0]
  change v^2*Z*t - 2*v*Z*dgBilinear (A z) g q + v*Z^2*(∑ i, c z i*g i) + σ*f z*v*Z^2 ≤
    ν/2*(dgGradientSq g*Z^2) + K*(v^2*(|t|+dgGradientSq q+Z^2)) + F*(v*Z^2)
  dsimp only [α,β] at herr
  nlinarith only [ht,hcross,hdrift,hsource,habs,herr]

/-- Closed top values inherit a uniform bound from strictly interior times. -/
theorem dg_closed_top_bound {S : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hc : ContinuousOn S (Icc a b)) (hbound : ∀ t ∈ Ioo a b, S t ≤ M) : S b ≤ M := by
  let ε : ℕ → ℝ := fun j => (1/2 : ℝ)^(j+1)
  let τ : ℕ → ℝ := fun j => b-(b-a)*ε j
  have hεpos (j : ℕ) : 0 < ε j := pow_pos (by norm_num) _
  have hεlt (j : ℕ) : ε j < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero j)
  have hτ (j : ℕ) : τ j ∈ Ioo a b := by
    have hba : 0 < b-a := sub_pos.mpr hab
    have hp := mul_pos hba (hεpos j)
    have hl := mul_lt_mul_of_pos_left (hεlt j) hba
    dsimp only [τ]
    constructor <;> nlinarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  have heps : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,pow_succ,zero_mul] using hpow.mul_const (1/2 : ℝ)
  have hlim : Tendsto τ atTop (𝓝 b) := by
    simpa only [τ,mul_zero,sub_zero] using tendsto_const_nhds.sub (heps.const_mul (b-a))
  have hlim' : Tendsto τ atTop (𝓝[Icc a b] b) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim,.of_forall (fun j => Ioo_subset_Icc_self (hτ j))⟩
  exact le_of_tendsto (((hc b ⟨hab.le,le_rfl⟩).tendsto).comp hlim')
    (.of_forall (fun j => hbound (τ j) (hτ j)))

theorem dgTruncationEnergyDensity_aestronglyMeasurable {n : ℕ} {U : Set (Point n)}
    (hU : IsOpen U) {u ζ : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hζ : ContDiff ℝ ∞ ζ) (σ k : ℝ) :
    AEStronglyMeasurable (dgTruncationEnergyDensity σ k u ζ) (volume.restrict U) := by
  have hs : AEStronglyMeasurable (fun z => dgGradientSq (dgTruncationGradient σ k u z)) (volume.restrict U) :=
    Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (dgTruncationGradient_aestronglyMeasurable hU hu σ k i).pow 2)
  exact hs.mul (hζ.continuous.aestronglyMeasurable.pow 2)

theorem dgTruncationCutoffGradient_aestronglyMeasurable {n : ℕ} {U : Set (Point n)}
    (hU : IsOpen U) {u ζ : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hζ : ContDiff ℝ ∞ ζ) (σ k : ℝ) :
    AEStronglyMeasurable (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z))
      (volume.restrict U) := by
  have hv : ContinuousOn (dgTruncation σ k u) U :=
    dgPositivePart_lipschitz.continuous.comp_continuousOn
      ((continuousOn_const.mul hu.continuousOn).sub continuousOn_const)
  have hvAE := hv.aestronglyMeasurable (μ := volume) hU.measurableSet
  exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
    (((hζ.continuous.aestronglyMeasurable.mul (dgTruncationGradient_aestronglyMeasurable hU hu σ k i)).add
      (hvAE.mul ((dgGradient_contDiffOn hU hζ.contDiffOn i).continuousOn.aestronglyMeasurable hU.measurableSet))).pow 2))

theorem dgTruncationCutoffGradient_pointwise_bound {n : ℕ} (σ k : ℝ) (u ζ : Point n → ℝ) (z : Point n) :
    dgGradientSq (dgTruncationCutoffGradient σ k u ζ z) ≤
      2*dgTruncationEnergyDensity σ k u ζ z+2*dgTruncationCutoffError σ k u ζ z := by
  have he (i : Yau.RIdx n) :
      (ζ z*dgTruncationGradient σ k u z i+dgTruncation σ k u z*dgGradient ζ z i)^2 ≤
        2*(ζ z*dgTruncationGradient σ k u z i)^2+2*(dgTruncation σ k u z*dgGradient ζ z i)^2 := by
    nlinarith [sq_nonneg (ζ z*dgTruncationGradient σ k u z i-dgTruncation σ k u z*dgGradient ζ z i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => he i)
  have hsum : (∑ i, (2*(ζ z*dgTruncationGradient σ k u z i)^2+
      2*(dgTruncation σ k u z*dgGradient ζ z i)^2)) =
      2*dgTruncationEnergyDensity σ k u ζ z + 2*(dgTruncation σ k u z)^2*dgGradientSq (dgGradient ζ z) := by
    simp only [Finset.sum_add_distrib,mul_pow,dgTruncationEnergyDensity,dgGradientSq,
      Finset.mul_sum,Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [hsum] at hs
  have herror : (dgTruncation σ k u z)^2*dgGradientSq (dgGradient ζ z) ≤ dgTruncationCutoffError σ k u ζ z := by
    unfold dgTruncationCutoffError
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith [abs_nonneg (deriv (fun t => ζ (z.1,t)) z.2),sq_nonneg (ζ z)]
  exact hs.trans (by linarith)

/-- The companion product energy follows from actual integrability already
established for H and the cutoff error. -/
theorem dgTruncationCutoffGradient_integral_bound {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {a b σ k : ℝ} {u ζ : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo a b))
    (hζ : ContDiff ℝ ∞ ζ)
    (hH : Integrable (dgTruncationEnergyDensity σ k u ζ) (productVolume O (Ioo a b)))
    (hX : Integrable (dgTruncationCutoffError σ k u ζ) (productVolume O (Ioo a b))) :
    Integrable (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)) (productVolume O (Ioo a b)) ∧
    dgCylinderIntegral O a b (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)) ≤
      2*dgCylinderIntegral O a b (dgTruncationEnergyDensity σ k u ζ) +
        2*dgCylinderIntegral O a b (dgTruncationCutoffError σ k u ζ) := by
  have hmeas : AEStronglyMeasurable (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z))
      (productVolume O (Ioo a b)) := by
    rw [dg_productVolume_eq_restrict]
    exact dgTruncationCutoffGradient_aestronglyMeasurable (hO.prod isOpen_Ioo) hu hζ σ k
  have hdom := (hH.const_mul 2).add (hX.const_mul 2)
  have hi : Integrable (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z))
      (productVolume O (Ioo a b)) := hdom.mono' hmeas (.of_forall fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (dgGradientSq_nonneg _)]
    exact dgTruncationCutoffGradient_pointwise_bound σ k u ζ z)
  refine ⟨hi,?_⟩
  have hb := integral_mono hi hdom (fun z => dgTruncationCutoffGradient_pointwise_bound σ k u ζ z)
  have ha := integral_add (hH.const_mul 2) (hX.const_mul 2)
  simp only [Pi.add_apply] at hb
  rw [ha,integral_const_mul,integral_const_mul] at hb
  exact hb

theorem dgCylinderIntegral_prefix_le {n : ℕ} {O : Set (Space n)} {a b τ : ℝ}
    {f : Point n → ℝ} (hτb : τ ≤ b) (hf : Integrable f (productVolume O (Ioo a b)))
    (hf0 : ∀ z, 0 ≤ f z) : dgCylinderIntegral O a τ f ≤ dgCylinderIntegral O a b f := by
  unfold dgCylinderIntegral
  rw [← dg_prefix_measure hτb]
  exact integral_mono_measure Measure.restrict_le_self (.of_forall hf0) hf

theorem dgTruncation_prefix_estimate {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r a b τ ν L D F σ k : ℝ} (hla : l < a) (haτ : a < τ) (hτb : τ < b) (hbr : b ≤ r)
    (hν : 0 < ν) (hD : 0 ≤ D) (hF : 0 ≤ F)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u ζ : Point n → ℝ}
    (hf : DGClassicalFields (O ×ˢ Ioo l r) A c f u)
    (hpde : ClassicalDivEq (O ×ˢ Ioo l r) A c f u)
    (hb : DGUniformBounds (O ×ˢ Ioo l r) A c f ν L D F)
    (hu : ContinuousOn u (O ×ˢ Icc a b)) (hζ : DGSpatialCutoff O a b ζ) (hσ : DGSign σ) :
    dgSliceEnergy O (dgTruncation σ k u) ζ τ +
      ν*dgCylinderIntegral O a τ (dgTruncationEnergyDensity σ k u ζ) ≤
    (2+8*L^2/ν+2*D^2/ν)*dgCylinderIntegral O a b (dgTruncationCutoffError σ k u ζ) +
      2*F*dgCylinderIntegral O a b (dgTruncationForcingDensity σ k u ζ) +
      dgSliceEnergy O (dgTruncation σ k u) ζ a := by
  let H := dgTruncationEnergyDensity σ k u ζ
  let X := dgTruncationCutoffError σ k u ζ
  let Q := dgTruncationForcingDensity σ k u ζ
  let P := dgTruncationPrincipal A σ k u ζ
  let B := dgTruncationBalance A c f σ k u ζ
  let K := 1+4*L^2/ν+D^2/ν
  let μ := productVolume O (Ioo a τ)
  have hq := dg_cutoff_quantities_integrable (σ := σ) (k := k) hO hu hζ
  have hX : Integrable X μ := by
    change Integrable X (productVolume O (Ioo a τ))
    rw [← dg_prefix_measure hτb.le]
    exact hq.1.restrict
  have hQ : Integrable Q μ := by
    change Integrable Q (productVolume O (Ioo a τ))
    rw [← dg_prefix_measure hτb.le]
    exact hq.2.1.restrict
  have hH : Integrable H μ := dgTruncation_energy_integrable_before_top hO hla haτ hτb hbr hf.2.2.2 hζ
  obtain ⟨hP,hB,hbalance⟩ := dgTruncation_balance_before_top (σ := σ) (k := k) hO hla haτ hτb hbr hf hpde hζ
  have hU : IsOpen (O ×ˢ Ioo l r) := hO.prod isOpen_Ioo
  have hmem : ∀ᵐ z ∂μ, z ∈ O ×ˢ Ioo a τ := by
    change ∀ᵐ z ∂productVolume O (Ioo a τ), z ∈ O ×ˢ Ioo a τ
    rw [dg_productVolume_eq_restrict]
    exact ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet
  have hlow := integral_mono_ae (hH.const_mul ν) hP (by
    filter_upwards [hmem] with z hz
    have hzU : z ∈ O ×ˢ Ioo l r := ⟨hz.1,hla.trans hz.2.1,hz.2.2.trans (hτb.trans_le hbr)⟩
    have hl := mul_le_mul_of_nonneg_left (dg_elliptic_lower hb.1 hzU (dgTruncationGradient σ k u z)) (sq_nonneg (ζ z))
    change ν*H z ≤ P z
    dsimp only [H,P,dgTruncationEnergyDensity,dgTruncationPrincipal]
    nlinarith only [hl])
  rw [integral_const_mul] at hlow
  have hR := ((hH.const_mul (ν/2)).add (hX.const_mul K)).add (hQ.const_mul F)
  have hupp := integral_mono_ae hB hR (by
    filter_upwards [hmem] with z hz
    have hzU : z ∈ O ×ˢ Ioo l r := ⟨hz.1,hla.trans hz.2.1,hz.2.2.trans (hτb.trans_le hbr)⟩
    have hzClosed : z ∈ O ×ˢ Icc a b := ⟨hz.1,hz.2.1.le,hz.2.2.le.trans hτb.le⟩
    exact dgTruncation_balance_le hν hD hb hσ hzU (hζ.2.1 z hzClosed).1 (hζ.2.1 z hzClosed).2)
  have hs1 := integral_add ((hH.const_mul (ν/2)).add (hX.const_mul K)) (hQ.const_mul F)
  have hs2 := integral_add (hH.const_mul (ν/2)) (hX.const_mul K)
  try simp only [Pi.add_apply] at hs1 hs2
  change (∫ z, B z ∂μ) ≤ ∫ z, ν/2*H z+K*X z+F*Q z ∂μ at hupp
  rw [hs1,hs2,integral_const_mul,integral_const_mul,integral_const_mul] at hupp
  have hX0 (z : Point n) : 0 ≤ X z := by
    have hg0 := dgGradientSq_nonneg (dgGradient ζ z)
    dsimp only [X,dgTruncationCutoffError]
    positivity
  have hQ0 (z : Point n) : 0 ≤ Q z := by
    exact mul_nonneg (dgPositivePart_nonneg _) (sq_nonneg _)
  have hXmono := dgCylinderIntegral_prefix_le hτb.le hq.1 hX0
  have hQmono := dgCylinderIntegral_prefix_le hτb.le hq.2.1 hQ0
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hmX := mul_le_mul_of_nonneg_left hXmono hK
  have hmQ := mul_le_mul_of_nonneg_left hQmono hF
  change ν*dgCylinderIntegral O a τ H ≤ dgCylinderIntegral O a τ P at hlow
  change dgCylinderIntegral O a τ B ≤ ν/2*dgCylinderIntegral O a τ H+
    K*dgCylinderIntegral O a τ X+F*dgCylinderIntegral O a τ Q at hupp
  dsimp only [H,X,Q,P,B,K] at hlow hupp hmX hmQ
  simp only [div_eq_mul_inv] at hbalance hlow hupp hmX hmQ ⊢
  nlinarith only [hbalance,hlow,hupp,hmX,hmQ]

/-- The original universal truncation Caccioppoli interface is proved, with
one numerical constant fixed before the fields and before F. -/
theorem dgTruncation_caccioppoli : DGTruncationCaccioppoliGap := by
  unfold DGTruncationCaccioppoliGap
  intro n _hn ν L D hν _hνL hD
  let C := 8+16*L^2/ν+4*D^2/ν+2*ν
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro F hF x₀ R l r a b _hR hla hab hbr A c f u ζ
  dsimp only
  intro hf hpde hb hu hζ σ k hσ
  let O := Metric.ball x₀ R
  let U := O ×ˢ Ioo l r
  let V := O ×ˢ Ioo a b
  let H := dgTruncationEnergyDensity σ k u ζ
  let X := dgTruncationCutoffError σ k u ζ
  let Q := dgTruncationForcingDensity σ k u ζ
  let S := dgSliceEnergy O (dgTruncation σ k u) ζ
  let x := dgCylinderIntegral O a b X
  let q := dgCylinderIntegral O a b Q
  let K0 := 2+8*L^2/ν+2*D^2/ν
  let M := K0*x+2*F*q+S a
  let Btarget := C*x+C*F*q+C*S a
  have hO : IsOpen O := Metric.isOpen_ball
  have hV : IsOpen V := hO.prod isOpen_Ioo
  have hVU : V ⊆ U := by
    intro z hz
    exact ⟨hz.1,hla.trans hz.2.1,hz.2.2.trans_le hbr⟩
  have huv : ContDiffOn ℝ ∞ u V := hf.2.2.2.mono hVU
  have hζs := hζ.1
  have hq := dg_cutoff_quantities_integrable (σ := σ) (k := k) hO hu hζ
  have hH0 (z : Point n) : 0 ≤ H z := mul_nonneg (dgGradientSq_nonneg _) (sq_nonneg _)
  have hX0 (z : Point n) : 0 ≤ X z := by
    have hg0 := dgGradientSq_nonneg (dgGradient ζ z)
    dsimp only [X,dgTruncationCutoffError]
    positivity
  have hQ0 (z : Point n) : 0 ≤ Q z := mul_nonneg (dgPositivePart_nonneg _) (sq_nonneg _)
  have hx0 : 0 ≤ x := integral_nonneg hX0
  have hq0 : 0 ≤ q := integral_nonneg hQ0
  have hS0 (t : ℝ) : 0 ≤ S t := integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hK0 : 0 ≤ K0 := by dsimp only [K0]; positivity
  have hSa0 := hS0 a
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hpref (τ : ℝ) (hτ : τ ∈ Ioo a b) :
      S τ+ν*dgCylinderIntegral O a τ H ≤ M :=
    dgTruncation_prefix_estimate hO hla hτ.1 hτ.2 hbr hν hD hF hf hpde hb hu hζ hσ
  have hHmeas : AEStronglyMeasurable H (productVolume O (Ioo a b)) := by
    rw [dg_productVolume_eq_restrict]
    exact dgTruncationEnergyDensity_aestronglyMeasurable hV huv hζs σ k
  have hfull := dg_fullSlab_integrable_of_prefix_bounds hO hab
    (show 0 ≤ M/ν by positivity) hHmeas (.of_forall hH0) (fun τ hτ => by
      refine ⟨dgTruncation_energy_integrable_before_top hO hla hτ.1 hτ.2 hbr hf.2.2.2 hζ,?_⟩
      apply (le_div_iff₀ hν).mpr
      have hh := hpref τ hτ
      have hs := hS0 τ
      nlinarith only [hh,hs])
  have hEfull : ν*dgCylinderIntegral O a b H ≤ M := by
    have hh := (le_div_iff₀ hν).mp hfull.2
    nlinarith only [hh]
  have hSinterior (t : ℝ) (ht : t ∈ Ioo a b) : S t ≤ M := by
    have hh := hpref t ht
    have he0 : 0 ≤ dgCylinderIntegral O a t H := integral_nonneg hH0
    nlinarith [mul_nonneg hν.le he0]
  have hSa : S a ≤ M := by
    dsimp only [M]
    nlinarith [mul_nonneg hK0 hx0,mul_nonneg hF hq0]
  have hSb : S b ≤ M := dg_closed_top_bound hab (dgSliceEnergy_continuousOn hO hu hζ) hSinterior
  have hSall (t : ℝ) (ht : t ∈ Icc a b) : S t ≤ M := by
    rcases eq_or_lt_of_le ht.1 with ha | ha
    · rw [← ha]; exact hSa
    · rcases eq_or_lt_of_le ht.2 with hb' | hb'
      · rw [hb']; exact hSb
      · exact hSinterior t ⟨ha,hb'⟩
  have hcoefx : 2*K0+2*ν ≤ C := by
    dsimp only [K0,C]
    simp only [div_eq_mul_inv]
    nlinarith
  have hcoefq : 4 ≤ C := by
    have hh : 0 ≤ 16*L^2/ν+4*D^2/ν+2*ν := by positivity
    dsimp only [C]
    linarith
  have hcoefs : 2 ≤ C := (by norm_num : (2 : ℝ) ≤ 4).trans hcoefq
  have hBcomp : 2*M+2*ν*x ≤ Btarget := by
    have hx := mul_le_mul_of_nonneg_right hcoefx hx0
    have hq' := mul_le_mul_of_nonneg_right hcoefq (mul_nonneg hF hq0)
    have hs := mul_le_mul_of_nonneg_right hcoefs (hS0 a)
    dsimp only [M,Btarget]
    nlinarith only [hx,hq',hs]
  have hcomp := dgTruncationCutoffGradient_integral_bound hO huv hζs hfull.1 hq.1
  refine ⟨hfull.1,hq.1,hq.2.1,?_,hcomp.1,?_⟩
  · intro t ht
    refine ⟨hq.2.2 t ht,?_⟩
    have hs := hSall t ht
    have he := hEfull
    change S t+ν*dgCylinderIntegral O a b H ≤ Btarget
    nlinarith [mul_nonneg hν.le hx0]
  · change ν*dgCylinderIntegral O a b
      (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)) ≤ Btarget
    have hh := mul_le_mul_of_nonneg_left hcomp.2 hν.le
    change ν*dgCylinderIntegral O a b (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)) ≤
      ν*(2*dgCylinderIntegral O a b H+2*x) at hh
    nlinarith only [hh,hEfull,hBcomp]

theorem dg_local_smooth_compact_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {O : Set E} (hO : IsOpen O)
    {φ v : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hv : ContDiffOn ℝ ∞ v O) :
    ContDiff ℝ ∞ (fun x => φ x*v x) ∧ HasCompactSupport (fun x => φ x*v x) ∧
      tsupport (fun x => φ x*v x) ⊆ O := by
  refine ⟨?_,hcφ.mul_right,tsupport_mul_subset_left.trans hφO⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.contDiffAt.mul (hv.contDiffAt (hO.mem_nhds (hφO hx)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy,Pi.zero_apply,zero_mul]

theorem dgGradient_mul {n : ℕ} {u v : Point n → ℝ} {z : Point n}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (i : Yau.RIdx n) :
    dgGradient (fun q => u q*v q) z i = u z*dgGradient v z i+v z*dgGradient u z i := by
  rw [dgGradient_eq_joint_fderiv (u := fun q => u q*v q) (hu.mul hv) i,
    fderiv_fun_mul hu hv,dgGradient_eq_joint_fderiv hu i,dgGradient_eq_joint_fderiv hv i]
  simp only [add_apply,smul_apply,smul_eq_mul]

theorem dgGradient_scalar_comp {n : ℕ} {w : Point n → ℝ} {β : ℝ → ℝ} {z : Point n}
    (hw : DifferentiableAt ℝ w z) (hβ : DifferentiableAt ℝ β (w z)) (i : Yau.RIdx n) :
    dgGradient (fun q => β (w q)) z i = deriv β (w z)*dgGradient w z i := by
  have hc := hβ.hasDerivAt.comp_hasFDerivAt z hw.hasFDerivAt
  rw [dgGradient_eq_joint_fderiv (u := fun q => β (w q)) hc.differentiableAt i]
  change fderiv ℝ (β ∘ w) z (Yau.realVec i,0) = _
  rw [hc.fderiv,dgGradient_eq_joint_fderiv hw i]
  rfl

/-- Ordinary smooth local flux IBP is the constant-one case of the proved
positive-part chain rule. -/
theorem dg_smooth_flux_ibp {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {P η : Space n → ℝ} (hP : ContDiffOn ℝ ∞ P O) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O) (e : Space n) :
    Integrable (fun x => η x*fderiv ℝ P x e) (volume.restrict O) ∧
    Integrable (fun x => P x*fderiv ℝ η x e) (volume.restrict O) ∧
    (∫ x in O, η x*fderiv ℝ P x e) = -(∫ x in O, P x*fderiv ℝ η x e) := by
  have h := dg_positivepart_flux_ibp (w := fun _ => 1) hO contDiffOn_const hP hη hcη hηO e
  simpa [dgPositivePart] using h

def dgSpatialSmoothFluxBalance {n : ℕ} (m : Space n → ℝ)
    (P : Space n → Yau.RIdx n → ℝ) (x : Space n) : ℝ :=
  ∑ i, (m x*d (fun y => P y i) x i+P x i*d m x i)

theorem dgSpatialSmoothFluxBalance_integral_zero {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {m : Space n → ℝ} {P : Space n → Yau.RIdx n → ℝ}
    (hm : ContDiff ℝ ∞ m) (hcm : HasCompactSupport m) (hmO : tsupport m ⊆ O)
    (hP : ∀ i, ContDiffOn ℝ ∞ (fun x => P x i) O) :
    Integrable (dgSpatialSmoothFluxBalance m P) (volume.restrict O) ∧
    (∫ x in O, dgSpatialSmoothFluxBalance m P x) = 0 := by
  have hi (i : Yau.RIdx n) := dg_smooth_flux_ibp hO (hP i) hm hcm hmO (Yau.realVec i)
  have hInt : Integrable (dgSpatialSmoothFluxBalance m P) (volume.restrict O) :=
    integrable_finsetSum _ (fun i _ => (hi i).1.add (hi i).2.1)
  refine ⟨hInt,?_⟩
  have hsum := integral_finsetSum Finset.univ (fun i _ => (hi i).1.add (hi i).2.1)
  simp only [Pi.add_apply] at hsum
  simp only [dgSpatialSmoothFluxBalance,d]
  rw [hsum]
  apply Finset.sum_eq_zero
  intro i _
  have hs := integral_add (hi i).1 (hi i).2.1
  rw [hs]
  linarith [(hi i).2.2]

/-- The sharp real L² Cauchy--Schwarz bound, with actual square integrals. -/
theorem dg_integral_mul_cauchy {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {p q : E → ℝ} (hp : AEStronglyMeasurable p μ) (hq : AEStronglyMeasurable q μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hp2 : Integrable (fun x => (p x)^2) μ) (hq2 : Integrable (fun x => (q x)^2) μ) :
    Integrable (fun x => p x*q x) μ ∧
    (∫ x, p x*q x ∂μ) ≤ Real.sqrt (∫ x, (p x)^2 ∂μ)*Real.sqrt (∫ x, (q x)^2 ∂μ) := by
  have hpm : MemLp p 2 μ := (memLp_two_iff_integrable_sq hp).mpr hp2
  have hqm : MemLp q 2 μ := (memLp_two_iff_integrable_sq hq).mpr hq2
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    hp0 hq0 (by simpa using hpm) (by simpa using hqm)
  exact ⟨hpm.integrable_mul hqm,by simpa only [Real.rpow_two,← Real.sqrt_eq_rpow] using hh⟩

def dgJointSmoothFluxBalance {n : ℕ} (m : Point n → ℝ)
    (P : Point n → Yau.RIdx n → ℝ) (z : Point n) : ℝ :=
  ∑ i, (m z*dgGradient (fun q => P q i) z i+P z i*dgGradient m z i)

/-- Space-time smooth multiplier IBP on a compact spatial support, without a
time-compact test or any endpoint assertion about coefficient derivatives. -/
theorem dgJointSmoothFluxBalance_integral_zero {n : ℕ}
    {O K : Set (Space n)} {U : Set (Point n)} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) (hU : IsOpen U) {a b : ℝ} (hclosed : O ×ˢ Icc a b ⊆ U)
    {m : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hm : ContDiffOn ℝ ∞ m U) (hP : ∀ i, ContDiffOn ℝ ∞ (fun z => P z i) U)
    (hmslice : ∀ t ∈ Ioo a b, ContDiff ℝ ∞ (fun x => m (x,t)))
    (hmzero : ∀ z : Point n, z.2 ∈ Icc a b → z.1 ∉ K → m z = 0) :
    Integrable (dgJointSmoothFluxBalance m P) (productVolume O (Ioo a b)) ∧
      dgCylinderIntegral O a b (dgJointSmoothFluxBalance m P) = 0 := by
  have hKC : K ×ˢ Icc a b ⊆ U := (Set.prod_mono hKO Subset.rfl).trans hclosed
  have hA (i : Yau.RIdx n) : Integrable (fun z => m z*dgGradient (fun q => P q i) z i)
      (productVolume O (Ioo a b)) := by
    apply dg_integrable_of_compact_spatial_support hO hK
      ((hm.continuousOn.mul (dgGradient_contDiffOn hU (hP i) i).continuousOn).mono hKC)
    intro z hz hx
    change m z*dgGradient (fun q => P q i) z i = 0
    rw [hmzero z (Ioo_subset_Icc_self hz.2) hx]; exact zero_mul _
  have hB (i : Yau.RIdx n) : Integrable (fun z => P z i*dgGradient m z i)
      (productVolume O (Ioo a b)) := by
    apply dg_integrable_of_compact_spatial_support hO hK
      (((hP i).continuousOn.mul (dgGradient_contDiffOn hU hm i).continuousOn).mono hKC)
    intro z hz hx
    change P z i*dgGradient m z i = 0
    rw [dg_cutoff_gradient_zero hK.isClosed hmzero (Ioo_subset_Icc_self hz.2) hx]
    exact mul_zero _
  have hInt : Integrable (dgJointSmoothFluxBalance m P) (productVolume O (Ioo a b)) :=
    integrable_finsetSum _ (fun i _ => (hA i).add (hB i))
  refine ⟨hInt,?_⟩
  unfold dgCylinderIntegral productVolume
  rw [integral_prod_symm _ hInt]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hPs (i : Yau.RIdx n) : ContDiffOn ℝ ∞ (fun x => P (x,t) i) O :=
    (hP i).comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x hx => hclosed ⟨hx,Ioo_subset_Icc_self ht⟩)
  have hsupp : tsupport (fun x => m (x,t)) ⊆ K := by
    apply hK.isClosed.closure_subset_iff.mpr
    intro x hx
    by_contra hxK
    exact hx (hmzero (x,t) (Ioo_subset_Icc_self ht) hxK)
  have hcm : HasCompactSupport (fun x => m (x,t)) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hsupp
  exact (dgSpatialSmoothFluxBalance_integral_zero hO (hmslice t ht) hcm (hsupp.trans hKO) hPs).2

def dgSmoothMeanMultiplier {n : ℕ} (φ : Space n → ℝ) (ε σ k : ℝ)
    (u : Point n → ℝ) (z : Point n) : ℝ := φ z.1*dgSmoothStep ε (σ*u z-k)

def dgSmoothMeanTimeDensity {n : ℕ} (φ : Space n → ℝ) (ε σ k : ℝ)
    (u : Point n → ℝ) (z : Point n) : ℝ :=
  dgSmoothMeanMultiplier φ ε σ k u z*(σ*deriv (fun t => u (z.1,t)) z.2)

def dgSmoothMeanDensity {n : ℕ} (A : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) (φ : Space n → ℝ) (F ε σ k : ℝ)
    (u : Point n → ℝ) (z : Point n) : ℝ :=
  -dgBilinear (A z) (fun j => dgSmoothStep ε (σ*u z-k)*(σ*dgGradient u z j))
    (fun i => d φ z.1 i) +
    (∑ i, c z i*(dgSmoothStep ε (σ*u z-k)*(σ*dgGradient u z i)))*φ z.1 + F*φ z.1

theorem dgSmoothMeanMultiplier_gradient {n : ℕ} {w : Point n → ℝ}
    {φ : Space n → ℝ} {θ : ℝ → ℝ} {z : Point n}
    (hw : DifferentiableAt ℝ w z) (hφ : ContDiff ℝ ∞ φ)
    (hθ : DifferentiableAt ℝ θ (w z)) (i : Yau.RIdx n) :
    dgGradient (fun q => φ q.1*θ (w q)) z i =
      φ z.1*deriv θ (w z)*dgGradient w z i+θ (w z)*d φ z.1 i := by
  have hφj := (hφ.comp contDiff_fst).differentiable (by simp) z
  have hθw := hθ.comp z hw
  rw [dgGradient_mul (u := fun q => φ q.1) (v := fun q => θ (w q)) hφj hθw i,
    dgGradient_scalar_comp hw hθ i]
  change φ z.1*(deriv θ (w z)*dgGradient w z i)+θ (w z)*d φ z.1 i = _
  ring

theorem dgSmoothMeanMultiplier_contDiffOn {n : ℕ} {U : Set (Point n)}
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u U) {φ : Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (ε σ k : ℝ) :
    ContDiffOn ℝ ∞ (dgSmoothMeanMultiplier φ ε σ k u) U :=
  (hφ.comp contDiff_fst).contDiffOn.mul
    ((dgSmoothStep_contDiff ε).comp_contDiffOn ((contDiffOn_const.mul hu).sub contDiffOn_const))

theorem dgSmoothMeanDensity_continuousOn {n : ℕ} {U : Set (Point n)} (hU : IsOpen U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields U A c f u) {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (F ε σ k : ℝ) :
    ContinuousOn (dgSmoothMeanDensity A c φ F ε σ k u) U := by
  have hθ : ContinuousOn (fun z => dgSmoothStep ε (σ*u z-k)) U :=
    ((dgSmoothStep_contDiff ε).comp_contDiffOn ((contDiffOn_const.mul hf.2.2.2).sub contDiffOn_const)).continuousOn
  have hG (i : Yau.RIdx n) := (dgGradient_contDiffOn hU hf.2.2.2 i).continuousOn
  have hφD (i : Yau.RIdx n) : Continuous (fun z : Point n => d φ z.1 i) :=
    ((((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).comp contDiff_fst)).continuous
  have hB : ContinuousOn (fun z => dgBilinear (A z)
      (fun j => dgSmoothStep ε (σ*u z-k)*(σ*dgGradient u z j)) (fun i => d φ z.1 i)) U :=
    continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      (((hf.1 i j).continuousOn.mul (hθ.mul (continuousOn_const.mul (hG j)))).mul (hφD i).continuousOn)))
  have hC : ContinuousOn (fun z => ∑ i, c z i*(dgSmoothStep ε (σ*u z-k)*(σ*dgGradient u z i))) U :=
    continuousOn_finsetSum _ (fun i _ => (hf.2.1 i).continuousOn.mul (hθ.mul (continuousOn_const.mul (hG i))))
  exact (hB.neg.add (hC.mul (hφ.comp contDiff_fst).continuous.continuousOn)).add
    (continuousOn_const.mul (hφ.comp contDiff_fst).continuous.continuousOn)

theorem dgSmoothMean_time_before_top {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r s t τ ε σ k : ℝ} (hls : l < s) (hsτ : s < τ) (hτt : τ < t) (htr : t ≤ r)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo l r))
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) :
    Integrable (dgSmoothMeanTimeDensity φ ε σ k u) (productVolume O (Ioo s τ)) ∧
    dgCylinderIntegral O s τ (dgSmoothMeanTimeDensity φ ε σ k u) =
      (∫ x in O, φ x*dgSmoothPos ε (σ*u (x,τ)-k)) -
        ∫ x in O, φ x*dgSmoothPos ε (σ*u (x,s)-k) := by
  let U := O ×ˢ Ioo l r
  let w : Point n → ℝ := fun z => σ*u z-k
  let g : Point n → ℝ := fun z => φ z.1*dgSmoothPos ε (w z)
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hclosed : O ×ˢ Icc s τ ⊆ U := by
    intro z hz
    exact ⟨hz.1,hls.trans_le hz.2.1,hz.2.2.trans_lt (hτt.trans_le htr)⟩
  have hw : ContDiffOn ℝ ∞ w U := (contDiffOn_const.mul hu).sub contDiffOn_const
  have hgc : ContinuousOn g (O ×ˢ Icc s τ) :=
    (((hφ.comp contDiff_fst).contDiffOn.mul ((dgSmoothPos_contDiff ε).comp_contDiffOn hw)).continuousOn).mono hclosed
  have hTc : ContinuousOn (dgSmoothMeanTimeDensity φ ε σ k u) (O ×ˢ Icc s τ) :=
    (((dgSmoothMeanMultiplier_contDiffOn hu hφ ε σ k).mul
      (contDiffOn_const.mul (dgTimeDeriv_contDiffOn hU hu))).continuousOn).mono hclosed
  have hres := dg_finiteTime_integral_identity hO hcφ hφO hsτ.le hgc hTc
    (fun z _ hz => by
      change φ z.1*dgSmoothPos ε (w z) = 0
      rw [image_eq_zero_of_notMem_tsupport hz]; exact zero_mul _)
    (fun z _ hz => by
      change (φ z.1*dgSmoothStep ε (σ*u z-k))*(σ*deriv (fun q => u (z.1,q)) z.2) = 0
      rw [image_eq_zero_of_notMem_tsupport hz]; simp) (fun x hx q hq => by
      have hz : (x,q) ∈ U := hclosed ⟨hx,Ioo_subset_Icc_self hq⟩
      have hud := (hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
      have hMap : DifferentiableAt ℝ (fun v : ℝ => (x,v)) q :=
        ((hasFDerivAt_const x q).prodMk (hasFDerivAt_id q)).differentiableAt
      have hws := (((hud.comp q hMap).const_mul σ).sub_const k).hasDerivAt
      have hd := ((dgSmoothPos_hasDerivAt ε (σ*u (x,q)-k)).comp q hws).const_mul (φ x)
      change HasDerivAt (fun v => φ x*dgSmoothPos ε (σ*u (x,v)-k))
        (φ x*(dgSmoothStep ε (σ*u (x,q)-k)*deriv (fun v => σ*u (x,v)-k) q)) q at hd
      rw [dgTimeDeriv_affine hud] at hd
      change HasDerivAt (fun v => φ x*dgSmoothPos ε (σ*u (x,v)-k))
        ((φ x*dgSmoothStep ε (σ*u (x,q)-k))*(σ*deriv (fun v => u (x,v)) q)) q
      convert hd using 1 <;> ring)
  exact hres

theorem dgBilinear_smul_left {n : ℕ} (A : Mat n) (θ : ℝ) (p q : Yau.RIdx n → ℝ) :
    dgBilinear A (fun j => θ*p j) q = θ*dgBilinear A p q := by
  simp only [dgBilinear,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dgSmoothMeanDensity_zero_off {n : ℕ} (A : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) {φ : Space n → ℝ} (F ε σ k : ℝ)
    (u : Point n → ℝ) {z : Point n} (hz : z.1 ∉ tsupport φ) :
    dgSmoothMeanDensity A c φ F ε σ k u z = 0 := by
  simp only [dgSmoothMeanDensity,dgBilinear,d,fderiv_of_notMem_tsupport ℝ hz,
    image_eq_zero_of_notMem_tsupport hz,zero_apply,mul_zero,Finset.sum_const_zero,neg_zero,zero_add]

theorem dgSmoothMean_subsolution_pointwise {n : ℕ} {U : Set (Point n)} (hU : IsOpen U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    {φ : Space n → ℝ} {ν L D F ε σ k : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    (hf : DGClassicalFields U A c f u) (hpde : ClassicalDivEq U A c f u)
    (hb : DGUniformBounds U A c f ν L D F) (hσ : DGSign σ)
    (hφ : ContDiff ℝ ∞ φ) (hφ0 : ∀ x, 0 ≤ φ x) {z : Point n} (hz : z ∈ U) :
    dgSmoothMeanTimeDensity φ ε σ k u z-dgSmoothMeanDensity A c φ F ε σ k u z ≤
      dgJointSmoothFluxBalance (dgSmoothMeanMultiplier φ ε σ k u) (dgFlux A (fun q => σ*u q-k)) z := by
  let w : Point n → ℝ := fun q => σ*u q-k
  let W : Yau.RIdx n → ℝ := fun i => σ*dgGradient u z i
  let θ := dgSmoothStep ε (w z)
  let θ' := deriv (dgSmoothStep ε) (w z)
  let dφ : Yau.RIdx n → ℝ := fun i => d φ z.1 i
  let m := dgSmoothMeanMultiplier φ ε σ k u
  let P := dgFlux A w
  have huz := (hf.2.2.2.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hwz := (huz.const_mul σ).sub_const k
  have hθz := (dgSmoothStep_contDiff ε).differentiable (by simp) (w z)
  have hW (i : Yau.RIdx n) : dgGradient w z i = W i := dgGradient_affine huz σ k i
  have hPval (i : Yau.RIdx n) : P z i = ∑ j, A z i j*W j := by
    unfold P dgFlux
    simp only [hW]
  have hmgrad (i : Yau.RIdx n) : dgGradient m z i = φ z.1*θ'*W i+θ*dφ i := by
    have hh := dgSmoothMeanMultiplier_gradient hwz hφ hθz i
    rw [hW] at hh
    exact hh
  have hsum1 : (∑ i, m z*dgGradient (fun q => P q i) z i) =
      (φ z.1*θ)*(∑ i, dgGradient (fun q => P q i) z i) := by
    rw [Finset.mul_sum]
    rfl
  have hsum2 : (∑ i, P z i*dgGradient m z i) =
      φ z.1*θ'*dgBilinear (A z) W W+θ*dgBilinear (A z) W dφ := by
    simp only [hPval,hmgrad,mul_add,Finset.sum_add_distrib,dgBilinear,Finset.mul_sum,Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;> ring
  have hDb : dgJointSmoothFluxBalance m P z =
      (φ z.1*θ)*(∑ i, dgGradient (fun q => P q i) z i) +
        φ z.1*θ'*dgBilinear (A z) W W+θ*dgBilinear (A z) W dφ := by
    simp only [dgJointSmoothFluxBalance,Finset.sum_add_distrib]
    rw [hsum1,hsum2]
    ring
  have hcscale : (∑ i, c z i*(θ*W i)) = θ*(∑ i, c z i*W i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hGb : dgSmoothMeanDensity A c φ F ε σ k u z =
      -θ*dgBilinear (A z) W dφ+θ*(∑ i, c z i*W i)*φ z.1+F*φ z.1 := by
    change -dgBilinear (A z) (fun i => θ*W i) dφ +
      (∑ i, c z i*(θ*W i))*φ z.1+F*φ z.1 = _
    rw [dgBilinear_smul_left,hcscale]
    ring
  have heq := dgClassicalDivEq_affine hU hf hpde σ k z hz
  change deriv (fun q => σ*u (z.1,q)-k) z.2 -
    (∑ i, dgGradient (fun q => P q i) z i) = (∑ i, c z i*dgGradient w z i)+σ*f z at heq
  rw [dgTimeDeriv_affine huz] at heq
  simp only [hW] at heq
  have heqm := congrArg (fun v : ℝ => φ z.1*θ*v) heq
  have hquad : 0 ≤ dgBilinear (A z) W W :=
    (mul_nonneg hb.1.1.le (dgGradientSq_nonneg W)).trans (dg_elliptic_lower hb.1 hz W)
  have hdefect : 0 ≤ φ z.1*θ'*dgBilinear (A z) W W :=
    mul_nonneg (mul_nonneg (hφ0 z.1) (dgSmoothStep_deriv_nonneg hε (w z))) hquad
  have hθ0 := (dgSmoothStep_bounds ε (w z)).1
  have hθ1 := (dgSmoothStep_bounds ε (w z)).2
  have hsource : θ*(σ*f z) ≤ F := by
    have hs := (le_abs_self (σ*f z)).trans (dg_sign_forcing_bound hσ (hb.2.2 z hz))
    exact (mul_le_mul_of_nonneg_left hs hθ0).trans
      ((mul_le_mul_of_nonneg_right hθ1 hF).trans_eq (one_mul F))
  have hsourceφ : 0 ≤ (F-θ*(σ*f z))*φ z.1 := mul_nonneg (sub_nonneg.mpr hsource) (hφ0 z.1)
  change dgSmoothMeanTimeDensity φ ε σ k u z-dgSmoothMeanDensity A c φ F ε σ k u z ≤
    dgJointSmoothFluxBalance m P z
  rw [hDb,hGb]
  change (φ z.1*θ)*(σ*deriv (fun q => u (z.1,q)) z.2) -
    (-θ*dgBilinear (A z) W dφ+θ*(∑ i, c z i*W i)*φ z.1+F*φ z.1) ≤ _
  nlinarith only [heqm,hdefect,hsourceφ]

/-- Smooth convex positive-part mean inequality on an interior terminal time.
The nonnegative convex defect is discarded before any limiting argument. -/
theorem dgSmoothMean_before_top {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r s t τ ν L D F ε σ k : ℝ} (hls : l < s) (hsτ : s < τ) (hτt : τ < t) (htr : t ≤ r)
    (hε : 0 < ε) (hF : 0 ≤ F)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields (O ×ˢ Ioo l r) A c f u)
    (hpde : ClassicalDivEq (O ×ˢ Ioo l r) A c f u)
    (hb : DGUniformBounds (O ×ˢ Ioo l r) A c f ν L D F) (hσ : DGSign σ)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    (∫ x in O, φ x*dgSmoothPos ε (σ*u (x,τ)-k)) -
      (∫ x in O, φ x*dgSmoothPos ε (σ*u (x,s)-k)) ≤
    dgCylinderIntegral O s τ (dgSmoothMeanDensity A c φ F ε σ k u) := by
  let U := O ×ˢ Ioo l r
  let w : Point n → ℝ := fun z => σ*u z-k
  let m := dgSmoothMeanMultiplier φ ε σ k u
  let P := dgFlux A w
  let D0 := dgJointSmoothFluxBalance m P
  let T0 := dgSmoothMeanTimeDensity φ ε σ k u
  let G0 := dgSmoothMeanDensity A c φ F ε σ k u
  let μ := productVolume O (Ioo s τ)
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hclosed : O ×ˢ Icc s τ ⊆ U := by
    intro z hz
    exact ⟨hz.1,hls.trans_le hz.2.1,hz.2.2.trans_lt (hτt.trans_le htr)⟩
  have hw : ContDiffOn ℝ ∞ w U := (contDiffOn_const.mul hf.2.2.2).sub contDiffOn_const
  have hm : ContDiffOn ℝ ∞ m U := dgSmoothMeanMultiplier_contDiffOn hf.2.2.2 hφ ε σ k
  have hP (i : Yau.RIdx n) := dgFlux_contDiffOn hU hf.1 hw i
  have hmslice (q : ℝ) (hq : q ∈ Ioo s τ) : ContDiff ℝ ∞ (fun x => m (x,q)) := by
    have hws : ContDiffOn ℝ ∞ (fun x => w (x,q)) O :=
      hw.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun x hx => hclosed ⟨hx,Ioo_subset_Icc_self hq⟩)
    exact (dg_local_smooth_compact_mul hO hφ hcφ hφO ((dgSmoothStep_contDiff ε).comp_contDiffOn hws)).1
  have hmzero : ∀ z : Point n, z.2 ∈ Icc s τ → z.1 ∉ tsupport φ → m z = 0 := by
    intro z _ hz
    change φ z.1*dgSmoothStep ε (σ*u z-k) = 0
    rw [image_eq_zero_of_notMem_tsupport hz]; exact zero_mul _
  have hD := dgJointSmoothFluxBalance_integral_zero hO hcφ hφO hU hclosed hm hP hmslice hmzero
  have hT := dgSmoothMean_time_before_top (ε := ε) (σ := σ) (k := k)
    hO hls hsτ hτt htr hf.2.2.2 hφ hcφ hφO
  have hG : Integrable G0 μ := by
    apply dg_integrable_of_compact_spatial_support hO hcφ
      ((dgSmoothMeanDensity_continuousOn hU hf hφ F ε σ k).mono
        ((Set.prod_mono hφO Subset.rfl).trans hclosed))
    intro z _ hz
    exact dgSmoothMeanDensity_zero_off A c F ε σ k u hz
  have hpoint : ∀ᵐ z ∂μ, T0 z-G0 z ≤ D0 z := by
    change ∀ᵐ z ∂productVolume O (Ioo s τ), T0 z-G0 z ≤ D0 z
    rw [dg_productVolume_eq_restrict]
    filter_upwards [ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet] with z hz
    exact dgSmoothMean_subsolution_pointwise hU hε hF hf hpde hb hσ hφ hφ0
      (hclosed ⟨hz.1,Ioo_subset_Icc_self hz.2⟩)
  have hh := integral_mono_ae (hT.1.sub hG) hD.1 hpoint
  have hsub : dgCylinderIntegral O s τ (fun z => T0 z-G0 z) =
      dgCylinderIntegral O s τ T0-dgCylinderIntegral O s τ G0 := by
    have hs := integral_sub hT.1 hG
    simpa only [dgCylinderIntegral,Pi.sub_apply,T0,μ] using hs
  change dgCylinderIntegral O s τ (fun z => T0 z-G0 z) ≤ dgCylinderIntegral O s τ D0 at hh
  have hDzero : dgCylinderIntegral O s τ D0 = 0 := hD.2
  rw [hsub,hDzero] at hh
  have hTval : dgCylinderIntegral O s τ T0 =
      (∫ x in O, φ x*dgSmoothPos ε (σ*u (x,τ)-k)) -
        ∫ x in O, φ x*dgSmoothPos ε (σ*u (x,s)-k) := hT.2
  rw [hTval] at hh
  linarith

/-- A genuine compact spatial plateau, chosen only from the test support. -/
theorem dg_exists_spatial_plateau {n : ℕ} {O K : Set (Space n)} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ χ : Space n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨V,hV,hKV,hVO,hVC⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨W,hW,hVW,hWO,hWC⟩ := exists_open_between_and_isCompact_closure hVC hO hVO
  obtain ⟨χ,hχ,hrange,hsupport,hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW (isClosed_closure : IsClosed (closure V)) hVW
  have hcχ : HasCompactSupport χ := by
    change IsCompact (tsupport χ)
    simpa only [tsupport,hsupport] using hWC
  have hχO : tsupport χ ⊆ O := by simpa only [tsupport,hsupport] using hWO
  exact ⟨χ,hχ,hcχ,hχO,fun x => hrange ⟨x,rfl⟩,fun x hx => (hone x).mp (subset_closure (hKV hx))⟩

def dgTruncationGradientNorm {n : ℕ} (σ k : ℝ) (u : Point n → ℝ) (z : Point n) : ℝ :=
  Real.sqrt (dgGradientSq (dgTruncationGradient σ k u z))

def dgSpatialTestGradientNorm {n : ℕ} (φ : Space n → ℝ) (x : Space n) : ℝ :=
  Real.sqrt (dgGradientSq (fun i => d φ x i))

theorem dgTruncationGradientNorm_aestronglyMeasurable {n : ℕ} {U : Set (Point n)}
    (hU : IsOpen U) {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (σ k : ℝ) :
    AEStronglyMeasurable (dgTruncationGradientNorm σ k u) (volume.restrict U) := by
  have hs : AEStronglyMeasurable (fun z => dgGradientSq (dgTruncationGradient σ k u z)) (volume.restrict U) :=
    Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (dgTruncationGradient_aestronglyMeasurable hU hu σ k i).pow 2)
  exact Real.continuous_sqrt.comp_aestronglyMeasurable hs

theorem dgSpatialTestGradientNorm_continuous {n : ℕ} {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (dgSpatialTestGradientNorm φ) := by
  apply Real.continuous_sqrt.comp
  exact continuous_finsetSum _ (fun i _ =>
    (((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.pow 2))

theorem dg_spatial_time_integral {n : ℕ} (O : Set (Space n)) {s t : ℝ} (hst : s ≤ t)
    (f : Space n → ℝ) : dgCylinderIntegral O s t (fun z => f z.1) = (t-s)*(∫ x in O, f x) := by
  have htime : (∫ _q in Ioo s t, (1 : ℝ)) = t-s := by
    simp only [integral_const,measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst),smul_eq_mul,mul_one]
  have hh := integral_prod_mul (μ := volume.restrict O) (ν := volume.restrict (Ioo s t)) f (fun _ => (1 : ℝ))
  simp only [mul_one] at hh
  rw [htime] at hh
  exact hh.trans (mul_comm _ _)

theorem dg_test_product_integrable {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {s t : ℝ} {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) :
    Integrable (fun z : Point n => φ z.1) (productVolume O (Ioo s t)) ∧
    Integrable (fun z : Point n => (φ z.1)^2) (productVolume O (Ioo s t)) ∧
    Integrable (fun z : Point n => dgGradientSq (fun i => d φ z.1 i)) (productVolume O (Ioo s t)) := by
  have hφi : Integrable φ (volume.restrict O) := hφ.continuous.integrable_of_hasCompactSupport hcφ |>.integrableOn
  have hφ2 : Integrable (fun x => (φ x)^2) (volume.restrict O) := by
    apply dg_integrable_spatial hO hcφ hφO (hφ.continuous.pow 2).continuousOn
    intro x _ hx
    change (φ x)^2 = 0
    rw [image_eq_zero_of_notMem_tsupport hx]; exact zero_pow (by decide : 2 ≠ 0)
  have hGi : Integrable (fun x => dgGradientSq (fun i => d φ x i)) (volume.restrict O) := by
    have hc : Continuous (fun x => dgGradientSq (fun i => d φ x i)) :=
      continuous_finsetSum _ (fun i _ => (((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.pow 2))
    apply dg_integrable_spatial hO hcφ hφO hc.continuousOn
    intro x _ hx
    simp only [dgGradientSq,d,fderiv_of_notMem_tsupport ℝ hx,zero_apply,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
  have h1 := hφi.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo s t)))
  have h2 := hφ2.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo s t)))
  have h3 := hGi.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo s t)))
  simpa only [productVolume,mul_one] using And.intro h1 (And.intro h2 h3)

def dgMeanMajorant {n : ℕ} (χ φ : Space n → ℝ) (L D F σ k : ℝ) (u : Point n → ℝ) (z : Point n) : ℝ :=
  L*((χ z.1*dgTruncationGradientNorm σ k u z)*dgSpatialTestGradientNorm φ z.1) +
    D*((χ z.1*dgTruncationGradientNorm σ k u z)*φ z.1)+F*φ z.1

theorem dgMeanMajorant_integrable {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {s t L D F σ k : ℝ} {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo s t))
    {χ φ : Space n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x)
    (hE : Integrable (dgTruncationEnergyDensity σ k u (fun z => χ z.1)) (productVolume O (Ioo s t))) :
    Integrable (dgMeanMajorant χ φ L D F σ k u) (productVolume O (Ioo s t)) := by
  let μ := productVolume O (Ioo s t)
  let p : Point n → ℝ := fun z => χ z.1*dgTruncationGradientNorm σ k u z
  let q1 : Point n → ℝ := fun z => dgSpatialTestGradientNorm φ z.1
  let q2 : Point n → ℝ := fun z => φ z.1
  have hp : AEStronglyMeasurable p μ := by
    rw [show μ = volume.restrict (O ×ˢ Ioo s t) from dg_productVolume_eq_restrict O _]
    exact (hχ.comp contDiff_fst).continuous.aestronglyMeasurable.mul
      (dgTruncationGradientNorm_aestronglyMeasurable (hO.prod isOpen_Ioo) hu σ k)
  have hq1 : AEStronglyMeasurable q1 μ :=
    ((dgSpatialTestGradientNorm_continuous hφ).comp continuous_fst).aestronglyMeasurable
  have hq2 : AEStronglyMeasurable q2 μ := (hφ.comp contDiff_fst).continuous.aestronglyMeasurable
  have hp2 : Integrable (fun z => (p z)^2) μ := hE.congr (.of_forall fun z => by
    dsimp only [p,dgTruncationGradientNorm,dgTruncationEnergyDensity]
    rw [mul_pow,Real.sq_sqrt (dgGradientSq_nonneg _)]
    ring)
  have htst := dg_test_product_integrable (s := s) (t := t) hO hφ hcφ hφO
  have hq12 : Integrable (fun z => (q1 z)^2) μ := htst.2.2.congr (.of_forall fun z => by
    dsimp only [q1,dgSpatialTestGradientNorm]
    exact (Real.sq_sqrt (dgGradientSq_nonneg _)).symm)
  have hI1 := (dg_integral_mul_cauchy hp hq1
    (.of_forall fun z => mul_nonneg (hχ0 z.1) (Real.sqrt_nonneg _))
    (.of_forall fun _ => Real.sqrt_nonneg _) hp2 hq12).1
  have hI2 := (dg_integral_mul_cauchy hp hq2
    (.of_forall fun z => mul_nonneg (hχ0 z.1) (Real.sqrt_nonneg _))
    (.of_forall fun z => hφ0 z.1) hp2 htst.2.1).1
  exact ((hI1.const_mul L).add (hI2.const_mul D)).add (htst.1.const_mul F)

theorem dg_mean_abs_bound {θ a b φ F A B : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hφ : 0 ≤ φ) (hF : 0 ≤ F) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |-θ*a+θ*b*φ+F*φ| ≤ A+B*φ+F*φ := by
  have hθ : |θ| ≤ 1 := by rwa [abs_of_nonneg hθ0]
  have hA : |-θ*a| ≤ A := by
    rw [abs_mul,abs_neg]
    simpa only [one_mul] using mul_le_mul hθ ha (abs_nonneg a) (by norm_num : (0 : ℝ) ≤ 1)
  have hB : |θ*b*φ| ≤ B*φ := by
    rw [abs_mul,abs_of_nonneg hφ,abs_mul]
    have hh : |θ| * |b| ≤ B := by
      simpa only [one_mul] using mul_le_mul hθ hb (abs_nonneg b) (by norm_num : (0 : ℝ) ≤ 1)
    exact mul_le_mul_of_nonneg_right hh hφ
  calc
    _ ≤ |-θ*a+θ*b*φ|+|F*φ| := abs_add_le _ _
    _ ≤ (|-θ*a|+|θ*b*φ|)+|F*φ| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ A+B*φ+F*φ := by
      rw [abs_of_nonneg (mul_nonneg hF hφ)]
      exact add_le_add (add_le_add hA hB) le_rfl

theorem dgSmoothMeanDensity_eq_truncated {n : ℕ} (A : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) (φ : Space n → ℝ) (F σ k : ℝ)
    (u : Point n → ℝ) {ε : ℝ} (hε : 0 < ε) (z : Point n) :
    dgSmoothMeanDensity A c φ F ε σ k u z =
      -dgSmoothStep ε (σ*u z-k)*dgBilinear (A z) (dgTruncationGradient σ k u z) (fun i => d φ z.1 i) +
      dgSmoothStep ε (σ*u z-k)*(∑ i, c z i*dgTruncationGradient σ k u z i)*φ z.1+F*φ z.1 := by
  by_cases ha : k < σ*u z
  · have hg : dgTruncationGradient σ k u z = fun i => σ*dgGradient u z i := by
      funext i; exact ite_eq_left ha
    rw [hg]
    unfold dgSmoothMeanDensity
    rw [dgBilinear_smul_left]
    have hs : (∑ i, c z i*(dgSmoothStep ε (σ*u z-k)*(σ*dgGradient u z i))) =
        dgSmoothStep ε (σ*u z-k)*(∑ i, c z i*(σ*dgGradient u z i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  · have hθ := dgSmoothStep_zero hε (sub_nonpos.mpr (le_of_not_gt ha))
    simp only [dgSmoothMeanDensity,hθ,dgBilinear,zero_mul,mul_zero,Finset.sum_const_zero,neg_zero,
      zero_add,add_zero]

theorem dgTruncationMeanDensity_zero_off {n : ℕ} (A : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) {φ : Space n → ℝ} (F σ k : ℝ)
    (u : Point n → ℝ) {z : Point n} (hz : z.1 ∉ tsupport φ) :
    dgTruncationMeanDensity A c φ F σ k u z = 0 := by
  simp only [dgTruncationMeanDensity,d,fderiv_of_notMem_tsupport ℝ hz,
    image_eq_zero_of_notMem_tsupport hz,zero_apply,mul_zero,Finset.sum_const_zero,neg_zero,zero_add]

theorem dgMeanMajorant_dominates {n : ℕ} {U : Set (Point n)}
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    {χ φ : Space n → ℝ} {ν L D F σ k : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hb : DGUniformBounds U A c f ν L D F) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x ∈ tsupport φ, χ x = 1) (hφ0 : ∀ x, 0 ≤ φ x)
    {z : Point n} (hz : z ∈ U) :
    |dgTruncationMeanDensity A c φ F σ k u z| ≤ dgMeanMajorant χ φ L D F σ k u z ∧
    ∀ ε : ℝ, 0 < ε → |dgSmoothMeanDensity A c φ F ε σ k u z| ≤ dgMeanMajorant χ φ L D F σ k u z := by
  have hL : 0 ≤ L := hb.1.1.le.trans hb.1.2.1
  have hW0 : 0 ≤ dgMeanMajorant χ φ L D F σ k u z := by
    dsimp only [dgMeanMajorant,dgTruncationGradientNorm,dgSpatialTestGradientNorm]
    have hc0 := hχ0 z.1
    have hp0 := hφ0 z.1
    positivity
  by_cases hx : z.1 ∈ tsupport φ
  · have hc1 := hχ1 z.1 hx
    let g := dgTruncationGradient σ k u z
    let q : Yau.RIdx n → ℝ := fun i => d φ z.1 i
    have hA := dg_elliptic_bilinear_bound hb.1 hz g q
    have hB := dg_drift_bound hD (hb.2.1 z hz) g
    have hraw (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
        |-θ*dgBilinear (A z) g q+θ*(∑ i, c z i*g i)*φ z.1+F*φ z.1| ≤
          dgMeanMajorant χ φ L D F σ k u z := by
      have hh := dg_mean_abs_bound hθ0 hθ1 (hφ0 z.1) hF hA hB
      dsimp only [dgMeanMajorant,dgTruncationGradientNorm,dgSpatialTestGradientNorm]
      rw [hc1]
      simpa only [one_mul,mul_assoc] using hh
    refine ⟨?_,?_⟩
    · have hh := hraw 1 (by norm_num) le_rfl
      simpa only [one_mul,neg_one_mul,dgTruncationMeanDensity,dgBilinear,g,q] using hh
    · intro ε hε
      rw [dgSmoothMeanDensity_eq_truncated A c φ F σ k u hε z]
      exact hraw _ (dgSmoothStep_bounds _ _).1 (dgSmoothStep_bounds _ _).2
  · rw [dgTruncationMeanDensity_zero_off A c F σ k u hx]
    refine ⟨by simpa only [abs_zero] using hW0,?_⟩
    intro ε _
    rw [dgSmoothMeanDensity_zero_off A c F ε σ k u hx]
    simpa only [abs_zero] using hW0

theorem dgTruncationMeanDensity_aestronglyMeasurable {n : ℕ} {U : Set (Point n)} (hU : IsOpen U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields U A c f u) {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (F σ k : ℝ) :
    AEStronglyMeasurable (dgTruncationMeanDensity A c φ F σ k u) (volume.restrict U) := by
  have hA (i j : Yau.RIdx n) := (hf.1 i j).continuousOn.aestronglyMeasurable (μ := volume) hU.measurableSet
  have hC (i : Yau.RIdx n) := (hf.2.1 i).continuousOn.aestronglyMeasurable (μ := volume) hU.measurableSet
  have hG (i : Yau.RIdx n) := dgTruncationGradient_aestronglyMeasurable hU hf.2.2.2 σ k i
  have hφA : AEStronglyMeasurable (fun z : Point n => φ z.1) (volume.restrict U) :=
    (hφ.comp contDiff_fst).continuous.aestronglyMeasurable
  have hφD (i : Yau.RIdx n) : AEStronglyMeasurable (fun z : Point n => d φ z.1 i) (volume.restrict U) :=
    ((((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).comp contDiff_fst)).continuous.aestronglyMeasurable
  exact ((Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
    Finset.aestronglyMeasurable_fun_sum _ (fun j _ => ((hA i j).mul (hG j)).mul (hφD i)))).neg.add
    ((Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (hC i).mul (hG i))).mul hφA)).add
    (hφA.const_mul F)

theorem dgSmoothMeanDensity_tendsto {n : ℕ} (A : Point n → Mat n)
    (c : Point n → Yau.RIdx n → ℝ) (φ : Space n → ℝ) (F σ k : ℝ) (u : Point n → ℝ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hlim : Tendsto ε atTop (𝓝 0)) (z : Point n) :
    Tendsto (fun j => dgSmoothMeanDensity A c φ F (ε j) σ k u z) atTop
      (𝓝 (dgTruncationMeanDensity A c φ F σ k u z)) := by
  by_cases ha : k < σ*u z
  · let a := dgBilinear (A z) (dgTruncationGradient σ k u z) (fun i => d φ z.1 i)
    let b := ∑ i, c z i*dgTruncationGradient σ k u z i
    have hθ : Tendsto (fun j => dgSmoothStep (ε j) (σ*u z-k)) atTop (𝓝 1) := by
      simpa only [ite_eq_left (sub_pos.mpr ha)] using dgSmoothStep_tendsto hε hlim (σ*u z-k)
    have hh := (((hθ.neg.mul_const a).add ((hθ.mul_const b).mul_const (φ z.1))).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => F*φ z.1) atTop (𝓝 (F*φ z.1))))
    have heq : (fun j => -dgSmoothStep (ε j) (σ*u z-k)*a+
        dgSmoothStep (ε j) (σ*u z-k)*b*φ z.1+F*φ z.1) =
        (fun j => dgSmoothMeanDensity A c φ F (ε j) σ k u z) := by
      funext j
      exact (dgSmoothMeanDensity_eq_truncated A c φ F σ k u (hε j) z).symm
    rw [← heq]
    change Tendsto _ atTop (𝓝 (-a+b*φ z.1+F*φ z.1))
    simpa only [neg_one_mul,one_mul] using hh
  · have hg : dgTruncationMeanDensity A c φ F σ k u z = F*φ z.1 := by
      simp only [dgTruncationMeanDensity,dgTruncationGradient,ite_eq_right ha,mul_zero,zero_mul,
        Finset.sum_const_zero,neg_zero,zero_add]
    have heq : (fun j => dgSmoothMeanDensity A c φ F (ε j) σ k u z) = fun _ => F*φ z.1 := by
      funext j
      have hθ := dgSmoothStep_zero (hε j) (sub_nonpos.mpr (le_of_not_gt ha))
      simp only [dgSmoothMeanDensity,hθ,dgBilinear,zero_mul,mul_zero,Finset.sum_const_zero,neg_zero,zero_add]
    rw [heq,hg]
    exact tendsto_const_nhds

/-- Spatial dominated convergence for the actual weighted endpoint means. -/
theorem dgSmoothMean_tendsto {n : ℕ} {O : Set (Space n)} {J : Set ℝ} (hO : IsOpen O)
    {u : Point n → ℝ} (hu : ContinuousOn u (O ×ˢ J))
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) (σ k : ℝ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hlim : Tendsto ε atTop (𝓝 0)) {t : ℝ} (ht : t ∈ J) :
    Tendsto (fun j => ∫ x in O, φ x*dgSmoothPos (ε j) (σ*u (x,t)-k)) atTop
      (𝓝 (dgTruncationMean O φ σ k u t)) := by
  have hus : ContinuousOn (fun x => u (x,t)) O :=
    hu.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx,ht⟩)
  have hw : ContinuousOn (fun x => σ*u (x,t)-k) O := (continuousOn_const.mul hus).sub continuousOn_const
  have hv : ContinuousOn (fun x => dgTruncation σ k u (x,t)) O := dgPositivePart_lipschitz.continuous.comp_continuousOn hw
  have hdom : Integrable (fun x => φ x*dgTruncation σ k u (x,t)) (volume.restrict O) := by
    apply dg_integrable_spatial hO hcφ hφO (hφ.continuous.continuousOn.mul hv)
    intro x _ hx
    change φ x*dgTruncation σ k u (x,t) = 0
    rw [image_eq_zero_of_notMem_tsupport hx]; exact zero_mul _
  apply tendsto_integral_of_dominated_convergence (fun x => φ x*dgTruncation σ k u (x,t))
  · intro j
    exact (hφ.continuous.continuousOn.mul ((dgSmoothPos_contDiff (ε j)).continuous.comp_continuousOn hw)).aestronglyMeasurable hO.measurableSet
  · exact hdom
  · intro j
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hφ0 x) (dgSmoothPos_bounds (hε j) _).1)]
    exact mul_le_mul_of_nonneg_left (dgSmoothPos_bounds (hε j) _).2 (hφ0 x)
  · apply Filter.Eventually.of_forall
    intro x
    exact (dgSmoothPos_tendsto hε hlim (σ*u (x,t)-k)).const_mul (φ x)

/-- The PDE and the proved Caccioppoli theorem provide a single genuine L¹
majorant for the full mean density and every smooth convex approximation. -/
theorem dgTruncationMean_dominated {n : ℕ} (hn : 0 < n)
    {ν L D F : ℝ} (hν : 0 < ν) (hνL : ν ≤ L) (hD : 0 ≤ D) (hF : 0 ≤ F)
    {x₀ : Space n} {R l r s t : ℝ} (hR : 0 < R) (hls : l < s) (hst : s < t) (htr : t ≤ r)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields (Metric.ball x₀ R ×ˢ Ioo l r) A c f u)
    (hpde : ClassicalDivEq (Metric.ball x₀ R ×ˢ Ioo l r) A c f u)
    (hb : DGUniformBounds (Metric.ball x₀ R ×ˢ Ioo l r) A c f ν L D F)
    (hu : ContinuousOn u (Metric.ball x₀ R ×ˢ Icc s t))
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ Metric.ball x₀ R) (hφ0 : ∀ x, 0 ≤ φ x)
    {σ k : ℝ} (hσ : DGSign σ) :
    ∃ W : Point n → ℝ, Integrable W (productVolume (Metric.ball x₀ R) (Ioo s t)) ∧
      Integrable (dgTruncationMeanDensity A c φ F σ k u) (productVolume (Metric.ball x₀ R) (Ioo s t)) ∧
      (∀ᵐ z ∂productVolume (Metric.ball x₀ R) (Ioo s t), ‖dgTruncationMeanDensity A c φ F σ k u z‖ ≤ W z) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᵐ z ∂productVolume (Metric.ball x₀ R) (Ioo s t),
        ‖dgSmoothMeanDensity A c φ F ε σ k u z‖ ≤ W z := by
  let O := Metric.ball x₀ R
  let U := O ×ˢ Ioo l r
  let V := O ×ˢ Ioo s t
  let μ := productVolume O (Ioo s t)
  have hO : IsOpen O := Metric.isOpen_ball
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hV : IsOpen V := hO.prod isOpen_Ioo
  have hVU : V ⊆ U := by
    intro z hz
    exact ⟨hz.1,hls.trans hz.2.1,hz.2.2.trans_le htr⟩
  obtain ⟨χ,hχ,hcχ,hχO,hχrange,hχone⟩ := dg_exists_spatial_plateau hO hcφ hφO
  have hζ : DGSpatialCutoff O s t (fun z => χ z.1) := by
    refine ⟨hχ.comp contDiff_fst,fun z _ => hχrange z.1,tsupport χ,hcχ,hχO,?_⟩
    intro z _ hz
    exact image_eq_zero_of_notMem_tsupport hz
  obtain ⟨C,hC,hest⟩ := dgTruncation_caccioppoli n hn ν L D hν hνL hD
  have henergy := hest F hF x₀ R l r s t hR hls hst htr A c f u (fun z => χ z.1)
    hf hpde hb hu hζ σ k hσ
  have hE : Integrable (dgTruncationEnergyDensity σ k u (fun z => χ z.1)) μ := henergy.1
  let W := dgMeanMajorant χ φ L D F σ k u
  have hW : Integrable W μ := dgMeanMajorant_integrable hO (hf.2.2.2.mono hVU) hχ
    (fun x => (hχrange x).1) hφ hcφ hφO hφ0 hE
  have hmem : ∀ᵐ z ∂μ, z ∈ V := by
    change ∀ᵐ z ∂productVolume O (Ioo s t), z ∈ V
    rw [dg_productVolume_eq_restrict]
    exact ae_restrict_mem hV.measurableSet
  have hGm : AEStronglyMeasurable (dgTruncationMeanDensity A c φ F σ k u) μ := by
    rw [show μ = volume.restrict V from dg_productVolume_eq_restrict O _]
    exact (dgTruncationMeanDensity_aestronglyMeasurable hU hf hφ F σ k).mono_measure
      (Measure.restrict_mono hVU le_rfl)
  have hGbound : ∀ᵐ z ∂μ, ‖dgTruncationMeanDensity A c φ F σ k u z‖ ≤ W z := by
    filter_upwards [hmem] with z hz
    rw [Real.norm_eq_abs]
    exact (dgMeanMajorant_dominates hD hF hb (fun x => (hχrange x).1) hχone hφ0 (hVU hz)).1
  refine ⟨W,hW,hW.mono' hGm hGbound,hGbound,?_⟩
  intro ε hε
  filter_upwards [hmem] with z hz
  rw [Real.norm_eq_abs]
  exact (dgMeanMajorant_dominates hD hF hb (fun x => (hχrange x).1) hχone hφ0 (hVU hz)).2 ε hε

/-- Integrable cylinder functions have the expected prefix-integral limit at
the top, proved by dominated convergence through the actual restricted measures. -/
theorem dgCylinderIntegral_prefix_tendsto {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {s t : ℝ} {τ : ℕ → ℝ} (hτ : ∀ j, τ j ≤ t) (hlim : Tendsto τ atTop (𝓝 t))
    {G : Point n → ℝ} (hG : Integrable G (productVolume O (Ioo s t))) :
    Tendsto (fun j => dgCylinderIntegral O s (τ j) G) atTop (𝓝 (dgCylinderIntegral O s t G)) := by
  let μ := productVolume O (Ioo s t)
  let S : ℕ → Set (Point n) := fun j => {z | z.2 < τ j}
  have hc : AECover μ atTop S := by
    refine ⟨?_,fun j => (isOpen_lt continuous_snd continuous_const).measurableSet⟩
    have hmem : ∀ᵐ z ∂μ, z ∈ O ×ˢ Ioo s t := by
      rw [show μ = volume.restrict (O ×ˢ Ioo s t) from dg_productVolume_eq_restrict O _]
      exact ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet
    filter_upwards [hmem] with z hz
    exact hlim.eventually (lt_mem_nhds hz.2.2)
  have hh := hc.integral_tendsto_of_countably_generated hG
  have heq (j : ℕ) : μ.restrict (S j) = productVolume O (Ioo s (τ j)) := dg_prefix_measure (hτ j)
  simpa only [heq,dgCylinderIntegral] using hh

/-- The actual continuous top mean and the integrable density close the final
time face without evaluating any coefficient or solution derivative there. -/
theorem dg_mean_inequality_at_top {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {s t : ℝ} (hst : s < t) {h : ℝ → ℝ} {G : Point n → ℝ}
    (hc : ContinuousOn h (Icc s t)) (hG : Integrable G (productVolume O (Ioo s t)))
    (hp : ∀ τ ∈ Ioo s t, h τ-h s ≤ dgCylinderIntegral O s τ G) :
    h t-h s ≤ dgCylinderIntegral O s t G := by
  let ε : ℕ → ℝ := fun j => (1/2 : ℝ)^(j+1)
  let τ : ℕ → ℝ := fun j => t-(t-s)*ε j
  have hεpos (j : ℕ) : 0 < ε j := pow_pos (by norm_num) _
  have hεlt (j : ℕ) : ε j < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero j)
  have hτ (j : ℕ) : τ j ∈ Ioo s t := by
    have hba : 0 < t-s := sub_pos.mpr hst
    have hp := mul_pos hba (hεpos j)
    have hl := mul_lt_mul_of_pos_left (hεlt j) hba
    dsimp only [τ]
    constructor <;> nlinarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  have heps : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,pow_succ,zero_mul] using hpow.mul_const (1/2 : ℝ)
  have hlim : Tendsto τ atTop (𝓝 t) := by
    simpa only [τ,mul_zero,sub_zero] using tendsto_const_nhds.sub (heps.const_mul (t-s))
  have hlim' : Tendsto τ atTop (𝓝[Icc s t] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim,.of_forall (fun j => Ioo_subset_Icc_self (hτ j))⟩
  have hmean := ((hc t ⟨hst.le,le_rfl⟩).tendsto).comp hlim'
  have hright := dgCylinderIntegral_prefix_tendsto hO (fun j => (hτ j).2.le) hlim hG
  exact le_of_tendsto_of_tendsto (hmean.sub tendsto_const_nhds) hright (.of_forall fun j => hp (τ j) (hτ j))

/-- Positive-part mean subsolution on the full closed time slab. Both
approximation and terminal-time limits use proved actual L¹ majorants. -/
theorem dgTruncation_mean_without_increment {n : ℕ} (hn : 0 < n)
    {ν L D F : ℝ} (hν : 0 < ν) (hνL : ν ≤ L) (hD : 0 ≤ D) (hF : 0 ≤ F)
    {x₀ : Space n} {R l r s t : ℝ} (hR : 0 < R) (hls : l < s) (hst : s < t) (htr : t ≤ r)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields (Metric.ball x₀ R ×ˢ Ioo l r) A c f u)
    (hpde : ClassicalDivEq (Metric.ball x₀ R ×ˢ Ioo l r) A c f u)
    (hb : DGUniformBounds (Metric.ball x₀ R ×ˢ Ioo l r) A c f ν L D F)
    (hu : ContinuousOn u (Metric.ball x₀ R ×ˢ Icc s t))
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ Metric.ball x₀ R) (hφ0 : ∀ x, 0 ≤ φ x)
    {σ k : ℝ} (hσ : DGSign σ) :
    let O := Metric.ball x₀ R
    let h := dgTruncationMean O φ σ k u
    let G := dgTruncationMeanDensity A c φ F σ k u
    Integrable G (productVolume O (Ioo s t)) ∧
      h t-h s ≤ dgCylinderIntegral O s t G ∧ ContinuousOn h (Icc s t) := by
  let O := Metric.ball x₀ R
  let U := O ×ˢ Ioo l r
  let V := O ×ˢ Ioo s t
  let h := dgTruncationMean O φ σ k u
  let G := dgTruncationMeanDensity A c φ F σ k u
  let μ := productVolume O (Ioo s t)
  have hO : IsOpen O := Metric.isOpen_ball
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hV : IsOpen V := hO.prod isOpen_Ioo
  have hVU : V ⊆ U := by
    intro z hz
    exact ⟨hz.1,hls.trans hz.2.1,hz.2.2.trans_le htr⟩
  obtain ⟨W,hW,hG,hGbound,hApproxBound⟩ := dgTruncationMean_dominated hn hν hνL hD hF
    hR hls hst htr hf hpde hb hu hφ hcφ hφO hφ0 hσ
  let ε : ℕ → ℝ := fun j => (1/2 : ℝ)^j
  have hε (j : ℕ) : 0 < ε j := pow_pos (by norm_num) _
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hSmoothMeas (j : ℕ) : AEStronglyMeasurable (dgSmoothMeanDensity A c φ F (ε j) σ k u) μ := by
    rw [show μ = volume.restrict V from dg_productVolume_eq_restrict O _]
    exact ((dgSmoothMeanDensity_continuousOn hU hf hφ F (ε j) σ k).mono hVU).aestronglyMeasurable hV.measurableSet
  have hcont : ContinuousOn h (Icc s t) := dgTruncationMean_continuousOn hO hu hφ.continuous hcφ hφO σ k
  have hinterior (τ : ℝ) (hτ : τ ∈ Ioo s t) : h τ-h s ≤ dgCylinderIntegral O s τ G := by
    have hμpref : productVolume O (Ioo s τ) ≤ μ := by
      change productVolume O (Ioo s τ) ≤ productVolume O (Ioo s t)
      rw [← dg_prefix_measure hτ.2.le]
      exact Measure.restrict_le_self
    have hright : Tendsto (fun j => dgCylinderIntegral O s τ (dgSmoothMeanDensity A c φ F (ε j) σ k u))
        atTop (𝓝 (dgCylinderIntegral O s τ G)) := by
      apply tendsto_integral_of_dominated_convergence W
        (fun j => (hSmoothMeas j).mono_measure hμpref) (hW.mono_measure hμpref)
        (fun j => (hApproxBound (ε j) (hε j)).filter_mono (ae_mono hμpref))
      exact .of_forall (fun z => dgSmoothMeanDensity_tendsto A c φ F σ k u hε hεlim z)
    have hτmean := dgSmoothMean_tendsto hO hu hφ hcφ hφO hφ0 σ k hε hεlim (Ioo_subset_Icc_self hτ)
    have hsmean := dgSmoothMean_tendsto hO hu hφ hcφ hφO hφ0 σ k hε hεlim (show s ∈ Icc s t from ⟨le_rfl,hst.le⟩)
    exact le_of_tendsto_of_tendsto (hτmean.sub hsmean) hright (.of_forall fun j =>
      dgSmoothMean_before_top hO hls hτ.1 hτ.2 htr (hε j) hF hf hpde hb hσ hφ hcφ hφO hφ0)
  exact ⟨hG,dg_mean_inequality_at_top hO hst hcont hG hinterior,hcont⟩

/-- Sharp integral bound for the actual mean density from the actual unweighted
truncation energy. The original elliptic and drift constants are unchanged. -/
theorem dgTruncationMeanDensity_integral_le {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {U : Set (Point n)} (hU : IsOpen U) {s t : ℝ} (hst : s ≤ t)
    (hVU : O ×ˢ Ioo s t ⊆ U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    {ν L D F σ k E : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hf : DGClassicalFields U A c f u) (hb : DGUniformBounds U A c f ν L D F)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x)
    (hEint : Integrable (fun z => dgGradientSq (dgTruncationGradient σ k u z))
      (productVolume O (Ioo s t)))
    (hEb : dgCylinderIntegral O s t (fun z => dgGradientSq (dgTruncationGradient σ k u z)) ≤ E) :
    dgCylinderIntegral O s t (dgTruncationMeanDensity A c φ F σ k u) ≤
      (L*dgTestGradientL2 O φ+D*dgTestL2 O φ)*Real.sqrt E*Real.sqrt (t-s)+
        F*dgTestL1 O φ*(t-s) := by
  let μ := productVolume O (Ioo s t)
  let p : Point n → ℝ := dgTruncationGradientNorm σ k u
  let q1 : Point n → ℝ := fun z => dgSpatialTestGradientNorm φ z.1
  let q2 : Point n → ℝ := fun z => φ z.1
  have hp : AEStronglyMeasurable p μ := by
    rw [show μ = volume.restrict (O ×ˢ Ioo s t) from dg_productVolume_eq_restrict O _]
    exact dgTruncationGradientNorm_aestronglyMeasurable (hO.prod isOpen_Ioo) (hf.2.2.2.mono hVU) σ k
  have hq1 : AEStronglyMeasurable q1 μ :=
    ((dgSpatialTestGradientNorm_continuous hφ).comp continuous_fst).aestronglyMeasurable
  have hq2 : AEStronglyMeasurable q2 μ := (hφ.comp contDiff_fst).continuous.aestronglyMeasurable
  have hp2eq (z : Point n) : (p z)^2 = dgGradientSq (dgTruncationGradient σ k u z) :=
    Real.sq_sqrt (dgGradientSq_nonneg _)
  have hp2 : Integrable (fun z => (p z)^2) μ := hEint.congr (.of_forall fun z => (hp2eq z).symm)
  have htest := dg_test_product_integrable (s := s) (t := t) hO hφ hcφ hφO
  have hq12 : Integrable (fun z => (q1 z)^2) μ := htest.2.2.congr (.of_forall fun z => by
    exact (Real.sq_sqrt (dgGradientSq_nonneg _)).symm)
  obtain ⟨hI1,hB1⟩ := dg_integral_mul_cauchy hp hq1
    (.of_forall fun _ => Real.sqrt_nonneg _) (.of_forall fun _ => Real.sqrt_nonneg _) hp2 hq12
  obtain ⟨hI2,hB2⟩ := dg_integral_mul_cauchy hp hq2
    (.of_forall fun _ => Real.sqrt_nonneg _) (.of_forall fun z => hφ0 z.1) hp2 htest.2.1
  have hP : (∫ z, (p z)^2 ∂μ) ≤ E := by
    simpa only [hp2eq,dgCylinderIntegral,μ] using hEb
  have hQ1 : (∫ z, (q1 z)^2 ∂μ) = (t-s)*(∫ x in O, dgGradientSq (fun i => d φ x i)) := by
    have hh := dg_spatial_time_integral O hst (fun x => dgGradientSq (fun i => d φ x i))
    simpa only [dgCylinderIntegral,q1,dgSpatialTestGradientNorm,Real.sq_sqrt (dgGradientSq_nonneg _)] using hh
  have hQ2 : (∫ z, (q2 z)^2 ∂μ) = (t-s)*(∫ x in O, (φ x)^2) :=
    dg_spatial_time_integral O hst (fun x => (φ x)^2)
  have hQ : (∫ z, q2 z ∂μ) = (t-s)*dgTestL1 O φ := by
    have hh := dg_spatial_time_integral O hst φ
    simpa only [dgCylinderIntegral,q2,μ,dgTestL1,abs_of_nonneg (hφ0 _)] using hh
  have hroot := Real.sqrt_le_sqrt hP
  have htime : 0 ≤ t-s := sub_nonneg.mpr hst
  have hB1' : (∫ z, p z*q1 z ∂μ) ≤ Real.sqrt E*(Real.sqrt (t-s)*dgTestGradientL2 O φ) := by
    apply hB1.trans
    rw [hQ1,Real.sqrt_mul htime]
    exact mul_le_mul_of_nonneg_right hroot (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hB2' : (∫ z, p z*q2 z ∂μ) ≤ Real.sqrt E*(Real.sqrt (t-s)*dgTestL2 O φ) := by
    apply hB2.trans
    rw [hQ2,Real.sqrt_mul htime]
    exact mul_le_mul_of_nonneg_right hroot (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  let W := dgMeanMajorant (fun _ => 1) φ L D F σ k u
  have hWfun : W = fun z => L*(p z*q1 z)+D*(p z*q2 z)+F*q2 z := by
    funext z
    simp only [W,dgMeanMajorant,one_mul,p,q1,q2]
  have hW : Integrable W μ := by
    rw [hWfun]
    exact (((hI1.const_mul L).add (hI2.const_mul D)).add (htest.1.const_mul F)).congr
      (.of_forall fun _ => rfl)
  have hGm : AEStronglyMeasurable (dgTruncationMeanDensity A c φ F σ k u) μ := by
    rw [show μ = volume.restrict (O ×ˢ Ioo s t) from dg_productVolume_eq_restrict O _]
    exact (dgTruncationMeanDensity_aestronglyMeasurable hU hf hφ F σ k).mono_measure
      (Measure.restrict_mono hVU le_rfl)
  have hbound : ∀ᵐ z ∂μ, ‖dgTruncationMeanDensity A c φ F σ k u z‖ ≤ W z := by
    have hm : ∀ᵐ z ∂μ, z ∈ O ×ˢ Ioo s t := by
      rw [show μ = volume.restrict (O ×ˢ Ioo s t) from dg_productVolume_eq_restrict O _]
      exact ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet
    filter_upwards [hm] with z hz
    rw [Real.norm_eq_abs]
    exact (dgMeanMajorant_dominates hD hF hb (fun _ => zero_le_one) (fun _ _ => rfl) hφ0 (hVU hz)).1
  have hG : Integrable (dgTruncationMeanDensity A c φ F σ k u) μ := hW.mono' hGm hbound
  have hle : (∫ z, dgTruncationMeanDensity A c φ F σ k u z ∂μ) ≤ ∫ z, W z ∂μ :=
    integral_mono_ae hG hW (hbound.mono fun z hz => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hz))
  have hL : 0 ≤ L := hb.1.1.le.trans hb.1.2.1
  calc
    _ ≤ ∫ z, W z ∂μ := hle
    _ = L*(∫ z, p z*q1 z ∂μ)+D*(∫ z, p z*q2 z ∂μ)+F*(∫ z, q2 z ∂μ) := by
      rw [hWfun]
      have hq2i : Integrable q2 μ := htest.1
      have hh0 := integral_add ((hI1.const_mul L).add (hI2.const_mul D)) (hq2i.const_mul F)
      have hh1 := integral_add (hI1.const_mul L) (hI2.const_mul D)
      simp only [Pi.add_apply] at hh0 hh1
      rw [hh0,hh1]
      simp only [integral_const_mul]
    _ ≤ L*(Real.sqrt E*(Real.sqrt (t-s)*dgTestGradientL2 O φ))+
        D*(Real.sqrt E*(Real.sqrt (t-s)*dgTestL2 O φ))+F*((t-s)*dgTestL1 O φ) := by
      rw [hQ]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB1' hL)
        (mul_le_mul_of_nonneg_left hB2' hD)) le_rfl
    _ = _ := by ring

/-- The full original mean interface: actual density integrability, closed-slab
subsolution inequality and continuity, and the exact square-root time increment. -/
theorem dgTruncation_mean : DGTruncationMeanGap := by
  intro n hn ν L D F hν hνL hD hF x₀ R l r s t hR hls hst htr A c f u φ
  dsimp only
  intro hf hpde hb hu hφ hcφ hφO hφ0 σ k hσ
  obtain ⟨hG,hmean,hcont⟩ := dgTruncation_mean_without_increment hn hν hνL hD hF
    hR hls hst htr hf hpde hb hu hφ hcφ hφO hφ0 hσ
  refine ⟨hG,hmean,hcont,?_⟩
  intro E hE hEint hEb
  apply hmean.trans
  apply dgTruncationMeanDensity_integral_le Metric.isOpen_ball
    (Metric.isOpen_ball.prod isOpen_Ioo) hst.le ?_ hD hF hf hb hφ hcφ hφO hφ0 hEint hEb
  intro z hz
  exact ⟨hz.1,hls.trans hz.2.1,hz.2.2.trans_le htr⟩

end Yau.LeafProofs.L16Aux
