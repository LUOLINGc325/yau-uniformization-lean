import Yau.LeafProofs.L19EndpointEnergySupport
import Yau.LeafProofs.L19OrthonormalTrace

/-! A genuine lower support for the continuous distance cutoff. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def distanceCutoff (g : SmoothMetric M) (x : M.Carrier) (R : ℝ) (y : M.Carrier) : ℝ :=
  max 0 (1 - inducedDistance g.form x y ^ 2 / R ^ 2) ^ 2

theorem distanceCutoff_continuous (g : SmoothMetric M) (x : M.Carrier) (R : ℝ) :
    Continuous (distanceCutoff g x R) := by
  exact (continuous_const.max
    (continuous_const.sub ((continuous_distFrom g x).pow 2 |>.div_const (R ^ 2)))).pow 2

theorem distanceCutoff_nonneg (g : SmoothMetric M) (x : M.Carrier) (R : ℝ) (y : M.Carrier) :
    0 ≤ distanceCutoff g x R y := sq_nonneg _

theorem distanceCutoff_le_one (g : SmoothMetric M) (x : M.Carrier) (R : ℝ) (y : M.Carrier) :
    distanceCutoff g x R y ≤ 1 := by
  have ha : 1 - inducedDistance g.form x y ^ 2 / R ^ 2 ≤ 1 :=
    sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hb : max 0 (1 - inducedDistance g.form x y ^ 2 / R ^ 2) ≤ 1 := max_le zero_le_one ha
  have hc := le_max_left (0 : ℝ) (1 - inducedDistance g.form x y ^ 2 / R ^ 2)
  dsimp only [distanceCutoff]
  nlinarith

theorem distanceCutoff_center (g : SmoothMetric M) (x : M.Carrier) (R : ℝ) :
    distanceCutoff g x R x = 1 := by
  dsimp only [distanceCutoff]
  rw [show inducedDistance g.form x x = 0 from g.induced_distance_eq_zero.mpr rfl]
  norm_num

theorem distanceCutoff_pos_iff (g : SmoothMetric M) (x y : M.Carrier)
    {R : ℝ} (hR : 0 < R) : 0 < distanceCutoff g x R y ↔ inducedDistance g.form x y < R := by
  have hr := g.induced_distance_nonneg x y
  have hR2 := sq_pos_of_pos hR
  constructor
  · intro h
    by_contra h'
    have hs : R ^ 2 ≤ inducedDistance g.form x y ^ 2 :=
      (sq_le_sq₀ hR.le hr).mpr (le_of_not_gt h')
    have hd : 1 - inducedDistance g.form x y ^ 2 / R ^ 2 ≤ 0 := by
      linarith [(one_le_div hR2).mpr hs]
    simp only [distanceCutoff, max_eq_left hd, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at h
    exact lt_irrefl _ h
  · intro hy
    have hs : inducedDistance g.form x y ^ 2 < R ^ 2 := (sq_lt_sq₀ hr hR.le).mpr hy
    have hd : 0 < 1 - inducedDistance g.form x y ^ 2 / R ^ 2 :=
      sub_pos.mpr ((div_lt_one hR2).mpr hs)
    simpa only [distanceCutoff, max_eq_right hd.le] using sq_pos_of_pos hd

def cutoffProfile (R t : ℝ) : ℝ := (1 - t / R ^ 2) ^ 2

theorem cutoffProfile_contDiff (R : ℝ) : ContDiff ℝ ∞ (cutoffProfile R) := by
  exact (contDiff_const.sub (contDiff_id.div_const (R ^ 2))).pow 2

theorem cutoffProfile_hasDerivAt (R t : ℝ) :
    HasDerivAt (cutoffProfile R) (-2 * (1 - t / R ^ 2) / R ^ 2) t := by
  have hd := (((hasDerivAt_const t (1 : ℝ)).sub
    ((hasDerivAt_id t).div_const (R ^ 2))).pow 2)
  simp only [Pi.sub_apply, Pi.div_apply, id_eq, Nat.cast_ofNat, pow_one,
    Nat.reduceSub] at hd
  convert hd using 1
  · rfl
  · ring

theorem cutoffProfile_deriv (R t : ℝ) :
    deriv (cutoffProfile R) t = -2 * (1 - t / R ^ 2) / R ^ 2 :=
  (cutoffProfile_hasDerivAt R t).deriv

theorem cutoffProfile_secondDeriv (R t : ℝ) :
    deriv (deriv (cutoffProfile R)) t = 2 / (R ^ 2) ^ 2 := by
  have heq : deriv (cutoffProfile R) = fun s => -2 * (1 - s / R ^ 2) / R ^ 2 :=
    funext (cutoffProfile_deriv R)
  rw [heq]
  have hd := (((hasDerivAt_const t (1 : ℝ)).sub
    ((hasDerivAt_id t).div_const (R ^ 2))).const_mul (-2) |>.div_const (R ^ 2))
  simp only [Pi.sub_apply, Pi.div_apply, id_eq, Pi.mul_apply] at hd
  convert hd.deriv using 1 <;> ring

theorem continuousAt_of_chart_continuousAt {F : M.Carrier → ℝ} (q : M.Carrier)
    (hF : ContinuousAt (F ∘ chartInv q) (chartPt q q)) : ContinuousAt F q := by
  have hc := hF.comp (continuousAt_extChartAt (I := ComplexModel n) q)
  apply hc.congr
  filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) q).mem_nhds
    (mem_extChartAt_source q)] with y hy
  exact congrArg F ((extChartAt (ComplexModel n) q).left_inv hy)

/-- The genuine midpoint/center support yields a local C² cutoff with its
physical frame energy and Laplacian bounds. -/
theorem exists_distanceCutoff_lower_support (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef) (x q : M.Carrier)
    {R : ℝ} (hR : 0 < R) (hq : inducedDistance g.form x q < R) :
    letI := underlyingRealTangentNormedAddCommGroup g.form q
    letI := underlyingRealTangentInnerProductSpace g.form q
    ∃ η : M.Carrier → ℝ,
      ∃ b : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) q),
      ContDiffAt ℝ 2 (η ∘ chartInv q) (chartPt q q) ∧
      η q = distanceCutoff g x R q ∧
      (∀ᶠ y in 𝓝 q, η y ≤ distanceCutoff g x R y) ∧
      0 < η q ∧ η q ≤ 1 ∧
      endpointFrameGradientSq q b (η ∘ chartInv q) (chartPt q q) ≤
        16 / R ^ 2 * η q ∧
      -(16 * (n : ℝ)) / R ^ 2 ≤
        endpointFrameHessianTrace g q b (η ∘ chartInv q) (chartPt q q) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form q
  letI := underlyingRealTangentInnerProductSpace g.form q
  obtain ⟨F, b, hF, hval, hupper, hgrad, htrace⟩ :=
    exists_realDistanceSquareUpperSupport g hK hRic x q
  let r := inducedDistance g.form x q
  let a := 1 - r ^ 2 / R ^ 2
  let η : M.Carrier → ℝ := cutoffProfile R ∘ F
  have hr : 0 ≤ r := g.induced_distance_nonneg x q
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hrR : r ^ 2 < R ^ 2 := (sq_lt_sq₀ hr hR.le).mpr hq
  have ha : 0 < a := by dsimp [a]; exact sub_pos.mpr ((div_lt_one hR2).mpr hrR)
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact sub_le_self _ (div_nonneg (sq_nonneg r) hR2.le)
  have hFq : (F ∘ chartInv q) (chartPt q q) = r ^ 2 := by
    simpa only [Function.comp_apply, chartInv, chartPt,
      (extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q)] using hval
  have hηq : η q = a ^ 2 := by dsimp [η, cutoffProfile, a]; rw [hval]
  have hη : ContDiffAt ℝ 2 (η ∘ chartInv q) (chartPt q q) :=
    ((cutoffProfile_contDiff R).contDiffAt.of_le (by simp)).comp _ hF
  have hnear : ∀ᶠ y in 𝓝 q, F y < R ^ 2 :=
    (continuousAt_of_chart_continuousAt q hF.continuousAt).eventually
      (Iio_mem_nhds (by simpa only [hval] using hrR))
  refine ⟨η, b, hη, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hηq]
    change a ^ 2 = max 0 a ^ 2
    rw [max_eq_right ha.le]
  · filter_upwards [hnear, hupper] with y hy hFy
    have hA : 0 < 1 - F y / R ^ 2 := sub_pos.mpr ((div_lt_one hR2).mpr hy)
    have hle : 1 - F y / R ^ 2 ≤ 1 - inducedDistance g.form x y ^ 2 / R ^ 2 := by
      exact sub_le_sub_left ((div_le_div_iff_of_pos_right hR2).mpr hFy) 1
    have hB : 0 ≤ 1 - inducedDistance g.form x y ^ 2 / R ^ 2 := le_trans hA.le hle
    dsimp only [η, Function.comp_apply, cutoffProfile, distanceCutoff]
    rw [max_eq_right hB]
    exact (sq_le_sq₀ hA.le hB).mpr hle
  · rw [hηq]; exact sq_pos_of_pos ha
  · rw [hηq]; nlinarith
  · have hg := endpointFrameGradientSq_scalar_comp q b
      (hF.differentiableAt (by norm_num))
      ((cutoffProfile_contDiff R).differentiable (by simp) _)
    change endpointFrameGradientSq q b (cutoffProfile R ∘ (F ∘ chartInv q))
      (chartPt q q) ≤ _
    rw [hg, cutoffProfile_deriv, hFq, hgrad, hηq]
    change (-2 * a / R ^ 2) ^ 2 * (4 * r ^ 2) ≤ 16 / R ^ 2 * a ^ 2
    have hnum : 16 * a ^ 2 * r ^ 2 ≤ 16 * a ^ 2 * R ^ 2 :=
      mul_le_mul_of_nonneg_left hrR.le (by positivity)
    have hdiv := (div_le_div_iff_of_pos_right (sq_pos_of_pos hR2)).mpr hnum
    convert hdiv using 1 <;> field_simp <;> ring
  · have ht := endpointFrameHessianTrace_scalar_comp g q b hF
      ((cutoffProfile_contDiff R).contDiffAt.of_le (by simp))
    change _ ≤ endpointFrameHessianTrace g q b (cutoffProfile R ∘ (F ∘ chartInv q))
      (chartPt q q)
    rw [ht, cutoffProfile_deriv, cutoffProfile_secondDeriv, hFq, hgrad]
    have hdnonpos : -2 * a / R ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) hR2.le
    have hmul := mul_le_mul_of_nonpos_left htrace hdnonpos
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hsecond : 0 ≤ 2 / (R ^ 2) ^ 2 * (4 * r ^ 2) := by positivity
    push_cast at hmul
    change _ ≤ (-2 * a / R ^ 2) * _ + _
    have hbase : -(16 * (n : ℝ)) / R ^ 2 ≤ (-2 * a / R ^ 2) * (8 * (n : ℝ)) := by
      calc
        _ ≤ (-16 * a * (n : ℝ)) / R ^ 2 := by
          apply (div_le_div_iff_of_pos_right hR2).2
          nlinarith
        _ = _ := by ring
    linarith

/-- The same genuine support in the actual coordinate operators used by
CD and the logarithmic heat evolution. -/
theorem exists_distanceCutoff_lower_support_chart (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef) (x q : M.Carrier)
    {R : ℝ} (hR : 0 < R) (hq : inducedDistance g.form x q < R) :
    ∃ η : M.Carrier → ℝ,
      ContDiffAt ℝ 2 (η ∘ chartInv q) (chartPt q q) ∧
      η q = distanceCutoff g x R q ∧
      (∀ᶠ y in 𝓝 q, η y ≤ distanceCutoff g x R y) ∧
      0 < η q ∧ η q ≤ 1 ∧
      chartGradientPair g.form q (η ∘ chartInv q) (η ∘ chartInv q) (chartPt q q) ≤
        16 / R ^ 2 * η q ∧
      -(8 * (n : ℝ)) / R ^ 2 ≤
        chartRealLaplacian g.form q (η ∘ chartInv q) (chartPt q q) / 2 := by
  obtain ⟨η, b, hη, hval, hnear, hpos, hone, hgrad, htrace⟩ :=
    exists_distanceCutoff_lower_support g hK hRic x q hR hq
  refine ⟨η, hη, hval, hnear, hpos, hone, ?_, ?_⟩
  · rw [chartGradientPair_self_eq_orthonormal_sum g.form q _ b]
    exact hgrad
  · have ht : -(16 * (n : ℝ)) / R ^ 2 ≤
        chartRealLaplacian g.form q (η ∘ chartInv q) (chartPt q q) := by
      rw [chartRealLaplacian_eq_orthonormal_covHessian g.form q hη b]
      exact htrace
    have ht' : 2 * (-(8 * (n : ℝ)) / R ^ 2) ≤
        chartRealLaplacian g.form q (η ∘ chartInv q) (chartPt q q) := by
      convert ht using 1 <;> ring
    linarith

end Yau.LeafProofs.L19Aux
