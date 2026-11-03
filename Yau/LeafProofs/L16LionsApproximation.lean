import Yau.LeafProofs.L16TimeReflection

open MeasureTheory Filter Set
open scoped Topology ContDiff Convolution
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16LionsApproximation
open Yau.LeafProofs.L16TimeReflection Yau.LeafProofs.L16HilbertTimeRegularization

def temporalBump : ContDiffBump (0 : ℝ) := ⟨1/2,1,by norm_num,by norm_num⟩
def temporalMollifier : ℝ → ℝ := temporalBump.normed volume

theorem temporalMollifier_smooth : ContDiff ℝ ∞ temporalMollifier :=
  temporalBump.contDiff_normed

theorem temporalMollifier_compact : HasCompactSupport temporalMollifier :=
  temporalBump.hasCompactSupport_normed

theorem temporalMollifier_nonneg (r : ℝ) : 0 ≤ temporalMollifier r :=
  temporalBump.nonneg_normed r

theorem temporalMollifier_integral : (∫ r, temporalMollifier r) = 1 :=
  temporalBump.integral_normed

theorem temporalMollifier_support : tsupport temporalMollifier ⊆ Icc (-1) 1 := by
  rw [temporalMollifier,temporalBump.tsupport_normed_eq]
  intro r hr
  simpa only [temporalBump,Metric.mem_closedBall,Real.dist_eq,sub_zero,abs_le,mem_Icc] using hr

def temporalScale (T : ℝ) (k : ℕ) : ℝ := min 1 (T/4)/((k:ℝ)+1)

theorem temporalScale_pos {T : ℝ} (hT : 0 < T) (k : ℕ) : 0 < temporalScale T k := by
  dsimp only [temporalScale]
  positivity

theorem temporalScale_le_min {T : ℝ} (hT : 0 < T) (k : ℕ) :
    temporalScale T k ≤ min 1 (T/4) := by
  apply (div_le_iff₀ (by positivity : 0 < (k:ℝ)+1)).mpr
  have hC : 0 ≤ min (1 : ℝ) (T/4) := le_min (by norm_num) (by positivity)
  have hProd : 0 ≤ min (1 : ℝ) (T/4)*(k:ℝ) := mul_nonneg hC (Nat.cast_nonneg k)
  nlinarith

theorem temporalScale_le_one {T : ℝ} (hT : 0 < T) (k : ℕ) : temporalScale T k ≤ 1 :=
  (temporalScale_le_min hT k).trans (min_le_left _ _)

theorem temporalScale_lt_T {T : ℝ} (hT : 0 < T) (k : ℕ) : temporalScale T k < T :=
  ((temporalScale_le_min hT k).trans (min_le_right _ _)).trans_lt (by linarith)

theorem temporalScale_tendsto (T : ℝ) : Tendsto (temporalScale T) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => min 1 (T/4)/((k:ℝ)+1)) atTop (𝓝 0)
  simpa only [mul_one_div,mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min 1 (T/4))

theorem rescaled_temporalMollifier_support {ε : ℝ} (hε : 0 < ε) :
    tsupport (L03.rescaledFriedrichsMollifier temporalMollifier ε) ⊆ Icc (-ε) ε := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hρ : temporalMollifier (ε⁻¹ • s) ≠ 0 := by
    intro hz
    exact hs (by simp only [L03.rescaledFriedrichsMollifier,hz,mul_zero])
  have h := temporalMollifier_support (subset_tsupport _ hρ)
  simp only [smul_eq_mul] at h
  have hLeft := mul_le_mul_of_nonneg_left h.1 hε.le
  have hRight := mul_le_mul_of_nonneg_left h.2 hε.le
  simp only [mul_neg_one,mul_one,← mul_assoc,mul_inv_cancel₀ hε.ne',one_mul] at hLeft hRight
  exact ⟨hLeft,hRight⟩

def temporalKernel (T : ℝ) (k : ℕ) : ℝ → ℝ :=
  L03.rescaledFriedrichsMollifier temporalMollifier (temporalScale T k)

theorem temporalKernel_smooth (T : ℝ) (k : ℕ) : ContDiff ℝ ∞ (temporalKernel T k) :=
  L03.rescaledFriedrichsMollifier_contDiff_top _ _ temporalMollifier_smooth

theorem temporalKernel_compact {T : ℝ} (hT : 0 < T) (k : ℕ) :
    HasCompactSupport (temporalKernel T k) :=
  L03.rescaledFriedrichsMollifier_compact _ (temporalScale_pos hT k).ne' temporalMollifier_compact

theorem temporalKernel_nonneg {T : ℝ} (hT : 0 < T) (k : ℕ) (r : ℝ) :
    0 ≤ temporalKernel T k r := by
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (temporalScale_pos hT k).le _))
    (temporalMollifier_nonneg _)

theorem temporalKernel_integral {T : ℝ} (hT : 0 < T) (k : ℕ) :
    (∫ r, temporalKernel T k r) = 1 := by
  rw [temporalKernel,L03.rescaledFriedrichsMollifier_integral volume _ (temporalScale_pos hT k)]
  exact temporalMollifier_integral

section Banach
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def reflectedSmooth (T : ℝ) (U : ℝ → V) (k : ℕ) : ℝ → V :=
  temporalKernel T k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] evenTimeReflection T U

def reflectedDualSmooth (T : ℝ) (R : ℝ → E) (k : ℕ) : ℝ → E :=
  temporalKernel T k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] oddTimeReflection T R

theorem reflectedSmooth_contDiff {T : ℝ} (hT : 0 < T) {U : ℝ → V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T))) (k : ℕ) :
    ContDiff ℝ ∞ (reflectedSmooth T U k) :=
  mollify_contDiff _ (temporalKernel_smooth T k) (temporalKernel_compact hT k) _
    (evenTimeReflection_memLp hU)

theorem reflectedDualSmooth_contDiff {T : ℝ} (hT : 0 < T) {R : ℝ → E}
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T))) (k : ℕ) :
    ContDiff ℝ ∞ (reflectedDualSmooth T R k) :=
  mollify_contDiff _ (temporalKernel_smooth T k) (temporalKernel_compact hT k) _
    (oddTimeReflection_memLp hR)

theorem reflectedSmooth_memLp {T : ℝ} (hT : 0 < T) {U : ℝ → V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T))) (k : ℕ) :
    MemLp (reflectedSmooth T U k) 2 volume :=
  (mollify_L2_bound _ (temporalKernel_nonneg hT k) (temporalKernel_integral hT k) _
    (evenTimeReflection_memLp hU) (evenTimeReflection_compact T U)).1

theorem reflectedDualSmooth_memLp {T : ℝ} (hT : 0 < T) {R : ℝ → E}
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T))) (k : ℕ) :
    MemLp (reflectedDualSmooth T R k) 2 volume :=
  (mollify_L2_bound _ (temporalKernel_nonneg hT k) (temporalKernel_integral hT k) _
    (oddTimeReflection_memLp hR) (oddTimeReflection_compact T R)).1

/-- Smooth approximants satisfy the actual operator equation at every closed-slab time. -/
theorem reflectedSmooth_derivative (L : V →L[ℝ] E) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → E}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv φ t • L (U t)) = -(∫ t in Ioo 0 T, φ t • R t))
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    L (deriv (reflectedSmooth T U k) t) = reflectedDualSmooth T R k t := by
  exact localWeakDerivative_mollify _ isOpen_Ioo L _ _
    (evenTimeReflection_memLp hU) (evenTimeReflection_compact T U)
    (oddTimeReflection_memLp hR) (oddTimeReflection_compact T R)
    (reflected_operator_weak_derivative L hT hU hR hw)
    _ (temporalKernel_smooth T k) (temporalKernel_compact hT k) t
    (translated_kernel_support_subset (temporalScale_lt_T hT k)
      (rescaled_temporalMollifier_support (temporalScale_pos hT k)) ht)

/-- Restriction of an actual full-line strong L² approximation preserves its
    integral convergence, with every error function genuinely integrable. -/
theorem restrict_L2_tendsto_of_full {W U : ℝ → V} {Z : ℕ → ℝ → V} {T : ℝ}
    (hW : MemLp W 2 volume) (hZ : ∀ k, MemLp (Z k) 2 volume)
    (hEq : EqOn W U (Ioo 0 T))
    (hLim : Tendsto (fun k => ∫ r, ‖Z k r-W r‖^2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ r in Ioo 0 T, ‖Z k r-U r‖^2) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_ hLim
  apply Filter.Eventually.of_forall
  intro k
  have hi : Integrable (fun r => ‖Z k r-W r‖^2) :=
    (memLp_two_iff_integrable_sq_norm (hZ k |>.sub hW).aestronglyMeasurable).mp (hZ k |>.sub hW)
  have hIntEq : (∫ r in Ioo 0 T, ‖Z k r-U r‖^2) = ∫ r in Ioo 0 T, ‖Z k r-W r‖^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [hEq hr]
  rw [hIntEq]
  exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun _ => sq_nonneg _)

theorem reflectedSmooth_L2_tendsto {T : ℝ} (hT : 0 < T) {U : ℝ → V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T))) :
    Tendsto (fun k => ∫ r in Ioo 0 T, ‖reflectedSmooth T U k r-U r‖^2) atTop (𝓝 0) := by
  apply restrict_L2_tendsto_of_full (evenTimeReflection_memLp hU) (reflectedSmooth_memLp hT hU)
    (fun _ hr => evenTimeReflection_eq_on_original hr)
  exact mollify_L2_tendsto _ (temporalMollifier_smooth.of_le (by simp))
    temporalMollifier_compact temporalMollifier_nonneg temporalMollifier_integral
    (temporalScale T) (temporalScale_pos hT) (temporalScale_le_one hT) (temporalScale_tendsto T)
    _ (evenTimeReflection_memLp hU) (evenTimeReflection_compact T U)

theorem reflectedDualSmooth_L2_tendsto {T : ℝ} (hT : 0 < T) {R : ℝ → E}
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T))) :
    Tendsto (fun k => ∫ r in Ioo 0 T, ‖reflectedDualSmooth T R k r-R r‖^2) atTop (𝓝 0) := by
  apply restrict_L2_tendsto_of_full (oddTimeReflection_memLp hR) (reflectedDualSmooth_memLp hT hR)
    (fun _ hr => oddTimeReflection_eq_on_original hr)
  exact mollify_L2_tendsto _ (temporalMollifier_smooth.of_le (by simp))
    temporalMollifier_compact temporalMollifier_nonneg temporalMollifier_integral
    (temporalScale T) (temporalScale_pos hT) (temporalScale_le_one hT) (temporalScale_tendsto T)
    _ (oddTimeReflection_memLp hR) (oddTimeReflection_compact T R)

end Banach

end Yau.LeafProofs.L16LionsApproximation
