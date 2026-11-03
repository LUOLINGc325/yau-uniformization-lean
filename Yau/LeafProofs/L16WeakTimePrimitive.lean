import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith

/-! Banach valued weak time primitives, with both endpoint terms in scalar-test integration
by parts. Scalar absolute continuity is used only after applying a continuous linear functional. -/

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology ContDiff
set_option maxHeartbeats 800000
namespace Yau.L16WeakTimePrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual smooth compactly supported time tests on an open interval. -/
def TimeTest (T : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 T

omit [CompleteSpace E] in
private theorem dual_ext {x y : E} (h : ∀ L : E →L[ℝ] ℝ, L x = L y) : x = y := by
  obtain ⟨L, -, hL⟩ := exists_dual_vector'' ℝ (x - y)
  have hL' : L (x - y) = ‖x - y‖ := by simpa using hL
  have : ‖x - y‖ = 0 := by rw [← hL', map_sub, h L, sub_self]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Endpoint-retaining integration by parts for a genuine Bochner primitive and a C¹ scalar test. -/
theorem primitive_scalar_test_ibp {a b : ℝ} {r : ℝ → E}
    (hr : IntervalIntegrable r volume a b) (c : E) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    (∫ t in a..b, deriv φ t • (c + ∫ s in a..t, r s)) =
      φ b • (c + ∫ s in a..b, r s) - φ a • c - ∫ t in a..b, φ t • r t := by
  apply dual_ext
  intro L
  have hp := intervalIntegral.continuousOn_primitive_interval' hr (a := a) (by simp)
  have hrep : ContinuousOn (fun t => c + ∫ s in a..t, r s) (uIcc a b) :=
    continuousOn_const.add hp
  have hleft : IntervalIntegrable (fun t => deriv φ t • (c + ∫ s in a..t, r s))
      volume a b := (hφ.continuous_deriv_one.continuousOn.smul hrep).intervalIntegrable
  have hright : IntervalIntegrable (fun t => φ t • r t) volume a b :=
    hr.continuousOn_smul hφ.continuous.continuousOn
  rw [← L.intervalIntegral_comp_comm hleft, map_sub, map_sub,
    map_smul, map_smul, ← L.intervalIntegral_comp_comm hright]
  simp only [map_smul, smul_eq_mul]
  let p : ℝ → ℝ := fun t => ∫ s in a..t, L (r s)
  have hrL : IntervalIntegrable (fun t => L (r t)) volume a b := ⟨L.integrable_comp hr.1, L.integrable_comp hr.2⟩
  have hpL : ∀ t ∈ uIcc a b, p t = L (∫ s in a..t, r s) := by
    intro t ht
    exact L.intervalIntegral_comp_comm (hr.mono_set (uIcc_subset_uIcc_left ht))
  have hg : AbsolutelyContinuousOnInterval (fun t => L c + p t) a b :=
    (contDiff_const.contDiffOn.absolutelyContinuousOnInterval).add
      (hrL.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hφac := hφ.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  have hder : ∀ᵐ t, t ∈ uIcc a b → deriv (fun t => L c + p t) t = L (r t) := by
    filter_upwards [hrL.ae_hasDerivAt_integral] with t ht htab
    exact ((ht htab a (by simp)).const_add (L c)).deriv
  have hid := hφac.integral_mul_deriv_eq_deriv_mul hg
  have hdeq : (∫ t in a..b, φ t * deriv (fun t => L c + p t) t) =
      ∫ t in a..b, φ t * L (r t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hder] with t ht htab
    rw [ht (uIoc_subset_uIcc htab)]
  rw [hdeq] at hid
  have hpeq : (∫ t in a..b, deriv φ t * L (c + ∫ s in a..t, r s)) =
      ∫ t in a..b, deriv φ t * (L c + p t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [map_add, hpL t ht]
  rw [hpeq]
  have pa : p a = 0 := by simp [p]
  have pb := hpL b (by simp)
  rw [pa, pb, add_zero] at hid
  simp only [map_add] at ⊢
  linarith

private theorem exists_normalized_test {T : ℝ} (hT : 0 < T) :
    ∃ ρ : ℝ → ℝ, TimeTest T ρ ∧ (∫ t, ρ t) = 1 := by
  let B : ContDiffBump (T / 2) := ⟨T / 8, T / 4, by linarith, by linarith⟩
  refine ⟨B.normed volume, ⟨B.contDiff_normed, B.hasCompactSupport_normed, ?_⟩,
    B.integral_normed⟩
  rw [B.tsupport_normed_eq]
  intro t ht
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
  change -(T / 4) ≤ t - T / 2 ∧ t - T / 2 ≤ T / 4 at ht
  constructor <;> linarith

/-- Every zero-integral smooth time test is the derivative of another time test. -/
theorem exists_test_primitive {T : ℝ} {ψ : ℝ → ℝ}
    (hψ : TimeTest T ψ) (hz : (∫ t, ψ t) = 0) :
    ∃ η : ℝ → ℝ, TimeTest T η ∧ deriv η = ψ := by
  let η : ℝ → ℝ := fun t => ∫ s in 0..t, ψ s
  have hd : ∀ t, HasDerivAt η (ψ t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hψ.1.continuous.intervalIntegrable 0 t)
      hψ.1.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hψ.1.continuous.continuousAt
  have hder : deriv η = ψ := funext fun t => (hd t).deriv
  have hη : ContDiff ℝ ∞ η := contDiff_infty_iff_deriv.mpr
    ⟨fun t => (hd t).differentiableAt, by rw [hder]; exact hψ.1⟩
  by_cases hs : (tsupport ψ).Nonempty
  · obtain ⟨a, ha, hamin⟩ := hψ.2.1.exists_isMinOn hs continuousOn_id
    obtain ⟨b, hb, hbmax⟩ := hψ.2.1.exists_isMaxOn hs continuousOn_id
    have ha0 : 0 < a := (hψ.2.2 ha).1
    have hbT : b < T := (hψ.2.2 hb).2
    have hab : a ≤ b := hamin hb
    have hsab : tsupport ψ ⊆ Icc a b := fun t ht => ⟨hamin ht, hbmax ht⟩
    have hηsupp : support η ⊆ Icc a b := by
      intro t ht
      by_contra htab
      rw [mem_support] at ht
      apply ht
      have hor : t < a ∨ b < t := by simpa only [mem_Icc, not_and_or, not_le] using htab
      rcases hor with hta | hbt
      · calc
          η t = ∫ s in 0..t, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro s hs
            dsimp only
            apply image_eq_zero_of_notMem_tsupport
            intro hsp
            have hsa := (hsab hsp).1
            rcases (mem_uIcc.mp hs) with hs | hs <;> linarith
          _ = 0 := intervalIntegral.integral_zero
      · rw [show η t = ∫ s in 0..t, ψ s from rfl,
          intervalIntegral.integral_eq_integral_of_support_subset, hz]
        intro s hs
        have hss := hsab (subset_tsupport ψ hs)
        exact ⟨lt_of_lt_of_le ha0 hss.1, hss.2.trans hbt.le⟩
    have htη : tsupport η ⊆ Icc a b := closure_minimal hηsupp isClosed_Icc
    refine ⟨η, ⟨hη, isCompact_Icc.of_isClosed_subset isClosed_closure htη, ?_⟩, hder⟩
    intro t ht
    have := htη ht
    exact ⟨ha0.trans_le this.1, this.2.trans_lt hbT⟩
  · have hψzero : ψ = 0 := by
      ext t
      apply image_eq_zero_of_notMem_tsupport
      simp [Set.not_nonempty_iff_eq_empty.mp hs]
    refine ⟨η, ⟨hη, ?_, ?_⟩, hder⟩ <;> simp [η, hψzero, HasCompactSupport]

omit [CompleteSpace E] in
private theorem integrableOn_smul_test {T : ℝ} (hT : 0 ≤ T) {q : ℝ → E}
    (hq : IntegrableOn q (Ioo 0 T)) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    IntegrableOn (fun t => φ t • q t) (Ioo 0 T) := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hq).continuousOn_smul
    hφ.continuousOn

omit [CompleteSpace E] in
private theorem test_setIntegral_eq_integral {T : ℝ} {φ : ℝ → ℝ}
    (hφ : tsupport φ ⊆ Ioo 0 T) (q : ℝ → E) :
    (∫ t in Ioo 0 T, φ t • q t) = ∫ t, φ t • q t := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz : φ t = 0 := image_eq_zero_of_notMem_tsupport (fun hp => ht (hφ hp))
  simp [hz]

/-- A genuinely Banach valued distribution with zero time derivative is almost everywhere constant. -/
theorem ae_eq_const_of_weak_derivative_zero {T : ℝ} (hT : 0 < T) {q : ℝ → E}
    (hq : IntegrableOn q (Ioo 0 T))
    (hw : ∀ φ : ℝ → ℝ, TimeTest T φ →
      (∫ t in Ioo 0 T, deriv φ t • q t) = 0) :
    ∃ c : E, ∀ᵐ t ∂volume.restrict (Ioo 0 T), q t = c := by
  obtain ⟨ρ, hρ, hρone⟩ := exists_normalized_test hT
  let c : E := ∫ t in Ioo 0 T, ρ t • q t
  have hρq := integrableOn_smul_test hT.le hq hρ.1.continuous
  have hρint : Integrable ρ := hρ.1.continuous.integrable_of_hasCompactSupport hρ.2.1
  refine ⟨c, ?_⟩
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  have hqa : IntegrableOn (fun t => q t - c) (Ioo 0 T) := hq.sub (integrableOn_const (by simp))
  have heq := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hqa.locallyIntegrableOn ?_
  · filter_upwards [heq] with t ht hmem
    exact sub_eq_zero.mp (ht hmem)
  intro ψ hψsmooth hψcompact hψsupport
  have hψ : TimeTest T ψ := ⟨hψsmooth, hψcompact, hψsupport⟩
  let k : ℝ := ∫ t, ψ t
  let ψ₀ : ℝ → ℝ := fun t => ψ t - k • ρ t
  have hψ₀support : tsupport ψ₀ ⊆ tsupport ψ ∪ tsupport ρ := by
    intro t ht
    rcases tsupport_sub ψ (fun t => k • ρ t) ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr (tsupport_smul_subset_right (fun _ => k) ρ ht)
  have hψ₀compact : HasCompactSupport ψ₀ :=
    (hψcompact.union hρ.2.1).of_isClosed_subset isClosed_closure hψ₀support
  have hψ₀ : TimeTest T ψ₀ := by
    refine ⟨hψsmooth.sub (hρ.1.const_smul k), hψ₀compact, ?_⟩
    intro t ht
    rcases hψ₀support ht with ht | ht
    · exact hψsupport ht
    · exact hρ.2.2 ht
  have hψint : Integrable ψ := hψsmooth.continuous.integrable_of_hasCompactSupport hψcompact
  have hψ₀zero : (∫ t, ψ₀ t) = 0 := by
    change (∫ t, ψ t - k • ρ t) = 0
    have hint : (∫ t, ψ t - k • ρ t) = (∫ t, ψ t) - ∫ t, k • ρ t := by
      simpa only [Pi.smul_apply] using (integral_sub hψint (hρint.smul k))
    rw [hint, integral_smul, hρone]
    simp [k]
  obtain ⟨η, hη, hηder⟩ := exists_test_primitive hψ₀ hψ₀zero
  have hηzero := hw η hη
  have hψq := integrableOn_smul_test hT.le hq hψsmooth.continuous
  have hsplit : (fun t => deriv η t • q t) =
      (fun t => ψ t • q t - k • (ρ t • q t)) := by
    rw [hηder]
    ext t
    simp [ψ₀, sub_smul, smul_smul]
  have hint : (∫ t in Ioo 0 T, ψ t • q t - k • (ρ t • q t)) =
      (∫ t in Ioo 0 T, ψ t • q t) - ∫ t in Ioo 0 T, k • (ρ t • q t) := by
    simpa only [Pi.smul_apply] using (integral_sub hψq (hρq.smul k))
  rw [hsplit, hint, integral_smul] at hηzero
  have hk : (∫ t in Ioo 0 T, ψ t) = k := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (fun hp => ht (hψsupport hp))
  rw [← test_setIntegral_eq_integral hψsupport (fun t => q t - c)]
  simp_rw [smul_sub]
  rw [integral_sub hψq ((hψint.integrableOn).smul_const c), integral_smul_const, hk]
  exact hηzero

omit [CompleteSpace E] in
private theorem intervalIntegral_eq_Ioo {a b : ℝ} (hab : a ≤ b) (g : ℝ → E) :
    (∫ t in a..b, g t) = ∫ t in Ioo a b, g t := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- The actual primitive has weak derivative `r`, without pointwise regularity assumptions on `r`. -/
theorem primitive_weak_derivative {T : ℝ} (hT : 0 < T) {r : ℝ → E}
    (hr : IntegrableOn r (Ioo 0 T)) {φ : ℝ → ℝ} (hφ : TimeTest T φ) :
    (∫ t in Ioo 0 T, deriv φ t • (∫ s in 0..t, r s)) =
      -(∫ t in Ioo 0 T, φ t • r t) := by
  have hφ0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; have := hφ.2.2 h; simp at this)
  have hφT : φ T = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; have := hφ.2.2 h; simp at this)
  have hi := primitive_scalar_test_ibp
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hr) (0 : E)
    (hφ.1.of_le (by simp))
  simp only [zero_add, hφ0, hφT, zero_smul, sub_self, zero_sub] at hi
  simpa only [intervalIntegral_eq_Ioo hT.le] using hi

/-- A Bochner `L¹` function with an `L¹` distributional derivative has a continuous primitive
representative on the entire closed interval. -/
theorem exists_weak_time_primitive {T : ℝ} (hT : 0 < T) {f r : ℝ → E}
    (hf : IntegrableOn f (Ioo 0 T)) (hr : IntegrableOn r (Ioo 0 T))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv φ t • f t) = -(∫ t in Ioo 0 T, φ t • r t)) :
    ∃ c : E,
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), f t = c + ∫ s in 0..t, r s) ∧
      ContinuousOn (fun t => c + ∫ s in 0..t, r s) (Icc 0 T) := by
  have hrI : IntervalIntegrable r volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hr
  let P : ℝ → E := fun t => ∫ s in 0..t, r s
  have hPc : ContinuousOn P (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using
      (intervalIntegral.continuousOn_primitive_interval' hrI (a := 0) (by simp))
  have hPi : IntegrableOn P (Ioo 0 T) := hPc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hq : IntegrableOn (fun t => f t - P t) (Ioo 0 T) := hf.sub hPi
  obtain ⟨c, hc⟩ := ae_eq_const_of_weak_derivative_zero hT hq (by
    intro φ hφ
    have hfφ := integrableOn_smul_test hT.le hf (hφ.1.continuous_deriv (by simp))
    have hPφ := integrableOn_smul_test hT.le hPi (hφ.1.continuous_deriv (by simp))
    simp_rw [smul_sub]
    rw [integral_sub hfφ hPφ, hw φ hφ.1 hφ.2.1 hφ.2.2,
      primitive_weak_derivative hT hr hφ, sub_self])
  refine ⟨c, ?_, continuousOn_const.add hPc⟩
  filter_upwards [hc] with t ht
  have ht' : f t - P t = c := ht
  exact sub_eq_iff_eq_add.mp ht'

omit [CompleteSpace E] in
/-- All closed-interval increments of a Banach primitive are its actual Bochner integrals. -/
theorem primitive_increment {T : ℝ} (hT : 0 < T) {r : ℝ → E}
    (hr : IntegrableOn r (Ioo 0 T)) (c : E) {s t : ℝ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    (c + ∫ u in 0..t, r u) - (c + ∫ u in 0..s, r u) = ∫ u in s..t, r u := by
  have hrI := (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hr
  have hs' : s ∈ uIcc 0 T := by simpa [uIcc_of_le hT.le] using hs
  have ht' : t ∈ uIcc 0 T := by simpa [uIcc_of_le hT.le] using ht
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (hrI.mono_set (uIcc_subset_uIcc_left ht'))
    (hrI.mono_set (uIcc_subset_uIcc_left hs'))

/-- The continuous representative admits the expected derivative almost everywhere. -/
theorem ae_hasDerivAt_primitive {T : ℝ} (hT : 0 < T) {r : ℝ → E}
    (hr : IntegrableOn r (Ioo 0 T)) (c : E) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      HasDerivAt (fun t => c + ∫ s in 0..t, r s) (r t) t := by
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  have hrI := (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hr
  filter_upwards [hrI.ae_hasDerivAt_integral] with t ht hmem
  have htm : t ∈ uIcc 0 T := by
    simpa [uIcc_of_le hT.le] using Ioo_subset_Icc_self hmem
  exact (ht htm 0 (by simp)).const_add c

/-- Integration by parts for the original almost-everywhere function, retaining both traces of
its primitive representative. The test need only be C¹ and need not vanish at either endpoint. -/
theorem weak_scalar_test_ibp {T : ℝ} (hT : 0 < T) {f r : ℝ → E}
    (hr : IntegrableOn r (Ioo 0 T)) (c : E)
    (hc : ∀ᵐ t ∂volume.restrict (Ioo 0 T), f t = c + ∫ s in 0..t, r s)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ t in Ioo 0 T, deriv φ t • f t) =
      φ T • (c + ∫ s in 0..T, r s) - φ 0 • c - ∫ t in Ioo 0 T, φ t • r t := by
  calc
    _ = ∫ t in Ioo 0 T, deriv φ t • (c + ∫ s in 0..t, r s) := by
      apply integral_congr_ae
      filter_upwards [hc] with t ht using congrArg (fun z => deriv φ t • z) ht
    _ = _ := by
      simpa only [intervalIntegral_eq_Ioo hT.le] using
        primitive_scalar_test_ibp
          ((intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hr) c hφ

/-- The complete primitive package, including every closed-interval increment and endpoint
integration by parts for arbitrary C¹ scalar tests. -/
theorem exists_weak_time_primitive_with_endpoints {T : ℝ} (hT : 0 < T) {f r : ℝ → E}
    (hf : IntegrableOn f (Ioo 0 T)) (hr : IntegrableOn r (Ioo 0 T))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv φ t • f t) = -(∫ t in Ioo 0 T, φ t • r t)) :
    ∃ c : E,
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), f t = c + ∫ s in 0..t, r s) ∧
      ContinuousOn (fun t => c + ∫ s in 0..t, r s) (Icc 0 T) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        (c + ∫ u in 0..t, r u) - (c + ∫ u in 0..s, r u) = ∫ u in s..t, r u) ∧
      (∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ →
        (∫ t in Ioo 0 T, deriv φ t • f t) =
          φ T • (c + ∫ s in 0..T, r s) - φ 0 • c - ∫ t in Ioo 0 T, φ t • r t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T),
        HasDerivAt (fun t => c + ∫ s in 0..t, r s) (r t) t) := by
  obtain ⟨c, hc, hcont⟩ := exists_weak_time_primitive hT hf hr hw
  exact ⟨c, hc, hcont, fun _ hs _ ht => primitive_increment hT hr c hs ht,
    fun _ hφ => weak_scalar_test_ibp hT hr c hc hφ, ae_hasDerivAt_primitive hT hr c⟩

end Yau.L16WeakTimePrimitive
