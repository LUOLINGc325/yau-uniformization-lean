import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Finite dimensional Volterra equations with measurable, essentially bounded
coefficients and Bochner integrable forcing. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Yau.LeafProofs.L16Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def volterraExtend {T : ℝ} (hT : 0 ≤ T) (k : ℝ)
    (v : C(Icc (0 : ℝ) T, E)) (t : ℝ) : E :=
  Real.exp (k * t) • v (projIcc 0 T hT t)

private lemma volterraExtend_continuous {T : ℝ} (hT : 0 ≤ T) (k : ℝ)
    (v : C(Icc (0 : ℝ) T, E)) : Continuous (volterraExtend hT k v) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (v.continuous.comp continuous_projIcc)

private lemma volterraExtend_norm {T k : ℝ} (hT : 0 ≤ T) (hk : 0 ≤ k)
    (v : C(Icc (0 : ℝ) T, E)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖volterraExtend hT k v t‖ ≤ Real.exp (k * T) * ‖v‖ := by
  dsimp [volterraExtend]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hk))
    (v.norm_coe_le_norm _) (norm_nonneg _) (Real.exp_pos _).le

private lemma volterra_integrable_apply {T M C : ℝ}
    {A : ℝ → E →L[ℝ] E} {c : ℝ → E}
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo 0 T)))
    (hAM : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖A t‖ ≤ M)
    (hc : Continuous c) (hcC : ∀ t ∈ Ioo 0 T, ‖c t‖ ≤ C) :
    Integrable (fun t => A t (c t)) (volume.restrict (Ioo 0 T)) := by
  have hm : AEStronglyMeasurable (fun t => A t (c t))
      (volume.restrict (Ioo 0 T)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hA
      hc.aestronglyMeasurable
  refine (integrable_const (M * C)).mono' hm ?_
  filter_upwards [hAM, ae_restrict_mem measurableSet_Ioo] with t hAt ht
  exact (A t).le_opNorm (c t) |>.trans
    (mul_le_mul hAt (hcC t ht) (norm_nonneg _) ((norm_nonneg _).trans hAt))

private lemma volterra_exp_integral {k t : ℝ} (hk : k ≠ 0) :
    (∫ s in (0 : ℝ)..t, Real.exp (k * s)) = (Real.exp (k * t) - 1) / k := by
  rw [intervalIntegral.integral_comp_mul_left _ hk]
  simp only [mul_zero, integral_exp, Real.exp_zero, smul_eq_mul, inv_mul_eq_div]

private lemma volterra_integrable_rhs {T k M : ℝ} (hT : 0 ≤ T) (hk : 0 ≤ k)
    (A : ℝ → E →L[ℝ] E) (g : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo 0 T)))
    (hAM : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖A t‖ ≤ M)
    (hg : Integrable g (volume.restrict (Ioo 0 T)))
    (v : C(Icc (0 : ℝ) T, E)) :
    IntervalIntegrable (fun s => g s - A s (volterraExtend hT k v s)) volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr
  exact hg.sub (volterra_integrable_apply hA hAM (volterraExtend_continuous hT k v)
    (fun s hs => volterraExtend_norm hT hk v ⟨hs.1.le, hs.2.le⟩))

private def volterraMap {T k M : ℝ} (hT : 0 ≤ T) (hk : 0 ≤ k)
    (A : ℝ → E →L[ℝ] E) (g : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo 0 T)))
    (hAM : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖A t‖ ≤ M)
    (hg : Integrable g (volume.restrict (Ioo 0 T)))
    (v : C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, E) where
  toFun t := Real.exp (-k * t) •
    ∫ s in (0 : ℝ)..t, g s - A s (volterraExtend hT k v s)
  continuous_toFun := by
    have hi := volterra_integrable_rhs hT hk A g hA hAM hg v
    have hp : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t,
        g s - A s (volterraExtend hT k v s)) (Icc 0 T) := by
      simpa only [uIcc_of_le hT] using
        (intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul
      (continuousOn_iff_continuous_domRestrict.mp hp)

private lemma volterra_exp_bound {k t B : ℝ} (hk : 0 < k) (hB : 0 ≤ B) :
    Real.exp (-k * t) * (B * ((Real.exp (k * t) - 1) / k)) ≤ B / k := by
  calc
    _ = (B / k) * (1 - Real.exp (-k * t)) := by
      rw [neg_mul, Real.exp_neg]
      field_simp
    _ ≤ B / k := mul_le_of_le_one_right (div_nonneg hB hk.le)
      (sub_le_self _ (Real.exp_pos _).le)

private lemma volterraMap_norm_sub {T k M : ℝ} (hT : 0 ≤ T) (hk : 0 < k) (hM : 0 ≤ M)
    (A : ℝ → E →L[ℝ] E) (g : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo 0 T)))
    (hAM : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖A t‖ ≤ M)
    (hg : Integrable g (volume.restrict (Ioo 0 T)))
    (v w : C(Icc (0 : ℝ) T, E)) :
    ‖volterraMap hT hk.le A g hA hAM hg v - volterraMap hT hk.le A g hA hAM hg w‖ ≤
      (M / k) * ‖v - w‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (div_nonneg hM hk.le) (norm_nonneg _))).mpr
  intro t
  have hi (u : C(Icc (0 : ℝ) T, E)) :=
    volterra_integrable_rhs hT hk.le A g hA hAM hg u
  have his (u : C(Icc (0 : ℝ) T, E)) :
      IntervalIntegrable (fun s => g s - A s (volterraExtend hT k u s)) volume 0 t := by
    apply (hi u).mono_set
    simpa only [uIcc_of_le t.property.1, uIcc_of_le hT] using
      (Icc_subset_Icc le_rfl t.property.2)
  have hAM' : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → ‖A s‖ ≤ M := by
    apply (ae_restrict_iff' measurableSet_Ioc).mp
    rwa [← restrict_Ioo_eq_restrict_Ioc]
  have hbound : ∀ᵐ s ∂volume, s ∈ Ioc 0 (t : ℝ) →
      ‖(g s - A s (volterraExtend hT k v s)) -
        (g s - A s (volterraExtend hT k w s))‖ ≤
        (M * ‖v - w‖) * Real.exp (k * s) := by
    filter_upwards [hAM'] with s hs hst
    have hAs := hs ⟨hst.1, hst.2.trans t.property.2⟩
    have hext : ‖volterraExtend hT k v s - volterraExtend hT k w s‖ ≤
        Real.exp (k * s) * ‖v - w‖ := by
      calc
        _ = Real.exp (k * s) * ‖(v - w) (projIcc 0 T hT s)‖ := by
          simp only [volterraExtend, ← smul_sub, norm_smul, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _), ContinuousMap.sub_apply]
        _ ≤ _ := mul_le_mul_of_nonneg_left ((v - w).norm_coe_le_norm _) (Real.exp_pos _).le
    have heq : (g s - A s (volterraExtend hT k v s)) -
        (g s - A s (volterraExtend hT k w s)) =
        -(A s (volterraExtend hT k v s - volterraExtend hT k w s)) := by
      rw [map_sub]
      abel
    rw [heq, norm_neg]
    calc
      _ ≤ ‖A s‖ * ‖volterraExtend hT k v s - volterraExtend hT k w s‖ :=
        (A s).le_opNorm _
      _ ≤ M * (Real.exp (k * s) * ‖v - w‖) :=
        mul_le_mul hAs hext (norm_nonneg _) hM
      _ = _ := by ring
  have hscalar : IntervalIntegrable (fun s => (M * ‖v - w‖) * Real.exp (k * s))
      volume 0 (t : ℝ) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  change ‖Real.exp (-k * (t : ℝ)) • (∫ s in (0 : ℝ)..(t : ℝ),
      g s - A s (volterraExtend hT k v s)) -
    Real.exp (-k * (t : ℝ)) • (∫ s in (0 : ℝ)..(t : ℝ),
      g s - A s (volterraExtend hT k w s))‖ ≤ _
  rw [← smul_sub, ← intervalIntegral.integral_sub (his v) (his w), norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-k * (t : ℝ)) * (∫ s in (0 : ℝ)..(t : ℝ),
        (M * ‖v - w‖) * Real.exp (k * s)) :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_of_norm_le t.property.1 hbound hscalar)
        (Real.exp_pos _).le
    _ = Real.exp (-k * (t : ℝ)) *
        ((M * ‖v - w‖) * ((Real.exp (k * (t : ℝ)) - 1) / k)) := by
      rw [intervalIntegral.integral_const_mul, volterra_exp_integral hk.ne']
    _ ≤ (M * ‖v - w‖) / k :=
      volterra_exp_bound hk (mul_nonneg hM (norm_nonneg _))
    _ = (M / k) * ‖v - w‖ := by ring

/-- The Volterra equation for a measurable, essentially bounded linear coefficient
and integrable forcing, together with its almost everywhere differential equation. -/
theorem exists_integralODE_of_integrable [CompleteSpace E]
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (A : ℝ → E →L[ℝ] E) (g : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo 0 T)))
    (hAM : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖A t‖ ≤ M)
    (hg : Integrable g (volume.restrict (Ioo 0 T))) :
    ∃ c : ℝ → E, ContinuousOn c (Icc 0 T) ∧ c 0 = 0 ∧
      (∀ t ∈ Icc 0 T, c t = ∫ s in (0 : ℝ)..t, g s - A s (c s)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), HasDerivAt c (g t - A t (c t)) t) := by
  let k : ℝ := 1 + 2 * M
  have hk : 0 < k := by dsimp [k]; positivity
  let Φ := volterraMap hT.le hk.le A g hA hAM hg
  have hcontract : ContractingWith (⟨M / k, div_nonneg hM hk.le⟩ : NNReal) Φ := by
    constructor
    · change M / k < 1
      apply (div_lt_one hk).mpr
      dsimp [k]
      linarith
    · apply LipschitzWith.of_dist_le_mul
      intro v w
      change dist (Φ v) (Φ w) ≤ (M / k) * dist v w
      simp only [dist_eq_norm]
      exact volterraMap_norm_sub hT.le hk hM A g hA hAM hg v w
  let v := hcontract.fixedPoint Φ
  have hv : Φ v = v := hcontract.fixedPoint_isFixedPt
  let c : ℝ → E := volterraExtend hT.le k v
  have hc : Continuous c := volterraExtend_continuous hT.le k v
  have hceq : ∀ t ∈ Icc 0 T, c t = ∫ s in (0 : ℝ)..t, g s - A s (c s) := by
    intro t ht
    have hp := congrArg (fun u : C(Icc (0 : ℝ) T, E) => u ⟨t, ht⟩) hv
    change Real.exp (-k * t) • (∫ s in (0 : ℝ)..t, g s - A s (c s)) = v ⟨t, ht⟩ at hp
    change Real.exp (k * t) • v (projIcc 0 T hT.le t) = _
    rw [projIcc_of_mem hT.le ht, ← hp, smul_smul]
    have he : Real.exp (k * t) * Real.exp (-k * t) = 1 := by
      rw [← Real.exp_add]
      rw [show k * t + -k * t = 0 by ring, Real.exp_zero]
    rw [he, one_smul]
  refine ⟨c, hc.continuousOn, ?_, hceq, ?_⟩
  · simpa only [intervalIntegral.integral_same] using hceq 0 ⟨le_rfl, hT.le⟩
  · have hi := volterra_integrable_rhs hT.le hk.le A g hA hAM hg v
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hti
    have ht' : t ∈ uIcc (0 : ℝ) T := by
      simpa only [uIcc_of_le hT.le] using (show t ∈ Icc 0 T from ⟨hti.1.le, hti.2.le⟩)
    apply (ht ht' 0 left_mem_uIcc).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
    exact hceq s ⟨hs.1.le, hs.2.le⟩

/-- Finite Euclidean Galerkin coefficients with merely integrable forcing have an
actual continuous integral solution and satisfy the ODE almost everywhere. The
statement includes dimension zero. -/
theorem finiteVolterra_exists (m : ℕ) {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (A : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (g : ℝ → EuclideanSpace ℝ (Fin m))
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo 0 T)))
    (hAM : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖A t‖ ≤ M)
    (hg : Integrable g (volume.restrict (Ioo 0 T))) :
    ∃ c : ℝ → EuclideanSpace ℝ (Fin m),
      ContinuousOn c (Icc 0 T) ∧ c 0 = 0 ∧
      (∀ t ∈ Icc 0 T, c t = ∫ s in (0 : ℝ)..t, g s - A s (c s)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), HasDerivAt c (g t - A t (c t)) t) :=
  exists_integralODE_of_integrable hT hM A g hA hAM hg

end Yau.LeafProofs.L16Aux
