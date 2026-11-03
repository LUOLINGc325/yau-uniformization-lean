import Yau.LeafProofs.L09
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! A genuine weak planar gradient for scalar Lipschitz functions. The
integration-by-parts identity uses the actual measurable line derivatives;
no weak-gradient certificate is supplied as an input. -/

open scoped Topology ContDiff NNReal
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux

def planarLineGradient (v : ℂ → ℝ) (z : ℂ) : LeafCandidates.RV 2 :=
  WithLp.toLp 2 (fun i : Fin 2 => lineDeriv ℝ v z (if i = 0 then 1 else Complex.I))

theorem lipschitz_weakPlanarGradient {v : ℂ → ℝ} {C : ℝ≥0} (hv : LipschitzWith C v)
    {O : Set ℂ} (hO : Bornology.IsBounded O) :
    LeafCandidates.WeakPlanarGradient O v (planarLineGradient v) := by
  have hcompact : IsCompact (closure O) := hO.isCompact_closure
  refine ⟨(hv.continuous.continuousOn.integrableOn_compact hcompact).mono_set subset_closure, ?_, ?_⟩
  · rw [IntegrableOn, integrable_piLp_iff]
    intro i
    exact ((hv.locallyIntegrable_lineDeriv (μ := volume) (if i = 0 then 1 else Complex.I)).integrableOn_isCompact
      hcompact).mono_set subset_closure
  · intro φ hφ hφc hφO i
    let e : ℂ := if i = 0 then 1 else Complex.I
    obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
    have h := hv.integral_lineDeriv_mul_eq (μ := volume) hD hφc e
    have hglobal : (∫ z, v z * fderiv ℝ φ z e) =
        -(∫ z, lineDeriv ℝ v z e * φ z) := by
      simp_rw [(hφ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
        map_neg, neg_mul, integral_neg] at h
      simpa only [neg_neg, mul_comm] using (congrArg Neg.neg h).symm
    have hleft : (∫ z in O, v z * fderiv ℝ φ z e) = ∫ z, v z * fderiv ℝ φ z e := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hz' : z ∉ tsupport (fun w => fderiv ℝ φ w e) :=
        fun hmem => hz (hφO (tsupport_fderiv_apply_subset ℝ e hmem))
      rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]
    have hright : (∫ z in O, lineDeriv ℝ v z e * φ z) = ∫ z, lineDeriv ℝ v z e * φ z := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun hmem => hz (hφO hmem)), mul_zero]
    change (∫ z in O, v z * fderiv ℝ φ z e) = -(∫ z in O, lineDeriv ℝ v z e * φ z)
    rw [hleft, hright]
    exact hglobal

/-- A Lipschitz scalar function on an open bounded working domain has an
actual weak gradient with its original directional derivatives there. -/
theorem lipschitzOn_exists_weakPlanarGradient {v : ℂ → ℝ} {C : ℝ≥0}
    {O : Set ℂ} (hv : LipschitzOnWith C v O) (hO : IsOpen O) (hbounded : Bornology.IsBounded O) :
    ∃ g : ℂ → LeafCandidates.RV 2, LeafCandidates.WeakPlanarGradient O v g ∧
      ∀ z ∈ O, ∀ i : Fin 2, g z i = lineDeriv ℝ v z (if i = 0 then 1 else Complex.I) := by
  obtain ⟨w, hw, heq⟩ := hv.extend_real
  have hweak := lipschitz_weakPlanarGradient hw hbounded
  have hae : v =ᵐ[volume.restrict O] w := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    exact heq hz
  refine ⟨planarLineGradient w, ⟨hweak.1.congr hae.symm, hweak.2.1, ?_⟩, ?_⟩
  · intro φ hφ hφc hφO i
    calc
      _ = ∫ z in O, w z * fderiv ℝ φ z (if i = 0 then 1 else Complex.I) := by
        apply integral_congr_ae
        filter_upwards [hae] with z hz
        rw [hz]
      _ = _ := hweak.2.2 φ hφ hφc hφO i
  · intro z hz i
    have hevent : w =ᶠ[𝓝 z] v := by
      filter_upwards [hO.mem_nhds hz] with y hy
      exact (heq hy).symm
    exact hevent.lineDeriv_eq

end Yau.NodeProofs.D02Aux
