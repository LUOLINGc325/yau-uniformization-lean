import Yau.Proofs.P04InverseChartBound
import Yau.Proofs.P04LeviCharts

noncomputable section
open Set WithLp MeasureTheory
open scoped Topology Manifold ContDiff InnerProductSpace Matrix ComplexOrder ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

/-- On a genuine compact model set the computed inverse curvature of a
fixed smooth strictly psh weight and smooth source has one finite bound. -/
theorem compact_flat_inverseCurvature_bound (g : SmoothMetric M) (p : M.Carrier)
    {ψ : M.Carrier → ℝ} (hψ : IsSmoothStrictPsh ψ)
    (f : NQForm (CanonicalCoefficients M) 1)
    (hf : SmoothForm (r := 1) (CanonicalCoefficients M) f)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hs : K ⊆ chartTarget p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K,
      inverseCurvatureNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric ψ f (chartInv p z) ≤
        ENNReal.ofReal C := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : K → Matrix (Fin n) (Fin n) ℂ := fun z => leviC (inChart p ψ) z.1
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (L14Aux.leviC_contDiffOn ψ hψ.1 p i j).continuousOn.comp_continuous
      continuous_subtype_val (fun z => hs z.2)
  obtain ⟨δ,hδ,hlower⟩ := compact_posDef_uniform_lower_bound A hA
    (fun z => smooth_strictPsh_all_charts hψ p z.1 (hs z.2))
  let F : ComplexVector n → ComplexVector n :=
    fun z => toLp 2 (fun i => coefficients (r := 1) (CanonicalCoefficients M) f p z (fun _ => i) 0)
  have hF : ContinuousOn F (chartTarget p) := by
    apply (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n => ℂ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    simpa only [coefficient_localDomain] using (hf p (fun _ => i) 0).continuousOn
  have hd : ContinuousOn (fun z => (hMat g.form p z).det.re) (chartTarget p) :=
    Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g p)).continuousOn
  let b : ComplexVector n → ℝ := fun z => ((hMat g.form p z).det.re)⁻¹*(‖F z‖^2/δ)
  have hb : ContinuousOn b K :=
    ((hd.inv₀ (fun z hz => (L18Aux.hMat_det_re_pos g.form p hz).ne')).mul
      ((hF.norm.pow 2).div_const δ)).mono hs
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hb
  refine ⟨max C 0,le_max_right _ _,fun z hz => ?_⟩
  calc
    _ ≤ ENNReal.ofReal (b z) := flat_inverseCurvatureNormSq_inChart_le g ψ hψ.1 f p z (hs hz)
      hδ (hlower ⟨z,hz⟩)
    _ ≤ ENNReal.ofReal (max C 0) := by
      apply ENNReal.ofReal_le_ofReal
      have Hb : |b z| ≤ C := by simpa only [Real.norm_eq_abs] using hC z hz
      exact (le_abs_self (b z)).trans (Hb.trans (le_max_left _ _))

end Yau.Proofs.P04Aux
