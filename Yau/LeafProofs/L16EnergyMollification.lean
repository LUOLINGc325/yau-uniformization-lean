import Yau.LeafProofs.L16EnergyEquation

open MeasureTheory Filter
open scoped Topology ContDiff Convolution Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem integrable_translated_kernel_mul {n : ℕ} {ρ f : Point n → ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hf : Integrable f volume) (p : Point n) :
    Integrable (fun q => ρ (p-q)*f q) volume := by
  obtain ⟨M,hM⟩ := hcρ.exists_bound_of_continuous hρ
  have h := hf.bdd_smul M (hρ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => hM (p-q))
  exact h

theorem weakDivergenceEvolution_convolution {n : ℕ}
    {w : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ} {R : Point n → ℝ}
    (hEq : WeakDivergenceEvolution Set.univ Set.univ w P R)
    (hw : Integrable w volume) (hP : ∀ i, Integrable (fun q => P q i) volume)
    (hR : Integrable R volume) (ρ : Point n → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (p : Point n) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] w) p (0,1) =
      (∑ i, fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (fun q => P q i)) p
        (Yau.realVec i,0)) + (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] R) p := by
  classical
  let φ : Point n → ℝ := fun q => ρ (p-q)
  have hφ : ContDiff ℝ ∞ φ := hρ.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := by
    simpa [φ,Function.comp_def] using hcρ.comp_homeomorph (Homeomorph.subLeft p)
  have hdφ (q e : Point n) : fderiv ℝ φ q e = -fderiv ℝ ρ (p-q) e := by
    have h := ((hρ.differentiable (by simp) (p-q)).hasFDerivAt.comp q
      ((hasFDerivAt_id q).const_sub p)).fderiv
    simpa only [φ,Function.comp_def,ContinuousLinearMap.comp_apply,
      neg_apply,ContinuousLinearMap.id_apply,map_neg] using DFunLike.congr_fun h e
  have hTime (q : Point n) : deriv (fun t => φ (q.1,t)) q.2 = -fderiv ℝ ρ (p-q) (0,1) := by
    rw [test_timeDerivative_eq_joint_fderiv (hφ.differentiable (by simp) q),hdφ]
  have hSpace (q : Point n) (i : Yau.RIdx n) :
      d (fun x => φ (x,q.2)) q.1 i = -fderiv ℝ ρ (p-q) (Yau.realVec i,0) := by
    rw [d_eq_joint_fderiv (hφ.differentiable (by simp) q) i,hdφ]
  have hBase (z : Point n → ℝ) (hz : Integrable z volume) (e : Point n) :
      Integrable (fun q => fderiv ℝ ρ (p-q) e*z q) volume :=
    integrable_translated_kernel_mul
      ((hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      (hcρ.fderiv_apply ℝ e) hz p
  let A : Point n → ℝ := fun q => fderiv ℝ ρ (p-q) (0,1)*w q
  let B : Yau.RIdx n → Point n → ℝ := fun i q => fderiv ℝ ρ (p-q) (Yau.realVec i,0)*P q i
  let C : Point n → ℝ := fun q => ρ (p-q)*R q
  have hA : Integrable A volume := hBase w hw _
  have hB (i : Yau.RIdx n) : Integrable (B i) volume := hBase _ (hP i) _
  have hC : Integrable C volume := integrable_translated_kernel_mul hρ.continuous hcρ hR p
  have hSum : Integrable (fun q => ∑ i, B i q) volume := integrable_finsetSum _ (fun i _ => hB i)
  have h := hEq φ ⟨hφ,hcφ,by simp only [Set.univ_prod_univ]; exact Set.subset_univ _⟩
  rw [productVolume_eq_restrict] at h
  simp only [Set.univ_prod_univ,Measure.restrict_univ] at h
  have hFun : (fun q => -w q*deriv (fun t => φ (q.1,t)) q.2+
      (∑ i, P q i*d (fun x => φ (x,q.2)) q.1 i)-R q*φ q) =
      fun q => A q-(∑ i, B i q)-C q := by
    funext q
    simp only [hTime,hSpace,φ,A,B,C,mul_neg,Finset.sum_neg_distrib]
    simp only [mul_comm]
    ring
  rw [hFun] at h
  have hSplit1 := integral_sub (hA.sub hSum) hC
  have hSplit2 := integral_sub hA hSum
  simp only [Pi.sub_apply] at hSplit1 hSplit2
  rw [hSplit1,hSplit2,integral_finsetSum Finset.univ (fun i _ => hB i)] at h
  simp_rw [Yau.LeafProofs.L03.convolution_directional_derivative volume ρ _
    (hρ.of_le (by simp)) hcρ hw,
    Yau.LeafProofs.L03.convolution_directional_derivative volume ρ _
    (hρ.of_le (by simp)) hcρ (hP _),MeasureTheory.convolution_lsmul_swap,smul_eq_mul]
  change (∫ q, A q) = (∑ i, ∫ q, B i q)+(∫ q, C q)
  linarith

end Yau.LeafProofs.L16Aux
