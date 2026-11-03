import Yau.LeafProofs.L17PotentialLeviMap
import Yau.LeafProofs.L17BackgroundLogDetJets

noncomputable section
open Set Metric
open scoped Topology ContDiff
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17BootstrapFlowSmoothAux
open L17Aux L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- An affine spatial change preserves the same closed or arbitrary time set. -/
theorem translated_profile_contDiffOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (z0 : ComplexVector n) (r : ℝ) (I : Set ℝ)
    {f : ComplexVector n × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (ball 0 r ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × ℝ => f (a.1-z0,a.2))
      (ball z0 r ×ˢ I) := by
  apply hf.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn
  intro a ha
  refine ⟨?_,ha.2⟩
  simpa only [mem_ball,dist_eq_norm,sub_zero] using ha.1

/-- Levi entries are four actual bounded-linear Hessian evaluations. No matrix
norm or topology is changed in this entrywise statement. -/
theorem levi_entry_contDiffOn {O : Set (ComplexVector n × ℝ)}
    {Q : ComplexVector n × ℝ → D2 n} (hQ : ContDiffOn ℝ ∞ Q O)
    (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun a => leviHessianCLM n (Q a) i j) O := by
  have h00 : ContDiffOn ℝ ∞ (fun a => Q a (stdVec j) (stdVec i)) O :=
    (hQ.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have h11 : ContDiffOn ℝ ∞
      (fun a => Q a (Complex.I • stdVec j) (Complex.I • stdVec i)) O :=
    (hQ.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have h01 : ContDiffOn ℝ ∞ (fun a => Q a (stdVec j) (Complex.I • stdVec i)) O :=
    (hQ.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have h10 : ContDiffOn ℝ ∞ (fun a => Q a (Complex.I • stdVec j) (stdVec i)) O :=
    (hQ.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hRe : ContDiffOn ℝ ∞ (fun a =>
      (((1/4 : ℝ)*(Q a (stdVec j) (stdVec i)+
        Q a (Complex.I • stdVec j) (Complex.I • stdVec i)) : ℝ) : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul (h00.add h11))
  have hIm : ContDiffOn ℝ ∞ (fun a =>
      (((1/4 : ℝ)*(Q a (stdVec j) (Complex.I • stdVec i)-
        Q a (Complex.I • stdVec j) (stdVec i)) : ℝ) : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul (h01.sub h10))
  simpa only [leviHessianCLM_apply,leviFromHessian,Complex.mk_eq_add_mul_I]
    using hRe.add (hIm.mul (contDiffOn_const (c := Complex.I)))

variable (P : UniformChartPartition g) (p : P.centers) (z0 : ComplexVector n)
    (r : ℝ) (I : Set ℝ)
    (hCoord : MapsTo (fun theta : ComplexVector n => z0+theta)
      (ball 0 r) (ball 0 P.radius))

include hCoord

theorem background_metric_entry_contDiffOn (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × ℝ =>
      pullbackMatrix g (P.charts.chart p) (z0+a.1) i j) (ball 0 r ×ˢ I) := by
  apply (P.charts.coefficient_smooth p i j).comp
    (contDiffOn_const.add contDiff_fst.contDiffOn)
  intro a ha
  exact (ball_subset_ball P.radius_lt.le) (hCoord ha.1)

theorem background_ricci_entry_contDiffOn (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × ℝ =>
      pullbackRicci g (P.charts.chart p) (z0+a.1) i j) (ball 0 r ×ˢ I) := by
  have hH : ContDiffOn ℝ ∞ (fun a : ComplexVector n × ℝ =>
      fderiv ℝ (fderiv ℝ (P.charts.backgroundLogDet p)) (z0+a.1))
      (ball 0 r ×ˢ I) :=
    (P.charts.backgroundLogDet_hessian_smooth p).comp
      (contDiffOn_const.add contDiff_fst.contDiffOn)
      (fun a ha => (ball_subset_ball P.radius_lt.le) (hCoord ha.1))
  apply (levi_entry_contDiffOn hH i j).neg.congr
  intro a ha
  have hz : z0+a.1 ∈ ball 0 P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) (hCoord ha.1)
  have hSmooth : ContDiffAt ℝ 2 (P.charts.backgroundLogDet p) (z0+a.1) :=
    ((P.charts.backgroundLogDet_smooth p).contDiffAt (isOpen_ball.mem_nhds hz)).of_le
      (by simp)
  change -(leviC (P.charts.backgroundLogDet p) (z0+a.1) i j)=_
  rw [leviC_eq_leviHessianCLM hSmooth]

theorem metric_profile_entry_contDiffOn {Q : ComplexVector n × ℝ → D2 n}
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 r ×ˢ I)) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × ℝ =>
      pullbackMatrix g (P.charts.chart p) (z0+a.1) i j+
        (leviHessianCLM n (Q a) i j-
          (a.2 : ℂ)*pullbackRicci g (P.charts.chart p) (z0+a.1) i j))
      (ball 0 r ×ˢ I) := by
  have hTime : ContDiffOn ℝ ∞ (fun a : ComplexVector n × ℝ => (a.2 : ℂ))
      (ball 0 r ×ˢ I) := Complex.ofRealCLM.contDiff.comp_contDiffOn contDiff_snd.contDiffOn
  exact (background_metric_entry_contDiffOn P p z0 r I hCoord i j).add
    ((levi_entry_contDiffOn hQ i j).sub
      (hTime.mul (background_ricci_entry_contDiffOn P p z0 r I hCoord i j)))

end Yau.LeafProofs.L17BootstrapFlowSmoothAux
