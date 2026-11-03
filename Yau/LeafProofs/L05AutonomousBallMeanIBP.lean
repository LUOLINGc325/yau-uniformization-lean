import Yau.LeafProofs.L05AutonomousBallMoments

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

def autoBallMeanLaplacian {n : ℕ} (f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Yau.RIdx n, (fderiv ℝ (fderiv ℝ f) x) (Yau.realVec i) (Yau.realVec i)

theorem auto_ballMean_integrable_mul_compact {n : ℕ} {f g : Space n → ℝ}
    (hf : ContinuousOn f (tsupport g)) (hg : Continuous g) (hcg : HasCompactSupport g) :
    Integrable (fun x => f x*g x) := by
  have hInt : IntegrableOn (fun x => f x*g x) (tsupport g) volume :=
    (hf.mul hg.continuousOn).integrableOn_compact hcg.isCompact
  have hEq : (tsupport g).indicator (fun x => f x*g x)=(fun x => f x*g x) := by
    funext x
    by_cases hx : x∈tsupport g
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport hx,mul_zero]
  rw [← hEq]
  exact (integrable_indicator_iff (isClosed_tsupport g).measurableSet).mpr hInt

theorem auto_ballMean_local_spatial_ibp {n : ℕ} {f g : Space n → ℝ}
    (hf : ∀ x∈tsupport g, ContDiffAt ℝ 1 f x) (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (e : Space n) :
    (∫ x, f x*fderiv ℝ g x e)=-(∫ x, fderiv ℝ f x e*g x) := by
  have hFCont : ContinuousOn f (tsupport g) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hDFCont : ContinuousOn (fun x => fderiv ℝ f x e) (tsupport g) := by
    intro x hx
    exact (((hf x hx).fderiv_right (m := 0) (by norm_num)).clm_apply contDiffAt_const).continuousAt.continuousWithinAt
  have hDG : Continuous (fun x => fderiv ℝ g x e) :=
    ((hg.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hSub : tsupport (fun x => fderiv ℝ g x e) ⊆ tsupport g := by
    exact tsupport_fderiv_apply_subset ℝ e
  have hFG : Integrable (fun x => f x*g x) := auto_ballMean_integrable_mul_compact hFCont hg.continuous hcg
  have hDFG : Integrable (fun x => fderiv ℝ f x e*g x) := auto_ballMean_integrable_mul_compact hDFCont hg.continuous hcg
  have hFDG : Integrable (fun x => f x*fderiv ℝ g x e) :=
    auto_ballMean_integrable_mul_compact (hFCont.mono hSub) hDG (hcg.fderiv_apply ℝ e)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hDFG hFDG hFG
    (fun x hx => (hf x hx).differentiableAt (by norm_num))
    (fun x _ => hg.differentiable (by norm_num) x)

theorem auto_ballMean_direction_second {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (e : Space n) :
    fderiv ℝ (fun y => fderiv ℝ f y e) x e=(fderiv ℝ (fderiv ℝ f) x) e e := by
  have hD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [(hD.hasFDerivAt.clm_apply (hasFDerivAt_const e x)).fderiv]
  simp

theorem auto_ballMean_local_second_ibp {n : ℕ} {f g : Space n → ℝ}
    (hf : ∀ x∈tsupport g, ContDiffAt ℝ 2 f x) (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) (e : Space n) :
    (∫ x, g x*(fderiv ℝ (fderiv ℝ f) x) e e)=
      ∫ x, f x*(fderiv ℝ (fderiv ℝ g) x) e e := by
  have hGDir : ContDiff ℝ 1 (fun x => fderiv ℝ g x e) :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hFirst := auto_ballMean_local_spatial_ibp (f := f) (g := fun x => fderiv ℝ g x e)
    (fun x hx => (hf x (tsupport_fderiv_apply_subset ℝ e hx)).of_le (by norm_num))
    hGDir (hcg.fderiv_apply ℝ e) e
  have hFDir : ∀ x∈tsupport g, ContDiffAt ℝ 1 (fun y => fderiv ℝ f y e) x :=
    fun x hx => ((hf x hx).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hSecond := auto_ballMean_local_spatial_ibp (f := fun y => fderiv ℝ f y e) (g := g) hFDir (hg.of_le (by norm_num)) hcg e
  have hPointF (x : Space n) :
      fderiv ℝ (fun y => fderiv ℝ f y e) x e*g x=g x*(fderiv ℝ (fderiv ℝ f) x) e e := by
    by_cases hx : x∈tsupport g
    · rw [auto_ballMean_direction_second (hf x hx)]; ring
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,zero_mul]
  have hPointG (x : Space n) :
      f x*fderiv ℝ (fun y => fderiv ℝ g y e) x e=f x*(fderiv ℝ (fderiv ℝ g) x) e e := by
    rw [auto_ballMean_direction_second hg.contDiffAt]
  have hL := integral_congr_ae (ae_of_all volume hPointF)
  have hR := integral_congr_ae (ae_of_all volume hPointG)
  rw [hL] at hSecond
  rw [hR] at hFirst
  linarith only [hFirst,hSecond]


theorem auto_ballMean_local_laplacian_ibp {n : ℕ} {f g : Space n → ℝ}
    (hf : ∀ x∈tsupport g, ContDiffAt ℝ 2 f x) (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) :
    (∫ x, g x*autoBallMeanLaplacian f x)=∫ x, f x*autoBallMeanLaplacian g x := by
  let H : (Space n → ℝ) → Yau.RIdx n → Space n → ℝ :=
    fun u i x => (fderiv ℝ (fderiv ℝ u) x) (Yau.realVec i) (Yau.realVec i)
  have hIntF (i : Yau.RIdx n) : Integrable (fun x => g x*H f i x) := by
    have hCont : ContinuousOn (H f i) (tsupport g) := by
      intro x hx
      exact ((((hf x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiffAt_const |>.clm_apply contDiffAt_const).continuousAt.continuousWithinAt
    have h := auto_ballMean_integrable_mul_compact hCont hg.continuous hcg
    simpa only [mul_comm] using h
  have hIntG (i : Yau.RIdx n) : Integrable (fun x => f x*H g i x) := by
    have hEq : H g i=(fun x => fderiv ℝ (fun y => fderiv ℝ g y (Yau.realVec i)) x (Yau.realVec i)) := by
      funext x
      exact (auto_ballMean_direction_second hg.contDiffAt (Yau.realVec i)).symm
    have hCont : Continuous (H g i) :=
      (((hg.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiff_const |>.clm_apply contDiff_const).continuous
    have hCompact : HasCompactSupport (H g i) := by
      rw [hEq]
      exact (hcg.fderiv_apply ℝ (Yau.realVec i)).fderiv_apply ℝ (Yau.realVec i)
    have hSub : tsupport (H g i) ⊆ tsupport g := by
      rw [hEq]
      exact (tsupport_fderiv_apply_subset ℝ (Yau.realVec i)).trans (tsupport_fderiv_apply_subset ℝ (Yau.realVec i))
    exact auto_ballMean_integrable_mul_compact
      (fun x hx => (hf x (hSub hx)).continuousAt.continuousWithinAt) hCont hCompact
  have hEqF : (fun x => g x*autoBallMeanLaplacian f x)=(fun x => ∑ i, g x*H f i x) := by
    funext x
    rw [autoBallMeanLaplacian,Finset.mul_sum]
  have hEqG : (fun x => f x*autoBallMeanLaplacian g x)=(fun x => ∑ i, f x*H g i x) := by
    funext x
    rw [autoBallMeanLaplacian,Finset.mul_sum]
  rw [hEqF,hEqG,integral_finsetSum _ (fun i _ => hIntF i),integral_finsetSum _ (fun i _ => hIntG i)]
  exact Finset.sum_congr rfl (fun i _ => auto_ballMean_local_second_ibp hf hg hcg (Yau.realVec i))

end Yau.LeafProofs.L05AutonomousAux
