import Yau.LeafProofs.L05AutonomousSecondPositive
import Yau.LeafProofs.L05AutonomousSecondCoefficient
import Yau.LeafProofs.L05AutonomousMollifierSecond
import Yau.LeafProofs.L05AutonomousHessianAbsorption

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Positive second differences and the actual elliptic trace bound both signs of the smooth Hessian. -/
theorem auto_uniform_mollified_hessian :
    ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L → ConcaveOn ℝ univ F → F 0=0 →
      ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p|≤ 1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
        ∃ w : Point n →ᵇ ℝ, EqOn w u (unitClosed n) ∧ UniformContinuous (w : Point n → ℝ) ∧
          HasCompactSupport (w : Point n → ℝ) ∧ ‖w‖ ≤ 1 ∧
          ∀ (eps : ℝ) (heps : 0 < eps), eps < 1/256 → ∀ p∈autoClosed (0 : Space n) (45/64) 0,
            ‖secondFDerivMatrix (fun x => autoSpatialMollify eps heps w (x,p.2)) p.1‖ ≤ C := by
  intro n hn ell L hell hL
  obtain ⟨P,hP,hPositive⟩ := auto_uniform_second_positive n hn ell L hell hL
  obtain ⟨B,hB,hForF⟩ := auto_uniform_mollified_trace n hn ell L hell hL
  let C := 1+P*‖(1 : Mat n)‖+(P*((2*n : ℝ)*L)+B)/ell
  have hL0 : 0 ≤ L := hell.le.trans hL
  have hTerm : 0 ≤ (P*((2*n : ℝ)*L)+B)/ell := by positivity
  have hC : 0 < C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro F hF hE hConc h0 u hu hb hsol
  obtain ⟨A,hA,hForU⟩ := hForF F hF hE hConc h0
  obtain ⟨w,hwu,hw,hcw,hw1,hTrace⟩ := hForU u hu hb hsol
  refine ⟨w,hwu,hw,hcw,hw1,?_⟩
  intro eps heps hepsSmall p hp
  let f : Space n → ℝ := fun x => autoSpatialMollify eps heps w (x,p.2)
  have hf : ContDiff ℝ ∞ f := autoSpatialMollify_spatial_contDiff eps heps w hw p.2
  have hUpper (e : Space n) (he : ‖e‖=1) : fderiv ℝ (fderiv ℝ f) p.1 e e ≤ P := by
    have hSmall (h : ℝ) (hh : h≠0) (hstep : |h| < 1/512) : autoSecond (autoSpatialMollify eps heps w) e h p ≤ P := by
      have hShift (y : Space n) (hy : y∈Metric.closedBall (0 : Space n) eps) :
          autoSecond w e h (p.1-y,p.2) ≤ P := by
        have hx : ‖p.1‖ ≤ 45/64 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
        have hyNorm : ‖y‖ ≤ eps := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
        have hxy : ‖p.1-y‖ ≤ 23/32 := by
          have ht := norm_sub_le p.1 y
          linarith only [ht,hx,hyNorm,hepsSmall]
        have ht : -(45/64 : ℝ)^2 ≤ p.2 ∧ p.2 ≤ 0 := by simpa only [zero_sub,mem_Icc] using hp.2
        have hq : (p.1-y,p.2)∈autoClosed (0 : Space n) (23/32) 0 :=
          ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxy,
            by change (0 : ℝ)-(23/32)^2 ≤ p.2 ∧ p.2 ≤ 0;exact ⟨by linarith only [ht.1],ht.2⟩⟩
        obtain ⟨hq0,hqPlus,hqMinus⟩ := auto_second_closed_unit (by norm_num : (0 : ℝ) < 23/32)
          (by linarith only [hstep] : (23/32 : ℝ)+|h| < 1) he.le hq
        rw [auto_second_congr hwu e h _ hq0 hqPlus hqMinus]
        exact hPositive F hF hE hConc h0 u hu hb hsol e he h hh hstep _ hq
      let nu := autoMollifierMeasure n eps heps
      let : IsProbabilityMeasure nu := autoMollifierMeasure_isProbability n eps heps
      have hcomm := auto_mollify_second eps heps w hw e h p
      have hBound := integral_mono_ae hcomm.1 (integrable_const P) (by
        filter_upwards [autoMollifierMeasure_closedBall_ae n eps heps] with y hy
        exact hShift y hy)
      rw [← hcomm.2,integral_const,probReal_univ,one_smul] at hBound
      exact hBound
    have hlim := auto_spatial_second_limit hf p.1 e
    apply le_of_tendsto hlim
    have hevent : Ioo (0 : ℝ) (1/512)∈𝓝[>] 0 :=
      mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨_,by norm_num,subset_rfl⟩
    filter_upwards [hevent] with h hh
    exact hSmall h hh.1.ne' (by simpa only [abs_of_pos hh.1] using hh.2)
  have hTraceLower : -B ≤ Matrix.trace ((A : Mat n)*autoBilinearEntryMatrix (fderiv ℝ (fderiv ℝ f) p.1)) :=
    (abs_le.mp (hTrace eps heps (hepsSmall.trans (by norm_num)) p
      (autoClosed_subset 0 (by norm_num) (by norm_num) 0 hp))).1
  have hSym : ∀ x y, fderiv ℝ (fderiv ℝ f) p.1 x y=fderiv ℝ (fderiv ℝ f) p.1 y x :=
    (hf.contDiffAt.isSymmSndFDerivAt (by simp))
  have hBound := auto_bilinear_frobenius_bound hell hP.le hA (fderiv ℝ (fderiv ℝ f) p.1) hSym hUpper hTraceLower
  exact hBound.trans (by dsimp only [C];linarith)

end Yau.LeafProofs.L05AutonomousAux
