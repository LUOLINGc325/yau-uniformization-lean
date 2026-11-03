import Yau.Proofs.F05InteriorWideExpHolder
import Yau.Proofs.F05InteriorWideNonlinearSchauder
import Yau.Proofs.F05RawCoefficientBudget
import Yau.Proofs.F05SmoothClosedSlabC2
import Yau.Proofs.F05BootstrapNative

/-! Fixed smooth geometric fields and a value interval give a uniform
positive-time interior Schauder bound. The two explicit equation forms
are the native exponential divergence identity and the actual relative
nonlinear identity; both are computed from the original intrinsic PDE. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_interior_uniform_schauder (hn : 0 < n) {S s B lam upper : ℝ}
    (hS : 0 < S) (hs : 0 < s) (hsS : s < S) (hB : 0 ≤ B)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R : Point n → ℝ}
    (hab : SmoothCoefficients (Metric.ball 0 3 ×ˢ Icc 0 S) a b)
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Icc 0 S))
    (he : Elliptic (cylinder (Metric.closedBall 0 (11/4)) 0 S) a lam upper) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧ ∀ u : Point n → ℝ,
      ContDiffOn ℝ ∞ u (Metric.ball 0 3 ×ˢ Icc 0 S) →
      (∀ z ∈ cylinder (region none (11/4)) 0 S, 0 ≤ u z ∧ u z ≤ B) →
      ExpDivergenceEquation (F05CapOpen none 3 ×ˢ Ioc 0 S) a b R (fun z => Real.exp (u z)) →
      (∀ z ∈ region none (5/2) ×ˢ Icc (s/2) S,
        F05RelT (Icc (s/2) S) u z = Real.exp (-u z)*
          ((∑ j,∑ k,a z j k*F05RelDD (region none (5/2)) u z (realVec j) (realVec k))+
            ∑ j,b z j*F05RelD (region none (5/2)) u z (realVec j))+
          (1-Real.exp (-u z))*R z) →
      F05RelSchauder α (region none (9/4)) (Icc s S) u C := by
  have hs0 : 0 < s/2 := by linarith
  have hs0s : s/2 < s := by linarith
  obtain ⟨α,D,hα,hα1,hD,hHolder⟩ := F05_exp_wide_interior_value_holder_uniform hn
    (by norm_num : (0 : ℝ) < 1) (Real.one_le_exp_iff.mpr hB) hs0 hab hR he
  obtain ⟨M,hM,hBudget⟩ := F05_raw_smooth_coefficient_budget hS
    (by norm_num : (5/2 : ℝ) < 3) hab hR
  obtain ⟨C,hC,hSch⟩ := F05_wide_interior_nonlinear_schauder_uniform
    (lam := lam) (upper := upper) hα hα1 hM.le hD.le hB hs0s
  refine ⟨α,C,hα,hα1,hC,?_⟩
  intro u hu hRange hExpEq hRelEq
  have hDU : region (n := n) none (11/4) ⊆ Metric.ball 0 3 := by
    intro z hz
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hz.1]
  have hExpC2 := F05_smooth_cylinder_c2 Metric.isOpen_ball hDU hS le_rfl hu.exp
  have hExpSmooth : ContDiffOn ℝ ∞ (fun z => Real.exp (u z))
      (F05CapOpen none 3 ×ˢ Ioc 0 S) :=
    hu.exp.mono (fun z hz => ⟨hz.1.2,Ioc_subset_Icc_self hz.2⟩)
  have hExpRange (z : Point n) (hz : z ∈ cylinder (region none (11/4)) 0 S) :
      1 ≤ Real.exp (u z) ∧ Real.exp (u z) ≤ Real.exp B :=
    ⟨Real.one_le_exp_iff.mpr (hRange z hz).1,Real.exp_le_exp.mpr (hRange z hz).2⟩
  have hExpHolder := hHolder S hS le_rfl (fun z => Real.exp (u z))
    hExpC2 hExpSmooth hExpRange hExpEq
  let Q := region (n := n) none (5/2) ×ˢ Icc (s/2) S
  have hQ : Q ⊆ cylinder (Metric.closedBall 0 (5/2)) 0 S := by
    intro z hz
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1.1,
      hs0.le.trans hz.2.1,hz.2.2⟩
  have hQWide : Q ⊆ cylinder (region none (11/4)) 0 S :=
    fun z hz => ⟨F05_region_mono (by norm_num) hz.1,hs0.le.trans hz.2.1,hz.2.2⟩
  have hEll : Elliptic Q a lam upper :=
    ⟨he.1,he.2.1,fun z hz => he.2.2 z
      ⟨Metric.closedBall_subset_closedBall (by norm_num : (5/2 : ℝ) ≤ 11/4) (hQ hz).1,(hQ hz).2⟩⟩
  have hBase := hBudget α hα hα1 S le_rfl
  have hUSmooth : ContDiffOn ℝ ∞ u (Metric.ball 0 3 ×ˢ Icc (s/2) S) :=
    hu.mono (fun z hz => ⟨hz.1,hs0.le.trans hz.2.1,hz.2.2⟩)
  have hInnerDU : region (n := n) none (5/2) ⊆ Metric.ball 0 3 := by
    intro z hz
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hz.1]
  have hUC2 := F05_smooth_closed_slab_c2 Metric.isOpen_ball hInnerDU
    (hs0s.trans hsS) le_rfl hUSmooth
  exact hSch S hsS a b R u hEll (holderBound_mono hBase.1 hQ)
    (fun j => holderBound_mono (hBase.2.1 j) hQ) (holderBound_mono hBase.2.2 hQ)
    hExpHolder (F05_native_c2_to_relative (F05_region_uniqueDiffOn none (by norm_num)) hUC2)
    (fun z hz => hRange z (hQWide hz)) hRelEq

end Yau.Proofs.F05Aux
