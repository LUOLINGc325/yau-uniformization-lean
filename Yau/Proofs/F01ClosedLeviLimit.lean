import Yau.Proofs.F01ClosedSpatialSecondLimit
import Yau.LeafProofs.L22LeviCalculus

/-! The native nested Wirtinger Levi entries pass to the genuine closed
space-time jet limit, by their exact real-Hessian formulas. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem closed_levi_entry_limit_of_jets
    {S : Set (ComplexVector n)} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (f : ℕ → ComplexVector n × ℝ → ℝ) (g : ComplexVector n × ℝ → ℝ)
    (hf : ∀ m, ContDiffOn ℝ ∞ (f m) (S ×ˢ I)) (hg : ContDiffOn ℝ ∞ g (S ×ˢ I))
    (hconv : TendstoUniformlyOn (fun m p => iteratedFDerivWithin ℝ 2 (f m) (S ×ˢ I) p)
      (iteratedFDerivWithin ℝ 2 g (S ×ˢ I)) atTop (S ×ˢ I))
    {x : ComplexVector n} (hx : x ∈ S) {t : ℝ} (ht : t ∈ I) (i j : Fin n) :
    Tendsto (fun m => leviC (fun z => f m (z, t)) x i j) atTop
      (𝓝 (leviC (fun z => g (z, t)) x i j)) := by
  have hsecond (v w : ComplexVector n) :=
    closed_spatial_second_limit_of_jets hS hI f g hf hg hconv hx ht v w
  have hsmooth (q : ComplexVector n × ℝ → ℝ)
      (hq : ContDiffOn ℝ ∞ q (S ×ˢ I)) : ContDiffAt ℝ 2 (fun z => q (z, t)) x :=
    ((hq.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)).contDiffAt
      (hS.mem_nhds hx)).of_le (by simp)
  have hRF (m : ℕ) := (LeafProofs.L18Aux.leviMatrix_entry_re_im (hsmooth (f m) (hf m)) stdVec i j).1
  have hIF (m : ℕ) := (LeafProofs.L18Aux.leviMatrix_entry_re_im (hsmooth (f m) (hf m)) stdVec i j).2
  have hRG := (LeafProofs.L18Aux.leviMatrix_entry_re_im (hsmooth g hg) stdVec i j).1
  have hIG := (LeafProofs.L18Aux.leviMatrix_entry_re_im (hsmooth g hg) stdVec i j).2
  have hre : Tendsto (fun m => (leviC (fun z => f m (z, t)) x i j).re) atTop
      (𝓝 ((leviC (fun z => g (z, t)) x i j).re)) := by
    simpa only [leviC, hRF, hRG] using
      ((hsecond (stdVec j) (stdVec i)).add
        (hsecond (Complex.I • stdVec j) (Complex.I • stdVec i))).const_mul (1 / 4 : ℝ)
  have him : Tendsto (fun m => (leviC (fun z => f m (z, t)) x i j).im) atTop
      (𝓝 ((leviC (fun z => g (z, t)) x i j).im)) := by
    simpa only [leviC, hIF, hIG] using
      ((hsecond (stdVec j) (Complex.I • stdVec i)).sub
        (hsecond (Complex.I • stdVec j) (stdVec i))).const_mul (1 / 4 : ℝ)
  have hp := hre.prodMk_nhds him
  have h := Complex.equivRealProdCLM.symm.continuous.continuousAt.tendsto.comp hp
  simpa only [Function.comp_def, Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using h

end Yau.NodeProofs.F01Aux
