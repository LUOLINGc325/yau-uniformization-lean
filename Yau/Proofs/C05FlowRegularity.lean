import Yau.Proofs.C05CompleteFlowMetric

/-! Positive-time joint scalar regularity is obtained from the same original rho.
No time regularity of a chosen chart family is required. -/

open scoped Manifold Topology ContDiff
noncomputable section

namespace Yau.Proofs.C05Aux
open Yau Blueprint Set
open C04Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamily_hMat_contDiffOn (h : ℝ → HermitianField M) {I : Set ℝ}
    (hh : MetricFamilySmooth h I) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => hMat (h p.2) x p.1 i j)
      (chartTarget x ×ˢ I) := by
  simp_rw [hMat_from_real_coefficients]
  have h₁ := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hh x (i, 0) (j, 0)).div_const 2)
  have h₂ := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hh x (i, 0) (j, 1)).div_const 2)
  convert h₁.sub ((contDiffOn_const (c := Complex.I)).mul h₂) using 1
  funext p
  simp [Complex.ofReal_div]

theorem localizedFlow_scalar_smoothSpaceTime (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ) :
    SmoothSpaceTime (fun y t => scalarCurvature (h t) y) (Ioi 0) := by
  intro x
  let F : ComplexVector n × ℝ → ℝ := fun p => ρ (chartInv x p.1) p.2
  let O : Set (ComplexVector n × ℝ) := chartTarget x ×ˢ Ioi 0
  have hO : IsOpen O := (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi
  have hc : ContDiffOn ℝ ∞ F O := (hf.2.2.2.1 x).mono (prod_mono_right Ioi_subset_Ici_self)
  have he : ∀ p ∈ O, scalarCurvature (h p.2) (chartInv x p.1) =
      fderiv ℝ F p (0, 1) := by
    intro p hp
    have hd := (hc.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
    have hline : HasDerivAt (fun s : ℝ => (p.1, s)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt p.2 hline
    exact (rho_hasDerivAt X o h U P ρ hf (chartInv x p.1) hp.2).unique hcomp
  have hdc : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (0, 1)) O :=
    (hc.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  exact hdc.congr he

end Yau.Proofs.C05Aux
