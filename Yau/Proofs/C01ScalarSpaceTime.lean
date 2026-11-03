import Yau.Proofs.C01ScalarMetricHarnack

/-! The original scalar curvature is genuinely smooth in space and
positive time, as the time derivative of the original smooth potential P. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_spacetime_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => scalarCurvature (h p.2) (chartInv x p.1))
      (chartTarget x ×ˢ Set.Ioi 0) := by
  let F : ComplexVector n × ℝ → ℝ := fun p => P (chartInv x p.1) p.2
  let S : Set (ComplexVector n × ℝ) := chartTarget x ×ˢ Set.Ioi 0
  have hS : IsOpen S := (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi
  have hF : ContDiffOn ℝ ∞ F S :=
    (hflow.2.2.1 x).mono (fun p hp => ⟨hp.1, Set.Ioi_subset_Ici_self hp.2⟩)
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F) S := hF.fderiv_of_isOpen hS (by simp)
  have hEval : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (0, 1)) S :=
    hD.clm_apply contDiffOn_const
  have hPtime := hflow
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hPt, _⟩ := hPtime
  apply hEval.neg.congr
  intro p hp
  have ht : 0 < p.2 := hp.2
  have hFD := ((hF.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hγ : HasDerivAt (fun s : ℝ => (p.1, s)) ((0 : ComplexVector n), (1 : ℝ)) p.2 := by
    simpa only [id_eq] using! (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hslice : HasDerivAt (fun s => P (chartInv x p.1) s)
      (fderiv ℝ F p (0, 1)) p.2 := by
    simpa only [Function.comp_def, F] using! hFD.comp_hasDerivAt p.2 hγ
  have horiginal := ((hPt (chartInv x p.1) p.2 ht.le).1).hasDerivAt (Ici_mem_nhds ht)
  have heq := hslice.unique horiginal
  linarith

end Yau.NodeProofs.C01Aux
