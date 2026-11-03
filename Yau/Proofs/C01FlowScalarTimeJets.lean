import Yau.Proofs.C01FlowTimeJets

/-! The original scalar curvature is smooth in positive time, by its
actual inverse-metric Ricci trace. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_time_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun t => scalarCurvature (h t) x) (Set.Ioi 0) := by
  have hK (i j : Fin n) :
      ContDiffOn ℝ ∞ (fun t => (gMat (h t) x)⁻¹ i j) (Set.Ioi 0) := by
    have hK₀ : ContDiffOn ℝ ∞ (fun t => (gMat (h t) x)⁻¹ i j) (Set.Ici 0) :=
      (Alignment.Y03Proof.metricFamily_hMat_inv_contDiffOn hflow.1.2.1 x i j).comp
        (contDiffOn_const.prodMk contDiffOn_id)
        (fun t ht => ⟨mem_extChartAt_target (I := ComplexModel n) x, ht⟩)
    exact hK₀.mono Set.Ioi_subset_Ici_self
  change ContDiffOn ℝ ∞ (fun t =>
    (∑ i, ∑ j, (gMat (h t) x)⁻¹ i j * ricci (h t) x j i).re) (Set.Ioi 0)
  apply Complex.reCLM.contDiff.comp_contDiffOn
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    (hK i j).mul (localizedFlow_ricci_time_contDiffOn hflow x j i)

theorem localizedFlow_scalar_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => scalarCurvature (h s) x)
      (deriv (fun s => scalarCurvature (h s) x) t) t :=
  ((localizedFlow_scalar_time_contDiffOn hflow x).contDiffAt
    (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp) |>.hasDerivAt

end Yau.NodeProofs.C01Aux
