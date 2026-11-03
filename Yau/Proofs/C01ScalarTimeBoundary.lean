import Yau.Proofs.C01FlowScalarTimeJets

/-! The original one-sided smooth scalar potential gives continuity of
the same scalar curvature at time zero, without a curvature bound input. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_P_time_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) :
    ContDiffOn ℝ ∞ (P x) (Set.Ici 0) := by
  have hP := hflow.2.2.1
  have hcenter : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hp : ContDiffOn ℝ ∞
      (fun t => P (chartInv x (chartPt x x)) t) (Set.Ici 0) :=
    (hP x).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun t ht => ⟨mem_extChartAt_target (I := ComplexModel n) x, ht⟩)
  simpa only [hcenter, Function.comp_def] using! hp

theorem localizedFlow_scalar_time_contDiffOn_nonneg
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun t => scalarCurvature (h t) x) (Set.Ici 0) := by
  have hPtime := localizedFlow_P_time_contDiffOn hflow x
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hdP, _⟩ := hflow
  have hder : ContDiffOn ℝ ∞ (derivWithin (P x) (Set.Ici 0)) (Set.Ici 0) :=
    hPtime.derivWithin (uniqueDiffOn_Ici 0) (by simp)
  apply hder.neg.congr
  intro t ht
  rw [((hdP x t ht).1.derivWithin (uniqueDiffOn_Ici 0 t ht))]
  simp

end Yau.NodeProofs.C01Aux
