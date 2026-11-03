import Yau.Proofs.F05ExhaustionLimitEquation
import Yau.Proofs.F05LateInteriorSmooth

/-! The original same-flow geometric fields and rho bound discharge all
background budgets in the actual late interior smoothness bootstrap. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_raw_limit_smooth {O : Set (Pt X)} {A : AtlasData X.manifold}
    (hA : GenuineAtlas O A) (i : Fin A.count)
    (hCompact : IsCompact (lift A i '' Metric.closedBall 0 3))
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {l τ S T α C : ℝ} (hT : 0 < T) (hl : 0 < l) (hlτ : l < τ)
    (hτS : τ < S) (hST : S < T) (hα : 0 < α) (hα1 : α < 1) (hC : 0 < C)
    (W : STF X) (hRange : ∀ x t, t ∈ Ico 0 T → 0 ≤ W x t ∧ W x t ≤ ρ x t)
    (hSch : F05RelSchauder α (region none (9/4)) (Icc l T) (pull A i W) C)
    (hEq : F05RelativeNonlinearEquation none (9/4) l T
      (fun z => flatA (h z.2) A i z) (fun z a => flatB (h z.2) A i z a)
      (pull A i (fun x t => scalarCurvature (h t) x)) (pull A i W)) :
    ContDiffOn ℝ ∞ (pull A i W) (region none (3/2) ×ˢ Icc τ S) := by
  have hlS := hlτ.trans hτS
  have hX := F05_region_uniqueDiffOn (n := n) none (by norm_num : (0 : ℝ) < 9/4)
  have hTime : Icc l S ⊆ Icc l T := fun a ha => ⟨ha.1,ha.2.trans hST.le⟩
  have hSchS := F05_relative_schauder_restrict hX hX (uniqueDiffOn_Icc hlS) subset_rfl hTime hSch
  have hEqS := F05_relative_nonlinear_equation_restrict none
    (by norm_num : (0 : ℝ) < 9/4) (by norm_num : (0 : ℝ) < 9/4) le_rfl hlS le_rfl hST.le hSch.1 hEq
  have hh : MetricFamilySmooth h (Icc 0 T) := fun y a b =>
    (hloc.1.2.1 y a b).mono (fun q hq => ⟨hq.1,hq.2.1⟩)
  have hCoeff := F05_flat_coefficients_smooth hA h hh i
  have hR := F05_pull_spacetime_smooth hA
    (fun y a => scalarCurvature (h a) y) (F05_flow_scalar_smooth o h U P ρ hloc hT) i
  have hDataSub : Metric.ball (0 : Space n) 3 ×ˢ Icc l S ⊆ Metric.ball 0 3 ×ˢ Icc 0 T :=
    fun q hq => ⟨hq.1,hl.le.trans hq.2.1,hq.2.2.trans hST.le⟩
  obtain ⟨lam,upper,hEll⟩ := F05_flat_principal_elliptic_radius hA h
    (by norm_num : (9/4 : ℝ) < 3) hh i
  have hEllS : Elliptic (region none (9/4) ×ˢ Icc l S)
      (fun q => flatA (h q.2) A i q) lam upper :=
    ⟨hEll.1,hEll.2.1,fun q hq => hEll.2.2 q
      ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hq.1.1,
        hl.le.trans hq.2.1,hq.2.2.trans hST.le⟩⟩
  obtain ⟨B,hB,hRho⟩ := F05_flow_compact_rho_budget o h U P ρ hloc T hCompact
  have hBound : ∀ q ∈ region none (9/4) ×ˢ Icc l S, |pull A i W q| ≤ B := by
    intro q hq
    have hqt : q.2 ∈ Ico 0 T := ⟨hl.le.trans hq.2.1,hq.2.2.trans_lt hST⟩
    have hW := hRange (lift A i q.1) q.2 hqt
    have hxK : lift A i q.1 ∈ lift A i '' Metric.closedBall 0 3 := by
      refine ⟨q.1,?_,rfl⟩
      rw [Metric.mem_closedBall,dist_zero_right]
      linarith [hq.1.1]
    change |W (lift A i q.1) q.2| ≤ B
    rw [abs_of_nonneg hW.1]
    linarith [hRho (lift A i q.1) hxK q.2 ⟨hqt.1,hqt.2.le⟩]
  have hSmooth := F05_late_interior_positive_smooth hlτ hτS hα hα1 hC.le hB.le
    (hCoeff.1.mono hDataSub) (fun a => (hCoeff.2 a).mono hDataSub) (hR.mono hDataSub)
    hEllS hBound hSchS hEqS
  exact hSmooth

end Yau.Proofs.F05Aux
