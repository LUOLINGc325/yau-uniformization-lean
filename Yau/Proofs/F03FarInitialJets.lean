import Yau.Proofs.F03BoundedHeatLocalization
import Yau.Proofs.F03BoundedHeatChartEquation
import Yau.Proofs.F03AffineTensorRestriction
import Yau.Proofs.F04ZeroPastJets

/-! Actual far-source compact spatial jets vanish at the initial face. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates HeatConcreteBindings HeatTargetCandidates LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000

theorem dirichletMinimalBoundedHeat_far_initial_jets
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ y,|f y| ≤ B)
    (η : ScalarEnergyDomain g μ hμ) (hηrange : ∀ y,η y ∈ Icc (0 : ℝ) 1)
    (W : Set M.Carrier) (hW : IsOpen W) (hηone : ∀ y ∈ W,η y=1)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hKc : IsCompact K)
    (hKt : K ⊆ chartTarget a) (hKW : ∀ z ∈ K,chartInv a z ∈ W)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ,0 < δ ∧ ∀ t,0 < t → t < δ → ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun w => boundedKernelEvolution μ
        (dirichletMinimalKernelCandidate g hK μ hμ O hO) (fun y => (1-η y)*f y) t (chartInv a w)) z‖ < ε := by
  let F := fun y => (1-η y)*f y
  have hη : AEStronglyMeasurable (fun y => η y) μ :=
    (LeafProofs.L18Aux.continuous_of_smoothFn η.2.1).aestronglyMeasurable
  have hF : AEStronglyMeasurable F μ := (aestronglyMeasurable_const.sub hη).mul hf
  have hFb : ∀ y,|F y| ≤ B := by
    intro y
    have hOne : |1-η y| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hηrange y).2)]
      linarith [(hηrange y).1]
    exact (abs_mul (1-η y) (f y)).le.trans
      ((mul_le_mul_of_nonneg_right hOne (abs_nonneg _)).trans (by simpa using hBound y))
  let u : Point n → ℝ := fun p => boundedKernelEvolution μ
    (dirichletMinimalKernelCandidate g hK μ hμ O hO) F p.2 (chartInv a p.1)
  let R0 := {z | z ∈ chartTarget a ∧ chartInv a z ∈ W}
  have hR0 : IsOpen R0 := dirichletChartInterior_open W hW a
  have hKR0 : K ⊆ R0 := fun z hz => ⟨hKt hz,hKW z hz⟩
  obtain ⟨P,hP,hKP,hP0,hPc⟩ := exists_open_between_and_isCompact_closure hKc hR0 hKR0
  obtain ⟨V,hV,hKV,hVP,hVc⟩ := exists_open_between_and_isCompact_closure hKc hP hKP
  have hPt : closure P ⊆ chartTarget a := fun z hz => (hP0 hz).1
  have hVt : V ⊆ chartTarget a := subset_closure.trans (hVP.trans (subset_closure.trans hPt))
  have hu : ContDiffOn ℝ ∞ u (P ×ˢ Ioo (0 : ℝ) 2) :=
    (dirichletMinimalBoundedHeat_smooth g hK μ hμ O hO F hF B hB hFb a).mono
      (fun p hp => ⟨hPt (subset_closure hp.1),hp.2.1⟩)
  have hClass : ∀ p ∈ P ×ˢ Ioo (0 : ℝ) 2,
      linearOp (P ×ˢ Icc (0 : ℝ) 2) (scalarHeatChartCoeff g a) (fun _ _ => 0) u p=0 :=
    fun p hp => dirichletMinimalBoundedHeat_chart_equation g hK μ hμ O hO F hF B hB hFb
      a P hP hPc hPt 2 p hp
  obtain ⟨lam,upper,hEll⟩ := scalarHeatChartCoeff_elliptic g a hPc hPt (univ : Set ℝ)
  have hClosedSmooth := scalarHeatChartCoeff_smooth g a (subset_closure.trans hPt) (Icc (0 : ℝ) 2)
  have hClosedEll : Elliptic (P ×ˢ Icc (0 : ℝ) 2) (scalarHeatChartCoeff g a) lam upper :=
    ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p ⟨subset_closure hp.1,mem_univ _⟩⟩
  have hCrossSmooth := scalarHeatChartCoeff_smooth g a hVt (Ioo (-1 : ℝ) 1)
  have hCrossEll : Elliptic (V ×ˢ Ioo (-1 : ℝ) 1) (scalarHeatChartCoeff g a) lam upper :=
    ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p ⟨subset_closure (hVP (subset_closure hp.1)),mem_univ _⟩⟩
  obtain ⟨C,hC,hRate⟩ := (dirichletMinimalBoundedHeat_far_source g hK μ hμ O hO f hf B hB hBound η hηrange).2.2.2
  have hGrowth : ∀ Z : Set (Space n),IsOpen Z → IsCompact (closure Z) → closure Z ⊆ P →
      ∃ K : ℝ,0 ≤ K ∧ ∀ x ∈ Z,∀ t ∈ Ioo (0 : ℝ) 2,|u (x,t)| ≤ K*t := by
    intro Z _hZ _hZc hZP
    refine ⟨C,hC.le,fun x hx t ht => ?_⟩
    have hxW : chartInv a x ∈ W := (hP0 (subset_closure (hZP (subset_closure hx)))).2
    exact hRate t ht.1 (chartInv a x) (hηone _ hxW)
  have hZero := F04Proof.classical_homogeneous_zeroPast_smooth (complexManifold_dimension_pos M)
    hP hClosedSmooth hClosedEll hu hClass hGrowth V 1 hV hVc hVP (by norm_num) (by norm_num)
    hCrossSmooth hCrossEll
  obtain ⟨δ,hδ,hδ1,hJets⟩ := F04Proof.zeroPast_uniform_compact_initial_jets hV (by norm_num : (0 : ℝ) < 1)
    hZero.1 K hKc hKV m hε
  refine ⟨δ,hδ,fun t ht htd z hz => ?_⟩
  have hp : (z,t) ∈ P ×ˢ Ioo (0 : ℝ) 2 :=
    ⟨hVP (subset_closure (hKV hz)),ht,by linarith⟩
  exact (norm_iteratedFDeriv_spatial_slice_le (P ×ˢ Ioo (0 : ℝ) 2) (hP.prod isOpen_Ioo)
    u hu z t hp m).trans_lt (hJets t ⟨ht,htd⟩ z hz)

end Yau.Proofs.F03Aux
