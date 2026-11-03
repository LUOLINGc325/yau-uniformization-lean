import Yau.Proofs.V03JointGaussTwoForm
import Yau.Proofs.V03TwoFormPullback

/-! Smoothness of the actual fixed-chart Gauss pullback, including native
within derivatives on the original closed parameter set. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

theorem fixedGaussTwoForm_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (x : M.Carrier) {S : Set P} (hS : UniqueDiffOn ℂ S)
    {c : P → CotangentCoord n} (hc : ContDiffOn ℂ ∞ c S)
    (hmap : Set.MapsTo c S (cotangentTarget x)) :
    ContDiffOn ℝ ∞ (fun p =>
      (scalarLeviTwoForm (gaussPotential G x) (c p)).compContinuousLinearMap
        ((fderivWithin ℂ c S p).restrictScalars ℝ)) S := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hpot : ContDiffOn ℝ ∞ (gaussPotential G x) (cotangentTarget x) :=
    fun z hz => (gaussPotential_contDiffAt hG x hz).contDiffWithinAt
  have hA := (scalarLeviBilinear_contDiffOn hopen hpot).comp (hc.restrict_scalars ℝ) hmap
  have hD := hc.fderivWithin hS (m := ∞) (by simp)
  have hT : ContDiffOn ℝ ∞
      (fun p => (fderivWithin ℂ c S p).restrictScalars ℝ) S := by
    apply contDiffOn_clm_apply.mpr
    intro v
    exact (hD.clm_apply (contDiffOn_const (c := v))).restrict_scalars ℝ
  have hB := bilinearTwoForm_contDiffOn (pullbackBilinear_contDiffOn hA hT)
  simpa only [bilinearTwoForm_pullback, scalarLeviTwoForm, Function.comp_def] using hB

end Yau.Blueprint.V03Proof
