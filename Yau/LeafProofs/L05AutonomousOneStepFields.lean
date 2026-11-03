import Yau.LeafProofs.L05AutonomousFiniteFrame
import Yau.LeafProofs.L05AutonomousSlopes
import Yau.LeafProofs.L05AutonomousPeanoMeasurableHessian
import Yau.LeafProofs.L05AutonomousHarnackOscillation

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def oneStepTimeRep {n : ℕ} (V : Point n → ℝ) : Point n → ℝ :=
  (autoClosed (0 : Space n) (15/16) 0).indicator V

def oneStepFields {n N : ℕ} (e : Fin N → Space n) (w : Point n →ᵇ ℝ)
    (V : Point n → ℝ) : Fin (N+1) → Point n → ℝ :=
  Fin.cases (fun p => -oneStepTimeRep V p)
    (fun j p => autoBilinearMap n (peanoMeasurableHessian w p) (e j) (e j))

theorem oneStepTimeRep_eq {n : ℕ} (V : Point n → ℝ)
    {p : Point n} (hp : p∈autoClosed (0 : Space n) (15/16) 0) :
    oneStepTimeRep V p=V p := Set.indicator_of_mem hp V

theorem oneStepTimeRep_measurable {n : ℕ} {V : Point n → ℝ}
    (hV : ContinuousOn V (autoClosed (0 : Space n) (15/16) 0)) :
    Measurable (oneStepTimeRep V) := by
  classical
  exact hV.measurable_piecewise continuousOn_const
    (autoClosed_isCompact (0 : Space n) (15/16) 0).measurableSet

theorem oneStep_tracePair_bilinear {n : ℕ} (e : Space n) (H : Sym n) :
    tracePair (autoRankOne e) H=autoBilinearMap n H e e := by
  rw [auto_tracePair_rankOne,autoBilinearMap_apply]

theorem oneStepFields_measurable {n N : ℕ} (e : Fin N → Space n)
    (w : Point n →ᵇ ℝ) {V : Point n → ℝ}
    (hV : ContinuousOn V (autoClosed (0 : Space n) (15/16) 0)) :
    ∀ j, Measurable (oneStepFields e w V j) := by
  refine Fin.cases (oneStepTimeRep_measurable hV).neg ?_
  intro j
  have hc : Continuous (fun A : Sym n => autoBilinearMap n A (e j) (e j)) :=
    (((autoBilinearMap n).continuous.clm_apply continuous_const).clm_apply continuous_const)
  exact hc.measurable.comp (measurable_peanoMeasurableHessian w.continuous)

theorem oneStepFields_bounded {n N : ℕ} (e : Fin N → Space n)
    (he : ∀ j, ‖e j‖=1) (w : Point n →ᵇ ℝ) (V : Point n → ℝ)
    {S : Set (Point n)} (hS : S⊆autoClosed (0 : Space n) (15/16) 0) {B : ℝ}
    (hV : ∀ p∈S, |V p|≤B)
    (hH : ∀ p∈S, ∀ v : Space n, ‖v‖=1 →
      |autoBilinearMap n (peanoMeasurableHessian w p) v v|≤B) :
    ∀ j, ∀ p∈S, |oneStepFields e w V j p|≤B := by
  refine Fin.cases ?_ ?_
  · intro p hp
    simpa only [oneStepFields,Fin.cases_zero,oneStepTimeRep_eq V (hS hp),abs_neg] using hV p hp
  · intro j p hp
    exact hH p hp (e j) (he j)

theorem oneStepFields_positive_secant {n N : ℕ} {ell L a b : ℝ}
    (hell : 0<ell) (hL : ell≤L) (e : Fin N → Space n)
    (hFrame : ∀ A∈slopeSet n ell L, ∃ beta : Fin N → ℝ,
      (∀ j, beta j∈Icc a b) ∧ A=∑ j, beta j • autoRankOne (e j))
    {F : Sym n → ℝ} (hE : globalElliptic F ell L)
    (w : Point n →ᵇ ℝ) (V : Point n → ℝ) {p q : Point n}
    (hpK : p∈autoClosed (0 : Space n) (15/16) 0)
    (hqK : q∈autoClosed (0 : Space n) (15/16) 0)
    (hp : F (peanoMeasurableHessian w p)=V p)
    (hq : F (peanoMeasurableHessian w q)=V q) :
    ∃ c : Fin (N+1) → ℝ, (∀ j, c j∈Icc (min a 1) (max b 1)) ∧
      ∑ j, c j*(oneStepFields e w V j p-oneStepFields e w V j q)=0 := by
  obtain ⟨A,hA,hSecant⟩ := auto_secant_slope hell hL hE
    (peanoMeasurableHessian w p) (peanoMeasurableHessian w q)
  obtain ⟨beta,hBeta,hRep⟩ := hFrame A hA
  have hTrace : tracePair A (peanoMeasurableHessian w p-peanoMeasurableHessian w q)=
      ∑ j, beta j*(autoBilinearMap n (peanoMeasurableHessian w p) (e j) (e j)-
        autoBilinearMap n (peanoMeasurableHessian w q) (e j) (e j)) := by
    rw [← autoTraceFunctional_apply,hRep,map_sum]
    simp only [map_smul,smul_eq_mul,autoTraceFunctional_apply,← tracePair_sub,
      oneStep_tracePair_bilinear]
  have hBalance : (∑ j, beta j*(autoBilinearMap n (peanoMeasurableHessian w p) (e j) (e j)-
      autoBilinearMap n (peanoMeasurableHessian w q) (e j) (e j)))=V p-V q := by
    rw [← hTrace,← hSecant,hp,hq]
  refine ⟨Fin.cons 1 beta,?_,?_⟩
  · refine Fin.cases ⟨min_le_right _ _,le_max_right _ _⟩ ?_
    intro j
    exact ⟨(min_le_left _ _).trans (hBeta j).1,(hBeta j).2.trans (le_max_left _ _)⟩
  · rw [Fin.sum_univ_succ]
    simp only [oneStepFields,Fin.cons_zero,Fin.cons_succ,Fin.cases_zero,Fin.cases_succ,
      one_mul,oneStepTimeRep_eq V hpK,oneStepTimeRep_eq V hqK]
    linarith only [hBalance]

end Yau.LeafProofs.L05AutonomousAux
