import Yau.Proofs.D03ImageExtensions
import Yau.Proofs.D03GermJets

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace Yau.Proofs.D03Aux
open Yau

/-- Actual iterated derivatives commute with the actual coordinate projection.
The proof applies the continuous-linear chain rule to the Frechet derivative. -/
theorem iteratedDeriv_piLp_component {q : ℕ}
    (F : ℂ → ComplexVector q) (hF : AnalyticAt ℂ F 0) (j : ℕ) (i : Fin q) :
    iteratedDeriv j (fun z => F z i) 0 = (iteratedDeriv j F 0) i := by
  have hFC : ContDiffAt ℂ j F 0 := hF.contDiffAt
  have heq := (PiLp.proj 2 (fun _ : Fin q => ℂ) (𝕜 := ℂ) i).iteratedFDeriv_comp_left hFC (i := j) le_rfl
  exact congrArg (fun D : ContinuousMultilinearMap ℂ (fun _ : Fin j => ℂ) ℂ =>
    D (fun _ => 1)) heq

/-- The proved vector-valued L²/Cauchy estimate gives each scalar germ jet of
our actual image extensions, including derivative order zero. -/
theorem holomorphic_l2_component_iteratedDeriv_tendsto {q : ℕ}
    (R : ℝ) (hR : 0 < R) (F : ℂ → ComplexVector q) (Fn : ℕ → ℂ → ComplexVector q)
    (hF : DifferentiableOn ℂ F (ball 0 R))
    (hFn : ∀ n, DifferentiableOn ℂ (Fn n) (ball 0 R))
    (hfinite : ∀ n, (∫⁻ z in ball (0 : ℂ) R,
      ENNReal.ofReal (‖Fn n z - F z‖ ^ 2) ∂volume) < ⊤)
    (hconv : Tendsto (fun n => ∫⁻ z in ball (0 : ℂ) R,
      ENNReal.ofReal (‖Fn n z - F z‖ ^ 2) ∂volume) atTop (𝓝 0)) :
    ∀ (i : Fin q) (j : ℕ), Tendsto (fun n => iteratedDeriv j (fun z => Fn n z i) 0)
      atTop (𝓝 (iteratedDeriv j (fun z => F z i) 0)) := by
  have hF0 : AnalyticAt ℂ F 0 := hF.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hFn0 (n : ℕ) : AnalyticAt ℂ (Fn n) 0 := (hFn n).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  intro i j
  have hnEq : (fun n => iteratedDeriv j (fun z => Fn n z i) 0) =
      (fun n => (iteratedDeriv j (Fn n) 0) i) :=
    funext fun n => iteratedDeriv_piLp_component (Fn n) (hFn0 n) j i
  rw [hnEq, iteratedDeriv_piLp_component F hF0 j i]
  exact ((PiLp.proj 2 (fun _ : Fin q => ℂ) (𝕜 := ℂ) i).continuous.continuousAt.tendsto).comp
    (holomorphic_l2_iteratedDeriv_tendsto R hR F Fn hF hFn hfinite hconv j)

/-- Finite products of the actual scalar derivative limits give convergence of
every concrete jet. This includes empty ranks and jet order zero. -/
theorem jet_tendsto_of_component_derivatives
    (q : ℕ) (gseq : ℕ → Fin q → AnalyticGerm) (g : Fin q → AnalyticGerm)
    (h : ∀ (i : Fin q) (j : ℕ), Tendsto (fun n => germDerivative j (gseq n i))
      atTop (𝓝 (germDerivative j (g i)))) :
    ∀ k : ℕ, Tendsto (fun n => jet q k (gseq n)) atTop (𝓝 (jet q k g)) := by
  intro k
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact h i j.val

end Yau.Proofs.D03Aux
