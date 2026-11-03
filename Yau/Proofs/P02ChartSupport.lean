import Yau.Proofs.P02DistanceSupport
import Yau.LeafProofs.L22Locality

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L22Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem inChart_transition_eventuallyEq (p x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget p) (hx : chartInv p z=x) (s : M.Carrier → ℝ) :
    inChart p s =ᶠ[𝓝 z] (inChart x s) ∘ (fun u => chartPt x (chartInv p u)) := by
  have hI : ContinuousAt (chartInv p) z := continuousAt_extChartAt_symm'' hz
  have hsrc : ∀ᶠ u in 𝓝 z, chartInv p u ∈ (extChartAt (ComplexModel n) x).source :=
    hI.preimage_mem_nhds (by rw [hx]; exact extChartAt_source_mem_nhds x)
  filter_upwards [hsrc] with u hu
  change s (chartInv p u) = s (chartInv x (chartPt x (chartInv p u)))
  exact (congrArg s ((extChartAt (ComplexModel n) x).left_inv hu)).symm

theorem inChart_support_transport (h : HermitianField M)
    (p x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget p)
    (hx : chartInv p z=x) (s : M.Carrier → ℝ) (ε : ℝ)
    (hs : ContDiffAt ℝ 2 (inChart x s) (chartPt x x))
    (hLevi : ∀ v, ε*realMetricInChart h x (chartPt x x) v v ≤
      complexLeviQuadratic (inChart x s) (chartPt x x) v) :
    ContDiffAt ℝ 2 (inChart p s) z ∧
      ∀ v, ε*realMetricInChart h p z v v ≤ complexLeviQuadratic (inChart p s) z v := by
  have hx' : chartInv p z ∈ (extChartAt (ComplexModel n) x).source := by
    rw [hx]
    exact mem_extChartAt_source x
  let T : ComplexVector n → ComplexVector n := fun u => chartPt x (chartInv p u)
  have hT : ContDiffAt ℂ 2 T z := (L18Aux.chartTransition_contDiffAt p x hz hx').of_le (by simp)
  have hTz : T z=chartPt x x := by dsimp only [T]; rw [hx]
  have hsT : ContDiffAt ℝ 2 (inChart x s) (T z) := hTz.symm ▸ hs
  have HE := inChart_transition_eventuallyEq p x hz hx s
  have HC : ContDiffAt ℝ 2 ((inChart x s) ∘ T) z := hsT.comp z (hT.restrict_scalars ℝ)
  refine ⟨HC.congr_of_eventuallyEq HE,?_⟩
  intro v
  have Hlev : complexLeviQuadratic (inChart p s) z v =
      complexLeviQuadratic (inChart x s) (chartPt x x) (fderiv ℂ T z v) := by
    calc
      _ = complexLeviQuadratic ((inChart x s) ∘ T) z v := by
        unfold complexLeviQuadratic
        rw [HE.fderiv.fderiv_eq]
      _ = _ := by rw [complexLeviQuadratic_comp hT hsT,hTz]
  have hreal : fderiv ℝ T z v=fderiv ℂ T z v := by
    exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L v)
      ((hT.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ)
  have Hmetric := realMetricInChart_change h p x hz hx' v v
  change realMetricInChart h p z v v =
    realMetricInChart h x (T z) (fderiv ℝ T z v) (fderiv ℝ T z v) at Hmetric
  rw [hTz,hreal] at Hmetric
  rw [Hlev,Hmetric]
  exact hLevi (fderiv ℂ T z v)

end Yau.NodeProofs.P02Aux
