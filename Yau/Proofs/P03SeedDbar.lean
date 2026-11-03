import Yau.Proofs.P03FiniteSeeds
import Yau.Proofs.P03Wirtinger

open scoped Manifold Topology ContDiff
open Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem wirtBar_congr_germ {f g : ComplexVector n → ℂ} {z : ComplexVector n}
    (hfg : f =ᶠ[𝓝 z] g) (v : ComplexVector n) : wirtBar f z v = wirtBar g z v := by
  unfold wirtBar
  rw [hfg.fderiv_eq]

/-- The local dbar source is identically zero near each prescribed pole,
because the seed has the actual polynomial germ there. -/
theorem polynomial_germ_eventually_wirtBar_zero {f : M.Carrier → ℂ} {p : M.Carrier}
    {P : MvPolynomial (Fin n) ℂ}
    (hfg : inChart p f =ᶠ[𝓝 (chartPt p p)]
      (fun z => MvPolynomial.eval (fun i => z i - chartPt p p i) P)) :
    ∀ᶠ z in 𝓝 (chartPt p p), ∀ v : ComplexVector n, wirtBar (inChart p f) z v = 0 := by
  have hd : fderiv ℝ (inChart p f) =ᶠ[𝓝 (chartPt p p)]
      fderiv ℝ (fun z : ComplexVector n =>
        MvPolynomial.eval (fun i => z i - chartPt p p i) P) := hfg.fderiv
  filter_upwards [hd] with z hz v
  calc
    wirtBar (inChart p f) z v =
        wirtBar (fun z : ComplexVector n =>
          MvPolynomial.eval (fun i => z i - chartPt p p i) P) z v := by
      simp only [wirtBar, hz]
    _ = 0 := wirtBar_eq_zero_of_complex_differentiable _ z v
      (centeredPolynomial_differentiable P (chartPt p p) z)

/-- The computed scalar dbar vanishes off the genuine topological support
of the original function, independently of how charts are selected. -/
theorem wirtBar_inChart_zero_of_notMem_tsupport {f : M.Carrier → ℂ}
    {p : M.Carrier} (hp : p ∉ tsupport f) (v : ComplexVector n) :
    wirtBar (inChart p f) (chartPt p p) v = 0 := by
  have hf : f =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
  have hcp : Tendsto (chartInv p) (𝓝 (chartPt p p)) (𝓝 p) := by
    change Tendsto (extChartAt (ComplexModel n) p).symm
      (𝓝 ((extChartAt (ComplexModel n) p) p)) (𝓝 p)
    simpa only [extChartAt_to_inv] using
      (continuousAt_extChartAt_symm (I := ComplexModel n) p).tendsto
  have heq : inChart p f =ᶠ[𝓝 (chartPt p p)] (fun _ => (0 : ℂ)) :=
    hf.comp_tendsto hcp
  rw [wirtBar_congr_germ heq]
  simp [wirtBar]

end Yau.NodeProofs.P03Aux
