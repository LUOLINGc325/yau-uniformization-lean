import Yau.Proofs.C02ParallelSmooth

/-! Smooth insertion of two actual vectors in one fixed fiber of the
Whitney-sum bundle, using the genuine inverse bundle chart. -/

noncomputable section
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem transportInitialPair_smooth
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (p : M.Carrier)
    (v w : D →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ContMDiff 𝓘(ℝ, D) (realTransportModel n) ∞
      (fun z : D => (⟨p, (v z, w z)⟩ : realTransportBundle M)) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  let q₀ : realTransportBundle M := ⟨p, (0, 0)⟩
  let e := extChartAt (realTransportModel n) q₀
  let V := (realTangentCoords p p).comp v
  let W := (realTangentCoords p p).comp w
  let κ : D → ComplexVector n × (ComplexVector n × ComplexVector n) :=
    fun z => (chartPt p p, (V z, W z))
  have hκ : ContMDiff 𝓘(ℝ, D)
      𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) ∞ κ :=
    contMDiff_const.prodMk_space (V.contMDiff.prodMk_space W.contMDiff)
  have heq : ∀ z : D, e.symm (κ z) = (⟨p, (v z, w z)⟩ : realTransportBundle M) := by
    intro z
    have hsrc : (⟨p, (v z, w z)⟩ : realTransportBundle M) ∈ e.source :=
      (realTransportChart_source q₀ _).mpr (mem_chart_source _ _)
    have hcode : e (⟨p, (v z, w z)⟩ : realTransportBundle M) = κ z :=
      realTransportChart_eq_extChartAt q₀ _ (mem_chart_source _ _)
    rw [← hcode]
    exact e.left_inv hsrc
  intro z
  have htarget : κ z ∈ e.target :=
    (realTransportChart_target q₀ _).mpr (mem_extChartAt_target p)
  have hInv : ContMDiffAt 𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n))
      (realTransportModel n) ∞ e.symm (κ z) :=
    (contMDiffOn_extChartAt_symm q₀).contMDiffAt
      ((isOpen_extChartAt_target q₀).mem_nhds htarget)
  have hc := hInv.comp z hκ.contMDiffAt
  have hfun : (fun a => e.symm (κ a)) =
      (fun a : D => (⟨p, (v a, w a)⟩ : realTransportBundle M)) := funext heq
  rw [← hfun]
  exact hc

end Yau.Blueprint.C02Proof
