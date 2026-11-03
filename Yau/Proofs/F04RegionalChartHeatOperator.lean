import Yau.Proofs.F04GlobalChartHeatOperator
import Yau.Proofs.F04PhysicalCutoffSmooth
import Yau.Proofs.F04PhysicalHeatLocality
import Yau.Proofs.F04ChartOperatorLocality
import Yau.Proofs.F04SupportedCutoff

open Filter Set
open scoped Topology ContDiff Manifold Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Blueprint

/-- The actual regional physical heat equation becomes the computed
 operator in a fixed chart. A genuine spatial interior cutoff is built
 before using global chart naturality, so the raw finite-domain function
 is never assumed smooth across its spatial boundary. -/
theorem flow_heatOp_regional_fixed_chart
    {n : ℕ} (X : KahlerManifold n) (h : Yau.Blueprint.Flow X) (v : STF X) (c : Pt X)
    {Γ : Set (Pt X)} (hΓ : IsOpen Γ) {I : Set ℝ}
    (hv : ∀ a, ContDiffOn ℝ ∞ (fun p : Point n => v (chartInv a p.1) p.2)
      ((chartTarget a ∩ chartInv a ⁻¹' Γ) ×ˢ I))
    {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hOΓ : chartInv c '' closure O ⊆ Γ) :
    ∀ p ∈ O ×ˢ I,
      heatOp h I v (chartInv c p.1) p.2 = linearOp (O ×ˢ I) (flowChartPrincipal h c) (fun _ _ => 0)
        (fun q : Point n => v (chartInv c q.1) q.2) p := by
  have hKC : IsCompact (chartInv c '' closure O) := hOC.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) c).mono hOt)
  obtain ⟨ψ,N,hψ,_hcψ,hψΓ,hN,hKN,_hNΓ,hψOne,_hψRange⟩ :=
    exists_supported_smooth_cutoff (chartInv c '' closure O) Γ hKC hΓ hOΓ
  let w : STF X := fun x t => ψ x*v x t
  have hw : SmoothSpaceTime w I := physical_spatial_cutoff_smooth hΓ hψ hψΓ hv
  have he : EqOn (fun p : Pt X × ℝ => w p.1 p.2) (fun p => v p.1 p.2) (N ×ˢ I) := by
    intro p hp
    change ψ p.1*v p.1 p.2 = v p.1 p.2
    rw [hψOne p.1 hp.1,one_mul]
  have hCoordEq : EqOn (fun p : Point n => w (chartInv c p.1) p.2)
      (fun p => v (chartInv c p.1) p.2) (O ×ˢ I) := by
    intro p hp
    exact he (show (chartInv c p.1,p.2) ∈ N ×ˢ I from
      ⟨hKN (mem_image_of_mem _ (subset_closure hp.1)),hp.2⟩)
  intro p hp
  have hWslice : SmoothFn (fun x => w x p.2) := fun a => (hw a).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz,hp.2⟩)
  have hPhysical := physical_heatOp_congr_of_eqOn X h hN he
    (hKN (mem_image_of_mem _ (subset_closure hp.1))) hp.2
  have hChart := flow_heatOp_fixed_chart X h w c hp.1 (hOt (subset_closure hp.1)) I p.2 hWslice
  have hLocal := linearOp_congr_product_of_eqOn hO
    (a := flowChartPrincipal h c) (b := fun _ _ => 0) hCoordEq hp
  exact hPhysical.symm.trans (hChart.trans hLocal)

end Yau.F04Proof
