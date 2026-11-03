import Yau.Proofs.F03KernelProductCoefficients

/-! Compact actual packed chart buffers and internally obtained metric coefficients. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem kernelProductSpace_precompact (Ox Oy : Set (Space n))
    (hx : IsCompact (closure Ox)) (hy : IsCompact (closure Oy)) :
    IsCompact (closure (kernelProductSpace Ox Oy)) := by
  have hC := (hx.prod hy).image (kernelPairPack n).continuous
  apply hC.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hC.isClosed
  exact image_mono (prod_mono subset_closure subset_closure)

theorem kernelHeatProductCoeff_smooth (g : SmoothMetric M) (x y : M.Carrier)
    (Ox Oy : Set (Space n)) (I : Set ℝ) (hxt : Ox ⊆ chartTarget x) (hyt : Oy ⊆ chartTarget y) :
    SmoothCoefficients (kernelProductSpace Ox Oy ×ˢ I)
      (kernelProductCoeff (scalarHeatChartCoeff g x) (scalarHeatChartCoeff g y)) (fun _ _ => 0) :=
  kernelProductCoeff_smooth Ox Oy I _ _ (scalarHeatChartCoeff_smooth g x hxt I)
    (scalarHeatChartCoeff_smooth g y hyt I)

theorem kernelHeatProductCoeff_elliptic (g : SmoothMetric M) (x y : M.Carrier)
    (Ox Oy : Set (Space n)) (I : Set ℝ) (hxc : IsCompact (closure Ox)) (hyc : IsCompact (closure Oy))
    (hxt : closure Ox ⊆ chartTarget x) (hyt : closure Oy ⊆ chartTarget y) :
    ∃ lam upper : ℝ, Elliptic (kernelProductSpace Ox Oy ×ˢ I)
      (kernelProductCoeff (scalarHeatChartCoeff g x) (scalarHeatChartCoeff g y)) lam upper := by
  obtain ⟨lx,ux,hx⟩ := scalarHeatChartCoeff_elliptic g x hxc hxt I
  obtain ⟨ly,uy,hy⟩ := scalarHeatChartCoeff_elliptic g y hyc hyt I
  have hxO : Elliptic (Ox ×ˢ I) (scalarHeatChartCoeff g x) lx ux :=
    ⟨hx.1,hx.2.1,fun p hp => hx.2.2 p ⟨subset_closure hp.1,hp.2⟩⟩
  have hyO : Elliptic (Oy ×ˢ I) (scalarHeatChartCoeff g y) ly uy :=
    ⟨hy.1,hy.2.1,fun p hp => hy.2.2 p ⟨subset_closure hp.1,hp.2⟩⟩
  exact ⟨min lx ly/2,max ux uy/2,kernelProductCoeff_elliptic Ox Oy I _ _ lx ux ly uy hxO hyO⟩

end Yau.Proofs.F03Aux
