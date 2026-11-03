import Yau.Proofs.V03TimeScalars
import Yau.Proofs.V02WallTaylorSprayScalars

/-! The ordinary part of the original boundary cost retains its genuine
one-sided metric and localization time dependence. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q b : ℕ} {X : KahlerManifold n}

def ordinaryBoundaryScalar (d : VariationData X q) (j : ℕ)
    (y : CotangentPoint X.manifold) (t : ℝ) : ℝ :=
  dualNorm (d.h t) y.1 y.2 + baseCost d j y.1 t

theorem ordinaryBoundaryScalar_chart_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      ordinaryBoundaryScalar d j (cotangentChartInv x p.1) p.2)
      (cotangentTarget x ×ˢ Set.Icc 0 d.T) := by
  have hN := (metricFamily_dualNormChart_contDiffOn hd.2.2.1.1.1.2.1 x).mono
    (show cotangentTarget x ×ˢ Set.Icc 0 d.T ⊆ cotangentTarget x ×ˢ Set.Ici 0 from
      fun _ hp => ⟨hp.1, hp.2.1⟩)
  have hNa : ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      dualNorm (d.h p.2) (cotangentChartInv x p.1).1 (cotangentChartInv x p.1).2)
      (cotangentTarget x ×ˢ Set.Icc 0 d.T) :=
    hN.congr (fun p hp => dualNorm_cotangentChartInv (d.h p.2) x hp.1)
  have hproj : ContDiff ℝ ∞ (fun p : CotangentCoord n × ℝ => (p.1.1, p.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  have hQ := (hd.2.2.2.2.2.2.2.2.1.1 x).comp hproj.contDiffOn
    (show Set.MapsTo (fun p : CotangentCoord n × ℝ => (p.1.1, p.2))
      (cotangentTarget x ×ˢ Set.Icc 0 d.T) (chartTarget x ×ˢ Set.Icc 0 d.extendedT) from
      fun p hp => ⟨hp.1.1, hp.2.1, hp.2.2.trans hd.2.1.le⟩)
  have hρ := ((hd.2.2.2.2.2.2.2.2.2.1 j).1 x).comp hproj.contDiffOn
    (show Set.MapsTo (fun p : CotangentCoord n × ℝ => (p.1.1, p.2))
      (cotangentTarget x ×ˢ Set.Icc 0 d.T) (chartTarget x ×ˢ Set.Icc 0 d.extendedT) from
      fun p hp => ⟨hp.1.1, hp.2.1, hp.2.2.trans hd.2.1.le⟩)
  exact hNa.add ((contDiffOn_const.mul hQ).add hρ)

def sprayOrdinaryScalar (d : VariationData X q) (j : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) (p : (CotangentCoord n × (Fin b → ℂ)) × ℝ) : ℝ :=
  ordinaryBoundaryScalar d j (cotangentChartInv x (sprayCoordinate Ψ x p.1)) p.2

theorem sprayOrdinaryScalar_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {x : Pt X} {S : Set (CotangentCoord n × (Fin b → ℂ))}
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) S) :
    ContDiffOn ℝ ∞ (sprayOrdinaryScalar d j Ψ x)
      ((S ∩ (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x) ×ˢ Set.Icc 0 d.T) := by
  have hcoords := (hΨ.restrict_scalars ℝ).mono (Set.inter_subset_left :
    S ∩ (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x ⊆ S)
  have hh : ContDiffOn ℝ ∞
      (fun p : (CotangentCoord n × (Fin b → ℂ)) × ℝ => (sprayCoordinate Ψ x p.1, p.2))
      ((S ∩ (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x) ×ˢ Set.Icc 0 d.T) :=
    (hcoords.comp (f := fun p : (CotangentCoord n × (Fin b → ℂ)) × ℝ => p.1)
      contDiffOn_fst (fun _ hp => hp.1)).prodMk contDiffOn_snd
  exact (ordinaryBoundaryScalar_chart_contDiffOn hd j x).comp
    (f := fun p : (CotangentCoord n × (Fin b → ℂ)) × ℝ => (sprayCoordinate Ψ x p.1, p.2)) hh (fun p hp => ⟨hp.1.2, hp.2⟩)

theorem sprayOrdinaryScalar_eq_actual (d : VariationData X q) (j : ℕ)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {p : (CotangentCoord n × (Fin b → ℂ)) × ℝ}
    (hsource : (Ψ (NativeCotangentPoint.mk (cotangentChartInv x p.1.1), p.1.2)).val ∈ cotangentSource x) :
    sprayOrdinaryScalar d j Ψ x p =
      ordinaryBoundaryScalar d j (Ψ (NativeCotangentPoint.mk (cotangentChartInv x p.1.1), p.1.2)).val p.2 :=
  congrArg (fun y => ordinaryBoundaryScalar d j y p.2) (cotangentChart_left_inv x hsource)

end Yau.Blueprint.V02WallTaylorProof
