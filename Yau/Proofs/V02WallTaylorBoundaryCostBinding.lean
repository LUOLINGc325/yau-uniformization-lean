import Yau.Proofs.V02WallTaylorFamily
import Yau.Proofs.V02WallTaylorWallRegularity
import Yau.Proofs.V02WallTaylorCircleIntegral
import Yau.Proofs.V02WallTaylorOrdinaryScalar

/-! The computed ordinary-density and cleared reciprocal jet bounds give
the actual original boundaryCost C3 and operator third-derivative bound. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem boundaryCost_C3_of_density_jets {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (c : ℂ → Fin b → ℂ)
    {r O B : ℝ} (hO : 0 ≤ O) (hB : 0 ≤ B)
    (hfamily : HolomorphicDiscFamily F (wallSprayFamily d j a Ψ F c) r)
    (hboundary : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ,
      wallSprayFamily d j a Ψ F c z (circlePoint θ) ∈ boundaryRegion d j)
    (hordinary : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ,
      ‖iteratedFDeriv ℝ 3 (fun p => ordinaryBoundaryScalar d j
        (wallSprayFamily d j a Ψ F c p (circlePoint θ)) (discTime F (circlePoint θ))) z‖ ≤ O)
    (hinverse : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ,
      ‖iteratedFDeriv ℝ 3 (fun p => nativeInverseIncrement d j a Ψ (F.f (circlePoint θ))
        (p, (outerWallPhase d j a F.f θ, c (circlePoint θ)))) z‖ ≤ B) :
    ContDiffOn ℝ 3 (fun z => boundaryCost d j {F with f := wallSprayFamily d j a Ψ F c z})
      (Metric.ball (0 : ℂ) r) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖iteratedFDeriv ℝ 3 (fun p => boundaryCost d j {F with f := wallSprayFamily d j a Ψ F c p}) z‖ ≤
        O + (1 + d.T) * B := by
  have hDensity := family_boundaryDensity_contDiffOn_of_boundary hd j hF hfamily hboundary
  have hWalls := family_walls_contDiffOn_of_boundary hd j hfamily hboundary
  have hAngle : ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ => boundaryDensity d j {F with f := wallSprayFamily d j a Ψ F c p.1} (circlePoint p.2))
      (Metric.ball (0 : ℂ) r ×ˢ BoundaryAngleInterval) :=
    hDensity.mono (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  have hCost : ContDiffOn ℝ ∞
      (fun z => boundaryCost d j {F with f := wallSprayFamily d j a Ψ F c z}) (Metric.ball (0 : ℂ) r) := by
    change ContDiffOn ℝ ∞ (fun z => circleAverage (fun θ =>
      boundaryDensity d j {F with f := wallSprayFamily d j a Ψ F c z} (circlePoint θ))) _
    exact circleAverage_contDiffOn isOpen_ball hAngle
  refine ⟨hCost.of_le (by simp), fun z hz => ?_⟩
  have hT : 0 < d.T := hd.1
  have hM : 0 ≤ O + (1 + d.T) * B := by positivity
  change ‖iteratedFDeriv ℝ 3 (fun z => circleAverage (fun θ =>
    boundaryDensity d j {F with f := wallSprayFamily d j a Ψ F c z} (circlePoint θ))) z‖ ≤ _
  apply norm_iteratedFDeriv_circleAverage_le isOpen_ball hAngle hz 3 hM
  intro θ
  let D : ℂ → ℝ := fun p => boundaryDensity d j {F with f := wallSprayFamily d j a Ψ F c p} (circlePoint θ)
  let W : ℂ → ℝ := fun p => wallBase d j (wallSprayFamily d j a Ψ F c p (circlePoint θ)).1 +
    wallFiber d j (wallSprayFamily d j a Ψ F c p (circlePoint θ))
  let A : ℂ → ℝ := fun p => ordinaryBoundaryScalar d j
    (wallSprayFamily d j a Ψ F c p (circlePoint θ)) (discTime F (circlePoint θ))
  have hD : ContDiffAt ℝ 3 D z :=
    ((hDensity.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (show Set.MapsTo (fun p : ℂ => (p, (θ : ℝ))) (Metric.ball (0 : ℂ) r)
        (Metric.ball (0 : ℂ) r ×ˢ Set.univ) from fun _ hp => ⟨hp, Set.mem_univ _⟩)).contDiffAt
      (isOpen_ball.mem_nhds hz)).of_le (by simp)
  have hW : ContDiffAt ℝ 3 W z :=
    ((hWalls.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (show Set.MapsTo (fun p : ℂ => (p, (θ : ℝ))) (Metric.ball (0 : ℂ) r)
        (Metric.ball (0 : ℂ) r ×ˢ Set.univ) from fun _ hp => ⟨hp, Set.mem_univ _⟩)).contDiffAt
      (isOpen_ball.mem_nhds hz)).of_le (by simp)
  have hDA : D = fun p => A p + (1 + F.s) • W p := by
    funext p
    dsimp [D, A, W, boundaryDensity, ordinaryBoundaryScalar, wallCost, discTime]
    ring
  have hSC : ContDiffAt ℝ 3 (fun p => (1 + F.s) • W p) z :=
    (contDiffAt_const (c := 1 + F.s)).smul hW
  have hA : ContDiffAt ℝ 3 A z := by
    have hh := hD.sub hSC
    convert hh using 1
    funext p
    rw [hDA]
    change A p = (A p + (1 + F.s) * W p) - (1 + F.s) * W p
    ring
  have hWshift : W = fun p =>
      (wallBase d j (F.f (circlePoint θ)).1 + wallFiber d j (F.f (circlePoint θ))) +
        nativeInverseIncrement d j a Ψ (F.f (circlePoint θ))
          (p, (outerWallPhase d j a F.f θ, c (circlePoint θ))) := by
    funext p
    dsimp [W, nativeInverseIncrement]
    rw [wallSprayFamily_boundary_eq_nativeWallPoint hd j a hF c p θ]
    ring
  have hWbound : ‖iteratedFDeriv ℝ 3 W z‖ ≤ B := by
    rw [hWshift, iteratedFDeriv_const_shift _ _ 3 (by omega)]
    exact hinverse z hz θ
  have hAbound : ‖iteratedFDeriv ℝ 3 A z‖ ≤ O := hordinary z hz θ
  have hDjet : iteratedFDeriv ℝ 3 D z =
      iteratedFDeriv ℝ 3 A z + (1 + F.s) • iteratedFDeriv ℝ 3 W z := by
    rw [hDA]
    calc
      _ = iteratedFDeriv ℝ 3 A z + iteratedFDeriv ℝ 3 (fun p => (1 + F.s) • W p) z :=
        iteratedFDeriv_add_apply hA hSC
      _ = _ := by rw [iteratedFDeriv_const_smul_apply' (a := 1 + F.s) hW]
  have hs : |1 + F.s| ≤ 1 + d.T := by
    rw [abs_of_pos (by linarith [hF.2.2.2.1] : 0 < 1 + F.s)]
    linarith [hF.2.2.2.2.1]
  have hnorm := norm_add_le (iteratedFDeriv ℝ 3 A z) ((1 + F.s) • iteratedFDeriv ℝ 3 W z)
  rw [← hDjet, norm_smul, Real.norm_eq_abs] at hnorm
  have hmul := mul_le_mul hs hWbound (norm_nonneg _) (by linarith [hd.1] : 0 ≤ 1 + d.T)
  exact hnorm.trans (by linarith)

end Yau.Blueprint.V02WallTaylorProof
