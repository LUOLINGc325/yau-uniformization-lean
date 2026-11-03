import Yau.Proofs.V03WallTensor
import Yau.Proofs.V03MetricTime

/-! The actual boundary symbol is Hermitian. All native Hessians are
computed from the original time-dependent norm and reciprocal walls. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem boundaryCost_chart_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {y : CotangentPoint X.manifold} (hy : y ∈ boundaryRegion d j)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.extendedT) (s : ℝ) :
    ContDiffAt ℝ ∞ (fun z => let v := cotangentChartInv y.1 z
      dualNorm (d.h t) v.1 v.2 + wallCost d j v t s) (cotangentChart y.1 y) := by
  let x := y.1
  let z0 := cotangentChart x y
  have hz : z0 ∈ cotangentTarget x := cotangentChart_mapsTo x (mem_extChartAt_source x)
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hp : ContDiff ℝ ∞ (fun z : CotangentCoord n => (z, t)) :=
    contDiff_id.prodMk contDiff_const
  have hnormOn : ContDiffOn ℝ ∞
      (fun z => dualNorm (d.h t) (cotangentChartInv x z).1 (cotangentChartInv x z).2)
      (cotangentTarget x) := by
    have hh := (metricFamily_dualNormChart_contDiffOn hd.2.2.1.1.1.2.1 x).comp hp.contDiffOn
      (fun z hz => ⟨hz, ht.1⟩)
    exact hh.congr (fun z hz => dualNorm_cotangentChartInv (d.h t) x hz)
  have hscalar {b : Pt X → ℝ → ℝ} (hb : SmoothSpaceTime b (Set.Icc 0 d.extendedT)) :
      ContDiffOn ℝ ∞ (fun z : CotangentCoord n => b (cotangentChartInv x z).1 t)
        (cotangentTarget x) := by
    exact (hb x).comp (contDiff_fst.prodMk contDiff_const).contDiffOn
      (fun z hz => ⟨hz.1, ht⟩)
  have hbase : ContDiffOn ℝ ∞ (fun z => baseCost d j (cotangentChartInv x z).1 t)
      (cotangentTarget x) :=
    (contDiffOn_const.mul (hscalar hd.2.2.2.2.2.2.2.2.1.1)).add
      (hscalar (hd.2.2.2.2.2.2.2.2.2.1 j).1)
  have hb := (deltaBase_chart_contDiffOn hd j x).contDiffAt (hopen.mem_nhds hz)
  have hf := (deltaFiber_chart_contDiffOn hd j x).contDiffAt (hopen.mem_nhds hz)
  have hround : cotangentChartInv x z0 = y := cotangentChart_left_inv x (mem_extChartAt_source x)
  have hpos := setup_index_bounds hd j
  have hb0 : deltaBase d j (cotangentChartInv x z0).1 ≠ 0 := by
    rw [hround]
    exact (deltaBase_pos (setup_wallProfiles hd) hpos.1 hy.1).ne'
  have hf0 : deltaFiber d j (cotangentChartInv x z0) ≠ 0 := by
    rw [hround]
    exact (deltaFiber_pos (setup_wallProfiles hd) hpos.2 hy.2).ne'
  have hw := (contDiffAt_const (c := 1 + s)).mul
    (((hb.inv hb0).sub (contDiffAt_const (c := (1 : ℝ)))).add
      ((hf.inv hf0).sub (contDiffAt_const (c := (1 : ℝ)))))
  have htotal := (hnormOn.contDiffAt (hopen.mem_nhds hz)).add
    ((hbase.contDiffAt (hopen.mem_nhds hz)).add hw)
  simpa only [wallCost, wallBase, wallFiber, Pi.inv_apply, x, z0] using htotal

theorem boundaryHessian_isHermitian {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    (boundaryHessian d j F (circlePoint θ)).IsHermitian := by
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  exact leviMatrix_isHermitian
    ((boundaryCost_chart_contDiffAt hd j (hF.2.2.2.2.2.2.2.1 θ)
      ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩ F.s).of_le (by simp)) cotangentDir

theorem boundarySymbol_isHermitian {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    (a : ℕ) (E : ℂ → CotangentMatrix n) (θ : ℝ) :
    (boundarySymbol d j a F E (circlePoint θ)).IsHermitian := by
  apply (Matrix.isHermitian_conjTranspose_mul_mul (E (circlePoint θ))
    (boundaryHessian_isHermitian hd hF θ)).smul
  simp [IsSelfAdjoint]

end Yau.Blueprint.V03Proof
