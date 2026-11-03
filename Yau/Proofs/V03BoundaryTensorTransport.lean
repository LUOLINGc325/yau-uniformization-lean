import Yau.Proofs.V03SpatialHessianTransport
import Yau.Proofs.V03AmbientBoundaryRegularity
import Yau.Proofs.V03Walls

/-! The actual original symbol is the normalized-frame contraction of the
full smooth ambient tensor in every valid fixed chart. -/

open scoped Topology ContDiff Matrix Manifold ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem boundaryCost_fixed_chart_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.extendedT) (s : ℝ)
    (hb : deltaBase d j (cotangentChartInv x z).1 ≠ 0)
    (hf : deltaFiber d j (cotangentChartInv x z) ≠ 0) :
    ContDiffAt ℝ 2 (fun w => let y := cotangentChartInv x w
      dualNorm (d.h t) y.1 y.2 + wallCost d j y t s) z := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hSOn : ContDiffOn ℝ ∞ (fun w => boundarySmoothChartCost d j x (w, t))
      (cotangentTarget x) :=
    (boundarySmoothChartCost_contDiffOn hd j x).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun w hw => ⟨hw, ht⟩)
  have hS := (hSOn.contDiffAt (hopen.mem_nhds hz)).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hB := ((deltaBase_chart_contDiffOn hd j x).contDiffAt (hopen.mem_nhds hz)).of_le
    (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hF := ((deltaFiber_chart_contDiffOn hd j x).contDiffAt (hopen.mem_nhds hz)).of_le
    (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hW : ContDiffAt ℝ 2 (fun w => wallBase d j (cotangentChartInv x w).1 +
      wallFiber d j (cotangentChartInv x w)) z :=
    ((hB.inv hb).sub contDiffAt_const).add ((hF.inv hf).sub contDiffAt_const)
  have hh := hS.add ((contDiffAt_const (c := 1 + s)).mul hW)
  apply hh.congr_of_eventuallyEq
  filter_upwards [] with w
  dsimp only [boundarySmoothChartCost, wallCost, wallBase, wallFiber]
  ring

theorem boundarySymbol_eq_fixedAmbientBoundaryTensor {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (θ : ℝ) (x : Pt X)
    (hy : F.f (circlePoint θ) ∈ cotangentSource x) :
    boundarySymbol d j a F E (circlePoint θ) =
      (ambientFrame d.G F.f E (circlePoint θ))ᴴ *
        fixedAmbientBoundaryTensor d j a x
          ((cotangentChart x (F.f (circlePoint θ)), discTime F (circlePoint θ)), F.s) *
        ambientFrame d.G F.f E (circlePoint θ) := by
  let y := F.f (circlePoint θ)
  let t := discTime F (circlePoint θ)
  have hz : cotangentChart x y ∈ cotangentTarget x := cotangentChart_mapsTo x hy
  have hround : cotangentChartInv x (cotangentChart x y) = y := cotangentChart_left_inv x hy
  have ht0 := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have ht : t ∈ Set.Icc 0 d.extendedT := ⟨ht0.1.le, ht0.2.le.trans hd.2.1.le⟩
  have hp := setup_index_bounds hd j
  have hregion : y ∈ boundaryRegion d j := hF.2.2.2.2.2.2.2.1 θ
  have hb : deltaBase d j (cotangentChartInv x (cotangentChart x y)).1 ≠ 0 := by
    rw [hround]
    exact (deltaBase_pos (setup_wallProfiles hd) hp.1 hregion.1).ne'
  have hf : deltaFiber d j (cotangentChartInv x (cotangentChart x y)) ≠ 0 := by
    rw [hround]
    exact (deltaFiber_pos (setup_wallProfiles hd) hp.2 hregion.2).ne'
  have hcost := boundaryCost_fixed_chart_contDiffAt hd j x hz ht F.s hb hf
  have hH := spatialHessian_in_fixed_chart
    (fun u => dualNorm (d.h t) u.1 u.2 + wallCost d j u t F.s) x hy hcost
  have hw := clearedBoundaryTensor_eq hd j a ha x hz ht F.s hb hf
  rw [hround] at hw
  have hA := (cotangentDG_gram_posDef_in_chart hd.2.2.2.2.1 x y hy).isUnit
  simp_rw [ambientFrame_in_fixed_chart hd.2.2.2.2.1.1 F.f E x _ hy]
  unfold fixedAmbientBoundaryTensor
  dsimp only
  rw [hround, ambientLeviTensor_frame hA, hw]
  unfold boundarySymbol boundaryHessian
  change _ = _
  rw [hH]
  simp only [frameInChart, y, t, Matrix.conjTranspose_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc, Complex.ofReal_pow]

theorem boundarySymbol_opNorm_le_fixedAmbient {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (hE : NormalizedDiscFrame d.G F.f E) (θ : ℝ) (x : Pt X)
    (hy : F.f (circlePoint θ) ∈ cotangentSource x) :
    rectOpNorm (boundarySymbol d j a F E (circlePoint θ)) ≤
      rectOpNorm (fixedAmbientBoundaryTensor d j a x
        ((cotangentChart x (F.f (circlePoint θ)), discTime F (circlePoint θ)), F.s)) := by
  rw [boundarySymbol_eq_fixedAmbientBoundaryTensor hd j a ha F hF E θ x hy]
  exact rectOpNorm_frame_contraction_le _ (hE.2.1 θ) _

end Yau.Blueprint.V03Proof
