import Yau.Proofs.V03BoundaryChartRegularity

/-! A smooth polynomial representative for the WHOLE actual scaled
boundary Hessian, with its genuine time-dependent norm and base cost. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def clearedBoundaryTensor (d : VariationData X q) (j a : ℕ) (x : Pt X)
    (p : (CotangentCoord n × ℝ) × ℝ) : CotangentMatrix n :=
  (((wallPower d j a (cotangentChartInv x p.1.1)) ^ 2 : ℝ) : ℂ) •
      leviMatrix (fun z => boundarySmoothChartCost d j x (z, p.1.2)) p.1.1 cotangentDir +
    (((1 + p.2 : ℝ) : ℂ)) • clearedWallTensor d j a x p.1.1

theorem clearedBoundaryTensor_entry_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (x : Pt X) (b c : CotangentIndex n) :
    ContDiffOn ℝ ∞ (fun p => clearedBoundaryTensor d j a x p b c)
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) := by
  have hwall : ContDiffOn ℝ ∞ (fun z => wallPower d j a (cotangentChartInv x z))
      (cotangentTarget x) :=
    ((deltaBase_chart_contDiffOn hd j x).mul (deltaFiber_chart_contDiffOn hd j x)).pow a
  have hcoord : ContDiff ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ => p.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hwallLift : ContDiffOn ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ =>
      wallPower d j a (cotangentChartInv x p.1.1))
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) :=
    hwall.comp hcoord.contDiffOn (fun p hp => hp.1.1)
  have hH : ContDiffOn ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ =>
      leviMatrix (fun z => boundarySmoothChartCost d j x (z, p.1.2)) p.1.1 cotangentDir b c)
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) :=
    (boundarySmoothChartHessian_entry_contDiffOn hd j x b c).comp
      contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hW : ContDiffOn ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ =>
      clearedWallTensor d j a x p.1.1 b c)
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) :=
    (clearedWallTensor_entry_contDiffOn hd j a x b c).comp
      hcoord.contDiffOn (fun p hp => hp.1.1)
  have hs : ContDiffOn ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ => ((1 + p.2 : ℝ) : ℂ))
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.add contDiffOn_snd)
  exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hwallLift.pow 2)).mul hH).add (hs.mul hW)

theorem clearedBoundaryTensor_eq {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.extendedT) (s : ℝ)
    (hb : deltaBase d j (cotangentChartInv x z).1 ≠ 0)
    (hf : deltaFiber d j (cotangentChartInv x z) ≠ 0) :
    clearedBoundaryTensor d j a x ((z, t), s) =
      (((wallPower d j a (cotangentChartInv x z)) ^ 2 : ℝ) : ℂ) •
        leviMatrix (fun w => let y := cotangentChartInv x w
          dualNorm (d.h t) y.1 y.2 + wallCost d j y t s) z cotangentDir := by
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
  have hfun : (fun w => let y := cotangentChartInv x w
      dualNorm (d.h t) y.1 y.2 + wallCost d j y t s) =
      fun w => boundarySmoothChartCost d j x (w, t) +
        (1 + s) * (wallBase d j (cotangentChartInv x w).1 + wallFiber d j (cotangentChartInv x w)) := by
    funext w
    dsimp only [wallCost, boundarySmoothChartCost]
    ring
  rw [hfun, leviMatrix_add hS (contDiffAt_const.mul hW), leviMatrix_const_mul hW]
  unfold clearedBoundaryTensor
  rw [clearedWallTensor_eq hd j a ha x hz hb hf]
  ext b c
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_pow]
  ring

end Yau.Blueprint.V03Proof
