import Yau.Proofs.V02WallTaylorChartFactorSmooth
import Yau.Proofs.V02WallTaylorPersistence
import Yau.Proofs.V02WallTaylorZeroWalls

/-! The globally defined increments are the literal original wall expressions.
Their chart representatives have the cleared smooth formulas, including on zero walls. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

def nativeWallPoint (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (y : CotangentPoint X.manifold) (p : ℂ × (ℂ × (Fin b → ℂ))) : CotangentPoint X.manifold :=
  (Ψ (NativeCotangentPoint.mk y, wallPower d j a y • (p.1 • (p.2.1 • p.2.2)))).val

def nativeInverseIncrement (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (y : CotangentPoint X.manifold) (p : ℂ × (ℂ × (Fin b → ℂ))) : ℝ :=
  wallBase d j (nativeWallPoint d j a Ψ y p).1 + wallFiber d j (nativeWallPoint d j a Ψ y p) -
    (wallBase d j y.1 + wallFiber d j y)

def nativeLogIncrement (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (y : CotangentPoint X.manifold) (p : ℂ × (ℂ × (Fin b → ℂ))) : ℝ :=
  Real.log (wallProduct d j (nativeWallPoint d j a Ψ y p)) - Real.log (wallProduct d j y)

def chartBaseFactor (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) : ℂ × ChartFactorAux n b → ℝ :=
  chartSprayFactor Ψ (fun y => deltaBase d j y.1) (fun u => wallPower d j a (cotangentChartInv x u)) x

def chartFiberFactor (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) : ℂ × ChartFactorAux n b → ℝ :=
  chartSprayFactor Ψ (deltaFiber d j) (fun u => wallPower d j a (cotangentChartInv x u)) x

theorem native_wall_increments_eq_chart {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 3 ≤ a)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Pt X)
    {A : CotangentCoord n} {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall A δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x)
    {p : ℂ × ChartFactorAux n b} (hu : p.2.1 ∈ Metric.closedBall A δ)
    (hτ : wallPower d j a (cotangentChartInv x p.2.1) • chartFactorDirection p ∈
      Metric.closedBall (0 : Fin b → ℂ) (R / 2))
    (hRb : |chartBaseFactor d j a Ψ x p| ≤ 1 / 2)
    (hRf : |chartFiberFactor d j a Ψ x p| ≤ 1 / 2) :
    (nativeInverseIncrement d j a Ψ (cotangentChartInv x p.2.1) (p.1, p.2.2) =
      clearedInverseIncrement a (deltaBase d j (cotangentChartInv x p.2.1).1)
        (deltaFiber d j (cotangentChartInv x p.2.1)) (chartBaseFactor d j a Ψ x p) +
      clearedInverseIncrement a (deltaFiber d j (cotangentChartInv x p.2.1))
        (deltaBase d j (cotangentChartInv x p.2.1).1) (chartFiberFactor d j a Ψ x p)) ∧
    (nativeLogIncrement d j a Ψ (cotangentChartInv x p.2.1) (p.1, p.2.2) =
      clearedLogIncrement a (deltaBase d j (cotangentChartInv x p.2.1).1)
        (deltaFiber d j (cotangentChartInv x p.2.1)) (chartBaseFactor d j a Ψ x p) +
      clearedLogIncrement a (deltaFiber d j (cotangentChartInv x p.2.1))
        (deltaBase d j (cotangentChartInv x p.2.1).1) (chartFiberFactor d j a Ψ x p)) := by
  let m : CotangentCoord n → ℝ := fun u => wallPower d j a (cotangentChartInv x u)
  have hp : p ∈ chartFactorDomain Ψ m x A δ R :=
    mem_chartFactorDomain_of_time_bound hδ hR hsource hu hτ
  have huT := hvalid (Metric.closedBall_subset_ball (by linarith) hu)
  have hsrc := hsource _ hu _ hτ
  have hb := chartSprayFactor_identity hΨ (B := fun y => deltaBase d j y.1)
    (deltaBase_chart_contDiffOn hd j x) hp
  have hf := chartSprayFactor_identity hΨ (B := deltaFiber d j)
    (deltaFiber_chart_contDiffOn hd j x) hp
  rw [sprayScalar_eq_actual (Ψ := Ψ) (fun y => deltaBase d j y.1) x hsrc,
    sprayScalar_zero hzero (fun y => deltaBase d j y.1) x huT] at hb
  rw [sprayScalar_eq_actual (Ψ := Ψ) (deltaFiber d j) x hsrc,
    sprayScalar_zero hzero (deltaFiber d j) x huT] at hf
  have hprofiles := setup_wallProfiles hd
  have hbu : deltaBase d j (cotangentChartInv x p.2.1).1 ∈ Set.Icc 0 1 :=
    ⟨(hprofiles.2.2.1 _).1, deltaBase_le_one hprofiles _ _⟩
  have hfu : deltaFiber d j (cotangentChartInv x p.2.1) ∈ Set.Icc 0 1 :=
    ⟨(hprofiles.2.2.2 _).1, deltaFiber_le_one hprofiles _ _⟩
  have hbe : deltaBase d j (nativeWallPoint d j a Ψ (cotangentChartInv x p.2.1) (p.1, p.2.2)).1 =
      deltaBase d j (cotangentChartInv x p.2.1).1 +
        (deltaBase d j (cotangentChartInv x p.2.1).1 *
          deltaFiber d j (cotangentChartInv x p.2.1)) ^ a * chartBaseFactor d j a Ψ x p := by
    change _ - _ = _ at hb
    exact eq_add_of_sub_eq' hb
  have hfe : deltaFiber d j (nativeWallPoint d j a Ψ (cotangentChartInv x p.2.1) (p.1, p.2.2)) =
      deltaFiber d j (cotangentChartInv x p.2.1) +
        (deltaBase d j (cotangentChartInv x p.2.1).1 *
          deltaFiber d j (cotangentChartInv x p.2.1)) ^ a * chartFiberFactor d j a Ψ x p := by
    exact eq_add_of_sub_eq' hf
  have hh := cleared_wall_increments_eq ha hbu hfu hRb hRf hbe hfe
  refine ⟨?_, hh.2⟩
  dsimp [nativeInverseIncrement, wallBase, wallFiber]
  linarith [hh.1]

end Yau.Blueprint.V02WallTaylorProof
