import Yau.Proofs.D05CompactMatrixBounds
import Yau.Proofs.V03SpatialHessianTransport
import Yau.Proofs.V03TransitionInverse

/-! The forward center bound uses the supplied normalized frame's original
interior ambient operator bound and a compact lower bound for the immersion. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem centerFrame_forward_bound {d : VariationData X q} (hd : VariationSetup d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
      rectOpNorm (frameInChart d.chart F.f E 0) ≤ C := by
  classical
  have hG := hd.2.2.2.2.1
  have hc := hd.2.2.2.2.2.2.2.1
  let K₀ : Set (CotangentCoord n) := Prod.fst '' centerCylinder d
  have hK₀ : IsCompact K₀ := hc.1.image continuous_fst
  have hKt : K₀ ⊆ cotangentTarget d.chart := by
    rintro z ⟨p, hp, rfl⟩
    exact (hc.2.2.1 hp).1
  let A : CotangentCoord n → Matrix (Fin q) (CotangentIndex n) ℂ :=
    fun z => cotangentDG d.G d.chart (cotangentChartInv d.chart z)
  have hcoord : ContDiffOn ℂ ∞
      (fun z => cotangentChart d.chart (cotangentChartInv d.chart z)) (cotangentTarget d.chart) :=
    contDiffOn_id.congr (fun z hz => V03Proof.cotangentChart_right_inv d.chart hz)
  have hAc (a : Fin q) (i : CotangentIndex n) : ContinuousOn (fun z => A z a i) K₀ := by
    have hs : ContDiffOn ℂ ∞ (fun z => A z a i) (cotangentTarget d.chart) := by
      intro z hz
      exact V03Proof.cotangentDG_entry_contDiffWithinAt hG.1 d.chart
        (V03Proof.cotangentChartInv_mapsTo d.chart hz) (hcoord z hz) a i
    exact hs.continuousOn.mono hKt
  have hAi (z : CotangentCoord n) (hz : z ∈ K₀) : Function.Injective (Matrix.toEuclideanLin (A z)) := by
    intro u v huv
    apply WithLp.ofLp_injective
    apply V03Proof.cotangentDG_mulVec_injective_in_chart hG d.chart
      (cotangentChartInv d.chart z) (V03Proof.cotangentChartInv_mapsTo d.chart (hKt hz))
    exact congrArg WithLp.ofLp huv
  obtain ⟨γ, Γ, hγ, _, hlow⟩ := D05Proof.compact_matrix_bounds hK₀ hAc hAi
  have hγinv : 0 ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
  refine ⟨1 + γ⁻¹, by positivity, fun j F E hF hE => ?_⟩
  have hcenter := hF.2.2.2.2.2.1
  have hzK : cotangentChart d.chart (F.f 0) ∈ K₀ := Set.mem_image_of_mem Prod.fst hcenter.2
  let S := frameInChart d.chart F.f E 0
  have hS : rectOpNorm S ≤ γ⁻¹ := by
    unfold rectOpNorm
    apply ContinuousLinearMap.opNorm_le_bound _ hγinv
    intro v
    change ‖Matrix.toEuclideanLin S v‖ ≤ γ⁻¹ * ‖v‖
    have hlo := (hlow (cotangentChart d.chart (F.f 0)) hzK (Matrix.toEuclideanLin S v)).1
    dsimp only [A] at hlo
    rw [V03Proof.cotangentChart_left_inv d.chart hcenter.1] at hlo
    have hU : rectOpNorm (ambientFrame d.G F.f E 0) ≤ 1 := hE.2.2.1 0 (by simp)
    have hu : ‖Matrix.toEuclideanLin (ambientFrame d.G F.f E 0) v‖ ≤ ‖v‖ := by
      calc
        _ ≤ rectOpNorm (ambientFrame d.G F.f E 0) * ‖v‖ :=
          ((Matrix.toEuclideanLin (ambientFrame d.G F.f E 0)).toContinuousLinearMap).le_opNorm v
        _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hU (norm_nonneg v)
        _ = _ := one_mul _
    have hcomp : Matrix.toEuclideanLin (cotangentDG d.G d.chart (F.f 0))
        (Matrix.toEuclideanLin S v) = Matrix.toEuclideanLin (ambientFrame d.G F.f E 0) v := by
      rw [V03Proof.ambientFrame_in_fixed_chart hG.1 F.f E d.chart 0 hcenter.1]
      exact (LinearMap.congr_fun (Matrix.toLpLin_mul 2 2 2
        (cotangentDG d.G d.chart (F.f 0)) S) v).symm
    rw [hcomp] at hlo
    exact (le_inv_mul_iff₀ hγ).mpr (hlo.trans hu)
  exact hS.trans (by linarith)

end Yau.Blueprint.V02Proof
