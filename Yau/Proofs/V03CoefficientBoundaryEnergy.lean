import Yau.Proofs.V03CompactImmersionCoefficient
import Yau.Proofs.V03BoundaryAmbientTensor
import Yau.Proofs.V03EnergyTraceBounds
import Yau.Proofs.V03GagliardoVector

/-! Every genuine smooth scalar coefficient on the boundary compact set
has uniform supremum and original half-order bounds from the full energy. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem cotangentCoefficient_trace_continuous {d : VariationData X q}
    (hd : VariationSetup d) {b : CotangentPoint X.manifold → ℂ}
    (hb : ∀ x : Pt X, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x))
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    Continuous (fun θ => b (F.f (circlePoint θ))) := by
  have hK : CotangentCompact (boundaryCompact d j) :=
    (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.2.1
  have hy (θ : ℝ) : F.f (circlePoint θ) ∈ boundaryCompact d j :=
    ⟨(hF.2.2.2.2.2.2.2.1 θ).1.le, (hF.2.2.2.2.2.2.2.1 θ).2.le⟩
  let p : ℝ → d.G '' boundaryCompact d j := fun θ =>
    ⟨d.G (F.f (circlePoint θ)), ⟨F.f (circlePoint θ), hy θ, rfl⟩⟩
  have hp : Continuous p := (admissible_ambient_trace_continuous hd hF).subtype_mk _
  have hc := (compactImmersionCoefficient_locallyLipschitz hd.2.2.2.2.1 hb hK).continuous.comp hp
  apply hc.congr
  intro θ
  exact congrArg b (compactImmersionPoint_eq hd.2.2.2.2.1.2.1 _ (hy θ))

theorem cotangentCoefficient_uniform_boundary_control {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) {b : CotangentPoint X.manifold → ℂ}
    (hb : ∀ x : Pt X, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x)) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F →
      (∀ θ, ‖b (F.f (circlePoint θ))‖ ≤ M) ∧
      boundaryDSq (fun θ (_ : Unit) => b (F.f (circlePoint θ))) ≤
        ENNReal.ofReal C * variationEnergy d j F := by
  have hK : CotangentCompact (boundaryCompact d j) :=
    (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.2.1
  obtain ⟨C, M, hC, hM, hnorm, hdiff⟩ :=
    cotangentCoefficient_compact_control hd.2.2.2.2.1 hb hK
  let D : ℝ := C ^ 2 * (2 * Real.pi)⁻¹
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) (by positivity)
  refine ⟨D, M, hD, hM, fun F hF => ?_⟩
  have hy (θ : ℝ) : F.f (circlePoint θ) ∈ boundaryCompact d j :=
    ⟨(hF.2.2.2.2.2.2.2.1 θ).1.le, (hF.2.2.2.2.2.2.2.1 θ).2.le⟩
  refine ⟨fun θ => hnorm _ (hy θ), ?_⟩
  have hG := admissible_ambient_trace_continuous hd hF
  have hDSq : boundaryDSq (fun θ (_ : Unit) => b (F.f (circlePoint θ))) ≤
      ENNReal.ofReal (C ^ 2) * boundaryDSq (fun θ k => d.G (F.f (circlePoint θ)) k) := by
    apply boundaryDSq_le_of_sum_square_bound
      (fun k => (PiLp.continuous_apply 2 (fun _ : Fin q => ℂ) k).comp hG)
      (cotangentCoefficient_trace_continuous hd hb hF)
      (fun k θ => congrArg (fun v : ComplexVector q => v k)
        (circleTrace_periodic (fun ζ => d.G (F.f ζ)) θ))
      (circleTrace_periodic (fun ζ => b (F.f ζ))) (sq_nonneg C)
    intro θ τ
    have hh := hdiff _ (hy θ) _ (hy τ)
    have hsq : ‖b (F.f (circlePoint θ)) - b (F.f (circlePoint τ))‖ ^ 2 ≤
        (C * ‖d.G (F.f (circlePoint θ)) - d.G (F.f (circlePoint τ))‖) ^ 2 := by
      nlinarith [mul_self_le_mul_self (norm_nonneg _) hh]
    have he := PiLp.norm_sq_eq_of_L2 (fun _ : Fin q => ℂ)
      (d.G (F.f (circlePoint θ)) - d.G (F.f (circlePoint τ)))
    rw [mul_pow, he] at hsq
    exact hsq
  calc
    _ ≤ ENNReal.ofReal (C ^ 2) * boundaryDSq (fun θ k => d.G (F.f (circlePoint θ)) k) := hDSq
    _ = ENNReal.ofReal D * euclideanArea (fun ζ => d.G (F.f ζ)) := by
      rw [boundaryDSq_vector_eq_inverse_area
        (cotangentDisc_ambient_contDiffOn hF.1 hd.2.2.2.2.1.1)]
      dsimp only [D]
      rw [ENNReal.ofReal_mul (sq_nonneg C), mul_assoc]
      rfl
    _ ≤ ENNReal.ofReal D * variationEnergy d j F := by
      gcongr
      exact euclideanArea_le_variationEnergy d j F

end Yau.Blueprint.V03Proof
