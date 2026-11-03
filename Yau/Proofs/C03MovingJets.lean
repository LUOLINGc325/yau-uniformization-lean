import Yau.Proofs.C03MovingNeighborhood
import Yau.Proofs.C03SourceEnergy

/-! Real partial jets of the explicit two-ended holomorphic trial family. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau.LeafProofs L23Aux
set_option backward.isDefEq.respectTransparency false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mapDirection_parameter (Z : ℂ × ℝ → E) {a : ℂ} {t : ℝ}
    (hZ : DifferentiableAt ℝ Z (a, t)) (v : ℂ) :
    mapDirection Z (v, 0) (a, t) = mapDirection (fun b => Z (b, t)) v a := by
  have H := hZ.hasFDerivAt.comp a
    ((hasFDerivAt_id (𝕜 := ℝ) a).prodMk (hasFDerivAt_const (𝕜 := ℝ) t a))
  have H' : HasFDerivAt (fun b => Z (b, t))
      ((fderiv ℝ Z (a, t)).comp ((ContinuousLinearMap.id ℝ ℂ).prod 0)) a := by
    simpa only [Function.comp_def, id_eq] using H
  exact (congrArg (fun L : ℂ →L[ℝ] E => L v) H'.fderiv).symm

theorem mapDirection_parameter_second (Z : ℂ × ℝ → E) {a : ℂ} {t : ℝ}
    (hZ : ContDiffAt ℝ 2 Z (a, t)) (v w : ℂ) :
    mapDirection (mapDirection Z (v, 0)) (w, 0) (a, t) =
      mapDirection (mapDirection (fun b => Z (b, t)) v) w a := by
  have hD : DifferentiableAt ℝ (mapDirection Z (v, 0)) (a, t) :=
    ((hZ.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := (v, 0)))).differentiableAt_one
  rw [mapDirection_parameter _ hD w]
  apply mapDirection_congr
  have H : ∀ᶠ b in 𝓝 a, ContDiffAt ℝ 1 Z (b, t) :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      ((hZ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num))
  filter_upwards [H] with b hb
  exact mapDirection_parameter Z hb.differentiableAt_one v

section Complex
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem movingTrial_mapDirection (γ W : ℝ → E) (Q : E) (t : ℝ) (a v : ℂ) :
    mapDirection (movingTrial γ W Q t) v a =
      v • (W t + ((t : ℂ) * a) • Q) := by
  have H := (movingTrial_hasDerivAt γ W Q t a).hasFDerivAt.restrictScalars ℝ
  unfold mapDirection
  rw [H.fderiv]
  rfl

theorem movingTrial_second_mapDirection (γ W : ℝ → E) (Q : E)
    (t : ℝ) (a v w : ℂ) :
    mapDirection (mapDirection (movingTrial γ W Q t) v) w a =
      (v * ((t : ℂ) * w)) • Q := by
  have heq : mapDirection (movingTrial γ W Q t) v =
      fun b => v • (W t + ((t : ℂ) * b) • Q) := by
    funext b
    exact movingTrial_mapDirection γ W Q t b v
  rw [heq]
  have H := ((((hasDerivAt_id a).const_mul (t : ℂ)).smul_const Q).const_add (W t)).const_smul v
  have H' : HasDerivAt (fun b : ℂ => v • (W t + ((t : ℂ) * b) • Q))
      (v • ((t : ℂ) • Q)) a := by
    convert! H using 1 <;> simp only [Pi.smul_apply, id_eq, mul_one]
  unfold mapDirection
  rw [(H'.hasFDerivAt.restrictScalars ℝ).fderiv]
  change w • (v • ((t : ℂ) • Q)) = _
  simp only [smul_smul]
  congr 1
  ring

theorem movingTrial_radial_trace_zero (γ W : ℝ → E) (Q : E) (t : ℝ) (a : ℂ) :
    mapDirection (mapDirection (movingTrial γ W Q t) 1) 1 a +
      mapDirection (mapDirection (movingTrial γ W Q t) Complex.I) Complex.I a = 0 := by
  rw [movingTrial_second_mapDirection, movingTrial_second_mapDirection]
  have H : Complex.I * ((t : ℂ) * Complex.I) = -(t : ℂ) := by
    calc
      _ = (Complex.I * Complex.I) * (t : ℂ) := by ring
      _ = -(t : ℂ) := by rw [Complex.I_mul_I]; ring
  simp only [one_mul, mul_one, H, neg_smul, add_neg_cancel]

end Complex
end Yau.Proofs.C03Aux
