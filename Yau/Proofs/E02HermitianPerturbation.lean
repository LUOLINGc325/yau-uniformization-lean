import Yau.Proofs.E02QuadraticNorm
import Yau.Proofs.E02PosDefLower

open Matrix Set Filter
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Positivity is stable among Hermitian matrices, proved in the actual
entrywise norm. No openness in the full complex matrix space is claimed. -/
theorem posDef_of_hermitian_norm_sub_lt {n : ℕ} (A A₀ : Herm n)
    (hA : A.IsHermitian) {β : ℝ} (hβ : 0 < β)
    (hLower : (A₀-(β : ℂ) • (1 : Herm n)).PosSemidef)
    (hNorm : ‖A-A₀‖ < β/((n : ℝ)^2+1)) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
  intro v hv
  let V : ComplexVector n := WithLp.toLp 2 v
  have hV : V ≠ 0 := by
    intro h
    apply hv
    exact congrArg WithLp.ofLp h
  have hVSq : 0 < ‖V‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hV)
  have hLow := (RCLike.nonneg_iff.mp (hLower.dotProduct_mulVec_nonneg v)).1
  change 0 ≤ qform (A₀-(β : ℂ) • (1 : Herm n)) V at hLow
  rw [qform_sub_real_smul,qform_one] at hLow
  have hDiff : qform (A-A₀) V = qform A V-qform A₀ V := by
    simpa using qform_sub_real_smul A A₀ 1 V
  have hBound := abs_qform_le_entrywise (A-A₀) V
  have hNegative := neg_abs_le (qform (A-A₀) V)
  have hDen : 0 < (n : ℝ)^2+1 := by positivity
  have hSmall := (lt_div_iff₀ hDen).mp hNorm
  have hCoefficient : 0 < β-(n : ℝ)^2*‖A-A₀‖ := by
    nlinarith [norm_nonneg (A-A₀)]
  have hPositive : 0 < qform A V := by
    have hProd := mul_pos hCoefficient hVSq
    rw [hDiff] at hBound hNegative
    nlinarith
  have hImag := congrArg Complex.im (hA.star_dotProduct_mulVec_comm v v)
  simp only [Complex.star_def,Complex.conj_im] at hImag
  apply RCLike.pos_iff.mpr
  constructor
  · exact hPositive
  · change (star v ⬝ᵥ (A*ᵥv)).im = 0
    linarith

theorem eventually_posDef_of_tendsto_hermitian {ι : Type*} {l : Filter ι} {n : ℕ}
    (A : ι → Herm n) (A₀ : Herm n) (h₀ : A₀.PosDef) (hA : ∀ᶠ i in l, (A i).IsHermitian)
    (hlim : Tendsto A l (𝓝 A₀)) : ∀ᶠ i in l, (A i).PosDef := by
  obtain ⟨β,hβ,hLower⟩ := posDef_exists_scalar_lower A₀ h₀
  have hRadius : 0 < β/((n : ℝ)^2+1) := div_pos hβ (by positivity)
  have hBall := hlim.eventually (Metric.ball_mem_nhds A₀ hRadius)
  filter_upwards [hA,hBall] with i hi hBall
  apply posDef_of_hermitian_norm_sub_lt (A i) A₀ hi hβ hLower
  simpa only [Metric.mem_ball,dist_eq_norm] using hBall

end Yau.NodeProofs.E02Aux
