import Yau.Proofs.C01FixedChartRicci
import Yau.Proofs.C01PathHarnackInequality

/-! Compactness of the unit sphere makes a continuous positive matrix
family uniformly coercive on a compact parameter set.  The original
manifold supplies positive dimension internally. -/

noncomputable section

open scoped Topology Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

def matrixQuadraticReal {n : ℕ} (H : Herm n) (v : ComplexVector n) : ℝ :=
  (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re

theorem matrixQuadraticReal_continuousOn_product
    {n : ℕ} {Z : Type*} [TopologicalSpace Z]
    (H : Z → Herm n) (S : Set Z) (T : Set (ComplexVector n))
    (hH : ∀ i j, ContinuousOn (fun z => H z i j) S) :
    ContinuousOn (fun p : Z × ComplexVector n => matrixQuadraticReal (H p.1) p.2) (S ×ˢ T) := by
  have hv (i : Fin n) : ContinuousOn (fun p : Z × ComplexVector n => p.2 i) (S ×ˢ T) :=
    ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).continuous.comp continuous_snd).continuousOn
  simp only [matrixQuadraticReal, dotProduct, Matrix.mulVec, Pi.star_apply]
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro i _
  apply (hv i).star.mul
  apply continuousOn_finsetSum
  intro j _
  exact ((hH i j).comp continuous_fst.continuousOn (fun p hp => hp.1)).mul (hv j)

theorem compact_matrix_quadratic_coercivity
    {n : ℕ} (hn : 0 < n) {Z : Type*} [TopologicalSpace Z]
    (H A : Z → Herm n) (S : Set Z) (hS : IsCompact S)
    (hH : ∀ i j, ContinuousOn (fun z => H z i j) S)
    (hA : ∀ i j, ContinuousOn (fun z => A z i j) S)
    (hpos : ∀ z ∈ S, (A z).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ S, ∀ v : ComplexVector n,
      c * matrixQuadraticReal (H z) v ≤ matrixQuadraticReal (A z) v := by
  classical
  by_cases hSne : S.Nonempty
  · letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let T : Set (ComplexVector n) := Metric.sphere 0 1
    have hT : IsCompact T := isCompact_sphere _ _
    have hTne : T.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    have hK : IsCompact (S ×ˢ T) := hS.prod hT
    have hKne : (S ×ˢ T).Nonempty := hSne.prod hTne
    have hpositive (p : Z × ComplexVector n) (hp : p ∈ S ×ˢ T) :
        0 < matrixQuadraticReal (A p.1) p.2 := by
      have hnorm : ‖p.2‖ = 1 := by
        simpa only [T, Metric.mem_sphere, dist_zero_right] using hp.2
      have hv : p.2 ≠ 0 := by
        intro hz
        rw [hz, norm_zero] at hnorm
        norm_num at hnorm
      have hvec : WithLp.ofLp p.2 ≠ 0 := by
        simpa only [ne_eq, WithLp.ofLp_eq_zero] using hv
      exact (Complex.pos_iff.mp ((hpos p.1 hp.1).dotProduct_mulVec_pos hvec)).1
    obtain ⟨pA, hpA, hmin⟩ := hK.exists_isMinOn hKne
      (matrixQuadraticReal_continuousOn_product A S T hA)
    obtain ⟨pH, hpH, hmax⟩ := hK.exists_isMaxOn hKne
      (matrixQuadraticReal_continuousOn_product H S T hH)
    let m := matrixQuadraticReal (A pA.1) pA.2
    let M := matrixQuadraticReal (H pH.1) pH.2
    let B := max M 0
    let c := m / (B + 1)
    have hm : 0 < m := hpositive pA hpA
    have hB : 0 ≤ B := le_max_right M 0
    have hden : 0 < B + 1 := add_pos_of_nonneg_of_pos hB zero_lt_one
    have hc : 0 < c := div_pos hm hden
    have hcancel : c * (B + 1) = m := div_mul_cancel₀ _ hden.ne'
    have hunit (z : Z) (hz : z ∈ S) (v : ComplexVector n) (hv : v ∈ T) :
        c * matrixQuadraticReal (H z) v ≤ matrixQuadraticReal (A z) v := by
      have hupper : matrixQuadraticReal (H z) v ≤ B :=
        (hmax (show (z, v) ∈ S ×ˢ T from ⟨hz, hv⟩)).trans (le_max_left M 0)
      have hlower : m ≤ matrixQuadraticReal (A z) v :=
        hmin (show (z, v) ∈ S ×ˢ T from ⟨hz, hv⟩)
      calc
        _ ≤ c * B := mul_le_mul_of_nonneg_left hupper hc.le
        _ ≤ m := by nlinarith [hcancel, hc.le]
        _ ≤ _ := hlower
    refine ⟨c, hc, ?_⟩
    intro z hz v
    by_cases hv : v = 0
    · subst v
      simp [matrixQuadraticReal]
    let w : ComplexVector n := (‖v‖⁻¹ : ℝ) • v
    have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hwnorm : ‖w‖ = 1 := by
      dsimp only [w]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      exact inv_mul_cancel₀ hr.ne'
    have hw : w ∈ T := by simpa only [T, Metric.mem_sphere, dist_zero_right] using hwnorm
    have hscaled := hunit z hz w hw
    dsimp only [w] at hscaled
    simp only [matrixQuadraticReal, quadratic_real_smul] at hscaled
    have hscaled' : (‖v‖⁻¹) ^ 2 * (c * matrixQuadraticReal (H z) v) ≤
        (‖v‖⁻¹) ^ 2 * matrixQuadraticReal (A z) v := by
      dsimp only [matrixQuadraticReal]
      nlinarith only [hscaled]
    exact le_of_mul_le_mul_left hscaled' (sq_pos_of_pos (inv_pos.mpr hr))
  · refine ⟨1, zero_lt_one, ?_⟩
    intro z hz
    exact (hSne ⟨z, hz⟩).elim

end Yau.NodeProofs.C01Aux
