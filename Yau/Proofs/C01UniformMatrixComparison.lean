import Yau.Proofs.C01CompactQuadraticCoercivity

/-! On a compact parameter set, continuity of a positive metric family
makes its quadratic forms uniformly close in time, in every direction.
This finite-dimensional statement does not use completeness. -/

noncomputable section

open scoped Topology Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint Filter

variable {n : ℕ}

theorem matrixQuadraticReal_continuous_product
    {Z : Type*} [TopologicalSpace Z] (H : Z → Herm n)
    (hH : ∀ i j, Continuous (fun z => H z i j)) :
    Continuous (fun p : Z × ComplexVector n => matrixQuadraticReal (H p.1) p.2) := by
  apply continuousOn_univ.mp
  simpa only [Set.univ_prod_univ] using
    matrixQuadraticReal_continuousOn_product H Set.univ Set.univ
      (fun i j => (hH i j).continuousOn)

theorem compact_uniform_matrix_comparison
    {T Z : Type*} [TopologicalSpace T] [TopologicalSpace Z]
    (H : T → Z → Herm n) (a : T) (S : Set Z) (hS : IsCompact S)
    (hH : ∀ i j, Continuous (fun p : T × Z => H p.1 p.2 i j))
    (hpos : ∀ z ∈ S, (H a z).PosDef) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 a, ∀ z ∈ S, ∀ v : ComplexVector n,
      |matrixQuadraticReal (H t z) v - matrixQuadraticReal (H a z) v| ≤
        ε * matrixQuadraticReal (H a z) v := by
  classical
  let K : Set (Z × ComplexVector n) := S ×ˢ Metric.sphere 0 1
  have hK : IsCompact K := hS.prod (isCompact_sphere _ _)
  have hq := matrixQuadraticReal_continuous_product (fun p : T × Z => H p.1 p.2) hH
  have hnow : Continuous (fun p : T × (Z × ComplexVector n) =>
      matrixQuadraticReal (H p.1 p.2.1) p.2.2) :=
    hq.comp ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))
  have hbase : Continuous (fun p : T × (Z × ComplexVector n) =>
      matrixQuadraticReal (H a p.2.1) p.2.2) :=
    hnow.comp (continuous_const.prodMk continuous_snd)
  have hunits : ∀ᶠ t in 𝓝 a, ∀ p ∈ K,
      |matrixQuadraticReal (H t p.1) p.2 - matrixQuadraticReal (H a p.1) p.2| <
        ε * matrixQuadraticReal (H a p.1) p.2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    have hvnorm : ‖p.2‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hp.2
    have hv : WithLp.ofLp p.2 ≠ 0 := by
      intro hz
      have hz' : p.2 = 0 := by simpa only [WithLp.ofLp_eq_zero] using hz
      rw [hz', norm_zero] at hvnorm
      norm_num at hvnorm
    have hpositive : 0 < matrixQuadraticReal (H a p.1) p.2 :=
      (Complex.pos_iff.mp ((hpos p.1 hp.1).dotProduct_mulVec_pos hv)).1
    apply (isOpen_lt (hnow.sub hbase).abs (continuous_const.mul hbase)).mem_nhds
    change |matrixQuadraticReal (H a p.1) p.2 - matrixQuadraticReal (H a p.1) p.2| <
      ε * matrixQuadraticReal (H a p.1) p.2
    rw [sub_self, abs_zero]
    exact mul_pos hε hpositive
  filter_upwards [hunits] with t ht
  intro z hz v
  by_cases hv : v = 0
  · subst v
    simp [matrixQuadraticReal]
  let r := ‖v‖⁻¹
  let w : ComplexVector n := r • v
  have hr : 0 < r := inv_pos.mpr (norm_pos_iff.mpr hv)
  have hwnorm : ‖w‖ = 1 := by
    dsimp only [w, r]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ (norm_pos_iff.mpr hv).ne'
  have hw : w ∈ Metric.sphere (0 : ComplexVector n) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hwnorm
  have hunit := (ht (z, w) ⟨hz, hw⟩).le
  dsimp only [w] at hunit
  simp only [matrixQuadraticReal, quadratic_real_smul] at hunit
  have habs : |r ^ 2 * matrixQuadraticReal (H t z) v -
      r ^ 2 * matrixQuadraticReal (H a z) v| =
      r ^ 2 * |matrixQuadraticReal (H t z) v - matrixQuadraticReal (H a z) v| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
  change |r ^ 2 * matrixQuadraticReal (H t z) v -
      r ^ 2 * matrixQuadraticReal (H a z) v| ≤
      ε * (r ^ 2 * matrixQuadraticReal (H a z) v) at hunit
  rw [habs] at hunit
  apply le_of_mul_le_mul_left (a := r ^ 2) _ (sq_pos_of_pos hr)
  nlinarith only [hunit]

end Yau.NodeProofs.C01Aux
