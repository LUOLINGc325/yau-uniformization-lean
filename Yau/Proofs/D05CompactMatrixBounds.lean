import Yau.Proofs.D05MaximumPrinciple
import Mathlib.Topology.Order.Compact

/-! Uniform upper and strictly positive lower bounds for a compact family
of injective finite complex matrices. Empty compacts and indices are allowed. -/

open scoped Topology Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof

theorem compact_matrix_bounds {X ι κ : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι] [Fintype κ] {K : Set X} (hK : IsCompact K)
    {A : X → Matrix κ ι ℂ}
    (hc : ∀ i j, ContinuousOn (fun x => A x i j) K)
    (hi : ∀ x ∈ K, Function.Injective (Matrix.toEuclideanLin (A x))) :
    ∃ γ Γ : ℝ, 0 < γ ∧ γ ≤ Γ ∧ ∀ x ∈ K, ∀ v : EuclideanSpace ℂ ι,
      γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (A x) v‖ ∧
        ‖Matrix.toEuclideanLin (A x) v‖ ≤ Γ * ‖v‖ := by
  classical
  let S := K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ ι) 1
  let F : X × EuclideanSpace ℂ ι → ℝ :=
    fun p => ‖Matrix.toEuclideanLin (A p.1) p.2‖
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hFv : ContinuousOn (fun p : X × EuclideanSpace ℂ ι =>
      Matrix.toEuclideanLin (A p.1) p.2) S := by
    change ContinuousOn (fun p : X × EuclideanSpace ℂ ι =>
      WithLp.toLp 2 (fun i => ∑ j, A p.1 i j * p.2 j)) S
    apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    change ContinuousOn (fun p : X × EuclideanSpace ℂ ι =>
      ∑ j, A p.1 i j * p.2 j) S
    apply continuousOn_finset_sum
    intro j _
    exact ((hc i j).comp continuous_fst.continuousOn (fun _ hp => hp.1)).mul
      ((((EuclideanSpace.proj j : EuclideanSpace ℂ ι →L[ℂ] ℂ).continuous).comp
        continuous_snd).continuousOn)
  have hF : ContinuousOn F S := hFv.norm
  obtain ⟨γ, hγ, hlower⟩ := hS.exists_forall_le' hF (a := 0) (by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    apply norm_pos_iff.mpr
    intro hzero
    have hvzero : v = 0 := (hi x hx) (hzero.trans (map_zero _).symm)
    have hvnorm : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
    simpa [hvzero] using hvnorm)
  obtain ⟨C, hC⟩ := hS.bddAbove_image hF
  let Γ := max γ (max 1 C)
  have hγΓ : γ ≤ Γ := le_max_left _ _
  have hCΓ : C ≤ Γ := (le_max_right _ _).trans (le_max_right _ _)
  have hunit : ∀ x ∈ K, ∀ v : EuclideanSpace ℂ ι, ‖v‖ = 1 →
      γ ≤ ‖Matrix.toEuclideanLin (A x) v‖ ∧
        ‖Matrix.toEuclideanLin (A x) v‖ ≤ Γ := by
    intro x hx v hv
    have hp : (x, v) ∈ S := ⟨hx, by simpa only [Metric.mem_sphere, dist_zero_right] using hv⟩
    change γ ≤ F (x, v) ∧ F (x, v) ≤ Γ
    have hlo : γ ≤ F (x, v) := hlower (x, v) hp
    have hup : F (x, v) ≤ C := hC ⟨(x, v), hp, rfl⟩
    exact ⟨hlo, hup.trans hCΓ⟩
  refine ⟨γ, Γ, hγ, hγΓ, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : EuclideanSpace ℂ ι := (‖v‖⁻¹ : ℂ) • v
  have hwn : ‖w‖ = 1 := by
    simp only [w, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hvpos, inv_mul_cancel₀ hvpos.ne']
  have hAw : ‖Matrix.toEuclideanLin (A x) w‖ = ‖v‖⁻¹ * ‖Matrix.toEuclideanLin (A x) v‖ := by
    simp only [w, map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hvpos]
  obtain ⟨hlo, hup⟩ := hunit x hx w hwn
  rw [hAw] at hlo hup
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlo hvpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hvpos.ne', one_mul, mul_comm ‖v‖ γ] using hh
  · have hh := mul_le_mul_of_nonneg_left hup hvpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hvpos.ne', one_mul, mul_comm ‖v‖ Γ] using hh

end Yau.Blueprint.D05Proof
