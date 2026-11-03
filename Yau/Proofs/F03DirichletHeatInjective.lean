import Yau.Proofs.F03DirichletHeat

/-! Injectivity of the actual self-adjoint supported heat semigroup. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletHeat_zero_of_double_zero (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    {s : ℝ} (hs : 0 ≤ s) (f : Lp ℝ 2 (μ.restrict O))
    (hf : dirichletHeat g μ hμ O (s+s) f = 0) : dirichletHeat g μ hμ O s f = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    ⟪dirichletHeat g μ hμ O s f,dirichletHeat g μ hμ O s f⟫_ℝ =
        ⟪f,(dirichletHeat g μ hμ O s).adjoint (dirichletHeat g μ hμ O s f)⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = ⟪f,dirichletHeat g μ hμ O s (dirichletHeat g μ hμ O s f)⟫_ℝ := by rw [dirichletHeat_adjoint]
    _ = ⟪f,dirichletHeat g μ hμ O (s+s) f⟫_ℝ := by
      rw [dirichletHeat_add g μ hμ O hs hs,mul_apply_eq_comp]
    _ = 0 := by rw [hf,inner_zero_right]

/-- Halving and strong continuity at zero exclude any nonzero vector from
the kernel of the actual self-adjoint heat at positive time. -/
theorem dirichletHeat_zero_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O)) :
    dirichletHeat g μ hμ O t f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    let τ : ℕ → ℝ := fun k => t * (1/2 : ℝ)^k
    have hτ (k : ℕ) : 0 ≤ τ k := by dsimp [τ]; positivity
    have hzero (k : ℕ) : dirichletHeat g μ hμ O (τ k) f = 0 := by
      induction k with
      | zero => simpa only [τ,pow_zero,mul_one] using hf
      | succ k ih =>
        apply dirichletHeat_zero_of_double_zero g μ hμ O (hτ (k+1)) f
        have he : τ (k+1) + τ (k+1) = τ k := by dsimp [τ]; rw [pow_succ]; ring
        rw [he]
        exact ih
    have hτ0 : Tendsto τ atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1))
    have hτ0' : Tendsto τ atTop (𝓝[≥] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hτ0,Eventually.of_forall hτ⟩
    have hlim := (dirichletHeat_tendsto_zero g μ hμ O hO f).comp hτ0'
    have hlim0 : Tendsto (fun k => dirichletHeat g μ hμ O (τ k) f) atTop (𝓝 0) := by
      simp_rw [hzero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hlim0
  · intro hf
    rw [hf,map_zero]

theorem dirichletHeat_injective (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    {t : ℝ} (ht : 0 < t) : Function.Injective (dirichletHeat g μ hμ O t) := by
  intro f k hfk
  apply sub_eq_zero.mp
  apply (dirichletHeat_zero_iff g μ hμ O hO ht (f-k)).mp
  rw [map_sub,hfk,sub_self]

end Yau.Proofs.F03Aux
