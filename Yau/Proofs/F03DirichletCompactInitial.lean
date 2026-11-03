import Yau.Proofs.F03DirichletCoreDuhamel
import Yau.Proofs.F03DirichletUniformCoreApprox
import Yau.Proofs.F03DirichletClassicalHeat

/-! The true uniform initial face for continuous supported compact sources. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem continuous_compact_scalarL2 (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) {f : M.Carrier → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f) :
    ScalarL2 (μ.restrict O) f := by
  have : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  exact (scalarL2_iff_memLp _ _).mpr
    ((hf.memLp_of_hasCompactSupport hcf : MemLp f 2 μ).restrict O)

theorem dirichletClassicalHeat_uniform_compact_initial (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (f : M.Carrier → ℝ)
    (hf : Continuous f) (hcf : HasCompactSupport f) (hfo : tsupport f ⊆ O)
    (hfL : ScalarL2 (μ.restrict O) f) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ x ∈ O, |dirichletClassicalHeat g hK μ hμ O hO (scalarToLp hfL) x t-f x| < ε := by
  intro ε hε
  obtain ⟨k,hk⟩ := exists_uniform_dirichletCore_approx g μ hμ O hf hcf hfo
    (show 0 < ε/4 by positivity)
  obtain ⟨C,hC⟩ := (continuous_of_smoothFn (smoothFn_laplacian g k.val.2.1)).bounded_above_of_compact_support
    (laplacian_hasCompactSupport g.form k.val.2.1 k.val.2.2)
  let K : ℝ := max 1 C
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hLap : ∀ x, |laplacian g.form k.val x| ≤ K := by
    intro x
    exact (show |laplacian g.form k.val x| ≤ C by simpa only [Real.norm_eq_abs] using hC x).trans
      (le_max_right _ _)
  let δ := ε/(2*(K+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro t ht htδ
  let kL := l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)
  have hsub : ∀ᵐ x ∂μ.restrict O, |(scalarToLp hfL-kL) x| ≤ ε/4 := by
    filter_upwards [scalarToLp_coe hfL,restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ k.val),
      ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ k.val),
      Lp.coeFn_sub (scalarToLp hfL) kL] with x hfx hr hkx hs
    change |(scalarToLp hfL-kL) x| ≤ _
    rw [hs,Pi.sub_apply,hfx]
    change |f x-restrictL2 μ O _ x| ≤ _
    rw [hr,hkx]
    exact (hk x).le
  have hheat := dirichletHeat_abs_markov g μ hμ O hO.measurableSet ht.le (ε/4)
    (by positivity) (scalarToLp hfL-kL) hsub
  rw [map_sub] at hheat
  have hinit := dirichletHeat_compact_initial_ae g hK μ hμ O hO k hK0 ht hLap
  have hAE : ∀ᵐ x ∂μ.restrict O,
      |dirichletClassicalHeat g hK μ hμ O hO (scalarToLp hfL) x t-k.val x| ≤ ε/4+t*K := by
    filter_upwards [dirichletClassicalHeat_ae g hK μ hμ O hO (scalarToLp hfL) ht,
      hheat,hinit,Lp.coeFn_sub (dirichletHeat g μ hμ O t (scalarToLp hfL))
        (dirichletHeat g μ hμ O t kL)] with x hux hh hi hs
    rw [hs,Pi.sub_apply] at hh
    have htri := abs_sub_le (dirichletClassicalHeat g hK μ hμ O hO (scalarToLp hfL) x t)
      (dirichletHeat g μ hμ O t kL x) (k.val x)
    rw [hux] at htri
    rw [hux]
    linarith only [htri,hh,hi]
  have hpoint := leOn_open_of_riemannian_ae_le g μ hμ O hO _ _
    (((dirichletClassicalHeat_continuousOn g hK μ hμ O hO (scalarToLp hfL) ht).sub
      (continuous_of_smoothFn k.val.2.1).continuousOn).abs) continuousOn_const hAE
  have htK : t*K < ε/2 := by
    have hm := mul_lt_mul_of_pos_right htδ (show 0 < K+1 by linarith only [hK0])
    have hc : δ*(K+1)=ε/2 := by dsimp [δ]; field_simp
    rw [hc] at hm
    nlinarith only [hm,ht]
  intro x hx
  have htri := abs_sub_le (dirichletClassicalHeat g hK μ hμ O hO (scalarToLp hfL) x t) (k.val x) (f x)
  have hkx : |k.val x-f x| < ε/4 := by rw [abs_sub_comm];exact hk x
  have hpx := hpoint x hx
  simp only [Pi.sub_apply] at hpx
  linarith only [htri,hkx,hpx,htK]

end Yau.Proofs.F03Aux
