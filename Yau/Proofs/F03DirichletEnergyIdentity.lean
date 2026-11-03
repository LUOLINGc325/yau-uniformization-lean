import Yau.Proofs.F03DirichletDifferential

/-! Exact actual-measure scalar and one-form energy identities. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
open LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarEnergyDomainRestrictedL2_inner (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f k : ScalarEnergyDomain g μ hμ) :
    ⟪l2Restriction μ O (scalarEnergyDomainL2 g μ hμ f),
      l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k)⟫_ℝ =
        ∫ x in O, f x * k x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ f),
    restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ k),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ f),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ k)] with x hfr hkr hf hk
  simp only [l2Restriction_apply, RCLike.inner_apply, conj_trivial, hfr, hkr, hf, hk,
    mul_comm]

theorem scalarEnergyDomainD_inner (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f k : ScalarEnergyDomain g μ hμ) :
    ⟪scalarEnergyDomainD g μ hμ O f, scalarEnergyDomainD g μ hμ O k⟫_ℝ =
      ∫ x in O, scalarGradientPair g.form f k x ∂μ := by
  rw [scalarEnergyDomainD, scalarEnergyDomainD, realizeL2Form_inner]
  apply integral_congr_ae
  exact ae_of_all _ (scalarExterior_inner g.form f.2.1 k.2.1)

theorem scalarExterior_eq_zero_off_core (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : dirichletCore g μ hμ O) (x : M.Carrier) (hx : x ∉ O) :
    scalarExterior f.val x = 0 := by
  by_contra hn
  exact hx (f.property ((scalarExterior_support_subset f.val.2.1) (subset_closure hn)))

theorem dirichletCore_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f k : dirichletCore g μ hμ O) :
    ⟪f.val, k.val⟫_ℝ =
      ⟪l2Restriction μ O (scalarEnergyDomainL2 g μ hμ f.val),
        l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)⟫_ℝ +
      (1 / 2 : ℝ) * ⟪scalarEnergyDomainD g μ hμ O f.val,
        scalarEnergyDomainD g μ hμ O k.val⟫_ℝ := by
  rw [scalarEnergyDomainRestrictedL2_inner, scalarEnergyDomainD_inner,
    scalarEnergyDomain_inner]
  have hfint : (∫ x in O, f.val x * k.val x ∂μ) = ∫ x, f.val x * k.val x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hfzero : f.val x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hs => hx (f.property hs))
    rw [hfzero, zero_mul]
  have hdint : (∫ x in O, scalarGradientPair g.form f.val k.val x ∂μ) =
      ∫ x, scalarGradientPair g.form f.val k.val x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [← scalarExterior_inner g.form f.val.2.1 k.val.2.1 x]
    have he := formInner_congr_at g.form
      (A' := (0 : RealForm M 1)) (scalarExterior_eq_zero_off_core g μ hμ O f x hx)
      (B' := scalarExterior k.val) rfl
    exact he.trans (congrFun (formInner_zero_left g.form (scalarExterior k.val)) x)
  rw [hfint, hdint]
  rfl

/-- Exact completion identity. The factor one-half is the frozen paper
normalization and the derivative uses the actual one-form Hilbert space. -/
theorem dirichletEnergy_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (u v : DirichletEnergy g μ hμ O) :
    ⟪u, v⟫_ℝ = ⟪dirichletL2 g μ hμ O u, dirichletL2 g μ hμ O v⟫_ℝ +
      (1 / 2 : ℝ) * ⟪dirichletD g μ hμ O u, dirichletD g μ hμ O v⟫_ℝ := by
  let V := ScalarEnergySpace g μ hμ
  let S := (dirichletCore g μ hμ O).map
    (UniformSpace.Completion.toComplL : ScalarEnergyDomain g μ hμ →L[ℝ] V).toLinearMap
  let J := (l2Restriction μ O).comp (scalarEnergyL2 g μ hμ)
  let D := scalarEnergyD g μ hμ O
  let P : Set (V × V) := {p | ⟪p.1, p.2⟫_ℝ =
    ⟪J p.1, J p.2⟫_ℝ + (1 / 2 : ℝ) * ⟪D p.1, D p.2⟫_ℝ}
  have hclosed : IsClosed P := isClosed_eq (continuous_fst.inner continuous_snd)
    (((J.continuous.comp continuous_fst).inner (J.continuous.comp continuous_snd)).add
      (continuous_const.mul
        ((D.continuous.comp continuous_fst).inner (D.continuous.comp continuous_snd))))
  have hcore : (S : Set V) ×ˢ (S : Set V) ⊆ P := by
    rintro ⟨a, b⟩ ⟨⟨f, hf, rfl⟩, ⟨k, hk, rfl⟩⟩
    change ⟪(f : V), (k : V)⟫_ℝ =
      ⟪l2Restriction μ O (scalarEnergyL2 g μ hμ (f : V)),
        l2Restriction μ O (scalarEnergyL2 g μ hμ (k : V))⟫_ℝ +
      (1 / 2 : ℝ) * ⟪scalarEnergyD g μ hμ O (f : V),
        scalarEnergyD g μ hμ O (k : V)⟫_ℝ
    rw [UniformSpace.Completion.inner_coe, scalarEnergyL2_coe, scalarEnergyL2_coe,
      scalarEnergyD_coe, scalarEnergyD_coe]
    exact dirichletCore_inner g μ hμ O ⟨f, hf⟩ ⟨k, hk⟩
  have hmem : (u.val, v.val) ∈ closure ((S : Set V) ×ˢ (S : Set V)) := by
    rw [closure_prod_eq]
    exact ⟨u.property, v.property⟩
  exact (closure_minimal hcore hclosed) hmem

theorem dirichletEnergy_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (v : DirichletEnergy g μ hμ O) :
    ‖v‖ ^ 2 = ‖dirichletL2 g μ hμ O v‖ ^ 2 +
      (1 / 2 : ℝ) * ‖dirichletD g μ hμ O v‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using dirichletEnergy_inner g μ hμ O v v

end Yau.Proofs.F03Aux
