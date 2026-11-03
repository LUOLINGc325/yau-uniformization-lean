import Yau.Proofs.F04CoreGarding
import Yau.Proofs.F04FlowTraceBound

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.Proofs.F03Aux Yau.LeafProofs.L18Aux

variable {n : ℕ}

theorem scalarGradientPair_young {m : ℕ} {M : ComplexManifold m}
    (H : HermitianField M) (u v : M.Carrier → ℝ) (x : M.Carrier) :
    2 * |scalarGradientPair H u v x| ≤ scalarGradientPair H u u x + scalarGradientPair H v v x := by
  have hc := scalarGradientPair_cauchy H u v x
  have hu := scalarGradientPair_self_nonneg H u x
  have hv := scalarGradientPair_self_nonneg H v x
  nlinarith [sq_nonneg (scalarGradientPair H u u x - scalarGradientPair H v v x),
    sq_abs (scalarGradientPair H u v x), abs_nonneg (scalarGradientPair H u v x)]

theorem flow_core_quadratic_bound_with_coefficients
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O K : Set (Pt X)) (hOK : O ⊆ K) {t : ℝ} (ht : 0 ≤ t)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcomp : ∀ f : Pt X → ℝ, SmoothFn f → ∀ x ∈ K,
      scalarGradientPair (h t) f f x ≤ C * scalarGradientPair X.metric.form f f x)
    (hDb : ∀ x ∈ K, scalarGradientPair (h t) (fun y => ρ y t) (fun y => ρ y t) x ≤ D)
    (f v : dirichletCore X.metric μ hμ O) :
    |-(∫ x, v.val x * laplacian (h t) f.val x ∂μ)| ≤
      (C + D + 1) * (‖dirichletCoreEmbedding X.metric μ hμ O f‖ ^ 2 +
        ‖dirichletCoreEmbedding X.metric μ hμ O v‖ ^ 2) := by
  have hg := flow_fixed_volume_green X o h U P ρ hloc μ hμ ht f.val.2.1 v.val.2.1 v.val.2.2
  have hEf := scalarGradientPair_integrable X.metric μ hμ f.val.2.1 f.val.2.1 f.val.2.2
  have hEv := scalarGradientPair_integrable X.metric μ hμ v.val.2.1 v.val.2.1 v.val.2.2
  have hFf : Integrable (fun x => f.val x * f.val x) μ :=
    smoothFn_integrable_compact X.metric μ hμ (smoothFn_mul f.val.2.1 f.val.2.1) f.val.2.2.mul_right
  have hFv : Integrable (fun x => v.val x * v.val x) μ :=
    smoothFn_integrable_compact X.metric μ hμ (smoothFn_mul v.val.2.1 v.val.2.1) v.val.2.2.mul_right
  let Pp := fun x => scalarGradientPair (h t) v.val f.val x
  let Dr := fun x => v.val x * scalarGradientPair (h t) (fun y => ρ y t) f.val x
  let Rhs := fun x => C * (scalarGradientPair X.metric.form f.val f.val x +
      scalarGradientPair X.metric.form v.val v.val x) + D * (f.val x * f.val x + v.val x * v.val x)
  have hp (x : Pt X) : |Pp x + Dr x| ≤ Rhs x := by
    dsimp only [Pp, Dr, Rhs]
    by_cases hx : x ∈ K
    · have hpr := scalarGradientPair_young (h t) v.val f.val x
      have hdr := scalarGradientPair_drift_absorption (h t) (fun y => ρ y t) f.val x (v.val x) D (hDb x hx)
      have hcf := hcomp f.val f.val.2.1 x hx
      have hcv := hcomp v.val v.val.2.1 x hx
      have hev := scalarGradientPair_self_nonneg X.metric.form v.val x
      nlinarith [abs_add_le (scalarGradientPair (h t) v.val f.val x)
        (v.val x * scalarGradientPair (h t) (fun y => ρ y t) f.val x),
        mul_nonneg hC hev, mul_nonneg hD (sq_nonneg (f.val x)), mul_nonneg hD (sq_nonneg (v.val x))]
    · have hxf : x ∉ tsupport (f.val : Pt X → ℝ) := fun hs => hx (hOK (f.property hs))
      have hxv : x ∉ tsupport (v.val : Pt X → ℝ) := fun hs => hx (hOK (v.property hs))
      rw [scalarGradientPair_zero_of_notMem_tsupport (h t) v.val f.val hxv,
        scalarGradientPair_zero_of_notMem_tsupport X.metric.form f.val f.val hxf,
        scalarGradientPair_zero_of_notMem_tsupport X.metric.form v.val v.val hxv,
        image_eq_zero_of_notMem_tsupport hxf, image_eq_zero_of_notMem_tsupport hxv]
      simp only [zero_mul, mul_zero, add_zero, abs_zero, le_refl]
  have hRi : Integrable Rhs μ := ((hEf.add hEv).const_mul C).add ((hFf.add hFv).const_mul D)
  have hi := integral_mono (hg.2.1.add hg.2.2.1).norm hRi hp
  have heR : (∫ x, Rhs x ∂μ) =
      C * ((∫ x, scalarGradientPair X.metric.form f.val f.val x ∂μ) +
        ∫ x, scalarGradientPair X.metric.form v.val v.val x ∂μ) +
      D * ((∫ x, f.val x * f.val x ∂μ) + ∫ x, v.val x * v.val x ∂μ) := by
    dsimp only [Rhs]
    have ho := integral_add ((hEf.add hEv).const_mul C) ((hFf.add hFv).const_mul D)
    have hE := integral_add hEf hEv
    have hF := integral_add hFf hFv
    dsimp only [Pi.add_apply] at ho hE hF
    rw [ho, integral_const_mul, integral_const_mul, hE, hF]
  rw [heR] at hi
  have hn : |∫ x, Pp x + Dr x ∂μ| ≤ ∫ x, |Pp x + Dr x| ∂μ := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := fun x => Pp x + Dr x) (μ := μ))
  have hbound : |-(∫ x, v.val x * laplacian (h t) f.val x ∂μ)| ≤
      (1 / 2 : ℝ) * (C * ((∫ x, scalarGradientPair X.metric.form f.val f.val x ∂μ) +
        ∫ x, scalarGradientPair X.metric.form v.val v.val x ∂μ) +
      D * ((∫ x, f.val x * f.val x ∂μ) + ∫ x, v.val x * v.val x ∂μ)) := by
    rw [hg.2.2.2, ← integral_add hg.2.1 hg.2.2.1, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left (hn.trans hi) (by norm_num)
  rw [dirichletCoreEmbedding_norm_integral, dirichletCoreEmbedding_norm_integral]
  have hE0 : 0 ≤ (∫ x, scalarGradientPair X.metric.form f.val f.val x ∂μ) +
      ∫ x, scalarGradientPair X.metric.form v.val v.val x ∂μ := add_nonneg (integral_nonneg (scalarGradientPair_self_nonneg X.metric.form f.val))
    (integral_nonneg (scalarGradientPair_self_nonneg X.metric.form v.val))
  have hF0 : 0 ≤ (∫ x, f.val x * f.val x ∂μ) + ∫ x, v.val x * v.val x ∂μ := add_nonneg (integral_nonneg (fun x => mul_self_nonneg (f.val x)))
    (integral_nonneg (fun x => mul_self_nonneg (v.val x)))
  nlinarith [mul_nonneg hC hF0, mul_nonneg hD hE0, mul_nonneg hD hF0]

theorem flow_core_quadratic_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O K : Set (Pt X)) (hK : IsCompact K) (hOK : O ⊆ K) {S : ℝ} (hS : 0 < S) :
    ∃ A : ℝ, 0 < A ∧ ∀ t ∈ Icc 0 S, ∀ f v : dirichletCore X.metric μ hμ O,
      |-(∫ x, v.val x * laplacian (h t) f.val x ∂μ)| ≤
        A * (‖dirichletCoreEmbedding X.metric μ hμ O f‖ ^ 2 +
          ‖dirichletCoreEmbedding X.metric μ hμ O v‖ ^ 2) := by
  obtain ⟨C, hC, hCb⟩ := flow_compact_gradient_comparison X o h U P ρ hloc hS K hK
  obtain ⟨D, hD, hDb⟩ := flow_rho_gradient_bound X o h U P ρ hloc hS K hK
  refine ⟨C + D + 1, by positivity, ?_⟩
  intro t ht f v
  exact flow_core_quadratic_bound_with_coefficients X o h U P ρ hloc μ hμ O K hOK ht.1
    C D hC.le hD.le (fun k hk x hx => (hCb k hk x hx t ht).2)
      (fun x hx => hDb x hx t ht) f v

end Yau.F04Proof
