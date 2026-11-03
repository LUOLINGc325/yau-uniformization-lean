import Yau.Proofs.C01RicciFrameCoercivity
import Yau.Proofs.C01MetricQuadraticJets

/-! The actual Kähler--Ricci equation integrates a quantitative relative
Ricci bound into the original power decay of the metric. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_metric_weight_antitoneOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (c : ℝ)
    (hbound : ∀ t, 1 ≤ t → ∀ v : Fin n → ℂ,
      c * (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re ≤
        t * (star v ⬝ᵥ (ricci (h t) x *ᵥ v)).re) (v : Fin n → ℂ) :
    AntitoneOn (fun t => t ^ c * (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re) (Set.Ici 1) := by
  have hd (t : ℝ) (ht : t ∈ Set.Ici 1) :
      HasDerivAt (fun s => s ^ c * (star v ⬝ᵥ (gMat (h s) x *ᵥ v)).re)
        (c * t ^ (c - 1) * (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re +
          t ^ c * (-(star v ⬝ᵥ (ricci (h t) x *ᵥ v)).re)) t := by
    have htpos : 0 < t := zero_lt_one.trans_le ht
    simpa only [Complex.neg_re, Pi.mul_apply] using!
      (Real.hasDerivAt_rpow_const (p := c) (Or.inl htpos.ne')).mul
        (localizedFlow_metric_quadratic_hasDerivAt hflow x htpos v)
  apply antitoneOn_of_deriv_nonpos (convex_Ici (1 : ℝ))
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have htc := interior_subset ht
    have htpos : 0 < t := zero_lt_one.trans_le htc
    rw [(hd t htc).deriv]
    have hpow : t ^ (c - 1) * t = t ^ c := by
      rw [Real.rpow_sub_one htpos.ne' c, div_mul_cancel₀ _ htpos.ne']
    calc
      _ = t ^ (c - 1) * (c * (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re -
          t * (star v ⬝ᵥ (ricci (h t) x *ᵥ v)).re) := by rw [← hpow]; ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.rpow_pos_of_pos htpos _).le
        (sub_nonpos.mpr (hbound t htc v))

theorem localizedFlow_metric_power_quadratic_bound
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (c : ℝ)
    (hbound : ∀ t, 1 ≤ t → ∀ v : Fin n → ℂ,
      c * (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re ≤
        t * (star v ⬝ᵥ (ricci (h t) x *ᵥ v)).re)
    (t : ℝ) (ht : 1 ≤ t) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re ≤
      t ^ (-c) * (star v ⬝ᵥ (gMat X.metric.form x *ᵥ v)).re := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hanti := localizedFlow_metric_weight_antitoneOn hflow x c hbound v
    (show (1 : ℝ) ∈ Set.Ici 1 by change (1 : ℝ) ≤ 1; exact le_rfl) ht ht
  have hanti' : t ^ c * (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re ≤
      (star v ⬝ᵥ (gMat (h 1) x *ᵥ v)).re := by
    simpa only [Real.one_rpow, one_mul] using hanti
  have hg := hflow.2.2.2.2.1 1 zero_le_one x
  change (gMat X.metric.form x - gMat (h 1) x).PosSemidef at hg
  have hgq : (star v ⬝ᵥ (gMat (h 1) x *ᵥ v)).re ≤
      (star v ⬝ᵥ (gMat X.metric.form x *ᵥ v)).re := by
    simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using
      (Complex.nonneg_iff.mp (hg.dotProduct_mulVec_nonneg v)).1
  have hm := mul_le_mul_of_nonneg_left (hanti'.trans hgq) (Real.rpow_pos_of_pos htpos (-c)).le
  have hcancel : t ^ (-c) * t ^ c = 1 := by
    rw [← Real.rpow_add htpos, neg_add_cancel, Real.rpow_zero]
  simpa only [← mul_assoc, hcancel, one_mul] using hm

theorem localizedFlow_metric_power_bound
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (c : ℝ)
    (hbound : ∀ t, 1 ≤ t → ∀ v : Fin n → ℂ,
      c * (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re ≤
        t * (star v ⬝ᵥ (ricci (h t) x *ᵥ v)).re)
    (t : ℝ) (ht : 1 ≤ t) :
    HermLE (gMat (h t) x) (((t ^ (-c) : ℝ) : ℂ) • gMat X.metric.form x) := by
  have hH (g : HermitianField X.manifold) : (gMat g x).IsHermitian :=
    (Alignment.Y03Proof.hMat_posDef g x (chartPt x x)
      (mem_extChartAt_target (I := ComplexModel n) x)).isHermitian
  have hherm : ((((t ^ (-c) : ℝ) : ℂ) • gMat X.metric.form x) - gMat (h t) x).IsHermitian :=
    ((hH X.metric.form).smul (by simp [IsSelfAdjoint])).sub (hH (h t))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hherm.im_star_dotProduct_mulVec_self v).symm⟩
  simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, sub_nonneg] using
      localizedFlow_metric_power_quadratic_bound hflow x c hbound t ht v

end Yau.NodeProofs.C01Aux
