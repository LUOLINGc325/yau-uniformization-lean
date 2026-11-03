import Yau.LeafProofs.L05ABPMollifierPeano
import Yau.LeafProofs.L05ABPLimit

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem pastSupport_of_frequently_contact {n : ℕ} {R a b : ℝ}
    {u : ℕ → Point n → ℝ} {w : Point n → ℝ} {z : Point n} {xi : Space n}
    (hz : z ∈ abpOpen n R a b)
    (hvalues : ∀ q ∈ abpClosed n R a b, Tendsto (fun j => u j q) atTop (𝓝 (w q)))
    (hgrad : Tendsto (fun j => spatialGrad (u j) z) atTop (𝓝 xi))
    (hcontact : ∃ᶠ j in atTop, z ∈ smoothContact R a b (u j)) :
    pastSupports R a w z xi := by
  intro y hy s hs
  have hzD : z ∈ abpClosed n R a b :=
    ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2.le⟩
  have hqD : (y,s) ∈ abpClosed n R a b := ⟨hy,hs.1,hs.2.trans hz.2.2.le⟩
  exact le_of_tendsto_of_tendsto_of_frequently (hvalues (y,s) hqD)
    ((hvalues z hzD).add (hgrad.inner tendsto_const_nhds))
    (hcontact.mono fun j hj => hj.2 y hy s hs)

theorem contact_signs_of_frequently {n : ℕ} {R a b : ℝ}
    {u : ℕ → Point n → ℝ} {z : Point n} {a0 : ℝ} {H : Sym n}
    (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (ht : Tendsto (fun j => timeD Set.univ (u j) z) atTop (𝓝 a0))
    (hH : Tendsto (fun j => hessian (u j) z) atTop (𝓝 H))
    (hcontact : ∃ᶠ j in atTop, z ∈ smoothContact R a b (u j)) :
    0≤a0 ∧ (-(H : Mat n)).PosSemidef := by
  refine ⟨ge_of_tendsto_of_frequently ht
    (hcontact.mono fun j hj => smoothContact_time_nonneg (hu j) hj),?_⟩
  have hcoer := (continuous_subtype_val.tendsto H).comp hH
  have hclosed : IsClosed {A : Mat n | A.PosSemidef} := Matrix.posSemidef_is_closed
  exact hclosed.mem_of_frequently_of_tendsto
    (hcontact.mono fun j hj => smoothContact_hessian_nonpos (hu j) hj) hcoer.neg

theorem contact_absJacobian_tendsto {n : ℕ} {u : ℕ → Point n → ℝ} {z : Point n}
    {a0 : ℝ} {H : Sym n} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (ht : Tendsto (fun j => timeD Set.univ (u j) z) atTop (𝓝 a0))
    (hH : Tendsto (fun j => hessian (u j) z) atTop (𝓝 H)) :
    Tendsto (fun j => |(fderiv ℝ (contactMap (u j)) z).det|) atTop (𝓝 |a0*Matrix.det (H : Mat n)|) := by
  have hcoer := (continuous_subtype_val.tendsto H).comp hH
  have hc : Continuous (Matrix.det : Mat n → ℝ) := by fun_prop
  have hd := (hc.tendsto (H : Mat n)).comp hcoer
  have hi := (ht.mul hd).abs
  convert! hi using 1
  funext j
  rw [contactMap_det (hu j) z]
  rfl

theorem smoothContactDensity_le_absJacobian {n : ℕ} (R a b : ℝ) (u : Point n → ℝ) (z : Point n) :
    smoothContactDensity R a b u z≤|(fderiv ℝ (contactMap u) z).det| := by
  by_cases hz : z ∈ smoothContact R a b u
  · simp [smoothContactDensity,hz]
  · simp [smoothContactDensity,hz]

/-- A pointwise source bound uses a frequent contact limit; the exceptional
Peano set is never sent through a nonsmooth contact map. -/
theorem smoothContactDensity_limsup_bound {n : ℕ} {R a b k G : ℝ}
    {u : ℕ → Point n → ℝ} {w : Point n → ℝ} {z : Point n} {xi : Space n}
    {a0 : ℝ} {H : Sym n} (hk : 0<k) (hz : z ∈ abpOpen n R a b)
    (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hvalues : ∀ q ∈ abpClosed n R a b, Tendsto (fun j => u j q) atTop (𝓝 (w q)))
    (hgrad : Tendsto (fun j => spatialGrad (u j) z) atTop (𝓝 xi))
    (ht : Tendsto (fun j => timeD Set.univ (u j) z) atTop (𝓝 a0))
    (hH : Tendsto (fun j => hessian (u j) z) atTop (𝓝 H))
    (hsource : pastSupports R a w z xi → a0+k*Matrix.trace (-(H : Mat n))≤G) :
    limsup (fun j => ENNReal.ofReal (smoothContactDensity R a b (u j) z)) atTop ≤
      ENNReal.ofReal ((k⁻¹)^(2*n)*(max G 0)^(2*n+1)) := by
  by_cases hc : ∃ᶠ j in atTop, z ∈ smoothContact R a b (u j)
  · have hs := pastSupport_of_frequently_contact hz hvalues hgrad hc
    obtain ⟨ha,hneg⟩ := contact_signs_of_frequently hu ht hH hc
    have hdet := contact_determinant_bound hneg ha hk (hsource hs)
    have he : Matrix.det (-(H : Mat n))=Matrix.det (H : Mat n) := by
      rw [Matrix.det_neg]
      simp [Yau.RIdx]
    have habs : |a0*Matrix.det (H : Mat n)|=a0*Matrix.det (-(H : Mat n)) := by
      rw [abs_mul,abs_of_nonneg ha,← he,abs_of_nonneg hneg.det_nonneg]
    have hJ := contact_absJacobian_tendsto hu ht hH
    have hE := (ENNReal.continuous_ofReal.tendsto |a0*Matrix.det (H : Mat n)|).comp hJ
    simp only [Function.comp_def] at hE
    have hupper := limsup_le_limsup (f := atTop) (Filter.Eventually.of_forall fun j =>
      ENNReal.ofReal_le_ofReal (smoothContactDensity_le_absJacobian R a b (u j) z))
    rw [hE.limsup_eq,habs] at hupper
    apply hupper.trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using hdet
  · have hevent : ∀ᶠ j in atTop, z ∉ smoothContact R a b (u j) := not_frequently.mp hc
    have heq : (fun j => ENNReal.ofReal (smoothContactDensity R a b (u j) z))=ᶠ[atTop]
        (fun _ => (0 : ENNReal)) := by
      filter_upwards [hevent] with j hj
      simp [smoothContactDensity,hj]
    rw [limsup_congr heq,limsup_const]
    exact bot_le

end Yau.LeafProofs.L05Aux
