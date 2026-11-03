import Yau.Proofs.F05BootstrapSmoothRelative

/-! Exact fixed coefficients after subtracting a smooth physical datum.
Every mixed principal entry and the full first-order drift is retained. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05DatumPrincipal (p : Point n → ℝ) (A : Point n → Mat n) (z : Point n) : Mat n :=
  Real.exp (-p z) • A z

def F05DatumDrift (p : Point n → ℝ) (B : Point n → RIdx n → ℝ) (z : Point n) (j : RIdx n) : ℝ :=
  Real.exp (-p z)*B z j

def F05DatumSource (p : Point n → ℝ) (A : Point n → Mat n)
    (B : Point n → RIdx n → ℝ) (R : Point n → ℝ) (z : Point n) : ℝ :=
  Real.exp (-p z)*((∑ j,∑ k,A z j k*spatialDD p z (realVec j) (realVec k))+
    (∑ j,B z j*spatialD p z (realVec j))-R z)

def F05DatumFree (T : ℝ) (p R : Point n → ℝ) (z : Point n) : ℝ :=
  R z-F05GoodPartial T none p z

theorem F05_datum_coefficients_smooth {T : ℝ}
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (R p : Point n → ℝ)
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hB : ∀ j, ContDiffOn ℝ ∞ (fun z => B z j) (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hp : ContDiffOn ℝ ∞ p (Metric.ball 0 3 ×ˢ Ioc 0 T)) :
    ContDiffOn ℝ ∞ (F05DatumPrincipal p A) (Metric.ball 0 3 ×ˢ Ioc 0 T) ∧
      (∀ j, ContDiffOn ℝ ∞ (fun z => F05DatumDrift p B z j) (Metric.ball 0 3 ×ˢ Ioc 0 T)) ∧
      ContDiffOn ℝ ∞ (F05DatumSource p A B R) (Metric.ball 0 3 ×ˢ Ioc 0 T) ∧
      ContDiffOn ℝ ∞ (F05DatumFree T p R) (Metric.ball 0 3 ×ˢ Ioc 0 T) := by
  have hExp := hp.neg.exp
  have hJets := F05_joint_spatial_jets_smooth Metric.isOpen_ball hp
  have hTime := F05_joint_vector_time_derivative_smooth (uniqueDiffOn_Ioc 0 T) hp
  have hAE (j k : RIdx n) : ContDiffOn ℝ ∞ (fun z => A z j k) (Metric.ball 0 3 ×ˢ Ioc 0 T) :=
    (matrixEntryCLM j k).contDiff.comp_contDiffOn hA
  have hHE (j k : RIdx n) : ContDiffOn ℝ ∞ (fun z => spatialDD p z (realVec j) (realVec k))
      (Metric.ball 0 3 ×ˢ Ioc 0 T) :=
    (hJets.2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hGE (j : RIdx n) : ContDiffOn ℝ ∞ (fun z => spatialD p z (realVec j))
      (Metric.ball 0 3 ×ˢ Ioc 0 T) := hJets.1.clm_apply contDiffOn_const
  have hPrincipal := ContDiffOn.sum (fun j (_ : j ∈ (Finset.univ : Finset (RIdx n))) =>
    ContDiffOn.sum (fun k (_ : k ∈ (Finset.univ : Finset (RIdx n))) => (hAE j k).mul (hHE j k)))
  have hDrift := ContDiffOn.sum (fun j (_ : j ∈ (Finset.univ : Finset (RIdx n))) => (hB j).mul (hGE j))
  exact ⟨hExp.smul hA,fun j => hExp.mul (hB j),hExp.mul ((hPrincipal.add hDrift).sub hR),hR.sub hTime⟩

end Yau.Proofs.F05Aux
