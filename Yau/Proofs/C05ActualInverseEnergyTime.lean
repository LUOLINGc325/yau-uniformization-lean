import Yau.Proofs.C05InverseEnergyTimeDerivative
import Yau.Proofs.C05ScalarDifferentialTime
import Yau.Proofs.C05RealRicciPositive

/-! The actual quadratic term in the original scalar Harnack inequality
has the explicitly computed physical-time derivative. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C05Aux
open Yau Blueprint Yau.LeafProofs Set Filter C04Aux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

def realScalarCovector (k : HermitianField X.manifold) (x : Pt X) : RIdx n → ℝ :=
  fun a => rDeriv (inChart x (scalarCurvature k)) (chartPt x x) a

def realScalarCovectorTime (h : Flow X) (x : Pt X) (t : ℝ) : RIdx n → ℝ :=
  fun a => rDeriv (inChart x (fun y => deriv (fun s => scalarCurvature (h s) y) t))
    (chartPt x x) a

def ricciDifferentialEnergyTime (h : Flow X) (x : Pt X) (t : ℝ) : ℝ :=
  let A := Matrix.of (realRicciCoeff (h t) x (chartPt x x))
  let B := (2 : ℝ) • Yau.NodeProofs.G01Aux.rawReal (levi (scalarCurvature (h t)) x)
  let p := realScalarCovector (h t) x
  let q := realScalarCovectorTime h x t
  (1 / 2 : ℝ) * ∑ a : RIdx n, ∑ b : RIdx n,
    ((-(A⁻¹ * B * A⁻¹)) a b * p a * p b + A⁻¹ a b * q a * p b + A⁻¹ a b * p a * q b)

theorem realRicciDifferentialEnergy_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realRicciDifferentialEnergy (h s) (scalarCurvature (h s)) x)
      (ricciDifferentialEnergyTime h x t) t := by
  let A := fun s => Matrix.of (realRicciCoeff (h s) x (chartPt x x))
  let p := fun s => realScalarCovector (h s) x
  let B := (2 : ℝ) • Yau.NodeProofs.G01Aux.rawReal (levi (scalarCurvature (h t)) x)
  let q := realScalarCovectorTime h x t
  have hAd (a b : RIdx n) : HasDerivAt (fun s => A s a b) (B a b) t :=
    realRicci_hasDerivAt_scalar_levi o h U P ρ hf x ht a b
  have hu := localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf
  have hpd (a : RIdx n) : HasDerivAt (fun s => p s a) (q a) t :=
    hasDerivAt_rDeriv_of_smoothSpaceTime isOpen_Ioi hu x (mem_extChartAt_target x) ht a
  have ht0 : t ∈ Ici (0 : ℝ) := by change 0 ≤ t; exact ht.le
  have hdet : (A t).det ≠ 0 := (realRicciMatrix_posDef (h t)
    (L23Aux.metricFamilySmooth_slice h hf.1.2.1 ht0) (hf.1.2.2.1 t ht.le) x
    (hH.2.2.1 t ht.le x)).det_pos.ne'
  have hd := inverseMatrixEnergy_hasDerivAt A p B q t hAd hpd hdet
  have he : (fun s => realRicciDifferentialEnergy (h s) (scalarCurvature (h s)) x) =
      (fun s => (1 / 2 : ℝ) * (p s ⬝ᵥ ((A s)⁻¹ *ᵥ p s))) := by
    funext s
    unfold realRicciDifferentialEnergy
    congr 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [A, p, realScalarCovector]
    ring
  rw [he]
  exact hd

theorem scalarHarnackQuadratic_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => dualNormMat (ricci (h s) x) (scalarCovector (h s) x))
      (ricciDifferentialEnergyTime h x t) t := by
  apply (realRicciDifferentialEnergy_hasDerivAt o h U P ρ hf hH x ht).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hspos : 0 < s := hs
  have hs0 : s ∈ Ici (0 : ℝ) := by change 0 ≤ s; exact hspos.le
  exact scalar_differential_ricci_dual_eq (h s)
    (L23Aux.metricFamilySmooth_slice h hf.1.2.1 hs0) (hf.1.2.2.1 s hspos.le)
    (scalarCurvature (h s)) (spaceSlice_smoothFn
      (localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf) hspos) x (hH.2.2.1 s hspos.le x)

end Yau.Proofs.C05Aux
