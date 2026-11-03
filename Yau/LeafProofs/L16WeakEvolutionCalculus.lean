import Yau.LeafProofs.L16WeakSchwarz

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The concrete distributional evolution identity on an arbitrary coordinate region. -/
def WeakDivergenceEvolutionOn {n : ℕ} (Q : Set (Point n))
    (w : Point n → ℝ) (P : Point n → Yau.RIdx n → ℝ) (R : Point n → ℝ) : Prop :=
  ∀ φ : Point n → ℝ, Test Q φ →
    -(∫ p, w p*fderiv ℝ φ p (0,1) ∂volume.restrict Q)+
      (∑ i, ∫ p, P p i*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict Q)-
      (∫ p, R p*φ p ∂volume.restrict Q) = 0

theorem integral_divergence_test_form {n : ℕ} {Q : Set (Point n)}
    {w R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 (volume.restrict Q))
    (hP : ∀ i, MemLp (fun p => P p i) 2 (volume.restrict Q))
    (hR : MemLp R 2 (volume.restrict Q)) {φ : Point n → ℝ} (hφ : Test Q φ) :
    (∫ p, -w p*fderiv ℝ φ p (0,1)+
      (∑ i, P p i*fderiv ℝ φ p (Yau.realVec i,0))-R p*φ p ∂volume.restrict Q) =
      -(∫ p, w p*fderiv ℝ φ p (0,1) ∂volume.restrict Q)+
      (∑ i, ∫ p, P p i*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict Q)-
      (∫ p, R p*φ p ∂volume.restrict Q) := by
  have hTime : Integrable (fun p => w p*fderiv ℝ φ p (0,1)) (volume.restrict Q) :=
    hw.integrable_mul (test_memLp (test_directionalDerivative hφ (0,1)))
  have hSpace (i : Yau.RIdx n) :
      Integrable (fun p => P p i*fderiv ℝ φ p (Yau.realVec i,0)) (volume.restrict Q) :=
    (hP i).integrable_mul (test_memLp (test_directionalDerivative hφ (Yau.realVec i,0)))
  have hSource : Integrable (fun p => R p*φ p) (volume.restrict Q) :=
    hR.integrable_mul (test_memLp hφ)
  have hTimeNeg : Integrable (fun p => -w p*fderiv ℝ φ p (0,1)) (volume.restrict Q) := by
    convert! hTime.neg using 1
    ext p
    simp only [Pi.neg_apply,neg_mul]
  have hSum := integrable_finsetSum Finset.univ (fun i _ => hSpace i)
  have hA := integral_add hTimeNeg hSum
  have hS := integral_sub (hTimeNeg.add hSum) hSource
  simp only [Pi.add_apply] at hS
  rw [hS,hA,integral_finsetSum Finset.univ (fun i _ => hSpace i)]
  simp only [neg_mul,integral_neg]

theorem weakDivergenceEvolutionOn_prod_iff {n : ℕ}
    (O : Set (Space n)) (I : Set ℝ) {w R : Point n → ℝ}
    {P : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 (volume.restrict (O ×ˢ I)))
    (hP : ∀ i, MemLp (fun p => P p i) 2 (volume.restrict (O ×ˢ I)))
    (hR : MemLp R 2 (volume.restrict (O ×ˢ I))) :
    WeakDivergenceEvolutionOn (O ×ˢ I) w P R ↔ WeakDivergenceEvolution O I w P R := by
  constructor
  · intro h φ hφ
    rw [productVolume_eq_restrict]
    simp_rw [test_timeDerivative_eq_joint_fderiv (hφ.1.differentiable (by simp) _),
      d_eq_joint_fderiv (hφ.1.differentiable (by simp) _)]
    rw [integral_divergence_test_form hw hP hR hφ]
    exact h φ hφ
  · intro h φ hφ
    have hEq := h φ hφ
    rw [productVolume_eq_restrict] at hEq
    simp_rw [test_timeDerivative_eq_joint_fderiv (hφ.1.differentiable (by simp) _),
      d_eq_joint_fderiv (hφ.1.differentiable (by simp) _)] at hEq
    rw [integral_divergence_test_form hw hP hR hφ] at hEq
    exact hEq

theorem weakDivergenceEvolutionOn_mono {n : ℕ} {Q V : Set (Point n)}
    {w R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hEq : WeakDivergenceEvolutionOn Q w P R) (hVQ : V ⊆ Q) :
    WeakDivergenceEvolutionOn V w P R := by
  intro φ hφ
  have hφQ : Test Q φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans hVQ⟩
  have h := hEq φ hφQ
  simp_rw [test_pairing_integral_restrict (test_directionalDerivative hφQ (0,1)) w,
    test_pairing_integral_restrict (test_directionalDerivative hφQ (Yau.realVec _,0)) _,
    test_pairing_integral_restrict hφQ R] at h
  simp_rw [test_pairing_integral_restrict (test_directionalDerivative hφ (0,1)) w,
    test_pairing_integral_restrict (test_directionalDerivative hφ (Yau.realVec _,0)) _,
    test_pairing_integral_restrict hφ R]
  exact h

theorem weakDivergenceEvolutionOn_spatial_derivative {n : ℕ} {Q : Set (Point n)}
    {w R : Point n → ℝ} {H P J : Point n → Yau.RIdx n → ℝ}
    {K : Yau.RIdx n → Point n → Yau.RIdx n → ℝ}
    (hEq : WeakDivergenceEvolutionOn Q w P R) (hW : WeakGradientOn Q w H)
    (hP : ∀ j, WeakGradientOn Q (fun p => P p j) (K j))
    (hR : WeakGradientOn Q R J) (i : Yau.RIdx n) :
    WeakDivergenceEvolutionOn Q (fun p => H p i) (fun p j => K j p i) (fun p => J p i) := by
  intro φ hφ
  have h := hEq (fun p => fderiv ℝ φ p (Yau.realVec i,0))
    (test_directionalDerivative hφ (Yau.realVec i,0))
  have hTime := hW (fun p => fderiv ℝ φ p (0,1)) (test_directionalDerivative hφ (0,1)) i
  have hSpace (j : Yau.RIdx n) := hP j (fun p => fderiv ℝ φ p (Yau.realVec j,0))
    (test_directionalDerivative hφ (Yau.realVec j,0)) i
  have hSource := hR φ hφ i
  have hComm (e v p : Point n) : fderiv ℝ (fun q => fderiv ℝ φ q e) p v =
      fderiv ℝ (fun q => fderiv ℝ φ q v) p e := by
    exact directional_gradient_commute (hφ.1.of_le (by simp)) p v e
  have hTimeEq : (∫ p, w p*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec i,0)) p (0,1) ∂volume.restrict Q) =
      -(∫ p, H p i*fderiv ℝ φ p (0,1) ∂volume.restrict Q) := by
    calc
      _ = ∫ p, w p*fderiv ℝ (fun q => fderiv ℝ φ q (0,1)) p (Yau.realVec i,0) ∂volume.restrict Q := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun p => congrArg (fun z => w p*z) (hComm (Yau.realVec i,0) (0,1) p))
      _ = _ := hTime
  have hSpaceEq (j : Yau.RIdx n) :
      (∫ p, P p j*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec i,0)) p (Yau.realVec j,0) ∂volume.restrict Q) =
        -(∫ p, K j p i*fderiv ℝ φ p (Yau.realVec j,0) ∂volume.restrict Q) := by
    calc
      _ = ∫ p, P p j*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec j,0)) p (Yau.realVec i,0) ∂volume.restrict Q := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun p => congrArg (fun z => P p j*z) (hComm (Yau.realVec i,0) (Yau.realVec j,0) p))
      _ = _ := hSpace j
  change -(∫ p, w p*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec i,0)) p (0,1) ∂volume.restrict Q)+
    (∑ j, ∫ p, P p j*fderiv ℝ (fun q => fderiv ℝ φ q (Yau.realVec i,0)) p (Yau.realVec j,0) ∂volume.restrict Q)-
    (∫ p, R p*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict Q) = 0 at h
  rw [hTimeEq,hSource] at h
  simp_rw [hSpaceEq] at h
  rw [Finset.sum_neg_distrib] at h
  linarith

theorem weakDivergenceEvolutionOn_congr_ae {n : ℕ} {Q : Set (Point n)}
    {w w' R R' : Point n → ℝ} {P P' : Point n → Yau.RIdx n → ℝ}
    (hEq : WeakDivergenceEvolutionOn Q w P R)
    (hw : w =ᵐ[volume.restrict Q] w')
    (hP : ∀ i, (fun p => P p i) =ᵐ[volume.restrict Q] (fun p => P' p i))
    (hR : R =ᵐ[volume.restrict Q] R') : WeakDivergenceEvolutionOn Q w' P' R' := by
  intro φ hφ
  have hTime : (∫ p, w p*fderiv ℝ φ p (0,1) ∂volume.restrict Q) =
      ∫ p, w' p*fderiv ℝ φ p (0,1) ∂volume.restrict Q := by
    apply integral_congr_ae
    filter_upwards [hw] with p hp
    rw [hp]
  have hSpace (i : Yau.RIdx n) : (∫ p, P p i*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict Q) =
      ∫ p, P' p i*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict Q := by
    apply integral_congr_ae
    filter_upwards [hP i] with p hp
    rw [hp]
  have hSource : (∫ p, R p*φ p ∂volume.restrict Q) =
      ∫ p, R' p*φ p ∂volume.restrict Q := by
    apply integral_congr_ae
    filter_upwards [hR] with p hp
    rw [hp]
  have h := hEq φ hφ
  rw [hTime,hSource] at h
  simp_rw [hSpace] at h
  exact h

end Yau.LeafProofs.L16Aux
