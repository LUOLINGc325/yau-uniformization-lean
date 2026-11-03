import Yau.Proofs.F05HolderGauge
import Yau.LeafProofs.L16ExpBoundaryHolderAmplitude

/-! The elementary amplitude estimates with the actual signed flat gauge.
The set carrying the data can be a buffered chart rather than a whole domain. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

theorem F05_min_error_time {Q : Set (Point n)} {k : Option (RIdx n)} {K : ℝ}
    {u G : Point n → ℝ} (hK : 0 ≤ K)
    (he : ∀ z ∈ Q, |u z-G z| ≤ K*min z.2 (F05FaceGauge k z.1)) :
    ∀ z ∈ Q, |u z-G z| ≤ K*z.2 :=
  fun z hz => (he z hz).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK)

theorem F05_min_error_face {Q : Set (Point n)} {k : Option (RIdx n)} {K : ℝ}
    {u G : Point n → ℝ} (hK : 0 ≤ K)
    (he : ∀ z ∈ Q, |u z-G z| ≤ K*min z.2 (F05FaceGauge k z.1)) :
    ∀ z ∈ Q, |u z-G z| ≤ K*F05FaceGauge k z.1 :=
  fun z hz => (he z hz).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK)

theorem F05_faceGauge_le_add (k : Option (RIdx n)) (x y : Space n) :
    F05FaceGauge k x ≤ F05FaceGauge k y+‖x-y‖ := by
  have h := (le_abs_self (F05FaceGauge k x-F05FaceGauge k y)).trans
    (F05FaceGauge_lipschitz k x y)
  linarith

theorem F05_near_pair_linear_bound {Q : Set (Point n)} {k : Option (RIdx n)} {K L : ℝ}
    {u G : Point n → ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (he : ∀ z ∈ Q, |u z-G z| ≤ K*min z.2 (F05FaceGauge k z.1))
    (hLip : ∀ p ∈ Q, ∀ q ∈ Q, |G p-G q| ≤ L*(‖p.1-q.1‖+|p.2-q.2|))
    {p q : Point n} (hp : p ∈ Q) (hq : q ∈ Q) (ht : q.2 ≤ p.2)
    (hδ1 : parabolicDistance p q ≤ 1)
    (hnear : F05FaceGauge k p.1 ≤ 16*parabolicDistance p q ∨
      p.2 ≤ 256*(parabolicDistance p q)^2) :
    |u p-u q| ≤ (512*K+2*L)*parabolicDistance p q := by
  let δ := parabolicDistance p q
  have hδ : 0 ≤ δ := parabolicDistance_nonneg p q
  have hx : ‖p.1-q.1‖ ≤ δ := parabolicDistance_spatial_le p q
  have hdt : |p.2-q.2| ≤ δ^2 := parabolicDistance_time_gap_le_sq p q
  have hδSq : δ^2 ≤ δ := by nlinarith
  have hdata : |G p-G q| ≤ 2*L*δ :=
    (hLip p hp q hq).trans (by nlinarith [mul_le_mul_of_nonneg_left hx hL,
      mul_le_mul_of_nonneg_left (hdt.trans hδSq) hL])
  rcases hnear with hbd | hbt
  · have hqbd : F05FaceGauge k q.1 ≤ 17*δ := by
      have h := F05_faceGauge_le_add k q.1 p.1
      rw [norm_sub_rev] at h
      linarith
    have hpair := pair_bound_from_error (F05_min_error_face hK he p hp)
      (F05_min_error_face hK he q hq) hdata
    nlinarith [mul_le_mul_of_nonneg_left hbd hK,mul_le_mul_of_nonneg_left hqbd hK,
      mul_nonneg hK hδ]
  · have hqTime : q.2 ≤ 256*δ^2 := ht.trans hbt
    have hpair := pair_bound_from_error (F05_min_error_time hK he p hp)
      (F05_min_error_time hK he q hq) hdata
    nlinarith [mul_le_mul_of_nonneg_left hbt hK,mul_le_mul_of_nonneg_left hqTime hK,
      mul_le_mul_of_nonneg_left hδSq hK]

theorem F05_outer_center_amplitude {Q : Set (Point n)} {k : Option (RIdx n)}
    {B K L ρ : ℝ} {u G : Point n → ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hsup : ∀ z ∈ Q, |u z| ≤ B)
    (he : ∀ z ∈ Q, |u z-G z| ≤ K*min z.2 (F05FaceGauge k z.1))
    (hLip : ∀ p ∈ Q, ∀ q ∈ Q, |G p-G q| ≤ L*(‖p.1-q.1‖+|p.2-q.2|))
    {p : Point n} (hp : p ∈ Q) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hQR : dgOscCylinder p R ⊆ Q)
    (hcase : F05FaceGauge k p.1 ≤ 2*R ∨ p.2 ≤ 4*R^2 ∨ ρ ≤ 2*R) :
    ∀ z ∈ dgOscCylinder p R, |u z-u p| ≤ outerAmplitude B K L ρ*R := by
  intro z hz
  have hzQ := hQR hz
  have hbounds := oscCylinder_spatial_time_bounds hz
  have hR2 : R^2 ≤ R := by nlinarith
  have hdata : |G z-G p| ≤ 2*L*R := by
    have hSpace := mul_le_mul_of_nonneg_left hbounds.1.le hL
    have hTime := mul_le_mul_of_nonneg_left (hbounds.2.trans hR2) hL
    linarith [hLip z hzQ p hp]
  have hlarge : 8*K+2*L ≤ outerAmplitude B K L ρ := by
    dsimp [outerAmplitude]
    have hh : 0 ≤ 4*B/ρ := div_nonneg (mul_nonneg (by norm_num) hB) hρ.le
    linarith
  have hcap : 4*B/ρ ≤ outerAmplitude B K L ρ := by dsimp [outerAmplitude]; linarith
  rcases hcase with hbd | hbt | hρR
  · have hzbd : F05FaceGauge k z.1 ≤ 3*R := by
      have h := F05_faceGauge_le_add k z.1 p.1
      linarith [hbounds.1]
    have hpair := pair_bound_from_error (F05_min_error_face hK he z hzQ)
      (F05_min_error_face hK he p hp) hdata
    have hmul := mul_le_mul_of_nonneg_right hlarge hR.le
    nlinarith [mul_le_mul_of_nonneg_left hzbd hK,mul_le_mul_of_nonneg_left hbd hK,
      mul_nonneg hK hR.le]
  · have hzt : z.2 ≤ 4*R^2 := hz.2.2.trans hbt
    have hpair := pair_bound_from_error (F05_min_error_time hK he z hzQ)
      (F05_min_error_time hK he p hp) hdata
    have hmul := mul_le_mul_of_nonneg_right hlarge hR.le
    nlinarith [mul_le_mul_of_nonneg_left hzt hK,mul_le_mul_of_nonneg_left hbt hK,
      mul_le_mul_of_nonneg_left hR2 hK]
  · have hpair : |u z-u p| ≤ 2*B := (abs_sub _ _).trans (by linarith [hsup z hzQ,hsup p hp])
    have hRatio : 2*B ≤ (4*B/ρ)*R := by
      have hEq : (4*B/ρ)*ρ = 4*B := by field_simp
      have hmul := mul_le_mul_of_nonneg_left hρR (div_nonneg (by positivity) hρ.le)
      nlinarith
    exact hpair.trans (hRatio.trans (mul_le_mul_of_nonneg_right hcap hR.le))

end Yau.Proofs.F05Aux
