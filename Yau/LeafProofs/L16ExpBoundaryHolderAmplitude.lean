import Yau.LeafProofs.L16ExpBoundaryHolderGeometry

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryHolderAux

open Yau.Parabolic L16Aux

theorem pair_bound_from_error {n : ℕ} {u G : Point n → ℝ} {p q : Point n}
    {ep eq d : ℝ} (hp : |u p-G p| ≤ ep) (hq : |u q-G q| ≤ eq)
    (hG : |G p-G q| ≤ d) : |u p-u q| ≤ ep+eq+d := by
  have hq' : |G q-u q| ≤ eq := by simpa only [abs_sub_comm] using hq
  calc
    _ = |(u p-G p)+(G p-G q)+(G q-u q)| := by congr 1; ring
    _ ≤ (|u p-G p|+|G p-G q|)+|G q-u q| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (ep+d)+eq := add_le_add (add_le_add hp hG) hq'
    _ = _ := by ring

theorem error_min_time {n : ℕ} {O : Set (Space n)} {T K : ℝ}
    {u G : Point n → ℝ} (hK : 0 ≤ K)
    (he : ∀ z ∈ cylinder (closure O) 0 T,
      |u z-G z| ≤ K*min z.2 (boundaryDistance O z.1)) :
    ∀ z ∈ cylinder (closure O) 0 T, |u z-G z| ≤ K*z.2 :=
  fun z hz => (he z hz).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK)

theorem error_min_boundary {n : ℕ} {O : Set (Space n)} {T K : ℝ}
    {u G : Point n → ℝ} (hK : 0 ≤ K)
    (he : ∀ z ∈ cylinder (closure O) 0 T,
      |u z-G z| ≤ K*min z.2 (boundaryDistance O z.1)) :
    ∀ z ∈ cylinder (closure O) 0 T, |u z-G z| ≤ K*boundaryDistance O z.1 :=
  fun z hz => (he z hz).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK)

/-- The true initial and lateral error bounds handle every pair close to
either parabolic boundary face, with a linear modulus. -/
theorem near_pair_linear_bound {n : ℕ} {O : Set (Space n)} {T K L : ℝ}
    {u G : Point n → ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (he : ∀ z ∈ cylinder (closure O) 0 T,
      |u z-G z| ≤ K*min z.2 (boundaryDistance O z.1))
    (hLip : ∀ p ∈ cylinder (closure O) 0 T, ∀ q ∈ cylinder (closure O) 0 T,
      |G p-G q| ≤ L*(‖p.1-q.1‖+|p.2-q.2|))
    {p q : Point n} (hp : p ∈ cylinder (closure O) 0 T) (hq : q ∈ cylinder (closure O) 0 T)
    (ht : q.2 ≤ p.2) (hδ1 : parabolicDistance p q ≤ 1)
    (hnear : boundaryDistance O p.1 ≤ 16*parabolicDistance p q ∨
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
  · have hqbd : boundaryDistance O q.1 ≤ 17*δ := by
      have h := boundaryDistance_le_add O q.1 p.1
      rw [norm_sub_rev] at h
      linarith
    have hpair := pair_bound_from_error (error_min_boundary hK he p hp)
      (error_min_boundary hK he q hq) hdata
    nlinarith [mul_le_mul_of_nonneg_left hbd hK,mul_le_mul_of_nonneg_left hqbd hK,
      mul_nonneg hK hδ]
  · have hqTime : q.2 ≤ 256*δ^2 := ht.trans hbt
    have hpair := pair_bound_from_error (error_min_time hK he p hp)
      (error_min_time hK he q hq) hdata
    nlinarith [mul_le_mul_of_nonneg_left hbt hK,mul_le_mul_of_nonneg_left hqTime hK,
      mul_le_mul_of_nonneg_left hδSq hK]

def outerAmplitude (B K L ρ : ℝ) : ℝ := 1+4*B/ρ+8*K+2*L

theorem outerAmplitude_pos {B K L ρ : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hρ : 0 < ρ) : 0 < outerAmplitude B K L ρ := by
  dsimp [outerAmplitude]
  positivity

/-- Boundary error and fixed-data Lipschitz bounds yield an O(R) outer
amplitude. This is the cancellation needed to keep the DG exponent. -/
theorem outer_center_amplitude {n : ℕ} {O : Set (Space n)} {T B K L ρ : ℝ}
    {u G : Point n → ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hsup : ∀ z ∈ cylinder (closure O) 0 T, |u z| ≤ B)
    (he : ∀ z ∈ cylinder (closure O) 0 T,
      |u z-G z| ≤ K*min z.2 (boundaryDistance O z.1))
    (hLip : ∀ p ∈ cylinder (closure O) 0 T, ∀ q ∈ cylinder (closure O) 0 T,
      |G p-G q| ≤ L*(‖p.1-q.1‖+|p.2-q.2|))
    {p : Point n} (hp : p ∈ cylinder (closure O) 0 T) {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hQR : dgOscCylinder p R ⊆ cylinder (closure O) 0 T)
    (hcase : boundaryDistance O p.1 ≤ 2*R ∨ p.2 ≤ 4*R^2 ∨ ρ ≤ 2*R) :
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
  · have hzbd : boundaryDistance O z.1 ≤ 3*R := by
      have h := boundaryDistance_le_add O z.1 p.1
      linarith [hbounds.1]
    have hpair := pair_bound_from_error (error_min_boundary hK he z hzQ)
      (error_min_boundary hK he p hp) hdata
    have hmul := mul_le_mul_of_nonneg_right hlarge hR.le
    nlinarith [mul_le_mul_of_nonneg_left hzbd hK,mul_le_mul_of_nonneg_left hbd hK,
      mul_nonneg hK hR.le]
  · have hzt : z.2 ≤ 4*R^2 := hz.2.2.trans hbt
    have hpair := pair_bound_from_error (error_min_time hK he z hzQ)
      (error_min_time hK he p hp) hdata
    have hmul := mul_le_mul_of_nonneg_right hlarge hR.le
    nlinarith [mul_le_mul_of_nonneg_left hzt hK,mul_le_mul_of_nonneg_left hbt hK,
      mul_le_mul_of_nonneg_left hR2 hK]
  · have hpair : |u z-u p| ≤ 2*B := (abs_sub _ _).trans (by linarith [hsup z hzQ,hsup p hp])
    have hRatio : 2*B ≤ (4*B/ρ)*R := by
      have hEq : (4*B/ρ)*ρ = 4*B := by field_simp
      have hmul := mul_le_mul_of_nonneg_left hρR (div_nonneg (by positivity) hρ.le)
      nlinarith
    exact hpair.trans (hRatio.trans (mul_le_mul_of_nonneg_right hcap hR.le))

end Yau.LeafProofs.L16ExpBoundaryHolderAux
