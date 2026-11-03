import Yau.Proofs.F05BootstrapSecants

/-! For every test vector one of its two orientations points into the closed
physical half-space. This yields operator-norm secant estimates without using
values on the other side of the physical face. -/

open Set
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05InwardVector (ν : Option (RIdx n)) (e : Space n) : Space n :=
  match ν with
  | none => e
  | some j => if realCoord e j ≤ 0 then e else -e

theorem F05InwardVector_norm (ν : Option (RIdx n)) (e : Space n) :
    ‖F05InwardVector ν e‖ = ‖e‖ := by
  cases ν with
  | none => rfl
  | some j => simp only [F05InwardVector]; split <;> simp only [norm_neg]

theorem F05InwardVector_abs_apply (ν : Option (RIdx n)) (e : Space n)
    (L : Space n →L[ℝ] ℝ) : |L (F05InwardVector ν e)| = |L e| := by
  cases ν with
  | none => rfl
  | some j => simp only [F05InwardVector]; split <;> simp only [map_neg,abs_neg]

theorem F05InwardVector_coordinate (j : RIdx n) (e : Space n) :
    realCoord (F05InwardVector (some j) e) j ≤ 0 := by
  simp only [F05InwardVector]
  split
  · assumption
  · rw [← realCoordLinear_apply,map_neg]
    rw [realCoordLinear_apply]
    linarith

theorem F05_inward_secant_mem_region (ν : Option (RIdx n)) {x e : Space n}
    {s R ℓ : ℝ} (hx : x ∈ region ν s) (he : ‖e‖ ≤ 1)
    (hℓ : 0 ≤ ℓ) (hMargin : s+ℓ ≤ R) :
    x+ℓ • F05InwardVector ν e ∈ region ν R := by
  refine ⟨?_,?_⟩
  · have hTri := norm_add_le x (ℓ • F05InwardVector ν e)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hℓ,F05InwardVector_norm] at hTri
    nlinarith [hx.1]
  · cases ν with
    | none => trivial
    | some j =>
      change realCoord (x+ℓ • F05InwardVector (some j) e) j ≤ 0
      rw [← realCoordLinear_apply,map_add,map_smul]
      simp only [realCoordLinear_apply,smul_eq_mul]
      have hNormal := F05InwardVector_coordinate j e
      have hxNormal : realCoord x j ≤ 0 := hx.2
      nlinarith

theorem F05_relative_cap_gradient_bound (ν : Option (RIdx n))
    {I : Set ℝ} {v : Point n → ℝ} {R s K B ℓ : ℝ}
    (hR : 0 < R) (hv : F05RelC2 (region ν R) I v)
    (hK : ∀ z ∈ region ν R ×ˢ I, ‖F05RelDD (region ν R) v z‖ ≤ K)
    (hB : ∀ z ∈ region ν R ×ˢ I, |v z| ≤ B)
    (hK0 : 0 ≤ K) (hB0 : 0 ≤ B) (hℓ : 0 < ℓ) (hMargin : s+ℓ ≤ R)
    {t : ℝ} (ht : t ∈ I) {x : Space n} (hx : x ∈ region ν s) :
    ‖F05RelD (region ν R) v (x,t)‖ ≤ K*ℓ+2*B/ℓ := by
  have hxR : x ∈ region ν R := F05_region_mono (by linarith) hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  let d := F05InwardVector ν e
  have hd : ‖d‖ ≤ 1 := by rw [F05InwardVector_norm]; exact he.le
  have hEnd : x+ℓ • d ∈ region ν R :=
    F05_inward_secant_mem_region ν hx he.le hℓ.le hMargin
  have hSecant := F05_relative_directional_secant hv (F05_region_uniqueDiffOn ν hR)
    (F05_region_convex ν R) hK hK0 hℓ ht hxR d hd hEnd
  have hValue : |v (x+ℓ • d,t)-v (x,t)| ≤ 2*B := by
    have hEndValue : |v (x+ℓ • d,t)| ≤ B := hB (x+ℓ • d,t) ⟨hEnd,ht⟩
    have hBaseValue : |v (x,t)| ≤ B := hB (x,t) ⟨hxR,ht⟩
    calc
      _ ≤ |v (x+ℓ • d,t)|+|v (x,t)| := abs_sub _ _
      _ ≤ B+B := add_le_add hEndValue hBaseValue
      _ = 2*B := by ring
  change |F05RelD (region ν R) v (x,t) e| ≤ _
  rw [← F05InwardVector_abs_apply ν e]
  change |F05RelD (region ν R) v (x,t) d| ≤ _
  calc
    _ = |(F05RelD (region ν R) v (x,t) d-(v (x+ℓ • d,t)-v (x,t))/ℓ)+
        (v (x+ℓ • d,t)-v (x,t))/ℓ| := by congr 1; ring
    _ ≤ |F05RelD (region ν R) v (x,t) d-(v (x+ℓ • d,t)-v (x,t))/ℓ|+
        |(v (x+ℓ • d,t)-v (x,t))/ℓ| := abs_add_le _ _
    _ ≤ K*ℓ+2*B/ℓ := by
      apply add_le_add hSecant
      rw [abs_div,abs_of_pos hℓ]
      exact div_le_div_of_nonneg_right hValue hℓ.le

end Yau.Proofs.F05Aux
