import Yau.Proofs.F05MatrixCalculus

/-! Positive compact scalar fields have actual positive lower bounds, and
their literal scalar multiples preserve computed ellipticity constants. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic

theorem F05_compact_positive_bounds {Z : Type*} [TopologicalSpace Z] {K : Set Z}
    (hK : IsCompact K) (hNE : K.Nonempty) {f : Z → ℝ} (hf : ContinuousOn f K)
    (hPos : ∀ z ∈ K, 0 < f z) :
    ∃ l b : ℝ, 0 < l ∧ l ≤ b ∧ ∀ z ∈ K, l ≤ f z ∧ f z ≤ b := by
  obtain ⟨x,hx,hMin⟩ := hK.exists_isMinOn hNE hf
  obtain ⟨y,hy,hMax⟩ := hK.exists_isMaxOn hNE hf
  exact ⟨f x,f y,hPos x hx,hMax hx,fun z hz => ⟨hMin hz,hMax hz⟩⟩

theorem F05_elliptic_scalar_mul {n : ℕ} {Q : Set (Point n)} {a : Point n → Mat n}
    {c : Point n → ℝ} {lam upper l b : ℝ} (ha : Elliptic Q a lam upper)
    (hl : 0 < l) (hlb : l ≤ b) (hc : ∀ p ∈ Q, l ≤ c p ∧ c p ≤ b) :
    Elliptic Q (fun p => c p • a p) (l*lam) (b*upper) := by
  refine ⟨mul_pos hl ha.1,mul_le_mul hlb ha.2.1 ha.1.le (hl.le.trans hlb),?_⟩
  intro p hp
  obtain ⟨hSym,hQuad⟩ := ha.2.2 p hp
  have hcp : 0 ≤ c p := hl.le.trans (hc p hp).1
  have hUpper : 0 ≤ upper := ha.1.le.trans ha.2.1
  refine ⟨?_,?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    simp only [Matrix.smul_apply,smul_eq_mul,hSym.apply i j]
  · intro v
    have hSum : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hScale : (∑ i,∑ j,(c p • a p) i j * v i * v j) = c p * (∑ i,∑ j,a p i j * v i * v j) := by
      simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
    rw [hScale]
    constructor
    · calc
        (l*lam)*(∑ i,(v i)^2) = l*(lam*(∑ i,(v i)^2)) := by ring
        _ ≤ c p*(lam*(∑ i,(v i)^2)) :=
          mul_le_mul_of_nonneg_right (hc p hp).1 (mul_nonneg ha.1.le hSum)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hQuad v).1 hcp
    · calc
        _ ≤ c p*(upper*(∑ i,(v i)^2)) := mul_le_mul_of_nonneg_left (hQuad v).2 hcp
        _ ≤ b*(upper*(∑ i,(v i)^2)) :=
          mul_le_mul_of_nonneg_right (hc p hp).2 (mul_nonneg hUpper hSum)
        _ = (b*upper)*(∑ i,(v i)^2) := by ring

end Yau.Proofs.F05Aux
