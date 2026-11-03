import Yau.Proofs.F05TimeAffineC2

/-! Quantitative affine time transport uses only the original Hölder
budget. It applies to all jet codomains, with the actual time slope. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem F05_holderWeight_timeAffine (α a b : ℝ) (p q : Point n) :
    holderWeight α (F05TimeAffinePoint a b p) (F05TimeAffinePoint a b q) ≤
      (1+|a|^(α/2))*holderWeight α p q := by
  have ht : |(a*p.2+b)-(a*q.2+b)|^(α/2) = |a|^(α/2)*|p.2-q.2|^(α/2) := by
    rw [show (a*p.2+b)-(a*q.2+b) = a*(p.2-q.2) by ring,abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  change ‖p.1-q.1‖^α+|(a*p.2+b)-(a*q.2+b)|^(α/2) ≤ _
  rw [ht]
  dsimp only [holderWeight]
  have hx := Real.rpow_nonneg (norm_nonneg (p.1-q.1)) α
  have hy := Real.rpow_nonneg (abs_nonneg (p.2-q.2)) (α/2)
  have ha := Real.rpow_nonneg (abs_nonneg a) (α/2)
  nlinarith

theorem F05_holder_timeAffine {X : Set (Space n)} {l r L R α C a b : ℝ}
    (hMap : MapsTo (fun t : ℝ => a*t+b) (Icc l r) (Icc L R))
    {u : Point n → E} (hu : HolderBound α (cylinder X L R) u C) :
    HolderBound α (cylinder X l r) (F05TimeAffine a b u) (C*(1+|a|^(α/2))) := by
  have ha : 0 ≤ |a|^(α/2) := Real.rpow_nonneg (abs_nonneg a) _
  have hC : C ≤ C*(1+|a|^(α/2)) := by nlinarith [hu.1]
  have hMapQ : MapsTo (F05TimeAffinePoint a b) (cylinder X l r) (cylinder X L R) :=
    fun _ hp => ⟨hp.1,hMap hp.2⟩
  refine ⟨mul_nonneg hu.1 (by positivity),fun p hp => (hu.2.1 _ (hMapQ hp)).trans hC,?_⟩
  intro p hp q hq
  exact (hu.2.2 _ (hMapQ hp) _ (hMapQ hq)).trans
    ((mul_le_mul_of_nonneg_left (F05_holderWeight_timeAffine α a b p q) hu.1).trans_eq
      (by ring))

end Yau.Proofs.F05Aux
