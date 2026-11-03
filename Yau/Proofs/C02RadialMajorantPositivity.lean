import Yau.Proofs.C02RadialMajorants
import Yau.Proofs.C02JetProductBounds

noncomputable section
namespace Yau.Blueprint.C02Proof

theorem nextGaugeJetRow_nonnegative {K : ℕ → ℝ} (hK : ∀ j, 0 ≤ K j) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (m : ℕ) (previous : ℕ → GaugeJetRow) (hp : ∀ i, (previous i).Nonnegative) :
    (nextGaugeJetRow K ρ m previous).Nonnegative := by
  let b := fun i => (previous i).differential
  let a := fun i => (previous i).connection
  let q := fun j => binomialJetProduct (fun i => (previous i).tensor (j + 1)) b m +
    (4 + j) * binomialJetProduct (fun i => (previous i).tensor j) a m
  let L := q 0 * (3 / 2) ^ 2 + middleJetProduct (fun i => (previous i).tensor 0) b m * (3 / 2) +
    middleJetProduct (binomialJetProduct (fun i => (previous i).tensor 0) b) b m
  let c := ρ / ((m : ℝ) + 3)
  let d := ((m : ℝ) + 1) / ((m : ℝ) + 2)
  let bm := 2 * (c ^ 2 * L + c * d * (previous m).curvature + d * (previous m).connection)
  let fm := 3 * K 0 * bm + L
  have hq (j : ℕ) : 0 ≤ q j :=
    add_nonneg (binomialJetProduct_nonneg (fun i => (hp i).1 _) (fun i => (hp i).2.1) m)
      (mul_nonneg (by positivity) (binomialJetProduct_nonneg (fun i => (hp i).1 _)
        (fun i => (hp i).2.2.2) m))
  have hL : 0 ≤ L := add_nonneg
    (add_nonneg (mul_nonneg (hq 0) (sq_nonneg _))
      (mul_nonneg (middleJetProduct_nonneg (fun i => (hp i).1 0) (fun i => (hp i).2.1) m) (by norm_num)))
    (middleJetProduct_nonneg (fun k => binomialJetProduct_nonneg (fun i => (hp i).1 0)
      (fun i => (hp i).2.1) k) (fun i => (hp i).2.1) m)
  have hc : 0 ≤ c := div_nonneg hρ (by positivity)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hbm : 0 ≤ bm := mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) hL)
      (mul_nonneg (mul_nonneg hc hd) (hp m).2.2.1)) (mul_nonneg hd (hp m).2.2.2))
  have hfm : 0 ≤ fm := add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hK 0)) hbm) hL
  change (∀ j, 0 ≤ q j) ∧ 0 ≤ bm ∧ 0 ≤ fm ∧ 0 ≤ c * fm + d * (previous m).curvature
  exact ⟨hq, hbm, hfm, add_nonneg (mul_nonneg hc hfm) (mul_nonneg hd (hp m).2.2.1)⟩

end Yau.Blueprint.C02Proof
