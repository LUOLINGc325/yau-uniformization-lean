import Yau.Proofs.C02JetProducts
import Yau.Proofs.C02RadialConstants

/-! Explicit simultaneous scalar recursions. Each row is computed before
any particular metric or actual compact jet supremum is considered. -/

noncomputable section
namespace Yau.Blueprint.C02Proof

structure GaugeJetRow where
  tensor : ℕ → ℝ
  differential : ℝ
  curvature : ℝ
  connection : ℝ

def zeroGaugeJetRow : GaugeJetRow := ⟨fun _ => 0, 0, 0, 0⟩

def initialGaugeJetRow (K : ℕ → ℝ) (ρ : ℝ) : GaugeJetRow :=
  ⟨K, 3 / 2, K 0 * (3 / 2) ^ 2, ρ / 2 * (K 0 * (3 / 2) ^ 2)⟩

def nextGaugeJetRow (K : ℕ → ℝ) (ρ : ℝ) (m : ℕ) (previous : ℕ → GaugeJetRow) : GaugeJetRow :=
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
  ⟨q, bm, fm, c * fm + d * (previous m).curvature⟩

def radialJetMajorant (K : ℕ → ℝ) (ρ : ℝ) (m : ℕ) : GaugeJetRow :=
  Nat.strongRecOn m fun m previous =>
    if _hm : m = 0 then initialGaugeJetRow K ρ else
      nextGaugeJetRow K ρ (m - 1) (fun i => if hi : i < m then previous i hi else zeroGaugeJetRow)

def GaugeJetRow.Nonnegative (R : GaugeJetRow) : Prop :=
  (∀ j, 0 ≤ R.tensor j) ∧ 0 ≤ R.differential ∧ 0 ≤ R.curvature ∧ 0 ≤ R.connection

theorem zeroGaugeJetRow_nonnegative : zeroGaugeJetRow.Nonnegative := by
  exact ⟨fun _ => le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem initialGaugeJetRow_nonnegative {K : ℕ → ℝ} (hK : ∀ j, 0 ≤ K j) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (initialGaugeJetRow K ρ).Nonnegative := by
  refine ⟨hK, by norm_num [initialGaugeJetRow], ?_, ?_⟩
  · exact mul_nonneg (hK 0) (sq_nonneg _)
  · exact mul_nonneg (div_nonneg hρ (by norm_num)) (mul_nonneg (hK 0) (sq_nonneg _))

end Yau.Blueprint.C02Proof
