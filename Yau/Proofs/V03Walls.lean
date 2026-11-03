import Yau.Proofs.V03Elementary

/-! Bounds for the actual positive cutoff walls on admissible boundaries. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem setup_wallProfiles {d : VariationData X q} (hd : VariationSetup d) :
    WallProfiles d := hd.2.2.2.2.2.2.1

theorem setup_index_bounds {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) :
    0 < d.A j ∧ 0 < d.B j := by
  have hj := hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j
  refine ⟨hj.1, lt_of_lt_of_le ?_ hj.2.1⟩
  positivity

theorem wallProduct_pos_le_one {d : VariationData X q} (hp : WallProfiles d)
    {j : ℕ} (hA : 0 < d.A j) (hB : 0 < d.B j)
    {y : CotangentPoint X.manifold} (hy : y ∈ boundaryRegion d j) :
    0 < wallProduct d j y ∧ wallProduct d j y ≤ 1 := by
  have hb := deltaBase_pos hp hA hy.1
  have hf := deltaFiber_pos hp hB hy.2
  exact ⟨mul_pos hb hf,
    mul_le_one₀ (deltaBase_le_one hp j y.1) hf.le (deltaFiber_le_one hp j y)⟩

theorem admissible_wallProduct_bounds {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    0 < wallProduct d j (F.f (circlePoint θ)) ∧
      wallProduct d j (F.f (circlePoint θ)) ≤ 1 := by
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  exact wallProduct_pos_le_one (setup_wallProfiles hd) hA hB
    (hF.2.2.2.2.2.2.2.1 θ)

theorem admissible_wallPower_bounds {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (a : ℕ) (θ : ℝ) :
    0 < wallPower d j a (F.f (circlePoint θ)) ∧
      wallPower d j a (F.f (circlePoint θ)) ≤ 1 := by
  obtain ⟨hp, hp1⟩ := admissible_wallProduct_bounds hd hF θ
  exact ⟨pow_pos hp a, pow_le_one₀ hp.le hp1⟩

theorem baseCost_nonneg {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {t : ℝ} (ht : t ∈ Set.Icc 0 d.extendedT) :
    0 ≤ baseCost d j x t := by
  obtain ⟨_, c, hc, hQ⟩ := hd.2.2.2.2.2.2.2.2.1
  have hQ0 : 0 ≤ d.Q x t := le_trans (by positivity) (hQ x t ht).1
  have hρ := (hd.2.2.2.2.2.2.2.2.2.1 j).2
  obtain ⟨C, hρ⟩ := hρ
  exact add_nonneg (mul_nonneg (by positivity) hQ0) (hρ x t ht).1

theorem wallCost_nonneg {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {y : CotangentPoint X.manifold} (hy : y ∈ boundaryRegion d j)
    {t s : ℝ} (ht : t ∈ Set.Icc 0 d.extendedT) (hs : 0 ≤ s) :
    0 ≤ wallCost d j y t s := by
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  have hp := setup_wallProfiles hd
  exact add_nonneg (baseCost_nonneg hd j y.1 ht)
    (mul_nonneg (by positivity)
      (add_nonneg (wallBase_nonneg hp (deltaBase_pos hp hA hy.1))
        (wallFiber_nonneg hp (deltaFiber_pos hp hB hy.2))))

theorem admissible_wallCost_nonneg {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    0 ≤ wallCost d j (F.f (circlePoint θ)) (discTime F (circlePoint θ)) F.s := by
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  exact wallCost_nonneg hd (hF.2.2.2.2.2.2.2.1 θ)
    ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩ hF.2.2.2.1.le

theorem admissible_wallAverage_nonneg {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    0 ≤ circleAverage (fun θ => wallCost d j (F.f (circlePoint θ))
      (discTime F (circlePoint θ)) F.s) :=
  circleAverage_nonneg (admissible_wallCost_nonneg hd hF)

end Yau.Blueprint.V03Proof
