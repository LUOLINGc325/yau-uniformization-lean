import Yau.Proofs.V02SpanningMatrix

/-! The ambient columns of genuine spanning vector fields are holomorphic
in every valid induced cotangent chart. Their minor sum is therefore smooth. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q b : ℕ} {M : ComplexManifold n}

theorem spanningAmbient_in_fixed_chart {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (x : M.Carrier) (y : CotangentPoint M) (hy : y ∈ cotangentSource x) :
    spanningAmbientMatrix G Z y = cotangentDG G x y *
      (cotangentTransition y.1 x y * fieldMatrix Z y) := by
  unfold spanningAmbientMatrix
  rw [V03Proof.cotangentDG_transition hG y.1 x y (mem_extChartAt_source _) hy,
    Matrix.mul_assoc]

theorem spanningAmbient_entry_chart_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (x : M.Carrier) (a : Fin q) (k : Fin b) :
    ContDiffOn ℂ ∞ (fun z => spanningAmbientMatrix G Z (cotangentChartInv x z) a k)
      (cotangentTarget x) := by
  have hcoord : ContDiffOn ℂ ∞
      (fun z => cotangentChart x (cotangentChartInv x z)) (cotangentTarget x) :=
    contDiffOn_id.congr (fun z hz => V03Proof.cotangentChart_right_inv x hz)
  intro z hz
  have hsource := V03Proof.cotangentChartInv_mapsTo x hz
  have hDG (i : CotangentIndex n) : ContDiffWithinAt ℂ ∞
      (fun z => cotangentDG G x (cotangentChartInv x z) a i) (cotangentTarget x) z :=
    V03Proof.cotangentDG_entry_contDiffWithinAt hG x hsource (hcoord z hz) a i
  have hW (i : CotangentIndex n) : ContDiffWithinAt ℂ ∞
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x) z :=
    V03Proof.complex_holomorphic_contDiffOn
      ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ)
        (hZ k x i) z hz
  have hmodel := ContDiffWithinAt.sum (fun i (_ : i ∈ Finset.univ) => (hDG i).mul (hW i))
  apply hmodel.congr_of_eventuallyEq_of_mem ?_ hz
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (congrFun (congrFun (spanningAmbient_in_fixed_chart hG Z x
    (cotangentChartInv x w) (V03Proof.cotangentChartInv_mapsTo x hw)) a) k)

theorem spanning_minor_chart_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (x : M.Carrier) (r : CotangentIndex n → Fin q) (c : CotangentIndex n → Fin b) :
    ContDiffOn ℂ ∞ (fun z =>
      ((spanningAmbientMatrix G Z (cotangentChartInv x z)).submatrix r c).det)
      (cotangentTarget x) := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => spanningAmbient_entry_chart_contDiffOn hG hZ x (r (σ i)) (c i))

theorem spanningMinorSq_chart_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => spanningMinorSq G Z (cotangentChartInv x z))
      (cotangentTarget x) := by
  unfold spanningMinorSq tupleMinorSq
  exact ContDiffOn.sum fun r _ => ContDiffOn.sum fun c _ =>
    ((spanning_minor_chart_contDiffOn hG hZ x r c).restrict_scalars ℝ).norm_sq ℂ

/-- A positive lower bound on the actual intrinsic compact, with the empty
compact allowed. No properness of the immersion is needed. -/
theorem spanningMinorSq_compact_lower_bound
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    ∃ s : ℝ, 0 < s ∧ ∀ y ∈ K, s ≤ spanningMinorSq G Z y := by
  have hc : IsCompact (spanningMinorSq G Z '' K) := by
    obtain ⟨r, x, C, hC, rfl⟩ := hK
    rw [Set.image_iUnion]
    apply isCompact_iUnion
    intro i
    simpa only [Set.image_image, Function.comp_def] using
      (hC i).1.image_of_continuousOn
        ((spanningMinorSq_chart_contDiffOn hG.1 hZ (x i)).continuousOn.mono (hC i).2)
  obtain ⟨s, hs, hb⟩ := hc.exists_forall_le' continuous_id.continuousOn
    (a := 0) (by
      rintro a ⟨y, hy, rfl⟩
      exact spanningMinorSq_pos hG hspan y)
  exact ⟨s, hs, fun y hy => hb _ (Set.mem_image_of_mem _ hy)⟩

end Yau.Blueprint.V02Proof
