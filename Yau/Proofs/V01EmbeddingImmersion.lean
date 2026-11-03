import Yau.Proofs.V01EmbeddingDerivative
import Yau.Proofs.V01BaseDifferential

/-! V01 scratch source: the actual block differential is injective because
the base derivative is injective and the original global fields span. -/

noncomputable section
open Set Filter
open scoped Manifold Topology ContDiff

namespace Yau.Blueprint.V01Proof

variable {n N m : ℕ} {M : ComplexManifold n}

theorem embeddingChartDerivative_injective
    (F : M.Carrier → ComplexVector N) (hF : IsHolomorphicVecMap F)
    (hImm : IsImmersionMap F) (V : Fin m → VectorField M)
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun j => V j y)) = ⊤)
    (x : M.Carrier) (p : CotangentCoord n) (hp : p ∈ cotangentTarget x) :
    Function.Injective (embeddingChartDerivative F V x p) := by
  let y := chartInv x p.1
  have hy : y ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hp.1
  have hpoint : chartPt x y = p.1 := (extChartAt (ComplexModel n) x).right_inv hp.1
  have hbase := base_chart_derivative_injective F hF hImm x y hy
  rw [hpoint] at hbase
  intro u v huv
  have hu₁ : u.1 = v.1 := by
    apply hbase
    ext i
    have hi := congrArg (fun w : ComplexVector (N + m) => w (Fin.castAdd m i)) huv
    simpa only [embeddingChartDerivative_base] using hi
  have hfiber (j : Fin m) :
      (∑ b, (fieldCoords (V j) x p.1) b * u.2 b) =
        ∑ b, (fieldCoords (V j) x p.1) b * v.2 b := by
    have hj := congrArg (fun w : ComplexVector (N + m) => w (Fin.natAdd N j)) huv
    simp only [embeddingChartDerivative_fiber, Finset.sum_add_distrib] at hj
    rw [hu₁] at hj
    exact add_left_cancel hj
  have hcov : covectorOfCoords x y u.2 = covectorOfCoords x y v.2 := by
    apply covector_eq_of_spanning y (fun j => V j y) (hspan y)
    intro j
    rw [covectorOfCoords_apply_tangent x y hy,
      covectorOfCoords_apply_tangent x y hy]
    exact hfiber j
  have hu₂ := congrArg (covectorCoords x y) hcov
  rw [Yau.Blueprint.V03Proof.covectorCoords_ofCoords x y hy,
    Yau.Blueprint.V03Proof.covectorCoords_ofCoords x y hy] at hu₂
  exact Prod.ext hu₁ hu₂

theorem cotangentEmbedding_hasFDerivAt_in_chart
    (F : M.Carrier → ComplexVector N) (hF : IsHolomorphicVecMap F)
    (V : Fin m → VectorField M) (hV : ∀ j, IsHolomorphicField (V j))
    (x : M.Carrier) (p : CotangentCoord n) (hp : p ∈ cotangentTarget x) :
    HasFDerivAt (fun z => cotangentEmbedding F V (cotangentChartInv x z))
      (embeddingChartDerivative F V x p) p := by
  apply (cotangentEmbeddingChart_hasFDerivAt F hF V hV x p hp).congr_of_eventuallyEq
  have hopen : IsOpen (cotangentTarget x) := (isOpen_extChartAt_target x).prod isOpen_univ
  filter_upwards [hopen.mem_nhds hp] with z hz
  exact cotangentEmbedding_in_chart F V x hz

theorem cotangentEmbedding_immersion
    (F : M.Carrier → ComplexVector N) (hF : IsHolomorphicVecMap F)
    (hinj : Function.Injective F) (hImm : IsImmersionMap F)
    (V : Fin m → VectorField M) (hV : ∀ j, IsHolomorphicField (V j))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun j => V j y)) = ⊤) :
    CotangentImmersion (cotangentEmbedding F V) := by
  refine ⟨cotangentEmbedding_holomorphic F hF V hV,
    cotangentEmbedding_injective F hinj V hspan, ?_⟩
  intro y
  have hp : cotangentChart y.1 y ∈ cotangentTarget y.1 :=
    Yau.Blueprint.V03Proof.cotangentChart_mapsTo y.1 (mem_extChartAt_source y.1)
  rw [(cotangentEmbedding_hasFDerivAt_in_chart F hF V hV y.1 _ hp).fderiv]
  exact embeddingChartDerivative_injective F hF hImm V hspan y.1 _ hp

theorem exists_cotangentImmersion_of_finiteInterpolation
    {X : KahlerManifold n} (hP03 : FiniteInterpolation X) :
    ∃ (q : ℕ) (G : CotangentPoint X.manifold → ComplexVector q), CotangentImmersion G := by
  obtain ⟨N, F, hF, hinj, hImm⟩ := hP03.2.2.1
  obtain ⟨m, V, hV, hspan⟩ := hP03.2.2.2
  exact ⟨N + m, cotangentEmbedding F V,
    cotangentEmbedding_immersion F hF hinj hImm V hV hspan⟩

end Yau.Blueprint.V01Proof
