import Yau.Proofs.E02FixedContactMajorant
import Yau.Proofs.E02ContactVertical
import Yau.Proofs.E02OrbitCoercivity

open Matrix Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- After a single tail shift, actual vertical coercivity makes every
fixed-κ majorant available. The chosen aggregate at each κ works for ALL
positive coefficient losses, before passing κ to zero. -/
theorem exists_eventual_contact_majorants {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (hV : EnvelopeInequality X h) (T : ℝ) (x : Pt X)
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1))))
    (hDom : ∀ q ∈ K, (envelopeRealCoordinates n).symm q ∈ envelopeDomain X T x)
    (κ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j)
    (f : ComplexVector n × ℝ → ℝ) (a₀ : ComplexVector n × ℝ)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) (η₀ : Fin m → ComplexVector n)
    (B : Herm n) (hB : B.PosDef)
    (hGram₀ : weightedColumns α η₀*(weightedColumns α η₀)ᴴ = B⁻¹)
    (hq₀ : ∀ i, qform B (η₀ i) = 1) (θ w : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hw : w < 1) (hWeight : ∀ i, α i ≤ w)
    (Q : ℕ → ProductPoint n m) (Q₀ : ProductPoint n m)
    (hQLim : Tendsto Q atTop (𝓝 Q₀))
    (hOrbit : Q₀ ∈ contactOrbit a₀ α B (rowProjector (weightedColumns α η₀)))
    (hf : ∀ j, ContDiffAt ℝ 2 f ((Q j).1,(Q j).2.1))
    (hM : ∀ j, (weightedColumns α (Q j).2.2*(weightedColumns α (Q j).2.2)ᴴ).PosDef)
    (p : ℕ → Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : ℕ → Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hJet : ∀ j i, RealSecondJet (compactInfConvolution K (packedEnvelopeReal X h T x) (κ j))
      (factorProjection n m i (productRealCoordinates n m (Q j))) (p j i) (A j i))
    (a : ℕ → Fin m → ComplexVector n × ComplexVector n × ℝ)
    (ha : ∀ j i, envelopeRealCoordinates n (a j i) ∈ interior K)
    (hMinSource : ∀ j i, compactInfConvolution K (packedEnvelopeReal X h T x) (κ j)
      (factorProjection n m i (productRealCoordinates n m (Q j))) =
        packedEnvelopeReal X h T x (envelopeRealCoordinates n (a j i))+
        ‖factorProjection n m i (productRealCoordinates n m (Q j))-envelopeRealCoordinates n (a j i)‖^2/(2*κ j))
    (slope : ℕ → EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))
    (hMin : ∀ j, IsLocalMin (fun R => (∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x)
      (κ j) (factorProjection n m i R))-productCostPacked f α (rowProjector (weightedColumns α η₀)) θ R-
        ⟪slope j,R⟫_ℝ) (productRealCoordinates n m (Q j))) :
    ∃ (N : ℕ) (L : ℕ → Herm n),
      (∀ j, (L j).PosSemidef ∧
        (L j-leviC (fun z => f (z,(Q (j+N)).2.1)) (Q (j+N)).1).PosSemidef) ∧
      ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop,
        ((1-θ)*(1-w)-r)*tracePair B (L j) ≤
          deriv (fun t => f ((Q (j+N)).1,t)) (Q (j+N)).2.1+
            ⟪slope (j+N),productRealCoordinates n m (0,1,0)⟫_ℝ := by
  let M₀ := weightedColumns α η₀
  have hM₀ : (M₀*M₀ᴴ).PosDef := by rw [show M₀*M₀ᴴ = B⁻¹ from hGram₀]; exact hB.inv
  have hBlocks (j : ℕ) : ∀ i, ((cotangentTensor (A j i)).toBlocks₂₂-
      columnLowerMatrix α θ (Q j).2.2 i).PosSemidef :=
    sameContact_vertical_blocks n m (fun _ => compactInfConvolution K (packedEnvelopeReal X h T x) (κ j))
      f α M₀ θ (Q j) (p j) (A j) (hJet j) (hf j) (hM j) hM₀ hα hθ₀ (innerSL ℝ (slope j)) (hMin j)
  have hLower := eventually_vertical_blocks_of_orbit_limit a₀ α hα η₀ B hB hGram₀ hq₀
    θ w hθ₁.le hWeight Q Q₀ hQLim hOrbit (fun j i => cotangentTensor (A j i)) hBlocks
  let c := (1-θ)*(1-w)
  have hc : 0 < c := mul_pos (sub_pos.mpr hθ₁) (sub_pos.mpr hw)
  have hPD : ∀ᶠ j in atTop, ∀ i, (cotangentTensor (A j i)).toBlocks₂₂.PosDef := by
    filter_upwards [hLower (c/2) (by positivity)] with j hj
    intro i
    have hd : 0 < (1-θ)*(1-w)-c/2 := by change 0 < c-c/2; linarith
    have hPos : (((((1-θ)*(1-w)-c/2 : ℝ)) : ℂ) • B).PosDef :=
      hB.smul (RCLike.ofReal_pos.mpr hd)
    have hh := Matrix.PosDef.posSemidef_add (hj i) hPos
    convert hh using 1 <;> module
  obtain ⟨N,hN⟩ := eventually_atTop.mp hPD
  have hEach (j : ℕ) := fixed_contact_psd_majorant X h hV T x K hDom (hκ (j+N)) f α hα M₀ θ
    hM₀ hθ₀ hθ₁.le (Q (j+N)) (hf (j+N)) (hM (j+N)) (p (j+N)) (A (j+N)) (hJet (j+N))
    (a (j+N)) (ha (j+N)) (hMinSource (j+N)) (hN (j+N) (Nat.le_add_left N j))
    (innerSL ℝ (slope (j+N))) (hMin (j+N)) B
  choose L hL hDomL hTrace using hEach
  refine ⟨N,L,fun j => ⟨hL j,hDomL j⟩,?_⟩
  intro r hr
  have hTail := (tendsto_add_atTop_nat N).eventually (hLower r hr)
  filter_upwards [hTail] with j hj
  exact hTrace j (((1-θ)*(1-w))-r) hj

end Yau.NodeProofs.E02Aux
