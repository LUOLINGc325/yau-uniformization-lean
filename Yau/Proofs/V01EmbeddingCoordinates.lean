import Yau.Proofs.V01CotangentEmbedding

/-! The actual formula for the cotangent embedding in coordinates. Its
identification with the original geometric map retains the chart target. -/

noncomputable section
namespace Yau.Blueprint.V01Proof
variable {n N m : ℕ} {M : ComplexManifold n}

def cotangentEmbeddingChart
    (F : M.Carrier → ComplexVector N) (V : Fin m → VectorField M)
    (x : M.Carrier) (p : CotangentCoord n) : ComplexVector (N + m) :=
  WithLp.toLp 2 (Fin.addCases (fun i => F (chartInv x p.1) i)
    (fun j => ∑ b, (fieldCoords (V j) x p.1) b * p.2 b))


end Yau.Blueprint.V01Proof
