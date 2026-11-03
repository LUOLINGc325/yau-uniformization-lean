import spec.attacks.EndpointAssembly
import Yau.Proofs.F01AActualGlobalCore
import Yau.Proofs.F04RootApplication
import Yau.Proofs.EnvelopeRootApplication
import Yau.Proofs.C04RootApplication
import Yau.Proofs.C07RootApplication
import Yau.Proofs.Y01RootApplication
import Yau.Proofs.U02
import Yau.Proofs.U03
import Yau.Proofs.U04
import Yau.Proofs.I01

noncomputable section
namespace Yau.NodeProofs

/-- Assemble Theorem 1.1 from the ten proved original producers on X. -/
theorem main_endpoint {n : ℕ} (hn : 1 ≤ n) (X : Yau.KahlerManifold n) :
    Yau.BiholomorphicToComplexEuclidean X.manifold :=
  Yau.Blueprint.EndpointAssemblyAttacks.endpoint_from_exact_producers
    F01_actual_proved F04_proved E03_actual_proved C04_proved C07_proved
    Y04_proved U02_proved U03_proved U04_proved I01_proved n hn X

end Yau.NodeProofs
